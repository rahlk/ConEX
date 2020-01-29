'''
1. given a configuration in a dictionary, generate a corresponding Coq representation
2. call coqc to check validate with configuration, and return true or false

needed information:
    1. parameters' modules
'''
import pandas as pd
from sysconf import cfg
from util import util
import os
import subprocess

class HadoopConfChecker:
    def __init__(self):
        self.parameters = util.parameters   # param => Parameter(pname, datatype, belongs)
        self.rtype_file = cfg.hadoop_realworld_type
        self.read_rtype(self.rtype_file)
        # create a folder to keep Coq configurations
        self.coq_conf_folder = cfg.gen_confs + os.sep + 'coq_confs'
        util.make_folder_ready(self.coq_conf_folder)

    def set_all_param_value(self, p_values):
        '''
        '''
        self.all_param_value = p_values

    def read_rtype(self, xlsx_file):
        self.param_valus = {}
        self.param_module = {}
        self.param_mtype = {}
        self.param_ntype = {}
        self.option_type = {}

        df = pd.read_excel(xlsx_file, header=0)
        for index, row in df.iterrows():
            param = row['Parameter'].strip()
            default_value = [str(row['Default']).strip()]
            alt_values = row['AltValues']
            alt_values = alt_values.strip().split(',')
            alt_values = [str(v).strip() for v in alt_values]
            all_values = default_value
            all_values.extend(alt_values)
            self.param_valus[param] = all_values
            module = row['Subcomponent']
            module = module.strip().split('-')[0]
            self.param_module[param] = module
            machine_type = row['Machine_Type']
            machine_type = self.unify_machine_type(param, machine_type)
            native_type = self.get_native_type(machine_type)
            self.param_mtype[param] = machine_type
            self.param_ntype[param] = native_type
            opt_type = str(row['OptionType']).strip()
            if opt_type.startswith('option'):
                self.option_type[param] = opt_type.strip()

    def unify_machine_type(self, p, input_type):
        input_type = input_type.lower().strip()
        if 'integer' in input_type:
            return 'Z'
        if 'nature' in input_type:
            return 'pos'
        if 'non-negative' in input_type:
            return 'N'
        if 'bool' in input_type:
            return 'bool'
        if 'opts' in p.lower() and 'string' in input_type.lower():
            return 'JavaOpts'
            # return 'string'
        return input_type


    def get_native_type(self, machine_type):
        # if 'opt' in machine_type.lower():
        #     return 'string'
        if 'pos' in machine_type:
            return 'positive'
        if 'float' in machine_type.lower():
            return 'R'
        return machine_type

    def check(self, profile_num, conf):
        self.conf = conf
        coq_conf_str = self.create_coq_conf(conf)
        # write into a temporary folder
        tmp_conf_name = 'tmp_conf' + str(profile_num) + '.v'
        tmp_conf_name = self.coq_conf_folder + os.sep + tmp_conf_name
        with open(tmp_conf_name, 'w') as fp:
            fp.write(coq_conf_str)
        # verify
        verify_cmd = 'coqc -R ' + cfg.hadoop_checker + ' Top ' + tmp_conf_name
        is_valid = self.run_shell_cmd(verify_cmd)
        return is_valid

    def create_coq_conf(self, conf):
        '''
        This function creates a Coq configuration string and return it.
        '''
        need_postfix = set(['positive', 'N', 'Z', 'R'])
        file_content = '''Require Import hadoop_config.
    Require Import Reals.
    Open Scope R_scope.
    Require Import Omega.
    '''
        core_module = '''Definition a_core_config: CoreConfig.
    Proof.
    unshelve refine (
        mk_core_config
    '''
        hdfs_module = '''Definition a_hdfs_config: HDFSConfig.
    Proof.
    unshelve refine (
        mk_hdfs_config
    '''
        mapred_module = '''Definition a_mapred_config: MapRedConfig.
    Proof.
    unshelve refine (
        mk_mapred_config
    '''
        yarn_module = '''Definition a_yarn_config: YarnConfig.
    Proof.
    unshelve refine (
        mk_yarn_config
    '''
        #############################################
        modules = list(set(self.param_module.values()))
        params = self.param_valus.keys()
        conf_ps = conf.keys()
        module_params = {'core':[], 'hdfs': [], 'mapred': [], 'yarn': []}
        for p in params:
            m = self.param_module[p].lower().strip()
            v = ''
            if p not in conf_ps:
                #print 'parameter not in conf:', p
                v = self.all_param_value.get(p.lower())[0].value
                if v is None:
                    print 'not found default value for:', p
            else:
                v = conf[p]
            v = str(v)
            if v == '' or v == 'None':
                print 'checker: value is empty...'
            if p in self.option_type:
                opt_type = self.option_type.get(p)
                if 'pos' in opt_type and int(v) > 0:
                    v = '(Some ' + v + '%positive)'
                else:
                    v = 'None'
            elif self.param_ntype[p] == 'string':
                v = '"' +v+ '"'
            elif self.param_ntype[p] == 'R':
                v = '(' + str(float(v)*100).split('.')[0] +'/100)%R'
            elif self.param_ntype[p] == 'N':
                v = v + '%N'
            elif self.param_ntype[p] == 'positive':
                v = v + '%positive'
            elif self.param_ntype[p] == 'Z':
                v = '(' + v + ')%Z'
            elif self.param_ntype[p] == 'JavaOpts':
                # parse number in java opts
                mem_num = v[4:-1]
                v = '(mk_java_opts ' + mem_num + '%positive 100%positive)'

            p_in_coq = p.replace('.', '_').replace('-', '__')

            if 'core' in m:
                module_params['core'].append((p_in_coq, v))
            elif 'hdfs' in m:
                module_params['hdfs'].append((p_in_coq, v))
            elif 'mapred' in m:
                module_params['mapred'].append((p_in_coq, v))
            elif 'yarn' in m:
                module_params['yarn'].append((p_in_coq, v))

        for module, pvs in module_params.iteritems():
            sorted_pvs = sorted(pvs, key=lambda x: x[0])
            module_str = ''
            for p, v in sorted_pvs:
                module_str += '    (' + p + '.mk false '+ v + ' _ )\n'

            if module == 'core':
                core_module += module_str
            elif module == 'hdfs':
                hdfs_module += module_str
            elif module == 'mapred':
                mapred_module += module_str
            elif module == 'yarn':
                yarn_module += module_str

        #############################################
        core_module += '''); try (exact I); try compute; auto.
    Defined.

    '''
        hdfs_module += '''); try (exact I).
    Defined.

    '''
        mapred_module += '''      _
        _
        _
        _
        _
    ); try (exact I); simpl; try (intro H); try (inversion H); try compute; try reflexivity; auto.
    Defined.

    '''
        yarn_module += '''      _
          _
          _
    ); try (exact I); compute; try reflexivity; auto.
    Defined.
    '''

        file_content += '\n'.join([core_module, hdfs_module, mapred_module, yarn_module])
        file_content += '''
    Definition a_hadoop_config: HadoopConfig.
    Proof.
     unshelve refine (
      mk_hadoop_config
        a_yarn_config
        a_mapred_config
        a_core_config
        a_hdfs_config
        _
        _
    ); try (exact I); simpl; omega.
    Defined.
    '''
        return file_content

    def run_shell_cmd(self, cmd):
        FNULL = open(os.devnull, 'w')
        p = subprocess.Popen(cmd.split(' '), stdout=FNULL, stderr=FNULL)
        p.wait()
        ret_code = p.returncode
        FNULL.close()
        if ret_code != 0:
            return False
        return True
