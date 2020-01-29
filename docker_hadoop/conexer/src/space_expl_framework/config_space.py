from sysconf import cfg
import pandas as pd

class Parameter:
    def __init__(self, pname, datatype, comp):
        self.name = pname
        self.component = comp
        self.data_type = datatype


class Value:
    def __init__(self, p, v):
        self.pname = p
        self.value = v
        self.visited = False
        self.visited_num = 0


class ComponentType:
    unknown, core, hdfs, yarn, mapred = range(5)


class ParamDataType:
    unknown, boolean, integer, category, string, double = range(6)


class ConfSpace:
    '''
    This class contains all parameters and their values.
    '''
    def __init__(self):
        # self.hadoop_semantics = HadoopSemantics()
        self.parameters = self.get_searchable_parameters()
        self.param_values = self.read_confspace_xls()
        self.perf_param = 'performance'
        # this will keep the index of current configuration
        # This will used later to find nearest neighbor
        self.curr_conf_idx = None

    def get_default_conf(self, params):
        default_conf = {}
        for p in params:
            val = self.param_values.get(p)
            if val is None:
                print 'cannot find value for parameter:', p
            else:
                default_conf[p] = val[0].value
        # for p, vlist in self.param_values.iteritems():
        #     default_conf[p] = vlist[0]
        return default_conf

    def get_all_params(self):
        return self.parameters

    def get_values_by_param(self, p):
        return self.param_values.get(p)

    def get_searchable_parameters(self):
        csv_file = cfg.important_params
        searchable_params = []
        with open(csv_file, 'r') as fp:
            for line in fp:
                param = line.strip().split(',')[0].strip()
                searchable_params.append(param)
        return searchable_params

    # def get_init_conf(self):
    #     # history data is sorted by performance
    #     # so the first row is the conf with best performance in history
    #     # init_conf = self.hist_data.hist_data.iloc[0]
    #     # conf_params = self.hist_data.hist_data.columns.tolist()
    #     # selected_cols = list(set(self.parameters).intersection(conf_params))
    #     # return init_conf[selected_cols]
    #     first_idx = self.hist_data.hist_data.index[0]
    #     first_conf = self.hist_data.hist_data.loc[first_idx]
    #     self.curr_conf_idx = first_idx
    #     return first_conf.to_dict()

    # def get_confdict_from_hist_record(self, record):
    #     # the input is a serious
    #     # return a dictionary
    #     return record.to_dict()

    # def get_next_conf_by_dist(self):
    #     '''
    #     This function returns a neighbor configuration by parameter vector distance.
    #     '''
    #     ret_idx, neighbor_conf = self.hist_data.get_next_neighbor_by_dist(self.curr_conf_idx)
    #     if ret_idx is None:
    #         print 'No further neighbor. Exit...'
    #         return None
    #     self.curr_conf_idx = ret_idx
    #     print ret_idx
    #     return neighbor_conf

    def read_confspace_xls(self):
        '''
        This function reads a configuration space representation in .xlsx file.
        Data to read:
            1. parameters
            2. default value and alternative values
            3. parameter data type
            4. parameter component type
        '''
        param_df = pd.read_excel(cfg.p_values, header=0)
        params = param_df['Parameters']
        default_values = param_df['Default']
        alternatives = param_df['Alternative']
        good_as_param = param_df['Good']
        param_values = {}
        for index, row in param_df.iterrows():
            # row head: Parameters, Default,Alternative, Note, Good
            # if str(good_as_param[index]).lower().strip() == 'n':
            #     continue
            param = params[index].strip()
            v = Value(param, str(default_values[index]).strip())
            all_values = [v]
            # all_values = [] # do not include default values
            for altV in str(alternatives[index]).split(','):
                if altV == 'nan' or altV.lower().strip() == '':
                    continue
                all_values.append(Value(param, altV.strip()))
            param_values[param.strip().lower()] = all_values
        # print '========== test parameter exists =============='
        # print 'yarn.resourcemanager.scheduler.class' in param_values
        # print 'yarn.resourcemanager.store.class' in param_values
        # print 'mapred.child.java.opts' in param_values
        return param_values
