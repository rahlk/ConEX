from space_expl_framework import AbsConfSpace
from space_expl_framework import Config
from space_expl_framework.conf_space import Value
import pandas as pd

class SparkConfSpace(AbsConfSpace):
    def __init__(self, config):
        self.config = config
        self.param_value, self.param_datatype, self.param_component = self.read_confspace()
        return None

    def read_confspace(self):
        return self.read_confspace_xls(self.config.p_values)

    def read_confspace_xls(self, xls_file):
        '''
        This function reads a configuration space representation in .xlsx file.
        Data to read:
            1. parameters
            2. default value and alternative values
            3. parameter data type
            4. parameter component type
        '''
        space_df = pd.read_excel(xls_file, header=0)
        # print space_df.dtypes
        param_values = {}
        param_datatype = {}
        param_component = {}
        for index, row in space_df.iterrows():
            # row head: parameters, default, alternative, note, important, datatype, component
            if str(row['important']).lower().strip() == 'false':
                continue
            param = row['parameter'].strip().lower()
            default_v = Value(param, str(row['default']).strip())
            all_values = [default_v]
            # all_values = [] # do not include default values
            for altV in str(row['alternative']).split(','):
                if altV == 'nan' or altV.lower().strip() == '':
                    continue
                all_values.append(Value(param, altV.strip()))
            param_values[param] = all_values
            param_datatype[param] = str(row['datatype']).strip().lower()
            param_component[param] = str(row['component']).strip().lower()
        return param_values, param_datatype, param_component

    def get_default_conf(self):
        default_conf = {}
        for p in self.param_value.keys():
            val = self.param_value.get(p)
            if val is None:
                print 'cannot find value for parameter:', p
            else:
                default_conf[p] = val[0].value
        return default_conf

    def get_all_params(self):
        return self.param_value.keys()

    def get_values_by_param(self, p):
        return self.param_value.get(p)
