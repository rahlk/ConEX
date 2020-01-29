from configparser import ConfigParser
import os
import sys


class Config:
    def __init__(self, config_path):
        '''
        Parse the configuration file.

        Input: the path of configuration path
        Output: a directory object contains all configurations
        '''
        # print 'Call Config init...'
        config = ConfigParser()
        # check if the configuration file exists
        if not os.path.isfile(config_path):
            print("The given configuration file doesn't exist!")
            sys.exit(-1)
        config.readfp(open(config_path))

        # base_dir = 'resource'
        # # create base directory if not exists
        # if not os.path.exists(base_dir):
        #     os.makedirs(base_dir)

        # config_dict['hist_data'] = base_dir + os.sep + \
        #     config.get('resource', 'hist_data')
        # config_dict['important_params'] = base_dir + os.sep + \
        #     config.get('resource', 'important_parameters')
        # config_dict['p_values'] = base_dir + os.sep + \
        #     config.get('resource', 'parameter_values')
        self.platform = config.get('platform', 'cluster')
        self.hadoop_home = config.get('paths', 'hadoop_home')
        self.hibench_home = config.get('paths', 'hibench_home')
        self.gen_confs = config.get('paths', 'conf_generated')
        self.hadoop_checker = config.get('paths', 'hadoop_typechecker')

        base_dir = config.get('resource', 'base_dir')
        self.hist_data = base_dir + os.sep + \
            config.get('resource', 'hist_data')
        self.important_params = base_dir + os.sep + \
            config.get('resource', 'important_parameters')
        self.p_values = base_dir + os.sep + \
            config.get('resource', 'parameter_values')
        self.hadoop_params = base_dir + os.sep + \
            config.get('resource', 'hadoop_params')
        self.tiny_data = base_dir + os.sep + \
            config.get('resource', 'tiny_data')
        self.small_data = base_dir + os.sep + \
                          config.get('resource', 'small_data')
        self.distance = base_dir + os.sep + \
                        config.get('resource', 'distance')
        self.perf_predict_model = base_dir + os.sep + \
                                  config.get('resource', 'perf_predict_model')
        self.X_scaler = base_dir + os.sep + \
                      config.get('resource', 'X_scaler')
        self.y_scaler = base_dir + os.sep + \
                        config.get('resource', 'y_scaler')
        self.conf_params = base_dir + os.sep + \
                      config.get('resource', 'conf_params')
        self.old_new_param_mapping = base_dir + os.sep + \
                                     config.get('resource', 'old_new_param')
        self.important_feature_from_model = base_dir + os.sep + \
                                     config.get('resource', 'important_feature_from_model')
        self.hadoop_param_hierarchy = base_dir + os.sep + \
                                     config.get('resource', 'hadoop_param_hierarchy')
        self.hadoop_realworld_type = base_dir + os.sep + \
                                     config.get('resource', 'realworld_type')

        self.debug = config.get('debug', 'enable')
        self.debug_log = config.get('debug', 'log_file')


cfg = Config('conf.ini')
