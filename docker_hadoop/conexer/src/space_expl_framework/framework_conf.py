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

        self.platform = config.get('platform', 'cluster')
        self.sys_home = config.get('paths', 'sys_home')
        self.hibench_home = config.get('paths', 'hibench_home')
        self.gen_confs = config.get('paths', 'conf_generated')

        base_dir = config.get('resource', 'base_dir')
        self.p_values = base_dir + os.sep + \
            config.get('resource', 'parameter_values')

        self.debug = config.get('debug', 'enable')
        self.debug_log = config.get('debug', 'log_file')
