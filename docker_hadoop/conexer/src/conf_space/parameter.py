import pandas as pd
import random
from sysconf import cfg
from value import Value
from conf_type import ConfType


class Parameter:
    def __init__(self, name, datatype, belongs):
        self.name = name
        self.belongs = belongs
        self.data_type = datatype

    def get_conf_file(self):
        if self.belongs is ConfType.yarn:
            return 'yarn-site.xml'
        elif self.belongs is ConfType.hdfs:
            return 'hdfs-site.xml'
        elif self.belongs is ConfType.mapred:
            return 'mapred-site.xml'
        elif self.belongs is ConfType.core:
            return 'core-site.xml'
