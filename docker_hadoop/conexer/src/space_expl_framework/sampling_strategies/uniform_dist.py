from space_expl_framework.abs_classes import AbstractSamplingStrategy
import random
from conf_space import ConfType, ConfDataType

class UniformDistStrategy(AbstractSamplingStrategy):
    def __init__(self, param, dt, central, low, high):
        self.name = 'uniform_distribution'
        self.param_name = param
        self.param_datatype = None
        if dt is ConfDataType.float:
            self.param_datatype = float
            central = float(central)
            low = float(low)
            high = float(high)
        elif dt is ConfDataType.integer:
            self.param_datatype = int
            central = int(central)
            low = int(low)
            high = int(high)
        self.central = central
        self.low = low
        self.high = high

    def next_value(self):
        '''
        Return next value...
        '''
        if self.param_datatype is None:
            print '===Error...Datatype is none'
            return None
        if self.param_datatype == int:
            return random.randint(self.low, self.high)
        if self.param_datatype == float:
            return random.uniform(self.low, self.high)
