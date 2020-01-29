from space_expl_framework.abs_classes import AbstractSamplingStrategy
import random

class ListSamplingStrategy(AbstractSamplingStrategy):
    def __init__(self, param, dt, values=[]):
        '''
        When initializing a ListSamplingStrategy, one needs to give a list of
        possible values.
        '''
        self.name = 'list_sampling_strategy'
        self.param_name = param
        self.param_datatype = dt
        self.values = values
        # This dictionary will save how many times an element has been visited
        self.visit_freq = dict()
        for v in values:
            self.visit_freq[v] = 0

    def next_value(self, curt_val=None):
        '''
        Return the next value according to the current value.
        '''
        # TODO: maybe we don't need a current value
        # For now, just return a random value
        if len(self.values) == 0:
            return None
        return random.choice(self.values)
