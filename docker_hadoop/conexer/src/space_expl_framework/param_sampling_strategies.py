from util import util
from conf_space import ConfType, ConfDataType
from sampling_strategies import UniformDistStrategy, ListSamplingStrategy


class PSS:
    def __init__(self, param_values):
        '''
        Input: a dictionary map parameter to values
        '''
        self.param_strategies = self.initial_strategies(param_values)

    def initial_strategies(self, param_values):
        param_strategies = {}
        for p in param_values.keys():
            if p not in util.important_params:
                # print 'No Sampling Strategy found for:', p
                continue
            dt = util.parameters.get(p.lower().strip()).data_type
            values = param_values[p]
            values = [v.value for v in values]
            if dt is ConfDataType.integer:
                values = [int(v) for v in values]
            elif dt is ConfDataType.float:
                values = [float(v) for v in values]

            # find sampling strategy classes
            strategy_name = util.param_sampling_strategy[p]
            strategy_class = globals()[strategy_name]
            print p, values
            if 'list' in strategy_class.__name__.lower():
                param_strategies[p] = strategy_class(p, dt, values)
            elif 'uniform' in strategy_class.__name__.lower():
                default = values[0]
                if 'java.opt' in p:
                    dt = ConfDataType.integer
                    values = [int(v[4:-1]) for v in values]
                values = sorted(values)
                low, high = values[0], values[-1]
                print low, high
                param_strategies[p] = strategy_class(p, dt, default, low, high)
        return param_strategies

    def get_strategy(self, param):
        if param in self.param_strategies:
            return self.param_strategies[param]
        # return None if no strategy found
        return None
