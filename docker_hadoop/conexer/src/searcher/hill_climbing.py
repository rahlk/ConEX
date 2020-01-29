from profiler import Profiler
from conf_space import ConfSpace
from conf_space import Parameter
import os
import random
from util import util
from predict_model import PerfPredict


class HillClimbing:
    def __init__(self):
        self.conf_space = ConfSpace()
        self.profiler = Profiler()
        self.predictor = PerfPredict()
        self.exploit_times = 0
        self.exploit_max = 5
        # how many configurations to predict with performance predictor before really runs the benchmark
        self.predict_max = 1000

    def get_next_value(self, values, curr_v):
        # TODO: currently, we are explore the value randomly, we might need more intelligent way to do it
        # when the program run first time, we need to set the value object that has curr_v as visited
        # for v in values:
        #     if v.value == curr_v:
        #         v.visited_num += 1
        #         break
        # sort value list by visited times
        # values_sorted = sorted(values, key=lambda x: x.visited_num)
        # return the first one since it has been least times
        # return values_sorted[0].value
        # values = [v for v in values if v.value != curr_v and v.visited is False]
        # values = [v for v in values if v.value != curr_v]   # filter out the current value
        # if len(values) is 0:
        #     return curr_v
        # selected_value = random.choice(values)
        # selected_value.visited = True
        # return selected_value.value
        # just get a random value
        while True:
            next_v = random.choice(values)
            if str(next_v.value).lower().strip() != str(curr_v).lower().strip():
                return next_v.value

    def get_next_conf_exploit(self, in_conf):
        curr_conf = in_conf.copy()
        '''
        Now it's randomly select next values.
        A more intelligent way is needed.
        We could use the importance of parameters.
        :param curr_conf:
        :return:
        '''
        # print 'calling get_next_conf_exploit'
        # here we adjust the value of first 10 parameters
        # TODO: we changed first 10 parameters, but it was found that number of final configurations are few
        # TODO: an alternative way could be randomly select N parameters to exploit
        param_to_exploit = self.predictor.important_feature_from_model
        param_to_exploit = random.sample(param_to_exploit, len(param_to_exploit)/2)
        # param_to_exploit = util.important_params
        # print 'params to exploit:', param_to_exploit
        for p in param_to_exploit:
            p_orig = p
            p = p.lower().strip()
            values = self.conf_space.param_values.get(p)
            curr_v = curr_conf.get(p_orig)
            if values is None:
                print 'cannot find values for parameter:', p
                continue
            # if curr_v is None:
            #     print 'Warning: current value is None'
            #     continue
            # find the next different value
            new_v = self.get_next_value(values, curr_v)
            # if new_v == curr_v:
            #     print 'Waning... return the same value'
            curr_conf[p_orig] = new_v
        return curr_conf

    def get_next_conf_by_distance(self):
        # print 'calling get_next_conf_by_distance'
        return self.conf_space.get_next_conf_by_dist()

    def get_next_conf(self, curr_conf):
        if self.exploit_times < self.exploit_max:
            self.exploit_times += 1
            return self.get_next_conf_exploit(curr_conf)
        else:
            self.exploit_times = 0
            return self.get_next_conf_by_distance()

    def get_random_conf(self):
        conf = {}
        for p in self.predictor.important_feature_from_model:
            values = self.conf_space.param_values.get(p)
            v = random.choice(values)
            conf[p] = v.value
        return conf

    def better_perf(self, perf1, perf2):
        return perf1 < perf2

    def conf_diff(self, conf1, conf2):
        diff_conf = []
        print '========== conf diff: ============='
        for p in conf1:
            if conf1.get(p) != conf2.get(p):
                print p
        print '========== end conf diff ============='

    def get_return_conf(self, conf, params):
        new_conf = {}
        for p in params:
            new_conf[p] = conf[p]
        return new_conf

    def find_next_conf_by_predictor(self, conf, perf):
        params = conf.keys()
        params = [p for p in params if '.' in p]
        # print 'prediction input conf', conf

        curr_conf = conf.copy()
        # run the performance model N times to try to find better configuration
        for i in range(self.predict_max):
            # get a neighbor configuration
            curr_conf = self.get_next_conf_exploit(curr_conf)
            # predict the performance of this neighbor
            curr_perf = self.predictor.predict(curr_conf, params)
            if curr_perf <= perf:
                print 'Found better after ==', i, '==iterations. Perf::: ', curr_perf
                return True, curr_conf, curr_perf

        print '==========No better configurations found, return the current configuration.=========='
        return False, conf, perf

    def run(self, N):
        # N is the maximum iterate numbers
        best_idx, iter_idx = 1, 1
        curr_conf = self.conf_space.get_init_conf()
        best_conf = curr_conf
        # This is very important !!!!
        self.profiler.start()
        best_perf = self.profiler.profile(iter_idx, curr_conf)
        print 'iteration:', iter_idx, '\treal-case time:', best_perf
        iter_idx += 1
        while iter_idx < N:
            # try to find a better neighbor configuration by static performance model
            found_better, curr_conf, pred_perf = self.find_next_conf_by_predictor(curr_conf, best_perf)

            if found_better:
                # a better neighbor is found, then profile it with benchmark
                curr_perf = self.profiler.profile(iter_idx, curr_conf)
                print 'iteration:', iter_idx, '\tpredicated:', pred_perf, '\treal-case time:', curr_perf
                if curr_perf < best_perf:
                    best_perf = curr_perf
                    best_conf = curr_conf
                    best_idx = iter_idx
            else:
                # no better neighbor found, we generate a random configuration to start again
                curr_conf = self.get_random_conf()
                print 'iteration:', iter_idx, '\tGet a random configuration and restart search...'
            iter_idx += 1
        self.profiler.finish()
        # return the best configuration and its performance
        return best_idx, best_conf, best_perf
