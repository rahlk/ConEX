from config_space import ConfSpace
from config_space import Parameter
from config_space import ComponentType, ParamDataType
import os, sys
import random
from util import util
import numpy as np
from abs_classes import AbstractAlgo

class CoordinateDescent(AbstractAlgo):
    def __init__(self, profiler):
        self.conf_space = ConfSpace()
        # self.semantics = self.conf_space.hadoop_semantics
        self.profiler = profiler()
        # self.predictor = PerfPredict()
        self.profile_num = 1
        self.performance_track = []
        self.K_iters_for_convergence_test = 5   # check the last 5 iterations
        self.perf_improvement_threshold = 0.02   # 2% of the improvement on the last cycle
        self.best_conf = None

    def test_feature_engineering_gen_values(self, params):
        param_values = dict()
        for pname, p in params.iteritems():
            data_type = p.data_type
            values = []
            if data_type is ConfDataType.boolean:
                values.extend([True, False])
            elif data_type is ConfDataType.integer:
                values.extend([1,2,3,4,5])
            elif data_type is ConfDataType.string:
                values.extend(['hello', 'world', 'foo', 'bar', 'gar'])
            elif data_type is ConfDataType.category:
                values.extend(['default', 'three', 'values'])
            elif data_type is ConfDataType.float:
                values.extend([0.1, 0.2, 0.3, 0.4, 0.5])
            param_values[p.name] = values
        return param_values

    def test_feature_engineering(self):
        '''
        This function tests the number of duplicates detected with feature
        engineering.
        Output: #dup_confs, #total_confs
        0. get the child to parent dictionary
        1. get all parameters
        2. generate random value for them
        3. generate an initial configuration
        4. go through all parameters and values
        5. count the number of duplicates
            A. add 1 to the number of children parameters when parent is False
        '''
        total_save = 0
        total = 0
        all_parents = self.semantics.get_all_parents()
        # all_parents = [p.lower() for p in all_parents]
        all_params = util.parameters # here all_params is a dictionary of p_name-> a Parameter definition
        # print '#All parameters:', len(all_params)
        param_values = self.test_feature_engineering_gen_values(all_params)
        child_parent = self.semantics.get_parent(all_params)
        # for pp in all_parents:
        #     children = self.semantics.get_children_by_parent(pp)
        #     for c in children:
        #         values = param_values[c.lower()]
        #         if values is None:
        #             print 'error in find values for parameter:', c
        #         values_len = len(values)
        #         total_save += values_len
        init_conf = dict()
        # for p, values in param_values.iteritems():
        #     v = random.choice(values)
        #     init_conf[p] = v
        '''
        1. select all parents
        2. random set values for parents
        3. iterate all parameters, add total
            A. if child parameter, add total save
        '''
        for pp in all_parents:
            ppvs = param_values[pp]
            init_conf[pp] = random.choice(ppvs)
        tmp_pp = len([p for p, v in init_conf.iteritems() if v is False])
        # print 'True parents:', tmp_pp
        all_directions = set(param_values.keys())
        max_iter = 10000
        index = 0
        while index < max_iter:
            if len(all_directions) == 0:
                # print 'another round'
                all_directions = set(param_values.keys())
            next_d = random.choice(list(all_directions))
            all_directions.discard(next_d)
            next_d_values = param_values[next_d]
            index += len(next_d_values)
            total += len(next_d_values)
            if next_d in child_parent and init_conf[child_parent[next_d]] is False:
                total_save += len(next_d_values)
        return total, total_save
        # all_directions = set(param_values.keys())
        # max_iter = 10000
        # index = 0
        # while index < max_iter:
        #     if len(all_directions) == 0:
        #         # print 'another round'
        #         all_directions = set(param_values.keys())
        #     next_d = random.choice(list(all_directions))
        #     all_directions.discard(next_d)
        #     next_d_values = param_values[next_d]
        #     index += len(next_d_values)
        #     total += len(next_d_values)
        #     if next_d in child_parent and:
        #         # children = self.semantics.get_children_by_parent(next_d)
        #         # for c in children:
        #         values = param_values[next_d]
        #         total_save += len(values)
        #         index += len(values)
        #         all_directions.discard(c)

        # init_conf = dict()
        # for p, values in param_values.iteritems():
        #     # total += len(values)
        #     v = random.choice(values)
        #     init_conf[p] = v
        #     # values.remove(v)
        # child_parent = self.semantics.get_parent(init_conf.keys())
        # print 'length of child_parent:', len(child_parent)
        # # check if values have been changed
        # # fst_p, snd_p = param_values.keys()[0], param_values.keys()[1]
        # # print 'values of parameter', fst_p, ':', param_values[fst_p]
        # # print 'values of parameter', snd_p, ':', param_values[snd_p]
        # # now we have an initial configuration, let's check the number of
        # # configurations we could save
        # # for p in init_conf:
        # #     if p in child_parent and init_conf[child_parent[p].lower()] is False:
        # #         total_save += 1
        # # print 'total saved in initial conf:', total_save
        # # count the left ones
        # all_directions = set(param_values.keys())
        # max_iter = 10000
        # index = 0
        # while index < max_iter:
        #     index += 1
        #     if len(all_directions) == 0:
        #         # print 'another round'
        #         all_directions = set(param_values.keys())
        #     # here we optimize the next_direction, a single parameter
        #     next_direction = random.choice(list(all_directions))
        #     all_directions.discard(next_direction)
        #     nd_values = param_values[next_direction]
        #     for v in nd_values:
        #         total += 1
        #         init_conf[next_direction] = v
        #         if next_direction in child_parent and child_parent[next_direction] is False:
        #             total_save += 1

        # print 'total:', total, 'total_saved', total_save

    def run(self):
        print 'called coordinate descent run()'
        return 1, 2, 3
        '''
        We are going to use coordinate descent to find a best configuration.
        We find the best value for each parameter to achieve an optimal point.
        :return: the number of iterations, best configuration, and corresponding performance
        '''
        init_conf = self.get_initial_confs()
        self.all_params = init_conf.keys()
        print '========= Default Configuration ==========='
        print init_conf
        init_perf = self.profiler.profile(self.profile_num, init_conf)
        self.global_best_perf = init_perf
        self.performance_track.append(init_perf)
        print 'Iteration:', self.profile_num, ' == Default performance:', init_perf
        self.profile_num += 1
        params = init_conf.keys()
        self.last_best = init_perf
        self.best_perf = init_perf
        self.best_conf = init_conf
        best_iter = 1
        # params = ['io.map.index.skip']
        all_directions = set(params)
        # curr_best_conf = init_conf
        # curr_best_perf = init_perf
        while not self.converged():
            if len(all_directions) == 0:
                self.last_best = self.best_perf
                all_directions = set(params)
                self.performance_track = []
            next_direction = random.choice(list(all_directions))
            curr_best_perf, curr_best_conf = self.optimize_a_parameter(next_direction, self.best_conf, self.best_perf)
            self.performance_track.append(curr_best_perf)
            if curr_best_perf < self.best_perf:
                self.best_perf = curr_best_perf
                self.best_conf = curr_best_conf
                best_iter = self.profile_num
            all_directions.discard(next_direction)
        # for p in params:
        #     # p here is the initial point
        #     # the returned configuration is optimized in dimension p and its performance
        #     best_perf_p, best_conf_p = self.optimize_for_single_parameter(p, init_conf, init_perf)
        #     if best_perf_p < best_perf:
        #         best_perf = best_perf_p
        #         best_conf = best_conf_p
        #     # find the next direction to optimize
        #     all_directions = set(params)
        #     all_directions.discard(p)
        #     while True:
        #         if len(all_directions) == 0:
        #             break
        #         # randomly select next direction to optimize
        #         next_direction = random.choice(list(all_directions))
        #         best_perf_p, best_conf_p = self.optimize_for_single_parameter(next_direction, best_conf_p, best_perf)
        #         if best_perf_p < best_perf:
        #             best_perf = best_perf_p
        #             best_conf = best_conf_p
        #         all_directions.discard(next_direction)
        print 'Best performance found in iteration:', best_iter, '\tPerformance:', self.best_perf
        return self.profile_num, self.best_conf, self.best_perf

    def converged(self):
        if len(self.performance_track) < len(self.all_params):
            return False
        #sorted_perf_track = sorted(self.performance_track)
        #best_in_this_loop = sorted_perf_track[0]
        if self.best_perf > self.last_best:
            return True
        improvement_percentage = (self.last_best - self.best_perf) / (self.last_best * 1.0)
        if improvement_percentage < self.perf_improvement_threshold:
            return True
        return False

    def old_converged(self):
        '''
        This function tests if the algorithm converged.
        It tests whether each one of the last K optimizations improved the performance by a threshold.
        This threshold is defined as 20% of the average improvement in optimization from [0, K-1].
        :return:
        '''
        if len(self.performance_track) < self.K_iters_for_convergence_test + 1:
            return False

        print 'performance track', self.performance_track
        # the first performance value is the default performance
        def_perf = self.performance_track[0]
        # these are performance values that we want to compute the average performance improvement
        # they are performance between the default one and the last K ones (exclusive)
        # other_iterations = self.performance_track[1:]
        performance_to_compare = self.performance_track[1:-self.K_iters_for_convergence_test]
        if len(performance_to_compare) == 0:
            return False

        perf_improvement = []
        for i in range(1, len(performance_to_compare)):
            perf_improvement.append(self.performance_track[i-1] - self.performance_track[i])
        print 'performance improvement', perf_improvement

        # some directions have improvements 0, remove them first before compute the average improvement
        improvement_larger_than_0 = [v for v in perf_improvement if v > 0]
        if len(improvement_larger_than_0) == 0:
            # improvement is 0 in more then K times
            if len(perf_improvement) >= self.K_iters_for_convergence_test:
                return True
            return False

        mean_improvement = np.mean(improvement_larger_than_0)
        last_K_iterations = self.performance_track[-self.K_iters_for_convergence_test:]
        print 'last K iterations performance improvement', last_K_iterations
        # in case any one of last K iterations is larger than the threshold, return False
        for i in range(-self.K_iters_for_convergence_test, 0):
            tmp_improvement = self.performance_track[i-1] - self.performance_track[i]
            # last_K_improvement.append(tmp_improvement)
            if tmp_improvement >= mean_improvement * self.perf_improvement_threshold:
                return False
        return True

    def optimize_a_parameter(self, param, in_conf, curr_perf):
        '''
        This function optimize the configuration on a single dimension given by parameters.
        :param param: the given parameter to optimize
        :param in_conf: a given start point
        :param curr_perf: performance of in_conf
        :return: the best configuration found on "param"
        '''
        print '====================================================================='
        print 'Optimize Parameter:', param
        conf = in_conf.copy()
        all_values = self.conf_space.param_values.get(param)
        if all_values is None:
            print 'no values found for:', param
            return sys.maxsize, in_conf
        all_values = [v.value for v in all_values]
        print 'All values:', all_values
        curr_value = conf[param]
        print 'current value:', curr_value
        # self.profile_num += 1
        best_perf = curr_perf
        best_value = curr_value

        param_data_type = util.parameters.get(param).data_type
        if param_data_type in [ConfDataType.integer, ConfDataType.float]:
            '''
            # First, we can sort all values.
            # Second, we can find the index of the current value
            # Third, we evaluate the previous and next value of the current one to find the direction to go
            # Forth, once we found the direction, we go to that direction
            # TODO: here we assume that performance curve is convex
            '''
            # integer of float
            if param_data_type is ConfDataType.integer:
                all_values = [int(v) for v in all_values]
                curr_value = int(curr_value)
            else:
                all_values = [float(v) for v in all_values]
                curr_value = float(curr_value)
            all_values = sorted(all_values)

            curr_idx = all_values.index(curr_value)
            # if the current value is the first one of the value list
            if curr_idx == 0:
                for v in all_values[1:]:
                    conf[param] = v
                    p = self.profiler.profile(self.profile_num, conf)
                    print 'Iteration:', self.profile_num, 'Parameter:', param, '=== Value:', \
                        v, "=== Performance:", p
                    self.profile_num += 1
                    if p < best_perf:
                        best_value = v
                        best_perf = p
                # conf[param] = best_value
                # return best_perf, conf
            # if the current value is the last one of the value list
            elif curr_idx == len(all_values) - 1:
                for i in range(len(all_values) - 2, -1 , -1):
                    v = all_values[i]
                    conf[param] = v
                    p = self.profiler.profile(self.profile_num, conf)
                    print 'Iteration:', self.profile_num, 'Parameter:', param, '=== Value:', \
                        v, "=== Performance:", p
                    self.profile_num += 1
                    if p < best_perf:
                        best_value = v
                        best_perf = p
                # conf[param] = best_value
                # return best_perf, conf
            else:
                # the current value is at somewhere in the middle
                # we test the previous one and the next one to decide which direction to go
                perf_dict = {}
                perf_dict[curr_value] = curr_perf
                # evaluate the previous one
                conf[param] = all_values[curr_idx - 1]
                previous_perf = self.profiler.profile(self.profile_num, conf)
                print 'Iteration:', self.profile_num, 'Parameter:', param, '=== Value:', \
                    all_values[curr_idx - 1], "=== Performance:", previous_perf
                perf_dict[all_values[curr_idx - 1]] = previous_perf
                self.profile_num += 1
                # evaluate the next one
                conf[param] = all_values[curr_idx + 1]
                next_perf = self.profiler.profile(self.profile_num, conf)
                print 'Iteration:', self.profile_num, 'Parameter:', param, '=== Value:', \
                    all_values[curr_idx + 1], "=== Performance:", next_perf
                perf_dict[all_values[curr_idx + 1]] = next_perf
                self.profile_num += 1
                # decide which direction to go
                values_to_profile = []
                if previous_perf < next_perf:
                    # evaluate the first half
                    values_to_profile = all_values[0:curr_idx - 1]
                else:
                    values_to_profile = all_values[curr_idx + 2:]
                perf_dict = self.profile_all_values(param, values_to_profile, conf, perf_dict)
                # find the best one
                best_value = min(perf_dict, key=perf_dict.get)
                best_perf = perf_dict[best_value]
        elif param_data_type in [ConfDataType.boolean, ConfDataType.category, ConfDataType.string]:
            # here, the only option is to evaluate them all
            all_values = set([str(v).strip() for v in all_values])
            # we already know the performance of the current value, no need to profile one more time
            all_values.discard(curr_value)
            all_values = list(all_values)
            perf_dict = {}
            perf_dict[curr_value] = curr_perf
            perf_dict = self.profile_all_values(param, all_values, conf, perf_dict)
            best_value = min(perf_dict, key=perf_dict.get)
            best_perf = perf_dict[best_value]
        print 'Best value for parameter:', param, ' === ', best_value, \
            '=== Performance:', best_perf
        conf[param] = best_value
        return best_perf, conf

    def profile_all_values(self, param, values, init_conf, perf_dict):
        new_conf = init_conf.copy()
        for v in values:
            new_conf[param] = v
            perf = self.profiler.profile(self.profile_num, new_conf)
            print 'Iteration:', self.profile_num, ' Parameter:', param, '=== Value:', v, "=== Performance:", perf
            self.profile_num += 1
            perf_dict[v] = perf
        # find out the value of the best performance
        return perf_dict

    def get_initial_confs(self):
        '''
        The initial configuration is the default one.
        :return:
        '''
        # params_to_exploit = self.predictor.important_feature_from_model
        params_to_exploit = util.important_params
        # next, we can default value for these parameters
        init_conf = {}
        for p in params_to_exploit:
            p = p.strip().lower()
            # the first one is default value
            def_v = self.conf_space.param_values.get(p)[0]
            init_conf[p] = def_v.value
        return init_conf
