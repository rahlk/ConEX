'''
This script implements a MCMC algorithm for configuration space exploration.

We combine MCMC (for accept probability) and GA (for mutation).

Now the stop criterion becomes "maximum number of iterations". GA just do
the mutation, but not check convergence. Convergence checking is MCMC's work.
'''
import os
import sys
import random
import time
import math # for math.exp()
import numpy as np
from util import util
from conf_space import ConfDataType
from abs_classes import AbstractAlgo
from hadoop import HadoopConfChecker


class MCMC(AbstractAlgo):
    def __init__(self, conf, confspace, profiler):
        self.conf_space = confspace()
        # self.hadoop_semantics = self.conf_space.hadoop_semantics
        self.profiler = profiler()
        self.type_checker = HadoopConfChecker()
        self.type_checker.set_all_param_value(self.conf_space.param_values)
        self.curr_genconf_folder = conf.gen_confs + os.sep + 'conf'
        # the maximum generations to evolve, as a stopping criterion
        # self.max_generation = 10
        # the population size in each generation
        self.population_size = 200
        # self.conf_to_profile = 10
        self.profile_num = 0
        # the global performance improvement threshold, as a stopping criterion
        self.global_improvement = 0.8
        # discard a candidate if the performance improvement is less than this threshold
        # self.local_improvement = 0.01     # MCMC decides which configuration enter into parent set
        self.max_iter = 6000    # the maximum number of iteration for MCMC
        self.invalid_confs = []

    def run(self):
        '''
        This is the entrance of MCMC.
        '''
        params = self.conf_space.get_all_params()
        default_conf = self.conf_space.get_default_conf(params)
        print 'default configuration:'
        print default_conf
        default_perf = self.profile_conf(default_conf)
        if default_perf == sys.maxsize:
            print 'profile default configuration failed, exit...'
            sys.exit(-1)
        print 'Default performance. Profile num:', self.profile_num - 1, '=== Performance:', default_perf
        best_conf = default_conf.copy()
        best_perf = default_perf
        reference_point = best_perf
        best_profile_num = self.profile_num - 1
        conf_set = self.get_initial_confs()
        evolve_confs = []
        parent_confs = []
        for i in xrange(self.max_iter):
            # select a configuration and profile it
            conf_to_profile = None
            if len(conf_set) > 0:
                conf_index = random.randint(0, len(conf_set)-1)
                conf_to_profile = conf_set[conf_index]
                del conf_set[conf_index]
                curr_perf = self.profile_conf(conf_to_profile)
                if curr_perf == sys.maxsize:
                    continue
                
                if curr_perf <= best_perf:
                    print 'Better performance found. Profile num:', self.profile_num - 1, '=== Performance:', curr_perf
                    # update best configuration and performance
                    best_perf = curr_perf
                    best_conf = conf_to_profile
                    best_profile_num = self.profile_num - 1
                # reference point is the best on in last generation
                to_accept = self.to_accept(curr_perf, reference_point)
                if to_accept:
                    # add this configuration to candidate set
                    evolve_confs.append(conf_to_profile)
                    print 'Accept it!!!'
                if (default_perf - best_perf)*1.0/default_perf >= self.global_improvement:
                    print 'converged since achieved global performance improvement'
                    break
            else:
                # first update the reference point to the best one in last generation
                reference_point = best_perf
                # then evolve to next generation
                if len(evolve_confs) < int(self.population_size/10):
                    print '===== size less than 1/10 of population_size, recreate a set of initial configurations ===='
                    # add parent configurations
                    evolve_confs.extend(parent_confs)
                else:
                    parent_confs = evolve_confs
                # if the first generation has no enough good configurations
                # we have to add some random configurations
                if len(evolve_confs) < int(self.population_size/10):
                    for i in range(self.population_size/10 - len(evolve_confs)):
                        tmp_conf = self.get_a_random_conf()
                        evolve_confs.append(tmp_conf)
                conf_set = self.mutate(best_conf, evolve_confs)
                evolve_confs = []
        print 'invalid confs:', self.invalid_confs
        print 'Best performance:', best_perf, '==== best iteration:', best_profile_num
        return best_profile_num, best_conf, best_perf

    def to_accept(self, curr_perf, reference_perf):
        '''
        Compute the accept probability.
        Return: True for accept, False for reject
        '''
        # compute improvement percentage
        improvement = (reference_perf - curr_perf)*1.0/reference_perf
        # 0.8 here is a parameter
        accept_prob = math.exp(60*improvement)
        # generate a random float in (0,1)
        rand_float = 0.0
        while True:
            rand_float = np.random.uniform()
            if rand_float > 0.0:
                break
        if rand_float < accept_prob:
            return True   # accept
        return False

    def mutate(self, refer_conf, conf_sets):
        '''
        This is the mutate operation in MCMC. Here we follow the same procedure
        of GA to mutate configurations.
        Input: a set of configurations and their performance
        :return: a new set of configurations generated with crossover and
            mutation in GA.
        '''
        offsprings = []
        # first evolve all confs in conf_sets
        for c in conf_sets:
            new_conf = self.create_offspring(refer_conf, c)
            offsprings.append(new_conf)
        # then randomly select some configurations to evolve
        for i in range(self.population_size - len(offsprings)):
            parent1, parent2 = refer_conf, random.choice(conf_sets)
            new_conf = self.create_offspring(parent1, parent2)
            offsprings.append(new_conf)
        return offsprings

    def create_offspring(self, parent1, parent2):
        offspring = parent1.copy()
        # random select half parameters to crossover
        crossover_params = random.sample(parent1.keys(), len(parent1)/2)
        for p in crossover_params:
            offspring[p] = parent2.get(p)

        mutate_params = random.sample(crossover_params, int(len(parent1)*0.06))
        for p in mutate_params:
            values = self.conf_space.get_values_by_param(p)
            values = [v.value for v in values]
            '''
            This is a new implementation. For numerical parameters, we select values from a range.
            '''
            v = ''
            p_data_type = util.parameters.get(p.lower().strip()).data_type
            # p_data_type = self.conf_space.param_datatype.get(p.lower().strip())
            if p_data_type in [ConfDataType.float, ConfDataType.integer]:
                if p_data_type is ConfDataType.float:
                    values = [float(v) for v in values]
                    values = sorted(values)
                    v = random.uniform(values[0], values[-1])
                    v = "{0:.2f}".format(v)
                else:
                    values = [int(v) for v in values]
                    values = sorted(values)
                    v = random.randint(values[0], values[-1])
                    v = str(v)
            else:
                v = random.choice(values)
            offspring[p] = v
        return offspring

    def get_initial_confs(self):
        '''
        # Initial configurations do not need to consider the hierarchy structure.
        # So we do not need to do that here, only in the evolution steps.
        '''
        # params_to_exploit = self.conf_space.get_all_params()
        conf_set = []
        for i in range(self.population_size):
            new_conf = self.get_a_random_conf()
            # for p in params_to_exploit:
            #     values = self.conf_space.get_values_by_param(p.lower().strip())
            #     random_v = random.choice(values)
            #     new_conf[p] = random_v.value
            # print new_conf.values()
            conf_set.append(new_conf)
        # conf_set = self.hadoop_semantics.remove_dup_confs(conf_set)
        return conf_set

    def get_a_random_conf(self):
        params_to_exploit = self.conf_space.get_all_params()
        conf = {}
        for p in params_to_exploit:
            values = self.conf_space.get_values_by_param(p.lower().strip())
            random_v = random.choice(values)
            conf[p] = random_v.value
        return conf

    def profile_conf(self, conf):
        # print 'Enter profile_confs'
        perf = sys.maxsize
        # type checker for cnf
        if not self.type_checker.check(self.profile_num, conf):
            print 'type-checking failed, config', str(self.profile_num)
            self.invalid_confs.append(self.profile_num)
            genconf_folder = self.curr_genconf_folder + str(self.profile_num)
            util.make_folder_ready(genconf_folder)
            tmp_conf = conf.copy()
            for p, v in self.profiler.original_confs.iteritems():
                tmp_conf[p] = v
            util.write_into_conf_file(tmp_conf, genconf_folder)
            self.profile_num += 1
            return perf
        perf = self.profiler.profile(self.profile_num, conf)
        print time.strftime("%Y-%d-%m %H:%M:%S"), self.profile_num, 'benchmark done! Performance: ', perf
        self.profile_num += 1
        return perf
