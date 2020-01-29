from conf_space import ConfSpace
from conf_space import Parameter
from conf_space import ConfDataType
import os
import sys
import random
from util import util
from profiler import Profiler
from sysconf import cfg
# from predict_model import PerfPredict
import time
from space_expl_framework import HadoopConfChecker
from space_expl_framework import PSS


class Genetic:
    def __init__(self):
        self.conf_space = ConfSpace()
        # self.hadoop_semantics = self.conf_space.hadoop_semantics
        self.profiler = Profiler()
        self.pss = PSS(self.conf_space.param_values)
        self.curr_genconf_folder = cfg.gen_confs + os.sep + 'conf'
        self.type_checker = HadoopConfChecker()
        self.type_checker.set_all_param_value(self.conf_space.param_values)
        # self.predictor = PerfPredict()
        # the maximum generations to evolve, as a stopping criterion
        self.max_generation = 10
        # the population size in each generation
        self.population_size = 100
        self.conf_to_profile = 10
        self.profile_num = 1
        # how many configurations to predict with performance predictor before really runs the benchmark
        # self.predict_max = 1000
        # the global performance improvement threshold, as a stopping criterion
        self.global_improvement = 0.3
        # discard a candidate if the performance improvement is less than this threshold
        self.local_improvement = 0.0    # 0.001
        self.invalid_confs = []

    def run_vanilla_GA(self):
        '''
        1. get the default configuration and evaluate its performance
        2. get $population_size initial configurations and evaluate them
        3. remove invalid configurations (random generation could lead to "invalid" configurations,
            and invalid ones will have performance sys.maxsize)
        4. select the best configuration in this generation and compare with the global best one,
            keep the new one if it's better
        5. select configurations that improve performance by $local_improvement,
            if the number of selected ones is less than 2, add parents into this set, and
            continue to evolve till $max_generation reached (call elitism in some evolutionary algorithms)
        6. random select two configurations from resulting configurations from step 5,
            and apply cross-over and mutation to create a new offspring configuration.
        7. Repeat step 6 till we have "population_size" next-generation configurations.
        8. repeat step 2-7 until [meet $max_generation or achieve $improvement_threshold]
        :return:
        '''

        # step 1
        def_conf = self.conf_space.get_default_conf(util.important_params)
        print 'Default configuration:\n', def_conf
        def_perf = self.profiler.profile(0, def_conf)
        if def_perf == sys.maxsize:
            print 'profile default configuration failed, exit...'
            sys.exit(-1)
        print time.strftime("%Y-%d-%m %H:%M:%S"), 'Default benchmark done! Performance: ', def_perf

        best_conf = def_conf
        best_perf = def_perf

        # step 2
        parent_confs = self.get_initial_confs()
        self.generation_index = 1
        self.improvement = sys.maxsize
        last_gen_best_perf = def_perf
        best_generation = 1
        while self.generation_index <= self.max_generation or (best_perf*1.0-def_perf)/best_perf >= self.global_improvement:
            # profile all parent configurations
            real_perfs = self.profile_confs(parent_confs)
            self.generation_index += 1
            # step 3: remove invalid configurations
            parent_confs, real_perfs = self.remove_invalid_confs_by_perf(parent_confs, real_perfs)
            if len(parent_confs) == 0:
                # no valid configurations, then we create another set of initial configurations
                parent_confs = self.get_initial_confs()
                continue
            # sort configurations by performance
            parent_confs, real_perfs = self.sort_confs_by_perfs(parent_confs, real_perfs)

            # step 4: select the best configuration in this generations
            curr_best_conf, curr_best_perf = parent_confs[0], real_perfs[0]
            print '=== Best performance in generation', self.generation_index, ' === performance:', curr_best_perf
            if curr_best_perf <= best_perf:
                best_perf = curr_best_perf
                best_conf = curr_best_conf
                best_generation = self.generation_index
            # self.improvement = (best_perf - curr_best_perf) / (best_perf*1.0)

            # step 5: now parent configurations are sorted, we select confs by $local_improvement
            confs_to_evolve = []
            for i, p in enumerate(real_perfs):
                local_imp = (last_gen_best_perf - p*1.0)/last_gen_best_perf
                if local_imp >= self.local_improvement:
                    confs_to_evolve.append(parent_confs[i])

            last_gen_best_perf = curr_best_perf
            if len(confs_to_evolve) < max(self.population_size/10, 2):
                print '=== configurations to evolve less than self.population_size/10 ==='
                '''
                TODO: is this correct??
                what should we do if ---
                   the current generation has no better configuration than the best one in last generation?
                the current logic is to add parents into offspring (called elitism in some evolutionary algorithms),
                and continue to evolve till the maximum number of generations reached
                '''
                confs_to_evolve.extend(parent_confs)

            # step 6 and 7: create offspring configurations
            new_parents = []
            for i in range(self.population_size):
                parent1, parent2 = random.sample(confs_to_evolve, 2)
                new_conf = self.create_offspring(parent1, parent2)
                new_parents.append(new_conf)
            parent_confs = list(new_parents)
            # step 8: repeat

        if self.generation_index > self.max_generation:
            print '=== The GA algorithm ends because reach maximum generation ====='
        else:
            print '=== The GA algorithm ends because reach performance threshold ====='
        print 'Invalid configurations:'
        print self.invalid_confs
        return best_generation, best_conf, best_perf

    def converged(self):
        if self.generation_index <= 1:
            return False
        if self.improvement < self.global_improvement:
            return True
        return False

    def remove_invalid_confs_by_perf(self, confs, perfs):
        new_confs = []
        new_perfs = []
        for i, p in enumerate(perfs):
            if p < sys.maxsize:
                new_confs.append(confs[i])
                new_perfs.append(p)
        return new_confs, new_perfs

    def old_run(self):
        '''
        1. get a set of initial configurations (These are parent configurations)
        2. predict/evaluate them for performance (or maybe predict them??)
        3. Find N best predicted configurations to dynamically profile and find the best one
        4. Take these N configurations to evolve (take half of the parameter and exchange and then update M)
        5. get a set of offspring configurations to repeat step 1
        6. Ends till G generations
        :return:
        '''
        best_conf = None
        best_perf = sys.maxsize

        parent_confs = self.get_initial_confs()
        generation_index = 1
        best_generation = 1
        # best_dynamic_profile_num = 1
        while generation_index < self.max_generation:
            # predict performance of parent configurations
            pred_parent_perfs = self.predict_N_conf_perf(parent_confs)
            print 'Generation:', generation_index, '\t=== prediction finished ==='
            parent_confs, pred_parent_perfs = self.sort_confs_by_perfs(parent_confs, pred_parent_perfs)

            # select N to dynamically benchmark to select the best one
            if len(parent_confs) < self.conf_to_profile:
                self.conf_to_profile = len(parent_confs)
            confs_to_profile = random.sample(parent_confs, self.conf_to_profile)
            real_perfs = self.profile_confs(confs_to_profile)
            # best_dynamic_profile_num += len(confs_to_profile)
            curr_best_conf, curr_best_perf = self.select_top_N_conf_by_perf(confs_to_profile, real_perfs, 1)
            curr_best_conf, curr_best_perf = curr_best_conf[0], curr_best_perf[0]

            print 'Best performance in this generation: ', curr_best_perf
            if curr_best_perf <= best_perf:
                best_perf = curr_best_perf
                best_conf = curr_best_conf
                best_generation = generation_index

            # now parent configurations are sorted, we select half best ones to evolve
            confs_to_evolve = random.sample(parent_confs, len(parent_confs)/2)
            # add some profiled configurations to evolve
            sorted_profiled_confs = self.sort_confs_by_perfs(confs_to_profile, real_perfs)
            confs_to_evolve.extend(sorted_profiled_confs[:len(confs_to_profile)*3/2])
            if len(confs_to_evolve) == 0:
                break
            # print 'generation', generation_index, 'evovling is finished'
            # parent_confs = self.evolve(best_conf, confs_to_evolve)
            parent_confs = self.evolve(curr_best_conf, confs_to_evolve)
            generation_index += 1
        return best_generation, best_conf, best_perf

    def create_offspring(self, parent1, parent2):
        offspring = parent1.copy()
        # random select half parameters to crossover
        crossover_params = random.sample(parent1.keys(), len(parent1)/2)
        for p in crossover_params:
            offspring[p] = parent2.get(p)

        mutate_params = random.sample(crossover_params, int(len(parent1)*0.06))
        for p in mutate_params:
            strategy = self.pss.get_strategy()
            if strategy is None:
                print 'No strategy found for:', p
                continue
            next_val = strategy.next_value()
            if next_val is None:
                continue
            next_val = str(next_val)
            if 'java.opt' in p:
                next_val = '-Xmx' + next_val + 'm'
            offspring[p] = next_val
            # values = self.conf_space.param_values[p]
            # values = [v.value for v in values]
            # '''
            # This is a new implementation. For numerical parameters, we select values from a range.
            # '''
            # v = ''
            # p_data_type = util.parameters.get(p.lower().strip()).data_type
            # if p_data_type in [ConfDataType.float, ConfDataType.integer]:
            #     if p_data_type is ConfDataType.float:
            #         values = [float(v) for v in values]
            #         values = sorted(values)
            #         v = random.uniform(values[0], values[-1])
            #         v = "{0:.2f}".format(v)
            #     else:
            #         values = [int(v) for v in values]
            #         values = sorted(values)
            #         v = random.randint(values[0], values[-1])
            #         v = str(v)
            # else:
            #     v = random.choice(values)
            # offspring[p] = v
        return offspring

    def evolve(self, best_conf, parents):
        '''
        The evolving step of genetic algorithm.
        :param best_conf:
        :param parents:
        :return:
        '''
        # first find parameters to mutate
        params_to_exchange = random.sample(best_conf.keys(), len(best_conf)/2)
        offspring_confs = []
        for cnf in parents:
            new_cnf = cnf.copy()
            # first exchange
            for p in params_to_exchange:
                new_cnf[p] = best_conf[p]
            # then mutate
            params_to_mutate = random.sample(params_to_exchange, len(params_to_exchange)/2)
            for p in params_to_mutate:
                values = self.conf_space.param_values[p]
                values = [v.value for v in values]
                '''
                This is a new implementation. For numerical parameters, we select values from a range.
                '''
                v = ''
                p_data_type = util.parameters.get(p.lower().strip()).data_type
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
                # print 'mutation step ==== parameter:', p, '==value:', v
                new_cnf[p] = v
            offspring_confs.append(new_cnf)
        # here we remove duplicate configurations by semantics
        # offspring_confs = self.hadoop_semantics.remove_dup_confs(offspring_confs)
        return offspring_confs

    def profile_confs(self, confs):
        # print 'Enter profile_confs'
        real_perfs = []
        for index, cnf in enumerate(confs):
            # type checker for cnf
            if not self.type_checker.check(self.profile_num, cnf):
                print 'type-checking failed, config', str(self.profile_num)
                self.invalid_confs.append(self.profile_num)
                genconf_folder = self.curr_genconf_folder + str(self.profile_num)
                util.make_folder_ready(genconf_folder)
                tmp_conf = cnf.copy()
                for p, v in self.profiler.original_confs.iteritems():
                    tmp_conf[p] = v
                util.write_into_conf_file(tmp_conf, genconf_folder)
                self.profile_num += 1
                real_perfs.append(sys.maxsize)
                continue
            perf = self.profiler.profile(self.profile_num, cnf)
            print time.strftime("%Y-%d-%m %H:%M:%S"), self.profile_num, 'benchmark done! Performance: ', perf
            self.profile_num += 1
            real_perfs.append(perf)
        return real_perfs

    def sort_confs_by_perfs(self, confs, perfs):
        sorted_perfs = sorted(perfs)
        sorted_confs = []
        for i in range(len(sorted_perfs)):
            p_index = perfs.index(sorted_perfs[i])
            sorted_confs.append(confs[p_index])
        return sorted_confs, sorted_perfs

    def select_top_N_conf_by_perf(self, confs, perfs, N):
        if N > len(confs):
            print 'N is larger than the number of configurations'
            return None
        # first sort perf
        tmp_perfs = list(perfs)
        sorted_perfs = sorted(tmp_perfs)
        sorted_confs = []
        for i in range(N):
            p_index = perfs.index(sorted_perfs[i])
            sorted_confs.append(confs[p_index])
        return sorted_confs[:N], sorted_perfs[:N]

    def predict_N_conf_perf(self, confs):
        perfs = []
        for c in confs:
            p = self.predictor.predict(c, c.keys())
            perfs.append(p)
        return perfs

    def get_initial_confs(self):
        '''
        # Initial configurations do not need to consider the hierarchy structure.
        # So we do not need to do that here, only in the evolution steps.
        '''
        #params_to_exploit = self.predictor.important_feature_from_model
        # params_to_exploit = util.important_params
        params = self.conf_space.parameters
        print 'length of params:', len(params)
        # hierarchy_structure = self.hadoop_semantics.get_partial_structure(params_to_exploit)
        # child_parent = slef.hadoop_semantics.get_parent(params_to_exploit)
        conf_set = []
        for i in range(self.population_size):
            new_conf = {}
            for p in params:
                strategy = self.pss.get_strategy(p)
                if strategy is None:
                    continue
                val = strategy.next_value()
                if val is None:
                    print 'no value found for:', p
                val = str(val)
                if 'java.opt' in p:
                    val = '-Xmx' + val + 'm'
                new_conf[p] = val
                # values = self.conf_space.param_values.get(p)
                # random_v = random.choice(values)
                # new_conf[p] = random_v.value
            # print new_conf.values()
            conf_set.append(new_conf)
        # conf_set = self.hadoop_semantics.remove_dup_confs(conf_set)
        return conf_set
