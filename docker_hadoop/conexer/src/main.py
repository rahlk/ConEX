#!/usr/bin/env python
from searcher import Searcher
import sys
from profiler import Profiler
from conf_space import ConfSpace
from space_expl_framework import MCMC
from util import util
from sysconf import cfg

"""
This is the main entry of this program.
This program has three main components:
1. value generator is used to generate the whole configuration space
2. heuristic searching is used to search in the space
3. profiler is used to profile the performance of a new configuration
"""

"""
1. working on the value/configuration space generator:
    a. how to generate a random/rule-based value for a parameter
2. core algorithms to search configuration space
3. profiling...
"""

N = 300
if len(sys.argv) > 1:
    N = int(sys.argv[1])
'''
Before starting the search algorithm, we evaluate performance of the default configuration.
'''
# my_profiler = Profiler()
# my_conf_space = ConfSpace()
# tmp_conf = my_conf_space.get_default_conf()
# def_conf = dict()
# for k in util.important_params:
#     def_conf[k] = tmp_conf[k].value
# # print def_conf
# cpu_time = my_profiler.profile(0, def_conf)
# print 'Default performance:', cpu_time
# print 'iterations: ', N
# explorer = Searcher()
# best_iter, conf, perf = explorer.hill_climbing.run(N)
# best_iter, conf, perf = explorer.genetic.run()
# best_iter, conf, perf = explorer.coordinate_descent.run()
# best_iter, conf, perf = explorer.genetic.run_vanilla_GA()

# conf = Config('conf.ini')
mcmc = MCMC(cfg, ConfSpace, Profiler)
best_iter, conf, perf = mcmc.run()
print 'best iteration\t\t', best_iter
print 'best configuration\t\t', conf
print 'CPU performance\t\t', perf


# total_saved = 0
# for i in range(0, 100):
#     total, single_save = explorer.coordinate_descent.test_feature_engineering()
#     total_saved += single_save
#     # print i, '===total:', total, '===single_save:', single_save

# print 'total save:', total_saved/100.0
