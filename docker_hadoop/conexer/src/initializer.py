# from searcher import Genetic
from space_expl_framework import HadoopProfiler
# from improve_spark import SparkProfiler
# from improve_spark import SparkConfSpace
from space_expl_framework import ConfSpace
from space_expl_framework import Genetic
from space_expl_framework import MCMC
from space_expl_framework import Config

target_system  = 'Hadoop'
# target_system  = 'Spark'

def run(target_system, conf_file, confspace, exp_algo, profiler):
    my_algo = exp_algo(conf_file, confspace, profiler)
    my_algo.population_size = 200
    my_algo.global_improvement = 0.8
    my_algo.local_improvement = 0.01
    my_algo.max_generation = 30
    # my_profiler = profiler()
    best_iter, conf, perf = my_algo.run()
    print 'best iteration\t\t', best_iter
    print 'best configuration\t\t', conf
    print 'CPU performance\t\t', perf

# run(target_system, Genetic, HadoopProfiler)
# run(target_system, CoordinateDescent, HadoopProfiler)
# conf = Config('conf_spark.ini')
conf_file = Config('conf.ini')
# run(target_system, conf_file, SparkConfSpace, Genetic, SparkProfiler)
run(target_system, conf_file, ConfSpace, MCMC, HadoopProfiler)
print 'Done!'
