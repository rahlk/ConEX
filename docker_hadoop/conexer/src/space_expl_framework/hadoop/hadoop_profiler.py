import os
import subprocess
import sys
# import random
import time
from sysconf import cfg
from util import util
import numpy as np
import xml.etree.ElementTree as ElementTree
from space_expl_framework.abs_classes import AbstractProfiler

class HadoopProfiler(AbstractProfiler):
    def __init__(self):
        self.itertime = 1
        # Here are some critical settings
        self.original_confs = self.parse_orig_confs() # Chong
        self.hadoop_conf_home = os.sep.join([str(cfg.hadoop_home), 'etc', 'hadoop'])
        self.avg_run_time = 2000    # seconds
        self.hibench_output = ''

    def parse_orig_confs(self):
        orig_conf = {}
        hadoop_home = cfg.hadoop_home
        hadoop_conf_home = os.sep.join([hadoop_home, 'etc', 'hadoop'])
        files = ['mapred-site.xml', 'core-site.xml', 'yarn-site.xml', 'hdfs-site.xml']
        for f in files:
            full_path = hadoop_conf_home + os.sep + f
            root = ElementTree.parse(full_path).getroot()
            properties = root.findall('property')
            for p in properties:
                prop = p.find('name').text
                if prop is None:
                    #print 'parsed wrong property'
                    continue
                value = p.find('value').text
                if value is None:
                    value = ''
                orig_conf[prop] = value
        # print 'Chong: original configurations: ', orig_conf
        return orig_conf

    def start(self):
        self.backup_folder = 'backup'
        util.make_folder_ready(self.backup_folder)
        # read original hadoop configurations
        self.backup_original_confs()

    def finish(self):
        self.restore_hadoop_confs()

    def backup_original_confs(self):
        '''
        Some parameters related to resource have to be set correctly/
        They are not configurable in a specific cluster. So we back up them and merge them with a new configuration.
        This function will do two things.
        1. copy the original Hadoop configuration files to a new folder
        2. parse the original configuration files and save them in a dictionary
        :return:
        '''
        # confs = []
        conf_files = ['mapred-site.xml', 'core-site.xml', 'yarn-site.xml', 'hdfs-site.xml']
        for conf_file in conf_files:
            if cfg.platform == 'aws':
                cmd = ' '.join(['sudo cp', self.hadoop_conf_home + os.sep + conf_file, self.backup_folder])
            else:
                cmd = ' '.join(['cp', self.hadoop_conf_home + os.sep + conf_file, self.backup_folder])
            self.run_cmd(cmd)

    def profile(self, conf):
        print 'hadoop profiler called()'
        return sys.maxsize

    def profile(self, itertime, in_conf):
        '''
        Profile the Hadoop system with the given configuration
        :param conf: a new configuration
        :return: performance
        '''
        # return itertime
        conf = in_conf.copy()
        self.itertime = itertime
        # prepare the system with new configurations
        # generate configuration files
        self.curr_genconf_folder = cfg.gen_confs + os.sep + 'conf' + str(self.itertime)
        util.make_folder_ready(self.curr_genconf_folder)
        # now merge the original configurations with new ones
        for p, v in self.original_confs.iteritems():
            # if p not in conf:
                #      print 'new configuration tries to update the old one:', p
            conf[p] = v
        # the default configuration
        # print itertime
        # if itertime == 0:
        #     print conf
        # print 'Chong: updated configs: ', conf
        confs = util.write_into_conf_file(conf, self.curr_genconf_folder)

        self.copy_new_conf(confs)
        '''
        No need to restart Hadoop. Only need to copy new configuration files to
        the configuration folder on Master node.
        HiBench will use those configuration files when submit a new job.
        '''
        # if self.restart_hadoop_with_new_conf(confs) != 0:
        #     print 'Error....prepare system failed.'
        #     return sys.maxsize

        # profile the system to get its performance
        # execute HiBench here
        cpu_times = []
        for i in range(3):
            success, elapsed_time = self.call_benchmark()
            # print 'profile time: ', elapsed_time
            if success:
                cpu_time = self.get_cpu_time_from_output()
                cpu_times.append(cpu_time)
            else:
                # clear output of the last run
                self.hibench_output = ''
                # clear cpu_times
                cpu_times = []
                # if any one of these runs failed, that means this configuration is bad
                # no need to test more, fail fast
                break
        cpu_times = [t for t in cpu_times if t < sys.maxsize]
        average_cpu_time = sys.maxsize   # maximum time
        if len(cpu_times) > 0:
            average_cpu_time = np.mean(cpu_times)
        return int(average_cpu_time)

    def call_benchmark(self):
        '''
        This function will call HiBench benchmark suites to test the system performance.
        :return: the time performance (Note: This is different as CPU_MILLISECONDS reported by Hadoop)
        '''
        success = True
        hibench_home = cfg.hibench_home
        run_all_script = os.sep.join(['./'+hibench_home, 'bin', 'run_all.sh'])
        # run_all_script = run_all_script + '> /dev/null'
        # print run_all_script
        start_time = time.time()
        success = self.run_benchmark_cmd(run_all_script)
        if not success:
            print 'run benchmark command is not success, exit..'
        end_time = time.time()
        elapsed = end_time - start_time
        if success is True:
            self.avg_run_time = elapsed * 2
        # if cfg.platform == 'docker':
        #     self.kill_useless_process()
        # print 'time to finish profile: ', self.avg_run_time
        return success, elapsed

    def wait_timeout(self, proc, seconds):
        # Wait for a process to finish, or raise exception after timeout
        start = time.time()
        end = start + seconds
        interval = 1  # query every 1s
        self.stderr = ''
        while True:
            #print 'waiting...'
            result = proc.poll()
            self.stderr += proc.stderr.read()
            if result is not None:
                return result
            if time.time() > end:
                # raise RuntimeError("Process timed out")
                print 'wait timeout:', seconds, 'kill process..., avg_run_time:', self.avg_run_time
                return -100  # -100 as the error code
            time.sleep(interval)

    def run_benchmark_cmd(self, cmd):
        ret = True
        try:
            # Using PIPE here could cause a deadlock problem. When there is too much content in stdout or stderr,
            # the PIPE will be full and process will hang
            cmd = cmd.split(' ')
            p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            wait_result = self.wait_timeout(p, self.avg_run_time)
            stdout, stderr = p.communicate()
            return_code = p.returncode
            if wait_result == 0 or return_code == 0:
                self.hibench_output = self.stderr
            elif wait_result == -100:
                # print cmd
                # print stdout
                # print stderr
                p.kill()
                ret = False
            else:
                # print '***return is not 0 *** cmd:', cmd, 'return code:', return_code
                # print stdout
                # print '============='
                # print '============='
                # print stderr
                ret = False
        except Exception as e:
            # print 'Profiler: execute', cmd, 'failed. Exit msg =', e.message
            # print 'error message:', e.output
            # self.restore_hadoop_confs()
            ret = False
        return ret

    def get_cpu_time_from_output(self):
        find_real_job = False
        find_reduce_job = False
        times = []
        start_line = 'map-reduce framework'
        reduce_line = 'reduce'
        for line in self.hibench_output.split('\n'):
            # print line
            line = line.strip().lower()
            # if '_0002 completed successfully' in line:
            if start_line in line:
                find_real_job = True
                # print 'found job'
            if line.startswith(reduce_line):
                find_reduce_job = True

            if find_real_job and find_reduce_job and 'cpu time spent' in line:
                time = int(line.split('=')[-1])
                times.append(time)
                find_real_job = False
                find_reduce_job = False
        self.hibench_output = ''
        # if error, returns sys.maxsize
        # print 'times:', times
        if len(times) == 0:
            return sys.maxsize
        # print times
        return sum(times)

    def kill_useless_process(self):
        killall_ssh = 'killall ssh'
        self.run_cmd(killall_ssh)
        # killall python processs on slave nodes
        slave_nodes = ['hadoop-slave1', 'hadoop-slave2', 'hadoop-slave3', 'hadoop-slave4']
        for s in slave_nodes:
            kill_python = 'ssh ' + s + ' \"ps -ef|grep \'socket.SOCK\'|awk \'{ print \$2 }\' |xargs kill\"'
            # kill_python = 'ssh ' + s + ' killall python'
            self.run_cmd(kill_python)

    def run_multiple_cmds(self, cmds):
        for cmd in cmds:
            #print 'run command:', cmd
            if not self.run_cmd(cmd):
                return False
        return True

    def run_cmd(self, cmd):
        devnull = open(os.devnull, 'w')
        return_code = subprocess.call(cmd, shell=True, stdout=devnull, stderr=devnull)
        devnull.close()
        #print return_code
        if return_code == 0:
            #print 'run', cmd, 'success'
            return True
        else:
            print 'cmd', cmd, '===return is not 0:', return_code
            return True

    def restart_hadoop_with_new_conf(self, confs):
        # stop hadoop first
        stop_all = []
        start_all = []
        # if cfg.platform == 'docker':
        #     stop_all = [os.sep.join([cfg.hadoop_home, 'sbin', 'stop-all.sh'])]
        #     start_all = [os.sep.join([cfg.hadoop_home, 'sbin', 'start-all.sh'])]
        # elif cfg.platform == 'aws':
        #     stop_all = ['sudo stop hadoop-yarn-resourcemanager']
        #     start_all = ['sudo start hadoop-yarn-resourcemanager']
        if cfg.platform == 'aws':
            stop_all = ['sudo stop hadoop-yarn-resourcemanager']
            start_all = ['sudo start hadoop-yarn-resourcemanager']
        else:
            stop_all = [os.sep.join([cfg.hadoop_home, 'sbin', 'stop-all.sh'])]
            start_all = [os.sep.join([cfg.hadoop_home, 'sbin', 'start-all.sh'])]
        if not self.run_multiple_cmds(stop_all):
            print 'Stop Hadoop failed, return...'
            return -1
        # copy the new configuration into place
        self.copy_new_conf(confs)
        # then start hadoop
        if not self.run_multiple_cmds(start_all):
            print 'Start Hadoop failed, return...'
            return -1
        leave_safe_mode = 'hdfs dfsadmin -safemode get'
        leave_safe_mode = leave_safe_mode.split(' ')
        while True:
            output = subprocess.check_output(leave_safe_mode)
            if output.lower().strip() == 'safe mode is off':
                break
            time.sleep(1)
        return 0

    def restore_hadoop_confs(self):
        files_to_copy = [self.backup_folder + os.sep + f for f in os.listdir(self.backup_folder)]
        if cfg.platform == 'aws':
            cmd = ' '.join(['sudo cp', ' '.join(files_to_copy), self.hadoop_conf_home])
        else:
            cmd = ' '.join(['cp', ' '.join(files_to_copy), self.hadoop_conf_home])
        self.run_cmd(cmd)

    def copy_new_conf(self, confs):
        '''
        Copy configuration files to slave nodes using ssh
        1. get all slave nodes from hadoop configuation files "slaves"
        2. construct command to copy configuration files

        Actually, there is no need to copy files to slave nodes.
        HiBench will use the configuration files on the master node to submit jobs.
        '''
        # slave_nodes = self.get_slave_nodes()

        files_to_copy = ''
        for file_name in confs:
            files_to_copy += self.curr_genconf_folder + os.sep + file_name + ' '

        # copy configuration files to master node
        master_target_folder = self.hadoop_conf_home
        if cfg.platform == 'aws':
            copy_cmd = ' '.join(['sudo cp', files_to_copy, master_target_folder])
        else:
            copy_cmd = ' '.join(['cp', files_to_copy, master_target_folder])
        self.run_cmd(copy_cmd)
        # copy to slave nodes
        # for snode in slave_nodes:
        #     slave_target_folder = snode + ':' + self.hadoop_conf_home
        #     # TODO: Chong: things are complicated when run this on AWS
        #     # On AWS, we need "sudo" to save files into hadoop configuration folder
        #     # we ignore that for now but fix it later
        #     copy_cmd = ' '.join(['scp', files_to_copy, slave_target_folder])
        #     self.run_cmd(copy_cmd)


        # for file_name in confs:
        #     original_file = self.curr_genconf_folder + os.sep + file_name
        #     target_folder = self.hadoop_conf_home
        #     copy_cmd = ''
        #     # copy to master node
        #     if cfg.platform == 'aws':
        #         copy_cmd = ' '.join(['sudo cp', original_file, target_folder])
        #     else:
        #         copy_cmd = ' '.join(['cp', original_file, target_folder])
        #     self.run_cmd(copy_cmd)


        #     for snode in slave_nodes:
        #         copy_cmd = ' '.join([scp ])
        return True

    def get_slave_nodes(self):
        slave_nodes = []
        slaves_file = os.sep.join([self.hadoop_conf_home, 'slaves'])
        with open(slaves_file, 'r') as fp:
            for node in fp:
                node = node.strip()
                if node.startswith('#'):
                    continue
                slave_nodes.append(node)
        return slave_nodes
