from glob import glob
import subprocess as subproc
from ipdb import set_trace
from pathlib import Path
import pandas as pd


def run_os_cmd(cmd_str):
    """ Run the command string
    Parameters
    ----------
    cmd_str: str
        The command to execute

    Returns
    -------
    int:
        The return code
    """
    return_code = subproc.call(cmd_str, shell=True)
    return return_code


def main():
    # # Copy the HiBench Config over the master node
    # run_os_cmd("docker cp config/hibench.conf hadoop-master:/root/HiBench/conf/")

    # # Run default configurations
    # run_os_cmd(
    #     "docker exec -it hadoop-master /root/HiBench/bin/run_all.sh")
    # run_os_cmd(
    #     "docker exec -it hadoop-master cat /root/HiBench/report/wordcount/hadoop/bench.log | grep 'CPU time spent' | sed 's/\t//g' | sed 's/CPU time spent (ms)=//g' | tee -a wc_scale_up_small_to_large.txt")

    # # Backup default hadoop configurations
    # run_os_cmd(
    #     "docker exec -it hadoop-master cp -r /usr/local/hadoop-2.7.4/etc/hadoop/ /root/hadoop_defaults")

    # cur_dir = Path.cwd()
    # res_dir = cur_dir.joinpath("results")
    # small_res = pd.read_csv(res_dir.joinpath("hadoop_small_results.csv"))
    # small_res = small_res.sort_values(
    #     by="Perf").reset_index(drop=True).iloc[48:50]
    # working_confs = set(small_res["Conf"].values.astype("str").tolist())

    # # Loop through every folder
    # for conf_dir in res_dir.glob("*/"):
    #     if conf_dir.name[4:] in working_confs:
    #         # -- Save the configs --
    #         run_os_cmd("echo {} >> top_50_confs.txt".format(conf_dir.name[4:])

    #         # -- Copy over all the configurations to the master node --
    #         for conf_file in conf_dir.glob("*.xml"):
    #             run_os_cmd(
    #                 "docker cp {} hadoop-master:/usr/local/hadoop-2.7.4/etc/hadoop/".format(str(conf_file)))

    #         # -- Run HiBench and gather the runtime --
    #         run_os_cmd(
    #             "docker exec -it hadoop-master /root/HiBench/bin/run_all.sh")

    #         run_os_cmd(
    #             "docker exec -it hadoop-master cat /root/HiBench/report/wordcount/hadoop/bench.log | grep 'CPU time spent' | sed 's/\t//g' | sed 's/CPU time spent (ms)=//g' | tee -a scale_up_small_to_huge.txt")


if __name__ == "__main__":
    main()
