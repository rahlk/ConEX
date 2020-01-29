Require Import String.
Open Scope string_scope.
Require Export core_config.
Require Export mapred_config.
Require Export hdfs_config.
Require Export yarn_config.
Require Export env_desc.
Require Import ZArith.
Require Import Reals.
Open Scope Z_scope.

(*
Here is a Hadoop configuration. It's a compound system built based on sub-components.
It also contains a few dependent types and constrains.
*)
Record HadoopConfig := mk_hadoop_config {
  yarn_config: YarnConfig
 ;mapred_config: MapRedConfig
 ;core_config: CoreConfig
 ;hdfs_config: HDFSConfig

  (* Cross-component constraints *)

  (* we cast the positive value to be of type Z so we can use omega in the proofs later *)
 ;mr_mem_lt_yarn_mem: 
     (Zpos (mapreduce_map_memory_mb.value (mapreduce_map_memory_mb mapred_config))) <
     (Zpos (yarn_nodemanager_resource_memory__mb.value (yarn_nodemanager_resource_memory__mb yarn_config)))
 ;mr_core_lt_yarn_core:
    (Zpos (mapreduce_map_cpu_vcores.value (mapreduce_map_cpu_vcores mapred_config))) <
    (Zpos (yarn_nodemanager_resource_cpu__vcores.value (yarn_nodemanager_resource_cpu__vcores yarn_config)))
}.
