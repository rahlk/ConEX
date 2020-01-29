Require Import hadoop_config.
Require Import Reals.
Open Scope R_scope.

Definition a_core_config: CoreConfig.
Proof.
unshelve refine (
    mk_core_config
    (io_file_buffer_size.mk false 65536%positive _ )
    (io_map_index_interval.mk false 128%positive _ )
    (io_map_index_skip.mk false 2%N _ )
    (io_seqfile_compress_blocksize.mk false 800000%positive _ )
    (io_seqfile_sorter_recordlimit.mk false 800000%positive _ )
    (ipc_maximum_data_length.mk false 74000000%positive _ )
); try (exact I); try compute; auto.
Qed.


Definition a_hdfs_config: HDFSConfig.
Proof.
unshelve refine (
    mk_hdfs_config
    (dfs_namenode_handler_count.mk false 10%positive _ )
    (dfs_replication.mk false 1%positive _ )
); try (exact I).
Qed.


Definition a_mapred_config: MapRedConfig.
Proof.
unshelve refine (
    mk_mapred_config
    (mapred_child_java_opts.mk false "-Xmx180m" _ )
    (mapred_map_output_compression_type.mk false "BLOCK" _ )
    (mapreduce_ifile_readahead.mk false false _ )
    (mapreduce_ifile_readahead_bytes.mk false 6291456%positive _ )
    (mapreduce_input_fileinputformat_split_maxsize.mk false 184217728%positive _ )
    (mapreduce_input_fileinputformat_split_minsize.mk false 335544320%N _ )
    (mapreduce_input_lineinputformat_linespermap.mk false 8%positive _ )
    (mapreduce_job_counters_max.mk false 160%positive _ )
    (mapreduce_job_jvm_numtasks.mk false (4)%Z _ )
    (mapreduce_job_max_split_locations.mk false 14%positive _ )
    (mapreduce_job_reduce_slowstart_completedmaps.mk false (10/100)%R _ )
    (mapreduce_job_reducer_unconditional__preempt_delay_sec.mk false 300%positive _ )
    (mapreduce_job_running_map_limit.mk false 0%Z _ )
    (mapreduce_job_running_reduce_limit.mk false 2%Z _ )
    (mapreduce_job_speculative_minimum__allowed__tasks.mk false 16%positive _ )
    (mapreduce_job_speculative_retry__after__no__speculate.mk false 800%positive _ )
    (mapreduce_job_speculative_retry__after__speculate.mk false 12000%positive _ )
    (mapreduce_job_speculative_speculative__cap__running__tasks.mk false (8/100)%R _ )
    (mapreduce_job_speculative_speculative__cap__total__tasks.mk false (6/100)%R _ )
    (mapreduce_job_split_metainfo_maxsize.mk false 9000000%Z _ )
    (mapreduce_job_ubertask_enable.mk false false _ )
    (mapreduce_job_ubertask_maxmaps.mk false 13%positive _ )
    (mapreduce_job_ubertask_maxreduces.mk false 6%positive _ )
    (mapreduce_jobtracker_expire_trackers_interval.mk false 480000%positive _ )
    (mapreduce_jobtracker_handler_count.mk false 6%positive _ )
    (mapreduce_jobtracker_maxtasks_perjob.mk false (-1)%Z _ )
    (mapreduce_jobtracker_taskcache_levels.mk false 5%positive _ )
    (mapreduce_map_cpu_vcores.mk false 4%positive _ )
    (mapreduce_map_java_opts.mk false "-Xmx1152m" _ )
    (mapreduce_map_maxattempts.mk false 6%positive _ )
    (mapreduce_map_memory_mb.mk false 1200%positive _ )
    (mapreduce_map_output_compress.mk false true _ )
    (mapreduce_map_output_compress_codec.mk false "org.apache.hadoop.io.compress.BZip2Codec" _ )
    (mapreduce_map_skip_maxrecords.mk false 3%N _ )
    (mapreduce_map_skip_proc_count_autoincr.mk false true _ )
    (mapreduce_map_sort_spill_percent.mk false (88/100)%R _ )
    (mapreduce_map_speculative.mk false true _ )
    (mapreduce_output_fileoutputformat_compress.mk false false _ )
    (mapreduce_output_fileoutputformat_compress_codec.mk false "org.apache.hadoop.io.compress.DefaultCodec" _ )
    (mapreduce_output_fileoutputformat_compress_type.mk false "NONE" _ )
    (mapreduce_reduce_cpu_vcores.mk false 3%positive _ )
    (mapreduce_reduce_input_buffer_percent.mk false (40/100)%R _ )
    (mapreduce_reduce_java_opts.mk false "-Xmx2816m" _ )
    (mapreduce_reduce_markreset_buffer_percent.mk false (0/100)%R _ )
    (mapreduce_reduce_maxattempts.mk false 6%positive _ )
    (mapreduce_reduce_memory_mb.mk false 1200%positive _ )
    (mapreduce_reduce_merge_inmem_threshold.mk false 1000%Z _ )
    (mapreduce_reduce_shuffle_input_buffer_percent.mk false (50/100)%R _ )
    (mapreduce_reduce_shuffle_memory_limit_percent.mk false (20/100)%R _ )
    (mapreduce_reduce_shuffle_merge_percent.mk false (75/100)%R _ )
    (mapreduce_reduce_shuffle_parallelcopies.mk false 5%positive _ )
    (mapreduce_reduce_shuffle_retry__delay_max_ms.mk false 540000%positive _ )
    (mapreduce_shuffle_max_connections.mk false 10%N _ )
    (mapreduce_shuffle_max_threads.mk false 4%N _ )
    (mapreduce_shuffle_transfer_buffer_size.mk false 166608%positive _ )
    (mapreduce_task_combine_progress_records.mk false 11000%positive _ )
    (mapreduce_task_io_sort_factor.mk false 8%positive _ )
    (mapreduce_task_io_sort_mb.mk false 80%positive _ )
    (mapreduce_task_merge_progress_records.mk false 8000%positive _ )
    (mapreduce_task_profile_maps.mk false "1-3" _ )
    (mapreduce_task_profile_reduces.mk false "3-5" _ )
    (mapreduce_tasktracker_http_threads.mk false 50%positive _ )
    (mapreduce_tasktracker_indexcache_mb.mk false 10%positive _ )
    (mapreduce_tasktracker_map_tasks_maximum.mk false 2%positive _ )
    (mapreduce_tasktracker_reduce_tasks_maximum.mk false 3%positive _ )
    (mapreduce_tasktracker_taskmemorymanager_monitoringinterval.mk false 5000%positive _ )
      _
).
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I). simpl. try compute. try reflexivity. auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
try (exact I); simpl; try compute; try reflexivity; auto.
Qed.


Definition a_yarn_config: YarnConfig.
Proof.
unshelve refine (
    mk_yarn_config
    (yarn_app_mapreduce_am_command__opts.mk false "-Xmx800m" _ )
    (yarn_app_mapreduce_am_containerlauncher_threadpool__initial__size.mk false 8%positive _ )
    (yarn_app_mapreduce_am_job_task_listener_thread__count.mk false 20%positive _ )
    (yarn_app_mapreduce_am_resource_cpu__vcores.mk false 1%positive _ )
    (yarn_app_mapreduce_am_resource_mb.mk false 3200%positive _ )
    (yarn_nodemanager_container__manager_thread__count.mk false 16%positive _ )
    (yarn_nodemanager_localizer_client_thread__count.mk false 5%positive _ )
    (yarn_nodemanager_localizer_fetch_thread__count.mk false 6%positive _ )
    (yarn_nodemanager_recovery_compaction__interval__secs.mk false 3600%positive _ )
    (yarn_nodemanager_resource_cpu__vcores.mk false 18%positive _ )
    (yarn_nodemanager_resource_memory__mb.mk false 16384%positive _ )
    (yarn_nodemanager_resource_percentage__physical__cpu__limit.mk false 80%positive _ )
    (yarn_nodemanager_vmem__check__enabled.mk false true _ )
    (yarn_nodemanager_vmem__pmem__ratio.mk false (210/100)%R _ )
    (yarn_nodemanager_windows__container_cpu__limit_enabled.mk false false _ )
    (yarn_nodemanager_windows__container_memory__limit_enabled.mk false true _ )
    (yarn_resourcemanager_admin_client_thread__count.mk false 5%positive _ )
    (yarn_resourcemanager_amlauncher_thread__count.mk false 40%positive _ )
    (yarn_resourcemanager_client_thread__count.mk false 60%positive _ )
    (yarn_resourcemanager_ha_enabled.mk false true _ )
    (yarn_resourcemanager_resource__tracker_client_thread__count.mk false 30%positive _ )
    (yarn_resourcemanager_scheduler_class.mk false "org.apache.hadoop.yarn.server.resourcemanager.scheduler.fair.FairScheduler" _ )
    (yarn_resourcemanager_scheduler_client_thread__count.mk false 60%positive _ )
    (yarn_resourcemanager_store_class.mk false "org.apache.hadoop.yarn.server.resourcemanager.recovery.ZKRMStateStore" _ )
    (yarn_scheduler_increment__allocation__mb.mk false 400%positive _ )
    (yarn_scheduler_maximum__allocation__mb.mk false 9800%positive _ )
    (yarn_scheduler_maximum__allocation__vcores.mk false 29%positive _ )
    (yarn_scheduler_minimum__allocation__mb.mk false 1638%positive _ )
    (yarn_scheduler_minimum__allocation__vcores.mk false 6%positive _ )
    (yarn_sharedcache_admin_thread__count.mk false 8%positive _ )
    (yarn_sharedcache_client__server_thread__count.mk false 70%positive _ )
    (yarn_sharedcache_enabled.mk false true _ )
      _
      _
      _
); try (exact I); compute; try reflexivity; auto.
Qed.

Definition a_hadoop_config := mk_hadoop_config myEnv
    a_yarn_config
    a_mapred_config
    a_core_config
    a_hdfs_config.
