Require Import mapred_config.
Require Import Omega.
Require Import env_desc.
Require Import Reals.
Open Scope R_scope.

Definition a_mapred_config: MapRedConfig.
Proof.
unshelve refine (
  mk_mapred_config 
    (mapred_child_java_opts.mk            false   (mk_java_opts 200%positive 100%positive) _ )
    (mapreduce_ifile_readahead.mk            false  true _ )
    (mapreduce_ifile_readahead_bytes.mk            false 4194304%positive  _ )
    (mapreduce_input_fileinputformat_split_maxsize.mk            false   268435456%positive _ )
    (mapreduce_input_fileinputformat_split_minsize.mk            false   0%N _ )
    (mapreduce_input_lineinputformat_linespermap.mk            false   1%positive _ )
    (mapreduce_job_counters_max.mk            false   120%positive _ )
    (mapreduce_job_jvm_numtasks.mk            false   (Some 1%positive) _ )
    (mapreduce_job_max_split_locations.mk            false   10%positive _ )
    (mapreduce_job_reduce_slowstart_completedmaps.mk            false   (5/100%R) _ )
    (mapreduce_job_reducer_unconditional__preempt_delay_sec.mk            false   300%positive _ )
    (mapreduce_job_running_map_limit.mk            false  None _ )
    (mapreduce_job_running_reduce_limit.mk            false   None _ )
    (mapreduce_job_speculative_minimum__allowed__tasks.mk            false   10%positive _ )
    (mapreduce_job_speculative_retry__after__no__speculate.mk            false   1000%positive _ )
    (mapreduce_job_speculative_retry__after__speculate.mk            false   15000%positive _ )
    (mapreduce_job_speculative_speculative__cap__running__tasks.mk            false   (1/10%R) _ )
    (mapreduce_job_speculative_speculative__cap__total__tasks.mk            false   (1/100%R) _ )
    (mapreduce_job_split_metainfo_maxsize.mk            false   (Some 10000000%positive) _ )
    (mapreduce_job_ubertask_enable.mk            false  false _ )
    (mapreduce_job_ubertask_maxmaps.mk            false   9%positive _ )
    (mapreduce_job_ubertask_maxreduces.mk            false   (Some 1%positive) _ )
    (mapreduce_jobtracker_expire_trackers_interval.mk            false   600000%positive _ )
    (mapreduce_jobtracker_handler_count.mk            false   10%positive _ )
    (mapreduce_jobtracker_maxtasks_perjob.mk            false   (Some 1%positive) _ )
    (mapreduce_jobtracker_taskcache_levels.mk            false  2%positive _ )
    (mapreduce_map_cpu_vcores.mk            false   1%positive _ )
    (mapreduce_map_java_opts.mk            false  (mk_java_opts 1152%positive 100%positive) _ )
    (mapreduce_map_memory_mb.mk            false   1024%positive _ )
    (mapreduce_map_output_compress.mk            false   false _ )
    (mapreduce_map_output_compress_codec.mk            false   "org.apache.hadoop.io.compress.DefaultCodec" _ )
    (mapreduce_map_skip_maxrecords.mk            false   0%N _ )
    (mapreduce_map_skip_proc_count_autoincr.mk            false   true _ )
    (mapreduce_map_sort_spill_percent.mk            false   (8/10%R) _ )
    (mapreduce_map_speculative.mk            false   true _ )
    (mapreduce_output_fileoutputformat_compress.mk           false  false _ )
    (mapreduce_output_fileoutputformat_compress_codec.mk            false  "org.apache.hadoop.io.compress.DefaultCodec"  _ )
    (mapreduce_output_fileoutputformat_compress_type.mk            false  "RECORD" _ )
    (mapreduce_reduce_cpu_vcores.mk            false   1%positive _ )
    (mapreduce_reduce_input_buffer_percent.mk            false   (0/1%R) _ )
    (mapreduce_reduce_java_opts.mk            false  (mk_java_opts 2560%positive 100%positive) _ )
    (mapreduce_reduce_markreset_buffer_percent.mk    false  (0/1%R) _ )
    (mapreduce_reduce_memory_mb.mk            false   1024%positive _ )
    (mapreduce_reduce_merge_inmem_threshold.mk            false   (Some 1000%positive) _ )
    (mapreduce_reduce_shuffle_input_buffer_percent.mk            false   (7/10%R) _ )
    (mapreduce_reduce_shuffle_memory_limit_percent.mk            false   (25/100%R) _ )
    (mapreduce_reduce_shuffle_merge_percent.mk            false   (66/100%R) _ )
    (mapreduce_reduce_shuffle_parallelcopies.mk            false   5%positive _ )
    (mapreduce_shuffle_max_connections.mk            false      None _ )
    (mapreduce_shuffle_max_threads.mk            false   0%N _ )
    (mapreduce_shuffle_transfer_buffer_size.mk            false   131072%positive _ )
    (mapreduce_task_combine_progress_records.mk            false   10000%positive _ )
    (mapreduce_task_io_sort_factor.mk            false   10%positive _ )
    (mapreduce_task_io_sort_mb.mk            false   100%positive _ )
    (mapreduce_task_merge_progress_records.mk            false   10000%positive _ )
    (mapreduce_task_profile_maps.mk            false  "0-2" _ )
    (mapreduce_task_profile_reduces.mk            false  "0-2" _ )
    (mapreduce_tasktracker_http_threads.mk            false  40%positive _ )
    (mapreduce_tasktracker_indexcache_mb.mk            false  10%positive _ )
    (mapreduce_tasktracker_map_tasks_maximum.mk            false   2%positive _ )
    (mapreduce_tasktracker_reduce_tasks_maximum.mk            false   2%positive _ )
    (mapreduce_tasktracker_taskmemorymanager_monitoringinterval.mk     false   5000%positive _ )
    (yarn_app_mapreduce_am_command__opts.mk            false   (mk_java_opts 1024%positive 100%positive) _ )
    (yarn_app_mapreduce_am_containerlauncher_threadpool__initial__size.mk            false   10%positive _ )
    (yarn_app_mapreduce_am_job_task_listener_thread__count.mk            false   30%positive _ )
    (yarn_app_mapreduce_am_resource_cpu__vcores.mk            false    1%positive _ )
    (yarn_app_mapreduce_am_resource_mb.mk            false   2880%positive _ )
    _
    _
    _
    _
    _
    _
    _
); try (exact I); simpl; try (intro H); try (inversion H); try compute; try reflexivity; auto.
Qed.
