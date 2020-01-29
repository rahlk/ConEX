Require Import yarn_config.
Require Import Omega.
Require Import env_desc.
Require Import Reals.
Open Scope R_scope.
Open Scope Z_scope.
Open Scope positive_scope.


Definition a_yarn_config: YarnConfig.
Proof.
unshelve refine (
  mk_yarn_config
    (yarn_nodemanager_container__manager_thread__count.mk            false   20%positive _ )
    (yarn_nodemanager_localizer_client_thread__count.mk            false   5%positive _ )
    (yarn_nodemanager_localizer_fetch_thread__count.mk            false   4%positive _ )
    (yarn_nodemanager_recovery_compaction__interval__secs.mk            false   3600%positive _ )
    (yarn_nodemanager_resource_cpu__vcores.mk            false   8%positive _ )
    (yarn_nodemanager_resource_memory__mb.mk false 8192%positive _ )
    (yarn_nodemanager_resource_percentage__physical__cpu__limit.mk            false   100%positive _ )
    (yarn_nodemanager_vmem__check__enabled.mk            false  true _ )
    (yarn_resourcemanager_admin_client_thread__count.mk            false   1%positive _ )
    (yarn_resourcemanager_amlauncher_thread__count.mk            false   50%positive _ )
    (yarn_resourcemanager_client_thread__count.mk            false   50%positive _ )
    (yarn_resourcemanager_resource__tracker_client_thread__count.mk            false   50%positive _ )
    (yarn_resourcemanager_scheduler_class.mk            false   "org.apache.hadoop.yarn.server.resourcemanager.scheduler.capacity.CapacityScheduler" _ )
    (yarn_resourcemanager_scheduler_client_thread__count.mk            false   50%positive _ )
    (yarn_resourcemanager_store_class.mk            false   "org.apache.hadoop.yarn.server.resourcemanager.recovery.FileSystemRMStateStore" _ )
    (yarn_scheduler_increment__allocation__mb.mk            false   1%positive _ )
    (yarn_scheduler_maximum__allocation__mb.mk            false   8192%positive _ )
    (yarn_scheduler_maximum__allocation__vcores.mk            false   32%positive _ )
    (yarn_scheduler_minimum__allocation__mb.mk            false   1024%positive _ )
    (yarn_scheduler_minimum__allocation__vcores.mk            false   1%positive _ )
    (yarn_sharedcache_admin_thread__count.mk            false   1%positive _ )
    (yarn_sharedcache_client__server_thread__count.mk            false   50%positive _ )
    (yarn_sharedcache_enabled.mk            false   false _ )
    _
    _
    _
); try (exact I); try compute; try reflexivity; auto.
Qed.

