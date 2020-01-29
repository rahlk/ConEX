Require Export fieldType.
Require Import env_desc.
Require Import Coq.ZArith.Zdiv.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope positive_scope.
Require Import Reals.
Open Scope R_scope.
Require Export List.
Open Scope list_scope.


Module yarn_nodemanager_container__manager_thread__count_desc <: Field_ModuleType.
  Definition fName := "yarn.nodemanager.container-manager.thread-count".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_nodemanager_container__manager_thread__count_desc.
Module yarn_nodemanager_container__manager_thread__count := FieldModuleFunctor yarn_nodemanager_container__manager_thread__count_desc.
Export yarn_nodemanager_container__manager_thread__count.


Module yarn_nodemanager_localizer_client_thread__count_desc <: Field_ModuleType.
  Definition fName := "yarn.nodemanager.localizer.client.thread-count".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_nodemanager_localizer_client_thread__count_desc.
Module yarn_nodemanager_localizer_client_thread__count := FieldModuleFunctor yarn_nodemanager_localizer_client_thread__count_desc.
Export yarn_nodemanager_localizer_client_thread__count.


Module yarn_nodemanager_localizer_fetch_thread__count_desc <: Field_ModuleType.
  Definition fName := "yarn.nodemanager.localizer.fetch.thread-count".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_nodemanager_localizer_fetch_thread__count_desc.
Module yarn_nodemanager_localizer_fetch_thread__count := FieldModuleFunctor yarn_nodemanager_localizer_fetch_thread__count_desc.
Export yarn_nodemanager_localizer_fetch_thread__count.


Module yarn_nodemanager_resource_cpu__vcores_desc <: Field_ModuleType.
  Definition fName := "yarn.nodemanager.resource.cpu-vcores".
  Definition rTipe := rTipe_pos.
  (* A common sense constraint: CPU cores used by nodemanager must be less than a machine can provide. *)
  Definition rProperty := fun value: positive => Pos.lt value (env_virt_CPU_cores myEnv).
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_nodemanager_resource_cpu__vcores_desc.
Module yarn_nodemanager_resource_cpu__vcores := FieldModuleFunctor yarn_nodemanager_resource_cpu__vcores_desc.
Export yarn_nodemanager_resource_cpu__vcores.


Module yarn_nodemanager_resource_memory__mb_desc <: Field_ModuleType.
  Definition fName := "yarn.nodemanager.resource.memory-mb".
  Definition rTipe := rTipe_pos.
  (* A common sense constraint: memory used by nodemanager must be less than a machine can provide. *)
  Definition rProperty := fun value: positive => Pos.lt value (env_phys_mem_mb myEnv).
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_nodemanager_resource_memory__mb_desc.
Module yarn_nodemanager_resource_memory__mb := FieldModuleFunctor yarn_nodemanager_resource_memory__mb_desc.
Export yarn_nodemanager_resource_memory__mb.


Module yarn_nodemanager_resource_percentage__physical__cpu__limit_desc <: Field_ModuleType.
  Definition fName := "yarn.nodemanager.resource.percentage-physical-cpu-limit".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_nodemanager_resource_percentage__physical__cpu__limit_desc.
Module yarn_nodemanager_resource_percentage__physical__cpu__limit := FieldModuleFunctor yarn_nodemanager_resource_percentage__physical__cpu__limit_desc.
Export yarn_nodemanager_resource_percentage__physical__cpu__limit.


Module yarn_nodemanager_vmem__check__enabled_desc <: Field_ModuleType.
  Definition fName := "yarn.nodemanager.vmem-check-enabled".
  Definition rTipe := rTipe_bool.
  Definition rProperty := fun value: bool => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_nodemanager_vmem__check__enabled_desc.
Module yarn_nodemanager_vmem__check__enabled := FieldModuleFunctor yarn_nodemanager_vmem__check__enabled_desc.
Export yarn_nodemanager_vmem__check__enabled.


Module yarn_nodemanager_vmem__pmem__ratio_desc <: Field_ModuleType.
  Definition fName := "yarn.nodemanager.vmem-pmem-ratio".
  Definition rTipe := rTipe_float.
  Definition rProperty := fun value: R => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_nodemanager_vmem__pmem__ratio_desc.
Module yarn_nodemanager_vmem__pmem__ratio := FieldModuleFunctor yarn_nodemanager_vmem__pmem__ratio_desc.
Export yarn_nodemanager_vmem__pmem__ratio.


Module yarn_nodemanager_windows__container_cpu__limit_enabled_desc <: Field_ModuleType.
  Definition fName := "yarn.nodemanager.windows-container.cpu-limit.enabled".
  Definition rTipe := rTipe_bool.
  Definition rProperty := fun value: bool => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_nodemanager_windows__container_cpu__limit_enabled_desc.
Module yarn_nodemanager_windows__container_cpu__limit_enabled := FieldModuleFunctor yarn_nodemanager_windows__container_cpu__limit_enabled_desc.
Export yarn_nodemanager_windows__container_cpu__limit_enabled.


Module yarn_nodemanager_windows__container_memory__limit_enabled_desc <: Field_ModuleType.
  Definition fName := "yarn.nodemanager.windows-container.memory-limit.enabled".
  Definition rTipe := rTipe_bool.
  Definition rProperty := fun value: bool => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_nodemanager_windows__container_memory__limit_enabled_desc.
Module yarn_nodemanager_windows__container_memory__limit_enabled := FieldModuleFunctor yarn_nodemanager_windows__container_memory__limit_enabled_desc.
Export yarn_nodemanager_windows__container_memory__limit_enabled.


Module yarn_resourcemanager_admin_client_thread__count_desc <: Field_ModuleType.
  Definition fName := "yarn.resourcemanager.admin.client.thread-count".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_resourcemanager_admin_client_thread__count_desc.
Module yarn_resourcemanager_admin_client_thread__count := FieldModuleFunctor yarn_resourcemanager_admin_client_thread__count_desc.
Export yarn_resourcemanager_admin_client_thread__count.


Module yarn_resourcemanager_amlauncher_thread__count_desc <: Field_ModuleType.
  Definition fName := "yarn.resourcemanager.amlauncher.thread-count".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_resourcemanager_amlauncher_thread__count_desc.
Module yarn_resourcemanager_amlauncher_thread__count := FieldModuleFunctor yarn_resourcemanager_amlauncher_thread__count_desc.
Export yarn_resourcemanager_amlauncher_thread__count.


Module yarn_resourcemanager_client_thread__count_desc <: Field_ModuleType.
  Definition fName := "yarn.resourcemanager.client.thread-count".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_resourcemanager_client_thread__count_desc.
Module yarn_resourcemanager_client_thread__count := FieldModuleFunctor yarn_resourcemanager_client_thread__count_desc.
Export yarn_resourcemanager_client_thread__count.


Module yarn_resourcemanager_ha_enabled_desc <: Field_ModuleType.
  Definition fName := "yarn.resourcemanager.ha.enabled".
  Definition rTipe := rTipe_bool.
  Definition rProperty := fun value: bool => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_resourcemanager_ha_enabled_desc.
Module yarn_resourcemanager_ha_enabled := FieldModuleFunctor yarn_resourcemanager_ha_enabled_desc.
Export yarn_resourcemanager_ha_enabled.


Module yarn_resourcemanager_resource__tracker_client_thread__count_desc <: Field_ModuleType.
  Definition fName := "yarn.resourcemanager.resource-tracker.client.thread-count".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_resourcemanager_resource__tracker_client_thread__count_desc.
Module yarn_resourcemanager_resource__tracker_client_thread__count := FieldModuleFunctor yarn_resourcemanager_resource__tracker_client_thread__count_desc.
Export yarn_resourcemanager_resource__tracker_client_thread__count.


Module yarn_resourcemanager_scheduler_class_desc <: Field_ModuleType.
  Definition fName := "yarn.resourcemanager.scheduler.class".
  Definition rTipe := rTipe_string.
  Definition rProperty := fun value: string => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_resourcemanager_scheduler_class_desc.
Module yarn_resourcemanager_scheduler_class := FieldModuleFunctor yarn_resourcemanager_scheduler_class_desc.
Export yarn_resourcemanager_scheduler_class.


Module yarn_resourcemanager_scheduler_client_thread__count_desc <: Field_ModuleType.
  Definition fName := "yarn.resourcemanager.scheduler.client.thread-count".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_resourcemanager_scheduler_client_thread__count_desc.
Module yarn_resourcemanager_scheduler_client_thread__count := FieldModuleFunctor yarn_resourcemanager_scheduler_client_thread__count_desc.
Export yarn_resourcemanager_scheduler_client_thread__count.


Module yarn_resourcemanager_store_class_desc <: Field_ModuleType.
  Definition fName := "yarn.resourcemanager.store.class".
  Definition rTipe := rTipe_string.
  (* This constraint is documented in https://hadoop.apache.org/docs/r2.7.4/hadoop-yarn/hadoop-yarn-common/yarn-default.xml*)
  Definition rProperty := fun value: string => In value ("org.apache.hadoop.yarn.server.resourcemanager.recovery.FileSystemRMStateStore"::"org.apache.hadoop.yarn.server.resourcemanager.recovery.ZKRMStateStore"::nil).
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_resourcemanager_store_class_desc.
Module yarn_resourcemanager_store_class := FieldModuleFunctor yarn_resourcemanager_store_class_desc.
Export yarn_resourcemanager_store_class.


Module yarn_scheduler_increment__allocation__mb_desc <: Field_ModuleType.
  Definition fName := "yarn.scheduler.increment-allocation-mb".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_scheduler_increment__allocation__mb_desc.
Module yarn_scheduler_increment__allocation__mb := FieldModuleFunctor yarn_scheduler_increment__allocation__mb_desc.
Export yarn_scheduler_increment__allocation__mb.


Module yarn_scheduler_maximum__allocation__mb_desc <: Field_ModuleType.
  Definition fName := "yarn.scheduler.maximum-allocation-mb".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_scheduler_maximum__allocation__mb_desc.
Module yarn_scheduler_maximum__allocation__mb := FieldModuleFunctor yarn_scheduler_maximum__allocation__mb_desc.
Export yarn_scheduler_maximum__allocation__mb.


Module yarn_scheduler_maximum__allocation__vcores_desc <: Field_ModuleType.
  Definition fName := "yarn.scheduler.maximum-allocation-vcores".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_scheduler_maximum__allocation__vcores_desc.
Module yarn_scheduler_maximum__allocation__vcores := FieldModuleFunctor yarn_scheduler_maximum__allocation__vcores_desc.
Export yarn_scheduler_maximum__allocation__vcores.


Module yarn_scheduler_minimum__allocation__mb_desc <: Field_ModuleType.
  Definition fName := "yarn.scheduler.minimum-allocation-mb".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_scheduler_minimum__allocation__mb_desc.
Module yarn_scheduler_minimum__allocation__mb := FieldModuleFunctor yarn_scheduler_minimum__allocation__mb_desc.
Export yarn_scheduler_minimum__allocation__mb.


Module yarn_scheduler_minimum__allocation__vcores_desc <: Field_ModuleType.
  Definition fName := "yarn.scheduler.minimum-allocation-vcores".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_scheduler_minimum__allocation__vcores_desc.
Module yarn_scheduler_minimum__allocation__vcores := FieldModuleFunctor yarn_scheduler_minimum__allocation__vcores_desc.
Export yarn_scheduler_minimum__allocation__vcores.


Module yarn_sharedcache_admin_thread__count_desc <: Field_ModuleType.
  Definition fName := "yarn.sharedcache.admin.thread-count".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_sharedcache_admin_thread__count_desc.
Module yarn_sharedcache_admin_thread__count := FieldModuleFunctor yarn_sharedcache_admin_thread__count_desc.
Export yarn_sharedcache_admin_thread__count.


Module yarn_sharedcache_client__server_thread__count_desc <: Field_ModuleType.
  Definition fName := "yarn.sharedcache.client-server.thread-count".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_sharedcache_client__server_thread__count_desc.
Module yarn_sharedcache_client__server_thread__count := FieldModuleFunctor yarn_sharedcache_client__server_thread__count_desc.
Export yarn_sharedcache_client__server_thread__count.


Module yarn_sharedcache_enabled_desc <: Field_ModuleType.
  Definition fName := "yarn.sharedcache.enabled".
  Definition rTipe := rTipe_bool.
  Definition rProperty := fun value: bool => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_sharedcache_enabled_desc.
Module yarn_sharedcache_enabled := FieldModuleFunctor yarn_sharedcache_enabled_desc.
Export yarn_sharedcache_enabled.


Module yarn_nodemanager_recovery_compaction__interval__secs_desc <: Field_ModuleType.
  Definition fName := "yarn.nodemanager.recovery.compaction-interval-secs".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End yarn_nodemanager_recovery_compaction__interval__secs_desc.
Module yarn_nodemanager_recovery_compaction__interval__secs := FieldModuleFunctor yarn_nodemanager_recovery_compaction__interval__secs_desc.
Export yarn_nodemanager_recovery_compaction__interval__secs.
