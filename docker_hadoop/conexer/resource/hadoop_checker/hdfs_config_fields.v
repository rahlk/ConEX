Require Export fieldType.
Require Import env_desc.
Require Import Coq.ZArith.Zdiv.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope positive_scope.

Module dfs_namenode_handler_count_desc <: Field_ModuleType.
  Definition fName := "dfs.namenode.handler.count".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End dfs_namenode_handler_count_desc.
Module dfs_namenode_handler_count := FieldModuleFunctor dfs_namenode_handler_count_desc.
Export dfs_namenode_handler_count.


Module dfs_replication_desc <: Field_ModuleType.
  Definition fName := "dfs.replication".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End dfs_replication_desc.
Module dfs_replication := FieldModuleFunctor dfs_replication_desc.
Export dfs_replication.
