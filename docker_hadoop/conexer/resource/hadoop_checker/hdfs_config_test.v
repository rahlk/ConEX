Require Import hdfs_config.
Require Import env_desc.
Require Import Omega.


Definition a_hdfs_config: HDFSConfig.
Proof.
refine (
    mk_hdfs_config
    (dfs_namenode_handler_count.mk            false 10%positive _)
    (dfs_replication.mk     false 1%positive _)
); try (exact I).
Qed.
