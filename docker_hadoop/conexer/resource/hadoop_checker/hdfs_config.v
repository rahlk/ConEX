Require Export hdfs_config_fields.
Require Export env_desc.

Record HDFSConfig := mk_hdfs_config {
  dfs_namenode_handler_count: dfs_namenode_handler_count.ftype
 ;dfs_replication: dfs_replication.ftype
}.