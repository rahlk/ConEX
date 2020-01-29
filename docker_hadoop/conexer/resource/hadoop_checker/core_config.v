Require Export core_config_fields.
Require Export env_desc.

Record CoreConfig := mk_core_config {

  (* configuration file field names and types *)
  io_file_buffer_size: io_file_buffer_size.ftype
 ;io_map_index_interval: io_map_index_interval.ftype
 ;io_map_index_skip: io_map_index_skip.ftype
 ;io_seqfile_compress_blocksize: io_seqfile_compress_blocksize.ftype
 ;io_seqfile_sorter_recordlimit: io_seqfile_sorter_recordlimit.ftype
 ;ipc_maximum_data_length: ipc_maximum_data_length.ftype
}.