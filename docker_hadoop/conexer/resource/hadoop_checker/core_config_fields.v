Require Export fieldType.
Require Import env_desc.
Require Import Coq.ZArith.Zdiv.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope positive_scope.

Module io_file_buffer_size_desc <: Field_ModuleType.
  Definition fName := "io.file.buffer.size".
  Definition rTipe := rTipe_pos.
  (*The constraint is documented in https://hadoop.apache.org/docs/r2.7.4/hadoop-project-dist/hadoop-common/core-default.xml*)
  Definition rProperty := fun value: positive => ((Zpos value) mod (Zpos (myEnv.(env_hw_page_size)))) = 0%Z.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End io_file_buffer_size_desc.
Module io_file_buffer_size := FieldModuleFunctor io_file_buffer_size_desc.
Export io_file_buffer_size.


Module io_map_index_interval_desc <: Field_ModuleType.
  Definition fName := "io.map.index.interval".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End io_map_index_interval_desc.
Module io_map_index_interval := FieldModuleFunctor io_map_index_interval_desc.
Export io_map_index_interval.


Module io_map_index_skip_desc <: Field_ModuleType.
  Definition fName := "io.map.index.skip".
  Definition rTipe := rTipe_N.
  Definition rProperty := fun value: N => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End io_map_index_skip_desc.
Module io_map_index_skip := FieldModuleFunctor io_map_index_skip_desc.
Export io_map_index_skip.


Module io_seqfile_compress_blocksize_desc <: Field_ModuleType.
  Definition fName := "io.seqfile.compress.blocksize".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End io_seqfile_compress_blocksize_desc.
Module io_seqfile_compress_blocksize := FieldModuleFunctor io_seqfile_compress_blocksize_desc.
Export io_seqfile_compress_blocksize.


Module io_seqfile_sorter_recordlimit_desc <: Field_ModuleType.
  Definition fName := "io.seqfile.sorter.recordlimit".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End io_seqfile_sorter_recordlimit_desc.
Module io_seqfile_sorter_recordlimit := FieldModuleFunctor io_seqfile_sorter_recordlimit_desc.
Export io_seqfile_sorter_recordlimit.


Module ipc_maximum_data_length_desc <: Field_ModuleType.
  Definition fName := "ipc.maximum.data.length".
  Definition rTipe := rTipe_pos.
  Definition rProperty := fun value: positive => True.
  Definition fUnit := "".
  Definition fInterp := "".
  Definition fAdvice := "".
End ipc_maximum_data_length_desc.
Module ipc_maximum_data_length := FieldModuleFunctor ipc_maximum_data_length_desc.
Export ipc_maximum_data_length.
