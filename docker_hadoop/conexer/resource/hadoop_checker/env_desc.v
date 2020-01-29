Require Export Coq.ZArith.BinInt.
Require Export List.
Open Scope list_scope.
Require Export String.
Open Scope string_scope.

(*
Define global (Export) environment parameter values 
so that they're visible within the "field modules", which
is where we express the constraints on individual fields. 
These constraints can involve environment parameters,
so these values have to be visible at that point in the code.
Passing this information in a global variable really isn't
great, but because we're using the module system, we 
don't really have a choice. We can't pass this information
in as an ordinary function parameter.

Each user of this framework will have to provide his or
her own platform-specific version of this file then rebuild
this theory.
*)
Record Env := mk_env {
  env_phys_CPU_cores: positive
 ;env_virt_CPU_cores: positive
 ;env_phys_mem_mb: positive
 ;env_virt_mem_mb: positive
 ;env_hw_page_size: positive
 ;env_max_file_desc: positive
 ;env_max_threads: positive
 ;env_comp_codecs: list string
}.

Definition myEnv:Env := mk_env 
  14%positive 
  28%positive
  32768%positive (*32GB physical memory*)
  32768%positive (*32GB physical memory*)
  4096%positive  (*page size*)
  3000%positive  (*max file discriptor*)
  500%positive  (*max number of threads*)
  (*compression codecs*)
  ("org.apache.hadoop.io.compress.DefaultCodec"::"org.apache.hadoop.io.compress.GzipCodec"::"org.apache.hadoop.io.compress.BZip2Codec"::nil)
.
(*
Definition env_phys_CPU_cores: positive := 6%positive.
Definition env_virt_CPU_cores: positive := 48%positive.
Definition env_phys_mem_mb: positive := 4096%positive.
Definition env_virt_mem_mb: positive := 8192%positive.
Definition env_hw_page_size: positive := 4096%positive. 
Definition env_max_file_desc: positive := 3000%positive.
Definition env_max_threads: positive := 500%positive.
*)
