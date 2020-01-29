Require Export Coq.ZArith.BinInt.

Inductive JavaOpts := mk_java_opts {
   starting_heap_size: positive
 ; maximum_heap_size: positive
}.