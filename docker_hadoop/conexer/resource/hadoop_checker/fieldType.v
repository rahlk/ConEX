Require Export hadoop_base_types.
Require Import env_desc.
Require Export Coq.ZArith.BinInt.
Require Export String.
Require Import Reals.
Open Scope R_scope.


(*
We lift values of machine types to values of dependent pair types, representing subsets defined by
constraints (properties) over Coq "base" types denoted by these tipes. We make tipes explicit so that 
later on we can match on them (whereas Coq doesn't support matching on Types directly.
*)
Inductive RTipe := 
  | rTipe_Z 
  | rTipe_pos 
  | rTipe_N 
  | rTipe_string 
  | rTipe_bool 
  | rTipe_JavaOpts 
  | rTipe_float
  | rTipe_option_pos.

(*
Map RTipes to corresponding native Coq types. We lift values of machine types to these native types.
We then (below) require that such lifted values satisfy any additionally imposed constraints, yielding
what amounts to a dependent pair type as our notion of a real-world type, though we don't actually 
declare explcit Coq types for the dependent pairs.
*)
Definition typeOfTipe (mt: RTipe): Type :=
  match mt with
    | rTipe_Z                   => Z              (* any integer *)
    | rTipe_pos               => positive    (* positive integers *)
    | rTipe_N                   => N             (* non-negative integers *)
    | rTipe_string            => string
    | rTipe_bool              => bool
    | rTipe_JavaOpts     => JavaOpts
    | rTipe_float             => R
    | rTipe_option_pos  => option positive
  end.

(*
Field is a record type whose values represent fields of Hadoop configuration files.
The Field type is parameterized by a machine type and a property of a value of a
corresponding native Coq type; and it has (record) fields as indicated here: an id,
which must be the actual name of the Hadoop field, a flag indicating whether the
field is to be considered final (true) or not, a value of the native type corresponding
to the tipe, and finally a proof that that value has the specified property (i.e., is of
the specified "real world type," rwt.
*)
Inductive Field (tipe: RTipe) (property: (typeOfTipe tipe) -> Prop)  := mk_field {
    field_id: string
  ; field_final: bool
  ; field_value: (typeOfTipe tipe)
  ; field_proof: property field_value
}.

(*
The next few definitions use the Coq module system to provide mechanisms for easily
specifying the properties of individual Hadoop fields. See the Coq Module Tutorial for
background.
*)

(*
We start by defining a "Module Type", an abstract specification of what a
concrete Field-describing Module must specify. In particular, a module of
this kind must define the Hadoop name of the field, its RTipe, and its real
world type, which is to say, a property of the corresponding Coq native type.
*)
Module Type Field_ModuleType.
Parameter fName : string.
Parameter rTipe : RTipe.
Parameter rProperty : typeOfTipe rTipe -> Prop.
Parameter fUnit : string.
Parameter fInterp : string.
Parameter fAdvice : string.
End Field_ModuleType.

(*
Next we specify a "Module Functor", which is module that will take a
concrete module conforming to the just defined abstract specification,
and that constructs a new concrete module with additional definitions,
specialized to the concrete values defined in the concrete module. In
particular, the resulting module will (1) provide a function, [mk], that is
to be used to create field instances specifying finality, a (native) value
of the required type, and a proof that it satisfies the required property;
and (2) a function, type, that returns the (parameterized) Field type.
*)
Module FieldModuleFunctor (FieldModule : Field_ModuleType).
Import FieldModule.
Definition mtype := typeOfTipe rTipe.
Definition mk (isFinal: bool) (value: (typeOfTipe rTipe)) (pf: (rProperty value)) :=
  mk_field rTipe rProperty fName isFinal value pf.
Definition ftype := Field rTipe rProperty.
Definition name := fName.
Definition value (f: ftype): mtype := field_value rTipe rProperty f.
End FieldModuleFunctor.
