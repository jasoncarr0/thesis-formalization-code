Require Import stdpp.base.
Require Import stdpp.sets.
Require Import stdpp.fin_sets.

Module Type SyntaxParams.

  Parameter var : Type.
  Parameter vars : Type.

  Declare Instance var_decEq: EqDecision var.

  (* I can't seem to get these to be instances without doing this *)
  Context `{vars_elem: ElemOf var vars, vars_empty: Empty vars, vars_singleton: Singleton var vars, vars_union : Union vars, vars_intersection : Intersection vars, vars_difference : Difference vars, vars_elements : Elements var vars}.
  Existing Instances vars_elem vars_empty vars_singleton vars_union vars_intersection vars_difference vars_elements.
  Declare Instance vars_set : FinSet var vars.
  Declare Instance vars_elem_dec: forall (x: var) (xs: vars), Decision (elem_of x xs).
End SyntaxParams.