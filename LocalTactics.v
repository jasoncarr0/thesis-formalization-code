Require Import stdpp.tactics.
Require Import stdpp.fin_sets.

Ltac primforced term taclist :=
  let n := numgoals in
  destruct term eqn:?; try solve [intros; exfalso; subst; (solve taclist || discriminate || contradiction || congruence)];
    let m := numgoals in
    tryif (guard m <= n) then idtac else fail 0 term "not forced".
Tactic Notation "forced" constr(term) :=
  primforced term idtac.
Tactic Notation "forced" constr(term) "by" tactic_list(t) :=
  primforced term t.


                                             
Global Tactic Notation "define" "(" ident(H) ":" open_constr(type) ")" :=
  unshelve refine (let H := (_ : type) in _).


(* Based somewhat on https://github.com/tchajed/coq-tricks/blob/master/src/Deex.v
 with extra support for constructive exists *)
Ltac deex :=
  repeat match goal with
         | [ H: exists (name:_), _ |- _ ] =>
           let name' := fresh name in
           destruct H as [name' H]
         | [ H: { name:_ & _ } |- _ ] =>
           let name' := fresh name in
           destruct H as [name' H]
         | [ H: { name:_ | _ } |- _ ] =>
           let name' := fresh name in
           destruct H as [name' H]
         end.
(* Add products *)
Ltac deprod :=
  repeat match goal with
         | [ H: exists (name:_), _ |- _ ] =>
           let name' := fresh name in
           destruct H as [name' H]
         | [ H: { name:_ & _ } |- _ ] =>
           let name' := fresh name in
           destruct H as [name' H]
         | [ H: { name:_ | _ } |- _ ] =>
           let name' := fresh name in
           destruct H as [name' H]
         | [ H: _ /\ _ |- _ ] =>
           destruct H
         | [ H: (_ * _)%type |- _] =>
           destruct H
         end.

Ltac deep_set_unfold :=
  repeat progress (intro || deprod || simplify_eq || set_unfold).

  