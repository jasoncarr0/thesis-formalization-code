
Require Import IO.
Require Import stdpp.tactics.
Require Import Coq.Classes.RelationClasses.

Class Step S : Type := { step : option io_evt -> S -> S -> Type }.
Class Space S : Type := { space : S -> nat }.

Section Steps.
  Context {C S: Type}.
  Context `{stepFn: Step S}.
  Context `{spaceFn: Space S}.

  Inductive steps : S -> S -> Type
    :=
    | st_refl s : steps s s
    | st_cons {s1 s2 i s3} :
        steps s1 s2 ->
        step i s2 s3 ->
        steps s1 s3.

  Definition steps_compose :
    forall {s1 s2 s3},
      steps s1 s2 -> steps s2 s3 ->
      steps s1 s3.
  Proof.
    intros.
    induction X0.
    - assumption.
    - eapply st_cons.
      + apply IHX0. exact X.
      + exact s.
  Defined.

  Theorem steps_compose_0_r :
    forall {s1} s2 (st1: steps s1 s2),
      steps_compose st1 (st_refl s2) = st1.
  Proof.
    reflexivity.
  Qed.

  Theorem steps_compose_0_l :
    forall s1 {s2} (st2: steps s1 s2),
      steps_compose (st_refl s1) st2 = st2.
  Proof.
    intros.
    induction st2; simpl.
    - reflexivity.
    - rewrite -> IHst2. reflexivity.
  Qed.

  Theorem steps_compose_assoc:
    forall {s1 s2 s3 s4}
           (st1: steps s1 s2) (st2: steps s2 s3) (st3: steps s3 s4),
      steps_compose st1 (steps_compose st2 st3) =
      steps_compose (steps_compose st1 st2) st3.
  Proof.
    intros.
    induction st3; simpl.
    - reflexivity.
    - f_equal. apply IHst3.
  Qed.

  Fixpoint steps_io {s1 s2} (st: steps s1 s2) : list io_evt :=
    match st with
    | st_refl _ => []
    | @st_cons _ _ None _ st' _ => steps_io st'
    | @st_cons _ _ (Some (read k)) _ st' _ => (read k) :: steps_io st'
    | @st_cons _ _ (Some (write k)) _ st' _ => (write k) :: steps_io st'
    end
  .

  Theorem steps_io_distrib :
    forall {s1 s2 s3} (st1: steps s1 s2) (st2: steps s2 s3),
      steps_io (steps_compose st1 st2) = steps_io st2 ++ steps_io st1.
  Proof.
    intros.
    induction st2; simpl.
    - reflexivity.
    - destruct i; try destruct i; simpl; f_equal; apply IHst2.
  Qed.

End Steps.

Hint Immediate st_refl.
Hint Constructors steps.