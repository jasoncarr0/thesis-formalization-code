Require Import stdpp.base.
Require Import stdpp.sets.
Require Import stdpp.list. (* has some list definitions *)
Require Import stdpp.decidable.
Require Import stdpp.tactics.

Require Import Coq.Logic.Eqdep_dec. (* logical facts *)
Require Import Coq.Lists.List.
Import ListNotations.

Require Import LocalTactics.

(* Several facts about decidable equality and list lookups

   I originally did this myself, as it has poor support in
   Coq's stdlib, especially for the set version, but

  eventually moved it over the Iris's std++, so this is mostly remapping names from my EqDecision to EqDecision *)


(* Type-level decidable equality *)
Definition decEq `{EqDecision X}: forall (x1 x2: X), {x1 = x2} + {x1 <> x2}
  :=
    fun x1 x2 => decide (x1 = x2).

Instance decEq_list {A} `(EqDecision A) : EqDecision (list A).
Proof.
  unfold EqDecision. intros.
  generalize dependent y.
  induction x; induction y; try solve [right; discriminate].
  - left. reflexivity.
  - destruct (decEq a a0) as [-> | a_neq]; destruct (IHx y) as [-> | rest_neq];
      solve [left; reflexivity] ||
            right; intro; inversion H; subst; contradiction.
Qed.

Instance decEq_nat : EqDecision nat.
Proof.
  unfold EqDecision. intro x.
  induction x; induction y.
  - left. reflexivity.
  - right. discriminate.
  - right. discriminate.
  - destruct (IHx y).
    + left. subst. reflexivity.
    + right. intro H. inversion H. contradiction.
Qed.

Definition dec_eq_to_prop : forall {X} {x1 x2: X},
    {x1 = x2} + {x1 <> x2} -> x1 = x2 \/ x1 <> x2.
Proof.
  intros. destruct H; auto.
Qed.

Theorem decEq_refl : forall {X} `{EqDecision X} (x: X),
    decEq x x = left eq_refl.
Proof.
  intros. destruct (decEq x x).
  - (* by Hedberg's Theorem *)
    f_equal.
    refine (K_dec _ (fun (e': x = x) => e' = eq_refl) eq_refl e).
    intros. apply dec_eq_to_prop.
    apply decide. apply EqDecision0.
  - contradiction.
Qed.

Lemma if_decEq_neq : forall {X T} `{EqDecision X} (x y: X),
    forall {t1 t2: T},
    x <> y ->
    (if decEq x y then t1 else t2) = t2.
Proof.
  intros.
  forced (decEq x y).
  reflexivity.
Qed.

Ltac elim_decEq :=
  match goal with
  | H : context [@decide (?x = ?x)] |- _ => rewrite (@decEq_refl _ _ x) in H
  | H : context [@decEq _ _ ?x ?x] |- _ => rewrite (@decEq_refl _ _ x) in H
  | |- context [@decide (?x = ?x)] => rewrite (@decEq_refl _ _ x)
  | |- context [@decEq _ _ ?x ?x] => rewrite (@decEq_refl _ _ x)
  | H : ?x <> ?y |- context [if @decEq _ _ ?x ?y then ?a else ?b] => rewrite -> (if_decEq_neq x y H)
  | H : ?y <> ?x |- context [if @decEq _ _ ?x ?y then ?a else ?b] => rewrite -> (if_decEq_neq x y (not_eq_sym H))
  | |- context [if @decEq _ _ ?x ?x then ?a else ?b] => rewrite -> (@decEq_refl _ _ x)
  end.

Hint Extern 2 => elim_decEq : decEq.

(*

List membership definitions and facts, especially for decidable data

*)


Definition member {X} `{EqDecision X}
           (x: X) (xs: list X): {In x xs} + {~ In x xs}.
Proof.
  intros.
  induction xs.
  - right. apply in_nil.
  - simpl. destruct (decEq a x).
    + left. left. assumption.
    + destruct IHxs.
      * left. right. assumption.
      * right. unfold not. intros []; contradiction.
Defined.

Instance search {X Y} `{EqDecision X} : Lookup X Y (list (X * Y))
  :=
    fix search (x: X) (ps: list (X * Y)) {struct ps} :=
    match ps with
    | nil => None
    | (x', y) :: ps' =>
      if decEq x x'
      then Some y
      else search x ps'
    end.




(* Not strictly related, but useful *)
Lemma In_map_fst {X Y} : forall (x: X) (y: Y) ps,
    In (x, y) ps ->
    In x (map fst ps).
Proof with eauto.
  intros.
  induction ps...
  destruct H; subst; simpl in *.
  - left...
  - right...
Qed.
Hint Resolve In_map_fst : searches.
Hint Extern 1 (_ !! _ = _) => unfold lookup : searches.
Hint Resolve -> elem_of_list_In : searches.
Hint Resolve <- elem_of_list_In : searches.

Lemma In_map_fst_In {X Y} : forall (x: X) (ps: list (X * Y)),
    In x (map fst ps) ->
    exists y, In (x, y) ps.
Proof with auto.
  intros.
  induction ps...
  simpl in H.
  { contradiction. }
  destruct a.
  destruct H; subst...
  - exists y. simpl...
  - destruct (IHps H) as [y' ?].
    exists y'. right...
Qed.


Theorem In_search {X Y} `{EqDecision X}:
  forall (x: X) (y: Y) ps,
    NoDup (map fst ps) ->
    In (x, y) ps ->
    search x ps = Some y.
Proof with eauto with searches.
  intros.
  induction ps.
  - contradiction.
  - simpl in *. destruct a.
    destruct (decEq x x0) as [-> | neq]; simpl in *.
    + destruct H0.
      * congruence.
      * inversion H; subst.
        -- rewrite <- elem_of_list_In in H0.
           absurd (elem_of x0 (map fst ps))...
    + inversion H; subst.
      apply IHps...
      (* x <> x0 *)
      forced H0...
Qed.
    
Theorem In_fst_search :
  forall {X Y} `{EqDecision X} x (ps: list (X * Y)),
    In x (map fst ps) -> { y : Y & search x ps = Some y }.
Proof.
  intros.
  induction ps.
  - contradiction.
  - simpl in *. destruct a.
    destruct (decEq x x0) as [-> | neq]; simpl in *.
    + eexists. reflexivity.
    + apply IHps. destruct H as [->|?]; done.
Qed.

Theorem In_fst_search_not_None :
  forall {X Y} `{EqDecision X} x (ps: list (X * Y)),
    In x (map fst ps) -> search x ps <> None.
Proof.
  intros.
  destruct (In_fst_search x ps H).
  congruence.
Qed.

Theorem search_In :
  forall {X Y} `{EqDecision X} x y (ps: list (X * Y)),
    search x ps = Some y -> In (x, y) ps.
Proof with eauto.
  intros.
  induction ps; simpl in *; try discriminate.
  destruct a; subst.
  destruct (decEq x x0) as [->|?]...
  simplify_eq. left...
Qed.

Theorem not_In_fst_search :
  forall {X Y} `{EqDecision X} x (ps: list (X * Y)),
    ~ In x (map fst ps) -> search x ps = None.
Proof with eauto.
  intros.
  destruct (search x ps) eqn:eqsearch...
  apply search_In in eqsearch.
  contradict H.
  eauto with searches.
Qed.

Hint Rewrite @In_search : searches.
Hint Resolve @In_search search_In : searches.
Hint Resolve @In_fst_search @In_fst_search_not_None @search_In : searches.
Hint Rewrite @not_In_fst_search : searches.

Theorem In_if_member :
  forall {X Y} `{EqDecision X}
    (x: X) (xs: list X) (et ef: Y),
    In x xs ->
    (if member x xs then et else ef) = et.
Proof.
  intros.
  destruct (member x xs); reflexivity || contradiction.
Qed.
  
Theorem not_In_if_member :
  forall {X Y} `{EqDecision X}
    (x: X) (xs: list X) (et ef: Y),
    (~ In x xs) ->
    (if member x xs then et else ef) = ef.
Proof.
  intros.
  destruct (member x xs); reflexivity || contradiction.
Qed.

Hint Rewrite @In_if_member : searches.
Hint Rewrite @not_In_if_member : searches.

(* useful tactic to prove In *)
Hint Resolve in_eq.
Hint Resolve in_eq : searches.

Lemma In_map_snd :
  forall {X Y},
    forall y (xs: list (X * Y)),
      In y (map snd xs) ->
      exists x, 
        In (x, y) xs.
Proof with eauto.
  intros.
  induction xs.
  { destruct H. } (* otherwise eauto shelves *)
  simpl in *.
  destruct H.
  - destruct a as [a ?].
    simplify_eq.
    exists a...
  - destruct (IHxs H) as [x inx].
    exists x. right...
Qed.

Hint Resolve In_map_snd : searches.

Lemma Forall2_nth :
  forall {A B} (P: A -> B -> Prop) xs ys i x y,
    Forall2 P xs ys ->
    nth_error xs i = Some x ->
    nth_error ys i = Some y ->
    P x y.
Proof with eauto.
  intros. generalize dependent i.
  induction H; intros i xi yi.
  - destruct i; simpl in xi; discriminate.
  - destruct i; simpl nth_error in *.
    + simplify_eq...
    + eapply IHForall2...
Qed.

Hint Rewrite @Forall2_nth : searches.

Fixpoint map_option {X Y} (f: X -> option Y) (xs: list X):
  option (list Y)
  :=
    match xs with
    | [] => Some []
    | (x :: xs) =>
      match f x with
      | Some v =>
        match map_option f xs with
        | Some vs => Some (v :: vs)
        | None => None
        end
      | None => None
      end
    end.

Definition map_with_in {X Y} (xs: list X) (f: forall (x: X), In x xs -> Y): list Y.
  induction xs as [| x xs ].
  - exact [].
  - apply cons.
    + apply (f x); repeat constructor.
    + apply IHxs. intros.
      apply (f x0). simpl.
      right. assumption.
Defined.

Theorem map_option_all_some : forall
    {X Y} (f: X -> option Y) xs
    (getY: forall x,
        In x xs ->
        { y : Y &
              f x = Some y }),
    map_option f xs =
    Some (map_with_in xs (fun y i => projT1 (getY y i))).
Proof.
  intros.
  induction xs as [| x xs]; simpl.
  - reflexivity.
  - pose (fun x i0 => getY x (or_intror i0))
         as getY'.
    rewrite -> (IHxs getY').
    destruct (getY x _) as [ y fxy ].
    rewrite -> fxy.
    reflexivity.
Qed.

Fixpoint filter_map {X Y} (f: X -> option Y) (xs: list X): list Y
  :=
    match xs with
    | [] => []
    | (x :: xs) =>
      match f x with
      | Some y => y :: filter_map f xs
      | None => filter_map f xs
      end
    end.
Instance elem_of_filter_map {X Y} {f: X -> option Y} {xs: list X} : SetUnfoldElemOf (y:Y) (filter_map f xs : list Y) (exists x, elem_of x xs /\ f x = Some y).
Proof with eauto.
  intros. split.
  rewrite -> elem_of_list_In.
  split; intros.
  - induction xs; simpl in H.
    + contradiction.
    + destruct (f a) eqn:fa.
      * simpl in H. destruct H; subst...
        -- exists a. split... set_solver.
        -- destruct IHxs... deprod.
           exists x. split...
           set_solver.
      * destruct IHxs... deprod.
        exists x. split...
        set_solver.
  - deprod. rewrite -> elem_of_list_In in H.
    induction xs...
    simpl. destruct H; subst...
    + rewrite -> H0...
    + destruct (f a)...
      right...
Qed.

Lemma map_option_length {X Y Z}:
  forall (f: X -> option Y) (g: X -> option Z)
         xs ys1 ys2,
  map_option f xs = Some ys1 ->
  map_option g xs = Some ys2 ->
  length ys1 = length ys2.
Proof with eauto.
  intros f g xs.
  induction xs;
    simpl map_option;
    intros; simplify_eq...
  forced (f a).
  forced (map_option f xs).
  forced (g a).
  forced (map_option g xs).
  simplify_eq. simpl. f_equal.
  apply IHxs...
Qed.

Lemma filter_map_in {X Y} :
  forall (f: X -> option Y) x xs,
    In x (filter_map f xs) <->
    In (Some x) (map f xs).
Proof with eauto.
  intros.
  split; induction xs; simpl; intros...
  (* -> cons *)
  - destruct (f a)...
    + destruct H; subst...
  (* <- cons *)
  - destruct H.
    + rewrite -> H...
    + destruct (f a)...
      right...
Qed.
Hint Resolve -> filter_map_in : searches.
Hint Resolve <- filter_map_in : searches.

Lemma map_compose {X Y Z}:
  forall (f: Y -> Z) (g: X -> Y) xs,
    map f (map g xs) = map (fun x => f (g x)) xs.
Proof with eauto.
  intros.
  induction xs; simpl; f_equal...
Qed.


Lemma in_map_option_retract {X Y}:
  forall (f: X -> option Y) (g: Y -> X),
    (forall x y,
        f x = Some y ->
        x = g y) ->
    forall y xs,
    In (Some y) (map f xs) ->
    In (g y) xs.
Proof with eauto.
  intros.
  induction xs; simpl in H0 |- *...
  destruct H0.
  - left. apply H...
  - right...
Qed.

Lemma search_app :
  forall {X Y} `{EqDecision X} (ps1 ps2 : list (X * Y)) x y,
    search x ps1 = Some y ->
    search x (ps1 ++ ps2) = Some y.
Proof with eauto.
  intros.
  induction ps1; simpl in *...
  - discriminate.
  - destruct a.
    destruct (decEq x x0)...
Qed.
Hint Resolve search_app : searches.

Lemma In_pair_unique :
  forall {X Y} (ps : list (X * Y)) x y1 y2,
    NoDup (map fst ps) ->
    In (x, y1) ps ->
    In (x, y2) ps ->
    y1 = y2.
Proof with eauto.
  intros.
  induction ps.
  - contradiction H0.
  - simpl in H0, H1.
    inversion H; subst.
    destruct H0, H1.
    + congruence.
    + simplify_eq.
      contradict H4; eauto with searches.
    + simplify_eq.
      contradict H4; eauto with searches.
    + apply IHps...
Qed.

Hint Resolve In_pair_unique : searches.

Lemma In_submseteq :
  forall {X} (l1 l2 : list X) (x: X),
    submseteq l1 l2 ->
    In x l1 ->
    In x l2.
Proof with auto.
  intros.
  repeat rewrite <- elem_of_list_In in *.
  apply elem_of_submseteq with l1...
Qed.

Lemma In_sublist :
  forall {X} (l1 l2 : list X) (x: X),
    sublist l1 l2 ->
    In x l1 ->
    In x l2.
Proof with auto.
  intros.
  apply In_submseteq with l1...
  apply sublist_submseteq...
Qed.

Lemma In_drop :
  forall {X} (l : list X) (x: X) (n: nat),
    In x (drop n l) -> In x l.
Proof with auto.
  intros.
  apply In_sublist with (drop n l)...
  apply sublist_drop.
Qed.

Lemma ix_In :
  forall {X} (l: list X) (i: nat) (x: X),
    l !! i = Some x ->
    In x l.
Proof.
  intros. rewrite <- elem_of_list_In.
  apply elem_of_list_lookup_2 with i.
  exact H.
Qed.

Lemma NoDup_drop :
  forall {X} (l: list X) (n: nat),
    NoDup l ->
    NoDup (drop n l).
Proof with auto.
  intros. generalize dependent l.
  induction n; intros.
  - rewrite -> drop_0...
  - replace (S n) with (1 + n) by reflexivity.
    rewrite <- (drop_drop l n 1).
    apply IHn...
    inversion H...
    simpl. constructor.
Qed.

Lemma map_drop :
  forall {X Y} (f: X -> Y) (l: list X) (n: nat),
    map f (drop n l) = drop n (map f l).
Proof with auto.
  intros.
  generalize dependent n.
  induction l; intros.
  - destruct n...
  - destruct n.
    + rewrite -> drop_0...
    + simpl...
Qed.

Hint Resolve ix_In : searches.

Lemma take_S_exists :
  forall {X} (xs: list X) (n: nat),
    length xs >= S n ->
    { x: X & xs = take n xs ++ [x] ++ drop (S n) xs }.
Proof with eauto.
  intros. generalize dependent xs.
  induction n; intros xs len.
  - simpl. destruct xs... exfalso. inversion len.
  - destruct xs.
    + exfalso. inversion len.
    + simpl in *.
      apply le_S_n in len.
      destruct (IHn xs len).
      exists x0.
      f_equal. assumption.
Qed.

Definition searches {X V} `{EqDecision X} (xs: list X) (e : list (X * V)) : option (list V)
  := map_option (flip search e) xs.
    
Lemma In_searches {X V} `{EqDecision X} xs (e: list (X * V)) vs v :
  searches xs e = Some vs ->
  In v vs ->
  exists (x : X), In x xs /\ e !! x = Some v.
Proof with eauto.
  intros.
  unfold searches in *.
  generalize dependent vs.
  induction xs; intros; simpl...
  - inversion H; subst; contradiction.
  - simpl in H.
    forced (search a e).
    forced (map_option (flip search e) xs).
    simplify_eq.
    destruct H0...
    + subst. exists a. eauto.
    + destruct (IHxs l eq_refl H).
      deprod. exists x...
Qed.

Lemma filter_map_ext_in {X Y} (f g: X -> option Y) (xs: list X) :
  forall (ext: forall x, In x xs -> f x = g x), filter_map f xs = filter_map g xs.
Proof with eauto.
  intros.
  induction xs...
  simpl.
  replace (g a) with (f a).
  rewrite -> IHxs.
  reflexivity.
  - intros. apply ext. right...
  - apply ext...
Qed.
