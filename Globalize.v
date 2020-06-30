

Require Import stdpp.tactics.
Require Import stdpp.fin_sets.

Require Import LocalTactics.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import DecEq.
Require Import SXML.

Require Import Steps.
Require Import IO.


Require Import SyntaxParams.
Require Import HeapParams.
Module Globalization(varParams: SyntaxParams)(heapParams: HeapParams).
  Module Import SXML_ := SXML.SXML varParams heapParams.


(************

Definitions for globalization

 ************)

Fixpoint elim_defs
         (vars: list var) (e: exp): exp
  :=
    match e with
    | letsmall x se er =>
      if member x vars
      then (elim_defs vars er)
      else letsmall x se (elim_defs vars er)
    | letabs x xl el er =>
      if member x vars
      then (elim_defs vars er)
      else letabs x xl (elim_defs vars el) (elim_defs vars er)
    | branch vb et ef =>
      branch vb
        (elim_defs vars et)
        (elim_defs vars ef)
    | tail vf va => tail vf va
    | ret x => ret x
    end.

Theorem elim_defs_nil :
  forall e, elim_defs [] e = e.
Proof.
  intros. induction e; simpl.
  - rewrite -> IHe. reflexivity.
  - rewrite -> IHe1. rewrite -> IHe2. reflexivity.
  - rewrite -> IHe1. rewrite -> IHe2. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
Hint Resolve elim_defs_nil.

Lemma elim_defs_app :
  forall ds1 ds2 e,
    elim_defs ds1 (elim_defs ds2 e) =
    elim_defs (ds1 ++ ds2) e.
Proof.
  intros.
  induction e; simpl; try solve [f_equal; assumption].
  (* let small *)
  - destruct (member v ds2); destruct (member v (ds1 ++ ds2)); simpl.
    + exact IHe.
    + destruct (member v ds1);
      exfalso; apply n; apply in_or_app; right; assumption.
    + destruct (member v ds1).
      * exact IHe.
      * rewrite -> in_app_iff in i.
        destruct i; contradiction.
    + destruct (member v ds1).
      * exfalso. apply n0. apply in_or_app.
        left. exact i.
      * f_equal. exact IHe.
  (* let abs *)
  - destruct (member v ds2); destruct (member v (ds1 ++ ds2)); simpl.
    + exact IHe2.
    + exfalso. apply n. apply in_or_app; right; assumption.
    + destruct (member v ds1).
      * exact IHe2.
      * rewrite -> in_app_iff in i.
        destruct i; contradiction.
    + destruct (member v ds1).
      * exfalso. apply n0. apply in_or_app; left; assumption.
      * f_equal; assumption.
Qed.
Hint Resolve elim_defs_app.

Lemma elim_defs_comm :
  forall ds1 ds2 e,
    elim_defs ds1 (elim_defs ds2 e) =
    elim_defs ds2 (elim_defs ds1 e).
Proof.
  intros.
  induction e; simpl;
  try solve [f_equal; assumption].
  - destruct (member v ds1); destruct (member v ds2).
    + assumption.
    + rewrite <- IHe. simpl.
      destruct (member v ds1); try contradiction. reflexivity.
    + rewrite -> IHe. simpl.
      destruct (member v ds2); try contradiction. reflexivity.
    + simpl; destruct (member v ds1); destruct (member v ds2);
        try contradiction.
      f_equal. assumption.
  - destruct (member v ds1); destruct (member v ds2).
    + assumption.
    + rewrite <- IHe2. simpl.
      destruct (member v ds1); try contradiction. reflexivity.
    + rewrite -> IHe2. simpl.
      destruct (member v ds2); try contradiction. reflexivity.
    + simpl; destruct (member v ds1); destruct (member v ds2);
        try contradiction.
      f_equal; assumption.
Qed.

Inductive defined var
:=
  | dtuple : list var -> defined var
  | dabs : var -> exp -> defined var                                
  | dconst : bool -> defined var
.

Inductive defined_svalue (defs2: list (var * value)) : defined var -> svalue -> Prop
  :=
  | defined_stuple xs vals :
      searches xs defs2 = Some vals ->
      defined_svalue defs2 (dtuple _ xs) (stuple vals)
  | defined_sclos xl cl el :
      (forall x,
          free_in x cl ->
          x <> xl -> 
          exists v,
          defs2 !! x = Some v /\ el !! x = Some v) ->
      defined_svalue defs2 (dabs _ xl cl) (sclos (xl, cl, el))
.
Inductive defined_value : defined var -> value -> Prop
  :=
  | defined_tuple_vaddr xs a :
      defined_value (dtuple _ xs) (vaddr a)
  | defined_clos_vaddr xl el a :
      defined_value (dabs _ xl el) (vaddr a)
  | defined_vconst b :
      defined_value (dconst _ b) (vconst b)
.

Definition bind_defined (x: var) (def: defined var) (er: exp): exp
  :=
    match def with
    | dtuple _ se => letsmall x (tupleExp se) er
    | dconst _ b => letsmall x (constExp b) er
    | dabs _ xl el => letabs x xl el er
    end.

Fixpoint bind_globals 
         (terms: list (var * defined var)) (e: exp) : exp
  :=
    match terms with
    | [] => e
    | (bv, bd) :: ts => bind_globals ts (bind_defined bv bd e)
    end.
Lemma bind_globals_app :
  forall t1 t2 e,
    bind_globals (t1 ++ t2) e =
    bind_globals t2 (bind_globals t1 e).
Proof with eauto.
  intros. generalize dependent e.
  induction t1; intro e...
  simpl. destruct a. apply IHt1.
Qed.

(* Definition of globalize *)
Definition globalize 
         (terms: list (var * defined var)) (e: exp) : exp
  :=
    bind_globals terms (elim_defs (map fst terms) e).

Lemma globalize_nil :
  forall p,
    globalize [] p = p.
Proof.
  intros; unfold globalize; simpl.
  apply elim_defs_nil.
Qed.
Hint Resolve globalize_nil.

Inductive var_in_def : var -> defined var -> Prop
  :=
  | dv_tuple v vs :
      In v vs ->
      var_in_def v (dtuple _ vs)
  | dv_abs v xl el :
      free_in v el ->
      v <> xl ->
      var_in_def v (dabs _ xl el)
.
Hint Constructors var_in_def.

Inductive defs_well_scoped : list (var * defined var) -> Type
  (* in Type for random technical reasons to do with existentials *)
  :=
  | dv_nil : defs_well_scoped []
  | dv_cons v d ds :
      (forall v,
        var_in_def v d ->
        In v (map fst ds)) ->
      defs_well_scoped ds ->
      defs_well_scoped ((v, d) :: ds)
.
Hint Constructors defs_well_scoped.

Lemma defs_well_scoped_drop : forall defs n,
    defs_well_scoped defs ->
    defs_well_scoped (drop n defs).
Proof with eauto.
  intros.
  generalize dependent n.
  induction defs; intros.
  - destruct n...
  - destruct n; simpl.
    + exact X.
    + inversion X; subst.
      apply IHdefs...
Qed.

Lemma map_option_all_some {X Y} : forall (f: X -> option Y) vs,
    (forall v, In v vs -> { v2 : Y & f v = Some v2 }) ->
    { vs2 & map_option f vs = Some vs2 }.
Proof.
  intros. induction vs; simpl.
  - eexists; reflexivity.
  - destruct (X0 a) as [v2 ->].
    + repeat constructor.
    + destruct IHvs as [vs2 ->].
      * intros. apply X0.
        right. auto.
      * eexists; reflexivity.
Qed.

(************

Proofs about globalization

 ************)

(* ..., If it's concrete the instance resolver has no problem,
    no clue why it needs the extra help *)
Definition def_in_scope bd (e : env) := forall v, var_in_def v bd -> { vl & search v e = Some vl }.

Theorem lookup_store_path_after_extend :
  forall (h h': heap svalue) (a: addr) (sval: svalue),
    forall (alloc1: alloc h sval = (a, h')),
    forall (path : store_path) (v1 v2: value),
      lookup_store_path h v1 path = Some v2 ->
      lookup_store_path h' v1 path = Some v2.
Proof.
  intros.
  generalize dependent v1.
  pose proof (heap_lookup_earlier _ _ _ _ alloc1) as lookup_carry.
  induction path; intros; simpl in *; destruct v1; try done;
    destruct (h !! a0) eqn:lookup1; subst; try discriminate;
    rewrite -> (heap_lookup_some_later _ _ _ _ alloc1 a0 _ lookup1);
    repeat case_match; subst; try done;
    apply IHpath;
    assumption.
Qed.

(* Define our relations between machine states *)

(* TODO move to set *)
Definition image {X Y XS YS : Type} `{Elements X XS} `{Empty YS, Union YS, Singleton Y YS} (f: X -> option Y) (xs : XS) : YS :=
  list_to_set
    (filter_map (fun x => f x)
         (elements xs)).

(*
Definition is_image {X Y XS YS} `{ElemOf X XS} `{ElemOf Y YS} (f : X -> option Y) (xs : XS) (ys: YS) :=
  forall y,
    elem_of y ys <-> exists x, elem_of x xs /\ f x = Some y.

Theorem image_is_image {X Y XS YS} `{FinSet X XS} `{SemiSet Y YS} (f : X -> option Y) (xs : XS) :
  is_image f xs (image (YS:=YS) f xs).
Proof with auto.
  intros.
  unfold is_image, image.
  intro y; split; intros.
  - rewrite -> elem_of_union_list in H12.
    destruct H12 as [X0 [X0In yIn]].
    set_unfold.
    destruct X0In as [x [? ?]].
    exists x. subst; set_unfold.
    done.
  - rewrite -> elem_of_union_list.
    set_unfold.
    destruct H12 as [x [xIn ?]]; subst.
    eexists.
    split.
    + exists x...
    + rewrite -> H12. set_solver.
Qed.

Instance set_unfold_image {X Y XS YS} `{FSX: FinSet X XS} `{FSY: SemiSet Y YS} {f: X -> option Y} {xs: XS} {y: Y}:
  SetUnfoldElemOf y (image f xs) (exists x, elem_of x xs /\ f x = Some y).
Proof.
  constructor.
  apply image_is_image.
Qed.
*)


Lemma set_union_elements :
  forall {X XS} `{FinSet X XS},
    forall (xs: XS),
    equiv (union_list (map singleton (elements xs))) xs.
Proof with eauto.
  intros.
  set_unfold.
  split; intros.
  - rewrite -> elem_of_union_list in H7.
    destruct H7 as [X0 [X0In xIn]].
    remember (elements xs) as xs'.
    generalize dependent xs.
    induction xs'; intros; subst; simpl in *.
    + apply not_elem_of_nil in X0In. contradiction.
    + set_unfold.
      destruct X0In.
      (* head *)
      * subst. set_unfold. subst.
        rewrite <- elem_of_elements.
        rewrite <- Heqxs'.
        constructor.
      (* rest *)
      * destruct H7 as [? [? yIn]].
        subst. set_unfold. subst.
        rewrite <- elem_of_elements.
        rewrite -> elem_of_list_In in *.
        rewrite <- Heqxs'.
        right. assumption.
  - rewrite -> elem_of_union_list.
    exists (singleton x).
    set_unfold.
    split...
Qed.

Lemma image_union (addrs1 addrs2: addrs) f :
    equiv (image f (union addrs1 addrs2))
          (union (image f addrs1 : addrs) (image f addrs2 : addrs)).
Proof with eauto.
  intros.
  unfold image.
  set_unfold.
  intro x.
  split; intros; deep_set_unfold.
  - destruct H...
  - destruct H; deprod...
Qed.

(*
Lemma image_singleton (a1: addr) (af: addr -> option addr) :
    equiv (image af ({[ a1 ]} : addrs))
          (match (af a1) with
           | Some a2 => {[ a2 ]}
           | None => empty
           end: addrs).
Proof with eauto.
  unfold image. set_unfold.
  intro.
  rewrite -> elem_of_union_list.
  split; intros; deep_set_unfold...
  repeat eexists...
  set_solver.
Qed.
*)

(* We need to have both future and past defs, because lifting a lambda will require eliminating
   definitions before lifting it *)
Fixpoint defs_agree (defs: list (var * defined var)) (c: exp) {struct c} : Prop
  :=
  match c with
  | letsmall v s cr =>
    match s with
    | tupleExp vs =>
      match search v defs with
      | Some (dtuple _ vs') => vs = vs' /\ defs_agree defs cr
      | Some _ => False
      | None => defs_agree defs cr
      end
    | constExp b =>
      match search v defs with
      | Some (dconst _ b') => b = b' /\ defs_agree defs cr
      | Some _ => False
      | None => defs_agree defs cr
      end
    | _ =>
      match member v (map fst defs) with
      | left _ => False
      | right _ => defs_agree defs cr
      end
    end
  | letabs v vl cl cr =>
    match search v defs with
    | Some (dabs _ vl' cl') => ~ In vl (map fst defs) /\ vl = vl' /\ elim_defs (map fst defs) cl = cl' /\
        defs_agree defs cl /\ defs_agree defs cr
    | Some _ => False
    | None => ~ In vl (map fst defs) /\ defs_agree defs cl /\ defs_agree defs cr
    end
  | branch vb ct cf =>
    defs_agree defs ct /\ defs_agree defs cf
  | tail _ _ => True
  | ret _ => True
  end.

Section Relations.
  Definition address_relation := list (addr * addr).

  Definition code_related (defs : list (var * defined var)) (remaining: nat) c cg
    := bind_globals (take remaining defs) (elim_defs (map fst defs) c) = cg /\
       defs_agree defs c.

  Inductive val_related (ar: address_relation) : value -> value -> Prop :=
  | vconst_related b : val_related ar (vconst b) (vconst b)
  | vaddr_related a ag :
      search a ar = Some ag ->
      val_related ar (vaddr a) (vaddr ag).
  Inductive env_related (ar: address_relation) defspast (xs xsg : vars): env -> env -> Prop :=
  | env_vals_related e eg:
      forall
        (live_vars:
           forall x,
             elem_of x xs ->
             e !! x <> None)
      (pairs_related:
         forall x v,
          elem_of x xs ->
          elem_of x xsg ->
          e !! x = Some v ->
          exists vg,
          eg !! x = Some vg /\
          val_related ar v vg)
      (global_vals_agree:
         forall (x: var) (v vg: value),
           In (x, vg) defspast ->
           elem_of x xs ->
           e !! x = Some v ->
           val_related ar v vg)
      (globals_present:
         forall (x: var) (vg: value),
           In (x, vg) defspast ->
           elem_of x xsg ->
             eg !! x = Some vg),
      env_related ar defspast xs xsg e eg.
  Inductive clos_related (ar: address_relation) (defs : list (var * defined var)) (defspast : list (var * value)): clos -> clos -> Prop :=
  | clos_parts_related xl el cl elg clg :
      code_related defs 0 cl clg ->
      ~ In xl (map fst defspast) ->
      env_related ar defspast
                  (difference (free_vars cl) {[ xl ]})
                  (difference (free_vars clg) {[ xl ]}) el elg ->
      clos_related ar defs defspast (xl, cl, el) (xl, clg, elg).
  Inductive sval_related ar defs defspast : svalue -> svalue -> Prop :=
  | stuple_related vs vsg :
      Forall2 (val_related ar) vs vsg ->
      sval_related ar defs defspast (stuple vs) (stuple vsg)
  | sclos_related clos closg :
      clos_related ar defs defspast clos closg ->
      sval_related ar defs defspast (sclos clos) (sclos closg).
  Inductive stack_related ar defs defspast : list clos -> list clos -> Prop :=
  | stack_nil_related :
      stack_related ar defs defspast [] []
  | stack_cons_related clos k closg kg :
      clos_related ar defs defspast clos closg ->
      stack_related ar defs defspast k kg ->
      stack_related ar defs defspast (clos :: k) (closg :: kg).

  Inductive heap_related ar defs defspast (h hg : heap svalue) :=
  | heap_vals_related :
      forall 
        (related_addrs:
           forall (a: addr) sv, h !! a = Some sv ->
                        exists ag svg,
                          search a ar = Some ag /\
                          hg !! ag = Some svg /\
                          sval_related ar defs defspast sv svg)
        (global_addrs:
           (* Each variable has a past definitions
              only for bindings before it *)
           forall x v,
             In (x, v) defspast ->
                match v with
                  (* incorrect value handled in env *)
                | vaddr ag =>
                  exists d svg,
                  In (x, d) defs /\
                  hg !! ag = Some svg /\
                  defined_svalue defspast d svg
                | _ => True
                end),
    heap_related ar defs defspast h hg.

  Inductive state_related ar defs defspast remaining : state -> state -> Prop :=
  | state_parts_related c e h k cg eg hg kg :
      forall
            (* addresses handled in heap *)
            (defspast_sound_val:
               forall x v, In (x, v) defspast -> exists d,
                   In (x, d) defs /\
                   defined_value d v)
            (defspast_same :
               map fst defspast = drop remaining (map fst defs))
            (defspast_valid :
               valid_in_heap defspast hg)
            (ar_heap_dom:
               forall a ag,
                 In (a, ag) ar ->
                 h !! a <> None /\ hg !! ag <> None)
            (code_rel:
              code_related defs remaining c cg)
            (env_rel:
              env_related ar defspast (free_vars c) (free_vars cg) e eg)
            (heap_rel:
              heap_related ar defs defspast h hg)
            (stack_rel:
               stack_related ar defs defspast k kg)
            (ar_nodup:
               NoDup (map fst ar)),
      state_related ar defs defspast remaining (<< c, e, h, k >>) (<< cg, eg, hg, kg >>)
  .

  Lemma exists_fun_p {X Y} (P : Y -> Prop) :
    forall (x: X) (y: Y) (f: X -> option Y),
    (exists y, f x = Some y /\ P y) ->
    f x = Some y ->
    P y.
  Proof.
    intros.
    destruct H as [y0 [? ?]]; simplify_eq.
    done.
  Qed.

  Lemma env_lookup_related : forall ar defspast xs xsg e eg x v vg,
      env_related ar defspast xs xsg e eg ->
      elem_of x xs ->
      elem_of x xsg ->
      e !! x = Some v ->
      eg !! x = Some vg ->
      val_related ar v vg.
  Proof with eauto.
    intros.
    destruct H.
    apply exists_fun_p with x (eg !!)...
  Qed.

  Lemma env_lookups_related : forall ar defspast fvs fvsg e eg xs vs vgs,
      env_related ar defspast fvs fvsg e eg ->
      (forall x, In x xs -> elem_of x fvs) ->
      (forall x, In x xs -> elem_of x fvsg) ->
      searches xs e = Some vs ->
      searches xs eg = Some vgs ->
      Forall2 (val_related ar) vs vgs.
  Proof.
    unfold searches.
    intros.
    generalize dependent vgs.
    generalize dependent vs.
    induction xs; simpl in *; intros vs eqvs vgs eqvgs; simplify_eq.
    - constructor.
    - forced (search a e).
      forced (map_option (flip search e) xs).
      forced (search a eg).
      forced (map_option (flip search eg) xs).
      simplify_eq.
      constructor.
      { eapply env_lookup_related; eauto. }
      apply (IHxs (fun x fi => H0 x (or_intror fi)) (fun x fi => H1 x (or_intror fi)) l eq_refl l0 eq_refl).
  Qed.

  Lemma heap_lookup_related : forall {ar defs defspast h hg a ag sv svg},
      heap_related ar defs defspast h hg ->
      search a ar = Some ag ->
      h !! a = Some sv ->
      hg !! ag = Some svg ->
      sval_related ar defs defspast sv svg.
  Proof with eauto.
    intros.
    destruct H.
    destruct (related_addrs a sv H1).
    deprod.
    simplify_eq...
  Qed.


  End Relations.
  Hint Constructors val_related env_related clos_related sval_related stack_related heap_related state_related : related.
  Hint Resolve env_lookup_related env_lookups_related heap_lookup_related : related.

  (* For consistency, some relations are constructors with one variant,
     so force them to unfold during search *)
  Ltac unfold_simple_related :=
    repeat match goal with
    | H: code_related _ _ _ _ |- _ => unfold code_related in H
    | H: clos_related _ _ _ _ |- _ => destruct H
    | H: env_related _ _ _ _ |- _ => destruct H
    | H: heap_related _ _ _ _ |- _ => destruct H
    end.
    
(* Compatibility over heap extensions in both left and right sides *)
  
  (* Extending environments by related values are related *)

Lemma val_relate_alloc :
  forall a ag ar v1 v2,
    ~ addr_in v1 a ->
    val_related ar v1 v2 ->
    val_related ((a, ag) :: ar) v1 v2.
Proof with eauto.
  intros.
  inversion H0; subst; constructor.
  simpl.
  destruct (decEq a0 a); subst...
  - exfalso...
Qed.

Lemma env_relate_new :
  forall ar defspast xs xsg e1 e2 x v1 v2,
    env_related ar defspast xs xsg e1 e2 ->
    ~ In x (map fst defspast) ->
    val_related ar v1 v2 ->
    env_related ar defspast (union xs {[x]}) (union xsg {[x]}) ((x, v1) :: e1) ((x, v2) :: e2).
Proof with eauto.
  intros.
  destruct H.
  constructor; intros; unfold lookup in *.
  - simpl in *.
    destruct (decEq x0 x); simplify_eq.
    + discriminate.
    + set_unfold. destruct H...
  - simpl in *. destruct (decEq x0 x); simplify_eq.
    + exists v2. split...
    + apply pairs_related...
      set_unfold. destruct H... contradiction.
      set_unfold. destruct H2... contradiction.
  - simpl in *.
    destruct (decEq x0 x); simplify_eq.
    + exfalso. apply H0. eauto with searches.
    + apply global_vals_agree with x0...
      set_unfold. forced H2...
  - simpl in *.
    destruct (decEq x0 x); simplify_eq.
    + exfalso. apply H0. eauto with searches.
    + apply globals_present...
      set_unfold.
      destruct H2...
      contradiction.
Qed.

Lemma env_relate_alloc :
  forall ar defspast xs xsg e1 e2 a ag,
    env_related ar defspast xs xsg e1 e2 ->
    ~ addr_in (e1, xs) a ->
    env_related ((a, ag) :: ar) defspast xs xsg e1 e2.
Proof with eauto.
  intros.
  unfold addr_in, addr_in_env, not in H0.
  destruct H. constructor...
  (* pairs_related *)
  - intros.
    pose proof (pairs_related x v H H1 H2).
    deprod.
    exists vg. split...
    apply val_relate_alloc...
    intro.
    inversion H4; subst.
    eauto 10 with addr_in.
    eauto 10 with addr_in.
  (* *)
  - intros.
    pose proof (global_vals_agree x v vg H H1).
    apply val_relate_alloc...
    intro.
    apply H0.
    eauto 10 with addr_in.
Qed.

Lemma env_relate_subset :
  forall ar defspast xs1 xs2 xsg1 xsg2 e1 e2,
    env_related ar defspast xs2 xsg2 e1 e2 ->
    subseteq xs1 xs2 ->
    subseteq xsg1 xsg2 ->
    env_related ar defspast xs1 xsg1 e1 e2.
Proof with eauto.
  intros.
  set_unfold.
  destruct H; split; intros...
Qed.

Lemma search_head :
  forall (a1 a2 : addr) ar,
    search a1 ((a1, a2) :: ar) = Some a2.
Proof.
  intros. simpl. rewrite -> decEq_refl. reflexivity.
Qed.

Hint Resolve env_relate_new env_relate_alloc : related.

Lemma stack_relate_alloc defs defspast a1 a2 ar s sg :
  stack_related ar defs defspast s sg ->
  ~ addr_in s a1 ->
  stack_related ((a1, a2) :: ar) defs defspast s sg.
Proof with eauto.
  intros.
  induction H; constructor.
  -- inversion H; subst. constructor...
     assert (~ addr_in (el, difference (free_vars cl) {[xl]}) a1).
     { intro. apply H0. eauto with addr_in. }
     assert (forall x, elem_of x (free_vars cl ∖ {[xl]}) -> free_in x cl).
     { intros. set_unfold. deprod... rewrite <- in_free_vars_iff_free_in... }
     eauto with related.
  -- apply IHstack_related.
     eauto with addr_in.
Qed.

Hint Constructors val_related : related.
Hint Resolve search_head : related.
Hint Resolve val_relate_alloc stack_relate_alloc : related.


(************
 Safety hypotheses
 ***********)


Definition defs2_addrs (defs2: list (var * value)): addrs :=
  list_to_set (filter_map (fun x => value_to_addr (x.2)) defs2).


Definition clos_size_g defVars (cls: clos): nat
  := match cls with
      | (xl, el, cl) => 1 + size (difference (difference (free_vars el) {[xl]}) (list_to_set defVars))
      end.
Definition svalue_size_g defVars (sv : svalue): nat
  :=
    match sv with
    | sclos cls => clos_size_g defVars cls
    | stuple vs => 1 + length vs
    end.

Definition addrs_space_g defVars h (addrs1: addrs) :=
    space_of (svalue_size_g defVars) h addrs1.

Instance addrs_space_g_equiv {h defVars} : Proper (equiv ==> eq) (addrs_space_g defVars h).
Proof.
  unfold Proper, respectful.
  intros.
  unfold addrs_space_g.
  enough (Permutation (elements x) (elements y)).
  unfold space_of.
  rewrite -> H0. done.
  rewrite -> H.
  reflexivity.
Qed.

Lemma clos_size_g_lt :
  forall defVars clos,
    clos_size_g defVars clos <= clos_size clos.
Proof.
  intros.
  unfold clos_size_g, clos_size.
  destruct clos0 as [[xl cl] el].
  enough (size (free_vars cl ∖ {[xl]} ∖ list_to_set defVars) <= size (free_vars cl ∖ {[xl]})) by lia.
  apply subseteq_size.
  set_solver.
Qed.
Lemma svalue_size_g_lt :
  forall defVars sv,
    svalue_size_g defVars sv <= svalue_size sv.
Proof with eauto.
  intros.
  destruct sv...
  simpl. apply clos_size_g_lt.
Qed.
Lemma lookup_size_g_lt :
  forall defVars h sv,
    lookup_size (svalue_size_g defVars) h sv <= lookup_size svalue_size h sv.
Proof with eauto.
  intros.
  unfold lookup_size.
  destruct (h !! sv)...
  apply svalue_size_g_lt.
Qed.
Lemma addrs_space_g_lt :
  forall defVars h addrs1,
    addrs_space_g defVars h addrs1 <= space_of svalue_size h addrs1.
Proof with eauto.
  intros.
  unfold addrs_space_g, space_of.
  induction (elements addrs1)...
  simpl.
  pose proof (lookup_size_g_lt defVars h a).
  lia.
Qed.

Inductive globalize_safe (ar: address_relation) (defVars: list var) (defs2: list (var * value)) m n : state -> state -> Prop
  :=
    mk_globalize_safe c e h k cg eg hg kg :
      forall
        (af_safe : forall (addrs1: addrs),
          closed h addrs1 -> 
          (1 + length defs2) * addrs_space0 h addrs1 + m >=
          addrs_space0 hg (union (image (flip search ar) addrs1) (defs2_addrs defs2)))
        (af_safe_g : forall (addrs1: addrs),
          closed h addrs1 -> 
          addrs_space0 h addrs1 + n >=
          addrs_space_g defVars hg (union (image (flip search ar) addrs1) (defs2_addrs defs2))),

        globalize_safe
          ar defVars defs2 m n
          (<< c, e, h, k >>)%interp
          (<< cg, eg, hg, kg >>)%interp.

(************
 Main proofs of efficiency / justification
 - Initial steps: pivot through the globals in the target program,
 - Make single step with same head
 - Pivot through skipped source steps, leaving steps with the same head

 Thankfully for the single steps, we can split them up,
but in the others, Prop-Set divisions mean that they must be together
 ************)

Lemma closure_union_list :
  forall h addrss,
    heap_valid h ->
    equiv
      (closure _ h (union_list addrss))
      (union_list (map (closure _ h) addrss)).
Proof with eauto.
  intros.
  induction addrss; simpl.
  - apply closure_empty...
  - rewrite -> closure_union...
    rewrite -> IHaddrss.
    reflexivity.
Qed.

Instance image_proper {f} : Proper (equiv ==> equiv) (image f : addrs -> addrs).
Proof.
  unfold Proper, respectful.
  intros.
  set_unfold.
  set_solver.
Qed.

Lemma free_vars_elim_defs :
  forall c defVars,
    free_vars (elim_defs defVars c) ⊆ free_vars c ∪ list_to_set defVars.
Proof.
  intros c defVars. deep_set_unfold.
  rename H into x_in.
  induction c; simpl; set_unfold.
    - destruct (member v defVars) eqn:v_in_defs;
      simpl in *; set_unfold.
      + destruct (decEq x v); subst.
        * right. apply elem_of_list_In; done.
        * apply IHc in x_in.
          destruct x_in; eauto.
      + destruct x_in.
        * eauto.
        * destruct H.
          apply IHc in H.
          destruct H; eauto.
    - destruct (member v defVars) eqn:v_in_defs;
        simpl in *; set_unfold.
      + apply IHc2 in x_in. destruct x_in; eauto.
        destruct (decEq x v); subst.
        * right. apply elem_of_list_In; done.
        * left. right. done.
      + destruct x_in.
        * destruct H. apply IHc1 in H.
          destruct H; eauto.
        * destruct H; apply IHc2 in H.
          destruct H; eauto.
    - destruct x_in; subst; eauto.
      destruct H.
      + apply IHc1 in H.
        destruct H; eauto.
      + apply IHc2 in H.
        destruct H; eauto.
    - left. done.
    - left. set_solver.
Qed.

Lemma free_vars_bind_globals :
  forall c defs1 defs2,
    defs_well_scoped (defs1 ++ defs2) ->
    free_vars (bind_globals defs1 c) ⊆ free_vars c ∪ list_to_set (map fst (defs1 ++ defs2)).
Proof with eauto with searches free_in.
  intros.
  generalize dependent c.
  induction defs1; intros.
  - simpl. set_solver.
  - inversion X; subst.
    simpl. pose proof (IHdefs1 X0 (bind_defined v d c)).
    transitivity (free_vars (bind_defined v d c) ∪ list_to_set (map fst (defs1 ++ defs2)))...
    apply union_least; try solve [clear; set_solver].

    clear H.
    destruct d; simpl.
    + set_unfold. intros.
      pose proof (H0 x) as ix.
      rewrite <- elem_of_list_In in ix.
      deep_set_unfold.
      destruct H; deprod...
      right. right...
    + set_unfold. intros.
      pose proof (H0 x) as ix.
      rewrite <- elem_of_list_In in ix.
      deep_set_unfold.
      destruct H; deprod...
      right. right.
      apply ix. constructor...
    + set_unfold. intros.
      forced H. deprod.
      left...
Qed.

Lemma free_vars_related :
  forall c defs remaining,
    defs_well_scoped defs ->
    free_vars (bind_globals (take remaining defs) (elim_defs (map fst defs) c)) ⊆
              free_vars c ∪ list_to_set (map fst defs).
Proof with eauto.
  intros.
  transitivity (free_vars (elim_defs (map fst defs) c) ∪ list_to_set (map fst defs)).
  - rewrite <- (take_drop remaining defs) at 2 3 4.
    apply free_vars_bind_globals.
    rewrite -> take_drop. exact X.
  - apply union_least...
    + apply free_vars_elim_defs.
    + set_unfold. intros. deep_set_unfold.
      right. exists (v, d).
      repeat rewrite -> elem_of_list_In in *.
      split...
Qed.

(*** Initial Steps ***)

(* Prove only safety, first, the relatedness comes in trivially
   since the source program hasn't moved, and including it in here adds
   extra requirements that muddy the induction.
   We'll make sure all globals are live though and then re-establish relation. *)

(* (addrs_space0 (iheap st) (defs2_addrs defs2)) *)

    (* use code relation to split free variables correctly *)
(* *)


Definition has_globals (defs2 : list (var * value)) (eg: env): Prop
  :=
    forall (x: var) v,
    eg !! x = Some v <->
    defs2 !! x = Some v.

Lemma in_fst_pair : forall {A B} x (ps : list (A * B)),
    In x (map fst ps) ->
    exists y, In (x, y) ps.
Proof with auto.
  intros.
  induction ps; try contradiction.
  destruct H; subst.
  - destruct a; simpl.
    exists b...
  - destruct (IHps H) as [y iny].
    exists y. right...
Qed.

Lemma defined_svalue_extend : forall d sv defs x v,
    ~ In x (map fst defs) ->
    defined_svalue defs d sv ->
    defined_svalue ((x, v) :: defs) d sv.
Proof with eauto.
  intros.
  destruct H0; constructor.
  - unfold searches in *.
    generalize dependent vals.
    induction xs; intros vals lkps.
    + simpl in *; congruence.
    + simpl in *. destruct (decEq a x).
      { subst. exfalso. apply H.
        forced (search x defs). eauto with searches. }
      forced (search a defs).
      forced (map_option (flip search defs) xs).
      simplify_eq.
      rewrite -> IHxs with l...
  - intros.
    pose proof (H0 x0 H1 H2).
    deprod.
    exists v0. split...
    simpl. destruct (decEq x0 x).
    { subst. exfalso. apply H. eauto with searches. }
    unfold lookup. simpl.
    eauto with decEq.
Qed.

Lemma inner_scoped :
  forall bx bd defs x,
    defs_well_scoped defs ->

    In (bx, bd) defs ->
    var_in_def x bd ->
    In x (map fst defs).
Proof with eauto.
  intros. induction defs...
  simpl in *.
  inversion X; subst.
  destruct H; simplify_eq; right...
Qed.


Lemma searches_extend x y (ps:env) ys l :
  ~ In x (map fst ps) ->
  searches l ps = Some ys ->
  searches l ((x, y) :: ps) = Some ys.
Proof with eauto with searches.
  intros.
  generalize dependent ys.
  unfold searches.
  induction l; simpl; intros...
  (* cons *)
  forced (search a ps).
  forced (map_option (flip search ps) l).
  simplify_eq.
  destruct (decEq a x); subst...
  { contradict H... }
  rewrite -> (IHl l0)...
Qed.

Definition defined_size (d: defined var) :=
  match d with
  | dconst _ _ => 0
  | dabs _ xl cl => 1 + size (difference (free_vars cl) {[xl]})
  | dtuple _ xs => 1 + length xs
  end.

Definition defined_size_g defVars (d: defined var) :=
  match d with
  | dconst _ _ => 0
  | dabs _ xl cl => 1 + size (difference (difference (free_vars cl) {[xl]}) (list_to_set defVars))
  | dtuple _ xs => 1 + length xs
  end.

Theorem initial_step :
  (* Take one step in the target,
     given original state just before
     the binding (bx, bd), incorporate it into
     the definitions present in the environment

     |     ...    |
     |  defspast  |
     +------------+
     |  (bx, bd)  |
     +------------+
     | defsfuture |
     |     ...    |

     In effect, elements will be filtered from
     the defsfuture portion into defspast, eventually being the identity
     This is true without transparency since it appears in the type signature.

     The environment eg serves as both the lookup for definitions, and the
     environment of steps, but future steps will leave the definitions portion unchanged

     It is important that defspast and the environment are equivalent so that e.g.
     projections are still known to be in the globals
  *)
  forall bx bd defs n P sg sg' i,
    NoDup (map fst defs) ->
    defs_well_scoped defs ->

    defs !! n = Some (bx, bd) ->

    let s := start_state P in
    state_related [] defs (ienv sg) (S n) s sg ->
    step i sg sg' ->

    state_related [] defs (ienv sg') n s sg' /\
    (addrs_space0 (iheap sg) (defs2_addrs (ienv sg)) = (sum_list (map defined_size (map snd (drop (S n) defs)))) ->
     addrs_space0 (iheap sg') (defs2_addrs (ienv sg')) = (sum_list (map defined_size (map snd (drop n defs))))) /\
    (addrs_space_g (map fst defs) (iheap sg) (defs2_addrs (ienv sg)) = (sum_list (map (defined_size_g (map fst defs)) (map snd (drop (S n) defs)))) ->
     addrs_space_g (map fst defs) (iheap sg') (defs2_addrs (ienv sg')) = (sum_list (map (defined_size_g (map fst defs)) (map snd (drop n defs))))).
Proof with eauto.
  intros bx bd defs n P sg sg' i.
  intros nodup0 scoped0 futureeq s.
  intros rel0 stp.
  inversion rel0; subst.
  inversion code_rel as [<- agree0].
  subst.
  simpl in stp.
  unfold s in *.
  simpl start_state in *.
  simpl iheap in *.
  simpl ienv in *.

  pose proof (drop_S defs _ _ futureeq) as drop_n.
  pose (f_equal (map fst) drop_n) as drop_fstn.
  simpl in drop_fstn.
  repeat rewrite -> map_drop in drop_fstn.
  assert (nodup_n: NoDup (drop n (map fst defs))) by (apply NoDup_drop; eauto).
  rewrite -> drop_fstn in nodup_n.

  assert (bx_new: ~ In bx (map fst eg)).
  { rewrite -> defspast_same.
    inversion nodup_n... }

  replace (take (S n) defs) with (take n defs ++ [(bx, bd)]) in *
    by (symmetry; apply take_S_r; eauto).
  rewrite -> bind_globals_app in stp.
    
  destruct bd; inversion stp; simpl ienv in *; subst.
  - simpl in *.
    split. split...
    (* def values *)
    + intros. simpl in H.
      destruct H; simplify_eq...
      exists (dtuple var l). split...
      * eauto with searches.
      * constructor.
    (* same *)
    + simpl. symmetry. rewrite -> defspast_same. eapply drop_S...
      rewrite -> list_lookup_fmap.
      rewrite -> futureeq. simpl...
    (* valid *)
    + eauto 10 with addr_in.
    (* code *)
    + split...
    (* env *)
    + inversion env_rel; subst.
      constructor; unfold lookup in *. simpl; intros.
      * apply (live_vars x)...
      * intros. discriminate H1.
      * intros. simpl.
        destruct H; simplify_eq.
      * intros. simpl.
        destruct (decEq x bx); destruct H; simplify_eq...
        -- pose proof (globals_present bx vg H).
           absurd (In bx (map fst eg)).
           ++ inversion nodup_n; subst.
              rewrite <- defspast_same in H4...
           ++ eauto with searches.
        -- apply globals_present...
           rewrite -> bind_globals_app. simpl.
           clear - n0 H0. set_unfold...
    (* heap *)
    + destruct heap_rel; constructor.
      * intros.
        pose proof (related_addrs a0 sv H).
        deprod.
        inversion H0.
      * intros.
        destruct v...
        simpl in H.
        destruct H; simplify_eq...
        -- exists (dtuple var l).
           exists (stuple vs).
           repeat split_and...
           ++ eauto with searches.
           ++ eauto with heaps.
           ++ apply defined_svalue_extend...
              constructor...
        -- pose proof (global_addrs x _ H).
           simpl in H0.
           deprod.
           exists d, svg.
           repeat split_and...
           eauto with heaps.
           apply defined_svalue_extend...
    (* stack; empty *)
    + inversion stack_rel; subst; constructor.
    (* safe *)
    + split; intros.
      * assert (a_fresh : {[a]} ## (list_to_set (filter_map (λ x : var * value, value_to_addr x.2) eg) : addrs)).
        { set_unfold. intros. subst.
          assert (hg !! a = None) by eauto with heaps.
          enough (hg !! a <> None) by congruence.
          apply defspast_valid.
          deep_set_unfold.
          exists v, (vaddr a).
          split...
          assert (NoDup (map fst eg)).
          { inversion nodup_n; subst. rewrite -> defspast_same... }
          unfold lookup.
          eauto with searches. }
        simpl. rewrite -> drop_n. simpl.
        rewrite <- H.
        unfold defs2_addrs. simpl.
        unfold addrs_space0, space_of.
        rewrite -> elements_disj_union...
        rewrite -> elements_singleton. simpl.
        assert (h' !! a = Some (stuple vs)) by eauto with heaps.
        unfold lookup_size.
        rewrite -> H0. simpl.
        f_equal.
        replace (length l) with (length vs).
        f_equal. f_equal.
        apply map_ext_in.
        intros.
        assert (a0 <> a).
        { rewrite <- elem_of_list_In in H1. set_unfold... }
        assert (hg !! a0 = h' !! a0) by eauto with heaps.
        destruct (hg !! a0) eqn:hga0.
        rewrite <- H3...
        rewrite <- H3...
        { unfold searches in lkps.
          eapply map_option_length with (flip search eg) (fun x => Some x) _...
          clear. induction l; simpl...
          rewrite -> IHl. reflexivity. }
      * assert (a_fresh : {[a]} ## (list_to_set (filter_map (λ x : var * value, value_to_addr x.2) eg) : addrs)).
        { set_unfold. intros. subst.
          assert (hg !! a = None) by eauto with heaps.
          enough (hg !! a <> None) by congruence.
          apply defspast_valid.
          deep_set_unfold.
          exists v, (vaddr a).
          split...
          assert (NoDup (map fst eg)).
          { inversion nodup_n; subst. rewrite -> defspast_same... }
          unfold lookup.
          eauto with searches. }
        simpl. rewrite -> drop_n. simpl.
        rewrite <- H.
        unfold defs2_addrs. simpl.
        unfold addrs_space_g, space_of.
        rewrite -> elements_disj_union...
        rewrite -> elements_singleton. simpl.
        assert (h' !! a = Some (stuple vs)) by eauto with heaps.
        unfold lookup_size.
        rewrite -> H0. simpl.
        f_equal.
        replace (length l) with (length vs).
        f_equal. f_equal.
        apply map_ext_in.
        intros.
        assert (a0 <> a).
        { rewrite <- elem_of_list_In in H1. set_unfold... }
        assert (hg !! a0 = h' !! a0) by eauto with heaps.
        destruct (hg !! a0) eqn:hga0.
        rewrite <- H3...
        rewrite <- H3...
        { unfold searches in lkps.
          eapply map_option_length with (flip search eg) (fun x => Some x) _...
          clear. induction l; simpl...
          rewrite -> IHl. reflexivity. }
  (* same exact case, make lemma for alloc ?*)
  - simpl in *.
    split. split...
    (* defspast -> defs *)
    + intros. simpl in H.
      destruct H; simplify_eq...
      exists (dabs var v e). split...
      * eauto with searches.
      * constructor.
    (* same *)
    + simpl. symmetry. rewrite -> defspast_same. eapply drop_S...
      rewrite -> list_lookup_fmap.
      rewrite -> futureeq. simpl...
    (* valid *)
    + eauto 20 with addr_in.
    (* code *)
    + split...
    (* env *)
    + inversion env_rel; subst.
      constructor; unfold lookup in *; simpl; intros...
      * intros. apply (live_vars x)...
      * discriminate.
      * discriminate.
      * intros. simpl.
        destruct (decEq x bx); destruct H; simplify_eq...
        -- pose proof (globals_present bx vg H).
           absurd (In bx (map fst eg)).
           ++ inversion nodup_n; subst.
              rewrite <- defspast_same in H4...
           ++ eauto with searches.

        -- apply globals_present...
           rewrite -> bind_globals_app. simpl.
           clear - n0 H0. set_unfold...
    (* heap *)
    + destruct heap_rel; constructor.
      * intros.
        pose proof (related_addrs a0 sv H).
        deprod.
        inversion H0.
      * intros.
        destruct v0...
        simpl in H.
        destruct H; simplify_eq...
        -- exists (dabs var v e), (sclos (v, e, eg)).
           repeat split_and...
           ++ eauto with searches.
           ++ eauto with heaps.
           ++ apply defined_svalue_extend...
              constructor...
              intros. unfold lookup. simpl.

              pose proof (defs_well_scoped_drop defs n scoped0).
              rewrite -> drop_n in X.
              inversion X; subst.
              rewrite -> map_drop in H2.
              rewrite <- defspast_same in H2.
              assert (var_in_def x0 (dabs var v e))...
              pose proof (H2 x0 H1).
              destruct (In_fst_search _ _ H3)...
        -- pose proof (global_addrs x _ H).
           simpl in H0.
           deprod. exists d, svg. repeat split_and...
           ++ eauto with heaps.
           ++ apply defined_svalue_extend...
    (* stack; empty *)
    + inversion stack_rel; subst; constructor.
    (* safe *)
    + split; intros.
      * assert (a_fresh : {[a]} ## (list_to_set (filter_map (λ x : var * value, value_to_addr x.2) eg) : addrs)).
        { set_unfold. intros. subst.
          assert (hg !! a = None) by eauto with heaps.
          enough (hg !! a <> None) by congruence.
          apply defspast_valid.
          deep_set_unfold.
          exists v0, (vaddr a).
          split...
          assert (NoDup (map fst eg)).
          { inversion nodup_n; subst. rewrite -> defspast_same... }
          unfold lookup.
          eauto with searches. }
        simpl. rewrite -> drop_n. simpl.
        rewrite <- H.
        unfold defs2_addrs. simpl.
        unfold addrs_space0, space_of.
        rewrite -> elements_disj_union...
        rewrite -> elements_singleton. simpl.
        assert (h' !! a = Some (sclos (v, e, eg))) by eauto with heaps.
        unfold lookup_size.
        rewrite -> H0. simpl.
        do 3 f_equal.
        apply map_ext_in.
        intros.
        assert (a0 <> a).
        { rewrite <- elem_of_list_In in H1. set_unfold... }
        assert (hg !! a0 = h' !! a0) by eauto with heaps.
        destruct (hg !! a0) eqn:hga0.
        rewrite <- H3...
        rewrite <- H3...
      * assert (a_fresh : {[a]} ## (list_to_set (filter_map (λ x : var * value, value_to_addr x.2) eg) : addrs)).
        { set_unfold. intros. subst.
          assert (hg !! a = None) by eauto with heaps.
          enough (hg !! a <> None) by congruence.
          apply defspast_valid.
          deep_set_unfold.
          exists v0, (vaddr a).
          split...
          assert (NoDup (map fst eg)).
          { inversion nodup_n; subst. rewrite -> defspast_same... }
          unfold lookup.
          eauto with searches. }
        simpl. rewrite -> drop_n. simpl.
        rewrite <- H.
        unfold defs2_addrs. simpl.
        unfold addrs_space_g, space_of.
        rewrite -> elements_disj_union...
        rewrite -> elements_singleton. simpl.
        assert (h' !! a = Some (sclos (v, e, eg))) by eauto with heaps.
        unfold lookup_size.
        rewrite -> H0. simpl.
        f_equal. f_equal. f_equal.
        apply map_ext_in.
        intros.
        assert (a0 <> a).
        { rewrite <- elem_of_list_In in H1. set_unfold... }
        assert (hg !! a0 = h' !! a0) by eauto with heaps.
        destruct (hg !! a0) eqn:hga0.
        rewrite <- H3...
        rewrite <- H3...
  (* const *)
  - split. split...
    + simpl. intros.
      destruct H; simplify_eq...
      exists (dconst var b).
      split; try constructor.
      eauto with searches.
    + simpl. symmetry. rewrite -> defspast_same. eapply drop_S...
      rewrite -> list_lookup_fmap.
      rewrite -> futureeq. simpl...
    + simpl ienv in *.
      eauto with addr_in.
    + simpl. intros.
      split...
    (* env *)
    + inversion env_rel; subst.
      constructor; unfold lookup in *; simpl; intros...
      * apply (live_vars x)...
      * discriminate.
      * discriminate.
      * intros. simpl.
        destruct (decEq x bx); destruct H; simplify_eq...
        -- pose proof (globals_present bx vg H).
           absurd (In bx (map fst eg)).
           ++ inversion nodup_n; subst.
              rewrite <- defspast_same in H4...
           ++ eauto with searches.
        -- apply globals_present...
           rewrite -> bind_globals_app. simpl.
           clear - n0 H0. set_unfold...
    (* heap *)
    + inversion heap_rel; subst.
      split...
      * intros.
        pose proof (related_addrs _ _ H).
        deprod. simpl in H0; discriminate.
      * intros.
        simpl in H.
        destruct H; simplify_eq...
        pose proof (global_addrs _ _ H).
        destruct v...
        deprod.
        exists d, svg. repeat split_and...
        apply defined_svalue_extend...
    + inversion stack_rel; constructor.
    + split; intros. simpl.
      * rewrite -> drop_n. simpl.
        rewrite <- H...
      * rewrite -> drop_n. simpl.
        rewrite <- H...
Qed.

Lemma initial_safe :
  forall defs remaining P sg,
    state_related [] defs (ienv sg) remaining (start_state P) sg ->
    globalize_safe [] (map fst defs) (ienv sg)
                   (addrs_space0 (iheap sg) (defs2_addrs (ienv sg)))
                   (addrs_space_g (map fst defs) (iheap sg) (defs2_addrs (ienv sg)))
                   (start_state P) sg.
Proof with eauto.
  intros.
  inversion H; subst.
  constructor.
  - intros.
    rewrite -> closed_empty_iff_empty in H0.
    rewrite -> H0.
    simpl.
    unfold addrs_space0, space_of.
    unfold image. 
    repeat rewrite -> elements_empty.
    simpl.
    rewrite -> Nat.mul_0_r. simpl.
    setoid_replace (union empty (defs2_addrs eg)) with (defs2_addrs eg) by set_solver.
    unfold ge. reflexivity.
  - intros.
    rewrite -> closed_empty_iff_empty in H0.
    rewrite -> H0.
    simpl.
    unfold addrs_space_g, addrs_space0, space_of.
    unfold image. 
    repeat rewrite -> elements_empty.
    simpl.
    setoid_replace (union empty (defs2_addrs eg)) with (defs2_addrs eg) by set_solver.
    unfold ge.
    induction (elements (defs2_addrs eg)); simpl...
Qed.

(* TODO move this into SXML *)
Inductive same_head : exp -> exp -> Prop
  :=
  | same_small cr1 cr2 v se :
      same_head (letsmall v se cr1) (letsmall v se cr2)
  | same_abs v vl cl1 cr1 cl2 cr2 :
      same_head (letabs v vl cl1 cr1) (letabs v vl cl2 cr2)
  | same_branch v ct1 cf1 ct2 cf2 :
      same_head (branch v ct1 cf1) (branch v ct2 cf2)
  | same_tail vf va :
      same_head (tail vf va) (tail vf va)
  | same_ret v :
      same_head (ret v) (ret v)
.

Definition head_not_global (defVars: list var) (e: exp): Prop
  :=
    match e with
    | letsmall x _ _ => not (In x defVars)
    | letabs x xl cl cr => not (In x defVars)
    | _ => True
    end.
Definition head_global (defVars: list var) (e: exp): Prop
  := (* this one is much less common *)
    match e with
    | letsmall x _ _ => In x defVars
    | letabs x xl cl cr => In x defVars
    | _ => False
    end.

Lemma related_head_not_global :
  forall defs c cg,
    elim_defs defs c = cg ->
    head_not_global defs cg.
Proof with eauto.
  intros.
  induction c; subst; simpl in *...
  - destruct (member v defs); subst...
  - destruct (member v defs); subst...
Qed.

Lemma sval_relate_alloc :
  forall ar a ag defs defspast sv svg,
    ~ addr_in sv a ->
    sval_related ar defs defspast sv svg ->
    sval_related ((a, ag) :: ar) defs defspast sv svg.
Proof with eauto.
  intros.
  destruct H0; constructor.
  - (* Induction will mess with the tuple structure,
           so we need to get this fact first *)
    clear - H H0.
    induction H0... constructor.
    (* val related *)
    + apply val_relate_alloc... eauto 20 with addr_in.
    + apply IHForall2...
      eauto 20 with addr_in.
  - inversion H0; subst. constructor...
    (* env *)
    apply env_relate_alloc...
Qed.

(* Common cases for related step *)
Lemma heap_relate_alloc defs defspast ar h hg h' hg' a ag sv svg :

  alloc h sv = (a, h') ->
  alloc hg svg = (ag, hg') ->

  sval_related ar defs defspast sv svg ->
  valid_in_heap h h ->
  valid_in_heap sv h ->

  heap_related ar defs defspast h hg ->
  heap_related ((a, ag) :: ar) defs defspast h' hg'.
Proof with eauto 15 with addr_in heaps.
  intros allocs allocsg svrel hvalid svvalid heaprel.
  destruct heaprel as [heaprel heapglobals].
  constructor.
  - intros a0 sv0 lkp0. destruct (decEq a0 a); subst.
    + exists ag.
      exists svg.
      simpl. rewrite -> decEq_refl.
      repeat split; eauto with heaps.
      assert (h' !! a = Some sv) by eauto with heaps. simplify_eq.

      apply sval_relate_alloc...
      addr_conflict h a.
    + assert (h !! a0 = Some sv0) by eauto with heaps.
      destruct (heaprel a0 sv0) as [ag0 [svg0 [arg [lkpg svgrel]]]]; try assumption.

      exists ag0.
      exists svg0.
      simpl.
      forced (decEq a0 a).
      repeat split...

      (* svals related *)
      eapply sval_relate_alloc...
      addr_conflict h a.
  - clear - allocs allocsg heapglobals.
    intros.
    pose proof (heapglobals _ _ H).
    destruct v...
    deprod.
    exists d, svg0...
Qed.

Definition sub_env (e1 e2 : env) := forall x, search x e1 = search x e2.

Instance list_equiv_reflexive {X} {equiv: X -> X -> Prop}: `(Reflexive equiv) -> Reflexive (@list_equiv _ equiv).
Proof.
  unfold Reflexive.
  intros.
  induction x; constructor.
  - apply H.
  - apply IHx.
Qed.


Lemma space_alloc ar (h h' hg hg' : heap svalue) a ag sv svg addrs1 defaddrs k n (size1 size2: svalue -> nat) :
    alloc h sv = (a, h') ->
    alloc hg svg = (ag, hg') ->
    (forall a0, ~ In (a0, ag) ar) ->
    ~ elem_of ag defaddrs ->

    k >= 1 ->
    k * size1 sv >= size2 svg ->
    let addrs1' := difference addrs1 {[ a ]} in
    k * space_of size1 h addrs1' + n ≥ space_of size2 hg (image (flip search ar) addrs1' ∪ defaddrs) ->
    k * space_of size1 h' addrs1 + n ≥ space_of size2 hg' (image (flip search ((a, ag) :: ar)) addrs1 ∪ defaddrs).
Proof with eauto with searches.
  intros allocs allocg ag_fresh1 ag_fresh2 k_pos sv_svg_size ? initial_space.
  unfold space_of in *.

  assert (image_ag_disj: (image (flip search ar) addrs1' : addrs) ## {[ ag ]}).
  { unfold image. deep_set_unfold.
    assert (In (x0, ag) ar)...
    apply ag_fresh1 in H2...
  }

  assert (addrs'_same: forall a, elem_of a addrs1' -> h' !! a = h !! a).
  { intros. assert (a0 <> a) by set_solver.
    eauto with heaps. }
  assert (addrs'_image_same:
            forall (a: addr), elem_of a (image (flip search ar) addrs1' : addrs) -> hg' !! a = hg !! a).
  { intros. deep_set_unfold.
    eapply heap_lookup_earlier'...
    intro. subst.
    assert (In (x, ag) ar)...
  }
  assert (defaddrs_same : forall a, elem_of a defaddrs -> hg !! a = hg' !! a).
  {
    intros. assert (a0 <> ag) by (intro; subst; contradiction).
    eauto with heaps.
  }

  assert (addrs1'_image: (image (flip search ((a, ag) :: ar)) addrs1' : addrs) = image (flip search ar) addrs1').
  {
    unfold image.
    f_equal.
    apply filter_map_ext_in.
    intros. simpl.
    unfold addrs1'. rewrite <- elem_of_list_In in H.
    set_unfold. deprod. forced (decEq x a)...
  }

  destruct (decide (elem_of a addrs1)).

  (* member *)
  - assert (equiv addrs1 (union addrs1' {[ a ]})).
    { set_unfold. intro.
      destruct (decEq x a). subst.
      split; intros...
      split; intros...
      forced H. deprod...
    }
    assert (addrs1' ## {[ a ]}) by set_solver.
    rewrite -> H.
    rewrite -> image_union.
    rewrite -> elements_disj_union...

    rewrite -> map_app.
    rewrite -> sum_list_app.
    
    (* simplify image of a *)
    unfold image at 2.
    rewrite -> elements_singleton. simpl.
    rewrite -> decEq_refl.

    (* simplify image of addrs1' *)
    rewrite -> addrs1'_image.

    setoid_replace (option_to_set (Some ag) ∪ ∅ : addrs) with
                   ({[ ag ]} : addrs) by (clear; set_solver).

    setoid_replace (image (flip search ar) addrs1' ∪ {[ag]} ∪ defaddrs) with
                   ({[ag]} ∪ (image (flip search ar) addrs1' ∪ defaddrs)) by (clear; set_solver).
    rewrite -> elements_disj_union.
    rewrite -> elements_singleton.
    rewrite -> map_app.
    rewrite -> sum_list_app.
    simpl.

    rewrite -> (map_ext_in (lookup_size size1 h') (lookup_size size1 h)).
    rewrite -> (map_ext_in (lookup_size size2 hg') (lookup_size size2 hg)).
    unfold lookup_size at 2.
    unfold lookup_size at 2.
    assert (lkpa: h' !! a = Some sv) by eauto with heaps.
    assert (lkpag: hg' !! ag = Some svg) by eauto with heaps.
    rewrite -> lkpa.
    rewrite -> lkpag.
    repeat rewrite -> Nat.add_0_r.

    clear - initial_space k_pos sv_svg_size.
    rewrite -> Nat.mul_add_distr_l.
    assert (k * sum_list (map (lookup_size size1 h) (elements addrs1')) >=
            sum_list (map (lookup_size size1 h) (elements addrs1'))).
    { destruct k; try solve [inversion k_pos].
      simpl. lia. }
    lia.

    (* map ext 2, image union defaddrs *)
    + intros.
      unfold lookup_size.
      rewrite <- elem_of_list_In in H1.
      deep_set_unfold.
      destruct H1.
      * rewrite -> (addrs'_image_same a0)...
      * rewrite -> (defaddrs_same a0)...
    (* map ext 1 *)
    + intros.
      rewrite <- elem_of_list_In in H1.
      set_unfold.
      apply addrs'_same in H1.
      unfold lookup_size. rewrite -> H1.
      reflexivity.
    (* union disjoint *)
    + clear - image_ag_disj ag_fresh2. set_solver.
  - assert (H: equiv addrs1' addrs1) by set_solver.
    rewrite -> H in initial_space.
    rewrite <- H.
    rewrite -> addrs1'_image.
    rewrite -> H.
    destruct k; try solve [inversion k_pos].
    simpl.
    (* copy-pasted *)
    rewrite -> (map_ext_in (lookup_size size1 h') (lookup_size size1 h)).
    rewrite -> (map_ext_in (lookup_size size2 hg') (lookup_size size2 hg)).
    lia.
    + intros.
      unfold lookup_size.
      rewrite <- H in H0.
      rewrite <- elem_of_list_In in H0.
      deep_set_unfold.
      destruct H0.
      * rewrite -> (addrs'_image_same a0)...
      * rewrite -> (defaddrs_same a0)...
    (* map ext 1 *)
    + intros.
      rewrite <- H in H0.
      rewrite <- elem_of_list_In in H0.
      set_unfold.
      apply addrs'_same in H0.
      unfold lookup_size. rewrite -> H0.
      reflexivity.
Qed.

Theorem clos_size_related :
  forall ar defs defspast clos1 clos2,
    clos_related ar defs defspast clos1 clos2 ->
    (1 + length defs) * clos_size clos1 >= clos_size clos2.
Proof with eauto.
  intros.
  inversion H; subst.
  destruct H0.
  simpl in H0.
  pose proof (free_vars_elim_defs cl (map fst defs)).

  inversion H; subst.
  unfold code_related in *.
  simpl in H. deprod.
  simpl take. simpl bind_globals.
  pose (elim_defs (map fst defs) cl) as cl2.
  assert (free_vars_subset: subseteq (free_vars cl2) (union (free_vars cl) (list_to_set (map fst defs)))).
  {
    subst cl2. simpl.
    apply free_vars_elim_defs.
  }
  subst cl2.
  simpl bind_globals in *.
  simpl map in *.
  simpl app in *.
  remember (free_vars (elim_defs (map fst defs) cl)) as fv2.
  remember (free_vars cl) as fv1.
  remember (list_to_set (map fst defs)) as defVars.
  assert (subseteq (difference fv2 {[xl]}) (union (difference fv1 {[xl]}) defVars))
    by (clear - free_vars_subset; set_solver).
  assert (size (difference fv2 {[xl]}) <= size (difference fv1 {[xl]}) + size defVars).
  {
    assert (size (difference fv2 {[xl]}) <= size (union (difference fv1 {[xl]}) defVars)).
    { apply subseteq_size... }
    enough (size (union (difference fv1 {[xl]}) defVars) <= size (difference fv1 {[xl]}) + size defVars) by lia.
    rewrite -> size_union_alt.
    enough (size (difference defVars (difference fv1 {[xl]})) <= size defVars) by lia.
    clear.
    apply subseteq_size.
    set_solver.
  }
  simpl.
  rewrite <- Heqfv1.
  rewrite <- Heqfv2.
  (* equal, but this is enough *)
  assert (length (map fst defs) >= size defVars).
  {
    subst defVars. generalize (map fst defs).
    clear.
    induction l; simpl.
    - rewrite -> size_empty...
    - rewrite -> size_union_alt.
      rewrite -> size_singleton.
      enough (size (difference (list_to_set l : vars) {[a]}) <= size (list_to_set l: vars)) by lia.
      apply subseteq_size. set_solver.
  }
  clear - H3 H7 H8.
  rewrite -> map_length in H8.
  rewrite -> Nat.mul_succ_r.
  simpl.
  lia.
Qed.
Theorem clos_size_related_g :
  forall ar defs defspast clos1 clos2,
    clos_related ar defs defspast clos1 clos2 ->
    clos_size clos1 >= clos_size_g (map fst defs) clos2.
Proof with eauto.
  intros.
  inversion H; subst.
  destruct H0.
  simpl in H0.
  pose proof (free_vars_elim_defs cl (map fst defs)).

  inversion H; subst.
  unfold code_related in *.
  simpl in H. deprod.
  simpl take. simpl bind_globals.
  pose (elim_defs (map fst defs) cl) as cl2.
  assert (free_vars_subset: subseteq (free_vars cl2) (union (free_vars cl) (list_to_set (map fst defs)))).
  {
    subst cl2. simpl.
    apply free_vars_elim_defs.
  }
  subst cl2.
  simpl bind_globals in *.
  simpl map in *.
  simpl app in *.
  remember (free_vars (elim_defs (map fst defs) cl)) as fv2.
  remember (free_vars cl) as fv1.
  remember (list_to_set (map fst defs)) as defVars.
  assert (subseteq (difference fv2 {[xl]}) (union (difference fv1 {[xl]}) defVars))
    by (clear - free_vars_subset; set_solver).
  simpl.
  rewrite <- Heqfv1.
  rewrite <- Heqfv2.
  rewrite <- HeqdefVars.
  (* equal, but this is enough *)
  clear - H3 H6.
  unfold ge. apply le_n_S.
  apply subseteq_size.
  set_solver.
Qed.

Theorem related_step ar defs defspast m n s sg s' sg' i :
    same_head (icode s) (icode sg) ->

    state_valid s ->
    state_valid sg ->

    NoDup (map fst defs) ->
    True ->

    step i s s' ->
    step i sg sg' ->

    state_related ar defs defspast 0 s sg
    /\ globalize_safe ar (map fst defs) defspast m n s sg ->
    exists ar',
      state_related ar' defs defspast 0 s' sg'
      /\ globalize_safe ar' (map fst defs) defspast m n s' sg'.
Proof with (auto || contradiction || eauto with related decEq).
  intros head valid validg nodup samedefs st1 stg1 [rel0 safe0].
  destruct rel0.
  rewrite -> drop_0 in defspast_same.

  inversion head; simpl in *; subst;
    inversion st1; subst; inversion stg1; subst;
      repeat unfold_simple_related;
      destruct code_rel as [code_rel agree0];
      pose proof (related_head_not_global (map fst defs) _ _ code_rel) as not_global.
  (* tuple *)
  - exists ((a, a0) :: ar).
    split.
    (* related *)
    + split; simpl in not_global |- *...
      * eauto with addr_in.
      * intros. destruct H; simplify_eq...
        -- split; eauto with heaps.
        -- pose proof (ar_heap_dom _ _ H).
           deprod. eauto with heaps.
      * simpl in code_rel, agree0.
        rewrite -> (not_In_if_member _ _ _ _ not_global) in code_rel.
        inversion code_rel; subst.
        intros.
        constructor... destruct (search v defs)...
        destruct d; deprod...
      * rewrite <- defspast_same in not_global.
        assert (~ addr_in (e, (free_vars (VAL v := tupleExp xs IN cr1)%exp)) a) by (intro; addr_conflict h a).
        eapply env_relate_subset.
        apply env_relate_new...
        -- simpl. set_unfold. intros. destruct (decEq x v)...
        -- simpl. set_unfold. intros. destruct (decEq x v)...
      * eapply (heap_relate_alloc _ _ _ _ _ _ _ _ _ _ _ alloc_tuple alloc_tuple0); eauto 20 with addr_in.
        -- constructor.
           assert (forall x, In x xs -> free_in x (VAL v := tupleExp xs IN cr2)%exp).
           { intros. apply free_smallExp.
             constructor... }
           eapply env_lookups_related...
           { intros. simpl. set_unfold... left. rewrite -> elem_of_list_In... }
           intros.
           rewrite -> in_free_vars_iff_free_in...
        -- assert (forall x, In x xs -> free_in x (VAL v := tupleExp xs IN cr1)) by eauto with free_in.
           eauto 20 with addr_in.
      * clear - stack_rel alloc_tuple valid.
        induction stack_rel; (constructor; try done).
        (* closure in stack *)
        -- inversion H. subst; split; eauto with related decEq.
           eapply env_relate_alloc...
           addr_conflict h a.
        (* rest of stack *)
        -- apply IHstack_rel.
           clear - valid.
           unfold valid_in_heap, addr_in, addr_in_state in *.
           intros. apply valid.
           destruct H...
           destruct H...
           right. left.
           eauto 20 with addr_in.
      * assert (~ In a (map fst ar)).
        { intro. apply In_fst_search in H.
          deprod. assert (In (a, y) ar) by eauto with searches.
          destruct (ar_heap_dom a y)...
          addr_conflict h a. }
        constructor...
    (* safe *)
    + assert (lens: length vs = length vs0) by (eapply (map_option_length _ _ xs); eauto).
      destruct env_rel.
      destruct heap_rel.
      inversion safe0; subst.

      assert (∀ a1 : addr, ¬ In (a1, a0) ar).
      { unfold not. intros.

        absurd ((hg !! a0) = None).
        -- destruct (ar_heap_dom a1 a0)...
        -- eauto with heaps. }
      assert (a0 ∉ defs2_addrs defspast).
      {intro.
        unfold defs2_addrs in *.
        set_unfold.
        deprod.
        rewrite -> elem_of_list_In in H0.
        simpl in H1.
        forced v1. simpl in H1.
        simplify_eq.
        assert (NoDup (map fst defspast)) by congruence.
        assert (search v0 defspast = Some (vaddr a0)) by eauto with searches.

        addr_conflict hg a0. }

      constructor.
      * intros. unfold addrs_space0, lookup_size in *.
        apply space_alloc with h hg (stuple vs) (stuple vs0)...
        (* size *)
        -- lia.
        -- simpl. rewrite -> lens. simpl. lia.
        -- assert (closed h (difference addrs1 {[a]})).
           { eapply closed_alloc_3... eauto 10 with addr_in. }
           apply af_safe...
      * intros. unfold addrs_space0, space_of, addrs_space_g, lookup_size in *.
        rewrite <- (Nat.mul_1_l (sum_list _)) at 1.
        unfold lookup_size in *.
        apply space_alloc with h hg (stuple vs) (stuple vs0); simpl...
        (* size *)
        -- lia.
        -- assert (closed h (difference addrs1 {[a]})).
           { eapply closed_alloc_3... eauto 10 with addr_in. }
           rewrite -> Nat.add_0_r.
           apply af_safe_g...
  (* app *)
  - (* simplify all the lookup info *)
    unfold lookup_object, lookup in *.
    forced (search xa e).
    forced (search xa eg).
    forced (search xf e).
    forced (search xf eg).
    simplify_eq.
    forced v4. forced v5. simplify_eq.
    forced (heap_lookup _ a h).
    forced (heap_lookup _ a0 hg).
    inversion env_rel; simplify_eq.
    unfold lookup in pairs_related.
    destruct (pairs_related xf (vaddr a)) as [? [? vgrel]]...
    { eauto with free_in. }
    { eauto with free_in. }
    inversion vgrel; simplify_eq.

    (* via heap related, force closures related *)
    pose proof (heap_lookup_related heap_rel H1 Heqo3 Heqo4) as H.
    inversion H; subst; clear H.
    inversion H3; subst; clear H3.
    deprod.
    exists ar.
    split; try solve [inversion safe0; done].
    deprod.
    split...
    (* env *)
    * intros.
      eapply env_relate_subset.
      eapply env_relate_new...
      eapply env_lookup_related with defspast _ _ e eg xa ...
      { eauto with free_in. }
      -- clear. simpl. set_unfold. destruct (decEq xa v)...
      -- clear. simpl. set_unfold. intros. destruct (decEq x xl0)...
      -- clear. simpl. set_unfold. intros. destruct (decEq x xl0)...
    (* stack *)
    * constructor...
      constructor...
      (* code *)
      -- inversion code_rel; subst.
         rewrite -> (not_In_if_member) in H0...
         inversion H0; subst.
         constructor...
         simpl in agree0.
         rewrite -> (not_In_if_member) in agree0...
      -- congruence.
      -- eapply env_relate_subset...
         clear. simpl. set_unfold. intros. deprod. right...
         clear. simpl. set_unfold. intros. deprod. right...
  (* proj *)
  - exists ar.
    split; try solve [inversion safe0; done].
    deprod.
    split...
    split...
    (* code 1 *)
    + clear - code_rel not_global.
      deprod.
      unfold code_related in *. simpl in *.
      rewrite -> (not_In_if_member _ _ _ _ not_global) in code_rel.
      inversion code_rel; done.
    (* defs agree *)
    + simpl in agree0. destruct (member v (map fst defs))...
    (* env related *)
    + unfold lookup_object in *.
      forced (e !! xt).
      forced (eg !! xt).
      forced v2.
      forced v3.
      assert (search a ar = Some a0).
      { assert (rel: val_related ar (vaddr a) (vaddr a0)).
        eapply env_lookup_related; eauto with free_in.
        simpl. inversion rel... }
      assert (svrel: sval_related ar defs defspast (stuple vs) (stuple vs0)) by eauto with related.
      inversion svrel; subst.

      simpl in not_global.
      eapply env_relate_subset.
      apply env_relate_new...
      * congruence.
      * eapply (Forall2_nth _ vs vs0 i0 _ _ H2)...
      * simpl. clear. set_unfold. intros. destruct (decEq x v)...
      * simpl. clear. set_unfold. intros. destruct (decEq x v)...
  (* write *)
  - exists ar.
    split; try solve [inversion safe0; done].
    deprod.
    split...
    split...
    + clear - code_rel not_global.
      unfold code_related in *. simpl in *.
      rewrite -> (not_In_if_member _ _ _ _ not_global) in code_rel.
      congruence.
    (* defs agree *)
    + simpl in agree0. forced (member v (map fst defs))...
    (* env related *)
    + simpl in agree0.
      forced (member v (map fst defs)).
      eapply env_relate_subset.
      eapply env_relate_new...
      congruence.
      * simpl. clear. set_unfold. intros. destruct (decEq x v)...
      * simpl. clear. set_unfold. intros. destruct (decEq x v)...
  (* const *)
  - exists ar.
    split; try solve [inversion safe0; done].
    split...
    split...
    + clear - code_rel not_global.
      deprod.
      unfold code_related in *. simpl in *.
      rewrite -> (not_In_if_member _ _ _ _ not_global) in code_rel.
      congruence.
    (* defs agree *)
    + simpl in agree0. forced (member v (map fst defs))...
      destruct (search v defs)...
      destruct d...
      deprod...
    + rewrite <- defspast_same in not_global.
      eapply env_relate_subset.
      eapply env_relate_new...
      * simpl. clear. set_unfold. intros. destruct (decEq x v)...
      * simpl. clear. set_unfold. intros. destruct (decEq x v)...
  (* abs *)
  - unfold code_related in code_rel.
    simpl elim_defs in *.
    simpl bind_globals in *.
    assert (agree1: defs_agree defs cl1).
    { clear - agree0. simpl in agree0...
      repeat case_match; deprod... }
    assert (agree2: defs_agree defs cr1).
    { clear - agree0. simpl in agree0...
      repeat case_match; deprod... }

    assert (abs_related: sval_related ar defs defspast (sclos (vl, cl1, e)) (sclos (vl, cl2, eg))).
    {
      constructor.
      simpl in agree0.
      assert (code_related defs 0 cl1 cl2).
      { destruct (member v (map fst defs)) eqn:v_global;
          simplify_eq; try done. }
      simpl in env_rel.
      destruct (search v defs)...
      + forced d.
        deprod... subst.
        constructor...
        congruence.
        (* env *)
        eapply env_relate_subset...
        * clear. set_solver.
        * clear. set_solver.
      + deprod... subst.
        constructor...
        congruence.
        (* env *)
        eapply env_relate_subset...
        * clear. set_solver.
        * clear. set_solver.
    }

    exists ((a, a0) :: ar).
    split.
    (* related *)
    + split...
      * eauto with addr_in.
      * simpl. intros.
        destruct H.
        -- simplify_eq.
           split; eauto with heaps.
        -- destruct (ar_heap_dom a1 ag H).
           split; eauto with heaps.
      * simpl in not_global.
        rewrite -> (not_In_if_member _ _ _ _ not_global) in code_rel.
        deprod. inversion code_rel; split...
      (* env *)
      * assert (valid_in_heap (e, free_vars (letabs v vl cl1 cr1)) h) by eauto 20 with addr_in.
        assert (~ addr_in (e, free_vars (letabs v vl cl1 cr1)) a).
        { intro. absurd (h !! a = None).
          ++ eauto with addr_in.
          ++ eauto with heaps.
        }
        assert (~ In v (map fst defspast)).
        { rewrite -> defspast_same.
          intro. simpl in agree0.
          destruct (search v defs) eqn:eqs; eauto with searches.
        }
        eapply env_relate_subset.
        eapply env_relate_new...
        -- simpl. clear. set_unfold. intros. destruct (decEq x v)...
        -- simpl. clear. set_unfold. intros. destruct (decEq x v)...
      (* heap *)
      * apply (heap_relate_alloc _ _ _ _ _ _ _ _ _ _ _ alloc_abs alloc_abs0);
          try (eauto 20 with addr_in)...
        do 2 intro. inversion H; subst.
        apply valid. unfold addr_in, addr_in_state.
        deprod.
        right. right. exists x, v0. split... split... simpl... clear - H1. set_solver.
      (* stack *)
      * clear - alloc_abs stack_rel valid.
        induction stack_rel; constructor.
        -- inversion H; subst. constructor...
           assert (valid_in_heap (el, difference (free_vars cl) {[xl]}) h) by eauto 20 with addr_in.
           assert (~ addr_in (el, difference (free_vars cl) {[xl]}) a) by (intro; absurd (h !! a = None); eauto with addr_in || eauto with heaps).
           eauto with related.
        -- apply IHstack_rel.
           rewrite <- (state_valid_product _ _ h _).
           rewrite <- (state_valid_product _ _ h _) in valid.
           deprod. repeat split...
           unfold valid_in_heap in *.
           intros. eauto with addr_in.
      * assert (~ In a (map fst ar)).
        { intro. apply In_fst_search in H.
          deprod. assert (In (a, y) ar) by eauto with searches.
          destruct (ar_heap_dom a y)...
          addr_conflict h a. }
        constructor...
    (* safe *)
    + destruct env_rel, heap_rel.
      inversion safe0; subst.

      assert (∀ a1 : addr, ¬ In (a1, a0) ar).
      { unfold not. intros.

        absurd ((hg !! a0) = None).
        -- destruct (ar_heap_dom a1 a0)...
        -- eauto with heaps. }
      assert (a0 ∉ defs2_addrs defspast).
      {intro.
        unfold defs2_addrs in *.
        set_unfold.
        deprod.
        rewrite -> elem_of_list_In in H0.
        simpl in H1.
        forced v1. simpl in H1.
        simplify_eq.
        assert (NoDup (map fst defspast)) by congruence.
        assert (search v0 defspast = Some (vaddr a0)) by eauto with searches.

        addr_conflict hg a0. }

      inversion abs_related; subst.
      assert (length defspast = length defs).
      { do 2 rewrite <- (map_length fst).
        congruence. }
      constructor.
      * intros. unfold addrs_space0, lookup_size in *.
        apply space_alloc with h hg (sclos (vl, cl1, e)) (sclos (vl, cl2, eg))...
        (* size *)
        -- lia.
        -- unfold svalue_size.
           rewrite -> H1.
           eapply (clos_size_related _ _ _ (vl, cl1, e) (vl, cl2, eg) H3 ).
        -- assert (closed h (difference addrs1 {[a]})).
          { eapply closed_alloc_3... eauto 10 with addr_in. }
          apply af_safe...
      * intros. unfold addrs_space0, addrs_space_g, space_of, lookup_size in *.
        rewrite <- (Nat.mul_1_l (sum_list _)) at 1.
        unfold lookup_size in *.
        apply space_alloc with h hg (sclos (vl, cl1, e)) (sclos (vl, cl2, eg))...
        (* size *)
        -- unfold svalue_size, svalue_size_g.
           rewrite -> Nat.mul_1_l.
           eapply (clos_size_related_g _ _ _ (vl, cl1, e) (vl, cl2, eg) H3 ).
        -- assert (closed h (difference addrs1 {[a]})).
           { eapply closed_alloc_3... eauto 10 with addr_in. }
           rewrite -> Nat.mul_1_l.
           apply af_safe_g...
  (* branch *)
  - exists ar.
    split; try solve [inversion safe0; done].
    inversion env_rel; subst.
    replace b with b0.
    unfold code_related in *. simpl in code_rel.
    inversion code_rel.
    simpl in agree0.
    deprod.
    subst.
    destruct b0; split; try solve [split; eauto]...
    + eapply env_relate_subset...
      simpl. clear. set_solver.
      simpl. clear. set_solver.
    + eapply env_relate_subset...
      simpl. clear. set_solver.
      simpl. clear. set_solver.
    (* b0 must be the same as b by relatedness *)
    + simpl lookup in *.
      assert (H0: val_related ar (vconst b) (vconst b0)).
      { eapply env_lookup_related...
        simpl. clear. set_solver.
        simpl. clear. set_unfold. left... }
      inversion H0; subst; reflexivity.
  (* ret *)
  - inversion stack_rel; subst.
    inversion H2; subst.
    exists ar.
    split; try solve [inversion safe0; done].
    split...
    eapply env_relate_subset.
    eapply env_relate_new...
    eapply env_lookup_related with defspast _ _ e eg v ...
    simpl. set_solver.
    simpl. set_solver.
    clear. set_unfold. intros. destruct (decEq x xl0)...
    clear. set_unfold. intros. destruct (decEq x xl0)...
Qed.

Theorem source_step ar defs defspast s sg sg' i :
  not_stuck s ->

  same_head (icode s) (icode sg) ->
  state_valid s ->

  state_related ar defs defspast 0 s sg ->
  step i sg sg' ->

  exists s' : state, step i s s'.
Proof with eauto.
  intros notstuck0 head valid rel stg.
  destruct rel. inversion head; subst;
  simpl icode in *; simplify_eq;
    inversion notstuck0; subst;
      try solve [inversion H];
      try solve [pose proof (X true) as invalid; destruct invalid as [invalid _]; inversion invalid].
  - replace i with (None: option io_evt).
    exists s2...
    inversion H; subst; inversion stg; subst; done || solve [inversion H3]...
  - replace i with (Some (write k0)).
    exists s2...
    inversion stg; subst; inversion H; subst.
    (* writes: same value *)
    assert (rel: val_related ar (vconst k0) (vconst b)).
    { eapply env_lookup_related...
      simpl. clear. set_solver.
      simpl. clear. set_solver.
    }
    inversion rel; done.
  - replace i with (None: option io_evt).
    exists s2...
    inversion stg...
  - inversion stg; subst.
    exists s2...
  - inversion stg; subst.
    exists s2...
  - inversion stg; subst.
    solve [inversion stack_rel].
Qed.



Lemma env_extend_source_global :
  forall ar defspast x v vg xs xsg e eg,
    NoDup (map fst defspast) ->
    In (x, vg) defspast ->
    val_related ar v vg ->
    env_related ar defspast xs xsg e eg ->
    env_related ar defspast (union xs {[x]}) xsg ((x, v) :: e) eg.
Proof with eauto.
  intros.
  destruct H2; split...
  (* source exists *)
  - intros. set_unfold.
    unfold lookup. simpl.
    destruct (decEq x0 x)...
    destruct H2...
  (* pairs related *)
  - intros.
    unfold lookup in *. simpl search in *.
    set_unfold.
    destruct (decEq x0 x); simplify_eq...
    destruct H2...
    contradiction.
  (* global vals agree *)
  - intros.
    unfold lookup in *. simpl search in *.
    destruct (decEq x0 x)...
    simplify_eq.
    destruct (In_pair_unique _ _ _ _ H H0 H2).
    exact H1.
    set_unfold.
    destruct H3... contradiction.
Qed.

Lemma heap_extend_source_global :
  forall ar defs defspast a x ag sv svg h h' hg,
    In (x, vaddr ag) defspast ->
    alloc h sv = (a, h') ->
    valid_in_heap sv h ->
    valid_in_heap h h ->
    hg !! ag = Some svg ->
    sval_related ar defs defspast sv svg ->
    heap_related ar defs defspast h hg ->
    heap_related ((a, ag) :: ar) defs defspast h' hg.
Proof with eauto with heaps.
  intros.
  destruct H5; split...
  (* pairs related *)
  - intros. simpl search.
    destruct (decEq a0 a); subst.
    (* a0 = a *)
    + exists ag, svg.
      assert (h' !! a = Some sv)...
      simplify_eq...
       
      repeat split_and...
      apply sval_relate_alloc...
      addr_conflict h a.
    + assert (h !! a0 = Some sv0)...
      pose proof (related_addrs _ _ H6).
      deprod.
      exists ag0, svg0.
      repeat split_and...
      apply sval_relate_alloc...
      addr_conflict h a.
Qed.
    

(*** Skipped steps ***)

Lemma larger_safe :
  forall ar defspast n h h' hg a ag sv size1 size2 k,
    heap_valid h ->
    alloc h sv = (a, h') ->
    addr_in defspast ag ->
    (forall addrs1,
        closed h addrs1 ->
        k * space_of size1 h addrs1 + n
        ≥ space_of size2 hg (image (flip search ar) addrs1 ∪ defs2_addrs defspast)) ->
  forall addrs1,
    closed h' addrs1 ->
  k * space_of size1 h' addrs1 + n
  ≥ space_of size2 hg (image (flip search ((a, ag) :: ar)) addrs1 ∪ defs2_addrs defspast).
Proof with eauto.
  intros.
  pose (difference addrs1 {[a]}) as addrs1'.
  assert (addrs1' ## {[a]}) by set_solver.
  pose (decide (elem_of a addrs1)) as a_elem.
  replace (space_of size1 h' addrs1) with
          (space_of size1 h addrs1' +
           if a_elem then size1 sv else 0).
  setoid_replace (union (image (flip search ((a, ag) :: ar)) addrs1 : addrs) (defs2_addrs defspast)) with
                 (union (image (flip search ar) addrs1' : addrs) (defs2_addrs defspast)).
  assert (closed h addrs1') by (eapply closed_alloc_3; eauto).
  pose proof (H2 _ H5).
  rewrite -> Nat.mul_add_distr_l.
  lia.
  (* image addrs1 union globals is image addrs1' union globals *)
  - deep_set_unfold.
    intros. split; intros; deprod.
    + destruct H5; try solve [right; assumption].
      (* old in image *)
      deprod.
      destruct (decEq x0 a); simplify_eq.
      (* equals a, in globals *)
      * right. unfold addr_in, addr_in_env0 in H1.
        deprod. unfold lookup in *. inversion H6; subst.
        exists (x0, vaddr x); eauto with searches.
      (* else, in old *)
      * left...
    + destruct H5; try solve [right; assumption].
      (* old in image *)
      deprod.
      left. exists x0.
      forced (decEq x0 a)...
  (* addrs_space addrs1 addrs1' *)
  - destruct a_elem.
    (* in addrs1 *)
    + setoid_replace addrs1 with (union addrs1' {[a]}) by (set_unfold; intros x; destruct (decEq x a); subst; intuition).
      rewrite -> addrs_space_union...
      pose (heap_extension_one H0) as h0.
      rewrite -> (addrs_space_extension h0).
      f_equal.
      unfold addrs_space0, space_of. rewrite -> elements_singleton.
      simpl. unfold lookup_size.
      replace (h' !! a) with (Some sv) by eauto with heaps.
      lia.
      (* extension preserves  in addrs1' *)
      * intros. assert (a0 <> a) by set_solver.
        eauto with heaps.
    (* no a in addrs1 *)
    + setoid_replace addrs1 with addrs1' by set_solver.
      pose (heap_extension_one H0) as h0.
      rewrite -> (addrs_space_extension h0).
      lia.
      * intros. assert (a0 <> a) by set_solver.
        eauto with heaps.
Qed.





Theorem skip_source_step ar defs defspast m n s0 sg0 :
    NoDup (map fst defs) ->
    not_stuck s0 ->
    state_valid s0 ->

    state_related ar defs defspast 0 s0 sg0 ->

    head_global (map fst defs) (icode s0) ->

    exists (ar' : address_relation) (s1 : state),
      (step None s0 s1 /\
       state_related ar' defs defspast 0 s1 sg0 /\
       (globalize_safe ar (map fst defs) defspast m n s0 sg0 ->
        globalize_safe ar' (map fst defs) defspast m n s1 sg0)).
Proof with eauto.
  intros nodup0 notstuck0 valid0 rel0 global0.
  destruct rel0.
  rewrite -> drop_0 in defspast_same.
  assert (nodup1: NoDup (map fst defspast)) by congruence.

  assert (hvalid : heap_valid h).
  { apply heap_valid_in_heap_proj_l2r.
    unfold state_valid in valid0.
    rewrite <- state_valid_product in valid0.
    deprod... }

  destruct code_rel.
  simpl in global0. unfold head_global in global0.
  destruct c; simpl in global0; try contradiction;
  inversion notstuck0; subst; try (inversion H); subst.
  (* smallExp *)
  - assert (global1: In v (map fst defspast)) by (rewrite -> defspast_same; exact global0).
    simpl in H0.
    inversion H1; subst; try (rewrite -> (In_if_member _ _ _ _ global0) in H0; contradiction).

    apply In_map_fst_In in global1.
    deprod.
    pose proof (defspast_sound_val v y global1).
    deprod.
    destruct d; simpl in H0; try solve [rewrite -> (In_search _ _ _ nodup0 H) in H0; contradiction].
    inversion H2; subst.
    (* addr *)
    + exists ((a, a0) :: ar).
      exists (<< c, (v, vaddr a) :: e, h', k >>)%interp.
      split...
      split.
      (* related *)
      * split...
        (* relation in heaps *)
        -- intros. inversion heap_rel.
           pose proof (global_addrs v (vaddr a0) global1).
           simpl in H4. deprod.
           destruct H3; simplify_eq; eauto with heaps.
           destruct (ar_heap_dom a1 ag H3); eauto with heaps.
        (* code related *)
        -- pose proof (In_fst_search _ _ global0).
           deprod.
           rewrite -> X0 in H0.
           forced y.
           deprod...
           split... f_equal. simpl.
           rewrite -> In_if_member...
        -- simpl in env_rel.
           forced (member v (map fst defs)).
           eapply env_relate_subset.
           eapply env_extend_source_global...
           ++ eauto with related.
           ++ apply env_relate_alloc...
              addr_conflict h a.
           ++ clear. set_unfold. intros. destruct (decEq x v)...
           ++ simpl. rewrite -> Heqs. reflexivity.
        -- inversion heap_rel; subst.
           pose proof (global_addrs _ _ global1). simpl in H3.
           deprod.
           replace d with (dtuple var l) in * by eauto with searches.
           rewrite -> (In_search _ _ _ nodup0 H3) in H0.
           eapply heap_extend_source_global; eauto 10 with addr_in...
           ++ assert (In v (map fst defs)) by eauto with searches.
              inversion H5; subst.
              assert (valid_in_heap (e, free_vars (VAL v := tupleExp xs IN
                                                                     c)) h) by eauto 20 with addr_in.
              do 2 intro.
              apply H7.
              apply addr_in_searches with xs vs...
              intros. simpl. clear - H10. rewrite <- elem_of_list_In in H10. set_solver.
         
           ++ inversion H5; subst.
              constructor.
              destruct env_rel. simpl in *.
              forced (member v (map fst defs)).
              deprod. subst.
              clear - lkps H7 global_vals_agree.

              generalize dependent vs.
              generalize dependent vals.
              unfold searches.
              induction l; intros vgs lkpvgs vs lkpvs; simpl in *.
              ** simplify_eq. constructor.
              ** forced (search a defspast).
                 forced (map_option (flip search defspast) l).
                 forced (search a e).
                 forced (map_option (flip search e) l).
                 simplify_eq.
                 constructor...
                 --- apply global_vals_agree with a...
                     eauto with searches.
                     clear. set_solver.
                 --- apply IHl...
                     intros.
                     apply global_vals_agree with x...
                     clear - H0. set_solver.
        -- apply stack_relate_alloc...
           addr_conflict h a.
        -- simpl.
           assert (~ In a (map fst ar)).
           { intro. apply In_fst_search in H3.
             deprod. assert (In (a, y) ar) by eauto with searches.
             destruct (ar_heap_dom a y)...
             addr_conflict h a. }
           constructor...
      * intros safe0. inversion safe0; subst.
        constructor.
        -- intros addrs1 caddrs1.
           eapply larger_safe...
           unfold addr_in, addr_in_env0.
           exists v, (vaddr a0). split...
           eauto with searches.
        -- intros addrs1 caddrs1.
           rewrite <- (Nat.mul_1_l (addrs_space0 _ _)) at 1.
           eapply larger_safe...
           unfold addr_in, addr_in_env0.
           exists v, (vaddr a0). split...
           eauto with searches.
           simpl; intros.
           rewrite -> Nat.add_0_r...
    (* constant *)
    + pose proof (In_fst_search _ _ global0).
      deprod.
      rewrite -> X0 in H0.
      forced y.
      deprod; simplify_eq.
      exists ar. exists (<< c, (v, vconst b0) :: e, h, k >>)%interp.
      repeat split_and...
      * split...
        (* code *)
        -- simpl. rewrite -> In_if_member...
           split...
        (* env *)
        -- simpl. rewrite -> In_if_member...
           assert (In (v, dconst var b0) defs) by eauto with searches.
           destruct (In_fst_search _ _ global1) as [vg ?].
           assert (In (v, vg) defspast) by eauto with searches.
           eapply env_relate_subset.
           eapply env_extend_source_global...
           ++ destruct (defspast_sound_val v vg H2).
              deprod.
              assert (x = dconst var b0) by eauto with searches.
              subst.
              inversion H4...
              constructor.
           ++ simpl. clear.
              set_unfold. intros; destruct (decEq x v)...
           ++ simpl.
              forced (member v (map fst defs))...
      * intro safe0.
        inversion safe0; split...
  - pose proof (X true) as [? _].
    inversion s0.
  - inversion H1; subst.
    simpl in H0. rewrite -> In_if_member in H0...
    contradiction.
  - inversion H1; subst.
    simpl in H0.
    destruct (search v defs) eqn:searchv.
    + forced d. deprod.
      simpl in *. subst.
      forced (member v (map fst defs)).
      assert (global1: In v (map fst defspast)) by congruence.
      forced (search v defs).
      simplify_eq.
      pose proof (In_fst_search _ _ global1).
      deprod.
      assert (In (v, y) defspast) by eauto with searches.
      pose proof (defspast_sound_val v y H0).
      deprod.
      assert (In (v, dabs var v1 (elim_defs (map fst defs) c1)) defs) by eauto with searches.
      pose proof (In_pair_unique _ _ _ _ nodup0 H2 H6).
      subst.
      inversion H5; subst.

      exists ((a, a0) :: ar). exists (<< c2, (v, vaddr a) :: e, h', k >>)%interp.

      repeat split_and...
      * split...
        -- destruct heap_rel.
           intros. destruct H7; simplify_eq...
           ++ split; eauto with heaps.
              pose proof (global_addrs v _ H0).
              simpl in H7. deprod... eauto with heaps.
           ++ pose proof (ar_heap_dom _ _ H7).
              deprod; split; eauto with heaps.
        -- split...
        -- eapply env_relate_subset.
           eapply env_extend_source_global...
           { eauto with related. }
           eapply env_relate_alloc...
           addr_conflict h a.
           ++ set_unfold. intros.
              destruct (decEq x v)...
           ++ reflexivity.
        -- inversion heap_rel.
           pose proof (global_addrs v _ H0).
           simpl in H7. deprod.
           
           eapply heap_extend_source_global...
           { do 2 intro.
             inversion H10. deprod.
             apply valid0.
             unfold addr_in, addr_in_state.
             right. right. simpl. exists x, v0.
             repeat split_and...
             clear - H12. set_solver. }
           eauto 20 with addr_in.
           pose proof (In_pair_unique _ _ _ _ nodup0 H2 H7).
           subst.
           inversion H9; subst.
           constructor. constructor...
           ++ constructor...
           ++ congruence.
           ++ destruct env_rel.
              constructor...
              ** intros. set_unfold. deprod...
              ** intros. set_unfold.
                 deprod. rewrite -> in_free_vars_iff_free_in in H11.
                 pose proof (H13 x H11 H14).
                 deprod. exists x0. split...
                 eapply global_vals_agree...
                 eauto with searches.
              ** intros. set_unfold.
                 deprod. rewrite -> in_free_vars_iff_free_in in H11.
                 apply (global_vals_agree x v0 vg)...
                 left. split... eauto with free_in.
              ** intros. set_unfold.
                 deprod.
                 rewrite -> in_free_vars_iff_free_in in H11.
                 pose proof (H13 x H11 H12).
                 deprod...
                 assert (In (x, x0) defspast) by eauto with searches.
                 destruct (In_pair_unique defspast x _ _ nodup1 H10 H16).
                 exact H15.
        -- apply stack_relate_alloc...
           addr_conflict h a.
        -- simpl.
           assert (~ In a (map fst ar)).
           { intro. apply In_fst_search in H7.
             deprod. assert (In (a, y) ar) by eauto with searches.
             destruct (ar_heap_dom a y)...
             addr_conflict h a. }
           constructor...
      * intros. inversion H7; subst. constructor.
        -- eapply larger_safe...
           unfold addr_in, addr_in_env0.
           exists v, (vaddr a0). split...
        -- intros.
           rewrite <- (Nat.mul_1_l (addrs_space0 _ _)).
           eapply larger_safe...
           unfold addr_in, addr_in_env0.
           exists v, (vaddr a0). split...
           intros. simpl. rewrite -> Nat.add_0_r...
    + contradict global0.
      intro. pose proof (In_fst_search_not_None _ _ H).
      contradiction.
  - pose proof (X true) as [? _].
    inversion s.
  - inversion H1.
Qed.

Theorem skip_source_steps ar defs defspast m n s0 sg0 :
    NoDup (map fst defs) ->

    not_stuck s0 ->
    state_valid s0 ->

    state_related ar defs defspast 0 s0 sg0 ->


    exists (ar' : address_relation) (s1 : state) (stp: steps s0 s1),
      (head_not_global (map fst defs) (icode s1) /\
       same_head (icode s1) (icode sg0) /\
       steps_io stp = [] /\
       state_related ar' defs defspast 0 s1 sg0 /\
       (globalize_safe ar (map fst defs) defspast m n s0 sg0 ->
       globalize_safe ar' (map fst defs) defspast m n s1 sg0)).
Proof with try contradiction || eauto.
  intros nodup0 notstuck0 valid0 rel0.
  destruct s0 as [c0 e0 h0 k0].
  generalize dependent k0.
  generalize dependent h0.
  generalize dependent e0.
  generalize dependent ar.

  induction c0; intros ar e0 h0 k0 notstuck0 valid0 rel0;
    destruct sg0 as [cg0 eg0 hg0 kg0]; simpl ienv in *; simpl iheap in *;
      inversion rel0; subst;
        destruct code_rel as [code0 agree0]; simpl in agree0;
  rewrite -> drop_0 in defspast_same.
  (* letsmall *)
  - pose (<< (VAL v := s IN c0)%exp, e0, h0, k0 >>)%interp as s0.
    pose (<< cg0, eg0, hg0, kg0 >>)%interp as sg0.
    destruct s.
    (* tuple *)
    + inversion notstuck0; try inversion H; subst.
      * destruct (member v (map fst defs)) eqn:searchdefs.
        -- pose proof (skip_source_step ar defs defspast m n s0 sg0 nodup0 notstuck0 valid0 rel0 i).
           deprod.
           destruct s1 as [c1 e1 h1 k1].
           replace c1 with c0 in * by (inversion H0; eauto).
           pose (<<c0, e1, h1, k1>>)%interp as s1.
           assert (notstuck1: not_stuck s1) by (apply not_stuck_step with None s0; eauto).
           assert (valid1: state_valid s1) by (apply state_valid_step with s0 None; eauto).
           pose proof (IHc0 ar' e1 h1 k1 notstuck1 valid1 H1).
           deprod.
           pose (st_cons (st_refl s0) H0) as stp1.
           exists ar'0. exists s2. exists (steps_compose stp1 stp).

           repeat split_and...
           rewrite -> steps_io_distrib. rewrite -> H5. unfold stp1.
           simpl. reflexivity.
        -- exists ar, s0, (st_refl s0)...
           repeat split_and...
           simpl.  rewrite -> searchdefs. constructor.
      * pose proof (X true) as [impossible _].
        inversion impossible.
    (* app *)
    + exists ar. exists s0... exists (st_refl _)...
      repeat split_and...
      simpl. intro. destruct (member v (map fst defs))...
      simpl in *. destruct (member v (map fst defs)); simplify_eq; try constructor...
    (* proj *)
    + exists ar. exists s0... exists (st_refl _)...
      repeat split_and...
      simpl. intro. destruct (member v (map fst defs))...
      simpl in *. destruct (member v (map fst defs)); simplify_eq; try constructor...
    (* write *)
    + exists ar. exists s0... exists (st_refl _)...
      repeat split_and...
      simpl. intro. destruct (member v (map fst defs))...
      simpl in *. destruct (member v (map fst defs)); simplify_eq; try constructor...
    (* read *)
    + exists ar. exists s0... exists (st_refl _)...
      repeat split_and...
      simpl. intro. destruct (member v (map fst defs))...
      simpl in *. destruct (member v (map fst defs)); simplify_eq; try constructor...
    (* const *)
    + destruct (search v defs) eqn:searchv.
      (* skip *)
      * forced d. deprod. subst. simpl.
        assert (In v (map fst defs)) by eauto with searches.
        forced (member v (map fst defs)).

        pose proof (skip_source_step ar defs defspast m n s0 sg0 nodup0 notstuck0 valid0 rel0 i).
        deprod.
        assert (notstuck1: not_stuck s1) by eauto with steps.
        assert (valid1: state_valid s1) by eauto with steps.
        destruct s1.
        replace icode0 with c0 in * by (inversion H1; eauto).
        pose proof (IHc0 ar' _ _ _ notstuck1 valid1 H2).
        deprod.
        simpl in *.
        forced (member v (map fst defs)).

        pose (st_cons (st_refl _) H1) as stp1.
        exists ar'0. exists s1. exists (steps_compose stp1 stp).

        repeat split_and...
        rewrite -> steps_io_distrib. rewrite -> H6. unfold stp1.
        simpl. reflexivity.
      * exists ar, s0, (st_refl s0)...
        assert (~ In v (map fst defs)).
        { intro. assert (search v defs <> None) by eauto with searches. contradiction. }
        repeat split_and...
        simpl in *. subst.
        forced (member v (map fst defs)).
        constructor.
  (* abs, see if we should skip *)
  - destruct (search v defs) eqn:searchv.
    (* skip *)
    + forced d. deprod. subst. simpl.
      assert (In v (map fst defs)) by eauto with searches.
      forced (member v (map fst defs)).

      pose proof (skip_source_step ar defs defspast m n _ _ nodup0 notstuck0 valid0 rel0 i).
      deprod.
      assert (notstuck1: not_stuck s1) by eauto with steps.
      assert (valid1: state_valid s1) by eauto with steps.
      destruct s1.
      replace icode0 with c0_2 in * by (inversion H1; eauto).
      pose proof (IHc0_2 ar' _ _ _ notstuck1 valid1 H4).
      deprod.
      simpl in *.
      forced (member v (map fst defs)).

      pose (st_cons (st_refl _) H1) as stp1.
      exists ar'0. exists s1. exists (steps_compose stp1 stp).

      repeat split_and...
      rewrite -> steps_io_distrib. rewrite -> H8. unfold stp1.
      simpl. reflexivity.
    + exists ar, (<< (letabs v v0 c0_1 c0_2), e0, h0, k0 >>)%interp, (st_refl _)...
      assert (~ In v (map fst defs)).
      { intro. assert (search v defs <> None) by eauto with searches. contradiction. }
      repeat split_and...
      simpl in *. subst.
      forced (member v (map fst defs)).
      constructor.
 (* branch *)
  - exists ar.
    exists (<< branch v c0_1 c0_2, e0, h0, k0 >>)%interp...
    exists (st_refl _)...
    simpl. repeat split_and...
    subst. constructor.
  (* tail *)
  - exists ar.
    exists (<< tail v v0, e0, h0, k0 >>)%interp...
    exists (st_refl _)...
    repeat split_and...
    subst. constructor.
  (* return *)
  - exists ar.
    exists (<< ret v, e0, h0, k0 >>)%interp...
    exists (st_refl _)...
    repeat split_and...
    subst. constructor.
Qed.

Theorem globalize_safe0 :
  forall (P: exp) defs,
    defs_agree defs P ->
    defs_well_scoped defs ->
    NoDup (map fst defs) ->

    (forall x, ~ free_in x P) ->
    not_stuck (start_state P) ->

  forall (t: state) (stpt: steps (start_state (globalize defs P)) t),
    (* initial steps, defs is partitioned, the start state is pinned down *)
    (exists remaining,
        remaining <= length defs /\
        steps_io stpt = [] /\
        istack t = [] /\
        state_related [] defs (ienv t) remaining (start_state P) t /\
        addrs_space0 (iheap t) (defs2_addrs (ienv t)) = sum_list (map defined_size (map snd (drop remaining defs))) /\
        addrs_space_g (map fst defs) (iheap t) (defs2_addrs (ienv t)) = sum_list (map (defined_size_g (map fst defs)) (map snd (drop remaining defs))))
        \/
    (exists ar defspast
            (s: state) (stps: steps (start_state P) s),
        steps_io stpt = steps_io stps /\
        state_related ar defs defspast 0 s t /\
        globalize_safe ar (map fst defs) defspast
                       (sum_list (map defined_size (map snd defs)))
                       (sum_list (map (defined_size_g (map fst defs)) (map snd defs)))
                       s t).
Proof with eauto.
  intros P defs agree0 scoped0 nodup0 Pclosed Pnot_stuck t stpt.
  remember (start_state (globalize defs P)) as t0.
  induction stpt; subst; try pose proof (IHstpt eq_refl) as IHstpt.
  - left.
    exists (length defs).
    repeat split_and...
    (* related *)
    + simpl. constructor; simpl; try constructor; intros; try solve [intros; discriminate || contradiction]...
      * replace (length defs) with (length (map fst defs)) by apply map_length.
        symmetry.
        apply drop_all.
      (* ar valid *)
      * unfold valid_in_heap, addr_in, addr_in_env. simpl.
        intros. deprod...
        inversion H. deprod. unfold lookup, search in H0. discriminate.
      (* code 1 *)
      * simpl.
        rewrite -> firstn_all.
        reflexivity.
      * rewrite -> in_free_vars_iff_free_in in H.
        exfalso... apply Pclosed with x...
      (* heap *)
      * intros.
        rewrite -> lookup_empty in H. discriminate.
    (* safe *)
    + rewrite -> drop_all. simpl.
      unfold defs2_addrs. simpl.
      unfold addrs_space0, space_of. rewrite -> elements_empty.
      simpl. reflexivity.
    + rewrite -> drop_all. simpl.
      unfold defs2_addrs. simpl.
      unfold addrs_space_g, space_of. rewrite -> elements_empty.
      simpl. reflexivity.
  - deprod.
    destruct IHstpt.
    (* still processing globals *)
    + deprod.
      destruct remaining.
      (* finished, make a real step *)
      { right. simpl in *; subst.
        rewrite -> H0.
        pose proof (skip_source_steps [] defs (ienv s2) (sum_list (map defined_size (map snd defs))) (sum_list (map (defined_size_g (map fst defs)) (map snd defs))) (start_state P) s2 nodup0 Pnot_stuck
                   (state_valid_start P) H2).
        deprod.
        assert (notstuck1: not_stuck s1) by eauto with steps.
        assert (valid1: state_valid s1) by eauto with steps.

        pose proof (source_step ar' defs (ienv s2) s1 s2 s3 i notstuck1 H6 valid1 H8 s).
        deprod.
        assert (valid2: state_valid s2) by eauto with steps.

        simpl in H2.

        pose proof (initial_safe defs 0 P s2 H2).
        rewrite -> H3 in H11.
        rewrite -> H4 in H11.

        pose proof (related_step ar' defs (ienv s2)
                                 (sum_list (map defined_size (map snd defs)))
                                 (sum_list (map (defined_size_g (map fst defs)) (map snd defs)))
                                 s1 s2 s' s3 i H6 valid1 valid2 nodup0 I H10 s (conj H8 (H9 H11))).
        deprod.
        exists ar'0, (ienv s2), s'.
        exists (st_cons stp H10).
        simpl.
        rewrite -> H7.
        repeat split_and...
      } (* need to merge into lemma *)
      simpl in *; subst.

      inversion H2; subst.
      destruct code_rel.

      destruct (lookup_lt_is_Some_2 defs remaining) as [(bx, bd)]. rewrite <- Nat.le_succ_l...
      rewrite -> (take_S_r defs _ _ H7) in H5.
      rewrite -> bind_globals_app in H5.
      simpl in H5.

      assert (lkpbx: ([]: env) !! bx = None) by eauto.
      simpl in nodup0, scoped0, agree0.
      pose (<< cg, eg, hg, kg >>)%interp as s2.
      assert (envempty: forall (x: var), search x [] = (None : option value)) by reflexivity.
      simpl in H3.
      pose proof (initial_step bx bd defs remaining P s2 s3 i nodup0 scoped0 H7 H2 s)...
      deprod.

      inversion H7; subst.
      simpl istack in *.
      simpl ienv in *.
      simpl iheap in *.
      left.
      exists remaining.
      repeat split_and...
      * lia.
      * rewrite -> H0.
        destruct bd; simpl in s; inversion s; reflexivity.
      * inversion H8; subst. simpl in *. inversion stack_rel0...

    (* No more defs to process, go through normal evaluation *)
    + right. deprod.
      (* all of these are true by the existence of any steps *)
      assert (notstuck0: not_stuck s0) by eauto with steps.
      assert (valid0: state_valid s0) by eauto with steps.
      (* need to include in relation ? *)
      pose proof (skip_source_steps ar defs defspast
                                    (sum_list (map defined_size (map snd defs)))
                                    (sum_list (map (defined_size_g (map fst defs)) (map snd defs)))
                                    s0 s2 nodup0 notstuck0 valid0 H0) as skip.
      deprod.
      assert (notstuck1: not_stuck s1) by eauto with steps.
      assert (valid1: state_valid s1) by eauto with steps.
      assert (valid2: state_valid s2) by eauto with steps.
      destruct (source_step ar' defs defspast s1 s2 s3 i) as [s1' ?]...
      pose proof (related_step ar' defs defspast
                               (sum_list (map defined_size (map snd defs)))
                               (sum_list (map (defined_size_g (map fst defs)) (map snd defs)))
                               s1 s2 s1' s3 i H3 valid1 valid2 nodup0 I H7 s (conj H5 (H6 H1))).
      deprod.

      exists ar'0, defspast, s1'.
      exists (st_cons (steps_compose stps stp) H7).
      simpl.
      rewrite -> steps_io_distrib.
      rewrite -> H4. simpl.
      repeat split_and...
      * rewrite -> H...
Qed.
Lemma clos_addr_in_src :
  forall ar defs defspast clos closg a2,
    forall (defspast_same : map fst defspast = map fst defs),
    clos_related ar defs defspast clos closg ->
    addr_in closg a2 ->
    (exists a1,
      In (a1, a2) ar /\
       addr_in clos a1) \/
      elem_of a2 (defs2_addrs defspast).
Proof with eauto.
  intros.
  inversion H; subst.
  destruct H1.
  rewrite -> firstn_O in *.
  simpl in *.
  inversion H3; subst.
  pose proof (free_vars_elim_defs cl (map fst defs)).
  unfold addr_in, addr_in_clos, addr_in, addr_in_env in *.
  deep_set_unfold.
  destruct (H1 _ H5).
  + assert (el !! x <> None) by eauto.
    forced (el !! x).
    destruct (pairs_related x v0)...
    deprod.
    simplify_eq.
    inversion H6; subst.
    inversion H11; subst.
    left.
    exists a. split... eauto with searches.
    unfold addr_in, addr_in_svalue, addr_in, addr_in_clos, addr_in, addr_in_env.
    do 2 eexists. repeat split_and...
    constructor.
  + deprod. simplify_eq. simpl in *.
    inversion H6; subst.
    assert (In v0 (map fst defs)) by eauto with searches.
    assert (In v0 (map fst defspast)) by congruence.
    destruct (In_fst_search _ _ H10).
    assert (In (v0, x) defspast) by eauto with searches.
    pose proof (globals_present v0 x H11 (conj H5 H7)).
    simplify_eq.
    inversion H6; subst.
    right.
    exists (v0, vaddr a2)...
    split...
    eauto with searches.
Qed.

Lemma sval_addr_in_src :
  forall ar defs defspast sv svg a2,
    forall (samedefs: map fst defspast = map fst defs),
    sval_related ar defs defspast sv svg ->
    addr_in svg a2 ->
    (exists a1,
      In (a1, a2) ar /\
      addr_in sv a1) \/
    elem_of a2 (defs2_addrs defspast).
Proof with eauto.
  intros.
  inversion H; subst.
  - inversion H0; subst.
    deprod. clear H.
    induction H1.
    + inversion H2.
    + simpl in H2.
      destruct H2.
      * subst.
        inversion H3; subst.
        inversion H; subst.
        left.
        exists a.
        split.
        -- eauto with searches.
        -- eauto 20 with addr_in.
      * destruct IHForall2...
        eauto 20 with addr_in.
        deprod.
        left.
        exists a1. split...
        eauto 20 with addr_in.
  - unfold addr_in, addr_in_svalue.
    apply clos_addr_in_src with defs closg...
Qed.

Lemma image_closure :
  forall ar defs defspast h hg,
    (map fst defspast = map fst defs) ->
    NoDup (map fst ar) ->
    heap_valid h ->
    heap_valid hg ->
    heap_related ar defs defspast h hg ->
    forall (ar_heap_dom: forall a1 a2,
               In (a1, a2) ar -> h !! a1 <> None /\ hg !! a2 <> None),

    forall (addrs1 : addrs)
      (addrs1_valid : forall a, elem_of a addrs1 -> h !! a <> None),
    subseteq
      (closure _ hg (@image addr addr addrs addrs addrs_elements addrs_empty addrs_union addrs_singleton
                            (flip search ar) addrs1))
      (union (image (flip search ar) (closure _ h addrs1)) (defs2_addrs defspast)).
Proof with eauto with searches.
  intros ar defs defspast h hg samedefs arnodup ? ? ? ? ? ?.
  unfold image in *.
  deep_set_unfold. intros.
  destruct H1.
  induction x, H2 using (closure_ind H0); deep_set_unfold.
  (* inject *)
  - left. exists x. split...
    + apply closure_inject...
  (* descend *)
  - destruct IH1; deep_set_unfold.
    (* actual image *)
    + assert (In (x, a) ar) by eauto with searches.
      destruct (ar_heap_dom _ _ H5).
      forced (h !! x).
      destruct (sval_addr_in_src ar defs defspast s v a2 samedefs)...
      * pose proof (related_addrs _ _ Heqo). deprod.
        simplify_eq...
      * left. deprod.
        exists a1. repeat split_and; eauto with searches.
        (* in closure *)
        eapply closure_descend with x s...
      * right. unfold defs2_addrs in H8.
        set_unfold. deprod. set_unfold.
        exists (v0, v1)...
    + right.
      rewrite -> elem_of_list_In in H3. pose proof (global_addrs _ _ H3).
      simpl in H4. deprod...
      inversion H6; subst...
      * unfold addr_in, addr_in_svalue in H2. forced v. subst.
        unfold addr_in, addr_in_svalue, addr_in, addr_in_list, addr_in in H2.
        deprod. inversion H8; subst.
        simplify_eq.
        destruct (In_searches _ _ _ _ H7 H2).
        deprod.
        exists (x, vaddr a2). split...
      * unfold addr_in, addr_in_svalue in H2. forced v. simplify_eq.
        unfold addr_in, addr_in_svalue, addr_in, addr_in_clos, addr_in, addr_in_env, addr_in in H2.
        deprod. inversion H8; subst.
        exists (x, vaddr a2).
        split...
        set_unfold. deprod.
        rewrite -> in_free_vars_iff_free_in in H5.
        destruct (H7 x)... deprod...
        simplify_eq...
Qed.

Lemma roots_subset :
forall ar defs defspast c e k eg kg,
forall (samedefs: map fst defspast = map fst defs)
       (nodup0: NoDup (map fst ar))
       (nodup1: NoDup (map fst defs))
       (defspast_sound_val:
          forall x v, In (x, v) defspast -> exists d,
              In (x, d) defs /\
              defined_value d v),
  env_related ar defspast (free_vars c) (free_vars (elim_defs (map fst defs) c)) e eg ->
  stack_related ar defs defspast k kg ->
  (⋃ map clos_addresses kg ∪ env_addresses (free_vars (elim_defs (map fst defs) c)) eg)
  ⊆ image (flip search ar) (⋃ map clos_addresses k ∪ env_addresses (free_vars c) e) ∪ (defs2_addrs defspast).
Proof with eauto.
  intros.
  deep_set_unfold. rewrite -> elem_of_union_list in H1.
  destruct H1.
  (* stack *)
  - pose proof (@addrs_iff clos _ _) as H4.
    deep_set_unfold.
    rewrite -> H4 in H2. clear H4.
    unfold addr_in, addr_in_clos, addr_in in H2.
    destruct y as [[xl cl] el].
    refine
      (match _ with
       | or_introl (ex_intro _ a (conj p1 p2)) => or_introl (ex_intro _ a (conj (or_introl p1) p2))
       | or_intror pf => or_intror pf
       end).
    rewrite -> elem_of_list_In in H3.
    induction H0.
    + inversion H3.
    + destruct H3; simplify_eq...
      * pose proof (clos_addr_in_src ar defs defspast _ _ x samedefs H0).
        destruct H3.
        { unfold addr_in, addr_in_clos, addr_in, addr_in_env.
          deep_set_unfold.
          exists x0, v... }
        -- left. deep_set_unfold.
           exists a1. split; eauto with searches.
           left.
           rewrite <- (@addrs_iff clos _ clos_addresses') in H4...
        -- right.
           inversion H0; subst.
           deep_set_unfold.
           exists (v0, vaddr x)...
      * destruct IHstack_related...
        left. deprod.
        exists a. split...
        simpl. set_solver.
  (* env *)
  - deprod.
    forced (search x0 eg). forced v.
    simplify_eq.
    refine
      (match _ with
       | or_introl (ex_intro _ a (conj p1 p2)) => or_introl (ex_intro _ a (conj (or_intror p1) p2))
       | or_intror pf => or_intror pf
       end).
    remember H1 as H2. clear HeqH2.
    apply free_vars_elim_defs in H1.
    deep_set_unfold.
    destruct H1...
    (* free in code  *)
    + left.
      inversion H; subst.
      assert (e !! x0 <> None) by eauto.
      forced (e !! x0).
      pose proof (pairs_related x0 v H1 H2 Heqo0).
      unfold lookup in *.
      deprod. simplify_eq.
      inversion H5; subst.
      exists a. split...
      exists x0. split...
      rewrite -> Heqo0.
      reflexivity.
    (* global *)
    + right.
      deprod. simpl fst in *. simplify_eq.
      inversion H; subst.
      exists (v, vaddr x).
      split...

      rewrite -> elem_of_list_In in H3.
      assert (In v (map fst defs)) by eauto with searches.
      assert (In v (map fst defspast)) by congruence.
      destruct (In_fst_search  _ _ H4).
      assert (In (v, x0) defspast) by eauto with searches.
      pose proof (defspast_sound_val v x0 H5).
      deprod.
      replace x1 with d in * by eauto with searches.

      pose proof (globals_present v x0 H5 H2).
      unfold lookup in *.
      simplify_eq.
      rewrite -> elem_of_list_In...
Qed.

Lemma globals_closed :
  forall defs defspast hg,
    heap_valid hg ->
    (forall x v,
      In (x, v) defspast ->
        match v with
          (* incorrect value handled in env *)
        | vaddr ag =>
          exists d svg,
          In (x, d) defs /\
          hg !! ag = Some svg /\
          defined_svalue defspast d svg
        | _ => True
        end) ->
    closed hg (defs2_addrs defspast).
Proof with eauto.
  intros ? ? ? valid0 global_addrs.
  unfold closed, set_Forall. deep_set_unfold.
  intros. deprod. simpl snd in *. simplify_eq.
  rewrite -> elem_of_list_In in H.
  pose proof (global_addrs _ _ H). simpl in H0.
  deprod. exists svg.
  split...
  intros.
  inversion H2; subst; simpl in H3; set_unfold; deprod.
  - rewrite -> elem_of_list_In in H3.
    destruct (In_searches _ _ _ x1 H4 H3).
    deprod.
    rewrite <- elem_of_list_In in H6.
    exists (x2, x1). split.
    eauto with searches. 
    simpl. set_unfold...
  - forced (search x1 el). forced v0.
    deep_set_unfold.
    rewrite -> in_free_vars_iff_free_in in H3.
    pose proof (H4 x1 H3 H5).
    deprod.
    unfold lookup in *. simplify_eq.
    assert (In (x1, vaddr x0) defspast) by eauto with searches.
    rewrite <- elem_of_list_In in H7.
    exists (x1, vaddr x0)...
Qed.

(*** Relatedness + Safety is enough *)
Theorem state_space_safe :
  forall ar defs defspast m n s sg,
    NoDup (map fst defs) ->
    defs_well_scoped defs ->
    NoDup (map fst ar) ->
    state_valid s ->
    state_valid sg ->

    state_related ar defs defspast 0 s sg ->
    globalize_safe ar (map fst defs) defspast m n s sg ->
    (1 + length defs) * state_space s + m >= state_space sg.
Proof with eauto.
  (* 
    addrs_space0 (iheap sg) (defs2_addrs defspast) = n -> *)
  intros ar defs defspast m n s sg nodup0 scoped0 nodup1 valid validg rel safe.
  unfold state_space.

  destruct rel.
  inversion safe; subst.
  simpl iheap in *.

  assert (defssame: map fst defspast = map fst defs) by (destruct code_rel; eauto).
  assert (defslength_same : length defspast = length defs).
  { do 2 rewrite <- (map_length fst).
    congruence. }

  assert (size (free_vars cg) <= size (free_vars c) + length defs).
  { clear - code_rel nodup0 scoped0.
    remember (map fst defs) as defVars.
    rewrite <- (map_length fst defs). rewrite <- HeqdefVars.
    
    cut (subseteq (free_vars cg) (union (free_vars c) (list_to_set (map fst defs)))).
    { rewrite <- HeqdefVars.
      intro is_subset.
      apply subseteq_size in is_subset.

      transitivity (size (free_vars c ∪ list_to_set defVars))...
      pose proof (size_union_alt (free_vars c) (list_to_set defVars)).
      assert (@size vars _ (list_to_set defVars : vars) = length defVars).
      { clear - nodup0.
        induction defVars.
        - rewrite -> list_to_set_nil.
          rewrite -> size_empty.
          simpl...
        - rewrite -> list_to_set_cons.
          inversion nodup0; subst.
          assert ({[a]} ## (list_to_set defVars : vars)).
          { set_unfold. intro.
            intros; subst.
            rewrite -> elem_of_list_In in H0.
            contradiction.
          }
          rewrite -> (size_union _ _ H).
          simpl. rewrite -> size_singleton.
          f_equal. apply IHdefVars...
      }
      rewrite <- H0.
      assert (size (difference (list_to_set defVars) (free_vars c)) <= size (list_to_set defVars: vars)).
      { apply subseteq_size. set_solver. }
      lia.
    }
    unfold code_related in *.
    rewrite <- HeqdefVars in *.
    simpl in code_rel. deprod. subst.
    apply free_vars_elim_defs...
  }
  assert (env_size: (1 + length defs) * (1 + size (free_vars c)) >= size (free_vars cg)).
  { rewrite -> Nat.mul_add_distr_l.
    rewrite -> Nat.mul_1_r.
    assert ((1 + length defs) * size (free_vars c) >= size (free_vars c)) by (simpl; lia).
    lia. }
          
  assert ((1 + length defs) * sum_list (map clos_size k) >= sum_list (map clos_size kg)).
  { simpl in stack_rel.
    clear - stack_rel defssame.
    induction stack_rel.
    - simpl. lia.
    - simpl. rewrite -> Nat.mul_add_distr_r in IHstack_rel.
      rewrite -> Nat.mul_1_l in IHstack_rel.
      rewrite -> Nat.mul_add_distr_l.
      enough ((1 + length defs) * clos_size clos0 >= clos_size closg).
      lia.

      inversion H; subst.
      inversion H0; subst.
      simpl take.
      eapply clos_size_related.
      exact H.
  }

  remember (closure svalue_addresses' h (live_roots (<< c, e, h, k >>))) as addrs1'.
  remember (defs2_addrs defspast) as global_addrs.
  remember (union (global_addrs) (closure svalue_addresses' hg (live_roots (<< cg, eg, hg, kg >>)))) as addrs2'.
  remember (closure svalue_addresses' hg (live_roots (<< cg, eg, hg, kg >>))) as addrs3'.
  assert ((1 + length defspast) * addrs_space0 h addrs1' + m >= addrs_space0 hg addrs3').
  {
    unfold live_roots.

    assert (H1: valid_in_heap h h) by eauto 20 with addr_in.
    rewrite -> heap_valid_in_heap in H1.
    assert (H2: valid_in_heap hg hg) by eauto 20 with addr_in.
    rewrite -> heap_valid_in_heap in H2.
    pose proof (closure_closed h (live_roots (<< c, e, h, k >>)) H1).
    rewrite <- Heqaddrs1' in H3.
    pose proof (af_safe addrs1' H3).
    eapply Nat.le_trans with (addrs_space0 hg (image (flip search ar) addrs1' ∪ global_addrs))...
    apply space_of_subset.
    set_unfold.

    subst addrs3'.
    intros. 
    destruct code_rel.
    simpl in H6.
    rewrite -> Heqglobal_addrs.

    assert (globals_closed : closed hg (defs2_addrs defspast)).
    { apply globals_closed with defs...
      inversion heap_rel... }
    assert (globals_closure: equiv (closure _ hg (defs2_addrs defspast)) (defs2_addrs defspast))
    by (apply closure_of_closed; eauto).

    (* membership is decidable, so peirce's law lets us refine the subset deep in the branch *)
    refine
      (match (decide (elem_of x (defs2_addrs defspast))) with
       | left global => or_intror global
       | right not_global => _
       end).

    (* have to stage this a bit weird because of typeclass issues *)
    pose proof (image_closure ar defs defspast h hg defssame nodup1 H1 H2 heap_rel ar_heap_dom).
    (* duplicate globals in the union here, to apply better *)
    deep_set_unfold.
    apply H8.
    (* all roots valid *)
    { unfold closed, set_Forall in H3. intros.
      apply valid. unfold addr_in, addr_in_state.
      set_unfold.
      destruct H6.
      - right. left. unfold addr_in, addr_in_list.
        rewrite -> elem_of_union_list in H6.
        deprod. rewrite -> elem_of_list_In in H6.
        clear - H6 H9.
        induction k; simpl in *.
        + contradiction.
        + destruct H6.
          * exists a. split...
            rewrite <- addrs_iff.
            unfold addresses, clos_addresses'.
            congruence.
          * pose proof (IHk H).
            deprod. exists x...
      (* env *)
      - deep_set_unfold.
        forced (search x1 e).
        forced v. simplify_eq.
        right. right.
        exists x1...
    }
    (* image of roots is root *)
    {
      enough (elem_of x ((closure svalue_addresses' hg (image (flip search ar) (⋃ map clos_addresses k ∪ env_addresses (free_vars c) e))) ∪ (defs2_addrs defspast))).
      { clear - H6 not_global. deep_set_unfold. destruct H6; try contradiction... }

      deep_set_unfold.
      destruct (globals_closure x) as [gcfw _].
      refine (match _ with
              | or_introl p => or_introl p
              | or_intror q => or_intror (gcfw q)
              end).

      (* need simplification in here *)
      pose proof (closure_union hg (image (flip search ar) (⋃ map clos_addresses k ∪ env_addresses (free_vars c) e)) (defs2_addrs defspast)). set_unfold.
      destruct (H6 H2 x) as [fw _].
      apply fw.

      pose proof (roots_subset ar defs defspast c e k eg kg defssame nodup1 nodup0 defspast_sound_val env_rel stack_rel).
      apply closure_monotonic with ((⋃ map clos_addresses kg ∪ env_addresses (free_vars (elim_defs (map fst defs) c)) eg) ∪ (defs2_addrs defspast))...
      - clear - H9. set_solver.
      - clear - H2 H5 H6 not_global globals_closure.
        rewrite -> closure_union...
        set_unfold. left...
    }
  }

  fold addrs_space0.
  remember (length defs) as l.
  remember (sum_list (map clos_size k)).
  remember (sum_list (map clos_size kg)).
  remember (addrs_space0 h addrs1').
  remember (addrs_space0 hg global_addrs).
  remember (addrs_space0 hg addrs2').
  remember (addrs_space0 hg addrs3').
  remember (size (free_vars c)).
  remember (size (free_vars cg)).
  replace (length defspast) with l in * by assumption.
  clear - H H0 H1 env_size.
  (* need to simplify multiplication a bit *)
  replace ((1 + l) * (1 + n2 + n6 + n0)) with ((1 + l) + (1 + l) * n2 + n6 + l * n6 + (1 + l) * n0) by lia.
  lia.
Qed.

Definition state_space_g defVars st :=
  match st with
  | (<< c, _, h, k >>)%interp =>
      let roots := live_roots st in
      let addrs := closure svalue_addresses' h roots in
      1 + space_of (svalue_size_g defVars) h addrs + size (difference (free_vars c) (list_to_set defVars)) + sum_list (map (clos_size_g defVars) k)
  end.
  
(*** Relatedness + Safety is enough *)
Theorem state_space_safe_g :
  forall ar defs defspast m n s sg,
    NoDup (map fst defs) ->
    defs_well_scoped defs ->
    NoDup (map fst ar) ->
    state_valid s ->
    state_valid sg ->

    state_related ar defs defspast 0 s sg ->
    globalize_safe ar (map fst defs) defspast m n s sg ->
    state_space s + n >= state_space_g (map fst defs) sg.
Proof with eauto.
  intros ar defs defspast m n s sg nodup0 scoped0 nodup1 valid validg rel safe.
  unfold state_space, state_space_g.

  destruct rel.
  inversion safe; subst.
  simpl iheap in *.

  pose (map fst defs) as defVars.

  assert (defssame: map fst defspast = map fst defs) by (destruct code_rel; eauto).
  assert (defslength_same : length defspast = length defs).
  { do 2 rewrite <- (map_length fst).
    congruence. }

  assert (size (free_vars c) >= size (difference (free_vars cg) (list_to_set defVars))).
  { clear - code_rel nodup0 scoped0.
    unfold code_related in *. simpl in code_rel.
    deprod. subst.
    pose proof (free_vars_elim_defs c defVars).
    apply subseteq_size.
    set_solver.
  }
          
  assert (sum_list (map clos_size k) >= sum_list (map (clos_size_g defVars) kg)).
  { simpl in stack_rel.
    clear - stack_rel defssame.
    induction stack_rel.
    - simpl. lia.
    - simpl.
      enough (clos_size clos0 >= clos_size_g defVars closg) by lia.

      inversion H; subst.
      inversion H0; subst.
      eapply clos_size_related_g.
      exact H.
  }

  remember (closure svalue_addresses' h (live_roots (<< c, e, h, k >>))) as addrs1'.
  remember (defs2_addrs defspast) as global_addrs.
  remember (union (global_addrs) (closure svalue_addresses' hg (live_roots (<< cg, eg, hg, kg >>)))) as addrs2'.
  remember (closure svalue_addresses' hg (live_roots (<< cg, eg, hg, kg >>))) as addrs3'.
  assert (addrs_space0 h addrs1' + n >= addrs_space_g defVars hg addrs3').
  {
    assert (H1: valid_in_heap h h) by eauto 20 with addr_in.
    rewrite -> heap_valid_in_heap in H1.
    assert (H2: valid_in_heap hg hg) by eauto 20 with addr_in.
    rewrite -> heap_valid_in_heap in H2.
    pose proof (closure_closed h (live_roots (<< c, e, h, k >>)) H1).
    rewrite <- Heqaddrs1' in H3.
    pose proof (af_safe_g addrs1' H3).
    eapply Nat.le_trans with (addrs_space_g defVars hg (image (flip search ar) addrs1' ∪ global_addrs))...
    apply space_of_subset.
    set_unfold.

    subst addrs3'.
    intros. 
    destruct code_rel.
    simpl in H6.
    rewrite -> Heqglobal_addrs.

    assert (globals_closed : closed hg (defs2_addrs defspast)).
    { apply globals_closed with defs...
      inversion heap_rel... }
    assert (globals_closure: equiv (closure _ hg (defs2_addrs defspast)) (defs2_addrs defspast))
    by (apply closure_of_closed; eauto).

    (* membership is decidable, so peirce's law lets us refine the subset deep in the branch *)
    refine
      (match (decide (elem_of x (defs2_addrs defspast))) with
       | left global => or_intror global
       | right not_global => _
       end).

    (* have to stage this a bit weird because of typeclass issues *)
    pose proof (image_closure ar defs defspast h hg defssame nodup1 H1 H2 heap_rel ar_heap_dom).
    (* duplicate globals in the union here, to apply better *)
    deep_set_unfold.
    apply H8.
    (* all roots valid *)
    { unfold closed, set_Forall in H3. intros.
      apply valid. unfold addr_in, addr_in_state.
      set_unfold.
      destruct H6.
      - right. left. unfold addr_in, addr_in_list.
        rewrite -> elem_of_union_list in H6.
        deprod. rewrite -> elem_of_list_In in H6.
        clear - H6 H9.
        induction k; simpl in *.
        + contradiction.
        + destruct H6.
          * exists a. split...
            rewrite <- addrs_iff.
            unfold addresses, clos_addresses'.
            congruence.
          * pose proof (IHk H).
            deprod. exists x...
      (* env *)
      - deep_set_unfold.
        forced (search x1 e).
        forced v. simplify_eq.
        right. right.
        exists x1...
    }
    (* image of roots is root *)
    {
      enough (elem_of x ((closure svalue_addresses' hg (image (flip search ar) (⋃ map clos_addresses k ∪ env_addresses (free_vars c) e))) ∪ (defs2_addrs defspast))).
      { clear - H6 not_global. deep_set_unfold. destruct H6; try contradiction... }

      deep_set_unfold.
      destruct (globals_closure x) as [gcfw _].
      refine (match _ with
              | or_introl p => or_introl p
              | or_intror q => or_intror (gcfw q)
              end).

      (* need simplification in here *)
      pose proof (closure_union hg (image (flip search ar) (⋃ map clos_addresses k ∪ env_addresses (free_vars c) e)) (defs2_addrs defspast)). set_unfold.
      destruct (H6 H2 x) as [fw _].
      apply fw.

      pose proof (roots_subset ar defs defspast c e k eg kg defssame nodup1 nodup0 defspast_sound_val env_rel stack_rel).
      apply closure_monotonic with ((⋃ map clos_addresses kg ∪ env_addresses (free_vars (elim_defs (map fst defs) c)) eg) ∪ (defs2_addrs defspast))...
      - clear - H9. set_solver.
      - clear - H2 H5 H6 not_global globals_closure.
        rewrite -> closure_union...
        set_unfold. left...
    }
  }
  rewrite -> drop_0 in defspast_same. rewrite -> defspast_same in *.

  unfold defVars in *.
  unfold addrs_space0, addrs_space_g in *.
  remember (sum_list (map clos_size k)).
  remember (sum_list (map (clos_size_g (map fst defs)) kg)).
  remember (space_of svalue_size h addrs1').
  remember (space_of (svalue_size_g (map fst defs)) hg global_addrs).
  remember (space_of (svalue_size_g (map fst defs)) hg addrs2').
  remember (space_of (svalue_size_g (map fst defs)) hg addrs3').
  remember (size (free_vars c)).
  remember (size (difference (free_vars cg) (list_to_set (map fst defs)))).
  clear - H H0 H1.
  (* need to simplify multiplication a bit *)
  lia.
Qed.


Theorem global_roots :
  forall ar defs remaining P cg eg hg kg,
    defs_well_scoped defs ->
    map fst eg = drop remaining (map fst defs) ->
    state_related ar defs eg remaining (start_state P) (<<cg, eg, hg, kg>>) ->
    (⋃ map clos_addresses kg ∪ env_addresses (free_vars cg) eg)
      ⊆ (defs2_addrs eg).
Proof with eauto.
  intros ? ? ? ? ? ? ? ? scoped0 samedefs ?.
  inversion H; subst.
  inversion stack_rel; subst.
  simpl. deep_set_unfold.
  forced H0. clear Heqo.
  deprod. 
  forced (search x0 eg).
  forced v.
  simplify_eq.
  inversion code_rel; subst.
  apply free_vars_related in H1...
  set_unfold.
  inversion env_rel; subst.
  destruct H1...
  - exists (x0, vaddr x). split...
    eauto with searches.
  - exists (x0, vaddr x). split...
    eauto with searches.
Qed.


(* Final theorem *)

Theorem globalize_is_safe :
  forall (P: exp) defs,
    defs_agree defs P ->
    defs_well_scoped defs ->
    NoDup (map fst defs) ->

    (forall x, ~ free_in x P) ->
    not_stuck (start_state P) ->

    let m := (sum_list (map defined_size (map snd defs))) in
    let n := (sum_list (map (defined_size_g (map fst defs)) (map snd defs))) in
    forall (t: state) (stpt: steps (start_state (globalize defs P)) t),
      (exists (s: state) (stps: steps (start_state P) s),
          steps_io stps = steps_io stpt /\
          (1 + length defs) * state_space s + m >= state_space t /\
          state_space s + n >= state_space_g (map fst defs) t).
Proof with eauto.
  intros.
  pose proof (globalize_safe0 P defs H X H0 H1 X0 t stpt).
  destruct H2; deprod; simplify_eq.
  - exists (start_state P). exists (st_refl _).
    split...
    pose proof (initial_safe defs remaining P t H5).
    inversion H5; subst.
    inversion env_rel; subst.
    simpl state_space.
    rewrite -> (Nat.mul_add_distr_l (1 + length defs) 1 _).
    rewrite -> Nat.mul_1_r.

    assert (forall xs, equiv (env_addresses xs []) empty).
    { intros. unfold env_addresses. induction (elements xs)... }
    rewrite -> H9.
    assert (equiv (free_vars P) empty).
    { set_unfold. intros. intro. apply (H1 x). eauto with free_in. }
    rewrite -> H10.
    rewrite -> size_empty.
    unfold addrs_space0, addrs_space_g, space_of.
    setoid_replace (union empty empty : addrs) with (empty : addrs) by (clear; set_solver).
    rewrite -> closure_empty.
    rewrite -> elements_empty. simpl.
    replace (S (length defs + length defs * 0 + n)) with (S (length defs + n)) by lia.
    simpl in *. subst.
    simpl.
    pose proof (global_roots [] defs remaining P _ _ _ _ X defspast_same H5).
    unfold ge.

    assert (heap_valid hg).
    { assert (state_valid (<< _, eg, hg, [] >>)%interp) by eauto with steps.
      eauto with addr_in. }

    split.
    + transitivity (S (addrs_space0 hg (defs2_addrs eg)) + size (free_vars (bind_globals (take remaining defs) (elim_defs (map fst defs) P)))).
      * subst.
        inversion code_rel; subst.
        simpl in *. unfold addrs_space0.
        apply le_n_S.
        pose proof (closure_monotonic _ _ (defs2_addrs eg) H11 H4).
        rewrite -> Nat.add_0_r.
        transitivity
          (sum_list
            (map (lookup_size svalue_size hg)
                (elements (closure svalue_addresses' hg (defs2_addrs eg))))
          + size (free_vars (bind_globals (take remaining defs) (elim_defs (map fst defs) P)))).
        -- apply Nat.add_le_mono_r.
          apply sum_list_sublist.
          apply map_sublist.
          apply elements_submseteq.
          assumption.
        -- apply Nat.add_le_mono_r.
          setoid_replace (closure svalue_addresses' hg (defs2_addrs eg)) with (defs2_addrs eg).
          reflexivity.
          eapply closure_of_closed...

          apply globals_closed with defs...
          inversion heap_rel...
      * simpl. apply le_n_S.
        rewrite -> H6. unfold n.
        enough (size (free_vars (bind_globals (take remaining defs) (elim_defs (map fst defs) P))) <= length defs).
        enough (sum_list (map defined_size (map snd (drop remaining defs))) <= sum_list (map defined_size (map snd defs))).
        lia.
        (* smaller list *)
        {  apply sum_list_sublist.
          apply map_sublist.
          apply map_sublist.
          apply sublist_submseteq.
          apply sublist_drop. }
        (* size free vars *)
        { pose proof (free_vars_related P defs remaining X).
          transitivity (size (free_vars P ∪ list_to_set (map fst defs))).
          * apply subseteq_size.
            exact H12.
          * rewrite -> H10.
            setoid_replace (union empty (list_to_set (map fst defs)) : vars) with 
              (list_to_set (map fst defs) :vars) by (clear; set_solver).
            rewrite <- (map_length fst).
            clear.
            induction (map fst defs); simpl...
            -- rewrite -> size_empty...
            -- rewrite -> size_union_alt.
              rewrite -> size_singleton.
              apply le_n_S.
              transitivity (size (list_to_set l : vars))...
              apply subseteq_size.
              set_solver.
        }
    + apply le_n_S.
      inversion code_rel; deprod; subst.
      simpl in *.
      replace (size (free_vars (bind_globals (take remaining defs) (elim_defs (map fst defs) P)) ∖ list_to_set (map fst defs))) with 0.
      repeat rewrite -> Nat.add_0_r.
      unfold space_of.
      unfold n.
      * transitivity (sum_list
                        (map (lookup_size (svalue_size_g (map fst defs)) hg)
                             (elements
                                (closure svalue_addresses' hg
                                         (defs2_addrs eg))))).
        -- apply sum_list_sublist.
           apply map_sublist.
           apply elements_submseteq.
           apply closure_monotonic...
        -- setoid_replace (closure svalue_addresses' hg (defs2_addrs eg)) with (defs2_addrs eg).
           unfold addrs_space_g, space_of in H7.
           rewrite -> H7.
           (* drop <= full *)
           apply sum_list_sublist.
           apply map_sublist.
           rewrite -> map_drop.
           apply submseteq_drop.

           eapply closure_of_closed...
           apply globals_closed with defs...
           inversion heap_rel...
      (* free vars empty *)
      * replace 0 with (size (empty : vars)) by (apply size_empty).
        apply set_size_proper.
        deep_set_unfold.
        intros; split; try contradiction.
        intros; deprod.
        apply free_vars_related in H12...
        set_unfold.
        destruct H12...
        apply H10 in H12...

    + intro. intros. rewrite -> lookup_empty in H11. discriminate.
  - exists s, stps.
    split...
    split...
    + apply state_space_safe with ar defspast n...
      * inversion H3...
      * eauto with steps.
      * eauto with steps.
    + apply state_space_safe_g with ar defspast m...
      * inversion H3...
      * eauto with steps.
      * eauto with steps.
Qed.

End Globalization.


(* need defs2 agrees with defs *)
(*
Theorem initial_steps :
  forall defs cg,
    defs_well_scoped defs ->
    NoDup (map fst defs) ->

    { eg : env &
    { hg : heap svalue &
          (steps
             (<< bind_globals defs cg, [], empty, [] >>)%interp
             (<< cg, eg, hg, [] >>)%interp *
           (map fst defs = map fst eg) *
           state_related  eg eg)%type
    }}.
Proof with eauto with decEq.
  intros defs cg scoped unique.
  (* To make the induction go through, we pick c and cg to have
     the binding at the front, so we need to generalize *)
  generalize dependent cg.
  unfold globals_present.
  induction defs; intros cg.
  - exists []. exists empty.
    simpl.
    repeat split; intros;
      auto ||
      discriminate ||
      case_match; intro; contradiction.
  - inversion scoped; subst.
    pose (map fst defs) as defVars.
    simpl in unique.
    assert (defs_well_scoped defs) by (inversion scoped; eauto).
    assert (NoDup (map fst defs)) by (inversion unique; eauto).
    destruct (IHdefs X H (bind_defined v d cg)) as [eg0 [hg0 [[st0 same_globals] heap_globals]]].
    destruct d.
    (* We have  a lot of redundancy between cases that should ideally be factored out *)
    + (* have to gather some values ahead of time *)
      (* define tuple values *)
      destruct (map_option_all_some (fun x => search x eg0) l).
      { intros. enough (In v0 (map fst defs))...
        rewrite -> same_globals in H2.
        destruct (In_fst_search v0 eg0) as [a searchdefs]...
      }
      destruct (alloc hg0 (stuple x)) eqn:alloc1.
      define (st1: (step None
                      (<< bind_defined v (dtuple var l) cg, eg0, hg0, [] >>)%interp
                      (<< cg, _, _, _ >>)%interp)).
      { apply (step_tuple v l _ eg0 hg0 [] x a h)... }
      exists ((v, vaddr a) :: eg0).
      exists h.
      repeat split; try done; try (inversion rel1; subst).
      * apply (st_cons st0 st1).
      * simpl. congruence.
      * intro global. case_match.
        intro global_in. subst.
        destruct (((v, vaddr a) :: eg0) !! v0) eqn:search1.
        unfold lookup in search1.
        simpl in search1. subst.
        destruct (decEq v0 v); simplify_eq.
        -- exists a. exists (stuple x).
           repeat split...
           ++ simpl...
           ++ simpl...
           ++ eauto with heaps.
           ++ inversion unique; subst.
              assert (In (v, d) defs -> False) by eauto with searches.
              forced global_in; simplify_eq.
              apply defined_stuple.
              clear - e H0 H3 unique heap_globals.
              generalize dependent x.
              induction l; intros x e...
              simpl map_option in *.

              forced (search a0 eg0).
              forced (map_option (λ x : var, search x eg0) l). 
              simplify_eq.
              rewrite IHl with l0...
              unfold lookup. simpl.
              destruct (decEq a0 v); simplify_eq...
              { absurd (In v (map fst defs))... }
              intros. inversion H. subst. apply H0...
              constructor. right...
        -- assert (In (v0, d) defs) by (forced global_in; assumption).
           destruct (heap_globals (v0, d) H1) as [a' [sv [in1 [lkp1 [hlkp1 d0]]]]].
           exists a'. exists sv.
           deprod.
           repeat split; simpl...
           ++ eauto with heaps.
           ++ clear - d0 same_globals unique scoped.
              inversion unique; subst.
              inversion d0; clear d0; subst; constructor.
              ** generalize dependent vals.
                 induction xs...
                 intros vals H.
                 simpl map_option in *.
                 unfold lookup in *.
                 forced (search a0 eg0).
                 forced (map_option (flip search eg0) xs).
                 simplify_eq.
                 rewrite -> (IHxs l0)...
                 simpl.
                 destruct (decEq a0 v) as [->|neq]...

                 contradict H1.
                 enough (In (v, v0) eg0); eauto with searches.
                 rewrite -> same_globals. eauto with searches.
              ** unfold lookup in *.
                 intros x0 x0_free x0_neq.
                 simpl search in *.
                 destruct (decEq x0 v)... subst.
                 contradict H1.
                 destruct (H v x0_free x0_neq) as [? [? _]].
                 rewrite -> same_globals.
                 eauto with searches.
        (* search can't fail *)
        -- unfold lookup in search1. simpl in search1.
           destruct (decEq v0 v); simplify_eq.
           contradict search1.
           simpl In in global_in.
           forced global_in; subst.
           destruct (heap_globals (v0, d) i) as [? [? [? _]]].
           deprod.
           eauto with searches.
    + destruct (alloc hg0 (sclos (v0, e, eg0))) eqn:alloc1.
      exists ((v, vaddr a) :: eg0).
      exists h.
      repeat split...
      * simpl. eapply (st_cons st0).
        constructor...
      * simpl. congruence.
        (* FIXME copy-pasted *)
      * intro global. case_match.
        intro global_in.
        destruct (((v, vaddr a) :: eg0) !! v1) eqn:search1.
        unfold lookup in search1.
        simpl in search1.
        destruct (decEq v1 v); simplify_eq.
        -- exists a. exists (sclos (v0, e, eg0)).
           repeat split...
           ++ simpl...
           ++ simpl...
           ++ eauto with heaps.
           ++ inversion unique; subst.
              assert (In (v, d) defs -> False) by eauto with searches.
              forced global_in; simplify_eq.
              apply defined_sclos.
              clear - H0 unique scoped same_globals heap_globals.
              intros x0 x0_free x0_neq.
              enough (In x0 (map fst defs)).
              ** unfold lookup.
                 rewrite -> same_globals in H.
                 destruct (In_fst_search x0 eg0 H) as [y search_x0].
                 exists y. split...
                 simpl. destruct (decEq x0 v)...
                 subst. rewrite <- same_globals in H.
                 inversion unique; subst.
                 contradict H3...
              ** apply H0. constructor...
        (* copy-pasted, should fix *)
        -- assert (In (v1, d) defs) by (forced global_in; assumption).
           destruct (heap_globals (v1, d) H1) as [a' [sv [in1 [lkp1 [hlkp1 d0]]]]].
           exists a'. exists sv.
           deprod.
           repeat split...
           ++ simpl. forced (decEq v1 v)...
           ++ simpl. forced (decEq v1 v)...
           ++ eauto with heaps.
           ++ clear - d0 same_globals unique scoped.
              inversion unique; subst.
              inversion d0; clear d0; subst; constructor.
              ** generalize dependent vals.
                 induction xs...
                 intros vals H.
                 simpl map_option in *.
                 unfold lookup in *.
                 forced (search a0 eg0).
                 forced (map_option (flip search eg0) xs).
                 simplify_eq.
                 rewrite -> (IHxs l)...
                 simpl.
                 destruct (decEq a0 v) as [->|neq]...

                 contradict H1.
                 enough (In (v, v1) eg0); eauto with searches.
                 rewrite -> same_globals. eauto with searches.
              ** unfold lookup in *.
                 intros x0 x0_free x0_neq.
                 simpl search in *.
                 destruct (decEq x0 v)... subst.
                 contradict H1.
                 destruct (H v x0_free x0_neq) as [? [? _]].
                 rewrite -> same_globals.
                 eauto with searches.
        (* search can't fail *)
        -- unfold lookup in search1. simpl in search1.
           destruct (decEq v1 v); simplify_eq.
           contradict search1.
           simpl In in global_in.
           forced global_in; subst.
           destruct (heap_globals (v1, d) i) as [? [? [? _]]].
           deprod.
           eauto with searches.
Qed.
*)
