
Require Import stdpp.base.
Require Import stdpp.sets.
Require Import stdpp.fin_sets.

Require Import LocalTactics.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import DecEq.
Require Import IO.
Require Steps.

Require Import SyntaxParams.
Require Import HeapParams.
Module SXML (varParams: SyntaxParams) (heapParams: HeapParams).
  Export varParams.
  Export heapParams.

  (* Source language *)
  
  Inductive smallExp :=
  | tupleExp : list var -> smallExp
  | appExp : var -> var -> smallExp
  | projExp : var -> nat -> smallExp
  | writeExp : var -> smallExp
  | readExp : smallExp
  | constExp : bool -> smallExp
  .

  Inductive exp :=
  | letsmall : var -> smallExp -> exp -> exp
  | letabs : var -> var -> exp -> exp -> exp
  | branch : var -> exp -> exp -> exp
  | tail : var -> var -> exp
  | ret : var -> exp
  .

  (* Operational types *)

  Inductive value :=
  | vaddr : addr -> value
  | vconst : bool -> value
  .
  
  Definition env : Type := list (var * value).
  Definition clos := (var * exp * env)%type.

  Inductive svalue :=
  | sclos : clos -> svalue
  | stuple : list value -> svalue
  .

  Record state :=
    { icode : exp
    ; ienv : env
    ; iheap : heap svalue
    ; istack : list clos }.

  Notation "'<<' c ',' e ',' h ',' k '>>'" := (Build_state c e h k) (at level 60) : interp_scope.
  Bind Scope interp_scope with state.
  Delimit Scope interp_scope with interp.

  (* Step definitions *)

  Inductive store_path
    :=
    | clos_var (v: var) :
        store_path ->
        store_path
    | tuple_proj (i: nat) :
        store_path ->
        store_path
    | here : store_path
  .

  Record access_path :=
    { ap_stack_env : nat
    ; ap_env_var : var
    ; ap_store_path : store_path
    }
  .
  
  Fixpoint lookup_store_path (h: heap svalue) val spath: option value
    :=
      match spath, val with
      | clos_var v rest, vaddr a =>
        match h !! a with
        | Some (sclos (_, _, env)) =>
          match search v env with
          | Some val => lookup_store_path h val rest
          | None => None
          end
        | _ => None
        end
      | tuple_proj i rest, vaddr a =>
        match h !! a with
        | Some (stuple xs) =>
          match nth_error xs i with
          | Some val => lookup_store_path h val rest
          | None => None
          end
        | _ => None
        end
      | _, _ => Some val
      end
  .

  Definition lookup_store_value (h: heap svalue) val spath : option svalue
    :=
      match lookup_store_path h val spath with
      | Some (vaddr a) => h !! a
      | _ => None
      end.

  Definition lookup_object (e: env) (h: heap svalue) (x: var): option svalue :=
    match e !! x with
    | Some (vaddr a) => h !! a
    | _ => None
    end.

  (* TODO: read is missing *)
  Inductive step : option io_evt -> state -> state -> Prop :=
  | step_tuple x xs cr e h k vs a h' :
      forall (lkps: searches xs e = Some vs)
             (alloc_tuple: alloc h (stuple vs) = (a, h')),
      step None
        (<< letsmall x (tupleExp xs) cr , e, h, k >>)
        (<< cr , (x, vaddr a) :: e, h', k >>)
  | step_app x xf xa cr e h k xl el cl v :
      forall (lkp_clos_addr: 
                lookup_object e h xf = Some (sclos (xl, cl, el)))
             (lkp_arg: e !! xa = Some v),
      step None
        (<< letsmall x (appExp xf xa) cr , e, h, k >>)
        (<< cl , (xl, v) :: el, h, (x, cr, e) :: k >>)
  | step_proj x xt i cr e h k vs v :
      forall (lkp_proj: lookup_object e h xt = Some (stuple vs))
             (proj_tuple: nth_error vs i = Some v),
      step None
        (<< letsmall x (projExp xt i) cr , e, h, k >>)
        (<< cr , (x, v) :: e, h, k >>)
  | step_write x xw cr e h k b :
      forall (lkp_write: e !! xw = Some (vconst b)),
      step (Some (write b))
        (<< letsmall x (writeExp xw) cr , e, h, k >>)
        (<< cr , (x, vconst true) :: e, h, k >>)
  | step_const x b cr e h k :
      step None
        (<< letsmall x (constExp b) cr , e, h, k >>)
        (<< cr , (x, vconst b) :: e,  h, k >>)
  | step_abs x xl cl cr e h k h' a :
      forall (alloc_abs: alloc h (sclos (xl, cl, e)) = (a, h')),
      step None
        (<< letabs x xl cl cr , e, h, k >>)
        (<< cr , (x, vaddr a) :: e, h', k >>)
  | step_branch xb ct cf e h k b :
      forall (lkp_branch: e !! xb = Some (vconst b)),
      step None
        (<< branch xb ct cf , e, h, k >>)
        (<< if b then ct else cf , e, h, k >>)
  | step_ret xr e h xl cl el k v :
      forall (lkp: e !! xr = Some v),
      step None
        (<< ret xr , e, h, (xl, cl, el) :: k >>)
        (<< cl , (xl, v) :: el, h, k >>)
  .

  Theorem step_det : forall s1 s2 s3 io,
      step io s1 s2 ->
      step io s1 s3 ->
      s2 = s3.
  Proof.
    intros.
    inversion H; inversion H0; simplify_eq;
      congruence.
  Qed.

  Definition start_state c : state := (<< c, [], empty, [] >>)%interp.

  (* This is propositional up to extensionality,
     but we need to use the information when computing
     some data that we need in Type for computing sizes *)
  CoInductive not_stuck : state -> Type
    :=
    | can_pure s1 s2 :
        step None s1 s2 ->
        not_stuck s2 ->
        not_stuck s1
    | can_read s1 s2 :
        (forall k,
            step (Some (read k)) s1 s2 *
            not_stuck s2) ->
        not_stuck s1
    | can_write s1 s2 k :
        step (Some (write k)) s1 s2 ->
        not_stuck s2 ->
        not_stuck s1
    | finished xr e h :
        not_stuck (<< ret xr , e, h, [] >>)
  .

  Theorem not_stuck_step :
    forall i s1 s2,
      not_stuck s1 ->
      step i s1 s2 ->
      not_stuck s2.
  Proof with eauto.
    intros.
    destruct X.
    - enough (i = None).
      subst.
      destruct (step_det s1 s0 s2 None s H)...
      destruct H; inversion s; reflexivity.
    - destruct i.
      + destruct i.
        (* write *)
        * exfalso. destruct (p false).
          destruct H; inversion s.
        * destruct (p b).
          destruct (step_det s1 s0 s2 (Some (read b)))...
      + exfalso. destruct (p false).
        destruct H; inversion s.
    - enough (i = Some (write k))...
      subst.
      destruct (step_det s1 s0 s2 (Some (write k)))...
      inversion s; subst; inversion H; congruence.
    - exfalso. inversion H.
  Qed.

  Global Hint Resolve not_stuck_step : steps.


  Inductive free_in_small : var -> smallExp -> Prop
    :=
    | free_tuple x vs :
        In x vs ->
        free_in_small x (tupleExp vs)
    | free_app_f x va :
        free_in_small x (appExp x va)
    | free_app_a x vf :
        free_in_small x (appExp vf x)
    | free_proj x i:
        free_in_small x (projExp x i)
    | free_write x :
        free_in_small x (writeExp x)
  .

  Inductive free_in : var -> exp -> Prop
    :=
    | free_smallExp x v se er :
        free_in_small x se ->
        free_in x (letsmall v se er)
    | free_smallExp_r x v se er :
        free_in x er ->
        x <> v ->
        free_in x (letsmall v se er)
    | free_abs x v vl el er :
        free_in x el ->
        x <> vl ->
        free_in x (letabs v vl el er)
    | free_abs_r x v vl el er :
        free_in x er ->
        x <> v ->
        free_in x (letabs v vl el er)
    | free_ret x :
        free_in x (ret x)
    | free_branch_test b et ef:
        free_in b (branch b et ef)
    | free_branch_true x b et ef:
        free_in x et ->
        free_in x (branch b et ef)
    | free_branch_false x b et ef:
        free_in x ef ->
        free_in x (branch b et ef)
    | free_tail_f x va :
        free_in x (tail x va)
    | free_tail_a vf x:
        free_in x (tail vf x)
  .
  Hint Constructors free_in free_in_small : free_in.

  Fixpoint free_vars (e: exp): vars
    :=
    match e with
    | letsmall v se er =>
      union (
      match se with
      | tupleExp vs => list_to_set vs
      | appExp vf va => union {[vf]} {[va]}
      | projExp v _ => {[v]}
      | readExp => empty
      | writeExp v => {[v]}
      | constExp c => empty
      end)
      (difference (free_vars er) {[v]})
    | letabs v vl el er =>
      union 
        (difference (free_vars el) {[vl]})
        (difference (free_vars er) {[v]})
    | ret x => {[x]}
    | tail vf va => union {[vf]} {[va]}
    | branch b et ef =>
      union {[b]}
      (union (free_vars et) (free_vars ef))
    end.

  Theorem in_free_vars_iff_free_in : forall v e,
      elem_of v (free_vars e) <-> free_in v e.
  Proof with eauto.
    split. intros.
    (* -> *)
    - induction e; simpl in H |- *; set_unfold.
      (* letsmall *)
      + destruct H...
        (* in smallExp *)
        * apply free_smallExp.
          destruct s; set_unfold; subst;
            try contradiction;
            try constructor...
          { rewrite <- elem_of_list_In... }
          (* app *)
          -- destruct H; subst.
             ++ constructor...
             ++ constructor.
        (* in rest *)
        * destruct H. apply free_smallExp_r...
      (* letabs *)
      + destruct H as [[? ?] | [? ?]].
        (* v in free_vars e1 - v1 *)
        * apply free_abs...
        * apply free_abs_r...
      (* branch *)
      + destruct H as [? | [? | ?]]; subst.
        * constructor...
        * apply free_branch_true...
        * apply free_branch_false...
      (* tail *)
      + destruct H; subst; constructor...
      (* ret *)
      + destruct H...
        apply free_ret.
    - intros H. induction H; simpl; set_unfold...
      (* in small *)
      + inversion H; set_unfold; simplify_eq...
        (* tuple *)
        rewrite <- elem_of_list_In in H0...
  Qed.
  (* Blocks computation too much
  Instance set_unfold_free_vars {v e} : SetUnfold (elem_of v (free_vars e)) (free_in v e) :=
    { set_unfold := (in_free_vars_iff_free_in v e) }.
   *)

  Hint Resolve -> in_free_vars_iff_free_in : free_in addr_in.
  Hint Resolve <- in_free_vars_iff_free_in : free_in addr_in. (* useful to have these in addr_in for environments *)

  Definition clos_size (cls: clos): nat
    := match cls with
       | (xl, el, cl) => 1 + size (difference (free_vars el) {[xl]})
       end.

  Definition svalue_size (sv : svalue): nat
    :=
      match sv with
      | sclos cls => clos_size cls
      | stuple vs => 1 + length vs
      end.

  Definition value_to_addr (v: value): option addr
    :=
      match v with
      | vaddr a => Some a
      | _ => None
      end.
  (* This is weird but saves a lot of trouble *)
  Instance set_unfold_value_to_addr {v a} : SetUnfold (value_to_addr v = Some a) (v = vaddr a).
  Proof with eauto.
    intros; split; split; intros.
    - forced v. simpl in H. congruence.
    - subst. reflexivity.
  Qed.

  Definition var_points_to_addr (x: var) e := exists a, In (x, vaddr a) e.
  

  Definition env_addresses (xs: vars) (e: env) : addrs
    :=
      list_to_set
        (filter_map (fun v => match search v e with
                              | Some (vaddr a) => Some a
                              | _ => None
                              end)
        (elements xs)).

  Definition clos_addresses (clos: clos): addrs
    :=
      match clos with
      | (xl, cl, el) => env_addresses (difference (free_vars cl) {[xl]}) el 
      end.

  Definition svalue_addresses (sv : svalue): addrs
    :=
      match sv with
      | sclos cl => clos_addresses cl
      | stuple vs =>
        list_to_set (filter_map value_to_addr vs)
      end.

  Definition address_addresses (h: heap svalue) (a: addr): addrs
    :=
      match h !! a with
      | Some sv => svalue_addresses sv
      | None => empty
      end.

  Definition sum_list := fold_right plus 0. 

  Definition lookup_size (size1: svalue -> nat) (h: heap svalue) (a: addr) :=
    match h !! a with
    | Some sv => size1 sv
    | None => 0
    end.

  Definition live_roots st
    :=
      match st with
      | << c, e, h, k >>%interp =>
        let stack_roots := union_list (map clos_addresses k) in
        union
          stack_roots
          (env_addresses (free_vars c) e)
      end.

  Definition space_of (size1: svalue -> nat) (h: heap svalue) (addrs1: addrs) :=
    sum_list (map (lookup_size size1 h) (elements addrs1)).

  Instance sum_list_perm : Proper (Permutation ==> eq) sum_list.
  Proof.
    unfold Proper, respectful.
    intros.
    induction H; simpl; congruence || lia.
  Qed.

  Instance sum_list_sublist : Proper (submseteq ==> le) sum_list.
  Proof.
    unfold Proper, respectful.
    intros.
    induction H; simpl; lia.
  Qed.

  Instance map_sublist {A B} {f: A -> B} : Proper (@submseteq A ==> @submseteq B) (map f).
  Proof with auto.
    unfold Proper, respectful.
    intros.
    induction H; simpl.
    - apply submseteq_nil...
    - apply submseteq_skip...
    - apply submseteq_swap...
    - apply submseteq_cons...
    - apply submseteq_trans with (map f l2)...
  Qed.

  Instance space_of_equiv {size1 h} : Proper (equiv ==> eq) (space_of size1 h).
  Proof.
    intros. unfold space_of, Proper, respectful.
    intros.
    rewrite -> H.
    reflexivity.
  Qed.
    
  Instance space_of_subset {size1 h} : Proper (subseteq ==> le) (space_of size1 h).
    unfold Proper, respectful.
    intros.
    unfold space_of.
    apply sum_list_sublist.
    apply map_sublist.
    apply elements_submseteq.
    exact H.
  Qed.

  Theorem sum_list_app {l1 l2} : sum_list (l1 ++ l2) = sum_list l1 + sum_list l2.
  Proof with eauto.
    induction l1; simpl; lia.
  Qed.

  Lemma addrs_space_singleton {size1 h a1} : space_of size1 h (singleton a1) = lookup_size size1 h a1.
  Proof with eauto.
    intros. unfold space_of.
    rewrite -> elements_singleton.
    simpl...
  Qed.

  Lemma addrs_space_union {size1 h as1 as2} : as1 ## as2 -> space_of size1 h (union as1 as2) = space_of size1 h as1 + space_of size1 h as2.
  Proof with eauto.
    intros.
    unfold space_of.
    rewrite -> elements_disj_union...
    rewrite -> map_app.
    rewrite -> sum_list_app.
    done.
  Qed.

  Lemma addrs_space_extension {size1 h h' addrs} :
    heap_extension h h' ->
    (forall a s, elem_of a addrs -> h' !! a = Some s -> h !! a = Some s) ->
    space_of size1 h addrs = space_of size1 h' addrs.
  Proof with eauto.
    intros.
    induction H...
    rewrite <- IHheap_extension.
    (* one extension *)
    - unfold space_of.
      f_equal.
      apply map_ext_in.
      intros. set_unfold.

      rewrite <- elem_of_list_In in H2.
      assert (elem_of a0 addrs) by set_solver.
      unfold lookup_size.
      destruct (h2 !! a0) eqn:lkp2.
      + assert (h3 !! a0 = Some s) by (apply (found_extension _ _ H1 lkp2)).
        assert (H5: h1 !! a0 = Some s)...
        rewrite -> H5...
      + assert (h1 !! a0 = None) by eauto with heaps.
        rewrite -> H4...
    - intros.
      apply H0 in H3...
      eauto with heaps.
  Qed.


  Definition addrs_space0 :=
    space_of svalue_size.
  Definition addrs_space size1 s (addrs: addrs) :=
    match s with
    | << _, _, h, k >>%interp =>
      space_of size1 h addrs
    end.

  (*

    In order to be able to push validity and freshness statements through, we want to be able
    to talk about which addresses could possibly appear.

   *)

  Inductive addr_in_val : AddrIn value :=
  | addr_in_vaddr a :
      addr_in (vaddr a) a.
  Global Existing Instance addr_in_val.
  Global Hint Constructors addr_in_val : addr_in.
  Global Hint Extern 5 =>
    match goal with
    | [ H: addr_in_val (vconst _) _ |- _ ] =>
      solve [inversion H]
    | [ H: @addr_in value _ (vconst _) _ |- _ ] =>
      solve [inversion H]
    | [ H: addr_in_val ?v ?a |- _ ] =>
      (replace v with (vaddr a) in * by (inversion H; subst; reflexivity);
       clear H)
    | [ H: @addr_in value _ ?v ?a |- _ ] =>
      (replace v with (vaddr a) in * by (inversion H; subst; reflexivity);
       clear H)
    end : addr_in.


        

  Global Instance addr_in_env : AddrIn (env * vars) :=
    fun p =>
      let (e, xs) := p in
        fun a =>
        exists x v,
          e !! x = Some v /\
          elem_of x xs /\
          addr_in v a.

  Global Instance addr_in_env0 : AddrIn env :=
    fun e => fun a =>
      exists x v,
        e !! x = Some v /\
        addr_in v a.

  Global Instance addr_in_clos : AddrIn clos :=
    fun clos =>
      match clos with
      | (xl, cl, el) => addr_in (el, difference (free_vars cl) {[xl]})
      end.
  Instance clos_addresses' : Addresses clos :=
    { addresses := clos_addresses }.
  Proof with eauto.
    intros.
    unfold addr_in, addr_in_clos, addr_in, addr_in_env.
    destruct sv as [[xl cl] el].
    split; intros; deep_set_unfold.
    - forced (search x el). forced v.
      simplify_eq.
      exists x, (vaddr a).
      repeat split_and...
      constructor.
    - unfold lookup in *.
      exists x. rewrite -> H.
      inversion H1...
  Defined.

  Global Instance addr_in_list `{AddrIn X}: AddrIn (list X)
    :=
      fun l =>
        fun a =>
          exists x,
            In x l /\ addr_in x a.

  Global Instance addr_in_svalue : AddrIn svalue :=
    fun sv =>
      match sv with
      | stuple vs => addr_in vs
      | sclos clos => addr_in clos
      end.
  Instance svalue_addresses' : Addresses svalue :=
    { addresses := svalue_addresses }.
  Proof with eauto.
    intros; split; intros.
    - destruct sv; simpl in H.
      + destruct c; simpl in *. destruct p.
        unfold addr_in, addr_in_svalue, addr_in, addr_in_clos, addr_in, addr_in_env.
        unfold env_addresses in H.
        deep_set_unfold. unfold lookup.
        forced (search x e).
        forced v0. simplify_eq.
        exists x, (vaddr a). repeat split_and...
        constructor.
      + deep_set_unfold.
        unfold addr_in, addr_in_svalue, addr_in, addr_in_list.
        exists (vaddr a). split... rewrite <- elem_of_list_In...
        constructor.
    - unfold addr_in in H. destruct sv; simpl in *.
      + destruct c as [[xl cl] el].
        repeat unfold addr_in, addr_in_clos, addr_in_env in *.
        deep_set_unfold.
        inversion H1; subst.
        exists x. split...
        unfold lookup in H.
        rewrite -> H...
      + set_unfold.
        unfold addr_in, addr_in_list in *.
        deprod. exists x. rewrite -> elem_of_list_In.
        split...
        inversion H0; subst...
  Defined.

  Global Instance addr_in_heap `{AddrIn X} : AddrIn (heap X)
    :=
      fun h =>
        fun a =>
          exists a' sv,
            h !! a' = Some sv /\ addr_in sv a.

  Global Instance addr_in_state : AddrIn state
    :=
      fun s =>
        match s with
        | (<< c, e, h, k >>)%interp =>
          fun a =>
            addr_in h a \/ addr_in k a \/ addr_in (e, free_vars c) a
        end.

  Definition valid_in_heap `{AddrIn X} (x: X) (h: heap svalue): Prop
    :=
      forall a,
        addr_in x a -> h !! a <> None.

  Lemma heap_valid_in_heap h :
    valid_in_heap h h <-> heap_valid h.
  Proof with eauto.
    intros. unfold heap_valid, valid_in_heap, addr_in, addr_in_heap.
    split; intro H.
    - intros. apply H...
    - intros. deprod...
  Qed.

  Lemma valid_in_heap_alloc `{AddrIn X} (x: X) h h' a sv :
    alloc h sv = (a, h') ->
    valid_in_heap x h ->
    valid_in_heap x h'.
  Proof.
    unfold valid_in_heap.
    intros.
    eauto with heaps.
  Qed.
    

  Lemma const_valid_in_heap :
    forall b h,
    valid_in_heap (vconst b) h.
  Proof.
    unfold valid_in_heap. intros.
    inversion H.
  Qed.
      

  Global Hint Transparent valid_in_heap addr_in lookup : addr_in.
  Global Hint Unfold addr_in_list addr_in_env0 addr_in_env addr_in_heap addr_in_list addr_in_svalue addr_in_clos addr_in_state : addr_in.
  Global Hint Constructors addr_in_val.
  Global Hint Extern 1 (addr_in _ _) => unfold addr_in :  addr_in.
  Global Hint Unfold In : addr_in.
  Global Hint Resolve const_valid_in_heap : addr_in.
  Global Hint Resolve valid_in_heap_alloc : addr_in.
  Global Hint Resolve -> heap_valid_in_heap : addr_in.
  Global Hint Resolve <- heap_valid_in_heap : addr_in.

  Global Hint Resolve search_In : addr_in.

  Ltac addr_conflict h a :=
    match goal with
    | |- ¬ _ => intro
    | _ => idtac
    end;
    absurd (h !! a = None);
    solve [match goal with
    | [ |- ?h !! ?a = None ] => eauto with heaps
    | [ |- ?h !! ?a <> None ] => eauto 20 with addr_in
    end].

  Local Example ex_addr_in_cons :
    forall (h : heap svalue)  v a1 a2 vs,
      h !! a1 = Some (stuple (v :: vaddr a2 :: vs)) ->
    addr_in h a2.
  Proof.
    eauto 20 with addr_in.
  Qed.

  Lemma addr_in_cons `{AddrIn X} : forall a x (xs : list X),
      addr_in xs a ->
      addr_in (x :: xs) a.
  Proof with auto.
    intros.
    unfold addr_in, addr_in_list in *.
    destruct H0 as [x0 [? ?]].
    exists x0. split...
    right...
  Qed.

  Global Hint Resolve addr_in_cons : addr_in.
       
  Lemma addr_in_search : forall (e: env) (xs: vars) a x v,
      search x e = Some v ->
      elem_of x xs ->
      addr_in v a ->
      addr_in (e, xs) a.
  Proof with eauto.
    intros.
    assert (In (x, v) e) by eauto with searches.
    unfold addr_in, addr_in_env.
    exists x, v.
    repeat split_and...
  Qed.
  Lemma addr_in_search0 : forall (e: env) (xs: vars) a x v,
      search x e = Some v ->
      addr_in v a ->
      addr_in e a.
  Proof with eauto.
    intros.
    assert (In (x, v) e) by eauto with searches.
    unfold addr_in, addr_in_env.
    exists x, v.
    repeat split_and...
  Qed.
  Lemma addr_in_env_lookup : forall (e : env) (xs: vars) a x v,
      e !! x = Some v ->
      elem_of x xs ->
      addr_in v a ->
      addr_in (e, xs) a.
  Proof.
    unfold lookup. apply addr_in_search.
  Qed.
  Lemma addr_in_searches : forall (e: env) (xs0: vars) a xs vs,
      searches xs e = Some vs ->
      (forall x, In x xs -> elem_of x xs0) ->
      addr_in vs a ->
      addr_in (e, xs0) a.
  Proof with auto.
    intros. unfold searches in *.
    generalize dependent vs.
    induction xs; simpl; intros vs H in1; simplify_eq.
    - unfold addr_in, addr_in_list in in1.
      destruct in1 as [? [? ?]]; contradiction.
    - forced (search a0 e).
      forced (map_option (flip search e) xs).
      simplify_eq.
      unfold addr_in, addr_in_list in in1.
      deprod.
      destruct H; subst.
      + apply addr_in_search with a0 x...
      + apply IHxs with l...
        { intros. apply H0. right... }
        unfold addr_in, addr_in_list.
        exists x...
  Qed.
  Lemma addr_in_searches0 : forall (e: env) (xs0: vars) a xs vs,
      searches xs e = Some vs ->
      addr_in vs a ->
      addr_in e a.
  Proof with auto.
    intros. unfold searches in *.
    generalize dependent vs.
    induction xs; simpl; intros vs H in1; simplify_eq.
    - unfold addr_in, addr_in_list in in1.
      destruct in1 as [? [? ?]]; contradiction.
    - forced (search a0 e).
      forced (map_option (flip search e) xs).
      simplify_eq.
      unfold addr_in, addr_in_list in in1.
      deprod.
      destruct H; subst.
      + apply addr_in_search0 with a0 x...
      + apply IHxs with l...
        { intros. exists x... }
  Qed.
  Lemma In_env_valid : forall h e xs x v,
      valid_in_heap (e, xs) h ->
      elem_of x xs ->
      e !! x = Some v ->
      valid_in_heap v h.
  Proof with eauto.
    unfold valid_in_heap. intros.
    apply H. unfold addr_in, addr_in_env.
    exists x, v. repeat split_and...
  Qed.
    
      
  Global Hint Resolve addr_in_search addr_in_search0 addr_in_env_lookup addr_in_searches addr_in_searches0 : addr_in.

  Definition state_valid (s: state): Prop
    :=
      match s with
      | (<< _, _, h, _ >>)%interp =>
        valid_in_heap s h
      end.

  Lemma state_valid_product :
    forall c e h k,
      valid_in_heap (e, free_vars c) h /\
      valid_in_heap h h /\
      valid_in_heap k h
      <->
      valid_in_heap (<< c, e, h, k >>)%interp h.
  Proof with eauto.
    unfold valid_in_heap.
    intros; split; intros.
    - unfold addr_in, addr_in_state in H0.
      destruct H as [? [? ?]].
      destruct H0 as [? | [? | ?]]...
    - unfold addr_in, addr_in_state in H.
      repeat split...
  Qed.

  Lemma state_valid_into_heap :
    forall c e h k,
      valid_in_heap (<< c, e, h, k >>)%interp h ->
      valid_in_heap h h.
  Proof with eauto.
    intros.
    rewrite <- state_valid_product in *.
    deprod...
  Qed.

  Global Hint Extern 1 (valid_in_heap _ _) => unfold valid_in_heap :  addr_in.
  Global Hint Transparent state_valid : addr_in.
  Global Hint Transparent lookup : addr_in.
  Global Hint Resolve state_valid_into_heap : addr_in.
  Global Hint Resolve -> state_valid_product : addr_in.
  Global Hint Resolve <- state_valid_product : addr_in.


  Lemma extend_valid_env0 :
    forall (e : env) x sv a h h',
      alloc h sv = (a, h') ->
      valid_in_heap e h ->
      valid_in_heap ((x, vaddr a) :: e) h'.
  Proof with eauto.
    unfold valid_in_heap.
    intros.
    destruct H1 as [x0 [v0 [lkpx0 addrv0]]].
    unfold lookup in lkpx0. simpl in lkpx0.
    unfold addr_in in addrv0.
    inversion addrv0; subst.
    destruct (decEq x0 x); simplify_eq; deprod...
    - eauto with heaps.
    - eapply not_dangling_later...
      apply H0.
      eauto 20 with addr_in.
  Qed.
  Lemma extend_valid :
    forall (e : env) (xs : vars) x sv a h h',
      alloc h sv = (a, h') ->
      valid_in_heap (e, xs) h ->
      valid_in_heap ((x, vaddr a) :: e, xs) h'.
  Proof with eauto.
    unfold valid_in_heap.
    intros.
    destruct H1 as [x0 [v0 [lkpx0 addrv0]]].
    unfold lookup in lkpx0. simpl in lkpx0.
    unfold addr_in in addrv0.
    inversion addrv0; subst.
    destruct (decEq x0 x); simplify_eq; deprod...
    - inversion H4; subst. eauto with heaps.
    - eapply not_dangling_later...
      apply H0.
      unfold addr_in, addr_in_env.
      eauto 20 with addr_in.
  Qed.

  Global Hint Resolve extend_valid extend_valid_env0 : addr_in.
                          
  Lemma env_cons_addr_in : forall a x v (e : env) c,
      addr_in ((x, v) :: e, c) a ->
      addr_in v a \/ addr_in (e, c) a.
  Proof with eauto.
    intros.
    unfold addr_in, addr_in_env in *.
    deprod. unfold lookup in H. simpl in H.
    destruct (decEq x0 x); simplify_eq.
    - left...
    - right...
  Qed.
  Lemma env_cons_valid : forall h (e: env) c (v: value) x,
    valid_in_heap v h ->
    valid_in_heap (e, c) h ->
    valid_in_heap ((x, v) :: e, c) h.
  Proof.
    intros.
    unfold valid_in_heap in *.
    intros.
    apply env_cons_addr_in in H1.
    destruct H1; eauto with addr_in.
  Qed.
  Lemma env0_cons_addr_in : forall a x v (e : env),
      addr_in ((x, v) :: e) a ->
      addr_in v a \/ addr_in e a.
  Proof with eauto.
    intros.
    unfold addr_in, addr_in_env0 in *.
    deprod. unfold lookup in H. simpl in H.
    destruct (decEq x0 x); simplify_eq.
    - left...
    - right...
  Qed.
  Lemma env0_cons_valid : forall h (e: env) (v: value) x,
    valid_in_heap v h ->
    valid_in_heap e h ->
    valid_in_heap ((x, v) :: e) h.
  Proof.
    intros.
    unfold valid_in_heap in *.
    intros.

    apply env0_cons_addr_in in H1.
    destruct H1; eauto with addr_in.
  Qed.
  Global Hint Resolve env_cons_addr_in env_cons_valid : addr_in.
  Global Hint Resolve env0_cons_addr_in env0_cons_valid : addr_in.

  Lemma state_valid_start :
    forall P,
      state_valid (start_state P).
  Proof with eauto.
    intros.
    unfold state_valid.
    unfold start_state.
    do 2 intro.
    unfold addr_in, addr_in_state in H.
    destruct H.
    { inversion H. deprod.
      rewrite -> lookup_empty in H0.
      discriminate. }
    { inversion H; deprod; inversion H0; deprod; inversion H1. }
  Qed.

  Lemma state_valid_step :
    forall s1 s2 i,
      state_valid s1 ->
      step i s1 s2 ->
      state_valid s2.
  Proof with eauto 10 with heaps addr_in.
    unfold state_valid.
    intros. destruct s1, s2.
    rewrite <- state_valid_product in *.
    destruct H as [oldenv [oldheap oldstack]].
    inversion H0; subst; repeat split;
      try solve [typeclasses eauto 10 with addr_in];
    unfold valid_in_heap in *; intros...
    (* tuple env *)
    - destruct (decEq a a0); subst; eauto with heaps.
      eapply not_dangling_later...
      destruct H as [x0 [sv0 [? ?]]]; subst.
      unfold addr_in in H0. simpl in H0.
      unfold lookup in H.
      simpl in H.
      deprod.
      inversion H2; subst.
      forced (decEq x0 x).
      apply oldenv.
      unfold addr_in, addr_in_env.
      unfold lookup.
      exists x0, (vaddr a0).
      repeat split_and...
      simpl. set_solver.
    - destruct (decEq a a0); subst; eauto with heaps.
      eapply not_dangling_later...
      destruct H. deprod.
      destruct (decEq x0 a); subst...
      apply oldenv.
      assert (iheap1 !! a = Some (stuple vs)) by eauto with heaps.
      simplify_eq.
      inversion H1; subst. deprod.
      destruct (In_searches _ _ _ _ lkps H2).
      deprod.
      exists x1, x0.
      repeat split_and...
      (* fv *)
      simpl. rewrite <- elem_of_list_In in H4. clear - H4. set_solver.
    (* app env *)
    - destruct H; deprod.
      unfold lookup in H.
      simpl in H.
      destruct (decEq x0 xl); simplify_eq.
      + apply oldenv. exists xa, v0.
        repeat split_and...
        simpl. set_solver.
      + apply oldheap. unfold lookup_object in *.
        forced (ienv0 !! xf).
        forced v1. simplify_eq.
        exists a0, (sclos (xl, icode1, el)).
        split_and...
        exists x0, v0.
        repeat split_and...
        set_solver.
    (* app stack *)
    - inversion H. deprod.
      destruct H1; simplify_eq...
      apply oldenv.
      unfold addr_in, addr_in_clos in H2.
      simpl.
      destruct H2. deprod.
      exists x0, v0.
      repeat split_and...
      set_solver.
    (* proj env *)
    - destruct H. deprod.
      unfold lookup in H.
      simpl in H.
      destruct (decEq x0 x); simplify_eq.
      + apply oldheap. unfold lookup_object in *.
        forced (ienv0 !! xt).
        forced v.
        simplify_eq.
        exists a0, (stuple vs).
        split...
        split with v0.
        split...
        eapply nth_error_In...
      + apply oldenv.
        exists x0, v0.
        repeat split_and...
        simpl. set_solver.
    (* write env *)
    - destruct H. deprod.
      unfold lookup in H.
      simpl in H.
      destruct (decEq x0 x); simplify_eq.
      + inversion H2.
      + apply oldenv.
        exists x0, v. repeat split_and...
        simpl. set_solver.
    (* const env *)
    - destruct H. deprod.
      unfold lookup in H.
      simpl in H.
      destruct (decEq x0 x); simplify_eq.
      + inversion H2.
      + apply oldenv.
        exists x0, v. repeat split_and...
        simpl. set_solver.
    (* abs env *)
    - destruct (decEq a a0); subst; eauto with heaps.
      eapply not_dangling_later...
      destruct H. deprod.
      unfold lookup in H. simpl in H.
      destruct (decEq x0 x); subst...
      apply oldenv.
      assert (iheap1 !! a = Some _) by eauto with heaps.
      simplify_eq.
      inversion H2; subst.
      exists x0, (vaddr a0).
      repeat split_and...
      simpl. set_solver.
    (* abs heap *)
    - destruct (decEq a a0); subst; eauto with heaps.
      eapply not_dangling_later...
      destruct H. deprod.
      destruct (decEq x0 a); subst...
      apply oldenv.
      assert (iheap1 !! a = Some (sclos (xl, cl, ienv0))) by eauto with heaps.
      simplify_eq.
      unfold addr_in, addr_in_svalue, addr_in, addr_in_clos in H1.
      simpl.
      destruct H1; deprod.
      exists x0, v. repeat split_and...
      set_solver.
    (* branch env *)
    - apply oldenv.
      destruct H; deprod.
      exists x, v. repeat split_and...
      simpl. destruct b; set_solver.
    (* ret env *)
    - destruct H. deprod.
      unfold lookup in H.
      simpl in H. 
      destruct (decEq x xl); simplify_eq.
      + apply oldenv.
        exists xr, v0. repeat split_and...
        simpl. set_solver.
      + apply oldstack.
        exists (xl, icode1, el).
        split...
        exists x, v0. repeat split_and...
        simpl. set_solver.
  Qed.

  Global Hint Resolve state_valid_start state_valid_step : steps.

  Example fresh_addr_in_env c e h k sv a h' :
    state_valid (<< c, e, h, k >>) ->
    alloc h sv = (a, h') ->
    forall x,
      free_in x c ->
      e !! x <> Some (vaddr a).
  Proof.
    intros.
    intro.
    addr_conflict h a.
  Qed.




  Definition state_space st
    :=
      match st with
      | << c, e, h, k >>%interp =>
        let roots := live_roots st in
        let addrs := closure _ h roots in
        1 + space_of svalue_size h addrs + size (free_vars c) + sum_list (map clos_size k)
      end.

  Import Steps.

  Global Instance sxmlStep :
    Step state :=
    Build_Step _ SXML.step.

  Global Instance sxmlSpace :
    Space state :=
    Build_Space _ state_space.


  Bind Scope exp_scope with exp.
  Delimit Scope exp_scope with exp.
  Notation "'VAL' x ':=' e 'IN' er" := (letsmall x e er) (at level 90, right associativity,
  format "'VAL'  x  ':='  e  'IN'  '//'  er"): exp_scope.
  Notation "'FN' f x ':=' e 'IN' er" := (letabs f x e er) (at level 90, right associativity,
  format "'FN' f  x  ':=' e 'IN' '//' er"): exp_scope.



  Theorem not_stuck_steps :
    forall s1 s2,
      not_stuck s1 ->
      @steps state sxmlStep s1 s2 ->
      not_stuck s2.
  Proof with eauto.
    intros.
    induction X0...
    eapply not_stuck_step.
    { apply IHX0... }
    unfold step in s. unfold sxmlStep in s.
    apply s.
  Qed.

  Theorem state_valid_steps :
    forall s1 s2,
      state_valid s1 ->
      @steps state sxmlStep s1 s2 ->
      state_valid s2.
  Proof with eauto.
    intros.
    induction X...
    eapply state_valid_step.
    { apply IHX... }
    unfold step in s. unfold sxmlStep in s.
    apply s.
  Qed.

  Global Hint Resolve not_stuck_steps state_valid_steps : steps.

End SXML.

(*

  Require Import Coq.Strings.String.
  Definition foo := "foo"%string.
  Definition bar := "bar"%string.

Example prog1 : exp string
  :=
    VAL foo := tupleExp [] IN
    VAL bar := projExp foo 1 IN
    (ret foo).
Print prog1.
*)
