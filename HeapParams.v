Require Import stdpp.base.
Require Import stdpp.sets.
Require Import stdpp.fin_sets.
Require Import Coq.Classes.RelationClasses.
Require Import LocalTactics.
Require Import DecEq.

Module Type HeapParams.

  Parameter addr : Type.
  Parameter addrs : Type.

  (* Heaps can store any data *)
  Parameter heap : Type -> Type.

  Declare Instance addr_decEq: EqDecision addr.

  Context `{addrs_elem: ElemOf addr addrs, addrs_empty: Empty addrs, addrs_singleton: Singleton addr addrs, addrs_union : Union addrs, addrs_intersection : Intersection addrs, addrs_difference : Difference addrs, addrs_elements : Elements addr addrs}.
  Existing Instances addrs_elem addrs_empty addrs_singleton addrs_union addrs_intersection addrs_difference addrs_elements.
  Declare Instance addrs_finset : FinSet addr addrs.
  Declare Instance addrs_elem_dec: forall (a: addr) (aas: addrs), Decision (elem_of a aas).

  Declare Instance heap_empty : forall sv, Empty (heap sv).
  Declare Instance heap_lookup : forall sv, Lookup addr sv (heap sv).

  Class AddrIn X := addr_in : X -> addr -> Prop.
  Class Addresses SV `{AddrIn SV} :=
    { addresses : SV -> addrs
    ; addrs_iff : forall a sv,
        elem_of a (addresses sv) <-> addr_in sv a }.

  (* This parameter doesn't seem right??? *)
  Section Heap.
    Context {sv: Type}.
    Context `{sv_addr_in: AddrIn sv}.
    Context `{sv_addrs: @Addresses sv sv_addr_in}.

    Parameter alloc: heap sv -> sv -> (addr * heap sv).
    Parameter heap_lookup_finds : forall (h1 h2: heap sv) v (a: addr),
      alloc h1 v = (a, h2) ->
      h2 !! a = Some v.
    Parameter heap_lookup_fresh : forall (h1 h2: heap sv) v (a: addr),
      alloc h1 v = (a, h2) ->
      h1 !! a = None.
    Parameter heap_lookup_earlier : forall (h1 h2: heap sv) v1 (a1: addr),
      alloc h1 v1 = (a1, h2) ->
      forall (a: addr), (h2 !! a = h1 !! a) \/ a1 = a.
    Parameter heap_lookup_some_later : forall (h1 h2: heap sv) v1 (a1: addr),
      alloc h1 v1 = (a1, h2) ->
      forall (a: addr) v,
        h1 !! a = Some v ->
        h2 !! a = Some v.

    (* better for automation *)
    Lemma heap_lookup_earlier' : forall (h1 h2: heap sv) v1 (a1: addr),
      alloc h1 v1 = (a1, h2) ->
      forall (a: addr),
        a <> a1 ->
        (h2 !! a = h1 !! a).
    Proof.
      intros.
      destruct (heap_lookup_earlier h1 h2 v1 a1 H a); done.
    Qed.

    Parameter lookup_empty : forall (i: addr), (empty: heap sv) !! i = None.
    Hint Resolve alloc heap_lookup_finds heap_lookup_fresh heap_lookup_earlier heap_lookup_earlier' lookup_empty heap_lookup_some_later : heaps.

    Lemma heap_lookup_some_earlier : forall (h1 h2: heap sv) v1 (a1: addr),
      alloc h1 v1 = (a1, h2) ->
      forall (a: addr) v,
        a <> a1 ->
        h2 !! a = Some v ->
        h1 !! a = Some v.
    Proof.
      intros.
      assert (h2 !! a = h1 !! a) by eauto with heaps.
      congruence.
    Qed.

    Lemma heap_lookup_none_earlier : forall (h1 h2: heap sv) v1 (a1: addr),
      alloc h1 v1 = (a1, h2) ->
      forall (a: addr),
        h2 !! a = None ->
        h1 !! a = None.
    Proof.
      intros.
      destruct (heap_lookup_earlier h1 h2 v1 a1 H a); try congruence.
      (* a1 = a *)
      subst. apply (heap_lookup_fresh h1 h2 v1 a H).
    Qed.

    Lemma heap_lookup_none_later : forall (h1 h2: heap sv) v1 (a1: addr),
      alloc h1 v1 = (a1, h2) ->
      forall (a: addr),
        a <> a1 ->
        h1 !! a = None ->
        h2 !! a = None.
    intros.
    assert (h2 !! a = h1 !! a) by eauto with heaps.
    congruence.
    Qed.

    Hint Resolve heap_lookup_none_later : heaps.

    Definition closed `{Addresses sv} : heap sv -> addrs -> Prop
      :=
        fun h c =>
          set_Forall
            (fun (a: addr) => exists (sv: sv), h !! a = Some sv /\ addresses sv ⊆ c)
            c.

    Theorem closed_empty_iff_empty :
      forall c, closed empty c <-> equiv c empty.
    Proof.
      intros. split; unfold closed, set_Forall; set_unfold; intros.
      - unfold not. intros.
        destruct (H x H0) as [? [? _]].
        rewrite -> (lookup_empty x) in H1.
        discriminate.
      - destruct (H x H0).
    Qed.

    Theorem closed_alloc_1 :
      forall (h1 h2: heap sv) a sv c,
        alloc h1 sv = (a, h2) ->
        closed h1 c ->
        closed h2 c.
    Proof.
      unfold closed, set_Forall. intros.
      destruct (H0 x H1) as [sv1 [lkp1 in_addr]].
      exists sv1. split; auto.
      eauto with heaps.
    Qed.

    Theorem closed_alloc_2 :
      forall (h1 h2: heap sv) (a: addr) (sv: sv) (c: addrs),
        alloc h1 sv = (a, h2) ->
        closed h1 c ->
        (forall (a': addr),
            elem_of a' (addresses sv) ->
            elem_of a' c) ->
        closed h2 ({[ a ]} ∪ c).
    Proof.
      unfold closed, set_Forall. intros.
      set_unfold.
      destruct H2 as [-> | in_c].
      - exists sv0. split.
        + apply (heap_lookup_finds h1 h2 sv0 a); assumption.
        + set_solver.
      - destruct (H0 x in_c) as [ sv1 [ lkp1 in_addr]].
        exists sv1. split.
        + eauto with heaps.
        + auto.
    Qed.

    Definition heap_valid `{AddrIn sv} (h: heap sv) :=
      forall a (sv0: sv),
        h !! a = Some sv0 ->
        forall a',
          addr_in sv0 a' ->
          h !! a' <> None.

    Theorem closed_alloc_3 :
      forall (h1 h2: heap sv) (a: addr) (sv: sv) (c: addrs),
        heap_valid h1 ->
        alloc h1 sv = (a, h2) ->
        closed h2 c ->
        closed h1 (difference c {[ a ]}).
    Proof with auto.
      unfold closed, set_Forall. intros.
      - intros. set_unfold. destruct H2.
        destruct (H1 x H2) as [ sv1 [ lkp1 closed1]].
        exists sv1. split.
        + destruct (heap_lookup_earlier h1 h2 sv0 a H0 x) as [? | ->];
            congruence || contradiction.
        + intros. split.
          * set_solver.
          * destruct (heap_lookup_earlier h1 h2 sv0 a H0 x) as [? | ->];
              try congruence. unfold not. intros. subst.
            (* need an extra heap vailidity precondition:
              x0 would have been dangling in the pre-allocation heap *)
            unfold heap_valid in *.
            assert (h1 !! x = Some sv1) as old_x by congruence.
            destruct (H x sv1 old_x a).
            { rewrite <- addrs_iff... }
            eauto with heaps.
    Qed.

    Global Instance closed_proper {h} : Proper (equiv ==> impl) (closed h).
    Proof with auto.
      unfold Proper, closed, respectful, flip, impl, set_Forall.
      intros. rewrite <- H in H1.
      destruct (H0 x0 H1) as [sv1 [lkp1 addrs1]].
      exists sv1; split...
      rewrite <- H...
    Qed.

    Inductive heap_extension : heap sv -> heap sv -> Prop
      :=
      | heap_ext_refl h : heap_extension h h
      | heap_ext_cons h1 h2 h3 a v :
          alloc h1 v = (a, h2) ->
          heap_extension h2 h3 ->
          heap_extension h1 h3.
    Hint Constructors heap_extension : heaps.

    Global Instance heap_extension_reflexive : Reflexive heap_extension.
    Proof. intro. constructor. Qed.

    Global Instance heap_extension_transitive :
      Transitive heap_extension.
    Proof.
      unfold Transitive.
      intros. induction H.
      - exact H0.
      - apply (heap_ext_cons h1 h2 z a v); auto.
    Qed.

    Global Instance heap_extension_rewrite :
      RewriteRelation heap_extension.

    Definition heap_extension_one {h1 h2 a v} (H: alloc h1 v = (a, h2)): heap_extension h1 h2 :=
      heap_ext_cons h1 h2 h2 a v H (heap_ext_refl h2).


    Parameter closure : `{Addresses sv} -> heap sv -> addrs -> addrs.
    Parameter closure_inject : forall h a addrs1,
        elem_of a addrs1 ->
        h !! a <> None ->
        elem_of a (closure _ h addrs1).
    Parameter closure_descend : forall h a1 addrs1 v a2,
        elem_of a1 (closure _ h addrs1) ->
        h !! a1 = Some v ->
        addr_in v a2 ->
        h !! a2 <> None ->
        elem_of a2 (closure _ h addrs1).

    (* We need to make P dependent on the element proof to get Coq to figure out how to generalize,
       but in all cases we force P to be proof-irrelevant with it *)
    Parameter closure_ind :
      forall {h: heap sv} (valid: heap_valid h) {addrs1: addrs},
      forall (P: forall (a: addr), elem_of a (closure _ h addrs1) -> Prop)
        (P_inject: forall a, elem_of a addrs1 -> h !! a <> None -> forall el, P a el)
        (P_descend: forall a v el, P a el -> h !! a = Some v -> forall a2 el2, addr_in v a2 -> P a2 el2),
        forall a (el: elem_of a (closure _ h addrs1)), P a el.

    Theorem closure_empty :
      forall h,
        heap_valid h ->
        equiv (closure _ h empty) empty.
    Proof.
      intros.
      set_unfold. intro. intro.
      assert (forall a, elem_of a (empty: addrs) -> h !! a <> None) by set_solver.
      induction x, H0 using (closure_ind H).
      - intros. set_solver.
      - intros. contradiction.
    Qed.

    Theorem closure_union :
      forall h addrs1 addrs2,
        heap_valid h ->
        equiv (closure _ h (union addrs1 addrs2))
              (union (closure _ h addrs1)
                     (closure _ h addrs2)).
    Proof with eauto.
      intros.
      set_unfold.
      intros; split; intros.
      unfold heap_valid in H.
      - induction x, H0 using (closure_ind H).
        (* inject *)
        + intros. set_unfold.
          destruct H0_.
          * left. apply closure_inject...
          * right. apply closure_inject...
        (* descend *)
        + destruct IH1.
          * left. apply closure_descend with a v...


          * right. apply closure_descend with a v...
      - destruct H0.
        + induction x, H0 using (closure_ind H).
          (* inject *)
          * apply closure_inject... set_unfold...
          (* descend *)
          * apply closure_descend with a v...
        + induction x, H0 using (closure_ind H).
          (* inject *)
          * apply closure_inject... set_unfold...
          (* descend *)
          * apply closure_descend with a v...
    Qed.

    Lemma closure_valid :
      forall h s,
        heap_valid h ->
        forall a,
          elem_of a (closure _ h s) ->
          h !! a <> None.
    Proof with eauto.
      intros.
      induction a, H0 using (closure_ind H)...
    Qed.
        
    Theorem closure_closed :
      forall h s,
        heap_valid h ->
        closed h (closure _ h s).
    Proof with eauto.
      unfold closed, set_Forall.
      intros. unfold heap_valid in *.
      induction x, H0 using (closure_ind H).
      (* inject *)
      - forced (h !! a).
        exists s0. split...
        set_unfold.
        intros.
        eapply closure_descend...
        rewrite <- addrs_iff...
        apply H with a s0...
        rewrite <- addrs_iff...
      (* descend *)
      - deprod.
        destruct (h !! a2) eqn:ha2.
        + exists s0. split...
          set_unfold. intros.
          eapply closure_descend...
          rewrite <- addrs_iff...
          eapply H... 
          rewrite <- addrs_iff...
        + contradict ha2.
          eapply closure_valid...
    Qed.

    Theorem closure_of_closed :
      forall h s,
        heap_valid h ->
        closed h s ->
        equiv (closure _ h s) s.
    Proof with eauto.
      unfold closed, set_Forall.
      intros. set_unfold; split; intros.
      (* closure in original, by induction *)
      - induction x, H1 using (closure_ind H)...
        (* descend *)
        pose proof (H0 _ IH1).
        deprod. simplify_eq.
        set_unfold.
        pose proof (H4 a2) as H5.
        rewrite -> addrs_iff in H5.
        eauto.
      - apply closure_inject...
        destruct (H0 _ H1) as [? [? _]]...
        congruence.
    Qed.

    Declare Instance closure_proper : forall h, Proper (equiv ==> equiv) (closure _ h).

    Theorem closure_monotonic :
      forall h addrs1 addrs2,
        heap_valid h ->
        subseteq addrs1 addrs2 ->
        subseteq (closure _ h addrs1) (closure _ h addrs2).
    Proof.
      intros.
      pose proof (closure_union h addrs1 (union addrs1 addrs2) H).
      assert (equiv (union addrs1 addrs2) addrs2) by set_solver.
      intros x x_clos1.
      destruct (H1 x) as [_ bw].
      rewrite -> H2 in *.
      rewrite <- H2.
      apply bw.
      set_unfold. left. apply x_clos1.
    Qed.

    Lemma not_dangling_later :
      forall h h' a sv (a0: addr),
        alloc h sv = (a, h') ->
        h !! a0 <> None ->
        h' !! a0 <> None.
    Proof with eauto with heaps.
      intros.
      destruct (decide (a0 = a)); subst...
      intro. apply H0.
      eapply heap_lookup_none_earlier...
    Qed.

    Lemma fresh_not_dangling :
      forall h h' a sv,
        alloc h sv = (a, h') ->
        h' !! a <> None.
    Proof.
      intros. rewrite -> (heap_lookup_finds h h' sv0 a H).
      discriminate.
    Qed.



    Lemma not_dangling_extension {h h' : heap sv }:
      forall a,
        heap_extension h h' ->
        h !! a <> None -> h' !! a <> None.
    Proof with eauto.
      intros. induction H...
      apply IHheap_extension.
      apply (not_dangling_later _ _ _ _ _ H)...
    Qed.

    Lemma found_extension {h h' : heap sv }:
      forall a s,
        heap_extension h h' ->
        h !! a = Some s -> h' !! a = Some s.
    Proof with eauto with heaps.
      intros. induction H...
    Qed.

    Lemma dangling_extension {h h' : heap sv }:
      forall a,
        heap_extension h h' ->
        h' !! a = None -> h !! a = None.
    Proof with eauto with heaps.
      intros. induction H...
      eapply heap_lookup_none_earlier...
    Qed.

    End Heap.

    Global Existing Instance closure_proper.

    Hint Resolve alloc lookup_empty : heaps.
    Hint Resolve heap_lookup_finds heap_lookup_fresh heap_lookup_earlier heap_lookup_earlier' heap_lookup_some_later heap_lookup_none_later heap_lookup_some_earlier heap_lookup_none_earlier : heaps.
    Hint Resolve not_dangling_later fresh_not_dangling : heaps.
    Hint Extern 3 (_ = heap_lookup _ _) => symmetry : heaps.
    Hint Extern 3 (_ = @lookup addr _ (heap _) _ _ _) => symmetry : heaps.
    Hint Extern 5 (_ <> _) => congruence : heaps.

    Global Hint Resolve heap_extension_one heap_ext_refl : heaps.
    Hint Resolve closed_alloc_1 closed_alloc_2 closed_alloc_3 : heaps.
    Hint Resolve closed_empty_iff_empty : heaps.

End HeapParams.
