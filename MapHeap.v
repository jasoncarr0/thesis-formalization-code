Require Import stdpp.base.
Require Import stdpp.sets.
Require Import stdpp.fin_sets.
Require Import stdpp.fin_maps.
Require Import stdpp.listset.
Require Import stdpp.natmap.
Require Import HeapParams.
Require Import Coq.Classes.RelationClasses.
Require Import LocalTactics.
Require Import DecEq.

Module MapHeap : HeapParams.

  Definition addr := nat.
  Definition addrs := listset nat.
  Definition heap sv := list sv.

  Definition addr_decEq : EqDecision addr := _.

  Definition addrs_elem: ElemOf addr addrs := _.
  Definition addrs_singleton: Singleton addr addrs := _.
  Definition addrs_empty: Empty addrs := _.
  Definition addrs_union : Union addrs := _.
  Definition addrs_intersection : Intersection addrs := _.
  Definition addrs_difference : Difference addrs := _.
  Definition addrs_elements : Elements addr addrs := _.
  Definition addrs_finset : FinSet addr addrs := _.
  Definition addrs_elem_dec: forall (a: addr) (aas: addrs), Decision (elem_of a aas) := _.
  Instance heap_empty : forall sv, Empty (heap sv) := fun _ => [].
  (* this is going to cause some problems, but it's not too bad *)
  Instance heap_lookup {sv} : Lookup addr sv (heap sv) :=
    fun addr h => rev h !! addr.
    
  Class AddrIn X := addr_in : X -> addr -> Prop.
  Class Addresses SV `{AddrIn SV} :=
    { addresses : SV -> addrs
    ; addrs_iff : forall a sv,
        elem_of a (addresses sv) <-> addr_in sv a }.
  Section Heap.
    Context {sv: Type}.
    Context `{sv_addr_in: AddrIn sv}.
    Context `{sv_addrs: @Addresses sv sv_addr_in}.

    Definition alloc (h: heap sv) (v: sv) : addr * heap sv := (length h, v :: h).


    Hint Resolve rev_length.
    Hint Rewrite -> rev_length.
    Hint Rewrite -> app_length.
    Hint Resolve Nat.le_refl.

    Ltac doit := autorewrite with core; eauto.
    
    Theorem heap_lookup_finds : forall (h1 h2: heap sv) v (a: addr),
      alloc h1 v = (a, h2) ->
      h2 !! a = Some v.
    Proof with doit.
      intros. unfold lookup, heap_lookup, alloc in *.
      simplify_eq. simpl.
      apply list_lookup_middle...
    Qed.
    Theorem heap_lookup_fresh : forall (h1 h2: heap sv) v (a: addr),
      alloc h1 v = (a, h2) ->
      h1 !! a = None.
    Proof with doit.
      intros. unfold lookup, heap_lookup, alloc in *.
      simplify_eq.
      apply lookup_ge_None_2...
    Qed.
    Theorem heap_lookup_earlier : forall (h1 h2: heap sv) v1 (a1: addr),
      alloc h1 v1 = (a1, h2) ->
      forall (a: addr), (h2 !! a = h1 !! a) \/ a1 = a.
    Proof with doit.
      intros.
      unfold lookup, heap_lookup, alloc in *.
      simplify_eq.
      simpl.
      destruct (Nat.lt_trichotomy a (length h1)) as [? | [?|?]]...
      (* lt *)
      - left. apply lookup_app_l...
      (* gt, both none *)
      - repeat rewrite -> lookup_ge_None_2...
        lia. simpl. lia.
    Qed.
    Theorem heap_lookup_some_later : forall (h1 h2: heap sv) v1 (a1: addr),
      alloc h1 v1 = (a1, h2) ->
      forall (a: addr) v,
        h1 !! a = Some v ->
        h2 !! a = Some v.
    Proof with doit.
      intros.
      unfold lookup, heap_lookup, alloc in *.
      simplify_eq. simpl.
      apply lookup_app_l_Some...
    Qed.

Definition flatMap (f: addr -> addrs) (r: addrs) : addrs
  :=
    union_list (map f (elements r)).

Fixpoint closure0 (f: addr -> addrs)
         (n: nat) (r: addrs): addrs
  :=
    match n with
    | O => r
    | S n => closure0 f n
                     (union r (flatMap f r))
    end.

Lemma closure0_succ :
  forall f r n,
      closure0 f (S n) r = closure0 f n (closure0 f 1 r).
Proof.
  intros. simpl.
  reflexivity.
Qed.

Lemma closure0_one_plus :
  forall f r n,
      closure0 f 1 (closure0 f n r) = closure0 f n (closure0 f 1 r).
Proof.
  intros. generalize dependent r.
  induction n.
  - simpl. reflexivity.
  - intro r.
    rewrite -> (closure0_succ f (closure0 f 1 r) n).
    rewrite <- IHn.
    rewrite <- (closure0_succ f r n).
    reflexivity.
Qed.

Theorem closure0_plus_homomorphism :
  forall f r m n,
    closure0 f m (closure0 f n r) = closure0 f (m + n) r.
Proof.
  intros.
  generalize dependent r.
  generalize dependent n.
  induction m; intros.
  - reflexivity.
  - simpl (S m + n).
    rewrite -> (closure0_succ _ _ m).
    rewrite -> (closure0_succ _ _ (m + n)).
    rewrite <- IHm. f_equal.
    apply closure0_one_plus.
Qed.

Lemma closure0_one_increasing :
  forall f r,
    subseteq r (closure0 f 1 r).
Proof.
  deep_set_unfold.
  left. assumption.
Qed.

Theorem closure0_increasing :
  forall f r n,
    subseteq r (closure0 f n r).
Proof with eauto.
  deep_set_unfold.
  generalize dependent r.
  induction n; intros...
  simpl.
  apply IHn. set_unfold...
Qed.

Lemma in_flat_map :
  forall f r b,
    elem_of b (flatMap f r) -> (exists a, elem_of a r /\ elem_of b (f a)).
Proof with eauto.
  intros.
  unfold flatMap in *.
  rewrite -> elem_of_union_list in H.
  deep_set_unfold.
  exists y...
Qed.

Instance flatMap_unfold {y f xs} : SetUnfoldElemOf y (flatMap f xs) (exists x, elem_of x xs /\ elem_of y (f x)).
Proof with eauto.
  constructor. split; unfold flatMap; simpl in *; deep_set_unfold.
  - rewrite -> elem_of_union_list in H.
    deep_set_unfold.
    exists y0...
  - rewrite -> elem_of_union_list.
    deep_set_unfold.
    exists (f x).
    split...
Qed.

Theorem flatMap_monotonic :
  forall f r1 r2,
    subseteq r1 r2 ->
    subseteq (flatMap f r1) (flatMap f r2).
Proof with eauto.
  deep_set_unfold...
Qed.

Theorem closure0_monotonic :
  forall f r1 r2 n,
    subseteq r1 r2 ->
    subseteq (closure0 f n r1) (closure0 f n r2).
Proof with eauto.
  deep_set_unfold.
  generalize dependent r2.
  generalize dependent r1.
  induction n; intros r1 ? r2 ?...
  (* succ *)
  replace (S n) with (n + 1) in * by lia.
  rewrite <- (closure0_plus_homomorphism f r2 n 1).
  rewrite <- (closure0_plus_homomorphism f r1 n 1) in H0.
  apply IHn with (closure0 f 1 r1)...

  intros.
  deep_set_unfold.
  destruct H1...
  right. deprod.
  exists x1...
Qed.

Instance closure0_Sn {f n r y} : SetUnfoldElemOf y (closure0 f (S n) r)
                                          (exists x: addr, elem_of x (closure0 f n r) /\
                                                     (x = y \/ elem_of y (f x))).
Proof with eauto.
  split. split; intros; deep_set_unfold.
  - generalize dependent r.
    induction n; simpl in *; deep_set_unfold.
    + destruct H... deprod.
      exists x...
    + pose proof (IHn (union r (flatMap f r)) H).
      deprod.
      destruct H1...
  - generalize dependent r.
    induction n; simpl in *; deep_set_unfold...
    destruct H0; subst...
Qed.

Corollary closure0_union :
  forall f r1 r2 n x,
    elem_of x (closure0 f n (union r1 r2)) <->
    elem_of x (closure0 f n r1) \/ elem_of x (closure0 f n r2).
Proof with eauto.
  split; deep_set_unfold.
  - generalize dependent r1.
    generalize dependent r2.
    generalize dependent x.
    induction n; intros; simpl in *; deep_set_unfold...
    (* succ *)
    destruct (IHn _ _ _ H)...
  - generalize dependent r1.
    generalize dependent r2.
    generalize dependent x.
    induction n; intros; simpl in *; deep_set_unfold...
    destruct H; deprod.
    + exists x0...
    + exists x0...
Qed.

Theorem closure0_n_monotonic :
  forall f r m n,
    m <= n ->
    subseteq (closure0 f m r) (closure0 f n r).
Proof with eauto.
  intros.
  assert (n = (n - m) + m) by lia.
  rewrite -> H0 in H |- *.
  clear H0.
  induction (n - m)...
  (* S *)
  transitivity (closure0 f (n0 + m) r)...
  - apply IHn0.
    lia.
  - simpl plus.
    rewrite <- (closure0_plus_homomorphism _ _ 1 (n0 + m)).
    apply closure0_one_increasing.
Qed.

Definition closure `{Addresses sv} (h: heap sv) (r1: addrs): addrs
  :=
    closure0 (fun a =>
                match h !! a with
                | Some sv => filter (fun a => h !! a <> None) (addresses sv)
                | None => empty
                end) (length h)
             (filter (fun a => h !! a <> None) r1).

Theorem closure_inject : forall h a addrs1,
    elem_of a addrs1 ->
    h !! a <> None ->
    elem_of a (closure h addrs1).
Proof with eauto.
  intros. unfold closure.
  apply closure0_increasing.
  set_unfold.
  split...
Qed.

Instance closure0_proper {h n} : Proper (equiv ==> equiv) (closure0 h n).
Proof.
  unfold Proper, respectful, closure.
  induction n; simpl in *; intros.
  - set_unfold. intros.
    repeat rewrite -> elem_of_filter.
    set_solver.
  - apply IHn.
    clear - H. set_unfold. set_solver.
Qed.

Instance closure_proper {h} : Proper (equiv ==> equiv) (closure h).
Proof.
  unfold Proper, respectful, closure.
  intros.
  apply closure0_proper.
  set_solver.
Qed.

Theorem increasing_sequence_stable :
  forall (f: nat -> nat) (k: nat)
    (f_monotonic: forall m n, m <= n -> f m <= f n)
    (f_inertial: forall m n, f (S n) = f n -> f (m + n) = f n)
    (f_bounded: forall n, f n <= k),
    f (S k) = f k.
Proof with eauto.
  intros.

  generalize dependent f.
  induction k; intros.
  - assert ((f 0) <= 0)...
    assert ((f 1) <= 0)...
    lia.
  - pose (fun i => pred (f (S i))) as f'.

    assert (f_0 : forall n, f (S n) = 0 -> f n = 0).
    { intros.
      enough (f n <= 0) by lia.
      rewrite <- H... }
    assert (f_0_stuck : forall m n, f (S n) = 0 -> f (m + n) = 0).
    { intros.
      rewrite -> f_inertial...
      rewrite -> H.
      symmetry... }

    enough (f' (S k) = f' k).
    + unfold f' in H.
      destruct (f (S k)) eqn:fsk.
      { apply (f_0_stuck 2 k)... }
      simpl in H.
      assert (f (S (S k)) >= f (S k))...
      enough (f (S (S k)) <= f (S k)); lia.
    + apply IHk; intros.
      (* monotonic *)
      * unfold f'.
        pose proof (f_monotonic (S m) (S n) (le_n_S _ _ H)).
        lia.
      (* inertial *)
      * unfold f' in *.
        simpl.
        rewrite -> plus_n_Sm.
        rewrite -> (f_inertial m (S n))...
        destruct (f (S n)) eqn:fsn; simpl in H...
        -- apply (f_0_stuck 2 n)...
        -- assert (f (S (S n)) >= f (S n))...
           rewrite <- fsn.
           lia.
      (* bounded *)
      * unfold f'.
        pose proof (f_bounded (S n)).
        lia.
Qed.

Lemma closure0_size_injective_succ : forall r f,
    size (closure0 f 1 r) = size r ->
    equiv (closure0 f 1 r) r.
Proof with eauto.
  intros.
  simpl closure0 in *.
  rewrite -> size_union_alt in H.
  assert ((size (difference (flatMap f r) r)) = 0) by lia.
  apply size_empty_inv in H0.
  assert (subseteq (flatMap f r) r) by set_solver.
  set_solver.
Qed.

Lemma subseteq_size_eq_equiv {A C} `{FinSet A C} : forall (r1 r2: C),
    subseteq r1 r2 ->
    size r1 = size r2 ->
    equiv r1 r2.
Proof with eauto.
  intros.
  pose proof (size_union_alt r1 r2).
  rewrite -> subseteq_union_1 in H9...
  assert (size (r2 ∖ r1) = 0) by lia.
  apply size_empty_inv in H10.
  deep_set_unfold.
  intros; split...
  intros.
  destruct (decide (elem_of x (elements r1))); set_unfold...
  exfalso.
  unfold not in H10.
  apply (H10 x)...
Qed. 

Theorem closure0_size_injective : forall r1 f n1 n2,
    size (closure0 f n1 r1) = size (closure0 f n2 r1) ->
    equiv (closure0 f n1 r1) (closure0 f n2 r1).
Proof with eauto.
  intros r1 f.
  (* wlog n1 <= n2 *)
  refine (let prf := _ in
          fun n1 n2 eqn12 =>
          match Nat.le_ge_cases n1 n2 return closure0 f n1 r1 ≡ closure0 f n2 r1 with
          | or_introl le => prf n1 n2 le eqn12
          | or_intror ge => symmetry (prf n2 n1 ge (eq_sym eqn12))
          end); intros.
  apply subseteq_size_eq_equiv...
  apply closure0_n_monotonic...
Qed.

Lemma closure0_stable : forall r1 f k1 k2,
    (forall n, size (closure0 f n r1) <= k1) ->
    equiv (closure0 f (S (k1 + k2)) r1) (closure0 f (k1 + k2) r1).
Proof with eauto.
  intros.
  apply closure0_size_injective.
  apply (increasing_sequence_stable (fun k => size (closure0 f k r1))).
  (* montonic *)
  - intros. apply subseteq_size.
    apply closure0_n_monotonic...
  (* inertial *)
  - intros.
    apply closure0_size_injective in H0.
    apply set_size_proper.
    induction m...
    rewrite <- (closure0_plus_homomorphism _ _ 1 (m + n)).
    rewrite -> IHm.
    rewrite -> (closure0_plus_homomorphism _ _ 1 n).
    exact H0.
  (* bounded *)
  - intros. pose proof (H n). lia.
Qed.
Print closure.

Theorem closure_descend_inc : forall k (h : heap sv) a1 (addrs1 : addrs) v a2,
    let closure1 k :=
        closure0 (λ a : addr, match h !! a with
                             | Some sv0 => filter (λ a : nat, h !! a ≠ None) (addresses sv0)
                              | None => ∅
                              end) k (filter (λ a : nat, h !! a ≠ None) addrs1)
    in
    elem_of a1 (closure1 k) ->
    heap_lookup a1 h = Some v ->
    addr_in v a2 ->
    heap_lookup a2 h <> None ->
    elem_of a2 (closure1 (S k)).
Proof with eauto.
  intros.
  unfold closure1 in *.
  rewrite -> closure0_succ.
  rewrite <- closure0_one_plus.
  simpl (closure0 _ 1).
  remember (closure0 (λ a : addr, match h !! a with
                             | Some sv0 => filter (λ a : nat, h !! a ≠ None) (addresses sv0)
                             | None => ∅
                                  end) k (filter (λ a : nat, h !! a ≠ None) addrs1)) as addrs1'.
  clear Heqaddrs1'.
  deep_set_unfold.
  right. exists a1.
  split... unfold lookup.
  rewrite -> H0.
  deep_set_unfold.
  split...
  rewrite -> addrs_iff...
Qed.

Definition heap_valid `{AddrIn sv} (h: heap sv) :=
  forall a (sv0: sv),
    h !! a = Some sv0 ->
    forall a',
      addr_in sv0 a' ->
      h !! a' <> None.
(* We need to make P dependent on the element proof to get Coq to figure out how to generalize,
    but in all cases we force P to be proof-irrelevant with it *)

Inductive closure_elem (h: heap sv) (addrs1: addrs) : addr -> Prop :=
| closure_inject0 : forall a,
    elem_of a addrs1 ->
    h !! a <> None ->
    closure_elem h addrs1 a
| closure_descend0 : forall a1 a2 v,
    closure_elem h addrs1 a1 ->
    h !! a1 = Some v ->
    addr_in v a2 ->
    closure_elem h addrs1 a2.


Lemma union_empty :
  forall (r: addrs),
    union r empty = r.
Proof.
  intros. unfold union, listset_union, empty.
  destruct r.
  rename listset_car into r.
  pose proof (listset_empty_alt (A:= addr) listset_empty).
  destruct H as [H _].
  destruct listset_empty eqn:eq.
  simpl in H.
  rewrite -> H in *.
  - rewrite -> app_nil_r. reflexivity.
  - rewrite <- eq. reflexivity.
  - rewrite <- eq. reflexivity.
Qed.

Lemma closure0_ind : forall (x: addr) (k: nat) {f: addr -> addrs} {r: addrs} (P : forall (a: addr) (r: addrs), elem_of a r -> Prop),
    forall
      (P_start: forall x (el: elem_of x r), P x r el)
      (P_next: forall x r el, P x r el -> forall y (el: elem_of y (f x)), P y (f x) el)
      (P_unions: forall x r1 rs el, P x r1 el -> elem_of r1 rs -> forall el_union, P x (union_list rs) el_union)
      (P_union_l: forall x r1 r2 el1, P x r1 el1 -> forall el_union, P x (union r1 r2) el_union)
      (P_union_r: forall x r1 r2 el2, P x r2 el2 -> forall el_union, P x (union r1 r2) el_union),
    forall (el: elem_of x (closure0 f k r)), P x (closure0 f k r) el.
Proof with auto.
  intros.
  generalize dependent x.
  generalize dependent r.
  induction k...
  intros.
  pose proof (closure0_succ f r k).
  symmetry in H.
  destruct H.

  apply IHk...
  intros.
  simpl closure0 in *.

  assert (forall el, P x empty el).
  { intros. exfalso. set_solver. }
  
  remember el0 as el0'.
  clear Heqel0'.
  rewrite -> elem_of_union in el0.
  destruct el0.
  - apply P_union_l with H0...
  - apply P_union_r with H0.
    unfold flatMap in H0.
    assert (exists X, elem_of X (elements r) /\ elem_of x0 (f X)).
    { clear - H0. rewrite -> elem_of_union_list in H0.
      set_solver. }
    deprod.
    apply P_unions with (f X) H2...
    + assert (elem_of X r) by set_solver.
      apply P_next with r H3...
    + clear - H1.
      set_solver.
Qed.

Lemma closure_subset : forall h addrs1,
    heap_valid h ->
    forall a, elem_of a (closure h addrs1) ->
              h !! a <> None.
Proof with eauto.
  intros.
  unfold heap_valid in H.
  unfold closure in H0.
  induction H0 using (closure0_ind a (length h))...
  - set_solver.
  - forced (h !! x) by set_solver.
    deep_set_unfold.
Qed.

Lemma member_lt_len : forall (a: addr) (h: heap sv),
    h !! a <> None ->
    a < length h.
Proof.
  unfold lookup, heap_lookup.
  intros.
  rewrite <- rev_length.
  apply lookup_lt_is_Some.
  destruct (rev h !! a) eqn:eq; eauto || congruence.
Qed.
  

Definition addrs_in_heap (h: heap sv) : addrs := set_seq 0 (length h).

Lemma size_addrs_in_heap :
  forall h, size (addrs_in_heap h) = length h.
Proof with eauto.
  intros.
  unfold addrs_in_heap in *.
  generalize 0.
  induction (length h)...
  set_unfold. intros.
  rewrite -> size_union.
  rewrite <- (IHn (S x)) at 2.
  rewrite -> size_singleton. lia.
  apply set_seq_S_start_disjoint.
Qed.

Theorem closure_descend : forall h a1 addrs1 v a2,
    elem_of a1 (closure h addrs1) ->
    h !! a1 = Some v ->
    addr_in v a2 ->
    h !! a2 <> None ->
    elem_of a2 (closure h addrs1).
Proof with doit.
  intros.
  unfold closure in *.
  replace (length h) with (length h + 0) in * by lia.
  rewrite <- closure0_stable...
  - apply (closure_descend_inc _ _ a1 _ v)...
  - clear - H. intros.
    enough (subseteq (closure0 (λ a : addr, match h !! a with
                              | Some sv0 => filter (λ a0 : nat, h !! a0 ≠ None) (addresses sv0)
                              | None => ∅
                              end) n (filter (λ a : nat, h !! a ≠ None) addrs1)) (addrs_in_heap h)).
    + rewrite <- size_addrs_in_heap.
      apply subseteq_size...
    + set_unfold.
      intros.
      enough (x < length h) by lia.
      apply member_lt_len...
      induction H0 using (closure0_ind x n)...
      * deep_set_unfold.
      * forced (h !! x0) by set_solver.
        deep_set_unfold.
Qed.

Lemma elem_elem_1 :
  forall h addrs1 a,
    heap_valid h ->
    closure_elem h addrs1 a -> elem_of a (closure h addrs1).
Proof with eauto.
  intros.
  induction H0.
  - apply closure_inject...
  - apply closure_descend with a1 v...
Qed.
Hint Resolve elem_elem_1.

Lemma elem_elem_2 :
  forall h addrs1 a,
    heap_valid h ->
    elem_of a (closure h addrs1) -> closure_elem h addrs1 a.
Proof with eauto.
  unfold closure.
  intros.
  generalize dependent addrs1.
  generalize dependent a.
  induction (length h); intros; simpl in H0.
  (* -> 0 *)
  - apply closure_inject0; set_solver.
  - setoid_replace
      (filter (λ a : nat, h !! a ≠ None) addrs1
          ∪ flatMap (λ a : addr, match h !! a with
                                | Some sv0 => filter (λ a0 : nat, h !! a0 ≠ None) (addresses sv0)
                                | None => ∅
                                end) (filter (λ a : nat, h !! a ≠ None) addrs1))
      with
        (filter (λ a : nat, h !! a ≠ None) (addrs1
          ∪ flatMap (λ a : addr, match h !! a with
                                | Some sv0 => filter (λ a0 : nat, h !! a0 ≠ None) (addresses sv0)
                                | None => ∅
                                end) addrs1)) in H0.
      + apply IHn in H0.
        induction H0; set_unfold.
        * destruct H0; deprod.
          -- apply closure_inject0...
          -- destruct (h !! x) eqn:lkpx; try solve [exfalso; set_solver].
             eapply closure_descend0 with x s...
             ++ apply closure_inject0...
                intro. simplify_eq.
             ++ deep_set_unfold. rewrite <- addrs_iff...
        * apply closure_descend0 with a1 v...
      + unfold heap_valid in H.
        clear - H. deep_set_unfold; split; deep_set_unfold.
        * destruct H0; deprod...
          split...
          unfold lookup in H0, H1.
          destruct (heap_lookup x0 h) eqn:lkp; try contradiction.
          apply H with x0 s...
          deep_set_unfold.
          rewrite <- addrs_iff...
        * destruct H1; deprod...
          right. exists x0.
          repeat split_and...
          destruct (h !! x0) eqn:lkpx0.
          -- deep_set_unfold.
             rewrite -> addrs_iff in H4.
             unfold lookup in *.
             simplify_eq.
          -- set_solver.
Qed.

Theorem closure_ind :
  forall {h: heap sv} (valid: heap_valid h) {addrs1: addrs},
  forall (P: forall (a: addr), elem_of a (closure h addrs1) -> Prop)
    (P_inject: forall a, elem_of a addrs1 -> h !! a <> None -> forall el, P a el)
    (P_descend: forall a v el, P a el -> h !! a = Some v -> forall a2 el2, addr_in v a2 -> P a2 el2),
    forall a (el: elem_of a (closure h addrs1)), P a el.
Proof with eauto.
  intros.

  assert (el' : closure_elem h addrs1 a) by (apply elem_elem_2; assumption). 

  induction el'.
  - apply P_inject...
  - apply elem_elem_1 in el'.
    pose proof (IHel' el'). 
    eapply P_descend...
    exact valid.
Qed.


(*

Proofs that are already done in the other file that I apparently need to reproduce...

Really didn't expect this out of the functor system

*)

    Lemma heap_lookup_earlier' : forall (h1 h2: heap sv) v1 (a1: addr),
      alloc h1 v1 = (a1, h2) ->
      forall (a: addr),
        a <> a1 ->
        (h2 !! a = h1 !! a).
    Proof.
      intros.
      destruct (heap_lookup_earlier h1 h2 v1 a1 H a); done.
    Qed.
    Lemma lookup_empty : forall (i: addr), (empty: heap sv) !! i = None.
    Proof.
      intros. unfold empty, heap_empty, lookup, heap_lookup, lookup.
      reflexivity.
    Qed.



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


    Theorem closure_empty :
      forall h,
        heap_valid h ->
        equiv (closure h empty) empty.
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
        equiv (closure h (union addrs1 addrs2))
              (union (closure h addrs1)
                     (closure h addrs2)).
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
          elem_of a (closure h s) ->
          h !! a <> None.
    Proof with eauto.
      intros.
      induction a, H0 using (closure_ind H)...
    Qed.
        
    Theorem closure_closed :
      forall h s,
        heap_valid h ->
        closed h (closure h s).
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
        equiv (closure h s) s.
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
        intro.
        unfold lookup in H2, H3.
        congruence.
    Qed.

    Theorem closure_monotonic :
      forall h addrs1 addrs2,
        heap_valid h ->
        subseteq addrs1 addrs2 ->
        subseteq (closure h addrs1) (closure h addrs2).
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


End MapHeap.
