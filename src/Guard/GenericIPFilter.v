Require Import
    Fiat.Narcissus.Examples.NetworkStack.IPv4Header
    Fiat.Narcissus.Examples.NetworkStack.TCP_Packet
    Bedrock.Word
    Coq.Arith.Arith
    Coq.Lists.List
    Fiat.QueryStructure.Automation.MasterPlan
    IndexedEnsembles
    Fiat.Narcissus.Examples.Guard.Core
    Fiat.Narcissus.Examples.Guard.IPTables
    Fiat.Narcissus.Examples.Guard.PacketFiltersLemmas
    Fiat.Narcissus.Examples.Guard.DropFields
    Coq.Sets.Ensembles.
Import ListNotations.

(* TODO: Add a proper makefile target *)
(* TODO: Fork this file into one that only does column reductions *)

Definition StatefulFilterSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : rep,
      Method "Filter" : rep * input -> rep * (option result)
    }.


(**
we are 18.X.X.X
outside world is all other IP addresses
filter allows outside address to talk to us only if we have talked to it first
**)

Definition OutgoingRule :=
  iptables -A FORWARD --source 18'0'0'0/24.

Definition IncomingRule :=
  iptables -A FORWARD --destination 18'0'0'0/24.

Definition OutgoingToRule (dst: address) :=
  and_cf OutgoingRule (lift_condition in_ip4 (cond_dstaddr {| saddr := dst; smask := None |})).

Definition OutgoingToRule' (cur pre : input) : Prop :=
  (OutgoingToRule cur.(in_ip4).(ipv4_source)).(cf_cond) pre = true.

Lemma OutgoingToImpliesOutgoing:
  forall inp dst,
    (OutgoingToRule dst).(cf_cond) inp -> OutgoingRule.(cf_cond) inp.
Proof.
  intros. simpl in *. unfold combine_conditions in *. apply andb_prop in H. destruct H. rewrite H. constructor. Qed.

Opaque OutgoingRule.
Opaque IncomingRule.
Opaque OutgoingToRule.

Definition FilterMethod {h} (topkt: @Tuple h -> input)
           (totup: input -> @Tuple h)
           (r: QueryStructure (PacketHistorySchema h)) (inp: input) :=
  If OutgoingRule.(cf_cond) inp
  Then <ACCEPT>
  Else (
      If negb (IncomingRule.(cf_cond) inp)
      Then ret None
      Else with r (In_History_Constr totup),
        if historically (OutgoingToRule' inp) then <ACCEPT> else <DROP>).

Definition FilterMethod_UnConstr {h} (topkt: @Tuple h -> input)
           (totup: input -> @Tuple h)
           (r: UnConstrQueryStructure (PacketHistorySchema h)) (inp: input) :=
  If OutgoingRule.(cf_cond) inp
  Then <ACCEPT>
  Else (
      If negb (IncomingRule.(cf_cond) inp)
      Then ret None
      Else with r (In_History totup),
        if historically (OutgoingToRule' inp) then <ACCEPT> else <DROP>).

Lemma UnConstrPreservesFilterMethod: forall h topkt totup r_o r_n inp res,
  DropQSConstraints_AbsR r_o r_n ->
  computes_to (@FilterMethod h topkt totup r_o inp) res <->
  computes_to (FilterMethod_UnConstr topkt totup r_n inp) res.
Proof. (* TODO: Either generalize or start at Unconstr level *)
  intros. unfold FilterMethod, FilterMethod_UnConstr in *.
  destruct (OutgoingRule.(cf_cond) inp) eqn:out. reflexivity.
  destruct (negb (IncomingRule.(cf_cond) inp)) eqn:inc. reflexivity.
  split; intros; apply Bind_inv in H0; destruct H0 as [b [Hbin Hbres]];
    unfold DropQSConstraints_AbsR in H; rewrite <- H in *;
    computes_to_econstructor; unfold In_History, In_History_Constr;
    [ change (GetUnConstrRelationBnd (DropQSConstraints r_o) ``"History")
        with (GetUnConstrRelation (DropQSConstraints r_o) Fin.F1);
      rewrite GetRelDropConstraints; apply Hbin
    | apply Hbres
    |  change (GetRelationBnd r_o ``"History")
        with (GetRelation r_o Fin.F1);
      rewrite <- GetRelDropConstraints; apply Hbin
    | apply Hbres].
Qed.

Definition NoIncomingConnectionsFilter : ADT StatefulFilterSig :=
  Eval simpl in Def ADT {
    rep := QueryStructure Complete_PacketHistorySchema,
    Def Constructor0 "Init" : rep := empty,,

    Def Method1 "Filter" (r: rep) (inp: input) : rep * option result :=
      res <- FilterMethod Complete_topkt Complete_totup r inp;
      `(r, _) <- Insert (Complete_totup inp) into r!"History";
      ret (r, res)
  }%methDefParsing.

Lemma simpl_in_bind:
  forall (T U: Type) (x v : T) (y: U),
    In T (`(r', _) <- ret (x, y); ret r') v -> x = v.
Proof.
  intros. apply Bind_inv in H. destruct H. destruct H. apply Return_inv in H. rewrite <- H in H0. simpl in H0. apply Return_inv in H0. assumption. Qed.


Definition LessHistoryRelation {h} totup
           (r_o r_n : UnConstrQueryStructure (PacketHistorySchema h)) :=
  FiniteTables_AbsR r_o r_o /\   (* TODO *)
  forall inp,
    (OutgoingRule.(cf_cond) inp) ->
    (In_History totup r_n inp <-> In_History totup r_o inp).


Lemma LessHistoryPreservesFilter:
  forall inp h totup topkt r_o r_n,
    LessHistoryRelation totup r_o r_n ->
    refine
      (@FilterMethod_UnConstr h topkt totup r_o inp)
      (FilterMethod_UnConstr topkt totup r_n inp).
Proof.
  red; intros. unfold FilterMethod_UnConstr in *.
  unfold LessHistoryRelation in H. destruct H as [Hfin H].
  destruct (cf_cond OutgoingRule inp) eqn:outrule;
    destruct (negb (cf_cond IncomingRule inp)) eqn:ninrule;
    simpl in *; try apply H0.
  inversion H0. destruct H1. computes_to_econstructor.
  destruct x eqn:truefalse.

  - instantiate (1 := x).
    computes_to_econstructor. unfold decides; simpl.
    destruct H1. destruct H1. exists x0. split.
    * apply (H x0).
      apply (OutgoingToImpliesOutgoing x0 (ipv4_source (in_ip4 inp))).
      assumption. assumption.
    * assumption.

  - computes_to_econstructor; unfold decides; simpl.
    unfold not; intros. destruct H1. destruct H3. destruct H1.
    exists x0. split.
    * apply (H x0).
      apply (OutgoingToImpliesOutgoing x0 (ipv4_source (in_ip4 inp))).
      assumption. assumption.
    * assumption.

  - assumption.
Qed.

Notation IndexType sch :=
  (@ilist3 RawSchema (fun sch : RawSchema =>
                        list (string * Attributes (rawSchemaHeading sch)))
           (numRawQSschemaSchemas sch) (qschemaSchemas sch)).

(* This computes the set of columns to keep *)
Theorem DroppedFilterMethod : FilterAdapter (@FilterMethod_UnConstr).
Proof. solve_drop_fields. Defined.

Definition IPFilterSchema :=
  Eval cbn in PacketHistorySchema (DroppedFilterMethod.(h _)).

(** Genpatcher hooks here **)

(* ???columns??? is the list of columns available; this will vary depending on the filter *)

Definition columns :=
  Eval compute in (Vector.to_list (DroppedFilterMethod.(h _).(HeadingNames))).

Print columns.
(* columns = ["Chain"; "TransportLayerPacket"; "DestAddress"; "SourceAddress"]%list
     : list string *)

Open Scope list_scope.

(* Here are two examples *)

Definition SlowIndex : IndexType IPFilterSchema :=
  {| prim_fst := [];
     prim_snd := () |}.

Definition FastIndex :=
  {| prim_fst := [("EqualityIndex", "DestAddress" # "History" ## IPFilterSchema)]%list;
     prim_snd := () |}.

(* Genpatcher should mutate the following definition: *)
Definition Index : IndexType IPFilterSchema :=
  {| prim_fst := [];
     prim_snd := () |}.

(** End of GenPatcher hooks **)

Notation "( x 'in' r '%' Ridx ) bod" :=
  (let qs_schema : QueryStructureSchema := _ in
   let r' : UnConstrQueryStructure qs_schema := r in
   let Ridx' := ibound (indexb (@Build_BoundedIndex _ _ (QSschemaNames qs_schema) Ridx%string _)) in
   @UnConstrQuery_In _ qs_schema r' Ridx'
            (fun x : @RawTuple (GetNRelSchemaHeading (qschemaSchemas qs_schema) Ridx') => bod)) (at level 0, x at level 200, r at level 0, bod at level 0).

Definition FilterMethod_UnConstr_Comp {h} (topkt: @Tuple h -> input)
           (totup: input -> @Tuple h)
           (r: UnConstrQueryStructure (PacketHistorySchema h)) (inp: input) :=
  If cf_cond OutgoingRule inp Then <ACCEPT> Else
  If negb (cf_cond IncomingRule inp) Then ret None Else
    (c <- Count (For (t in r%"History")
                 Where (cf_cond (OutgoingToRule (ipv4_source (in_ip4 inp))) (topkt t) = true)
                 Return ());
     If 0 <? c Then <ACCEPT> Else <DROP>).


Lemma permutation_length {A: Type}:
  forall (l1 l2 : list A),
    Permutation l1 l2 -> Datatypes.length l1 = Datatypes.length l2.
Proof.
  intros. induction H; simpl; congruence.
Qed.

Open Scope list.
Lemma fold_comp_list_in:
  forall (T: Type) (P: T -> bool) (ltup: list T) l inp,
    fold_right
      (fun b a : Comp (list ()) =>
         l <- b;
         l' <- a;
         ret (l ++ l')%list) (ret [])
      (map
         (fun t : T =>
            {l : list () |
             (P t -> ret [()] ??? l) /\ (~ P t -> l = [])}) ltup) l ->
    List.In inp ltup ->
    P inp ->
    0 <? Datatypes.length l.
Proof.
  intros T P. induction ltup.
  - intros; auto.
  - intros l inp Hf Hin Hp. cbn in Hf.  destruct Hf as [x [Hx [y [Hy Happ]]]].
    unfold In in *. inversion Happ. destruct Hin as [Hin | Hin].
    * subst inp. inversion Hx. apply H0 in Hp. inversion Hp. auto.
    * pose proof (IHltup y inp Hy Hin Hp) as Hind. rewrite app_length.
      apply Nat.ltb_lt; apply Nat.lt_lt_add_l; apply Nat.ltb_lt; assumption.
Qed.

Lemma fold_comp_list_length:
  forall l l',
    fold_right
      (fun b a : Comp (list ()) =>
         l <- b;
         l' <- a;
         ret (l ++ l')%list) (ret [])
      l' l ->
    0 <? Datatypes.length l ->
    exists lin, List.In lin l' /\
                (exists lin', lin lin' /\ 0 <? Datatypes.length lin').
Proof.
  intros l l'. generalize dependent l. induction l'.
  - simpl. intros. inversion H. subst l. inversion H0.
  - simpl. intros. destruct H as [l1 [Hl1 Hl]]. red in Hl1. red in Hl.
    destruct Hl as [l2 [Hl2 Hl]]. red in Hl2. red in Hl. inversion Hl.
    destruct (0 <? Datatypes.length l2) eqn:Hlen2.
    * pose proof (IHl' l2 Hl2 Hlen2) as IH.
      destruct IH as [lin [Hlin1 Hlin2]]. exists lin. split.
      right; assumption. assumption.
    * apply Nat.ltb_ge in Hlen2. inversion Hlen2. rewrite <- H in H0.
      rewrite app_length in H0. rewrite H2 in H0. rewrite Nat.add_0_r in H0.
      exists a. split.
      left; reflexivity. exists l1. split. assumption. rewrite H2. apply H0.
Qed.
Close Scope list.

Lemma count_zero_iff:
  forall h (topkt: @Tuple h -> input) totup
    (r: UnConstrQueryStructure (PacketHistorySchema h))
    (P: input -> bool) count,
    (forall t, totup (topkt t) = t) ->
    (forall inp, P inp = P (topkt (totup inp))) ->
    computes_to (Count (For (UnConstrQuery_In r Fin.F1
                        (fun t =>
                          Where (P (topkt t))
                          Return ())))) count ->
    ((0 <? count) <-> (exists inp, In_History totup r inp /\ P inp)).
(*IndexedEnsemble_In (GetUnConstrRelation r Fin.F1) inp /\ P (topkt inp))).*)
Proof.
  Transparent Query_For. Transparent Count. Transparent QueryResultComp.
  unfold Count, Query_For, Query_Where, Query_Return, UnConstrQuery_In.
  unfold QueryResultComp, FlattenCompList.flatten_CompList.
  intros h topkt totup r P count toinv Ptoinv Hcount.
  destruct Hcount as [l [Hcount Htmp]].
  unfold In in *. inversion Htmp. rename H into Hlen. clear Htmp.
  destruct Hcount as [l' [Htmp Hperm]]. apply Pick_inv in Hperm.
  unfold In in *. destruct Htmp as [ltup [Hrel Hfold]].
  apply Pick_inv in Hrel. unfold In in *.
  pose proof (permutation_length l' l Hperm) as Hpermlen.
  rewrite <- Hpermlen in *. clear Hperm. clear Hpermlen. clear l.
  split; intros H.
  - pose proof (fold_comp_list_length l' _ Hfold H) as Hlin0.
    destruct Hlin0 as [lin [Hlinm [lin' [Hll Hlinc]]]].
    apply in_map_iff in Hlinm. destruct Hlinm as [x [Hpx Hlx]].
    exists (topkt x). split.
    * red in Hrel. destruct Hrel as [l [Hmap [Heql Hdup]]].
      red. rewrite <- Hmap in Hlx.
      apply in_map_iff in Hlx.
      destruct Hlx as [y [Hy1 Hy2]]. destruct y as [yidx yelem].
      exists yidx. simpl in Hy1. subst x. apply Heql. rewrite toinv. apply Hy2.
    * subst lin. inversion Hll.
      destruct (P (topkt x)) eqn:Hpx. reflexivity.
      assert (Hle: lin' = []%list) by (apply H1; congruence). subst lin'.
      inversion Hlinc.

  - red in Hrel. destruct Hrel as [l [Hmap [Heql Hdup]]].
    destruct H as [inp [Hinp Hpinp]]. red in Hinp. destruct Hinp as [idx Hinp].
    apply Heql in Hinp.
    assert (Hinp': List.In (totup inp) ltup).
    { rewrite <- Hmap. apply in_map_iff.
      exists {| elementIndex := idx; indexedElement := (totup inp) |}.
      split. reflexivity. assumption. }
    pose (fun t => P (topkt t)) as P'. rewrite Ptoinv in Hpinp.
    apply (fold_comp_list_in _ P' ltup l' _ Hfold Hinp' Hpinp).
Qed.

Lemma LessHistoryRelationRefl:
  forall h (totup: input -> @Tuple h) r_o,
    FiniteTables_AbsR r_o r_o -> LessHistoryRelation totup r_o r_o.
Proof.
  unfold LessHistoryRelation; split. assumption.
  split; intros; assumption. Qed.


Lemma QSEmptyFinite {qs_schema}:
  forall idx, FiniteEnsemble (GetUnConstrRelation (DropQSConstraints (QSEmptySpec qs_schema)) idx).
Proof.
  intros. red. exists []%list. red. exists []%list.
  split.
  - reflexivity.
  - split.
    * split; intros.
      + cbn in H. red in H. red in H.
        change (Vector.map schemaRaw (QSschemaSchemas qs_schema))
          with (qschemaSchemas qs_schema) in H. rewrite <- ith_imap2 in H.
        remember (ith2 _ _) in *.
        change (numQSschemaSchemas qs_schema)
          with (numRawQSschemaSchemas (QueryStructureSchemaRaw qs_schema)) in Heqy.
        change (fun x => ?f x) with f in Heqy.

        rewrite (Build_EmptyRelation_IsEmpty qs_schema idx) in Heqy.
        subst y. cbn in H. inversion H.
      + inversion H.
    * constructor.
Qed.

Definition incrMaxFreshIdx {T: Type} (l: list (@IndexedElement T)) :=
  S (fold_right (fun elem acc => max (elementIndex elem) acc) 0 l).

Print UnIndexedEnsembleListEquivalence. Print FiniteEnsemble.
Lemma incrMaxFreshIdx_computes:
  forall {qs_schema} {qidx: Fin.t (numRawQSschemaSchemas qs_schema)}
         (r: UnConstrQueryStructure qs_schema) l l',
    map indexedElement l' = l /\
    (forall x : IndexedElement,
    In IndexedElement (GetUnConstrRelation r qidx) x <-> List.In x l') /\
    NoDup (map elementIndex l') ->
    computes_to
      {idx: nat | UnConstrFreshIdx (GetUnConstrRelation r qidx) idx}
      (incrMaxFreshIdx l').
Proof.
  intros qsc qidx r l l' [Hmap [Heqv Hdup]]. computes_to_econstructor.
  red; intros elem Helem. apply Heqv in Helem.
  unfold lt. apply le_n_S. apply fold_right_max_is_max. apply Helem. Qed.

Lemma list_helper:
  forall {T: Type} (l: list T) (f: T -> nat) (big: nat),
    lt (fold_right (fun e acc => max (f e) acc) 0 l) big ->
    ~ List.In big (map f l).
Proof.
  induction l.
  - auto.
  - unfold not; intros f big Hbig H. cbn in Hbig. cbn in H.
    pose proof
         (Nat.max_spec (f a)
                       (fold_right (fun (e : T) (acc : nat) =>
                                      Init.Nat.max (f e) acc) 0 l)) as Hmax.
    destruct Hmax as [[Hlt Hmax] | [Hlt Hmax]]; rewrite Hmax in Hbig;
      destruct H as [H | H].
    + subst big. pose proof (lt_trans _ _ _ Hlt Hbig).
      apply lt_irrefl in H. auto.
    + apply (IHl f big Hbig H).
    + subst big. apply lt_irrefl in Hbig. auto.
    + pose proof (le_lt_trans _ _ _ Hlt Hbig). apply (IHl f big H0 H).
Qed.


Lemma CompPreservesFilterMethod:
  forall topkt totup r inp,
    topkt = (DropFields.topkt _ DroppedFilterMethod) ->
    totup = (DropFields.totup _ DroppedFilterMethod) ->
    refine (FilterMethod_UnConstr topkt totup r inp)
           (FilterMethod_UnConstr_Comp topkt totup r inp).
Proof.
  unfold FilterMethod_UnConstr, FilterMethod_UnConstr_Comp.
  red; intros topkt totup r inp Hp Ht v H;
    cbn in Hp, Ht; rewrite Hp, Ht in *.
  destruct (cf_cond OutgoingRule inp) eqn:outrule. assumption.
  destruct (negb (cf_cond IncomingRule inp)) eqn:inrule. assumption.
  inversion H as [c Hc]. destruct Hc as [Hcount Hres]. unfold In in *.

  epose proof (count_zero_iff _ _ _ _ _ c _ _ Hcount) as Hcziff.
  computes_to_econstructor. computes_to_econstructor.
  instantiate (1:=(0 <? c)). red. destruct (0 <? c) eqn:Hzero; simpl.
  - rewrite <- Hzero in Hcziff. apply Hcziff in Hzero.
    destruct Hzero as [pre [Hin Hcond]]. exists pre.
    split; [ apply Hin | apply Hcond ].
  - intro.
    rewrite <- Hzero in Hcziff. apply Hcziff in H0. congruence.
  - apply Hres.

    Unshelve.
    * intros. repeat (let i := fresh in destruct t as [i t]). reflexivity.
    * reflexivity.
Qed.

Definition myqidx (h: Heading) : Fin.t (numRawQSschemaSchemas (PacketHistorySchema h)).
apply Fin.F1. Defined.
Definition RefinedInsert h totup r d :=
  If cf_cond OutgoingRule d
  Then
    (idx <- {idx: nat |
             UnConstrFreshIdx (r!"History")%QueryImpl idx};
     ret (UpdateUnConstrRelation r (myqidx h)
            (BuildADT.EnsembleInsert
               {| elementIndex := idx;
                  indexedElement := totup d |}
               (r!"History")%QueryImpl)))
  Else
    ret r.

Lemma freshidxtemp:
  forall h r_o (r_n: UnConstrQueryStructure (PacketHistorySchema h)) totup,
    Complete_Dropped_qs_equiv totup r_o r_n ->
    refine
      {idx: nat | UnConstrFreshIdx (GetUnConstrRelation r_o Fin.F1) idx}
      {idx: nat | UnConstrFreshIdx (GetUnConstrRelation r_n Fin.F1) idx}.
Proof.
  intros h r_o r_n totup H. red in H. intro v; intros Hv; comp_inv.
  red in Hv. computes_to_econstructor. red; intros [idx [inp tmp]] Hinp.
  cbn in inp; destruct tmp. apply (H inp idx) in Hinp. apply Hv in Hinp.
  cbn in *. assumption.
Qed.

Ltac FindAttributeUses := EqExpressionAttributeCounter.
Ltac BuildEarlyIndex := ltac:(LastCombineCase6 BuildEarlyEqualityIndex).
Ltac BuildLastIndex := ltac:(LastCombineCase5 BuildLastEqualityIndex).
Ltac IndexUse := EqIndexUse.
Ltac createEarlyTerm := createEarlyEqualityTerm.
Ltac createLastTerm := createLastEqualityTerm.
Ltac IndexUse_dep := EqIndexUse_dep.
Ltac createEarlyTerm_dep := createEarlyEqualityTerm_dep.
Ltac createLastTerm_dep := createLastEqualityTerm_dep.
Ltac BuildEarlyBag := BuildEarlyEqualityBag.
Ltac BuildLastBag := BuildLastEqualityBag.
Ltac PickIndex := ltac:(fun makeIndex => let attrlist' := eval compute in Index in makeIndex attrlist').

Theorem SharpenNoIncomingFilter:
  FullySharpened NoIncomingConnectionsFilter.
Proof.
  start sharpening ADT. Transparent QSInsert.

  pose (h _ DroppedFilterMethod) as h. compute in h.
  pose (topkt _ DroppedFilterMethod) as topkt. cbn -[GetAttribute] in topkt.
  pose (totup _ DroppedFilterMethod) as totup. simpl in totup.
  pose (thm _ DroppedFilterMethod) as Hdrop. simpl in Hdrop.

  drop_constraints_under_bind Complete_PacketHistorySchema ltac:(
    intro v; intros Htemp;
    match goal with
      [H: DropQSConstraints_AbsR _ _ |- _] =>
      apply (UnConstrPreservesFilterMethod _ Complete_topkt Complete_totup
                                           _ _ _ _ H)
    end;
    apply Htemp).

  (* hone_finite_under_bind PacketHistorySchema myqidx. *)
  hone representation using (Complete_Dropped_qs_equiv totup).
  - simplify with monad laws.
    refine pick val (DropQSConstraints (QSEmptySpec _)).
    subst H; reflexivity. red. intros.
    split; intros Htmp; cbv in Htmp; inversion Htmp.
  - etransitivity. simplify with monad laws.
    apply refine_bind. apply Hdrop. apply H0.
    intro. cbn.

    eapply refine_bind. apply (freshidxtemp _ _ _ totup H0).
    intro idx.

    Definition tmpinsert h (totup: input -> @Tuple h)
               (r_n: UnConstrQueryStructure (PacketHistorySchema h))
               d (a: option result) idx :=
      ret (UpdateUnConstrRelation r_n Fin.F1
             (BuildADT.EnsembleInsert
                {| elementIndex := idx;
                   indexedElement := totup d |}
                (GetUnConstrRelation r_n Fin.F1)), a).

    Lemma refine_pair: forall (T U: Type) (x: T) (y: U) (c: Comp T),
      refine c (ret x) ->
      refine
        (x' <- c;
         ret (x', y))
        (ret (x, y)).
    Proof.
      intros. intro; intros. comp_inv. computes_to_econstructor.
      red in H. apply H. auto. auto. Qed.

    apply refine_pair. apply refine_pick. intros qs Hins. comp_inv.
    subst qs.
    instantiate (1 := (UpdateUnConstrRelation r_n Fin.F1
                         (BuildADT.EnsembleInsert
                            {| elementIndex := idx;
                               indexedElement := totup d |}
                            (GetUnConstrRelation r_n Fin.F1)))).
    red; intros oinp oidx; split; intros Hoinp;
      destruct Hoinp as [Hoinp | Hoinp].

    apply in_ensemble_insert_iff.
    left; inversion Hoinp; reflexivity.
    right; apply H0 in Hoinp; apply Hoinp.

    exists d. split. apply in_ensemble_insert_iff.
    left; inversion Hoinp; reflexivity.
    unfold totup; inversion Hoinp; reflexivity.

    pose proof (H0 oinp oidx). destruct H1 as [_ H1]. specialize (H1 Hoinp).
    destruct H1 as [inp' [H1 H2]]. exists inp'. split. apply in_ensemble_insert_iff.
    right. apply H1. apply H2.

    finish honing.



 - hone representation using (LessHistoryRelation totup);
    try simplify with monad laws.
   * refine pick val (DropQSConstraints (QSEmptySpec _));
       subst H; [reflexivity | apply LessHistoryRelationRefl].
     red; split; [reflexivity | apply QSEmptyFinite].
    
   * simpl. etransitivity. 2: (subst H; higher_order_reflexivity).
     apply refine_bind.
     apply (LessHistoryPreservesFilter d _ _ _ r_o r_n H0).

     red; intros;
      instantiate (1:=(fun a => r <- RefinedInsert _ totup r_n d; ret (r, a)));
      cbv beta; unfold RefinedInsert; unfold If_Then_Else;
      destruct (cf_cond OutgoingRule d) eqn:out; red; intros;
      repeat comp_inv;
      [ rename x0 into idx; rename H1 into Hidx;
        rename v into r; rename H4 into Hr; rename H3 into Hret
      | subst
      ];
      unfold LessHistoryRelation in H0; destruct H0 as [Hfin Hles];
      destruct Hfin as [HH Hfin]; unfold FiniteEnsemble in Hfin;
      pose proof Hfin as Hfinorig; specialize Hfin with Fin.F1;
      destruct Hfin as [lfin [lfin' Hlfin]].
      
    1-4: computes_to_econstructor;
      try apply (incrMaxFreshIdx_computes r_o lfin lfin' Hlfin);
      computes_to_econstructor; try reflexivity;
      computes_to_econstructor;
      red; split.

    all: repeat match goal with
      | [ |- FiniteTables_AbsR _ _ ] =>
        red; split; try reflexivity;
        intros finidx; destruct (Fin.eqb finidx (myqidx h)) eqn:Hfeq

      | [Hfeq: Fin.eqb _ _ = false |- _] =>
        rewrite get_update_unconstr_neq;
        [ specialize Hfinorig with finidx; red; assumption
        | intro; subst finidx; compute in Hfeq; inversion Hfeq ]

      | [ |- FiniteEnsemble _ ] =>
        red; apply Fin.eqb_eq in Hfeq; rewrite Hfeq;
        exists ((totup d) :: lfin)%list;
        rewrite get_update_unconstr_eq;
        red; exists (({| elementIndex := incrMaxFreshIdx lfin';
                    indexedElement := totup d |}) :: lfin')%list;
        destruct Hlfin as [Hmap [Heqv Hdup]]; split; [ | split ]

      | [ |- map _ _ = _ ] =>
        simpl; rewrite <- Hmap; reflexivity

      | [ |- NoDup _ ] =>
        cbn; constructor;
        try (unfold incrMaxFreshIdx; intro;
             apply (list_helper _ _ _ (Nat.lt_succ_diag_r _)) in H0);
        solve [auto]

      | [ |- forall _, In _ _ _ <-> List.In _ _ ] =>
        intros xelem; split; intros Hin; destruct Hin as [Hin | Hin];
        solve [ left; auto | right; apply Heqv in Hin; auto ]
    end.

    all: intros inp Hinp; split; repeat rewrite get_update_unconstr_eq;
      intros Hoin; try destruct Hoin as [eid [Hoin | Hoin]].
    + exists (incrMaxFreshIdx lfin');
      red; red; left. unfold totup. inversion Hoin; subst; reflexivity.
    + assert (Hoin': IndexedEnsemble_In
                       (GetUnConstrRelation r_n (myqidx h))
                       (totup inp)) by (exists eid; apply Hoin).
      apply (Hles inp Hinp) in Hoin'. red.
      destruct Hoin' as [eid' Hoin']. exists eid'.
      red; red; right. apply Hoin'.
    + exists idx; red; red; left; unfold totup; inversion Hoin; subst; auto.
    + assert (Hoin': IndexedEnsemble_In
                       (GetUnConstrRelation r_o (myqidx h))
                       (totup inp)) by (exists eid; apply Hoin).
      apply (Hles inp Hinp) in Hoin'. red.
      destruct Hoin' as [eid' Hoin']. exists eid'.
      red; red; right. apply Hoin'.
    + apply (Hles inp Hinp) in Hoin; red; destruct Hoin as [eid Hoin];
      exists eid; red; red; right; auto.
    + inversion Hoin. assert (Hrule: cf_cond OutgoingRule inp = cf_cond OutgoingRule d).
      { destruct inp, d, in_ip4, in_ip0; cbn in *; subst. reflexivity. }
      congruence.
    + assert (Hoin': IndexedEnsemble_In
                       (GetUnConstrRelation r_o (myqidx h))
                       (totup inp)) by (exists eid; apply Hoin).
      apply (Hles inp Hinp) in Hoin'. red.
      destruct Hoin' as [eid' Hoin']. exists eid'. apply Hoin'.


  * hone method "Filter".
    subst r_o. refine pick eq. simplify with monad laws.
    apply refine_bind. apply CompPreservesFilterMethod; reflexivity. intro.
    apply refine_bind. reflexivity. intro. simpl. higher_order_reflexivity.


    PickIndex ltac:(fun attrlist =>
                      make_simple_indexes attrlist BuildEarlyIndex BuildLastIndex).

    + plan CreateTerm EarlyIndex LastIndex makeClause_dep EarlyIndex_dep LastIndex_dep.
    + etransitivity. simplify with monad laws.
      repeat   match goal with
               | [|- refine (Bind _ _) _] => eapply refine_bind
               end.
      unfold FilterMethod_UnConstr_Comp.
      eapply refine_If_Then_Else. reflexivity.
      eapply refine_If_Then_Else. reflexivity.
      apply refine_bind.

      Arguments GetAttribute : clear implicits.
      Arguments RawTuple : clear implicits.

      etransitivity; [ setoid_rewrite refine_UnConstrQuery_In | ].
      { reflexivity. }
      { intro.
        etransitivity; [apply refine_Query_Where_Cond | ].

        {
        Transparent OutgoingToRule OutgoingRule.
        (* Arguments mask_of_nat: simpl never. *)
        Arguments wand: simpl never.
        Arguments N.land: simpl nomatch.
        Arguments chain_beq: simpl never.
        Arguments GetAttribute: simpl never.
        Hint Unfold cf_cond combine_conditions cond_srcaddr cond_dstaddr cond_chain match_address : iptables.
        Hint Unfold OutgoingToRule OutgoingRule : iptables.
        repeat (autounfold with iptables; cbn).

        (* Hint Rewrite -> wand_full_mask : iptables. *)
        Hint Rewrite -> andb_true_iff andb_true_l andb_true_r : iptables.
        Hint Rewrite -> internal_chain_dec_bl : iptables.
        Hint Rewrite -> N.eqb_eq : iptables.
        Hint Rewrite -> weqb_true_iff : iptables.
        autorewrite with iptables.

        repeat match goal with
               | _ => rewrite and_assoc
               | [  |- context[chain_beq ?x ?y = true /\ ?z] ] => rewrite (and_comm (chain_beq x y = true) z)
               end.
        rewrite <- !and_assoc.

        reflexivity.
        }

        Axiom refine_Query_Where_And :
          forall (ResultT : Type) (P Q : Prop)
            (body : Comp (list ResultT)),
            refine (Query_Where (P /\ Q) body)
                   (Query_Where P (Query_Where Q body)).

        clear Hdrop.
        etransitivity.
        apply refine_Query_Where_And.
        etransitivity.
        apply refine_Query_Where_And.

  (*       Proof. *)
  (*         unfold refine, Query_Where; intros * H. *)
  (*         computes_to_econstructor; computes_to_inv; *)
  (*           destruct H; split; *)
  (*             [intros (p & q) | intros]. *)
  (*         - specialize (H p); computes_to_inv; tauto. *)
  (*         - assert (~P \/ ~Q). *)
  (*           rewrite not_and_implication in H1. *)
  (*           Require Import Classical. *)
  (*           tauto. *)

  (*         (HP & HQ). *)
  (*         etransitivity; intro. *)
  (*         apply refine_Query_Where_Cond. with (Q := True). *)
  (*   intuition; intros. *)
  (*   intros; computes_to_econstructor; intuition. *)
  (* Qed. *)

        higher_order_reflexivity.
      }

      implement_Query IndexUse createEarlyTerm createLastTerm
      IndexUse_dep createEarlyTerm_dep createLastTerm_dep.

      simpl; repeat first [setoid_rewrite refine_bind_unit
                          | setoid_rewrite refine_bind_bind ];
      cbv beta; simpl.

      setoid_rewrite map_length.
      setoid_rewrite app_nil_r.
      setoid_rewrite map_length.

      finish honing.

      intro; higher_order_reflexivity.

      intro.
      unfold RefinedInsert.
      etransitivity; [ eapply refine_If_Then_Else_Bind | ].
      etransitivity; [ eapply refine_If_Then_Else | ].

      simpl.
      unfold myqidx.
      simplify with monad laws.
      subst totup topkt Hdrop.
      cbv beta.
      change (GetUnConstrRelationBnd r_o ?idx) with (GetUnConstrRelation r_o ((ibound (indexb idx)))).
      simpl.
      etransitivity.
      insertion IndexUse createEarlyTerm createLastTerm IndexUse_dep createEarlyTerm_dep createLastTerm_dep.

      simplify with monad laws.
      higher_order_reflexivity.

      simpl.
      simplify with monad laws.
      refine pick val _; [ | eauto ].
      simplify with monad laws.
      higher_order_reflexivity.

      (* FIXME: Can this safely be moved up? *)
      Arguments cf_cond: simpl never.
      higher_order_reflexivity.

      subst H.
      higher_order_reflexivity.

    + clear topkt.
      clear totup.
      clear Hdrop.

      (* FIXME get rid of topkt/totup/Hdrop to speed up derivations *)
      Implement_Bags BuildEarlyBag BuildLastBag.
Defined.

Definition GuardImpl :=
  Eval simpl in projT1 SharpenNoIncomingFilter.

Definition guard_init : ComputationalADT.cRep GuardImpl :=
  Eval simpl in (CallConstructor GuardImpl "Init").

(* FIXME rename Filter to ProcessPacket and take bytes as input *)
Definition guard_process_packet (bs: input) (rep: ComputationalADT.cRep GuardImpl) : (_ * option result) :=
  Eval simpl in CallMethod GuardImpl "Filter" rep bs.
