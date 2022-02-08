Require Import
        Fiat.Common.BoundedLookup.
Require Import
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Formats.WordOpt.
Require Import
        Coq.Vectors.Vector
        Bedrock.Word.

Section Enum.
  Context {len : nat}.
  Context {A : Type}.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Context {sz : nat}.
  Context {ta : t A (S len)}.
  Variable (tb : t (word sz) (S len)).

  Inductive NoDupVector {A}
    : forall {n}, Vector.t A n -> Prop :=
    NoDupVector_nil : NoDupVector (Vector.nil _)
  | NoDupVector_cons : forall (x : A) {n} (l : Vector.t A n),
      ~ Vector.In x l -> NoDupVector l -> NoDupVector (Vector.cons _ x _ l).

  Lemma NoDupVector_invert {A'}
    : forall n (l : Vector.t A' n),
      NoDupVector l
      -> match l with
         | Vector.nil => True
         | Vector.cons a _ l' =>
           ~ Vector.In a l' /\ NoDupVector l'
         end.
  Proof.
    clear; induction 1; eauto.
  Qed.

  Definition format_enum (idx : Fin.t _) :
    CacheFormat -> Comp (B * CacheFormat) :=
    format_word (nth tb idx).

  Definition encode_enum (idx : Fin.t _) :
    CacheFormat -> B * CacheFormat :=
    encode_word (nth tb idx).

  Lemma refine_format_enum :
    forall idx ce,
      refine (format_enum idx ce)
             (ret (encode_enum idx ce)).
  Proof.
    intros; reflexivity.
  Qed.

  Fixpoint word_indexed {n : nat}
           (w : word sz)
           (t : t (word sz) n) : Hopefully (Fin.t n)
    := match t in Vector.t _ n return Hopefully (Fin.t n) with
       | nil => OtherErrorInfo "Decoding enum error: index too large."
       | cons w' _ t' =>
         if (weqb w w') then Ok (Fin.F1) else
           match word_indexed w t' with
           | Ok f => Ok (Fin.FS f)
           | Error e => Error e 
           end
       end.

  Definition decode_enum (b : B)
             (cd : CacheDecode)
    : Hopefully (Fin.t _ * B * CacheDecode) :=
    `(w, b', cd') <- decode_word (sz:=sz) b cd;
      HBind word_indexed w tb as idx With
      Ok (idx, b', cd').

  Lemma word_indexed_correct :
    forall n (i : Fin.t n) (t : t (word sz) n),
      NoDupVector t
      -> match word_indexed (nth t i) t with
      | Ok w' => i = w'
      | _ => False
      end.
  Proof.
    clear.
    induction i.
    - intro; pattern n, t; apply Vector.caseS; simpl; intros.
      rewrite (proj2 (weqb_true_iff h h)); eauto.
    - intro; generalize i (IHi (Vector.tl t)); clear.
      pattern n, t; apply Vector.caseS; simpl.
      intros h n0 t0 i; case_eq (word_indexed (nth t0 i) t0); intros;
        apply NoDupVector_invert in H1; intuition subst.
      case_eq (weqb (nth t0 t1) h); intros; eauto.
      apply weqb_true_iff in H0; subst.
      destruct H2; generalize t0 H; clear; induction t1.
      + intro; pattern n, t0; apply Vector.caseS; simpl; intros; econstructor.
      + intro; revert t1 IHt1; pattern n, t0; apply Vector.caseS;
          simpl; intros.
        case_eq (weqb (nth t t1) h); intros; eauto.
        * apply weqb_true_iff in H0; subst; econstructor.
        * rewrite H0 in H.
          econstructor 2; apply IHt1.
          destruct (word_indexed (nth t t1) t); try discriminate.
          f_equal; apply Fin.FS_inj; congruence.
  Qed.

  Lemma word_indexed_correct':
    forall n (v : Fin.t n) (w : word sz) (t : t (word sz) n),
      word_indexed w t = Ok v -> w = nth t v.
  Proof.
    clear.
    induction v.
    - intros w tb; pattern n, tb;
        eapply Vector.caseS; simpl.
      intros; destruct (weqb w h) eqn: ?.
      eapply weqb_true_iff; eauto.
      destruct ( word_indexed w t); try discriminate.
    - intros w tb.
      revert w v IHv.
      pattern n, tb; eapply Vector.rectS; simpl; intros.
      inversion v.
      intros; destruct (weqb w a) eqn: ?.
      discriminate.
      destruct (word_indexed w v) eqn : ? ; try discriminate.
      eapply IHv.
      rewrite Heqh.
      f_equal.
      eapply Fin.FS_inj.
      congruence.
  Qed.

  Theorem Enum_decode_correct
          (tb_OK : NoDupVector tb)
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
    : CorrectDecoder monoid (fun _ => True)
                     (fun _ => True) eq format_enum decode_enum P
                     format_enum.
  Proof.
    apply_bijection_rule' with (fun w => word_indexed w tb);
      intuition eauto using Word_decode_correct.
    eapply word_indexed_correct in tb_OK.
    destruct word_indexed eqn:?; subst; intuition eauto.
    symmetry. eauto using word_indexed_correct'.

    derive_decoder_equiv;
      destruct (word_indexed w tb); injections; simpl; eauto; try discriminate.
  Qed.
End Enum.

Lemma VectorIn_cons {A} {n}
  : forall (v : Vector.t A n) a a',
    Vector.In a' (Vector.cons _ a _ v) -> a = a' \/ Vector.In a' v.
Proof.
  intros; inversion H; subst; eauto.
  apply Eqdep_dec.inj_pair2_eq_dec in H3; subst; eauto using Peano_dec.eq_nat_dec.
Qed.

Lemma forall_Vector_P {A} (P : A -> Prop) {n}
  : forall v : Vector.t A n,
    Vector.Forall P v
    -> forall idx, P (Vector.nth v idx).
Proof.
  induction v; simpl; intros.
  - inversion idx.
  - revert v IHv H; pattern n, idx; apply Fin.caseS; simpl;
      intros; inversion H; subst; eauto.
    eapply IHv.
    apply Eqdep_dec.inj_pair2_eq_dec in H2; subst; eauto using Peano_dec.eq_nat_dec.
Qed.

Ltac Discharge_NoDupVector :=
  match goal with
  |- NoDupVector _ =>
  repeat econstructor; intro;
  repeat match goal with
         | H : Vector.In _ _ |- _ =>
           first [apply VectorIn_cons in H; destruct H; try discriminate
                 | inversion H]
         end
  end.
