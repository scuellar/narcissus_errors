Require Import
        Fiat.Common
        Fiat.Computation
        Fiat.Computation.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.BaseFormats.


Unset Implicit Arguments.

Require Import Strings.String. (* For errors*)

(*** TAGS/ LABELS
     TOD: Move to other file
 **)
  Definition format_label {T B C} (label: string): @FormatM T B C -> @FormatM T B C := id.
  Lemma format_label_equiv: forall S T C label format,
      @EquivFormat S T C (format_label label format) format.
  Proof.
    intros. constructor; simpl; unfold format_label, id; simpl; intros ? **; auto.
  Qed.


(** END OF TAGS/LABELS
 **)


Require Import Fiat.Narcissus.BinLib.AlignedByteString.
Require Import Strings.String. (* For errors*)
Require Import Fiat.Narcissus.Stores.EmptyStore.

Definition encoder_tag {CacheFormat S} (label: string)
           (encoder: forall n,  (*@AlignedEncodeM c S sz*)
                      ByteBuffer.t n -> nat -> S -> CacheFormat -> Hopefully (ByteBuffer.t n * nat * CacheFormat)):
  (*@AlignedEncodeM c S sz*)
                   forall n, ByteBuffer.t n -> nat -> S -> CacheFormat -> Hopefully (ByteBuffer.t n * nat * CacheFormat):=
    fun C S n s c => catchError (encoder C S n s c) (LabelError label).
Definition decoder_tag {BS CD A} (label: string)
           (decoder: BS ->
                     CD ->
                     Hopefully (A * BS * CD)):
  BS -> CD -> Hopefully (A * BS * CD):= 
  fun b s  => catchError (decoder b s) (LabelError label).
Definition aligned_decoder_tag {BS CD A} (label: string)
           (decoder: BS ->
                     CD ->
                     Hopefully (A * BS * CD)):
  BS -> CD -> Hopefully (A * BS * CD):= 
  fun b s  => catchError (decoder b s) (LabelError label).

Lemma tag_decode_simple_correct
  : forall A tag
           (format_A : A ->
                       CacheFormat -> Comp (ByteString * CacheFormat))
           (A_cache_inv : CacheDecode -> Prop),
  forall
    (decode_A : ByteString ->
                CacheDecode ->
                Hopefully (A * ByteString * CacheDecode))
    (A_predicate : A -> Prop),
    CorrectDecoder ByteStringQueueMonoid A_predicate A_predicate eq
                   format_A decode_A A_cache_inv format_A ->
    CorrectDecoder ByteStringQueueMonoid A_predicate A_predicate eq
                   (format_label tag format_A)
                   (decoder_tag tag decode_A)
                   A_cache_inv
                   (format_label tag format_A).
Proof.
  unfold format_label, id; simpl; intros.
  (* PROOF SKETCH: `format_label` and `decoder_tag` are computational irrelevant.
     Proof technique: Prove an equivalence relation for `decoder_tag` and a morphism for `CorrectDecoder`
   *)
Admitted.

Lemma EquivFormat_label: forall S T C label format format',
    @EquivFormat S T C format format' ->
    @EquivFormat S T C (format_label label format) (format_label label format').
Proof. unfold format_label, id; auto. Qed.
(** END MOVE
 **)



(** end move
*)

(* From now on to deal with format_label you must use the lemmas in
this file. This is important so automation doens't just unfold and
simplify it away.  *)
Opaque format_label.
