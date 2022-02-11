Require Export
        Coq.Lists.List
        Fiat.Common
        Fiat.Computation.Core
        Fiat.Computation.Notations
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.Monoid
        Fiat.Narcissus.Stores.Cache.
Require Import Strings.String. (* For errors*)


Set Implicit Arguments.


(* For errors*)
Inductive CoderError : Type :=
(*Generic errors*)
| UnknownError
| OtherError
(*Decoder Errors*)
| EndOfBuffer
(*Encoder errors*)
| DecideableEnsembles
(* Label for error traceback*)
(* Add extra information*)
| InfoError (msg: string) (e: CoderError)
(* Traceback hierarchy step (e.g. function call) *)
| LabelError (msg: string) (e: CoderError).

Inductive Hopefully (T: Type): Type :=
| Ok: T -> Hopefully T
| Error: CoderError -> Hopefully T.
Arguments Ok {_} _.
Arguments Error {_} _.

Definition OtherErrorInfo {T} (st:string): Hopefully T:=
  Error (InfoError st OtherError).

Definition OptnError {T} (e: CoderError) (x: option T) : Hopefully T:=
  match x with
  | Some a => Ok a
  | None => Error e
  end.

(* This is ridiculous
     Derive from monad but its currently overloaded by Comp...
 *)
(* >>=*)
Definition hbind {A B: Type} (ha: Hopefully A) (f: A -> Hopefully B) : Hopefully B :=
  match ha with
  | Ok a => f a
  | Error e => Error e
  end.
Definition hmap {A B: Type} (f: A -> B)  (ha: Hopefully A) : Hopefully B :=
  hbind ha (fun x => Ok (f x)).
Notation "'HBind' c 'as' c' 'With' t" :=
  (hbind c (fun c' => t))
    (at level 70).
(* for error*)
Definition is_error {T} (t:Hopefully T):=
  match t with
  | Ok _ => False
  | Error _ => True
  end.
Lemma isError: forall {T} (x: Hopefully T) e, x = Error e -> is_error x.
Proof. intros; subst; constructor. Qed.

Inductive has_error {T}: Hopefully T -> CoderError -> Prop:=
| Has_error: forall e, has_error (Error e) e.



Inductive Ok_equiv {T}: relation (Hopefully T):=
  Build_Ok_equiv: forall h1 h2,
    h1 = h2 \/ (is_error h1 /\ is_error h2) -> Ok_equiv h1 h2.
Infix "~=":= Ok_equiv.
Instance Ok_equiv_reflexive: forall T, Reflexive (@Ok_equiv T).
Proof.
  intros ??.  econstructor; intros.
  destruct x; eauto.
Qed.
Global Hint Resolve Ok_equiv_reflexive: core.
Instance Ok_equiv_symmetry: forall {T},
    Symmetric (@Ok_equiv T).
Proof.
  intros ?? ? HH. econstructor.
  destruct HH. edestruct H; split_and; eauto.
Qed.
Instance Ok_equiv_transitivity: forall {T},
    Transitive (@Ok_equiv T).
Proof.
  intros ?? ? ? H1 H2. econstructor.
  destruct H1. destruct H2.
  destruct H; destruct H0; subst; eauto.
  split_and; eauto.
Qed.

Lemma Proper_hope_equiv_then {T}: Proper (Ok_equiv ==> Ok_equiv ==> impl) (@Ok_equiv T).
Proof.
  intros ??? ??? HH.
  etransitivity; eauto. symmetry.
  etransitivity; try eapply H.
  symmetry; eauto.
Qed.
Instance Proper_hope_equiv {T}: Proper (Ok_equiv ==> Ok_equiv ==> iff) (@Ok_equiv T).
Proof.
  constructor; eapply Proper_hope_equiv_then; eauto; symmetry; assumption.
Qed.
Instance Proper_is_error_equiv {T}: Proper (Ok_equiv ==> iff) (@is_error T).
Proof.
  intros  ? ? ?. destruct H. destruct H; subst.
  - reflexivity.
  - split_and. split; eauto.
Qed.



Lemma Ok_eq {T} {x y: Hopefully T} (H:x ~= y):
  forall x',
    x = Ok x' -> x = y.
Proof.
  intros; inversion H. subst.
  inversion H1; eauto. split_and. inversion H2.
Qed.
Lemma Ok_eq_Ok {T} {x y: Hopefully T} (H:x ~= y):
  forall y',
    y = Ok y' -> x = Ok y'.
Proof.
  intros. symmetry. symmetry in H.
   inversion H; subst.
  inversion H1; eauto. split_and. inversion H2.
Qed.

Global Hint Resolve Ok_eq: core.
Lemma hope_equiv_eq {T}:
  forall (x y: Hopefully T), x = y ->
         x ~= y.
Proof. constructor; left; assumption. Qed.
Global Hint Resolve hope_equiv_eq: core.


Lemma Error_eq {T}: forall x y,
  @Error T x ~= Error y.
Proof.
  intros. solve [repeat constructor].
Qed.
Global Hint Resolve Error_eq: core.

Instance Proper_hbind_equiv {A B}: Proper (Ok_equiv ==> eq ==> Ok_equiv) (@hbind A B).
Proof.
  intros ??? ???. subst. unfold hbind. break_match; eauto.
  + inversion H. destruct H0; inversion H0; subst; eauto. inversion H3.
  + inversion H. inversion H0; subst; try discriminate.
    destruct H3 as (HH & ?); inversion HH.
  + inversion H. inversion H0; subst; try discriminate.
    destruct H3 as (? & HH); inversion HH.
Qed.


Definition Ok_equiv_decoder {V T} {C: Cache}: relation (T -> CacheDecode -> Hopefully (V * T * CacheDecode)):= fun D1 D2 => forall t c, D1 t c ~= D2 t c.
Instance Ok_equiv_decoder_reflexive: forall {V T} {C: Cache},
    Reflexive (@Ok_equiv_decoder V T C).
Proof. intros ???? ?? .  reflexivity.  Qed.

Instance Ok_equiv_decoder_commutative: forall {V T} {C: Cache},
    Symmetric (@Ok_equiv_decoder V T C).
Proof. intros ???? ? HH ?? . symmetry; eauto. Qed.
Infix "~==":= Ok_equiv_decoder (at level 70).

(* Use this for easy rewrite of equalities *)
Lemma Ok_eqd {V T} {C: Cache} {x y: T -> CacheDecode -> Hopefully (V * T * CacheDecode)} (H:x ~== y):
  forall x' t c,
    x t c = Ok x' -> x t c = y t c.
Proof. intros. eapply Ok_eq; eauto. Qed.
(*Some useful tactics, im sure this is somewhere in fiat... *)

Definition catchError {T} (x: Hopefully T) (f: CoderError -> CoderError) :=
  match x with
  | Ok x => Ok x
  | Error e => Error (f e)
  end.
(* Notation "'Try' c 'Except' c' : t" := *)
(* (catchError c (fun c' => t)) (at level 70). *)
