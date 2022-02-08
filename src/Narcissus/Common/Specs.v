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



(** ERRORS
    New more descriptive errors.
    TODO: Move to a new file.

 **)


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

(** END of ERRORS


**)








Section Specifications.


  
  Variable S : Type. (* Source Type. (in-memory data) *)
  Variable T : Type. (* Target Type. (usually ByteStrings) *)
  Context {store : Cache}. (* Store Type. *)

  (* Formats are a quaternary relation on an source value, initial store,
     target value, and final store. *)
  Definition FormatM : Type :=
    S -> CacheFormat -> Comp (T * CacheFormat).

  (* Decoders consume a target value and store and produce either
     - a source value, remaining target value, and updated store
     - or an error value, i.e. None. *)

  Definition DecodeM : Type :=
    T -> CacheDecode -> Hopefully (S * CacheDecode).

  (* Encoders take a source value and store and produce either a
     - target value and updated store
     - or an error value, i.e. None. *)

  Definition EncodeM : Type :=
    S -> CacheFormat -> Hopefully (T * CacheFormat).

  Local Notation "a ∋ b" := (@computes_to _ a b) (at level 90).
  Local Notation "a ∌ b" := (~ @computes_to _ a b) (at level 90).

  Definition CorrectDecoder {V}
             (monoid : Monoid T)
             (Source_Predicate : S -> Prop)
             (View_Predicate : V -> Prop)
             (view : S -> V -> Prop)
             (format : FormatM)
             (decode : T -> CacheDecode -> Hopefully (V * T * CacheDecode))
             (decode_inv : CacheDecode -> Prop)
             (view_format : V -> CacheFormat -> Comp (T * CacheFormat)) :=
    (forall env env' xenv s t ext
            (env_OK : decode_inv env'),
        Equiv env env' ->
        Source_Predicate s ->
        format s env ∋ (t, xenv) ->
        exists v xenv',
          decode (mappend t ext) env' = Ok (v, ext, xenv')
          /\ view s v
          /\ (view_format v env ∋ (t, xenv))
          /\ Equiv xenv xenv' /\ decode_inv xenv') /\
    (forall (env : CacheFormat) (env' xenv' : CacheDecode) (v : V) (t t' : T),
        Equiv env env' ->
        decode_inv env' ->
        decode t env' = Ok (v, t', xenv') ->
        decode_inv xenv' /\
        exists (t'' : T) (xenv : CacheFormat),
          (view_format v env ∋ (t'', xenv))
          /\ t = mappend t'' t'
          /\ View_Predicate v
          /\ Equiv xenv xenv').

  Definition CorrectEncoder
             (format : FormatM)
             (encode : EncodeM)
    :=
      (forall (a : S) (env : CacheFormat) (b : T) (xenv : CacheFormat),
          encode a env = Ok (b, xenv)
          -> format a env ∋ (b, xenv))
      /\ (forall (a : S) (env : CacheFormat),
             is_error (encode a env)
             -> forall b xenv, ~ (format a env ∋ (b, xenv))).

    (* Definition that identifies properties of cache invariants for automation. *)
  Definition cache_inv_Property
             (P : CacheDecode -> Prop)
             (P_inv : (CacheDecode -> Prop) -> Prop) :=
    P_inv P.

  Lemma CorrectDecoderNone
        (monoid : Monoid T)
        {V}
    : forall (Source_Predicate : S -> Prop)
             (View_Predicate : V -> Prop)
             (format : FormatM)
             (decode : _)
             (view : S -> V -> Prop)
             (decode_inv : CacheDecode -> Prop)
             (view_format : V -> CacheFormat -> Comp (T * CacheFormat)),
      CorrectDecoder _ Source_Predicate View_Predicate view format decode decode_inv view_format
      -> forall b b' s_d,
        decode_inv s_d
        -> is_error( decode (mappend b b') s_d)
        -> forall a s_e s_e',
            Equiv s_e s_d
            -> Source_Predicate a
            -> format a s_e ∌ (b, s_e').
  Proof.
    unfold not, CorrectDecoder, is_error; intros.
    split_and.
    eapply H5 in H4; eauto.
    destruct_ex; split_and.
    rewrite H6 in H1. inversion H1. 
  Qed.

  Definition CorrectDecoder_id
             (monoid : Monoid T)
             (Source_Predicate : S -> Prop)
             (format : FormatM)
             (decode : T -> CacheDecode -> Hopefully (S * T * CacheDecode))
             (decode_inv : CacheDecode -> Prop) :=
    (forall env env' xenv s t ext
            (env_OK : decode_inv env'),
        Equiv env env' ->
        Source_Predicate s ->
        format s env ∋ (t, xenv) ->
        exists xenv',
          decode (mappend t ext) env' = Ok (s, ext, xenv')
          /\ Equiv xenv xenv' /\ decode_inv xenv') /\
    (forall env env' xenv' s t ext,
        Equiv env env'
        -> decode_inv env'
        -> decode t env' = Ok (s, ext, xenv')
        -> decode_inv xenv'
           /\ exists t' xenv,
            (format s env ∋ (t', xenv))
            /\ t = mappend t' ext
            /\ Source_Predicate s
            /\ Equiv xenv xenv').

  (* The current definition of decoder correctness is equivalent to an
   e arlier one, when the projection is the identity function. *)
  Lemma CorrectDecoder_equiv_CorrectDecoder_id
    : forall (monoid : Monoid T)
             (Source_Predicate : S -> Prop)
             (format : FormatM)
             encode
             (correctEncode : CorrectEncoder format encode)
             (decode : T -> CacheDecode -> Hopefully (S * T * CacheDecode))
             (decode_inv : CacheDecode -> Prop),
      (CorrectDecoder_id monoid Source_Predicate format decode decode_inv <->
       CorrectDecoder monoid Source_Predicate Source_Predicate eq format decode decode_inv format).
  Proof.
    unfold CorrectDecoder_id, CorrectDecoder; intuition eauto.
    - generalize H3; intro;
        eapply H0 in H3; destruct_ex; split_and; eauto.
      rewrite H5; eexists _, _; intuition eauto.
    - eapply H0 in H3; destruct_ex; split_and; eauto.
      rewrite H3; eexists _; subst; intuition eauto.
  Qed.

  Corollary CorrectDecoderNone_dec_Source_Predicates
            (monoid : Monoid T)
            {V}
    : forall (Source_Predicate : S -> Prop)
             (View_Predicate : V -> Prop)
             (view : S -> V -> Prop)
             (Source_Predicate_dec : forall a, Source_Predicate a \/ ~ Source_Predicate a)
             (format : FormatM)
             (decode : _)
             (decode_inv : CacheDecode -> Prop)
             view_format,
      CorrectDecoder _ Source_Predicate View_Predicate view format decode decode_inv view_format
      -> forall b b' s_d,
        decode_inv s_d
        -> is_error(decode (mappend b b') s_d)
        -> forall a ,
            (~ Source_Predicate a)
            \/ forall s_e s_e',
                Equiv s_e s_d
                -> format a s_e ∌ (b, s_e').
  Proof.
    intros.
    destruct (Source_Predicate_dec a); intuition.
    right; intros; eapply CorrectDecoderNone; eauto.
  Qed.

  Lemma decode_None :
    forall (monoid : Monoid T)
           (Source_Predicate : S -> Prop)
           (format : S -> CacheFormat -> Comp (T * CacheFormat))
           (decode : T -> CacheDecode -> Hopefully (S * T * CacheDecode))
           (decode_inv : CacheDecode -> Prop)
           (Source_Predicate_dec : forall a, {Source_Predicate a} + {~ Source_Predicate a}),
      CorrectDecoder monoid Source_Predicate Source_Predicate eq format decode decode_inv format
      -> forall b env' env,
        Equiv env env'
        -> is_error(decode b env')
        -> decode_inv env'
        -> forall s,
          ~ Source_Predicate s
          \/ ~ exists xenv, format s env ∋ (b, xenv).
  Proof.
    intros.
    destruct (Source_Predicate_dec s); try (solve [intuition]).
    right.
    intros [? ?].
    destruct ((proj1 H) env env' _ s _ mempty H2 H0 s0 H3); intuition;
      destruct_ex; intuition.
    rewrite mempty_right in H5. rewrite H5 in H1; inversion H1. 
  Qed.

  Local Transparent computes_to.

  (* We can always strengthen a format to disallow invalid s. *)
  Lemma CorrectDecoderStrengthenFormat :
    forall (monoid : Monoid T)
           {V}
           (Source_Predicate : S -> Prop)
           (View_Predicate : V -> Prop)
           (view : S -> V -> Prop)
           (format : S -> CacheFormat -> Comp (T * CacheFormat))
           (decode : T -> CacheDecode -> Hopefully (V * T * CacheDecode))
           (decode_inv : CacheDecode -> Prop)
           (Source_Predicate_dec : forall a, {Source_Predicate a} + {~ Source_Predicate a})
           view_format
    ,
      CorrectDecoder monoid Source_Predicate View_Predicate view format decode decode_inv view_format
      ->
      CorrectDecoder monoid Source_Predicate View_Predicate view  (fun a s b => (format a s ∋ b) /\ Source_Predicate a) decode decode_inv view_format.
  Proof.
    intros; destruct H as [? ? ]; unfold CorrectDecoder; split; intros.
    - eapply H; eauto.
      apply (proj1 H3).
    - eapply H0 in H3; intuition eauto.
  Qed.

  Local Opaque computes_to.

  Definition BindOpt {S' S''}
             (a_opt : Hopefully S')
             (k : S' -> Hopefully S'') :=
    hbind a_opt k.
  Lemma BindOpt_assoc {S''' S' S''} :
    forall (a_opt : Hopefully S''')
           (f : S''' -> Hopefully S')
           (g : S' -> Hopefully S''),
      BindOpt (BindOpt a_opt f) g =
      BindOpt a_opt (fun a => BindOpt (f a) g).
  Proof.
    destruct a_opt as [ ? | ]; simpl; intros; eauto.
  Qed.
  Instance Proper_BindOpt_equiv {A B}: Proper (Ok_equiv ==> eq ==> Ok_equiv) (@BindOpt A B).
  Proof.
    intros ??? ???. subst. unfold BindOpt.
    apply Proper_hbind_equiv; auto.
  Qed.
  

  Definition DecodeBindOpt2
             {V D E}
             (a : Hopefully (S * T * D))
             (k : S -> T -> D -> Hopefully (V * E * D))
    : Hopefully (V * E * D) :=
    BindOpt a (fun a => match a with (a, b, d) => k a b d end).

  Definition DecodeBindOpt
             {V}
             (a : Hopefully (S * T))
             (k : S -> T -> Hopefully (V * T))
    : Hopefully (V * T) :=
    BindOpt a (fun a => let (a, b) := a in k a b).

  Lemma DecodeBindOpt2_inv
        {V D E}
        (a_opt : Hopefully (S * T * D))
        (a : V * E * D)
        (k : S -> T -> D -> Hopefully (V * E * D))
    : DecodeBindOpt2 a_opt k = Ok a ->
      exists a' b' d',
        a_opt = Ok (a', b', d')
        /\ Ok a = k a' b' d'.
  Proof.
    unfold DecodeBindOpt2; destruct a_opt as [ [ [a' b'] d'] | ];
      simpl; intros; first [discriminate | injections ].
    eexists _, _, _; intuition eauto.
  Qed.

  Lemma DecodeBindOpt_inv
        {V}
        (a_opt : Hopefully (S * T))
        (a : V * T)
        (k : S -> T -> Hopefully (V * T))
    : DecodeBindOpt a_opt k = Ok a ->
      exists a' b',
        a_opt = Ok (a', b')
        /\ Ok a = k a' b'.
  Proof.
    unfold DecodeBindOpt; destruct a_opt as [ [a' b'] | ];
      simpl; intros; first [discriminate | injections ].
    eexists _, _; intuition eauto.
  Qed.
  
  Instance Proper_DecodeBindOpt2_equiv {A B C}: Proper (Ok_equiv ==> eq ==> Ok_equiv) (@DecodeBindOpt2 A B C).
  Proof.
    intros ??? ???. subst. unfold DecodeBindOpt2.
    apply Proper_hbind_equiv; auto.
  Qed.
  Instance Proper_DecodeBindOpt_equiv {A}: Proper (Ok_equiv ==> eq ==> Ok_equiv) (@DecodeBindOpt A).
  Proof.
    intros ??? ???. subst. unfold DecodeBindOpt.
    apply Proper_hbind_equiv; auto.
  Qed.

End Specifications.

Definition Cache_plus_inv (cache : Cache)
           (decode_inv : @CacheDecode cache -> Prop): Cache :=
  {| CacheFormat := @CacheFormat cache;
     CacheDecode := @CacheDecode cache;
     Equiv ce cd := Equiv ce cd /\ decode_inv cd|}.

Definition decode_strict
           {S T}
           {cache : Cache}
           {monoid : Monoid T}
           (decode : DecodeM S T)
  : DecodeM (S * T) T :=
  fun cd bs => 
    HBind decode cd bs
    as abscd'
         With Ok (fst abscd', mempty, snd abscd').

Definition RestrictFormat
           {S T}
           {cache : Cache}
           (format : FormatM S T)
           (Source_Predicate : S -> Prop)
  : FormatM S T :=
  fun s env txenv => format s env txenv /\ Source_Predicate s.

(* DoneLax 'appends' a supplied bytestring onto the end of a format *)
Definition DoneLax {S T}
           {cache : Cache}
           {monoid : Monoid T}
           (format : FormatM S T)
  : FormatM (S * T) T :=
  fun s_rest env txenv =>
    exists t', fst txenv = mappend t' (snd s_rest) /\
                 format (fst s_rest) env (t', snd txenv).

Definition decode_obliviously
           {S T}
           {cache : Cache}
           {monoid : Monoid T}
           (decode : DecodeM (S * T) T)
  : T -> CacheDecode -> Hopefully (S * CacheDecode) :=
  fun bs cd => hmap (fun abc => (fst (fst abc), snd abc)) (decode bs cd).

(*Lemma CorrectDecoder_simpl_lax_equiv
      {S T}
      (cache : Cache)
      (monoid : Monoid T)
      (Source_Predicate : S -> Prop)
  : forall (decode_inv : CacheDecode -> Prop)
           (format : FormatM S T)
           (decode : DecodeM (S * T) T),
    CorrectDecoder (store := cache) monoid Source_Predicate (fun _ _ => True)  format
                   decode
                   decode_inv
    <-> CorrectDecoder_simpl
         (store := Cache_plus_inv cache decode_inv)
         (DoneLax (RestrictFormat format Source_Predicate))
         decode.
Proof.
  unfold CorrectDecoder, CorrectDecoder_simpl, DoneLax, RestrictFormat, decode_obliviously; split.
  - intuition.
    + rewrite unfold_computes in H2; simpl in *; destruct_ex; intuition.
      destruct (H0 env env' xenv a x b); simpl; intuition eauto.
      rewrite H, H7; simpl; eauto.
    + destruct (decode t env') as [ [ [? ?] ?] | ] eqn: ?; destruct_ex;
        simpl in *; try discriminate; intuition; injections; eauto.
      eapply H1 in Heqo; intuition eauto; destruct_ex; intuition.
      rewrite H2; eexists; rewrite unfold_computes; intuition eauto.
      rewrite unfold_computes in H5; simpl; eauto.
  - intros; split_and; split; intros.
    + destruct (H0 env env' xenv (s, ext) (mappend t ext)).
      simpl; intuition.
      apply unfold_computes; simpl.
      eexists; intuition eauto.
      split_and; eauto.
    + destruct (H1 env env' xenv' (s, ext) t); eauto.
      split_and. rewrite unfold_computes in H5; destruct_ex; split_and.
      subst; split; eauto.
      eexists _, _; intuition eauto.
      eauto using unfold_computes.
Qed. *)

Definition DecodeOpt2_fmap
           {S S'}
           (f : S -> S')
           (a_opt : Hopefully S)
  : Hopefully S' := HBind a_opt as a With Ok (f a). 

Definition DecodeOpt2_fmap_id {S}
  : forall (a_opt : Hopefully S),
    DecodeOpt2_fmap id a_opt = a_opt.
Proof.
  destruct a_opt as [ a' | ]; reflexivity.
Qed.

Definition DecodeOpt2_fmap_compose
           {S S' S''}
  : forall
    (f : S -> S')
    (f' : S' -> S'')
    (a_opt : Hopefully S),
    DecodeOpt2_fmap f' (DecodeOpt2_fmap f a_opt) =
    DecodeOpt2_fmap (compose f' f) a_opt.
Proof.
  destruct a_opt as [ a' | ]; reflexivity.
Qed.

Definition DecodeBindOpt2_fmap
           {S T T'} :
  forall (f : T -> T')
         (a_opt : Hopefully S)
         (k : S -> Hopefully T),
    DecodeOpt2_fmap f (BindOpt a_opt k) =
    BindOpt a_opt (fun a => DecodeOpt2_fmap f (k a)).
Proof.
  destruct a_opt as [ a' | ]; reflexivity.
Qed.

(* Definition BindOpt_map *)
(*            {S T T'} : *)
(*   forall (f : Hopefully T -> T') *)
(*          (a_opt : Hopefully S) *)
(*          (k : S -> Hopefully T), *)
(*     f (BindOpt a_opt k) = *)
(*     Ifopt a_opt as a Then f (k a) Else f None. *)
(* Proof. *)
(*   destruct a_opt as [ a' | ]; reflexivity. *)
(* Qed. *)

(* Lemma If_Opt_Then_Else_BindOpt {S T V} *)
(*   : forall (a_opt : Hopefully S) *)
(*            (t : S -> Hopefully T) *)
(*            (e : Hopefully T) *)
(*            (k : _ -> Hopefully V), *)
(*     BindOpt (Ifopt a_opt as a Then t a Else e) k *)
(*     = Ifopt a_opt as a Then (BindOpt (t a) k) Else (BindOpt e k). *)
(* Proof. *)
(*   destruct a_opt; simpl; intros; reflexivity. *)
(* Qed. *)

Lemma DecodeOpt2_fmap_if_bool
      {S S' }
  : forall
    (f : S -> S')
    (b : bool)
    (a_opt a_opt' : Hopefully S),
    DecodeOpt2_fmap f (if b then a_opt else a_opt') =
    if b then (DecodeOpt2_fmap f a_opt)
    else (DecodeOpt2_fmap f a_opt').
Proof.
  intros; find_if_inside; reflexivity.
Qed.

Lemma BindOpt_map_if_bool
      {S S' }
  : forall
    (f : Hopefully S -> S')
    (b : bool)
    (a_opt a_opt' : Hopefully S),
    f (if b then a_opt else a_opt') =
    if b then (f a_opt)
    else (f a_opt').
Proof.
  intros; find_if_inside; reflexivity.
Qed.

Lemma DecodeOpt2_fmap_if
      {S S' P P'}
  : forall
    (f : S -> S')
    (b : {P} + {P'})
    (a_opt a_opt' : Hopefully S),
    DecodeOpt2_fmap f (if b then a_opt else a_opt') =
    if b then (DecodeOpt2_fmap f a_opt)
    else (DecodeOpt2_fmap f a_opt').
Proof.
  intros; find_if_inside; reflexivity.
Qed.

Lemma BindOpt_map_if
      {S S' P P'}
  : forall
    (f : Hopefully S -> S')
    (b : {P} + {P'})
    (a_opt a_opt' : Hopefully S),
    f (if b then a_opt else a_opt') =
    if b then (f a_opt)
    else (f a_opt').
Proof.
  intros; find_if_inside; reflexivity.
Qed.

Lemma DecodeBindOpt2_assoc {S T V D E F G} :
  forall (a_opt : Hopefully (S * T * D))
         (f : S -> T -> D -> Hopefully (V * E * D))
         (g : V -> E -> D -> Hopefully (F * G * D)),
    DecodeBindOpt2 (DecodeBindOpt2 a_opt f) g =
    DecodeBindOpt2 a_opt (fun a b c => DecodeBindOpt2 (f a b c) g).
Proof.
  destruct a_opt as [ [ [? ?] ?] | ]; simpl; intros; eauto.
Qed.

Lemma DecodeBindOpt2_under_bind {S T V D E} :
  forall (a_opt : Hopefully (S * T * D))
         (f f' : S -> T -> D -> Hopefully (V * E * D)),
    (forall a b d, f a b d = f' a b d)
    -> DecodeBindOpt2 a_opt f = DecodeBindOpt2 a_opt f'.
Proof.
  destruct a_opt as [ [ [? ?] ?] | ]; simpl; intros; eauto.
Qed.


Notation "`( a , b , env ) <- c ; k" :=
  (DecodeBindOpt2 c%format (fun a b env => k%format)) : format_scope.

Notation "`( a , b ) <- c ; k" :=
  (DecodeBindOpt c%format (fun a b => k%format)) : format_scope.

Open Scope format_scope.

Lemma optimize_If_td2_bool {S S' T T' V}
  : forall (c : bool)
           (t e : Hopefully (S * T * V))
           (k : S -> T -> V -> Hopefully (S' * T' * V)),
    (`(a, b, env) <- (If c Then t Else e); k a b env) =
    If c Then `(a, b, env) <- t; k a b env Else (`(a, b, env) <- e; k a b env).
Proof.
  destruct c; simpl; intros; reflexivity.
Qed.

Lemma If_sumbool_Then_Else_DecodeBindOpt {S T T' ResultT ResultT'} {c : Cache} {P}
  : forall (a_eq_dec : forall a a' : S, {P a a'} + {~ P a a'})
           a a'
           (k : _ -> _ -> _ -> Hopefully (ResultT' * T' * CacheDecode))
           (t : P a a' ->  Hopefully (ResultT * T * CacheDecode))
           (e : ~ P a a' -> Hopefully (ResultT * T * CacheDecode)),
    (`(w, b', cd') <- match a_eq_dec a a' with
                      | left e => t e
                      | right n => e n
                      end;
       k w b' cd') =
    match a_eq_dec a a' with
    | left e => `(w, b', cd') <- t e; k w b' cd'
    | right n => `(w, b', cd') <- e n; k w b' cd'
    end.
Proof.
  intros; destruct (a_eq_dec a a'); simpl; intros; reflexivity.
Qed.

Lemma optimize_under_DecodeBindOpt2_both {S T V D E} {T' }
  : forall (a_opt : Hopefully (S * T * V))
           (a_opt' : Hopefully (S * T' * V))
           (g : T' -> T)
           (a_opt_eq_Ok : forall a' b' c,
               a_opt' = Ok (a', b', c) ->
               a_opt = Ok (a', g b', c))
           (a_opt_eq_None : forall e, has_error a_opt' e -> has_error a_opt e)
           (k : _ -> _ -> _ -> Hopefully (D * E * V))
           (k' : _ -> _ -> _ -> _)
           (k_eq_Ok :
              forall a' b' c,
                a_opt' = Ok (a', b', c) ->
                k a' (g b') c = k' a' b' c),
    DecodeBindOpt2 a_opt k = DecodeBindOpt2 a_opt' k'.
Proof.
  destruct a_opt' as [ [ [? ?] ?] | ]; simpl; intros.
  erewrite a_opt_eq_Ok; simpl; eauto.
  specialize (a_opt_eq_None c ltac:(constructor)).
  inversion a_opt_eq_None; reflexivity.
Qed.

Definition EquivFormat {S T} {cache : Cache}
           (format1 format2 : FormatM S T) :=
  forall s env, refineEquiv (format1 s env) (format2 s env).

Lemma EquivFormat_sym {S T} {cache : Cache} :
  forall (FormatSpec FormatSpec'  : FormatM S T),
    EquivFormat FormatSpec FormatSpec'
    -> EquivFormat FormatSpec' FormatSpec.
Proof.
  unfold EquivFormat, refineEquiv; intuition eauto;
    eapply H.
Qed.

Lemma EquivFormat_reflexive
      {S T : Type} {cache : Cache}
  : forall (format : FormatM S T),
    EquivFormat format format.
Proof.
  unfold EquivFormat; intros.
  reflexivity.
Qed.

Add Parametric Morphism
    S T V
    (cache : Cache)
    (monoid : Monoid T)
    (decode_inv : CacheDecode -> Prop)
  : (fun Source_Predicate View_Predicate view format decode =>
       @CorrectDecoder S T cache V monoid Source_Predicate View_Predicate
                                view format decode decode_inv)
    with signature (pointwise_relation _ iff
                                       --> pointwise_relation _ (flip impl)
                                       --> pointwise_relation _ (pointwise_relation _ iff)
                                       --> EquivFormat
                                       --> Ok_equiv_decoder
                                       --> EquivFormat
                                       --> impl)
      as format_decode_correct_alt.
Proof.
  
  unfold EquivFormat, impl, pointwise_relation, CorrectDecoder; intros.
  intuition eauto; intros.
  - setoid_rewrite H1.
    eapply H2 in H9.
    eapply H6 in H9; try eapply H; eauto. 
    destruct_ex; split_and;
      eexists _, _; intuition eauto.
    2: eapply H4; eauto.
    symmetry in H3.
    erewrite <- (Ok_eqd H3); eauto.
  - eapply H7; eauto.
    erewrite <- (Ok_eqd H3); eauto.
  - erewrite (Ok_eqd H3) in H9; eauto.
    eapply H7 in H8; eauto.
    split_and; destruct_ex; split_and; subst.
    eexists _, _; intuition eauto.
    eapply H4; eauto.
Qed.

Add Parametric Morphism
    S T V
    (cache : Cache)
    (monoid : Monoid T)
    (decode_inv : CacheDecode -> Prop)
    View_Predicate
    view
    format
    decode
    view_format
  : (fun Source_Predicate  =>
       @CorrectDecoder S T cache V monoid Source_Predicate View_Predicate
                       view format decode decode_inv view_format)
    with signature (pointwise_relation _ impl
                                       --> impl)
      as weaken_source_pred.
Proof.
  unfold EquivFormat, impl, pointwise_relation, CorrectDecoder; intros.
  intuition eauto; intros.
Qed.

Add Parametric Morphism
    S T V
    (cache : Cache)
    (monoid : Monoid T)
    (Source_Predicate : S -> Prop)
    (View_Predicate : V -> Prop)
    view
    (decode : T -> CacheDecode -> Hopefully (V * T * CacheDecode))
    (decode_inv : CacheDecode -> Prop)
    view_format
  : (fun format =>
       @CorrectDecoder S T cache V monoid Source_Predicate View_Predicate
                                view format decode decode_inv view_format)
    with signature (EquivFormat --> impl)
      as format_decode_correct_refineEquiv.
Proof.
  unfold EquivFormat, impl, pointwise_relation; intros.
  eapply format_decode_correct_alt_Proper; eauto; try reflexivity.
  unfold flip, EquivFormat; intros; reflexivity.
Qed.

Add Parametric Morphism
    S T V
    (cache : Cache)
    (monoid : Monoid T)
    (View_Predicate : V -> Prop)
    format
    view
    (decode : T -> CacheDecode -> Hopefully (V * T * CacheDecode))
    (decode_inv : CacheDecode -> Prop)
    view_format
  : (fun Source_Predicate =>
       @CorrectDecoder S T cache V monoid Source_Predicate View_Predicate
                                view format decode decode_inv view_format)
    with signature (pointwise_relation _ iff --> impl)
      as format_decode_correct_EquivPred.
Proof.
  unfold EquivFormat, impl, pointwise_relation; intros.
  eapply format_decode_correct_alt_Proper; eauto; try reflexivity.
  unfold flip, EquivFormat; intros; reflexivity.
  unfold flip, EquivFormat; intros; reflexivity.
Qed.

Add Parametric Morphism
    S T
    (cache : Cache)
    (monoid : Monoid T)
    (Source_Predicate : S -> Prop)
    (View_Predicate : S -> Prop)
    view
    (decode : T -> CacheDecode -> Hopefully (S * T * CacheDecode))
    (decode_inv : CacheDecode -> Prop)
  : (fun format =>
       @CorrectDecoder S T cache S monoid Source_Predicate View_Predicate
                                view format decode decode_inv format)
    with signature (EquivFormat --> impl)
      as format_decode_correct_EquivFormatAndView.
Proof.
  unfold EquivFormat, impl, pointwise_relation; intros.
  eapply format_decode_correct_alt_Proper; eauto; try reflexivity.
Qed.


Add Parametric Morphism
    S T V
    (cache : Cache)
    (monoid : Monoid T)
    (Source_Predicate : S -> Prop)
    (View_Predicate : V -> Prop)
    format
    view
    (decode_inv : CacheDecode -> Prop)
    view_format
  : (fun decode =>
       @CorrectDecoder S T cache V monoid Source_Predicate View_Predicate
                                view format decode decode_inv view_format)
    with signature (Ok_equiv_decoder --> impl)
      as format_decode_correct_EquivDecoderOk.
Proof.
  unfold impl, pointwise_relation; intros.
  eapply format_decode_correct_alt_Proper; eauto; try reflexivity;
    unfold flip, EquivFormat; reflexivity.
Qed.

Add Parametric Morphism
    S T V
    (cache : Cache)
    (monoid : Monoid T)
    (Source_Predicate : S -> Prop)
    (View_Predicate : V -> Prop)
    format
    view
    (decode_inv : CacheDecode -> Prop)
    view_format
  : (fun decode =>
       @CorrectDecoder S T cache V monoid Source_Predicate View_Predicate
                                view format decode decode_inv view_format)
    with signature (pointwise_relation _ (pointwise_relation _ eq)
                                       --> impl)
      as format_decode_correct_EquivDecoder.
Proof.
  unfold impl, pointwise_relation; intros.
  eapply format_decode_correct_EquivDecoderOk; eauto.
  econstructor. rewrite H; auto.
Qed.


Add Parametric Morphism
    S T V
    (cache : Cache)
    (monoid : Monoid T)
    (decode_inv : CacheDecode -> Prop)
  : (fun Source_Predicate View_Predicate view format decode =>
       @CorrectDecoder S T cache V monoid Source_Predicate View_Predicate
                                view format decode decode_inv)
    with signature (pointwise_relation _ iff
                                       --> pointwise_relation _ (flip impl)
                                       --> pointwise_relation _ (pointwise_relation _ (flip impl))
                                       --> EquivFormat
                                       --> pointwise_relation _ (pointwise_relation _ eq)
                                       --> EquivFormat
                                       --> impl)
      as format_decode_correct_alt'.
Proof.
  unfold EquivFormat, impl, pointwise_relation, CorrectDecoder; intros.
  intuition eauto; intros.
  - setoid_rewrite H3.
    eapply H2 in H9.
    eapply H6 in H9.
    destruct_ex; split_and;
      eexists _, _; intuition eauto.
    eapply H4; eauto.
    eauto.
    eauto.
    eapply H; eauto.
  - eapply H7; eauto.
    rewrite <- H3; eauto.
  - rewrite H3 in H9.
    eapply H7 in H8; eauto.
    split_and; destruct_ex; split_and; subst.
    eexists _, _; intuition eauto.
    eapply H4; eauto.
Qed.

Lemma weaken_view_pred
      S T V
    (cache : Cache)
    (monoid : Monoid T)
    (decode_inv : CacheDecode -> Prop)
    (View_Predicate : V -> Prop)
    (view : S -> V -> Prop)
    (format : FormatM S T)
    decode
    (Source_Predicate : S -> Prop)
    (View_Predicate_OK : forall s v,
        Source_Predicate s ->
        view s v ->
        View_Predicate v)
  : forall x y : V -> CacheFormat -> T * CacheFormat -> Prop,
    (forall (a : V) (a0 : CacheFormat) (a1 : T * CacheFormat),
        View_Predicate a -> x a a0 a1 -> y a a0 a1) ->
  CorrectDecoder monoid Source_Predicate View_Predicate view format decode decode_inv x ->
  CorrectDecoder monoid Source_Predicate View_Predicate view format decode decode_inv y.
Proof.
  Local Transparent CorrectDecoder.
  unfold CorrectDecoder.
  intuition eauto; intros.
  - eapply H1 in H4.
    destruct_ex; split_and.
    rewrite H5; eexists _, _; intuition eauto.
    apply unfold_computes; eapply H; eauto.
    all: eauto.
  - eapply H2 in H4; intuition eauto.
  - eapply H2 in H4; intuition eauto.
    destruct_ex; split_and; subst; eexists _, _; intuition eauto.
    apply unfold_computes; eapply H; eauto.
Qed.

Section DecodeWMeasure.
  Context {S : Type}. (* s type *)
  Context {T : Type}. (* t type *)
  Context {cache : Cache}.
  Context {monoid : Monoid T}.

  Variable format_S : S -> CacheFormat -> Comp (T * CacheFormat).
  Variable S_decode : T -> CacheDecode -> Hopefully (S * T * CacheDecode).

  Definition Decode_w_Measure_lt
             (b : T)
             (cd : CacheDecode)
             (S_decode_lt
              : forall  (b : T)
                        (cd : CacheDecode)
                        (a : S)
                        (b' : T)
                        (cd' : CacheDecode),
                 S_decode b cd = Ok (a, b', cd')
                 -> lt_B b' b)
    : Hopefully (S * {b' : T | lt_B b' b} * CacheDecode).
    generalize (S_decode_lt b cd); clear.
    destruct (S_decode b cd) as [ [ [ a b' ] cd' ] | ]; intros;
      [ refine (Ok (a, exist _ b' (H _ _ _ eq_refl), cd'))
      | exact (Error (LabelError "Measure error lt" UnknownError)) ]. 
  Defined.

  Lemma Decode_w_Measure_lt_eq
        (b : T)
        (cd : CacheDecode)
        (S_decode_lt
         : forall  (b : T)
                   (cd : CacheDecode)
                   (a : S)
                   (b' : T)
                   (cd' : CacheDecode),
            S_decode b cd = Ok (a, b', cd')
            -> lt_B b' b)
    : forall a' b' cd',
      S_decode b cd = Ok (a', b', cd')
      -> exists pf,
        Decode_w_Measure_lt b cd S_decode_lt =
        Ok (a', exist _ b' pf , cd').
  Proof.
    clear; intros; unfold Decode_w_Measure_lt.
    remember (S_decode_lt b cd); clear Heql.
    destruct (S_decode b cd) as [ [ [? ?] ? ] | ].
    injections; eauto.
    discriminate.
  Qed.

  Lemma Decode_w_Measure_lt_eq'
        (b : T)
        (cd : CacheDecode)
        (S_decode_lt
         : forall  (b : T)
                   (cd : CacheDecode)
                   (a : S)
                   (b' : T)
                   (cd' : CacheDecode),
            S_decode b cd = Ok (a, b', cd')
            -> lt_B b' b)
    : is_error (S_decode b cd)
      -> is_error (Decode_w_Measure_lt b cd S_decode_lt).
  Proof.
    clear; intros; unfold Decode_w_Measure_lt.
    remember (S_decode_lt b cd); clear Heql.
    destruct (S_decode b cd) as [ [ [? ?] ? ] | ]; eauto.
    
  Qed.

  Definition Decode_w_Measure_le
             (b : T)
             (cd : CacheDecode)
             (S_decode_le
              : forall  (b : T)
                        (cd : CacheDecode)
                        (a : S)
                        (b' : T)
                        (cd' : CacheDecode),
                 S_decode b cd = Ok (a, b', cd')
                 -> le_B b' b)
    : Hopefully (S * {b' : T | le_B b' b} * CacheDecode).
    generalize (S_decode_le b cd); clear.
    destruct (S_decode b cd) as [ [ [ a b' ] cd' ] | ]; intros;
      [ refine (Ok (a, exist _ b' (H _ _ _ eq_refl), cd'))
      | exact (Error (LabelError "Measure error le" UnknownError)) ].
  Defined.

  Lemma Decode_w_Measure_le_eq
        (b : T)
        (cd : CacheDecode)
        (S_decode_le
         : forall  (b : T)
                   (cd : CacheDecode)
                   (a : S)
                   (b' : T)
                   (cd' : CacheDecode),
            S_decode b cd = Ok (a, b', cd')
            -> le_B b' b)
    : forall a' b' cd',
      S_decode b cd = Ok (a', b', cd')
      -> exists pf,
        Decode_w_Measure_le b cd S_decode_le =
        Ok (a', exist _ b' pf , cd').
  Proof.
    clear; intros; unfold Decode_w_Measure_le.
    remember (S_decode_le b cd); clear Heql.
    destruct (S_decode b cd) as [ [ [? ?] ? ] | ].
    injections; eauto.
    discriminate.
  Qed.

  Lemma Decode_w_Measure_le_eq'
        (b : T)
        (cd : CacheDecode)
        (S_decode_le
         : forall  (b : T)
                   (cd : CacheDecode)
                   (a : S)
                   (b' : T)
                   (cd' : CacheDecode),
            S_decode b cd = Ok (a, b', cd')
            -> le_B b' b)
    : is_error (S_decode b cd)
      -> is_error (Decode_w_Measure_le b cd S_decode_le).
  Proof.
    clear; intros; unfold Decode_w_Measure_le.
    remember (S_decode_le b cd); clear Heql.
    destruct (S_decode b cd) as [ [ [? ?] ? ] | ]; eauto.
    
  Qed.

  Lemma Decode_w_Measure_le_eq'':
    forall (b : T) (cd : CacheDecode)
           (S_decode_le : forall (b0 : T) (cd0 : CacheDecode) (a : S) (b' : T) (cd' : CacheDecode),
               S_decode b0 cd0 = Ok (a, b', cd') -> le_B b' b0),
      is_error (Decode_w_Measure_le b cd S_decode_le) ->
      is_error (S_decode b cd).
  Proof.
    clear; intros ? ? ?; unfold Decode_w_Measure_le in *.
    remember (S_decode_le b cd); clear Heql.
    destruct (S_decode b cd) as [ [ [? ?] ? ] | ]; eauto.
    
  Qed.

  Lemma Decode_w_Measure_lt_eq'':
    forall (b : T) (cd : CacheDecode)
           (S_decode_lt : forall (b0 : T) (cd0 : CacheDecode) (a : S) (b' : T) (cd' : CacheDecode),
               S_decode b0 cd0 = Ok (a, b', cd') -> lt_B b' b0),
      is_error (Decode_w_Measure_lt b cd S_decode_lt) ->
      is_error (S_decode b cd).
  Proof.
    clear; intros ? ? ?; unfold Decode_w_Measure_lt in *.
    remember (S_decode_lt b cd); clear Heql.
    destruct (S_decode b cd) as [ [ [? ?] ? ] | ]; eauto.
    
  Qed.

End DecodeWMeasure.

Global Unset Implicit Arguments.

Definition CorrectDecoderFor {S T} {cache : Cache}
           {monoid : Monoid T} Invariant FormatSpec :=
  { decodePlusCacheInv : (T -> CacheDecode -> Hopefully (S * T * CacheDecode)) * (CacheDecode -> Prop) * ((CacheDecode -> Prop) -> Prop)
    | (cache_inv_Property (snd (fst decodePlusCacheInv)) (snd decodePlusCacheInv)
     -> CorrectDecoder (S := S) monoid Invariant Invariant eq
                                FormatSpec
                                (fst (fst decodePlusCacheInv))
                                (snd (fst decodePlusCacheInv)) FormatSpec)
    /\ cache_inv_Property (snd (fst decodePlusCacheInv)) (snd decodePlusCacheInv)}.

Definition CorrectEncoderFor {S T} {cache : Cache}
      {monoid : Monoid T} FormatSpec :=
  { encoder' : EncodeM S T & forall a env,
        (forall benv', encoder' a env = Ok benv' ->
                       refine (FormatSpec a env) (ret benv'))
        /\ (is_error (encoder' a env) ->
            forall benv', ~ computes_to (FormatSpec a env) benv')}.

(* Here are the expected correctness lemmas for synthesized functions. *)
Lemma CorrectDecodeEncode
      {S T} {cache : Cache}
      {monoid : Monoid T}
  : forall Invariant
           (FormatSpec : FormatM S T)
           (encoder : CorrectEncoderFor FormatSpec)
           (decoder : CorrectDecoderFor Invariant FormatSpec),
    forall a envE envD b envE',
      Equiv envE envD
      -> Invariant a
      -> snd (fst (proj1_sig decoder)) envD
      -> projT1 encoder a envE = Ok (b, envE')
      -> exists envD',
          fst (fst (proj1_sig decoder)) b envD = Ok (a, mempty, envD').
Proof.
  intros.
  destruct encoder as [encoder encoder_OK].
  destruct decoder as [ [ [decoder Inv] P_env] [decoder_OK Inv_cd] ]; simpl in *.
  specialize (proj1 (encoder_OK a envE) _ H2); intro.
  specialize (decoder_OK Inv_cd).
  destruct decoder_OK as [decoder_OK _].
  unfold cache_inv_Property in Inv_cd.
  eapply decoder_OK  with (ext := mempty) in H3; eauto.
  destruct_ex; intuition.
  subst; rewrite mempty_right in H4; eauto.
Qed.

Lemma CorrectEncodeDecode
      {S T}
      {cache : Cache}
      {monoid : Monoid T}
  : forall Invariant
           (FormatSpec : FormatM S T)
           (decoder : CorrectDecoderFor Invariant FormatSpec),
    forall bs ce cd cd' s ext,
      Equiv ce cd
      -> snd (fst (proj1_sig decoder)) cd
      -> fst (fst (proj1_sig decoder)) bs cd = Ok (s, ext, cd')
      -> Invariant s /\
         exists ce' bs',
           bs = mappend bs' ext
           /\ Equiv ce' cd' /\ FormatSpec s ce (bs', ce').
Proof.
  intros.
  destruct decoder as [ [ [decoder Inv] P_env] [decoder_OK Inv_cd] ]; simpl in *.
  specialize (decoder_OK Inv_cd).
  destruct decoder_OK as [_ decoder_OK].
  eapply decoder_OK in H1; eauto.
  intuition; destruct_ex; intuition eauto.
Qed.

Lemma Start_CorrectDecoderFor
      {S T} {cache : Cache}
      {monoid : Monoid T}
      Invariant
      FormatSpec
      (decoder decoder_opt : T -> CacheDecode -> Hopefully (S * T * CacheDecode))
      (cache_inv : CacheDecode -> Prop)
      (P_inv : (CacheDecode -> Prop) -> Prop)
      (decoder_OK :
         cache_inv_Property cache_inv P_inv
         -> CorrectDecoder monoid Invariant Invariant
                           eq FormatSpec decoder cache_inv FormatSpec)
      (cache_inv_OK : cache_inv_Property cache_inv P_inv)
      (decoder_opt_OK : forall b cd, decoder b cd = decoder_opt b cd)
  : @CorrectDecoderFor S T cache monoid Invariant FormatSpec.
Proof.
  exists (decoder_opt, cache_inv, P_inv); split; simpl; eauto.
  unfold CorrectDecoder in *; intuition; intros.
  - destruct (H1 _ _ _ _ _ ext env_OK H0 H3 H4).
    rewrite decoder_opt_OK in H5; eauto.
  - rewrite <- decoder_opt_OK in H4; destruct (H2 _ _ _ _ _ _ H0 H3 H4); eauto.
  - rewrite <- decoder_opt_OK in H4; destruct (H2 _ _ _ _ _ _ H0 H3 H4); eauto.
Defined.

(* Shorthand for nondeterministically decoding a value. *)
Definition Pick_Decoder_For
           {S T} {cache : Cache}
           {monoid : Monoid T}
           Invariant
           FormatSpec
           (b : T)
           (ce : CacheFormat)
  := {a : Hopefully S |
      forall a' : S,
        a = Ok a' <->
        (exists b1 b2 (ce' : CacheFormat),
            computes_to (FormatSpec a' ce) (b1, ce')
            /\ b = mappend b1 b2
            /\ Invariant a')}%comp.

Lemma refine_Pick_Decoder_For
      {S T} {cache : Cache}
      {monoid : Monoid T}
      {Invariant}
      {FormatSpec}
      (decoderImpl : @CorrectDecoderFor S T cache monoid Invariant FormatSpec)
  : forall b ce cd,
    Equiv ce cd
    -> snd (fst (proj1_sig decoderImpl)) cd
    -> refine (Pick_Decoder_For Invariant FormatSpec b ce)
              (ret match fst (fst (proj1_sig decoderImpl)) b cd
                   with
                   | Ok (a, _, _) => Ok a
                   | Error e => Error e 
                   end).
Proof.
  intros.
  pose proof (proj2_sig (decoderImpl)).
  cbv beta in H1.
  destruct_ex; intuition.
  destruct H1 as [? ?].
  intros v Comp_v; computes_to_inv; subst;
    apply PickComputes; intros.
  split; intros.
  - destruct (fst (fst (proj1_sig decoderImpl)) b cd) as [ [ [? ?] ?] | ] eqn: ?; try discriminate.
    injections.
    eapply H2 in Heqh; eauto.
    destruct Heqh as [? [? [? [? ?] ] ] ].
    intuition.
    subst.
    eexists _, _, _ ; split; eauto.
  - destruct_ex; intuition; subst.
    eapply H1 in H5; eauto.
    destruct_ex; intuition.
    rewrite H5; simpl; congruence.
Qed.

Notation "a ∋ b" := (@computes_to _ a b) (at level 65) : format_scope.
Notation "a ∌ b" := (~ @computes_to _ a b) (at level 65) : format_scope.

(* Nicer notation for formating constants *)
Notation "'constant' n" := (fun _ => n) (at level 20) : format_scope.
