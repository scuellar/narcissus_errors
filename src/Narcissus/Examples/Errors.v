Require Import Fiat.Narcissus.Examples.TutorialPrelude.

Set Warnings "-local-declaration".
Set Nested Proofs Allowed.
Opaque format_label.

(** Some Hacks*)
Definition fake_label {T} (_ : string) (x: T):= x.
Transparent fake_label.
Arguments fake_label /. (* ^ Tells coq to unfold even when applied to no arguments. *)  
Infix "#":= format_label (at level 56).
Infix "##":= fake_label (at level 56). (* ^ This is to pretend we can
use labels everywhere, where in reality the sequence rule doens't work
yet. So `label1 # p1 ++ label2 p2` doesn't work *)

(*Pretty printing ERRORS*)
Declare Scope pretty.

Notation "'Execution_stopped_because_of_an_error:' e" :=
  (Error e) (at level 100, only printing, format
            "'//' 'Execution_stopped_because_of_an_error:' '/    ' e " ): pretty.
(** End Hacks*) 

Notation "'Unknown_Error'" := UnknownError (at level 10, only printing): pretty.
Notation "'Other_Error'" := OtherError (at level 10, only printing): pretty.
Notation "'ERROR_End_of_buffer'" := EndOfBuffer (at level 10, only printing): pretty.
Notation "e '----' 'while_processing:' label" :=
  (LabelError label e) (at level 25, only printing, left associativity, format
   "'[    ' e '//' '----' '//' '[    ' 'while_processing:' label ']' ']'"
                                                      ): pretty.
Notation "e 'Extra_Info:' info" :=
  (InfoError info e) (at level 25, only printing, left associativity, format
   "'[' e '//' 'Extra_Info:' info ']'"
): pretty.

















Module ErrorSensor.

  Let kind :=
      EnumType ["TEMPERATURE"; "HUMIDITY"].
  
  Record sensor_msg :=
    { stationID: word 8; data: (kind * word 14) }.

  Let format: FormatM sensor_msg ByteString :=
        "Sensor Message" #
                         ("ID" ## format_word ◦ stationID 
                          ++ format_unused_word 8
                          ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
                          ++ "Data"    #
                                      (format_enum [WO~0~0; WO~0~1] ◦ fst ◦ data
                                       ++ format_word ◦ snd ◦ data)
                         ).
  Let invariant (msg: sensor_msg) :=
        True.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined. (*Takes a bit longer, needs optimizing. *)
  (* `enc_dec` Still depends on the following unproven lemmas:
      - tag_decode_simple_correct 
      - Append_EncodeMEquivAlignedEncodeM
      - AlignedDecodeTag


     Use : `Print Assumptions enc_dec.`
   *)

  
  Open Scope pretty. (* Comment out to remove pretty printing*)
  
  Let encode := encoder_impl enc_dec.
  Let decode := decoder_impl enc_dec.
  Definition my_encode_message n:= encode _
    {|
      stationID := WO~0~0~0~0~0~1~1~1;
      data := (Fin.F1, WO~1~0~1~0~1~0~0~0~0~0~0~0~0~0)
    |} (initialize_Aligned_ByteString n).
  Compute (my_encode_message 4). (* ^ Errors with <6 *)
  
  
  Definition my_decoded_message :=
    decode _
           ([WO~0~0~0~0~0~1~1~1; WO~0~0~0~0~0~0~0~0; WO~0~0~0~0~0~1~1~1;
             WO~1~1~1~0~0~0~1~0; WO~0~0~1~0~1~0~1~0; WO~0~0~0~0~0~0~0~0]).
  Compute my_decoded_message.

  (*Length error*)
  Definition my_bad_decoded_message1 :=
    decode _
           ([WO~0~0~0~0~0~1~1~1; WO~0~0~0~0~0~0~0~0; WO~0~0~0~0~0~1~1~1;
             WO~1~1~1~0~0~0~1~0; WO~0~1~1~0~1~0~1~0]).
  Compute my_bad_decoded_message1.

  (*Enum error: the 5th byte should be `00` or `01`*)
  Definition my_bad_decoded_message2 :=
    decode _
           ([WO~0~0~0~0~0~1~1~1; WO~0~0~0~0~0~0~0~0; WO~0~0~0~0~0~1~1~1;
             WO~1~1~1~0~0~0~1~0; WO~1~1~1~0~1~0~1~0; WO~0~0~0~0~0~0~0~0]).
  Compute my_bad_decoded_message2.

  
  (* Error in the ID : The sequence rule is *not* yet implemented. So
  this example won't show the right error. An empty array should fail
  and the stack traceback should show the ID. Howevere the ID label is
  fake (using double tags `##`) and doesn't do anything. Use this
  example to check when the sequence rule for labels is implemented.
  *)
  Definition my_bad_decoded_message3 :=
    decode _
           ([]).
  Compute my_bad_decoded_message3.
  

  (* Wrong constant word: This shows a current *limitation* of the
     aproach:
     The error will say that the error is in Data, while the
     constant is outside the data field. That's because Narcissus
     pushes binary checks to the end of the parser. So in the current
     state all binary checks will show a "Data" error. Two ways to
     improve it:
     1. Change the way Narcissus pushes binary checks.
     2. Make the binary checks fail with more infomration (carrying
     their entire stack backtrace) and have a mechanism to remove the
     normal backtrace for this cases. *)
  Definition my_bad_decoded_message4 :=
    decode _
           ([WO~0~0~0~0~0~1~1~1; WO~0~0~0~0~0~0~0~0; WO~1~1~1~1~1~1~1~1;
             WO~1~1~1~0~0~0~1~0; WO~0~0~1~0~1~0~1~0; WO~0~0~0~0~0~0~0~0]).
  Compute my_bad_decoded_message4.
  
End ErrorSensor.


































Module Sensor3.
  Record sensor_msg :=
    { stationID: word 8; data: list (word 16) }.

  Let format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_list format_word ◦ data.

  Let invariant (msg: sensor_msg) :=
    True.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof.
    derive_encoder_decoder_pair.
    last_failing_goal.
    all:simpl.
  Abort.
End Sensor3.

(** The derivation fails, leaving multiple Coq goals unsolved.  We forgot to encode the length of the `data` list, and this prevents Narcissus from generating a decoder.  Our attempted fix, unfortunately, only gets us half of the way there (`format_nat 8 ◦ length` specifies that the length of the list should be truncated to 8 bits and written out): **)

Module Sensor4.
  Record sensor_msg :=
    { stationID: word 8; data: list (word 16) }.

  Let format :=
       format_word ◦ stationID
    ++ format_nat 8 ◦ length ◦ data
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_list format_word ◦ data.

  Let invariant (msg: sensor_msg) :=
    True.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair.
         last_failing_goal.
         all:simpl.
  Abort.
End Sensor4.

(** Again, decoder generation fails and produces an unsolvable goal. The problem is that, since we encode the list's length on 8 bits, the round-trip property that Narcissus attempts to prove only holds if the list has less than \(2^{8}\) elements: larger lists have their length truncated, and it becomes impossible for the decoder to know for cetain how many elements it should decode.  What we need is an input restriction: a predicate defining which messages we may encode; to this end, we update our example as follows:
**)

Module Sensor5.
  Record sensor_msg :=
    { stationID: word 8; data: list (word 16) }.

  Let format :=
       format_word ◦ stationID
    ++ format_nat 8 ◦ length ◦ data
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_list format_word ◦ data.

  Let invariant :=
    fun (msg: sensor_msg) =>
      length (msg.(data)) < pow2 8.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined.

  Let encode := encoder_impl enc_dec.
  (* fun (sz : nat) (r : sensor_msg) (v : ByteBuffer.t sz) =>
     (stationID ⋙ SetCurrentByte ≫
      data ⋙ Datatypes.length ⋙ natToWord 8 ⋙ SetCurrentByte ≫
      const WO~0~0~0~0~0~1~1~1 ⋙ SetCurrentByte ≫
      const WO~1~1~1~0~0~0~1~0 ⋙ SetCurrentByte ≫
      data ⋙ AlignedEncodeList (fun n : nat => low_bits 8 ⋙ SetCurrentByte ≫
                                               shift_right 8 ⋙ SetCurrentByte) sz) v 0 r tt *)

  Let decode := decoder_impl enc_dec.
  (* fun (sz : nat) (v : ByteBuffer.t sz) =>
     (b <- GetCurrentByte;
      b0 <- GetCurrentByte;
      b1 <- GetCurrentByte;
      b' <- GetCurrentByte;
      w <- return b1⋅b';
      (if weq w WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
       then
        l <- ListAlignedDecodeM
               (fun numBytes : nat =>
                w0 <- GetCurrentByte;
                w' <- w1 <- GetCurrentByte;
                      w' <- return WO;
                      return w1⋅w';
                return w0⋅w') (wordToNat b0);
        return {| stationID := b; data := l |}
       else fail)) v 0 tt *)
End Sensor5.

Module Sensor6.

  Inductive reading :=
  | Temperature (_ : word 14)
  | Humidity (_ : word 14).

  Let format_reading m s :=
    match m with
    | Temperature t => ret (serialize (Word.combine WO~0~0 t) s)
    | Humidity h => ret (serialize (Word.combine WO~0~1 h) s)
    end.

  Let enc_reading sz :=
    (fun buf idx m => @SetCurrentBytes _ _ sz 2 buf idx match m with
         | Temperature t => Word.combine WO~0~0 t
         | Humidity h => Word.combine WO~0~1 h
         end).

  Lemma enc_readingCorrect
    : CorrectAlignedEncoder format_reading enc_reading.
  Proof.
    unfold enc_reading, format_reading.
    eapply refine_CorrectAlignedEncoder.
    2: eapply CorrectAlignedEncoderForFormatMChar_f; eauto.
    intros; destruct s; simpl;
      rewrite refine_Projection_Format;
      split; try reflexivity;
        intros; eapply format_word_inhabited'; intros; eauto.
  Qed.

  Let dec_reading :=
    fun t ctx =>
    `(w, rest, ctx') <- decode_word t ctx;
      if weqb (split1 2 14 w) WO~0~0
      then Some (Temperature (split2 2 14 w), rest, ctx')
      else (if weqb (split1 2 14 w) WO~0~1 then
              Some (Humidity (split2 2 14 w), rest, ctx')
            else None).

  Transparent weqb.

  Lemma dec_readingCorrect
    : CorrectDecoder _ (fun _ => True) (fun _ => True) eq format_reading dec_reading (fun _ => True)
                     format_reading.
  Proof.
    eapply format_decode_correct_EquivFormatAndView
        with (fun m => format_word (match m with
                                 | Temperature t => Word.combine WO~0~0 t
                                 | Humidity h => Word.combine WO~0~1 h
                                 end)); eauto.
    unfold flip, EquivFormat, format_reading. intros; destruct s; reflexivity.

    apply_bijection_rule' with (fun w =>
                                  if weqb (split1 2 14 w) WO~0~0
                                  then Some (Temperature (split2 2 14 w))
                                  else (if weqb (split1 2 14 w) WO~0~1 then
                                          Some (Humidity (split2 2 14 w))
                                        else None));
      intuition eauto.
    - apply Word_decode_correct. try apply unfold_cache_inv_Property; intuition eauto.
    - destruct s; simpl; rewrite split2_combine; auto.
    - destruct weqb eqn:?; injections. apply weqb_true_iff in Heqb.
      rewrite <- Heqb. apply Word.combine_split.
      destruct (weqb _ WO~0~1) eqn:?; try discriminate; injections. apply weqb_true_iff in Heqb0.
      rewrite <- Heqb0. apply Word.combine_split.
    - intuition eauto.
    - derive_decoder_equiv; easy.
  Qed.

  Opaque weqb.
  Record sensor_msg :=
    { stationID: word 8; data: list reading }.

  Let format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_nat 8 ◦ length ◦ data
    ++ format_list format_reading ◦ data.

  Let invariant :=
    fun (msg: sensor_msg) =>
      length (msg.(data)) < pow2 8.

  Ltac new_encoder_rules ::= apply enc_readingCorrect.
  Ltac apply_new_base_rule ::= apply dec_readingCorrect.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair.
  Defined.

  Let encode := encoder_impl enc_dec.
  Let decode := decoder_impl enc_dec.

End Sensor6.
