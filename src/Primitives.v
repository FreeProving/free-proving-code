Require Import Coq.ZArith.BinInt.

Require Import FreeProving.Free.
Require Export FreeProving.Effects.

Export Free_Notation.
Export Zero.
Export One.
Export Const.
Export Pair.
Export Log.

Set Implicit Arguments.

Section Definitions.

  Variable C : Container.

  Definition Int := Z.

  Inductive Unit :=
  | Unit_ : Unit.

  Inductive Bool :=
  | False_ : Bool
  | True_ : Bool.

End Definitions.

Section Functions.

  Section generic.

    Variable C : Container.

    Definition and (fb1 fb2 : Free C Bool) : Free C Bool :=
      fb1 >>= fun b1 => match b1 with
                     | False_ => pure False_
                     | True_ => fb2
                     end.

    Definition selfAnd (fb : Free C Bool) : Free C Bool :=
      and fb fb.

    Definition selfAnd' (fb : Free C Bool) : Free C Bool :=
      fb >>= fun b => and (pure b) (pure b).
    
    Definition notb (fb : Free C Bool) : Free C Bool :=
      fb >>= fun b => match b with
                   | False_ => pure True_
                   | True_ => pure False_
                   end.

  End generic.

  Definition undefined a : Free C__Partial a :=
    impure (from one).

  Definition error a (msg : string) : Free C__Error a :=
    impure (from (const msg)).

  Definition choice a (x y : Free C__ND a) : Free C__ND a :=
    impure (from (pr x y)).

  Definition trace a (msg : string) (fx : Free C__Trace a) :=
  impure (from (log msg fx)).

End Functions.

Arguments undefined [_].

Section Propositions.

  Lemma notb_involutive__None :
    forall fb : Free C__None Bool, notb (notb fb) = fb.
  Proof.
    intros fb.
    destruct fb as [ b | [ s pf] ].
    (* [fb = pure b] *)
    - destruct b; reflexivity.
    (* [fb = impure (ext s pf)] *)
    - destruct s.
  Qed.

  Lemma notb_involutive__Partial :
    forall fb : Free C__Partial Bool, notb (notb fb) = fb.
  Proof.
    intros fb.
    destruct fb as [ b | [ s pf ] ].
    (* [fb = pure b] *)
    - destruct b; reflexivity.
    (* [fb = impure (ext s pf)] *)
    - simpl.
      do 2 f_equal. extensionality p. destruct p.
  Qed.

  Lemma notb_involutive__Error :
    forall fb : Free C__Error Bool, notb (notb fb) = fb.
  Proof.
    intros fb.
    destruct fb as [ b | [ s pf ] ].
    (* [fb = pure b] *)
    - destruct b; reflexivity.
    (* [fb = impure (ext s pf)] *)
    - simpl.
      do 2 f_equal. extensionality p. destruct p.
  Qed.

  Lemma selfAnd_identity__Partial :
    forall fb : Free C__Partial Bool, selfAnd fb = fb.
  Proof.
    intros fb.
    destruct fb as [ b | [ s pf ] ].
    (* [fb = pure b] *)
    - simpl. destruct b; reflexivity.
    (* [fb = impure (ext s pf)] *)
    - unfold selfAnd; simpl.
      do 2 f_equal. extensionality p. destruct p.
  Qed.

  Lemma selfAnd_identity__Error :
    forall fb : Free C__Error Bool, selfAnd fb = fb.
  Proof.
    intros fb.
    destruct fb as [ b | [ s pf ] ].
    (* [fb = pure b] *)
    - simpl. destruct b; reflexivity.
    (* [fb = impure (ext s pf)] *)
    - unfold selfAnd; simpl.
      do 2 f_equal. extensionality p. destruct p.
  Qed.

  Example trace_twice :
    selfAnd (trace "debug" (pure True_))
    = trace "debug" (trace "debug" (pure True_)).
  Proof.
    reflexivity.
  Qed.

  Section Inequality.

    Example selfAnd_not_identity__ND :
      exists (fb : Free C__ND Bool), selfAnd fb <> fb.
    Proof.
      exists (choice (pure False_) (pure True_)).
      intros Heq. dependent destruction Heq.
      apply equal_f with (x0 := false) in x. inversion x.
    Qed.

    Example selfAnd_not_identity__Trace :
      exists (fb : Free C__Trace Bool), selfAnd fb <> fb.
    Proof.
      exists (trace "debug" (pure True_)).
      intros Heq. dependent destruction Heq.
      apply equal_f with (x0 := tt) in x. inversion x.
    Qed.

  End Inequality.

  Section generic.

    Variable C : Container.

    Lemma notb_involutive :
      forall fb : Free C Bool, notb (notb fb) = fb.
    Proof.
      intros fb.
      induction fb as [ b | s pf IH ].
      (* [fb = pure b] *)
      - destruct b; reflexivity.
      (* [fb = impure (ext s pf)] *)
      - simpl.
        do 2 f_equal. extensionality p.
        apply IH.
    Qed.

    Lemma selfAnd'_identity :
      forall fb : Free C Bool, selfAnd' fb = fb.
    Proof.
      intros fb.
      induction fb as [ b | s pf IH ].
      (* [fb = pure b] *)
      - simpl.
        destruct b; reflexivity.
      (* [fb = impure (ext s pf)] *)
      - simpl.
        do 2 f_equal.
        extensionality p.
        apply IH.
    Qed.

  End generic.

End Propositions.
