Require Import FreeProving.Free.
Require Import FreeProving.Primitives.
Require Import FreeProving.Simple.

Set Implicit Arguments.

Section GenericDefinitions.
  
  Variable C : Container.

  Definition seq a b (fx : Free C a) (fy : Free C b) : Free C b :=
    fx >>= fun _ => fy.

  Definition Fun C A B := Free C A -> Free C B.

  Definition app a b (ff : Free C (Fun C a b)) (fx : Free C a) :=
    ff >>= fun f => f fx.

  Definition fun1 s : Free C (Fun C Bool Bool) :=
    impure (ext s (fun _ => pure (fun _ => pure True_))).

  Definition fun2 s : Free C (Fun C Bool Bool) :=
    pure (fun _ => impure (ext s (fun _ => (pure True_)))).

End GenericDefinitions.

Arguments fun1 [_].
Arguments fun2 [_].

Infix "$" := app (at level 28, left associativity).

Section EffectDefinitions.

  Definition fun1__Partial : Free C__Partial (Fun C__Partial Bool Bool) :=
  undefined.

  Definition fun2__Partial : Free C__Partial (Fun C__Partial Bool Bool) :=
    pure (fun _ => undefined).

  Definition fun1__Trace : Free C__Trace (Fun C__Trace Bool Bool) :=
    trace "debug" (pure (fun _ => pure True_)).

  Definition fun2__Trace : Free C__Trace (Fun C__Trace Bool Bool) :=
    pure (fun _ => trace "debug" (pure True_)).

  Definition fun1__ND : Free C__ND (Fun C__ND Bool Bool) :=
    choice (pure (fun _ => pure True_)) (pure (fun _ => pure True_)).

  Definition fun2__ND : Free C__ND (Fun C__ND Bool Bool) :=
    pure (fun _ => choice (pure True_) (pure True_)).

End EffectDefinitions.

Section Specification.

  (**
     seq :: a -> b -> b
     seq bot y = bot
     seq x y = y, if x <> bot
   *)

  Example seq_spec1 :
    forall a b (fy : Free C__Partial b),
      seq (@undefined a) fy = undefined.
  Proof.
    intros a b fy.
    apply (eq_impure Partial_Simple).
  Qed.

  Example seq_spec2 :
    forall a b (fx : Free C__Partial a) (fy : Free C__Partial b),
      fx <> undefined -> seq fx fy = fy.
  Proof.
    intros a b fx fy Hundefined.
    destruct fx as [ x | [ [] pf ] ].
    (* [fx = pure x] *)
    - reflexivity.
    (* [fx = impure (ext tt pf)] *)
    - specialize (Hundefined (eq_impure Partial_Simple _ _ _)).
      contradiction.
  Qed.

End Specification.

Example seq_Trace :
  forall a b (x : a) (fy : Free C__Trace b),
    seq (trace "debug" (pure x)) fy = trace "debug" fy.
Proof.
  intros a b x fy.
  reflexivity.
Qed.

Example seq_ND :
  forall a b (x1 x2 x3 : a) (fy : Free C__ND b),
    seq (choice (pure x1) (choice (pure x2) (pure x3))) fy
    = choice fy (choice fy fy).
Proof.
  intros a b x1 x2 x3 fy.
  unfold seq, choice.
  simpl.
  do 2 f_equal.
  extensionality p.
  destruct p.
  (* [p = true] *)
  - reflexivity.
  (* [p = false] *)
  - simpl.
    do 2 f_equal.
    extensionality p.
    destruct p; reflexivity.
Qed.

Section Propositions.

  Example same_result__Partial :
    forall (fb : Free C__Partial Bool), fun1__Partial $ fb = fun2__Partial $ fb.
  Proof.
    intros fb.
    apply (eq_impure Partial_Simple).
  Qed.

  Example distinguish_seq__Partial :
    seq fun1__Partial (pure True_) <> seq fun2__Partial (pure True_).
  Proof.
    intros H.
    inversion H.
  Qed.

  Example same_result__Trace :
    forall (fb : Free C__Trace Bool), fun1__Trace $ fb = fun2__Trace $ fb.
  Proof.
    intros fb.
    simpl.
    unfold trace.
    reflexivity.
  Qed.

  Example distinguish_seq__Trace :
    seq fun1__Trace (pure True_) <> seq fun2__Trace (pure True_).
  Proof.
    intros H.
    inversion H.
  Qed.

  Example same_result__ND :
    forall (fb : Free C__ND Bool), fun1__ND $ fb = fun2__ND $ fb.
  Proof.
    intros fb.
    unfold app.
    simpl.
    unfold choice.
    simpl.
    do 2 f_equal.
    extensionality p.
    destruct p.
    - reflexivity.
    - reflexivity.
  Qed.

  Example distinguish_seq__ND :
    seq fun1__ND (pure True_) <> seq fun2__ND (pure True_).
  Proof.
    intros H.
    inversion H.
  Qed.

  Section generic.
    Variable C : Container.

    Example same_result :
      forall s (fb : Free C Bool), fun1 s $ fb = fun2 s $ fb.
    Proof.
      intros s fb.
      unfold app.
      simpl.
      reflexivity.
    Qed.

    Example distinguish_seq :
      forall s, seq (fun1 s) (pure True_) <> seq (fun2 s) (pure True_).
    Proof.
      intros s H.
      inversion H.
    Qed.

  End generic.

End Propositions.
