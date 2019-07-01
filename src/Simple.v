Require Import FreeProving.Free.
Require Import FreeProving.Primitives.

Set Implicit Arguments.

Definition Simple (C : Container) : Prop :=
  forall (s : Shape) (p : Pos s), False.

Lemma None_Simple :
  Simple C__None.
Proof.
  intros s. destruct s.
Qed.

Lemma Partial_Simple :
  Simple C__Partial.
Proof.
  intros s p. destruct p.
Qed.

Lemma Error_Simple :
  Simple C__Error.
Proof.
  intros s p. destruct p.
Qed.

Open Scope string_scope.

Lemma Trace_not_Simple :
  not (Simple C__Trace).
Proof.
  intros HSimple.
  specialize (HSimple "debug" tt).
  apply HSimple.
Qed.

Close Scope string_scope.

Lemma ND_not_Simple :
  not (Simple C__ND).
Proof.
  intros HSimple.
  specialize (HSimple tt false).
  apply HSimple.
Qed.

Section Propositions.

  Variable C : Container.

  Lemma selfAnd_identity__Simple :
    Simple C -> forall (fb : Free C Bool), selfAnd fb = fb.
  Proof.
    intros HSimple fb.
    unfold selfAnd.
    destruct fb as [ b | [ s pf ] ]; simpl.
    (* [fb = pure b] *)
    - destruct b; reflexivity.
    (* [fb = impure (ext s pf)] *)
    - do 2 f_equal.
      extensionality p.
      specialize (HSimple s p).
      inversion HSimple.
  Qed.

  Lemma eq_impure :
    Simple C -> forall a (s : Shape) (pf1 pf2 : Pos s -> Free C a),
      impure (ext s pf1) = impure (ext s pf2).
  Proof.
    intros HSimple A s pf1 pf2.
    do 2 f_equal.
    extensionality p.
    specialize (HSimple s p).
    inversion HSimple.
  Qed.

  Lemma selfAnd_identity_improved__Simple :
    Simple C -> forall (fb : Free C Bool), selfAnd fb = fb.
  Proof.
    intros HSimple fb.
    destruct fb as [ b | [ s pf ] ]; simpl.
    (* [fb = pure b] *)
    - destruct b; reflexivity.
    (* [fb = impure (ext s pf)] *)
    - apply (eq_impure HSimple).
  Qed.

  Lemma selfAnd_identity_Simple:
    (forall fb, selfAnd fb = fb) -> Simple C.
  Proof.
    intros Heq s p.
    specialize (Heq (impure (ext s (fun p => pure True_)))).
    dependent destruction Heq.
    apply equal_f with (x0 := p) in x.
    inversion x.
  Qed.

End Propositions.
