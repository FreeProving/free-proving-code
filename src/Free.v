Require Export FunctionalExtensionality.
Require Export Program.Equality.

Require Export FreeProving.Base.

Set Implicit Arguments.

Section Free.

  Variable F : Type -> Type.

  Inductive Free (C__F : Container F) A :=
  | pure : A -> Free C__F A
  | impure : Ext Shape Pos (Free C__F A) -> Free C__F A.

End Free.

Arguments pure [_] [_] [_] _.

Section Free_Rect.

  Variable F : Type -> Type.
  Variable C__F : Container F.
  Variable A : Type.
  Variable P : Free C__F A -> Type.

  Variable Pure_rect : forall (x : A), P (pure x).
  Variable Impure_rect : forall (s : Shape) (pf : Pos s -> Free C__F A),
      (forall p, P (pf p)) -> P (impure (ext s pf)).

  Fixpoint Free_Rect (fx : Free C__F A) : P fx :=
    match fx with
    | pure x => Pure_rect x
    | impure (ext s pf) =>
      Impure_rect s pf (fun p : Pos s => Free_Rect (pf p))
    end.

End Free_Rect.

Section Free_Ind.

  Variable F : Type -> Type.
  Variable C__F : Container F.
  Variable A : Type.
  Variable P : Free C__F A -> Prop.

  Variable Pure_ind : forall (x : A), P (pure x).
  Variable Impure_ind : forall (s : Shape) (pf : Pos s -> Free C__F A),
      (forall p, P (pf p)) -> P (impure (ext s pf)).

  Definition Free_Ind (fx : Free C__F A) : P fx := Free_Rect P Pure_ind Impure_ind fx.

End Free_Ind.

Section MonadInstance.

  Variable F : Type -> Type.
  Variable C__F : Container F.

  Definition cmap A B (f : A -> B) (x : Ext Shape Pos A) : Ext Shape Pos B :=
    match x with
    | ext s pf => ext s (fun x => f (pf x))
    end.

  Section fbind.

    Variable A B: Type.
    Variable f: A -> Free C__F B.

    Fixpoint free_bind' (ffA: Free C__F A) :=
      match ffA with
      | pure x => f x
      | impure e => impure (cmap free_bind' e)
      end.

  End fbind.

  Definition free_bind A B (ffA: Free C__F A) (f: A -> Free C__F B) : Free C__F B :=
    free_bind' f ffA.

  Notation "mx >>= f" := (free_bind mx f) (at level 50, left associativity).
  Notation "'do' x <- mx ; f" :=
    (free_bind mx (fun x => f))
      (at level 50, x ident, mx at level 40, f at level 50).

  Lemma pure_bind :
    forall A B (x: A) (f: A -> Free C__F B), pure x >>= f = f x.
  Proof.
    reflexivity.
  Qed.

  Lemma bind_pure :
    forall A (fA: Free C__F A), fA >>= (fun x => pure x) = fA.
  Proof.
    induction fA using Free_Ind.
    - reflexivity.
    - simpl free_bind.
      repeat apply f_equal.
      apply functional_extensionality.
      apply H.
  Qed.

  Lemma free_bind_assoc :
    forall A B C (fa : Free C__F A) (f: A -> Free C__F B) (g: B -> Free C__F C),
      fa >>= (fun y => f y >>= g) = fa >>= f >>= g.
  Proof.
    intros.
    induction fa using Free_Ind.
    - econstructor.
    - simpl free_bind.
      repeat apply f_equal.
      apply functional_extensionality.
      apply H.
  Qed.

  Global Instance free_monad : Monad (Free C__F) :=
    {
      ret := @pure F C__F;
      bind := fun _ _ xs f => free_bind xs f;
      left_unit := pure_bind;
      right_unit := bind_pure;
      bind_assoc := free_bind_assoc
    }.

End MonadInstance.
Arguments cmap [_] [_] [_] [_].

Notation "mx >>= f" := (free_bind mx f) (at level 50, left associativity).
Notation "'do' x <- mx ; f" :=
  (free_bind mx (fun x => f))
    (at level 50, x ident, mx at level 40, f at level 50).

Section ForFree.

  Variable F : Type -> Type.
  Variable C__F : Container F.

  Inductive ForFree A (P : A -> Prop) : Free C__F A -> Prop :=
  | For_pure : forall (x : A), P x -> ForFree P (pure x)
  | For_impure : forall (s : Shape) (pf : Pos s -> Free C__F A),
      (forall p, ForFree P (pf p)) -> ForFree P (impure (ext s pf)).

  Lemma ForFree_bind :
    forall A B (fx : Free C__F A) (f: A -> Free C__F B) (g: A -> Free C__F B),
      ForFree (fun x => f x = g x) fx -> fx >>= f = fx >>= g.
  Proof.
    intros.
    induction H; simpl.
    - apply H.
    - repeat apply f_equal.
      apply functional_extensionality; intros.
      apply H0.
  Qed.

  Inductive InFree A : A -> Free C__F A -> Prop :=
  | In_Pure : forall x, InFree x (pure x)
  | In_Impure: forall x (s : Shape) (pf : Pos s -> Free C__F A),
      (exists p, InFree x (pf p)) -> InFree x (impure (ext s pf)).

  Lemma ForFree_forall :
    forall A (P : A -> Prop) (fx : Free C__F A),
      ForFree P fx <-> (forall (x : A), InFree x fx -> P x).
  Proof.
    intros A P fx.
    intuition.
    - induction H.
      + inversion H0; subst; assumption.
      + dependent destruction H0. destruct H0.
        apply H1 with (p := x0). apply H0.
    - induction fx using Free_Ind; simpl.
      + apply For_pure. apply H. apply In_Pure.
      + apply For_impure. intros p. apply H0. intros x HIn.
        apply H. apply In_Impure. exists p. apply HIn.
  Qed.

End ForFree.

Section Fold.

  Variable F : Type -> Type.
  Variable C__F : Container F.
  Variable F__F : Functor F.

  Fixpoint fold_free A B (pur : A -> B) (imp : F B -> B) (fx : Free C__F A) : B :=
    match fx with
    | pure x => pur x
    | impure e => imp (to (cmap (fold_free pur imp) e))
    end.

  Variable M : Type -> Type.
  Variable M__M : Monad M.

  Definition induce A (f : forall X, F X -> M X) (fx : Free C__F A) : M A :=
    fold_free (fun x => ret x) (fun x => join (f (M A) x)) fx.

End Fold.

Arguments induce [_] [_] [_] [_] [_].

Module Tactics.

  Ltac simplifyInductionHypothesis ident1 ident2 :=
  match goal with
  | [ ident1 : ForFree ?P (pure _) |- _ ] => inversion ident1 as [ Heq ident2 |]; clear ident1; subst
  | [ ident1 : ForFree ?P (impure (ext ?s ?pf)) |- _ ] =>
    dependent destruction ident1;
    match goal with
    | [ H1 : forall p, ForFree ?P (?pf p), H0 : forall p, ForFree _ (?pf p) -> _ = _ |- _ ] =>
      injection (H0 p (H1 p)) as IH; clear H1; clear H0
    end
  end.

  Tactic Notation "simplify" ident(H) "as" ident(IH) := (simplifyInductionHypothesis H IH).

End Tactics.
