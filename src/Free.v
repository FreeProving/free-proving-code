Require Export FunctionalExtensionality.
Require Export Program.Equality.

Require Export FreeProving.Base.
Require Import FreeProving.Classes.

Set Implicit Arguments.
Unset Elimination Schemes.

Section Free.

  Inductive Free (C : Container) (A : Type) : Type :=
  | pure : A -> Free C A
  | impure : Ext C (Free C A) -> Free C A.

End Free.

Arguments pure [_] [_] _.
Arguments impure [_] [_].

Section Free_Principles.

  Variable C : Container.

  Section Free_Rect.

    Variable A : Type.
    Variable P__rect : Free C A -> Type.
    Variable Pure_rect : forall (x : A), P__rect (pure x).
    Variable Impure_rect : forall (s : Shape) (pf : Pos s -> Free C A),
        (forall p, P__rect (pf p)) -> P__rect (impure (ext s pf)).

    Fixpoint Free_Rect (fx : Free C A) : P__rect fx :=
      match fx with
      | pure x => Pure_rect x
      | impure (ext s pf) =>
        Impure_rect s pf (fun p : Pos s => Free_Rect (pf p))
      end.

  End Free_Rect.

  Section Free_Ind.

    Variable A : Type.
    Variable P__ind : Free C A -> Prop.
    Variable Pure_ind : forall (x : A), P__ind (pure x).
    Variable Impure_ind : forall (s : Shape) (pf : Pos s -> Free C A),
        (forall p, P__ind (pf p)) -> P__ind (impure (ext s pf)).

    Check Pure_ind.

    Definition Free_ind (fx : Free C A) : P__ind fx :=
      Free_Rect P__ind Pure_ind Impure_ind fx.

  End Free_Ind.

End Free_Principles.

Section Free_Instances.
  Variable C : Container.

  Section FunctorInstance.

    Section fmap.

      Variable A B : Type.
      Variable f : A -> B.

      Fixpoint freeMap (fx : Free C A) :=
        match fx with
        | pure x => pure (f x)
        | impure (ext s pf) => impure (ext s (fun p => freeMap (pf p)))
        end.

    End fmap.

  End FunctorInstance.

  Section MonadInstance.

    Section fbind.

      Variable A B : Type.
      Variable f : A -> Free C B.

      Fixpoint free_bind' (ffA : Free C A) :=
        match ffA with
        | pure x => f x
        | impure (ext s pf) => impure (ext s (fun p => free_bind' (pf p)))
        end.

    End fbind.

    Definition free_bind (A B : Type) (ffA : Free C A) (f : A -> Free C B) :=
      free_bind' f ffA.

  End MonadInstance.

End Free_Instances.

Module Free_Notation.

  Notation "mx >>= f" := (free_bind mx f) (at level 50, left associativity).
  Notation "'do' x <- mx ; f" :=
    (free_bind mx (fun x => f))
      (at level 50, x ident, mx at level 40, f at level 50).

End Free_Notation.

Section ForFree.

  Import Free_Notation.

  Variable C : Container.

  Inductive ForFree (A : Type) (P : A -> Prop) : Free C A -> Prop :=
  | For_pure : forall (x : A), P x -> ForFree P (pure x)
  | For_impure : forall (s : Shape) (pf : Pos s -> Free C A),
      (forall p, ForFree P (pf p)) -> ForFree P (impure (ext s pf)).

End ForFree.

Section Fold.

  Variable F : Type -> Type.
  Variable C : Container.
  Variable C__Iso : Iso F C.
  Variable F__F : Functor F.

  Fixpoint fold_free A B (pur : A -> B) (imp : F B -> B) (fx : Free C A) : B :=
    match fx with
    | pure x => pur x
    | impure (ext s pf) => imp (to (ext s (fun p => fold_free pur imp (pf p))))
    end.

  Variable M : Type -> Type.
  Variable M__M : Monad M.

  Definition induce A (f : forall X, F X -> M X) (fx : Free C A) : M A :=
    fold_free (fun x => ret x) (fun x => join (f (M A) x)) fx.

End Fold.

Arguments induce [_] [_] [_] [_] [_] [_].

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
