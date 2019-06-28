Require Export FreeProving.Free.

Set Implicit Arguments.

Section ListDefinition.

  Variable F : Type -> Type.

  Inductive List (C__F : Container F) A :=
  | nil : List C__F A
  | cons : Free C__F A -> Free C__F (List C__F A) -> List C__F A.

End ListDefinition.

Arguments nil [_] [_] [_].

Section List_ind.

  Variable F : Type -> Type.
  Variable C__F : Container F.

  Variable A : Type.
  Variable P : List C__F A -> Prop.

  Hypothesis nilP : P nil.
  Hypothesis consP : forall (fx: Free C__F A)
                       (fxs : Free C__F (List C__F A)),
      ForFree P fxs -> P (cons fx fxs).

  Fixpoint List_Ind (l : List C__F A) : P l.
  Proof.
    destruct l.
    - apply nilP.
    - apply consP.
      apply ForFree_forall. intros xs HIn.
      induction f0 using Free_Ind.
      + inversion HIn; subst. apply List_Ind.
      + dependent destruction HIn; subst. destruct H0 as [ p ].
        apply H with (p := p). apply H0.
  Defined.

End List_ind.

Section FreeList_rect.

  Variable F : Type -> Type.
  Variable C__F : Container F.
  Variable A : Type.
  Variable PF : Free C__F (List C__F A) -> Type.
  Variable P : List C__F A -> Type.

  Hypothesis NilFP : P nil.
  Hypothesis ConsFP : forall fx fxs, PF fxs -> P (cons fx fxs).
  Hypothesis PureListF : forall xs, P xs -> PF (pure xs).
  Hypothesis ImpureP : forall (s : Shape) (pf : Pos s -> Free C__F (List C__F A)),
      (forall p, PF (pf p)) -> PF (impure (ext s pf)).

  Fixpoint List_Rect (xs: List C__F A) : P xs :=
    let fix aux (fys: Free C__F (List C__F A)) : PF fys :=
        match fys with
        | pure ys => PureListF (List_Rect ys)
        | impure (ext s pf) => ImpureP s pf (fun p => aux (pf p))
        end
    in match xs with
       | nil => NilFP
       | cons fx fxs => ConsFP fx (aux fxs)
       end.

  Fixpoint FreeList_rect (fxs: Free C__F (List C__F A)) : PF fxs :=
    match fxs with
    | pure xs => PureListF (List_Rect xs)
    | impure (ext s pf) => ImpureP s pf (fun p => FreeList_rect (pf p))
    end.

End FreeList_rect.

Section FreeList_ind.

  Variable F : Type -> Type.
  Variable C__F : Container F.
  Variable A : Type.
  Variable PF : Free C__F (List C__F A) -> Prop.
  Variable P : List C__F A -> Prop.

  Hypothesis NilFP : P nil.
  Hypothesis ConsFP : forall fx fxs, PF fxs -> P (cons fx fxs).
  Hypothesis PureListF : forall xs, P xs -> PF (pure xs).
  Hypothesis ImpureP : forall (s : Shape) (pf : Pos s -> Free C__F (List C__F A)),
      (forall p, PF (pf p)) -> PF (impure (ext s pf)).

  Definition FreeList_ind (fxs: Free C__F (List C__F A)) : PF fxs :=
    FreeList_rect PF P NilFP ConsFP PureListF ImpureP fxs.

End FreeList_ind.

Section Functions.

  Variable F : Type -> Type.
  Variable C__F : Container F.

  Definition Nil A : Free C__F (List C__F A) :=
    pure nil.
  Definition Cons A (fx : Free C__F A) (fxs : Free C__F (List C__F A)) : Free C__F (List C__F A) :=
    pure (cons fx fxs).


  Fixpoint append' A (xs: List C__F A) (fys: Free C__F (List C__F A)) : Free C__F (List C__F A) :=
    match xs with
    | nil => fys
    | cons fz fzs => Cons fz (fzs >>= fun zs => append' zs fys)
    end.

  Definition append A (fxs fys: Free C__F (List C__F A)) : Free C__F (List C__F A) :=
    fxs >>= fun xs => append' xs fys.

End Functions.