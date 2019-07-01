Require Export FreeProving.Free.

Set Implicit Arguments.
Unset Elimination Schemes.

Section ListDefinition.

  Variable C : Container.

  Inductive List (A: Type) : Type :=
  | nil : List A
  | cons : Free C A -> Free C (List A) -> List A.

End ListDefinition.

Arguments nil [_] [_].

Section List_ind.

  Variable C : Container.

  Variable A : Type.
  Variable P : List C A -> Prop.

  Hypothesis nilP : P nil.
  Hypothesis consP : forall (fx: Free C A)
                       (fxs : Free C (List C A)),
      ForFree P fxs -> P (cons fx fxs).

  Fixpoint List_ind (l : List C A) : P l :=
    match l as l0 return (P l0) with
    | nil => nilP
    | cons f f0 =>
      consP f
            (Free_ind (fun f1 : Free C (List C A) => ForFree P f1)
                      (fun x : List C A => For_pure _ P x (List_ind x))
                      (fun (s : Shape) (pf : Pos s -> Free C (List C A))
                         (H : forall p : Pos s, ForFree P (pf p)) =>
                         For_impure s pf (fun p : Pos s => H p)) f0)
    end.

End List_ind.

Section FreeList_rect.

  Variable C : Container.
  Variable A : Type.
  Variable PF : Free C (List C A) -> Type.
  Variable P : List C A -> Type.

  Hypothesis NilFP : P nil.
  Hypothesis ConsFP : forall fx fxs, PF fxs -> P (cons fx fxs).
  Hypothesis PureListF : forall xs, P xs -> PF (pure xs).
  Hypothesis ImpureP : forall (s : Shape) (pf : Pos s -> Free C (List C A)),
      (forall p, PF (pf p)) -> PF (impure (ext s pf)).

  Fixpoint List_Rect (xs: List C A) : P xs :=
    let fix aux (fys: Free C (List C A)) : PF fys :=
        match fys with
        | pure ys => PureListF (List_Rect ys)
        | impure (ext s pf) => ImpureP s pf (fun p => aux (pf p))
        end
    in match xs with
       | nil => NilFP
       | cons fx fxs => ConsFP fx (aux fxs)
       end.

  Fixpoint FreeList_rect (fxs: Free C (List C A)) : PF fxs :=
    match fxs with
    | pure xs => PureListF (List_Rect xs)
    | impure (ext s pf) => ImpureP s pf (fun p => FreeList_rect (pf p))
    end.

End FreeList_rect.

Section FreeList_ind.

  Variable C : Container.
  Variable A : Type.
  Variable PF : Free C (List C A) -> Prop.
  Variable P : List C A -> Prop.

  Hypothesis NilFP : P nil.
  Hypothesis ConsFP : forall fx fxs, PF fxs -> P (cons fx fxs).
  Hypothesis PureListF : forall xs, P xs -> PF (pure xs).
  Hypothesis ImpureP : forall (s : Shape) (pf : Pos s -> Free C (List C A)),
      (forall p, PF (pf p)) -> PF (impure (ext s pf)).

  Definition FreeList_ind (fxs: Free C (List C A)) : PF fxs :=
    FreeList_rect PF P NilFP ConsFP PureListF ImpureP fxs.

End FreeList_ind.

Section Functions.

  Variable C : Container.

  Import Free_Notation.

  Definition nilF (A : Type) : Free C (List C A) :=
    pure nil.

  Definition consF (A : Type) (fx : Free C A) (fxs : Free C (List C A)) :=
    pure (cons fx fxs).

  Fixpoint append' A (xs: List C A) (fys: Free C (List C A)) : Free C (List C A) :=
    match xs with
    | nil => fys
    | cons fz fzs => consF fz (fzs >>= fun zs => append' zs fys)
    end.

  Definition append A (fxs fys: Free C (List C A)) : Free C (List C A) :=
    fxs >>= fun xs => append' xs fys.

End Functions.