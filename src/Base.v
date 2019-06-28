Set Implicit Arguments.

Inductive Void : Type := .

Section Ext.
  
  Inductive Ext (Shape : Type) (Pos : Shape -> Type) (A : Type) :=
  | ext : forall (s : Shape), (Pos s -> A) -> Ext Pos A.

  Global Arguments Ext : clear implicits.
  Global Arguments ext [_] [_] [_] s pf.

End Ext.

Section Container.
  
  Class Container (F : Type -> Type) :=
    {
      Shape   : Type;
      Pos     : Shape -> Type;
      to      : forall A, Ext Shape Pos A -> F A;
      from    : forall A, F A -> Ext Shape Pos A;
      to_from : forall A (fx : F A), to (from fx) = fx;
      from_to : forall A (e : Ext Shape Pos A), from (to e) = e
    }.

  Arguments from [_] [_] [_] _.

End Container.

Section MonadClass.

  Class Monad (M: Type -> Type) :=
    {
      ret : forall A, A -> M A;
      bind : forall A B, M A -> (A -> M B) -> M B;
      left_unit : forall A B (x0: A) (f: A -> M B),
                    bind (ret x0) f = f x0;
      right_unit : forall A (ma: M A), bind ma (@ret A) = ma;
      bind_assoc: forall A B C (ma : M A) (f: A -> M B) (g: B -> M C),
                    bind ma (fun y => bind (f y) g) = bind (bind ma f) g
    }.

  Definition join (M: Type -> Type) `(Monad M) A (mmx : M (M A)) : M A := bind _ mmx (fun x => x).

  Global Arguments join [_] [_] [_].

End MonadClass.

Section FunctorClass.

  Class Functor (F: Type -> Type) :=
    {
      fmap : forall A B, (A -> B) -> F A -> F B;
      fmap_id : forall A (fx : F A), fmap (fun x => x) fx = fx;
      fmap_comp : forall A B C (f : B -> C) (g : A -> B) (fx : F A),
          fmap f (fmap g fx) = fmap (fun x => f (g x)) fx
    }.

End FunctorClass.