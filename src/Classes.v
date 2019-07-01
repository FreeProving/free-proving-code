Set Implicit Arguments.

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