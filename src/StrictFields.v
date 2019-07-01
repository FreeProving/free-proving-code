Require Import FreeProving.Free.
Require Import FreeProving.Primitives.
Require Import FreeProving.Simple.

Set Implicit Arguments.

Section GenericDefinitions.

  Variable C : Container.

  (**
     data Foo1 = Foo1 Int
     data Foo2 = Foo2 !Int
     newtype Foo3 = Foo3 Int
   *)

  Inductive Foo1 :=
  | Foo1_ : Free C Int -> Foo1.

  Inductive Foo2 :=
  | Foo2_ : Int -> Foo2.

  Definition Foo3 := Int.


  Definition appC a b (ff : Free C (Free C a -> b)) (fx : Free C a) :=
    ff >>= fun f => pure (f fx).

  Definition bangAppC a b (ff : Free C (a -> b)) (fx : Free C a) :=
    ff >>= fun f => fx >>= fun x => pure (f x).


  (**
     xFoo1 = case Foo1 undefined of
               Foo1 _ -> 1
   *)

End GenericDefinitions.

Infix "$$!" := bangAppC (at level 28, left associativity).

Section Examples.

  Definition xFoo1 :=
    pure (Foo1_ undefined) >>= fun x => match x with
                                     | Foo1_ _ => pure 1
                                     end.

  Example xFoo1_example : xFoo1 = pure 1.
  Proof.
    reflexivity.
  Qed.

  Definition xFoo2 :=
    (pure Foo2_ $$! undefined) >>= fun x => match x with
                                         | Foo2_ _ => pure 1
                                         end.

  Example xFoo2_example : xFoo2 = undefined.
  Proof.
    apply eq_impure.
    apply Partial_Simple.
  Qed.

  Definition xFoo3 := pure 1.

  Example xFoo3_example : xFoo3 = pure 1.
  Proof.
    reflexivity.
  Qed.

  Definition yFoo1 :=
    undefined >>= fun x => match x with
                        | Foo1_ _ => pure 1
                        end.

  Example yFoo1_example : yFoo1 = undefined.
  Proof.
    apply eq_impure.
    apply Partial_Simple.
  Qed.

  Definition yFoo2 :=
    undefined >>= fun x => match x with
                        | Foo2_ _ => pure 1
                        end.

  Example yFoo2_example : yFoo2 = undefined.
  Proof.
    apply eq_impure.
    apply Partial_Simple.
  Qed.

  Definition yFoo3 :=
    pure 1.

  Example yFoo3_example : yFoo3 = pure 1.
  Proof.
    reflexivity.
  Qed.

End Examples.