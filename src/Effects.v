Require Import FunctionalExtensionality.

Require Export FreeProving.Base.
Require Import FreeProving.Free.

Set Implicit Arguments.

Module Zero.

  Definition Zero (A : Type) := Void.

  Definition S__Zero := Void.
  Definition P__Zero (s : S__Zero) := Void.
  Definition E__Zero (A : Type) := Ext S__Zero P__Zero A.

  Definition toZero A (e : E__Zero A) : Zero A :=
    match e with
    | ext s _ => match s with end
    end.

  Definition fromZero A (z : Zero A) : E__Zero A :=
    match z with end.

  Global Instance C__Zero : Container Zero :=
    {
      Shape := S__Zero;
      Pos := P__Zero;
      to := toZero;
      from := fromZero
    }.
  Proof.
    - intros.
      destruct fx.
    - intros.
      destruct e.
      destruct s.
  Defined.

  Section MonadInstance.

    Definition Id (A : Type) := A.

    Definition id_ret A (x : A) : Id A :=
      x.

    Definition id_bind A B (a : Id A) (f : A -> Id B) : Id B := f a.

    Lemma id_left_identity :
      forall A B (a : A) (f : A -> Id B),
        id_bind (id_ret a) f = f a.
    Proof.
      repeat intro.
      unfold id_ret.
      unfold id_bind.
      reflexivity.
    Qed.

    Lemma id_right_identity :
      forall A (ia : Id A),
        id_bind ia (fun a => id_ret a) = ia.
    Proof.
      repeat intro.
      unfold id_bind.
      unfold id_ret.
      reflexivity.
    Qed.

    Lemma id_associativity :
      forall A B C (ia : Id A) (f : A -> Id B) (g : B -> Id C),
        id_bind ia (fun a => id_bind (f a) g) = id_bind (id_bind ia f) g.
    Proof.
      repeat intro.
      unfold id_bind.
      reflexivity.
    Qed.

    Global Instance id_monad : Monad Id :=
      {
        ret := id_ret;
        bind := id_bind;
        left_unit := id_left_identity;
        right_unit := id_right_identity;
        bind_assoc := id_associativity
      }.

  End MonadInstance.

  Definition zero_to_id A (zx : Zero A) : Id A := match zx with end.

  Definition free_to_id A (fx : Free C__Zero A) : Id A := induce zero_to_id fx.

End Zero.

Module One.

  Definition One (A : Type) := unit.

  Definition S__One := unit.
  Definition P__One (s : S__One) := Void.
  Definition E__One A := Ext S__One P__One A.

  Definition to__One A (e : E__One A) : One A :=
    tt.

  Definition from__One A (z : One A) : E__One A :=
    ext tt (fun p : P__One tt => match p with end).

  Lemma to_from__One : forall A (ox : One A), to__One (from__One ox) = ox.
  Proof.
    intros A ox.
    destruct ox.
    unfold from__One.
    unfold to__One.
    reflexivity.
  Qed.

  Lemma from_to__One : forall A (e : E__One A), from__One (to__One e) = e.
  Proof.
    intros A e.
    destruct e.
    destruct s.
    unfold to__One.
    unfold from__One.
    apply f_equal.
    extensionality p.
    destruct p.
  Qed.

  Instance C__One : Container One :=
    {
      Shape := S__One;
      Pos := P__One;
      to := to__One;
      from := from__One;
      to_from := to_from__One;
      from_to := from_to__One
    }.

  Section MonadInstance.

    Inductive Maybe A :=
    | nothing : Maybe A
    | just : A -> Maybe A.

    Global Arguments nothing [_].

    Definition maybe_ret A (a : A) : Maybe A :=
      just a.

    Definition maybe_bind A B (ma : Maybe A) (f : A -> Maybe B) : Maybe B :=
      match ma with
      | nothing => nothing
      | just a => f a
      end.

    Lemma maybe_left_identity :
      forall A B (a : A) (f : A -> Maybe B),
        maybe_bind (maybe_ret a) f = f a.
    Proof.
      reflexivity.
    Qed.

    Lemma maybe_right_identity :
      forall A (ma : Maybe A),
        maybe_bind ma (@maybe_ret A) = ma.
    Proof.
      induction ma.
      - reflexivity.
      - reflexivity.
    Qed.

    Lemma maybe_associativity :
      forall A B C (ma : Maybe A) (f : A -> Maybe B) (g : B -> Maybe C),
        maybe_bind ma (fun a => maybe_bind (f a) g) = maybe_bind (maybe_bind ma f) g.
    Proof.
      intros.
      induction ma.
      - reflexivity.
      - reflexivity.
    Qed.

    Global Instance maybe_monad : Monad Maybe :=
      {
        ret := maybe_ret;
        bind := maybe_bind;
        left_unit := maybe_left_identity;
        right_unit := maybe_right_identity;
        bind_assoc := maybe_associativity
      }.

  End MonadInstance.

  Definition one_to_maybe A (ox : One A) : Maybe A := nothing.

  Definition free_to_maybe A (fx : Free C__One A) : Maybe A := induce one_to_maybe fx.

End One.

Module Const.

  Inductive Const (B A : Type) := const : B -> Const B A.

End Const.