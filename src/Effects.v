Require Import FunctionalExtensionality.
Require Export Strings.String.

Require Export FreeProving.Base.
Require Import FreeProving.Classes.
Require Import FreeProving.Free.

Set Implicit Arguments.

Module Zero.

  Inductive Zero (A : Type) : Type := .

  Global Instance C__None : Container :=
    {
      Shape := Void;
      Pos   := fun _ => Void;
    }.

  Definition toZero (A : Type) (e : Ext C__None A) : Zero A :=
    match e with
    | ext s p => match s with end
    end.

  Definition fromZero (A : Type) (z : Zero A) : Ext C__None A :=
    match z with end.

  Global Instance Iso__None : Iso Zero C__None :=
    {
      to   := toZero;
      from := fromZero
    }.
  Proof.
    - intros A fx.
      destruct fx.
    - intros A e.
      destruct e as [s pf].
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

  Definition free_to_id A (fx : Free C__None A) : Id A := induce zero_to_id fx.

End Zero.

Module One.

  Inductive One (A : Type) : Type := one : One A.

  Arguments one [_].

  Global Instance C__Partial : Container :=
    {
      Shape := unit;
      Pos   := fun _ => Void;
    }.

  Definition toOne (B : Type) (e : Ext C__Partial B) : One B :=
    one.

  Definition fromOne (B : Type) (z : One B) : Ext C__Partial B :=
    match z with
    | one => ext tt (fun p => match p with end)
    end.

  Global Instance Iso__Partial : Iso One C__Partial :=
    {
      to   := toOne;
      from := fromOne
    }.
  Proof.
    - intros A fx.
      destruct fx.
      simpl.
      reflexivity.
    - intros A e.
      destruct e as [s pf].
      simpl.
      destruct s.
      f_equal.
      extensionality y.
      destruct y.
  Defined.

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

  Definition free_to_maybe A (fx : Free C__Partial A) : Maybe A := induce one_to_maybe fx.

End One.

Module Const.
  
  Inductive Const (E A : Type) : Type := const : E -> Const E A.
  Global Arguments const [_] [_].

  Definition S__Const (E : Type) := E.
  Definition P__Const (E : Type) (s : S__Const E) : Type := Void.

  Global Instance C__Error' (E : Type) : Container :=
    {
      Shape := E;
      Pos   := fun _ => Void;
    }.

  Definition toConst (E B : Type) (e : Ext (C__Error' E) B) : Const E B :=
    match e with
    | ext s _ => const s
    end.

  Definition fromConst (E B : Type) (c : Const E B) : Ext (C__Error' E) B :=
    match c with
    | const s => ext (s : @Shape (C__Error' E)) (fun p => match p with end)
    end.

  Global Instance Iso__Error' (E : Type) : Iso (Const E) (C__Error' E) :=
    {
      to   := @toConst E;
      from := @fromConst E
    }.
  Proof.
    - intros A cx.
      destruct cx; simpl.
      reflexivity.
    - intros A ext.
      destruct ext; simpl.
      unfold fromConst.
      f_equal.
      extensionality p1.
      destruct p1.
  Defined.

  Definition C__Error := C__Error' string.

End Const.

Module Pair.

  Inductive pair (A : Type) : Type :=
  | pr : A -> A -> pair A.

  Global Instance C__ND : Container :=
    {
      Shape := unit;
      Pos   := fun _ => bool;
    }.

  Definition toPair (A : Type) (e : Ext C__ND A) : pair A :=
    match e with
    | ext tt pf => pr (pf true) (pf false)
    end.

  Definition fromPair (A : Type) (p : pair A) : Ext C__ND A :=
    match p with
    | pr x y => ext tt (fun p => match p with
                             | true => x
                             | false => y
                             end)
    end.

  Global Instance Iso__ND : Iso pair C__ND :=
    {
      to   := toPair;
      from := fromPair
    }.
  Proof.
    - intros B ex.
      destruct ex; simpl.
      reflexivity.
    - intros B ext.
      destruct ext as [s pf]; simpl.
      destruct s; simpl.
      f_equal.
      extensionality p.
      dependent destruction p; reflexivity.
  Defined.

End Pair.

Module Log.

  Inductive Log (A : Type) : Type :=
  | log : string -> A -> Log A.

  Global Instance C__Trace : Container :=
    {
      Shape := string;
      Pos := fun _ => unit;
    }.

  Definition toLog A (e : Ext C__Trace A) : Log A :=
    match e with
    | ext str p => log str (p tt)
    end.

  Definition fromLog A (t : Log A) : Ext C__Trace A :=
    match t with
    | log str x => ext str (fun p => x)
    end.

  Global Instance Iso__Log : Iso Log C__Trace :=
    {
      to := toLog;
      from := fromLog
    }.
  Proof.
    - intros A t.
      destruct t.
      reflexivity.
    - intros A e.
      destruct e as [s pf]; simpl.
      apply f_equal.
      extensionality p; destruct p.
      reflexivity.
  Defined.

End Log.
