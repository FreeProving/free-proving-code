Set Implicit Arguments.

Inductive Void : Type := .

Class Container :=
  {
    Shape   : Type;
    Pos     : Shape -> Type;
  }.


Section Ext.
  
  Inductive Ext (C : Container) (A : Type) :=
  | ext : forall (s : Shape), (Pos s -> A) -> Ext C A.

  Global Arguments Ext : clear implicits.
  Global Arguments ext [_] [_] s pf.

End Ext.

Class Iso (F : Type -> Type) (C : Container) :=
  {
    to              : forall (A : Type), Ext C A -> F A;
    from            : forall (A : Type), F A -> Ext C A;
    to_from_inverse : forall (A : Type) (fx : F A), to (from fx) = fx;
    from_to_inverse : forall (A : Type) (e : Ext C A), from (to e) = e
  }.

Arguments to [_] [_] [_] [_].
Arguments from [_] [_] [_] [_].
