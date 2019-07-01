Require Import FreeProving.Free.
Require Export FreeProving.Primitives.

Import Free_Notation.

Set Implicit Arguments.
Unset Elimination Schemes.

Section Definitions.

  Variable C : Container.

  Inductive Dummy :=
  | D : Free C Bool -> Dummy.

  Definition value (fd : Free C Dummy) : Free C Bool :=
    fd >>= fun d => match d with
                 | D fb => fb
                 end.

  Definition shareDummy' (fb : Free C Bool) : Free C Bool :=
    pure (D fb) >>= fun d => and (value (pure d)) (value (pure d)).

End Definitions.

Section Propositions.

  Example shareDummy_trace_twice :
    shareDummy' (trace "debug" (pure True_))
    = trace "debug" (trace "debug" (pure True_)).
  Proof.
    reflexivity.
  Qed.

End Propositions.
