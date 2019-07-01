Require Import FreeProving.Free.
Require Import FreeProving.Seq.
Require Import FreeProving.Primitives.

Import Free_Notation.

Set Implicit Arguments.

Section GenericDefinitions.
  
  Variable C : Container.

  Definition const a b (fx : Free C a) : Free C (Fun C b a) :=
    pure (fun _ => fx).

  Arguments const [_] [_].

  Definition id a (fx : Free C a) :=
    fx.

  Definition compose a b c (ff : Free C b -> Free C c) (fg : Free C a -> Free C b) : Free C a -> Free C c :=
    fun fx => ff (fg fx).

  Inductive Pair a b :=
  | Pair_ : Free C a -> Free C b -> Pair a b.

  Definition fst a b (fp : Free C (Pair a b)) :=
    fp >>= fun p => match p with
                 | Pair_ fx _ => fx
                 end.

  Definition snd a b (fp : Free C (Pair a b)) :=
    fp >>= fun p => match p with
                 | Pair_ _ fy => fy
                 end.

  Definition State s a := Free C s -> Free C (Pair a s).

  Definition runS s a (fs : Free C (State s a)) := fs.

  Definition get s : Free C (State s s) :=
    pure (fun fs => pure (Pair_ fs fs)).

  Definition put s (fs : Free C s) : Free C (State s Unit) :=
    const (pure (Pair_ (pure Unit_) fs)).

End GenericDefinitions.

Arguments const [_] [_] [_].
Arguments State [_].
Arguments put [_] [_].
Arguments get [_] [_].

Section Monad.

  Variable C : Container.

  Section MonadDefintion.

    Class Monad (m : Type -> Type) :=
      {
        ret a : Free C a -> Free C (m a);
        bind a b : Free C (m a) -> Free C (Fun C a (m b)) -> Free C (m b)
      }.

    Global Arguments bind [_] [_] [_] [_].

    Definition then_ a b m `{Monad m} (ma : Free C (m a)) (mb : Free C (m b)) : Free C (m b) :=
      bind ma (pure (fun _ => mb)).

    Global Arguments then_ [_] [_] [_] [_].

    Definition skip m `(Monad m) :=
      ret (pure Unit_).

    Global Arguments skip [_].

  End MonadDefintion.

  Section StateInstances.

    Instance monad_State_strict s : Monad (State s) :=
      {
        ret a fx := pure (fun fs => pure (Pair_ fx fs));
        bind a b fm fk := pure (fun fs => runS fm $ fs >>= fun p =>
                                                          match p with
                                                          | Pair_ fx fs' => runS (fk $ fx) $ fs'
                                                          end)
      }.

    Instance monad_State_lazy s : Monad (State s) :=
      {
        ret a fx := pure (fun fs => pure (Pair_ fx fs));
        bind a b fm fk := pure (fun fs => let fp := runS fm $ fs
                                       in runS (fk $ fst fp) $ snd fp)
      }.

  End StateInstances.

  Definition constSkip s : Free C (Fun C Bool (State s Unit)) :=
    const (skip (monad_State_lazy s)).

  Section MonadLawsStrict.

    Variable s : Type.

    Definition bind_strict := bind (Monad := monad_State_strict s).
    Definition ret_strict   := ret (Monad := monad_State_strict s).

    Lemma MSPutPutLaw : forall (fs fs' : Free C s),
      bind_strict (put fs') (pure (fun _ => put fs)) = put fs.
    Proof.
      intros fs fs'.
      reflexivity.
    Qed.

    Lemma MSPutGetLaw : forall (fs fs' : Free C s),
        bind_strict (put fs) (pure (fun _ => get))
        = bind_strict (put fs) (pure (fun _ => ret_strict fs)).
    Proof.
      intros fs fs'.
      reflexivity.
    Qed.

    Lemma MSGetPutLaw :
        bind_strict (@get _ s) (pure (fun fs => put fs)) = skip (monad_State_strict s).
    Proof.
      reflexivity.
    Qed.

    Lemma MSGetGetLaw :
      forall a (fk : Free C (Fun C s (Free C s -> Free C (State s a)))),
        bind_strict get (pure (fun fs => bind_strict get (fk $ fs)))
        = bind_strict get (pure (fun fs => fk $ fs $ fs)).
    Proof.
      intros k.
      reflexivity.
    Qed.

  End MonadLawsStrict.

  Section MonadLaws.

    Definition MonadLaw1 m `(Monad m) :=
      forall a b (fx : Free C a) (ff : Free C (Fun C a (m b))),
        bind (ret fx) ff = ff $ fx.

    Definition MonadLaw2 m `(Monad m) :=
      forall a (fx : Free C (m a)),
        bind fx (pure (fun x => ret x)) = fx.

    Definition MonadLaw3 m `(Monad m) :=
      forall a b c (fx : Free C (m a))
        (ff : Free C (Fun C a (m b)))
        (fg : Free C (Fun C b (m c))),
        bind (bind fx ff) fg = bind fx (pure (fun x => bind (ff $ x) fg)).

  End MonadLaws.

End Monad.

Section Instances.

  Lemma MonadLaw1_State_lazy_fail__Partial :
    forall s, not (MonadLaw1 (monad_State_lazy C__Partial s)).
  Proof.
    intros s Heq.
    specialize (Heq _ Unit (pure False_) undefined).
    inversion Heq.
  Qed.

  Lemma MonadLaw1_State_strict_fail__Partial :
    forall s, not (MonadLaw1 (monad_State_strict C__Partial s)).
  Proof.
    intros s Heq.
    specialize (Heq _ Unit (pure False_) (const undefined)).
    inversion Heq.
  Qed.

  Lemma MonadLaw2_State_lazy_fail__Partial :
    forall s, not (MonadLaw2 (monad_State_lazy C__Partial s)).
  Proof.
    intros s Heq.
    specialize (Heq Bool undefined).
    inversion Heq.
  Qed.

  Lemma MonadLaw2_State_strict_fail__Partial :
    forall s, not (MonadLaw2 (monad_State_strict C__Partial s)).
  Proof.
    intros s Heq.
    specialize (Heq Bool undefined).
    inversion Heq.
  Qed.

  Lemma MonadLaw1_State_lazy__None :
    forall s, MonadLaw1 (monad_State_lazy C__None s).
  Proof.
    intros s a b fx ff.
    destruct ff as [ f | [ [] pf ] ]. simpl.
    destruct (f fx) as [ ffx | [ [] pf ] ]. simpl.
    reflexivity.
  Qed.

  Lemma MonadLaw1_State_strict__None :
    forall s, MonadLaw1 (monad_State_strict C__None s).
  Proof.
    intros s a b fx ff.
    destruct ff as [ f | [ [] pf ] ]. simpl.
    destruct (f fx) as [ ffx | [ [] pf ] ]. simpl.
    reflexivity.
  Qed.


  Section constSkip.
  
    Lemma MonadLaw1_State_lazy_fail__Trace :
      forall s, not (MonadLaw1 (monad_State_lazy C__Trace s)).
    Proof.
      intros s Heq.
      specialize (Heq _ _ (pure False_)
                      (trace "debug" (constSkip C__Trace s))).
      inversion Heq.
    Qed.

    Lemma MonadLaw1_State_lazy_fail__ND :
      forall s, not (MonadLaw1 (monad_State_lazy C__ND s)).
    Proof.
      intros s Heq.
      specialize (Heq _ _ (pure False_)
                      (choice (constSkip C__ND s) (constSkip C__ND s))).
      inversion Heq.
    Qed.

  End constSkip.

  Section generic.

    Variable C : Container.

    Lemma MonadLaw1_State_lazy_fail :
      forall (shape : Shape) s, not (MonadLaw1 (monad_State_lazy C s)).
    Proof.
      intros shape s Heq.
      specialize (Heq _ _ (pure False_)
                      (impure (ext shape (fun _ => constSkip C s)))).
      inversion Heq.
    Qed.

  End generic.

End Instances.
