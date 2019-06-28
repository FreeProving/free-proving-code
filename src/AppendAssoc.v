Require Import FreeProving.Free.
Require Import FreeProving.Effects.
Require Import FreeProving.List.

Set Implicit Arguments.

Section append_assoc.

  Import Tactics.

  Variable A : Type.

  Section ZeroContainer.

    Import Zero.

    Lemma append'_assoc__Id : forall (xs : List C__Zero A) (fys fzs : Free C__Zero (List C__Zero A)),
        append' xs (append fys fzs) = append (append' xs fys) fzs.
    Proof.
      (*Let [xs], [fys], [fzs] be arbitrary. *)
      intros xs fys fzs.

      (*Perform induction over the [List] structure [xs]. *)
      induction xs using List_Ind.

      - (*Base case: [xs = nil] *)
        reflexivity.

      - (*Inductive case: [xs = cons fx fxs] with induction hypothesis [H]
          Perform induction over the [Free] structure [fxs]. *)
        induction fxs using Free_Ind.

        + (*Base case: [fxs = pure x]
            Simplify and use induction hypothesis [IH]. *)
          simpl. simplify H as IH. rewrite IH. reflexivity.

        + (*Inductive case: [fxs = impure (ext s pf)] with [s] of type [S__Zero] *)
          destruct s.
    Qed.

    Lemma append_assoc__Id : forall (fxs fys fzs : Free C__Zero (List C__Zero A)),
        append fxs (append fys fzs) = append (append fxs fys) fzs.
    Proof.
      (*Let [fxs], [fys], [fzs] be arbitrary. *)
      intros fxs fys fzs.

      (*Perform induction over the [Free] structure of [fxs]. *)
      induction fxs using Free_Ind.

      - (*Base case: [fxs = pure x]
          Simplify and use auxiliary lemma. *)
        simpl. apply append'_assoc__Id.

      - (*Inductive case: [fxs = impure (ext s pf)] with [s] of type [S__Zero] *)
        destruct s.
    Qed.

    (* This proof does not use an auxiliary lemma *)
    Lemma append_assoc__Id' : forall (fxs fys fzs : Free C__Zero (List C__Zero A)),
        append fxs (append fys fzs) = append (append fxs fys) fzs.
    Proof.
      intros fxs fys fzs.
      induction fxs using Free_Ind.
      - simpl. induction x using List_Ind.
        + reflexivity.
        + simpl. induction fxs using Free_Ind.
          * simpl. inversion H as [Heq IH|]; clear H; subst. rewrite IH. reflexivity.
          * destruct s.
      - destruct s.
    Qed.

    (* This proof uses a more elaborate induction principle to prevent redundancies *)
    Lemma append_assoc__Id_ : forall (fxs fys fzs : Free C__Zero (List C__Zero A)),
        append fxs (append fys fzs) = append (append fxs fys) fzs.
    Proof.
      intros fxs fys fzs.
      induction fxs as [ | fx' fxs' IHfxs' | xs IHxs | s pf ] using FreeList_ind
        with (P := fun xs => append' xs (append fys fzs) = append (append' xs fys) fzs);
        simpl.
      - reflexivity.
      - apply f_equal, IHfxs'.
      - apply IHxs.
      - destruct s.
    Qed.

  End ZeroContainer.

  Section OneContainer.

    Import One.

    Lemma append'_assoc__Maybe : forall (xs : List C__One A) (fys fzs : Free C__One (List C__One A)),
        append' xs (append fys fzs) = append (append' xs fys) fzs.
    Proof.
      intros xs fys fzs.
      induction xs using List_Ind.
      - reflexivity.
      - induction fxs using Free_Ind.
        + simpl. simplify H as IH. rewrite IH. reflexivity.
        + (*Inductive case: [fxs = impure (ext s pf)]
            Simplify, drop [Cons], [impure], and [ext s] on both sides. *)
        simpl. do 3 apply f_equal.

        (*Use functional extensionality and case distinction over [p : P__One s] *)
        extensionality p. destruct p.
    Qed.

    Lemma append_assoc__Maybe : forall (fxs fys fzs : Free C__One (List C__One A)),
        append fxs (append fys fzs) = append (append fxs fys) fzs.
    Proof.
      intros fxs fys fzs.
      induction fxs using Free_Ind.
      - simpl. apply append'_assoc__Maybe.
      - (*Inductive case: [fxs = impure (ext s pf)]
          Simplify, drop [impure], and [ext s] on both sides. *)
        simpl. do 2 apply f_equal.

        (*Use functional extensionality and case distinction over [p : P__One s]. *)
        extensionality p. destruct p.
    Qed.

    (* This proof does not use an auxiliary lemma *)
    Lemma append_assoc__Maybe' : forall (fxs fys fzs : Free C__One (List C__One A)),
        append fxs (append fys fzs) = append (append fxs fys) fzs.
    Proof.
      intros fxs fys fzs.
      induction fxs using Free_Ind.
      - simpl. induction x using List_Ind.
        + reflexivity.
        + simpl. induction fxs using Free_Ind.
          * simpl. simplify H as IH. rewrite IH. reflexivity.
          * simpl in *. do 3 f_equal. extensionality p. dependent destruction H. destruct p.
      - simpl. do 3 f_equal. extensionality p. destruct p.
    Qed.

    (* This proof uses a more elaborate induction principle to prevent redundancies *)
    Lemma append_assoc__Maybe_ : forall (fxs fys fzs : Free C__One (List C__One A)),
        append fxs (append fys fzs) = append (append fxs fys) fzs.
    Proof.
      intros fxs fys fzs.
      induction fxs as [ | fx' fxs' IHfxs' | xs IHxs | s pf ] using FreeList_ind
        with (P := fun xs => append' xs (append fys fzs) = append (append' xs fys) fzs);
        simpl.
      - reflexivity.
      - apply f_equal, IHfxs'.
      - apply IHxs.
      - do 2 apply f_equal; extensionality p; destruct p.
    Qed.

  End OneContainer.

  Section Generic.

    Variable F : Type -> Type.
    Variable C__F : Container F.

    Lemma append'_assoc : forall (xs : List C__F A) (fys fzs : Free C__F (List C__F A)),
        append' xs (append fys fzs) = append (append' xs fys) fzs.
    Proof.
      intros xs fys fzs.
      induction xs using List_Ind.
      - reflexivity.
      - induction fxs using Free_Ind.
        + simpl. simplify H as IH. rewrite IH. reflexivity.
        + (*Inductive case: [fxs = impure (ext s pf)] with induction hypothesis [H] *)
          simpl. do 3 apply f_equal. extensionality p.
          simplify H as IH. apply IH.
    Qed.

    Lemma append_assoc : forall (fxs fys fzs : Free C__F (List C__F A)),
        append fxs (append fys fzs) = append (append fxs fys) fzs.
    Proof.
      intros fxs fys fzs.
      induction fxs as [ | s pf IH ] using Free_Ind.
      - simpl. apply append'_assoc.
      - (*Inductive case: [fxs = impure (ext s pf)] with induction hypothesis [IH] *)
        simpl. do 2 apply f_equal. extensionality p.
        apply IH.
    Qed.

    (* This proof does not use an auxiliary lemma *)
    Lemma append_assoc__' : forall (fxs fys fzs : Free C__F (List C__F A)),
        append fxs (append fys fzs) = append (append fxs fys) fzs.
    Proof.
      intros fxs fys fzs.
      induction fxs using Free_Ind.
      - simpl. induction x using List_Ind.
        + reflexivity.
        + simpl. induction fxs using Free_Ind.
          * simpl. simplify H as IH. rewrite IH. reflexivity.
          * simpl in *. do 3 f_equal. extensionality p. simplify H as IH. apply IH.
      - simpl. do 3 f_equal. extensionality p. apply H.
    Qed.

    (* This proof uses a more elaborate induction principle to prevent redundancies *)
    Lemma append_assoc_ : forall (fxs fys fzs : Free C__F (List C__F A)),
        append fxs (append fys fzs) = append (append fxs fys) fzs.
    Proof.
      intros fxs fys fzs.
      induction fxs as [ | fx' fxs' IHfxs' | xs IHxs | s pf ] using FreeList_ind
        with (P := fun xs => append' xs (append fys fzs) = append (append' xs fys) fzs).
      - reflexivity.
      - simpl. apply f_equal. apply IHfxs'.
      - simpl. apply IHxs.
      - simpl. do 2 apply f_equal. extensionality p. apply H.
    Qed.

  End Generic.

End append_assoc.