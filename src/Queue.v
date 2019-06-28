Require Import FreeProving.List.
Require Import FreeProving.Effects.
Require Import FreeProving.AppendAssoc.

Import One.

Set Implicit Arguments.

Section Queue.

  Definition Nothing A : Free C__One A :=
    impure (ext tt (fun p : P__One tt => match p with end)).

  Arguments Nothing [_].

  Section QueueDef.

    Variable F : Type -> Type.

    Inductive Pair (C__F : Container F) A B := pair : Free C__F A -> Free C__F B -> Pair C__F A B.

    Definition QueueI (C__F : Container F) A := Pair C__F (List C__F A) (List C__F A).

    Definition Queue (C__F : Container F) A := List C__F A.

  End QueueDef.

  Definition front A (fq : Free C__One (Queue C__One A)) : Free C__One A :=
    fq >>= fun q => match q with
                 | nil => Nothing
                 | cons x _ => x
                 end.

  Definition frontI A (fqi: Free C__One (QueueI C__One A)) : Free C__One A :=
    fqi >>= fun '(pair ff fb) => ff >>= fun f => match f with
                                          | nil => Nothing
                                          | cons fx _ => fx
                                          end.

  Section QueuePoly.

    Variable F : Type -> Type.
    Variable C__F : Container F.

    Definition singleton A (fx: Free C__F A) : Free C__F (List C__F A) :=
      pure (cons fx (pure nil)).

    Fixpoint reverse' A (xs: List C__F A) : Free C__F (List C__F A) :=
      match xs with
      | nil => pure nil
      | cons fy fys => append (fys >>= fun ys => reverse' ys) (singleton fy)
      end.

    Definition reverse A (fxs: Free C__F (List C__F A)) : Free C__F (List C__F A) :=
      fxs >>= fun xs => reverse' xs.

    Definition toQueue A (fqi: Free C__F (QueueI C__F A)) : Free C__F (Queue C__F A) :=
      fqi >>= fun '(pair ff fb) => append ff (reverse fb).

    Inductive total_list A : Free C__F (List C__F A) -> Prop :=
    | total_nil : total_list (pure nil)
    | total_cons : forall fx fxs, total_list fxs -> total_list (pure (cons fx fxs)).

    Definition null A (fl : Free C__F (List C__F A)) : Free C__F bool :=
      fl >>= fun l => match l with
                   | nil => pure true
                   | cons _ _ => pure false
                   end.

    Definition not (fb : Free C__F bool) : Free C__F bool :=
      fb >>= fun b => pure (negb b).

    Definition fst A B (fp : Free C__F (Pair C__F A B)) : Free C__F A :=
      fp >>= fun '(pair ff fb) => ff.

    Definition snd A B (fp : Free C__F (Pair C__F A B)) : Free C__F B :=
      fp >>= fun '(pair ff fb) => fb.

    Definition orF (fb1 fb2 : Free C__F bool) : Free C__F bool :=
      fb1 >>= fun b1 => fb2 >>= fun b2 => pure (orb b1 b2).

    Definition andF (fb1 fb2 : Free C__F bool) : Free C__F bool :=
      fb1 >>= fun b1 => fb2 >>= fun b2 => pure (andb b1 b2).

    Notation "b1 || b2" := (orF b1 b2).
    Notation "b1 && b2" := (andF b1 b2).

    Definition total_queue A (fqi : Free C__F (QueueI C__F A)) : Prop :=
      total_list (fst fqi) /\ total_list (snd fqi).

    Definition invariant A (fqi : Free C__F (QueueI C__F A)) : Free C__F bool :=
      null (snd fqi) || not (null (fst fqi)).

    Definition is_pure_true (fb : Free C__F bool) : Prop :=
      match fb with
      | pure true => True
      | _ => False
      end.

    Lemma is_pure_true_or :
      forall (fb1 fb2 : Free C__F bool),
        is_pure_true (fb1 || fb2) -> is_pure_true fb1 \/ is_pure_true fb2.
    Proof.
      intros fb1 fb2 Hpure.
      destruct fb1, fb2; simpl in *.
      - destruct b; auto.
      - destruct e; auto.
      - destruct e; auto.
      - destruct e; auto.
    Qed.

    Lemma is_pure_true_and :
      forall (fb1 fb2 : Free C__F bool),
        is_pure_true (fb1 && fb2) -> is_pure_true fb1 /\ is_pure_true fb2.
    Proof.
      intros fb1 fb2 Hpure.
      split; destruct fb1 as [ b1 | [s1 pf1]], fb2 as [ b2 | [s2 pf2]] ; simpl in *; auto.
      - destruct b1, b2; auto.
      - destruct b1; auto.
      - destruct b1, b2; auto.
      - destruct b2; auto.
    Qed.

    Definition quickCheckReq A (fqi : Free C__F (QueueI C__F A)) : Prop :=
      total_queue fqi /\ is_pure_true (invariant fqi).
    
    Definition cond (fb : Free C__F bool) (P : Prop) : Prop :=
      is_pure_true fb -> P.

    Definition isEmptyI A (fqi: Free C__F (QueueI C__F A)) : Free C__F bool :=
      fqi >>= fun '(pair ff _) => null ff.

    Definition isEmpty A (fq: Free C__F (Queue C__F A)) : Free C__F bool := null fq.

    Definition emptyI A : Free C__F (QueueI C__F A) :=
      pure (pair (pure nil) (pure nil)).

    Definition empty A : Free C__F (Queue C__F A) := pure nil.

    Definition add A (fx: Free C__F A) (fq: Free C__F (Queue C__F A)) : Free C__F (Queue C__F A) :=
      append fq (singleton fx).

    Definition flipQ A (fqi: Free C__F (QueueI C__F A)) : Free C__F (QueueI C__F A) :=
      fqi >>= fun '(pair ff fb) => ff >>= fun f => match f with
                                             | nil => pure (pair (reverse fb) (pure nil))
                                             | cons fx fxs => pure (pair (pure f) fb)
                                             end.

    Definition addI A (fx: Free C__F A) (fqi: Free C__F (QueueI C__F A)) : Free C__F (QueueI C__F A) :=
      fqi >>= fun q =>
                match q with
                | pair ff fb => flipQ (pure (pair ff (pure (cons fx fb))))
                end.

  End QueuePoly.

  Section QueueLemma.

    Notation "p ===> prop" := (cond p prop) (at level 40, prop at level 80, left associativity).
    Notation "b1 || b2" := (orF b1 b2).
    Notation "b1 && b2" := (andF b1 b2).

    Variable A : Type.
    Variable F : Type -> Type.
    Variable C__F : Container F.

    Lemma prop_front : forall (fqi : Free C__One (QueueI C__One A)),
        total_queue fqi ->
        invariant fqi && not (isEmptyI fqi) ===> frontI fqi = front (toQueue fqi).
  Proof.
    intros fqi Htotal HinvNempty.
    apply is_pure_true_and in HinvNempty.
    destruct HinvNempty as [Hinv Hnempty].
    destruct Htotal as [Htotal1 Htotal2].
    destruct fqi as [ [ff fb] | [s pf] ].
    - destruct ff as [l | [s pf] ].
      + destruct l.
        * destruct Hnempty.
        * reflexivity.
      + inversion Htotal1.
    - inversion Htotal2.
  Qed.

  Lemma prop_empty : toQueue (emptyI C__F A) = (empty C__F A).
  Proof. reflexivity. Qed.

  Lemma null_rev :
    forall (fq : Free C__F (List C__F A)),
      null fq ===> null (reverse fq) = pure true.
  Proof.
    intros fq Hnull.
    destruct fq as [ l | [s pf] ].
    - destruct l.
      + trivial.
      + destruct Hnull.
    - destruct Hnull.
  Qed.

  Lemma prop_isEmpty : forall (fqi : Free C__F (QueueI C__F A)),
      total_queue fqi ->
      invariant fqi ===> isEmptyI fqi = isEmpty (toQueue fqi).
  Proof.
    intros fqi Htotal Hinv.
    destruct Htotal as [Htotal1 Htotal2].
    destruct fqi as [q | [s pf] ].
    - destruct q as [fxs fys].
      destruct fxs as [l | [s pf] ].
      + destruct l ; simpl in *.
        * unfold invariant in Hinv; simpl in Hinv.
          apply is_pure_true_or in Hinv.
          destruct Hinv as [Hnil1 | Hnil2].
          -- apply null_rev in Hnil1.
             symmetry; apply Hnil1.
          -- inversion Hnil2.
        * reflexivity.
      + inversion Htotal1.
    - inversion Htotal2.
  Qed.

  Lemma append_nil : forall (fxs : Free C__F (List C__F A)), append fxs (pure nil) = fxs.
  Proof.
    intros fxs.
    induction fxs using FreeList_ind with (P := fun xs => append' xs (pure nil) = pure xs); simpl.
    - reflexivity.
    - unfold Cons; simpl; repeat apply f_equal. apply IHfxs1.
    - apply IHfxs.
    - repeat apply f_equal. extensionality p. apply H.
  Qed.

  Lemma prop_add : forall (fa : Free C__F A) (fqi : Free C__F (QueueI C__F A)),
      toQueue (addI fa fqi) = add fa (toQueue fqi).
  Proof.
    intros fx fqi.
    induction fqi as [ [f1 f2] | eq ] using Free_Ind; simpl.
    - destruct f1 as [l | [s pf]]; simpl.
      + destruct l as [ | fy fys]; simpl.
        * rewrite append_nil. reflexivity.
        * apply (append_assoc (pure (cons fy fys)) (reverse f2) (singleton fx)).
      + repeat apply f_equal. extensionality p.
        induction (pf p) as [fys |] using Free_Ind; simpl.
        * destruct fys; simpl.
          -- rewrite append_nil.
             reflexivity.
          -- apply f_equal. apply (append_assoc f0 (reverse f2) (singleton fx)).
        * repeat apply f_equal.
          extensionality p1.
          apply H.
    - repeat apply f_equal.
      extensionality p.
      apply H.
  Qed.

  End QueueLemma.

End Queue.