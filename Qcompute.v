From Stdlib Require Import Utf8.
From Stdlib Require Import Lists.List Nat Bool.
Import ListNotations.
From Crocqodile Require Import Qlang.
(** Functions to compute steps TODO adapt to IF THEN ELSE *)

Definition compute_toplevel_step (term : Q) : option Q :=
  match term with
  | ConsW (Letter b) (Word w) =>
    Some (Word (b :: w))
  | App (Abs body) arg =>
    if is_value arg then
      Some (body.[fun x => match x with | 0 => arg | _ => Var x end])
    else
      None
  | Qif (Letter b) Qthen thenBody Qelse elseBody =>
    if is_value thenBody && is_value elseBody then
      if b then
        Some thenBody
      else
        Some elseBody
    else
      None
  | _ => None
  end.

Definition compute_toplevel_step_refl : ∀ (t u : Q),
  (t →topQ u) ↔ compute_toplevel_step t = Some u.
Proof.
  intros t u.
  split.
  - intro Hred.
    inversion Hred as [b' w' eq1 eq2| body' arg' Hval eq |
      thenbody' elseBody' Hvalelse Hvalthen eq1 eq2  |
      thenbody' elseBody' Hvalelse Hvalthen eq1 eq2 ]; subst.
    3,4: simpl;
      apply (reflect_iff _ _ (is_value_refl _)) in Hvalelse, Hvalthen;
      rewrite Hvalelse, Hvalthen; reflexivity.
    1: reflexivity.
    + simpl.
      specialize (reflect_iff _ _ (is_value_refl arg')) as Hrefl.
      rewrite Hrefl in Hval.
      rewrite Hval.
      reflexivity.
  - intro H.
    destruct t as
    [x | w | b | hd tl | body | f arg | cond thenBody elseBody];
    simpl in H; try discriminate H.
    + destruct hd as [x' | w' | b' | hd' tl' | body' |
        f' arg' | cond' thenBody' elseBody' ];
      try discriminate H.
      destruct tl as [x'' | w'' | b'' | hd'' tl'' | body'' |
      f'' arg'' | cond'' thenBody'' elseBody'' ];
      try discriminate H.
      injection H; clear H; intro eq; subst.
      constructor.
    + destruct f as [x' | w' | b' | hd' tl' | body' |
      f'' arg'' | cond'' thenBody'' elseBody'' ];
      try discriminate H.
      destruct (is_value arg) eqn:Hisval;
      specialize (reflect_iff _ _ (is_value_refl arg)) as Hrefl.
      * rewrite <- Hrefl in Hisval.
        injection H; clear H; intro eq; subst.
        constructor.
        assumption.
      * discriminate H.
    + destruct cond as [x' | w' | b' | hd' tl' | body' |
        f' arg' | cond' thenBody' elseBody' ]; try discriminate H.
      destruct (is_value thenBody) eqn: Hisvalthen;
      [destruct (is_value elseBody) eqn: Hisvalelse|].
      2, 3: discriminate H.
      * simpl.
        apply (reflect_iff _ _ (is_value_refl _)) in Hisvalthen, Hisvalelse.
        destruct b'; simpl in H; injection H as eq; subst;
        constructor; assumption.
Qed.

Definition letter_value (b : bool) : value (Letter b).
specialize (reflect_iff _ _ (is_value_refl (Letter b))) as Hrefl.
rewrite Hrefl. simpl. reflexivity.
Defined.

Definition word_value (w : list bool) : value (Word w).
specialize (reflect_iff _ _ (is_value_refl (Word w))) as Hrefl.
rewrite Hrefl. simpl. reflexivity.
Defined.

Definition abs_value (body : {bind Q}) : value (Abs body).
specialize (reflect_iff _ _ (is_value_refl (Abs body))) as Hrefl.
rewrite Hrefl. simpl. reflexivity.
Defined.

Fixpoint compute_eval_env (term : Q) : option (QContext * Q)%type :=
  match term with
  | ConsW hd tl =>
    if is_value hd then
      if is_value tl then
        match hd, tl with
        | Letter b, Word w => Some (□, ConsW (Letter b) (Word w))
        | _, _ => None
        end
      else
        match compute_eval_env tl with
        | None => None
        | Some (Ctl, redex) => Some (CConsWTl hd Ctl, redex)
        end
    else
      match compute_eval_env hd with
      | None => None
      | Some (Chd, redex) => Some (CConsWHd Chd tl, redex)
      end
  | App f arg =>
    if is_value f then
      if is_value arg then
        match f with
        | Abs body => Some (□, App (Abs body) arg)
        | _ => None
        end
      else
        match compute_eval_env arg with
        | None => None
        | Some (Carg, redex) => Some (CAppArg f Carg, redex)
        end
    else
      match compute_eval_env f with
      | None => None
      | Some (Cf, redex) => Some (CAppF Cf arg, redex) 
      end
  | Qif cond Qthen thenBody Qelse elseBody =>
    if is_value cond then
      if is_value thenBody then
        if is_value elseBody then
          match cond with
          | Letter b => Some (□, Qif (Letter b) Qthen thenBody Qelse elseBody)
          | _ => None
          end
        else
          match compute_eval_env elseBody with
          | None => None
          | Some (EElse, redex) => Some (CIfElse cond thenBody EElse, redex)
          end
      else
        match compute_eval_env thenBody with
        | None => None
        | Some (EThen, redex) => Some (CIfThen cond EThen elseBody, redex)
        end
    else
      match compute_eval_env cond with
      | None => None
      | Some (ECond, redex) => Some (CIfCond ECond thenBody elseBody, redex)
      end
  | _ => None
  end
.

Definition compute_step (term : Q) : option Q :=
  match compute_eval_env term with
  | None => None
  | Some (E, redex) =>
    match compute_toplevel_step redex with
    | None => None
    | Some reduced => Some (E ⋄ reduced)
    end
  end.

Lemma compute_eval_env_spec : ∀ (E : QContext) (t t' : Q),
  compute_eval_env t = Some (E, t') ↔ QEvalContext E ∧ t = E ⋄ t' ∧ (∃ u', t' →topQ u').
Proof.
  intros E t t'.
  split.
  - induction t as [x|b|w|hd IHhd tl IHtl|body IH|f IHf arg IHarg|
      cond IHcond thenBody IHthen elseBody IHelse ]
      in E, t' |- *;
    intro H.
    1, 2, 3, 5: simpl in H; discriminate H.
    + simpl in H.
      destruct (is_value hd) eqn:eqisvalhd.
      * destruct (is_value tl) eqn:eqisvaltl.
        -- destruct hd as [xhd|whd|bhd|hdhd tlhd|bodyhd|fhd arghd|condhd thenhd elsehd];
          try discriminate H.
          destruct tl as [xtl|wtl|btl|hdtl tltl|bodytl|ftl argtl|condtl thentl elsetl];
          try discriminate H.
          injection H; intros eq1 eq2; subst.
          repeat split.
          ++ constructor.
          ++ exists (Word (bhd :: wtl)).
            constructor.
        -- destruct (compute_eval_env tl) as [[Etl redextl]|] eqn:eqEtl.
          ++ injection H; intros eq1 eq2; subst.
            specialize (IHtl Etl t').
            destruct IHtl as [IHtl1 [IHtl2 IHtl3]].
            1: reflexivity.
            repeat split.
            ** constructor.
              --- apply (reflect_iff _ _ (is_value_refl hd)).
                assumption.
              --- assumption.
            ** simpl. f_equal.
              assumption.
            ** assumption.
          ++ discriminate H.
      * destruct (compute_eval_env hd) as [[Ehd redexhd]|].
        2: discriminate H.
        injection H; intros eq1 eq2; subst; clear H.
        specialize (IHhd Ehd t') as [IHhd1 [IHhd2 IHhd3]].
        1: reflexivity.
        subst.
        repeat split.
        -- constructor. assumption.
        -- assumption.
    + simpl in H.
      destruct (is_value f) eqn:eqisvalf.
      * destruct (is_value arg) eqn:eqisvalarg.
        -- destruct f as [xf|wf|bf|hdf tlf|bodyf|ff argf|condf thenf elsef];
          try discriminate H.
          injection H; intros eq1 eq2; subst.
          repeat split.
          ++ constructor.
          ++ eexists.
            constructor.
            apply (reflect_iff _ _ (is_value_refl arg)).
            assumption.
        -- destruct (compute_eval_env arg) as [[Earg redexarg]|] eqn:eqEarg.
          ++ injection H; intros eq1 eq2; subst.
            specialize (IHarg Earg t').
            destruct IHarg as [IHarg1 [IHarg2 IHarg3]].
            1: reflexivity.
            repeat split.
            ** constructor.
              --- apply (reflect_iff _ _ (is_value_refl f)).
                assumption.
              --- assumption.
            ** simpl. f_equal.
              assumption.
            ** assumption.
          ++ discriminate H.
      * destruct (compute_eval_env f) as [[Ef redexf]|].
        2: discriminate H.
        injection H; intros eq1 eq2; subst; clear H.
        specialize (IHf Ef t') as [IHf1 [IHf2 IHf3]].
        1: reflexivity.
        subst.
        repeat split.
        -- constructor. assumption.
        -- assumption.
    + simpl in H.
      destruct (is_value cond) eqn:Hisvalcond;
      [destruct (is_value thenBody) eqn:Hisvalthen;
       [destruct (is_value elseBody) eqn:Hisvalelse|]|].
      * apply (reflect_iff _ _ (is_value_refl _)) in Hisvalcond, Hisvalelse, Hisvalthen.
        destruct cond as [| | [|] | | | |]; try discriminate H.
        all: injection H as eq1 eq2; subst.
        all: repeat split; [constructor|].
        all: eexists; constructor; assumption.
      * apply (reflect_iff _ _ (is_value_refl _)) in Hisvalcond, Hisvalthen.
        destruct (compute_eval_env elseBody) as [[E' redex]|] eqn:eqE.
        2: discriminate H.
        injection H as eq1 eq2; subst.
        specialize (IHelse E' t') as [IHeval [IHelseeq IHelsered]]; [reflexivity|].
        repeat split.
        1: constructor; assumption.
        1: simpl; rewrite IHelseeq; reflexivity.
        1: assumption.
      * apply (reflect_iff _ _ (is_value_refl _)) in Hisvalcond.
        destruct (compute_eval_env thenBody) as [[E' redex]|] eqn:eqE.
        2: discriminate H.
        injection H as eq1 eq2; subst.
        specialize (IHthen E' t') as [IHeval [IHtheneq IHthenred]]; [reflexivity|].
        repeat split.
        1: constructor; assumption.
        1: simpl; rewrite IHtheneq; reflexivity.
        1: assumption.
      * destruct (compute_eval_env cond) as [[E' redex]|] eqn:eqE.
        2: discriminate H.
        injection H as eq1 eq2; subst.
        specialize (IHcond E' t') as [IHeval [IHcondeq IHcondred]]; [reflexivity|].
        repeat split.
        1: constructor; assumption.
        1: simpl; rewrite IHcondeq; reflexivity.
        1: assumption.        
  - induction E as [|Chd IH tl|hd Ctl IH|Cf IH arg|f Carg IH|
      CCond IH thenBody elseBody|cond CThen IH elseBody|cond thenBody CElse IH]
      in t, t' |-*;  intros [Heval [eq [u' Htopred]]]; subst.
    + simpl.
      inversion Htopred as [b w eq1 eq2|f arg Hvalue eq|
        thenBody elseBody Hvalthen Hvalelse eq1 eq2 |
        thenBody elseBody Hvalthen Hvalelse eq1 eq2]; try symmetry in eq2; subst.
      * simpl.
        reflexivity.
      * simpl.
        apply (reflect_iff _ _ (is_value_refl _)) in Hvalue.
        rewrite Hvalue.
        reflexivity.
      * apply (reflect_iff _ _ (is_value_refl _)) in Hvalthen, Hvalelse.
        simpl. rewrite Hvalthen, Hvalelse. reflexivity.
      * apply (reflect_iff _ _ (is_value_refl _)) in Hvalthen, Hvalelse.
        simpl. rewrite Hvalthen, Hvalelse. reflexivity.
    + inversion Heval as [ |G0 G1 Hevalhd | | | | | |]; subst.
      specialize (IH (Chd ⋄ t') t').
      simpl.
      rewrite IH.
      * destruct (Chd ⋄ t') eqn:eqt;
          try reflexivity;
          try (simpl in IH; discriminate IH).
        all: (repeat split; try reflexivity; try assumption).
        all: exists u'; assumption.
      * repeat split. 1: assumption.
        exists u'. assumption.
    + inversion Heval as [ | |hd' Ctl' Hval Heval' eq | | | | |]; subst.
      specialize (IH (Ctl ⋄ t') t').
      simpl.
      rewrite IH.
      * assert (Hisvalhd : is_value hd = true).
        {
          rewrite <- (reflect_iff _ _ (is_value_refl _)).
          assumption.
        }
        rewrite Hisvalhd.
        assert (HnotisvalCtl : is_value (Ctl ⋄ t') = false).
        {
          destruct (is_value (Ctl ⋄ t')) eqn:eqisvalC.
          + exfalso.
            eapply eval_context_value.
            2: apply Heval'.
            2: apply (reflect_iff _ _ (is_value_refl _)).
            2: apply eqisvalC.
            intro Hvalt'.
            eapply value_normal.
            * apply Hvalt'.
            * exists u'.
              apply step_toplevel_step.
              assumption.
          + reflexivity.
        }
        rewrite HnotisvalCtl.
        reflexivity.
      * repeat split.
        1: assumption.
        exists u'; assumption.
    + inversion Heval as [ | | | Cf' arg' Heval' eq1 | | | |]; subst.
      simpl.
      rewrite (IH (Cf ⋄ t') t').
      * destruct Cf as [| Chd' tl' | hd' Ctl' | Cf' arg' | f' Carg' | | |];
        simpl; try reflexivity.
        destruct t' as [x|w|b|hd tl|body|f'' arg''|cond'' thenBody'' elseBody'']
          eqn:eqt'; try reflexivity.
        all: exfalso.
        all: apply (value_normal t').
        all: try (rewrite eqt'; constructor).
        all: exists u'; rewrite eqt'; apply step_toplevel_step; assumption.
      * repeat split.
        -- assumption.
        -- exists u'.
          assumption.
    + inversion Heval as [ | | | | f' Carg' Hvalue Heval' eq | | |]; subst.
      simpl.
      rewrite (IH (Carg ⋄ t') t').
      * assert (Hisvalf : is_value f = true).
        {
          rewrite <- (reflect_iff _ _ (is_value_refl _)).
          assumption.
        }
        rewrite Hisvalf.
        assert (HnotisvalCarg : is_value (Carg ⋄ t') = false).
        {
          destruct (is_value (Carg ⋄ t')) eqn:eqisvalC.
          + exfalso.
            eapply eval_context_value.
            2: apply Heval'.
            2: apply (reflect_iff _ _ (is_value_refl _)).
            2: apply eqisvalC.
            intro Hvalt'.
            eapply value_normal.
            * apply Hvalt'.
            * exists u'.
              apply step_toplevel_step.
              assumption.
          + reflexivity.
        }
        rewrite HnotisvalCarg.
        reflexivity.
      * repeat split.
        -- assumption.
        -- exists u'.
          assumption.
    + inversion Heval as [| | | | |x1 x2 x3 Heval' x5| |]; subst.
      assert (Hnval : ¬ value (CCond ⋄ t')).
      {
        apply (eval_context_value CCond t').
        - intro Hval; apply value_normal in Hval.
          apply Hval.
          exists u'.
          apply step_toplevel_step.
          assumption.
        - assumption.
      }
      simpl.
      destruct (is_value (CCond ⋄ t')) eqn:Hisval.
      1: apply (reflect_iff _ _ (is_value_refl _)) in Hisval;
        exfalso; apply Hnval; assumption.
      specialize (IH (CCond ⋄ t') t').
      rewrite IH.
      2: split; [assumption | eexists; eexists; apply Htopred].
      reflexivity.
    + inversion Heval as [| | | | | |x1 x2 x3 Hval Heval' x5 |]; subst.
      apply (reflect_iff _ _ (is_value_refl _)) in Hval.
      simpl; rewrite Hval.
      assert (Hnval : ¬ value (CThen ⋄ t')).
      {
        apply (eval_context_value CThen t').
        - intro Hval'; apply value_normal in Hval'.
          apply Hval'.
          exists u'.
          apply step_toplevel_step.
          assumption.
        - assumption.
      }
      destruct (is_value (CThen ⋄ t')) eqn:Hisval.
      1: apply (reflect_iff _ _ (is_value_refl _)) in Hisval;
        exfalso; apply Hnval; assumption.
      erewrite IH.
      1: reflexivity.
      repeat split.
      * assumption.
      * exists u'; assumption.
    + inversion Heval as [| | | | | | |x1 x2 x3 Hvalcond Hvalthen Heval']; subst.
      apply (reflect_iff _ _ (is_value_refl _)) in Hvalcond, Hvalthen.
      simpl; rewrite Hvalcond, Hvalthen.
      assert (Hnval : ¬ value (CElse ⋄ t')).
      {
        apply (eval_context_value CElse t').
        - intro Hval'; apply value_normal in Hval'.
          apply Hval'.
          exists u'.
          apply step_toplevel_step.
          assumption.
        - assumption.
      }
      destruct (is_value (CElse ⋄ t')) eqn:Hisval.
      1: apply (reflect_iff _ _ (is_value_refl _)) in Hisval;
        exfalso; apply Hnval; assumption.
      erewrite IH.
      1: reflexivity.
      repeat split.
      * assumption.
      * exists u'; assumption.
Qed.

Definition compute_step_refl : ∀ (t u : Q),
  (t →Q u) ↔ compute_step t = Some u.
Proof.
  intros t u.
  split.
  - intro Hred.
    inversion Hred as [E t0 u0 t' u' Heval Hredtop eq1 eq2]; subst.
    specialize (compute_eval_env_spec E (E ⋄ t') t') as [_ Heval_env].
    unfold compute_step.
    rewrite Heval_env.
    2: {
      repeat split. 1: assumption.
      exists u'.
      assumption.
    }
    specialize (compute_toplevel_step_refl t' u') as [Hcompute_toplevel _].
    apply Hcompute_toplevel in Hredtop as eq_compute_toplevel.
    rewrite eq_compute_toplevel.
    reflexivity.
  - intro H.
    destruct (compute_eval_env t) eqn:eq_evalenv_t.
    + destruct p as [E t'].
      unfold compute_step in H.
      rewrite eq_evalenv_t in H.
      apply compute_eval_env_spec in eq_evalenv_t as [Heval [eq [u' Hredtop]]]; subst.
      apply (compute_toplevel_step_refl t' u') in Hredtop as eq_toplevel_step.
      rewrite eq_toplevel_step in H.
      injection H; clear H; intro H; subst.
      econstructor.
      * apply Heval.
      * apply Hredtop.
      * reflexivity.
      * reflexivity.
    + unfold compute_step in H.
      rewrite eq_evalenv_t in H.
      discriminate H.
Qed.   

Fixpoint compute_fuel (term : Q) (fuel : nat) : Q :=
  match fuel with
  | 0 => term
  | S fuel' => 
    match compute_step term with
    | None => term
    | Some term' => compute_fuel term' fuel'
    end
  end.

Definition Id := Abs (Var 0).

(* Compute (compute_fuel <{ IdLetter IdLetter IdLetter }> 3). *)