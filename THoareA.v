Require Export EnvLibA.
Require Export RelLibA.
Require Export PRelLibA.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

(*
Require Import Coq.Strings.String.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Logic.ProofIrrelevance.
*)

Require Import StaticSemA.
Require Import DynamicSemA.
Require Import TRInductA.
Require Import WeakenA.
Require Import TSoundnessA.
Require Import IdModTypeA.
Require Import DetermA.
Require Import AbbrevA.
Require Import HoareA.

Module THoare (IdT: IdModType) <: IdModType.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Module Hoare := Hoare IdT.
Export Hoare.

(*
Open Scope string_scope.
*)
Import ListNotations.


(** inverse big-step lemmas *)


Lemma BindN_BStepT1 (ftenv: funTC) (tenv: valTC)
      (fenv: funEnv) (env: valEnv) 
      (e1 e2: Exp) (v: Value) (s s': W)
      (k1: FEnvTyping fenv ftenv)
      (k2: EnvTyping env tenv) (t: VTyp)
      (k3: ExpTyping ftenv tenv fenv (BindN e1 e2) t) :
  EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s' (Val v)) ->
  (sigT2 (fun s1 : W =>
            (sigT (fun v1: Value =>
                     EClosure fenv env (Conf Exp s e1) (Conf Exp s1 (Val v1)))))
         (fun s1 : W =>
            EClosure fenv env (Conf Exp s1 e2) (Conf Exp s' (Val v)))).
  intros.
  inversion k3; subst.
  rename X0 into Y1.
  rename X1 into Y2.
  rename t into t2.
  
  assert (ExpSoundness ftenv tenv fenv e1 t1 Y1) as X1.
  eapply (ExpEval ftenv tenv fenv e1 t1 Y1).
  unfold ExpSoundness in X1.
  unfold SoundExp in X1.
  specialize (X1 k1 env k2 s).
  destruct X1 as [v1 k4 X1].
  destruct X1 as [s1 X1].

  generalize X1.
  intro.

  assert (ExpSoundness ftenv tenv fenv e2 t2 Y2) as X2.
  eapply (ExpEval ftenv tenv fenv e2 t2 Y2).
  unfold ExpSoundness in X2.
  unfold SoundExp in X2.
  specialize (X2 k1 env k2 s1).
  destruct X2 as [v2 k5 X2].
  destruct X2 as [s2 X2].
  
  eapply BindN_extended_congruence in X1.
  instantiate (1:=e2) in X1.
  
  assert (EStep fenv env (Conf Exp s1 (BindN (Val v1) e2)) (Conf Exp s1 e2)).
  constructor.
  eapply StepIsEClos in X3.
  
  assert (EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s1 e2)).
  eapply EClosConcat.
  exact X1.
  assumption.  

  assert (EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s2 (Val v2))).
  eapply EClosConcat.
  exact X4.
  assumption.

  assert (s' = s2 /\ v = v2).
  eapply ExpConfluence. 
  exact k3.
  auto.
  eauto.
  eauto.
  auto.

  destruct H.
  subst.

  econstructor.
  econstructor.  
  eauto. 
  auto.
Defined.


Lemma BindS_BStepT1 (ftenv: funTC) (tenv: valTC)
      (fenv: funEnv) (env: valEnv) 
      (e1 e2: Exp) (x: Id) (v: Value) (s s': W)
      (k1: FEnvTyping fenv ftenv)
      (k2: EnvTyping env tenv) (t: VTyp)
      (k3: ExpTyping ftenv tenv fenv (BindS x e1 e2) t) :
  EClosure fenv env (Conf Exp s (BindS x e1 e2)) (Conf Exp s' (Val v)) ->
  sigT (fun s1 : W =>
     (sigT2 (fun v1: Value =>
        EClosure fenv env (Conf Exp s e1) (Conf Exp s1 (Val v1)))
              (fun v1 : Value =>
        EClosure fenv ((x,v1)::env) (Conf Exp s1 e2) (Conf Exp s' (Val v))))).
  intros.
  inversion k3; subst.
  rename X0 into Y1.
  rename X1 into Y2.
  rename t into t2.
  
  assert (ExpSoundness ftenv tenv fenv e1 t1 Y1) as X1.
  eapply (ExpEval ftenv tenv fenv e1 t1 Y1).
  unfold ExpSoundness in X1.
  unfold SoundExp in X1.
  specialize (X1 k1 env k2 s).
  destruct X1 as [v1 k4 X1].
  destruct X1 as [s1 X1].

  generalize X1.
  intro.

  eapply BindS_extended_congruence in X1.
  instantiate (1:=e2) in X1.
  instantiate (1:=x) in X1.
  
  assert (EStep fenv env (Conf Exp s1 (BindS x (Val v1) e2))
                         (Conf Exp s1 (BindMS emptyE [(x,v1)] e2))).
  constructor.
  eapply StepIsEClos in X2.
  
  assert (EClosure fenv env (Conf Exp s (BindS x e1 e2))
                            (Conf Exp s1 (BindMS emptyE [(x,v1)] e2))).
  eapply EClosConcat.
  exact X1.
  assumption.  

  assert (ExpSoundness ftenv tenv' fenv e2 t2 Y2) as X4.
  eapply (ExpEval ftenv tenv' fenv e2 t2 Y2).
  unfold ExpSoundness in X4.
  unfold SoundExp in X4.

  assert (MatchEnvsT ValueTyping ((x, v1) :: env) tenv').
  econstructor.
  auto.
  auto.
  specialize (X4 k1 ((x,v1)::env) X5 s1).
  destruct X4 as [v2 k5 X4].
  destruct X4 as [s2 X4].

  assert (EClosure fenv env (Conf Exp s (BindS x e1 e2))
                            (Conf Exp s2 (Val v2))).
  eapply EClosConcat.
  exact X3.

  assert (EClosure fenv env (Conf Exp s1 (BindMS emptyE [(x, v1)] e2))
                            (Conf Exp s2 (BindMS emptyE [(x, v1)] (Val v2)))).
  eapply BindMS_extended_congruence.
  reflexivity.
  reflexivity.
  assumption.
  
  eapply EClosConcat.
  exact X6.
  eapply StepIsEClos.
  constructor.
  
  assert (s' = s2 /\ v = v2).
  eapply ExpConfluence. 
  exact k3.
  auto.
  eauto.
  eauto.
  auto.
  
  destruct H.
  subst.

  econstructor.
  econstructor.  
  eauto. 
  auto.
Defined.


Lemma Apply_BStepT1 (ftenv: funTC) (tenv: valTC)
      (fenv: funEnv) (env: valEnv)
      (f: Fun) (es: list Exp) (v: Value) (s s': W) 
      (k1: FEnvTyping fenv ftenv)
      (k2: EnvTyping env tenv) (t: VTyp)
      (k3: ExpTyping ftenv tenv fenv (Apply (QF f) (PS es)) t) :
   match f as f with
    | FC fenv' tenv' e0 e1 x n =>
  length tenv' = length es ->     
  EClosure fenv env (Conf Exp s (Apply (QF f) (PS es)))
                                (Conf Exp s' (Val v)) ->
  sigT (fun s1 : W =>
     (sigT2 (fun vs: list Value =>
               PrmsClosure fenv env (Conf Prms s (PS es))
                                    (Conf Prms s1 (PS (map Val vs))))
            (fun vs : list Value =>
    match n with
    | 0 =>   
      EClosure fenv' (mkVEnv tenv' vs) (Conf Exp s1 e0)
                                       (Conf Exp s' (Val v))
    | S n' =>
      EClosure ((x, FC fenv' tenv' e0 e1 x n') :: fenv')
         (mkVEnv tenv' vs) (Conf Exp s1 e1) (Conf Exp s' (Val v))
    end)))
   end.

Proof.
  destruct f.
  intros.
  inversion k3; subst.
  rename X1 into Y2.
  rename X2 into Y1.
  
  assert (PrmsSoundness ftenv tenv fenv (PS es) (PT (map snd fps)) Y1) as X1.
  eapply (PrmsEval ftenv tenv fenv (PS es) (PT (map snd fps)) Y1).
  unfold PrmsSoundness in X1.
  unfold SoundPrms in X1.
  specialize (X1 k1 env k2 s).
  destruct X1 as [es1 X1].
  destruct X1 as [vs k4 X1].
  destruct X1 as [k5 X1].
  destruct X1 as [s1 X1].
  
  generalize X1.
  intro.

  eapply Apply1_extended_congruence with (f:=(FC fenv0 tenv0 e0 e1 x n)) in X1.
  
  econstructor.
  instantiate (1:=s1). 

  generalize X2.
  intro P6.
  eapply PrmsClos_aux0 in P6.
  inversion k4; subst.
  
  rewrite map_length with (f:=Val) in P6.
  rewrite P6 in H.
  clear P6.

  econstructor.
  instantiate (1:=vs).
  auto.
  
  destruct n.
  (**)
  inversion Y2; subst.
  inversion X3; subst.
  
  assert (ExpSoundness ftenv0 fps fenv0 e0 t X5) as X6.
  eapply (ExpEval ftenv0 fps fenv0 e0 t X5).
  unfold ExpSoundness in X6.
  unfold SoundExp in X6.

  assert (MatchEnvsT ValueTyping (mkVEnv fps vs) fps).
  eapply prmsTypingAux_T.
  auto.
  eapply matchListsAux02_T.
  eauto.
  eauto.
  
  specialize (X6 X4 (mkVEnv fps vs) X7 s1).
  destruct X6 as [v2 k7 P5].
  destruct P5 as [s2 P5].
  
  assert (EClosure fenv env (Conf Exp s1
            (Apply (QF (FC fenv0 fps e0 e1 x 0)) (PS (map Val vs))))
                   (Conf Exp s1 (BindMS fenv0 (mkVEnv fps vs) e0))) as A1.        eapply StepIsEClos.
  econstructor.
  econstructor.
  reflexivity.
  exact H.
  reflexivity.

  assert (EClosure fenv env (Conf Exp s1 (BindMS fenv0 (mkVEnv fps vs) e0))
                 (Conf Exp s2 (BindMS fenv0 (mkVEnv fps vs) (Val v2)))) as A2.
  eapply BindMS_extended_congruence.
  reflexivity.
  reflexivity.
  eapply weaken.
  exact P5.

  assert (EClosure fenv env
                   (Conf Exp s2 (BindMS fenv0 (mkVEnv fps vs) (Val v2)))
                   (Conf Exp s2 (Val v2))) as A3.
  eapply StepIsEClos.
  econstructor.

  assert (EClosure fenv env
        (Conf Exp s (Apply (QF (FC fenv0 fps e0 e1 x 0)) (PS es)))
        (Conf Exp s2 (Val v2))) as A4.
  eapply EClosConcat.
  exact X1.
  eapply EClosConcat.
  exact A1.  
  eapply EClosConcat.
  exact A2.
  exact A3.

  assert (s' = s2 /\ v = v2).
  eapply ExpConfluence.
  exact k3.
  auto.
  eauto.
  eauto.
  auto.

  destruct H0. 
  subst.
  exact P5.
(**)
  
  inversion Y2; subst.
  inversion X3; subst.
  
  assert (ExpSoundness ftenv' fps fenv' e1 t X5) as X06.
  eapply (ExpEval ftenv' fps fenv' e1 t X5).
  unfold ExpSoundness in X06.
  unfold SoundExp in X06.

  assert (MatchEnvsT ValueTyping (mkVEnv fps vs) fps).
  eapply prmsTypingAux_T.
  auto.
  eapply matchListsAux02_T.
  eauto.
  eauto.

  assert (MatchEnvsT FunTyping fenv' ftenv').
  econstructor.
  auto.
  auto.
  
  specialize (X06 X8 (mkVEnv fps vs) X7 s1).
  destruct X06 as [v2 k7 P5].
  destruct P5 as [s2 P5].
  
  assert (EClosure fenv env (Conf Exp s1
            (Apply (QF (FC fenv0 fps e0 e1 x (S n))) (PS (map Val vs))))
                   (Conf Exp s1 (BindMS fenv' (mkVEnv fps vs) e1))) as A1.        eapply StepIsEClos.
  econstructor.
  econstructor.
  reflexivity.
  exact H.
  reflexivity.

  assert (EClosure fenv env (Conf Exp s1 (BindMS fenv' (mkVEnv fps vs) e1))
                 (Conf Exp s2 (BindMS fenv' (mkVEnv fps vs) (Val v2)))) as A2.
  eapply BindMS_extended_congruence.
  reflexivity.
  reflexivity.
  eapply weaken.
  exact P5.

  assert (EClosure fenv env
                   (Conf Exp s2 (BindMS fenv' (mkVEnv fps vs) (Val v2)))
                   (Conf Exp s2 (Val v2))) as A3.
  eapply StepIsEClos.
  econstructor.

  assert (EClosure fenv env
        (Conf Exp s (Apply (QF (FC fenv0 fps e0 e1 x (S n))) (PS es)))
        (Conf Exp s2 (Val v2))) as A4.
  eapply EClosConcat.
  exact X1.
  eapply EClosConcat.
  exact A1.  
  eapply EClosConcat.
  exact A2.
  exact A3.

  assert (s' = s2 /\ v = v2).
  eapply ExpConfluence.
  exact k3.
  auto.
  eauto.
  eauto.
  auto.

  destruct H0. 
  subst.
  exact P5.
Defined.


(*
Lemma BStep_convert 
      (fenv: funEnv) (env: valEnv)
      (e1 e2: Exp) (v: Value) (s s': W) :
  forall P, 
    (forall 
        (w1: forall (fenv: funEnv) (env: valEnv) (e:Exp) (s: W),
             sigT (fun v: Value =>
                 sigT (fun s': W => 
          EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v))))) 
        (w2: forall (e:Exp) (s s1 s2: W) (v1 v2: Value), 
           EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
           EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) -> 
           (s1 = s2) /\ (v1 = v2)),
      P fenv env e1 e2 v s s') ->
    (forall 
        (ftenv: funTC) (tenv: valTC) 
        (k1: FEnvTyping fenv ftenv)
        (k2: EnvTyping env tenv) (t: VTyp)
        (k3: ExpTyping ftenv tenv fenv e1 t),
      P fenv env e1 e2 v s s').
  intros.
  eapply X.
  intros.
  econstructor.
  instantiate (1:= extractRunValue ftenv tenv fenv e1 t k3 k1 env k2 s).
  econstructor.
  instantiate (1:= extractRunState ftenv tenv fenv e1 t k3 k1 env k2 s).
  eapply EvalIntro.
*)  


Lemma Prms_BStepT1 (ftenv: funTC) (tenv: valTC)
      (fenv: funEnv) (env: valEnv) 
      (e: Exp) (es: list Exp) (v: Value) (vs: list Value) (s s': W)
      (k1: FEnvTyping fenv ftenv)
      (k2: EnvTyping env tenv) (pt: PTyp)
      (k3: PrmsTyping ftenv tenv fenv (PS (e::es)) pt) :
  PrmsClosure fenv env (Conf Prms s (PS (e::es)))
                       (Conf Prms s' (PS (map Val (v::vs)))) ->
  (sigT2 (fun s1 : W =>
            (sigT (fun v1: Value =>
                     EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)))))
         (fun s1 : W =>
            PrmsClosure fenv env (Conf Prms s1 (PS es))
                                 (Conf Prms s' (PS (map Val vs))))).
  intros.
  inversion k3; subst.
  inversion X0; subst.
  rename X1 into Y1.
  rename X2 into Y3.
  rename y into t.
  rename l' into ts.
  
  assert (ExpSoundness ftenv tenv fenv e t Y1) as X1.
  eapply (ExpEval ftenv tenv fenv e t Y1).
  unfold ExpSoundness in X1.
  unfold SoundExp in X1.
  specialize (X1 k1 env k2 s).
  destruct X1 as [v1 k4 X1].
  destruct X1 as [s1 X1].

  generalize X1.
  intro Y4.

  assert (PrmsTyping ftenv tenv fenv (PS es) (PT ts)) as Y2.
  constructor.
  auto.
  
  assert (PrmsSoundness ftenv tenv fenv (PS es) (PT ts) Y2) as X2.
  eapply (PrmsEval ftenv tenv fenv (PS es) (PT ts) Y2).
  unfold PrmsSoundness in X2.
  unfold SoundPrms in X2.
  specialize (X2 k1 env k2 s1).
  destruct X2 as [es1 X2].
  destruct X2 as [vs1 Y5 X2].
  destruct X2 as [Y6 X2].
  destruct X2 as [s2 X2].

  inversion Y5; subst.

(**)
  assert (PrmsClosure fenv env (Conf Prms s (PS (e :: es)))
        (Conf Prms s2 (PS (map Val (v1 :: vs1))))).
  eapply Pars_extended_congruence4.
  eauto.
  exact X2.
  
  constructor 1 with (x:=s1).
  constructor 1 with (x:=v1).
  exact X1.

  assert (s' = s2 /\ vs = vs1).
  eapply PrmsConfluence in X.
  specialize (X X3).
  destruct X.
  split.
  exact H.
  inversion H0; subst.
  auto.
  eauto.
  auto.
  auto.
  destruct H.
  rewrite H.
  rewrite H0.
  auto.
Defined.  



Lemma Prms_BStepT2 (ftenv: funTC) (tenv: valTC)
      (fenv: funEnv) (env: valEnv) 
      (e: Exp) (es: list Exp) (v: Value) (vs: list Value) (s s': W)
      (k1: FEnvTyping fenv ftenv)
      (k2: EnvTyping env tenv) (pt: PTyp)
      (k3: PrmsTyping ftenv tenv fenv (PS (e::es)) pt) :
  PrmsClosure fenv env (Conf Prms s (PS (e::es)))
                       (Conf Prms s' (PS (map Val (v::vs)))) ->
  (sigT2 (fun s1 : W =>
            (EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v))))
         (fun s1 : W =>
            PrmsClosure fenv env (Conf Prms s1 (PS es))
                                 (Conf Prms s' (PS (map Val vs))))).
  intros.
  inversion k3; subst.
  inversion X0; subst.
  rename X1 into Y1.
  rename X2 into Y3.
  rename y into t.
  rename l' into ts.
  
  assert (ExpSoundness ftenv tenv fenv e t Y1) as X1.
  eapply (ExpEval ftenv tenv fenv e t Y1).
  unfold ExpSoundness in X1.
  unfold SoundExp in X1.
  specialize (X1 k1 env k2 s).
  destruct X1 as [v1 k4 X1].
  destruct X1 as [s1 X1].
 
(*
  generalize X1.
  intro Y4.
*)
  assert (PrmsTyping ftenv tenv fenv (PS es) (PT ts)) as Y2.
  constructor.
  auto.
  
  assert (PrmsSoundness ftenv tenv fenv (PS es) (PT ts) Y2) as X2.
  eapply (PrmsEval ftenv tenv fenv (PS es) (PT ts) Y2).
  unfold PrmsSoundness in X2.
  unfold SoundPrms in X2.
  specialize (X2 k1 env k2 s1).
  
  destruct X2 as [es1 X2].
  destruct X2 as [vs1 Y5 X2].
  destruct X2 as [Y6 X2].
  destruct X2 as [s2 X2].
  inversion Y5; subst.

  assert (PrmsClosure fenv env (Conf Prms s (PS (e :: es)))
        (Conf Prms s2 (PS (map Val (v1 :: vs1))))).
  eapply Pars_extended_congruence4.
  eauto.
  exact X2.
  
  
  (**)
  assert (s' = s2 /\ (v::vs) = (v1::vs1)).
  eapply PrmsConfluence in X.
  specialize (X X3).
  exact X.

  eauto.
  auto.
  auto.
  destruct H.
  injection H0.
  intros.
  
  constructor 1 with (x:=s1).
  rewrite H2.
  auto.
  rewrite H.
  rewrite H1.
  auto.
Defined.  


Lemma IfThenElse_BStepT1 (ftenv: funTC) (tenv: valTC)
      (fenv: funEnv) (env: valEnv) 
      (e1 e2 e3: Exp) (v: Value) (s s': W)
      (k1: FEnvTyping fenv ftenv)
      (k2: EnvTyping env tenv) (t: VTyp)
      (k3: ExpTyping ftenv tenv fenv (IfThenElse e1 e2 e3) t) :
  EClosure fenv env (Conf Exp s (IfThenElse e1 e2 e3)) (Conf Exp s' (Val v)) ->
  sum (sigT2 (fun s1 : W =>
        EClosure fenv env (Conf Exp s e1) (Conf Exp s1 (Val (cst bool true))))           (fun s1 : W =>
             (EClosure fenv env (Conf Exp s1 e2) (Conf Exp s' (Val v)))))
      (sigT2 (fun s1 : W =>
      EClosure fenv env (Conf Exp s e1) (Conf Exp s1 (Val (cst bool false))))           (fun s1 : W => 
             (EClosure fenv env (Conf Exp s1 e3) (Conf Exp s' (Val v))))).
Proof.
  intros.
  inversion k3; subst.
  
  assert (ExpSoundness ftenv tenv fenv e1 Bool X0) as Y1.
  eapply (ExpEval ftenv tenv fenv e1 Bool X0).
  unfold ExpSoundness in Y1.
  unfold SoundExp in Y1.
  specialize (Y1 k1 env k2 s).

  assert (ExpSoundness ftenv tenv fenv e2 t X1) as Y2.
  eapply (ExpEval ftenv tenv fenv e2 t X1).
  unfold ExpSoundness in Y2.
  unfold SoundExp in Y2.
  specialize (Y2 k1 env k2).

  assert (ExpSoundness ftenv tenv fenv e3 t X2) as Y3.
  eapply (ExpEval ftenv tenv fenv e3 t X2).
  unfold ExpSoundness in Y3.
  unfold SoundExp in Y3.
  specialize (Y3 k1 env k2).

  destruct Y1 as [v1 H1 Y1].
  destruct Y1 as [s1 Y1].
  specialize (Y2 s1).
  specialize (Y3 s1).
  destruct v1.
  destruct v0. 
  inversion H1; subst.
  simpl in *.
  subst T.
  inversion H; subst.
  clear H2.

  destruct v0.

(**)
  destruct Y2 as [v2 H2 Y2].
  destruct Y2 as [s2 Y2].
  
  assert (EClosure fenv env (Conf Exp s (IfThenElse e1 e2 e3))
                   (Conf Exp s2 (Val v2))).  
  eapply EClosConcat.
  eapply IfThenElse_extended_congruence.
  exact Y1.
  econstructor.
  econstructor.
  exact Y2.

  assert (s' = s2 /\ v = v2).
  eapply (ExpConfluence ftenv tenv fenv (IfThenElse e1 e2 e3) t k3).
  auto.
  eauto.
  exact X.
  auto.
  destruct H.

  constructor.
  econstructor 1 with (x:=s1).
  auto.
  rewrite H.
  rewrite H3.
  exact Y2.

(**)
  clear Y2.
  rename Y3 into Y2.
  destruct Y2 as [v2 H2 Y2].
  destruct Y2 as [s2 Y2].
  
  assert (EClosure fenv env (Conf Exp s (IfThenElse e1 e2 e3))
                   (Conf Exp s2 (Val v2))).  
  eapply EClosConcat.
  eapply IfThenElse_extended_congruence.
  exact Y1.
  econstructor.
  econstructor.
  exact Y2.

  assert (s' = s2 /\ v = v2).
  eapply (ExpConfluence ftenv tenv fenv (IfThenElse e1 e2 e3) t k3).
  auto.
  eauto.
  exact X.
  auto.
  destruct H.

  constructor 2.
  econstructor 1 with (x:=s1).
  auto.
  rewrite H.
  rewrite H3.
  exact Y2.
Qed.
  


Lemma Apply_BStepT2
      (ftenv: funTC) (tenv: valTC)
      (fenv: funEnv) (env: valEnv)
      (f: Fun) (es: list Exp) (v: Value) (s s': W) 
      (k1: FEnvTyping fenv ftenv)
      (k2: EnvTyping env tenv) (t: VTyp)
      (k3: ExpTyping ftenv tenv fenv (Apply (QF f) (PS es)) t) :
  EClosure fenv env (Conf Exp s (Apply (QF f) (PS es)))
                                (Conf Exp s' (Val v)) ->
  sigT (fun s1 : W =>
          (sigT2 (fun vs: list Value =>   
               PrmsClosure fenv env (Conf Prms s (PS es))
                                    (Conf Prms s1 (PS (map Val vs))))
            (fun vs : list Value =>
               EClosure fenv env (Conf Exp s1 (Apply (QF f)
                                                  (PS (map Val vs))))
                                 (Conf Exp s' (Val v))))).
Proof.
  intros.
  inversion k3; subst.
  rename X1 into Y2.
  rename X2 into Y1.
  
  assert (PrmsSoundness ftenv tenv fenv (PS es) (PT (map snd fps)) Y1) as X1.
  eapply (PrmsEval ftenv tenv fenv (PS es) (PT (map snd fps)) Y1).
  unfold PrmsSoundness in X1.
  unfold SoundPrms in X1.
  specialize (X1 k1 env k2 s).
  destruct X1 as [es1 X1].
  destruct X1 as [vs k4 X1].
  destruct X1 as [k5 X1].
  destruct X1 as [s1 X1].
   
  generalize X1.
  intro.

  eapply Apply1_extended_congruence with (f:=f) in X1.
  
  econstructor 1 with (x:=s1).
  
  inversion k4; subst.

  econstructor 1 with (x:=vs).
  auto.

  assert (ExpTyping ftenv tenv fenv (Apply (QF f) (PS (map Val vs))) t).
  econstructor.
  reflexivity.
  auto.
  eauto.
  eapply weakenPrmsTyping in k5.
  instantiate (1:=fenv) in k5.
  instantiate (1:=tenv) in k5.
  instantiate (1:=ftenv) in k5.
  simpl in k5.
  auto.
  constructor.
  auto.

  set (Apply (QF f) (PS (map Val vs))) as e.

  assert (ExpSoundness ftenv tenv fenv e t X3) as X6.
  eapply (ExpEval ftenv tenv fenv e t X3).
  unfold ExpSoundness in X6.
  unfold SoundExp in X6.
  specialize (X6 X0 env k2 s1).
  destruct X6 as [v2 H0 X6].
  destruct X6 as [s2 X6].

  assert (EClosure fenv env (Conf Exp s (Apply (QF f) (PS es)))
                   (Conf Exp s2 (Val v2))).
  eapply EClosConcat.
  exact X1.
  auto.

  assert (s' = s2 /\ v = v2).
  eapply ExpConfluence.
  exact k3.
  auto.
  eauto.
  eauto.
  auto.
  destruct H.
  rewrite H.
  rewrite H1.
  auto.
Qed.
  

Lemma Apply_BStepT2t
      (ftenv: funTC) (tenv: valTC)
      (fenv: funEnv) (env: valEnv)
      (f: Fun) (es: list Exp) (v: Value) (s s': W) 
      (k1: FEnvTyping fenv ftenv)
      (k2: EnvTyping env tenv) (t: VTyp) (pt: PTyp)
      (k3: ExpTyping ftenv tenv fenv (Apply (QF f) (PS es)) t)
      (k0: PrmsTyping ftenv tenv fenv (PS es) pt) :
  EClosure fenv env (Conf Exp s (Apply (QF f) (PS es)))
                                (Conf Exp s' (Val v)) ->
  sigT (fun s1 : W =>
          (sigT2 (fun vs: list Value =>
               (PrmsTyping ftenv tenv fenv (PS (map Val vs)) pt *       
               PrmsClosure fenv env (Conf Prms s (PS es))
                                    (Conf Prms s1 (PS (map Val vs))))%type)
            (fun vs : list Value =>
               EClosure fenv env (Conf Exp s1 (Apply (QF f)
                                                  (PS (map Val vs))))
                                 (Conf Exp s' (Val v))))).
Proof.
  intros.
  inversion k3; subst.
  rename X1 into Y2.
  rename X2 into Y1.
  
  assert (PrmsSoundness ftenv tenv fenv (PS es) (PT (map snd fps)) Y1) as X1.
  eapply (PrmsEval ftenv tenv fenv (PS es) (PT (map snd fps)) Y1).
  unfold PrmsSoundness in X1.
  unfold SoundPrms in X1.
  specialize (X1 k1 env k2 s).
  destruct X1 as [es1 X1].
  destruct X1 as [vs k4 X1].
  destruct X1 as [k5 X1].
  destruct X1 as [s1 X1].
   
  generalize X1.
  intro.

  eapply Apply1_extended_congruence with (f:=f) in X1.
  
  econstructor 1 with (x:=s1).
  
  inversion k4; subst.

  econstructor 1 with (x:=vs).
  split.
  
  assert (pt = PT (map snd fps)).
  eapply PrmsStrongTyping.
  exact k0.
  auto.
  eauto.
  auto.
  rewrite H.
  auto.

  eapply weakenPrmsTyping in k5.
  instantiate (1:=fenv) in k5.
  instantiate (1:=tenv) in k5.
  instantiate (1:=ftenv) in k5.
  simpl in k5.
  auto.
  constructor.
  auto.

  exact X2.
    
  assert (ExpTyping ftenv tenv fenv (Apply (QF f) (PS (map Val vs))) t).
  econstructor.
  reflexivity.
  auto.
  eauto.
  eapply weakenPrmsTyping in k5.
  instantiate (1:=fenv) in k5.
  instantiate (1:=tenv) in k5.
  instantiate (1:=ftenv) in k5.
  simpl in k5.
  auto.
  constructor.
  auto.

  set (Apply (QF f) (PS (map Val vs))) as e.

  assert (ExpSoundness ftenv tenv fenv e t X3) as X6.
  eapply (ExpEval ftenv tenv fenv e t X3).
  unfold ExpSoundness in X6.
  unfold SoundExp in X6.
  specialize (X6 X0 env k2 s1).
  destruct X6 as [v2 H0 X6].
  destruct X6 as [s2 X6].

  assert (EClosure fenv env (Conf Exp s (Apply (QF f) (PS es)))
                   (Conf Exp s2 (Val v2))).
  eapply EClosConcat.
  exact X1.
  auto.

  assert (s' = s2 /\ v = v2).
  eapply ExpConfluence.
  exact k3.
  auto.
  eauto.
  eauto.
  auto.
  destruct H.
  rewrite H.
  rewrite H1.
  auto.
Qed.
  


(**************************************************************************)


Definition THoareTriple_Eval
           (P : W -> Prop) (Q : Value -> W -> Prop)
           (fenv: funEnv) (env: valEnv)
           (e: Exp) : Prop :=
  forall (ftenv: funTC) (tenv: valTC) 
         (k1: FEnvTyping fenv ftenv)
         (k2: EnvTyping env tenv)
         (t: VTyp)
         (k3: ExpTyping ftenv tenv fenv e t) 
         (s s': W) (v: Value),
    EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v)) ->
    P s -> Q v s'.


Definition THoarePrmsTriple_Eval
           (P : W -> Prop) (Q : list Value -> W -> Prop)
           (fenv: funEnv) (env: valEnv)
           (ps: Prms) : Prop :=
  forall (ftenv: funTC) (tenv: valTC) 
         (k1: FEnvTyping fenv ftenv)
         (k2: EnvTyping env tenv)
         (pt: PTyp)
         (k3: PrmsTyping ftenv tenv fenv ps pt)
         (s s': W) (vs: list Value),
    PrmsClosure fenv env (Conf Prms s ps) (Conf Prms s'
                                               (PS (map Val vs))) ->
    P s -> Q vs s'.

Inductive QFClosure :
     funEnv -> AConfig QFun -> AConfig QFun -> Type :=
  | QFC_Base : forall (fenv: funEnv) (p: AConfig QFun), 
              QFClosure fenv p p 
  | QFC_Step : forall (fenv: funEnv) (p1 p2: AConfig QFun),
           QFStep fenv p1 p2 ->
           QFClosure fenv p1 p2.


Definition THoareFunTripleA_Eval
      (P: W -> Prop) (Q: Value -> W -> Prop)  
      (fenv: funEnv) 
      (qf: QFun) : Prop := 
  forall (ftenv: funTC) 
         (k1: FEnvTyping fenv ftenv)
         (ft: FTyp)
         (k2: QFunTyping ftenv fenv qf ft)
         (s s': W) (f: Fun),
  QFClosure fenv (Conf QFun s qf) (Conf QFun s' (QF f)) -> 
  match f with
    | FC fenv' tenv' e0 e1 x n =>
      forall vs: list Value,
        let env' := mkVEnv tenv' vs in        
        EnvTyping env' tenv' ->   
    match n with
      | 0 =>        
        THoareTriple_Eval P Q fenv' (mkVEnv tenv' vs) e0
      | S n' =>        
        THoareTriple_Eval P Q ((x,FC fenv' tenv' e0 e1 x n')::fenv')
                           (mkVEnv tenv' vs) e1
    end
  end.


Definition THoareFunTriple_Eval
      (P: W -> Prop) (Q: Value -> W -> Prop)  
      (fenv: funEnv) (env: valEnv)
      (qf: QFun) : Prop := 
  forall (ftenv: funTC) 
         (k1: FEnvTyping fenv ftenv)
         (ft: FTyp)
         (k2: QFunTyping ftenv fenv qf ft)
         (s s': W) (f: Fun),
  QFClosure fenv (Conf QFun s qf) (Conf QFun s' (QF f)) -> 
  match f with
    | FC fenv' tenv' e0 e1 x n =>  
    EnvTyping env tenv' ->   
    match n with
      | 0 =>        
        THoareTriple_Eval P Q fenv' env e0
      | S n' =>        
        THoareTriple_Eval P Q ((x,FC fenv' tenv' e0 e1 x n')::fenv')
                           env e1
    end
  end.

(***********************************************************************)


Definition IHoareTriple_Eval
           (P : W -> Prop) (Q : Value -> W -> Prop)
           (e: Exp) : Prop :=
  forall (ftenv: funTC) (tenv: valTC) 
         (fenv: funEnv) (env: valEnv)
         (k1: FEnvTyping fenv ftenv)
         (k2: EnvTyping env tenv)
         (t: VTyp) 
         (k3: ExpTyping ftenv tenv fenv e t)
         (s: W), 
  P s -> Q (extractRunValue ftenv tenv fenv e t k3 k1 env k2 s)
           (extractRunState ftenv tenv fenv e t k3 k1 env k2 s).


Definition IHoarePrmsTriple_Eval
           (P : W -> Prop) (Q : list Value -> W -> Prop)
           (ps: Prms) : Prop :=
  forall (ftenv: funTC) (tenv: valTC) 
         (fenv: funEnv) (env: valEnv)
         (k1: FEnvTyping fenv ftenv)
         (k2: EnvTyping env tenv)
         (pt: PTyp)
         (k3: PrmsTyping ftenv tenv fenv ps pt)
         (s: W), 
  P s -> Q (extractPRunValue ftenv tenv fenv ps pt k3 k1 env k2 s)
           (extractPRunState ftenv tenv fenv ps pt k3 k1 env k2 s).


(*************************************************************************)

(*
Lemma THoare_weaken (P : W -> Prop) (Q : Value -> W -> Prop)
           (fenv fenv': funEnv) (env env': valEnv)
           (e: Exp) :  
  THoareTriple_Eval P Q (fenv++fenv') (env++env') e ->
  THoareTriple_Eval P Q fenv env e.
  unfold THoareTriple_Eval.
  intros.
*)  
  

Lemma BindN_VHTT1 (P0 P1: W -> Prop) (P2: Value -> W -> Prop)
      (fenv: funEnv) (env: valEnv)
      (e1 e2: Exp) :
  THoareTriple_Eval P0 (fun _ => P1) fenv env e1 ->
  THoareTriple_Eval P1 P2 fenv env e2 ->
  THoareTriple_Eval P0 P2 fenv env (BindN e1 e2) .
  unfold THoareTriple_Eval.
  intros.
  eapply BindN_BStepT1 in X.
  destruct X as [s1 X].
  destruct X as [v1 X].
  inversion k3; subst.
  eapply (H0 ftenv tenv).
  auto.
  auto.
  eauto.
  eauto.
  eapply (H ftenv tenv).
  auto. 
  auto.
  eauto.
  eauto.
  auto.
  eauto.
  eauto.
  eauto.
Qed.



Lemma BindN_VHTT2 (P0: W -> Prop) (P1 P2: Value -> W -> Prop)
      (fenv: funEnv) (env: valEnv)
      (e1 e2: Exp) :
  THoareTriple_Eval P0 P1 fenv env e1 ->
  (forall v: Value, THoareTriple_Eval (P1 v) P2 fenv env e2) ->
  THoareTriple_Eval P0 P2 fenv env (BindN e1 e2) .
  unfold THoareTriple_Eval.
  intros.
  eapply BindN_BStepT1 in X.
  destruct X as [s1 X].
  destruct X as [v1 X].
  inversion k3; subst.
  eapply (H0 v1 ftenv tenv).
  auto.
  auto.
  eauto.
  eauto.
  eapply (H ftenv tenv).
  auto. 
  auto.
  eauto.
  eauto.
  auto.
  eauto.
  eauto.
  eauto.
Qed.

 
Lemma BindS_VHTT1 (P0: W -> Prop) (P1 P2: Value -> W -> Prop)
        (fenv: funEnv) (env: valEnv)     
        (e1 e2: Exp) (x: Id) :
  THoareTriple_Eval P0 P1 fenv env e1 ->
  (forall v, THoareTriple_Eval (P1 v) P2 fenv ((x,v)::env) e2) ->
  THoareTriple_Eval P0 P2 fenv env (BindS x e1 e2).
Proof.
  unfold THoareTriple_Eval.
  intros.
  eapply BindS_BStepT1 in X.
  destruct X as [s1 X].
  destruct X as [v1 X].
  inversion k3; subst.
  eapply (H0 v1 ftenv tenv').
  auto.
  econstructor.
  assert (v1 = extractRunValue ftenv tenv fenv e1 t1 X0 k1 env k2 s).
  eapply (proj2 (EvalElim ftenv tenv fenv e1 t1 X0 k1 env k2 s s1 v1 X)).
  rewrite H2.
  exact (extractRunTyping ftenv tenv fenv e1 t1 X0 k1 env k2 s).
  auto.
  eauto.
  eauto.
  eapply (H ftenv tenv).
  auto.
  auto.
  eauto.
  eauto.
  auto.
  eauto.
  eauto.
  eauto.
Qed.  
  
  
Lemma Apply_VHTT1 (P0: W -> Prop) (P1: list Value -> W -> Prop)
                 (P2: Value -> W -> Prop)  
   (fenv: funEnv) (env: valEnv) (f: Fun) (es: list Exp) : 
  THoarePrmsTriple_Eval P0 P1 fenv env (PS es) ->
  match f with
  | FC fenv' tenv' e0 e1 x n => 
    length tenv' = length es /\     
    match n with
    | 0 => (forall vs: list Value,  
          THoareTriple_Eval (P1 vs) P2 fenv' (mkVEnv tenv' vs) e0)
    | S n' => (forall vs: list Value,
          THoareTriple_Eval (P1 vs) P2 ((x,FC fenv' tenv' e0 e1 x n')::fenv')
                           (mkVEnv tenv' vs) e1)
    end
  end ->             
  THoareTriple_Eval P0 P2 fenv env (Apply (QF f) (PS es)).
Proof.
  unfold THoareTriple_Eval, THoarePrmsTriple_Eval.
  intros.
  generalize (Apply_BStepT1 ftenv tenv fenv env f es v s s' k1 k2 t k3).
  intro P.
  destruct f.
  destruct H0.
  specialize (P H0 X).
  destruct P as [s1 P].
  destruct P as [vs P].
  inversion k3; subst.
  inversion X1; subst.
  specialize (H ftenv tenv k1 k2 (PT (map snd fps)) X2 s s1 vs P H1).

  assert (tenv0 = fps).
  inversion X3; subst.
  auto.
  auto.
  inversion H3; subst.
  clear H4.

  assert (length es = length (map Val vs)) as W.
  eapply PrmsClos_aux0.
  eauto.
  rewrite map_length with (f:=Val) in W. 
  
  assert (EnvTyping (mkVEnv fps vs) fps) as Q.
  eapply mkEnvTyping_aux0.
  rewrite <- W.
  auto.

  eapply prmsTyping_aux4.
  eauto.
  eauto.
  eauto.
  eauto.
  
  destruct n.

  inversion X3; subst.  
  eapply H2.
  eauto.
  eauto.
  eauto.
  eauto.
  auto.

  inversion X3; subst.
  eapply H2.
  eauto.
  instantiate (1:= (x, FT fps t) :: ftenv0).
  econstructor.
  auto.
  auto.
  eauto.
  eauto.
  auto.
  eauto.
  auto.
Qed.



Lemma Apply_VHTT2 (P0: W -> Prop) (P1: list Value -> W -> Prop)
                 (P2: Value -> W -> Prop)
                 (fenv: funEnv) (env: valEnv) (f: Fun) (es: list Exp) :
   THoarePrmsTriple_Eval P0 P1 fenv env (PS es) ->
   (forall vs,  
       THoareTriple_Eval (P1 vs) P2 fenv env
                                 (Apply (QF f) (PS (map Val vs)))) ->
   THoareTriple_Eval P0 P2 fenv env (Apply (QF f) (PS es)).
Proof.
  unfold THoareTriple_Eval, THoarePrmsTriple_Eval.
  intros.
  
  inversion k3; subst.
  generalize (Apply_BStepT2t ftenv tenv fenv env f es v s s' k1 k2 t
                             (PT (map snd fps)) k3 X2).
  intro P.

  specialize (P X).
  destruct P as [s1 P].
  destruct P as [vs P].
  inversion k3; subst.
  destruct P as [Q1 Q2].

  specialize (H ftenv tenv k1 k2 (PT (map snd fps)) X2 s s1 vs Q2 H1).
  assert (ExpTyping ftenv tenv fenv (Apply (QF f) (PS (map Val vs))) t).
  econstructor.
  reflexivity.
  auto.
  eauto.

  assert (FT fps t = FT fps0 t). 
  eapply QFunStrongTyping.
  eauto.
  auto.
  eauto.
  auto.
  inversion H2; subst.
  auto.
  
  eapply H0.
  eauto.
  eauto.
  eauto.
  eauto.
  auto.
Qed.



Lemma QFun_VHTT (P1: W -> Prop) (P2: Value -> W -> Prop)
      (fenv: funEnv) (env: valEnv) (x: Id) (f: Fun) (es: list Exp) :  
  findET fenv x f ->
  THoareTriple_Eval P1 P2 fenv env (Apply (QF f) (PS es))  ->
  THoareTriple_Eval P1 P2 fenv env (Apply (FVar x) (PS es)).
Proof.  
  unfold THoareTriple_Eval.
  intros.
  assert (sigT2 (findET ftenv x) (fun t: FTyp => FunTyping f t)).
  {- eapply ExRelValT1.
     eassumption.
     assumption.
  }  
  destruct X1 as [ft Z1 Z2].
  inversion k3; subst.  
  inversion X2; subst.

  eapply MatchEnvs2BT_find1 in X4.
  destruct X4 as [Z3 Z4].

  destruct ft.
  inversion Z1; subst.
  inversion Z4; subst.
  rewrite H1 in H2.
  inversion H2; subst.
  
  eapply H.
  - exact k1.
  - exact k2.
  - instantiate (1:=t).
    econstructor.
    + reflexivity.
    + assumption.
    + instantiate (1:=fps).
      econstructor.
      auto.
    + auto.

  - clear H2.
    instantiate (1:=s).
    inversion X0; subst.
    inversion X4; subst.
    inversion X6; subst.
    inversion X7; subst.
    inversion X; subst. 
    rewrite H2 in H3.
    inversion H3; subst.
    auto.
  - auto.
Qed.  


Lemma Apply_VHTT3 (P0: W -> Prop) (P1: list Value -> W -> Prop)
                 (P2: Value -> W -> Prop)
                 (fenv: funEnv) (env: valEnv) (x: Id) (f: Fun)
                 (es: list Exp) :
   THoarePrmsTriple_Eval P0 P1 fenv env (PS es) ->
   findET fenv x f->
   (forall vs ,
       THoareTriple_Eval (P1 vs) P2 fenv env
                         (Apply (QF f) (PS (map Val vs))))  -> 
   THoareTriple_Eval P0 P2 fenv env (Apply (FVar x) (PS es)).
Proof.
   intros.  
   eapply QFun_VHTT.
   eauto.
   eapply Apply_VHTT2.
   eauto.
   auto.
Qed.



Lemma Prms_VHTT1 (P0: W -> Prop) (P1: Value -> W -> Prop)
                  (P2: list Value -> W -> Prop) 
        (fenv: funEnv) (env: valEnv)     
        (e: Exp) (es: list Exp) :
  THoareTriple_Eval P0 P1 fenv env e ->
  (forall v: Value,
     THoarePrmsTriple_Eval (P1 v) (fun vs => P2 (v::vs)) fenv env (PS es)) ->
  THoarePrmsTriple_Eval P0 P2 fenv env (PS (e::es)).
Proof.
  unfold THoareTriple_Eval, THoarePrmsTriple_Eval.
  intros.
  inversion k3; subst.
  inversion X0; subst.
  rename y into t.
  rename l' into ts.
  
  destruct vs.
  eapply PrmsClos_aux0 in X.
  simpl in X.
  intuition.

  eapply Prms_BStepT2 in X.
  destruct X as [s1 X].
  specialize (H ftenv tenv k1 k2 t X1 s s1 v X H1).
  assert (PrmsTyping ftenv tenv fenv (PS es) (PT ts)).
  constructor.
  auto.
  specialize (H0 v ftenv tenv k1 k2 (PT ts) X3 s1 s' vs p H).
  auto.
  eauto.
  eauto.
  eauto.
Defined.  
  

Lemma IfTheElse_VHTT1 (P0: W -> Prop) (P1 P2: Value -> W -> Prop) 
        (fenv: funEnv) (env: valEnv)     
        (e1 e2 e3: Exp) :
  THoareTriple_Eval P0 P1 fenv env e1 ->
  THoareTriple_Eval (P1 (cst bool true)) P2 fenv env e2 ->
  THoareTriple_Eval (P1 (cst bool false)) P2 fenv env e3 ->
  THoareTriple_Eval P0 P2 fenv env (IfThenElse e1 e2 e3).
Proof.
  unfold THoareTriple_Eval.
  intros.
  generalize (IfThenElse_BStepT1
                ftenv tenv fenv env e1 e2 e3 v s s' k1 k2 t k3 X).
  intro.
  inversion k3; subst.
  specialize (H ftenv tenv k1 k2 Bool X1 s).
  specialize (H0 ftenv tenv k1 k2 t X2).
  specialize (H1 ftenv tenv k1 k2 t X3).
  destruct X0.

  destruct s0 as [s1 X0 X4].
  eapply H0.
  exact X4.
  eapply H.
  exact X0.
  exact H2.

  destruct s0 as [s1 X0 X4].
  eapply H1.
  exact X4.
  eapply H.
  exact X0.
  exact H2.
Qed.  


End THoare.