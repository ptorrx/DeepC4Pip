
Require Export Basics.

Require Export EnvLibA.
Require Export RelLibA.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.ProofIrrelevance.

Require Import StaticSemA.
Require Import DynamicSemA.
Require Import TRInductA.
Require Import WeakenA.
Require Import TSoundnessA.
Require Import SReducA.

Require Import Coq.Logic.EqdepFacts.

Module Determ (IdT: IdModType) <: IdModType.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Module SReducI := SReduc IdT.
Export SReducI.


(** stepwise determinism *)

Definition UniqueEStep 
                     (fenv: funEnv) (env: valEnv)
                     (n n1 n2: W) (e e1 e2: Exp) :=
    EStep fenv env (Conf Exp n e) ((Conf Exp n1 e1)) ->
    EStep fenv env (Conf Exp n e) ((Conf Exp n2 e2)) -> 
        (n1 = n2) /\ (e1 = e2).


Definition UniquePStep
                     (fenv: funEnv) (env: valEnv)
                     (n n1 n2: W) (ps ps1 ps2: Prms) :=
    PrmsStep fenv env (Conf Prms n ps) ((Conf Prms n1 ps1)) ->
    PrmsStep fenv env (Conf Prms n ps) ((Conf Prms n2 ps2)) -> 
        (n1 = n2) /\ (ps1 = ps2).


Definition UniqueQFStep
                         (fenv: funEnv) 
                         (n n1 n2: W) (q q1 q2: QFun) :=
    QFStep fenv (Conf QFun n q) ((Conf QFun n1 q1)) ->
    QFStep fenv (Conf QFun n q) ((Conf QFun n2 q2)) -> 
        (n1 = n2) /\ (q1 = q2).


Definition UniqueQVStep 
                         (env: valEnv)
                         (n n1 n2: W) (q q1 q2: QValue) :=
    QVStep env (Conf QValue n q) ((Conf QValue n1 q1)) ->
    QVStep env (Conf QValue n q) ((Conf QValue n2 q2)) -> 
        (n1 = n2) /\ (q1 = q2).



(*******************************************************)

Definition DPar_E :=
  fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
      (e: Exp) (t: VTyp) 
      (p: ExpTyping ftenv tenv fenv e t) =>
  FEnvTyping fenv ftenv ->
  forall (env: valEnv),                      
    EnvTyping env tenv ->
  forall (n n1 n2: W) (e1 e2: Exp), 
         UniqueEStep fenv env n n1 n2 e e1 e2.


Definition DPar_P :=
  fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
                (ps: Prms) (pt: PTyp) 
                (p: PrmsTyping ftenv tenv fenv ps pt) => 
  FEnvTyping fenv ftenv ->
  forall (env: valEnv),                      
    EnvTyping env tenv ->
    forall (n n1 n2: W) (ps1 ps2: Prms),  
          UniquePStep fenv env n n1 n2 ps ps1 ps2.


Definition DPar_F := fun (f: Fun) (ft: FTyp) 
   (p: FunTyping f ft) =>
   (forall (fps: valTC) (t: VTyp),
    ft = FT fps t ->      
    forall (i: nat) (fenv': funEnv) 
           (x: Id) (e0 e1: Exp), 
       f = FC fenv' fps e0 e1 x i -> 
       forall (n: W) (env: valEnv), 
       EnvTyping env fps -> 
       match i with 
         | 0 => forall (n1 n2: W) (e01 e02: Exp),
                  UniqueEStep fenv' env n n1 n2 e0 e01 e02
         | S j => forall (n1 n2: W) (e11 e12: Exp),
                  UniqueEStep (updateE fenv' x (FC fenv' fps e0 e1 x j))
                                 env n n1 n2 e1 e11 e12
        end).
   

Definition DPar_Q :=
   fun (ftenv: funTC) (fenv: funEnv)
          (qf: QFun) (ft: FTyp) 
   (p: QFunTyping ftenv fenv qf ft) =>
   FEnvTyping fenv ftenv ->
   forall (n n1 n2: W) (qf qf1 qf2: QFun),                        
   UniqueQFStep fenv n n1 n2 qf qf1 qf2.


Definition ExpTypingDet_rect :=
  ExpTyping_str_rect DPar_F DPar_Q DPar_E DPar_P.


(************************************************************************)

Definition UniqueVal 
                     (fenv: funEnv) (env: valEnv)
                     (n n1: W) (e: Exp) (v1: Value) :=
  forall (n2: W) (v2: Value),
     EClosure fenv env (Conf Exp n e) ((Conf Exp n2 (Val v2))) -> 
        (n2 = n1) /\ (v2 = v1).


Definition UniquePVal 
                      (fenv: funEnv) (env: valEnv)
                      (n n1: W) (ps: Prms) (vs1: list Exp) :=
  forall (n2: W) (vs2: list Exp),
    isValueList vs1 ->
    isValueList vs2 ->
    PrmsClosure fenv env (Conf Prms n ps)
                              ((Conf Prms n2 (PS vs2))) -> 
        (n2 = n1) /\ (vs2 = vs1).


Lemma QVDeterminism :
  forall (env: valEnv) (n n1 n2: W) (q q1 q2: QValue), 
    QVStep env (Conf QValue n q) ((Conf QValue n1 q1)) ->
    QVStep env (Conf QValue n q) ((Conf QValue n2 q2)) -> 
        (n1 = n2) /\ (q1 = q2).
Proof.
  intros.
  inversion X0; subst.
  inversion X; subst.
  inversion X1; subst.
  inversion X2; subst.
  rewrite H in H0.
  inversion H0; subst.
  auto.
Defined.  


Lemma QFDeterminism :
  forall (fenv: funEnv) (n n1 n2: W) (qf qf1 qf2: QFun), 
         UniqueQFStep fenv n n1 n2 qf qf1 qf2.
Proof.
  intros.
  unfold UniqueQFStep.
  intros.
  inversion X; subst.
  inversion X0; subst.
  inversion X1; subst.
  inversion X2; subst.
  rewrite H in H0.
  inversion H0; subst.
  auto.
Defined.  


Lemma deterAux1 (n1 n2: W) (v1 v2: Value) (e3 e4 e5 e6: Exp) :
  Conf Exp n1 (IfThenElse (Val v1) e3 e4) =
  Conf Exp n2 (IfThenElse (Val v2) e5 e6) ->
  v1 = v2.
  intros.
  inversion H; subst.
  auto.
 Defined.

Lemma deterAux2 (n1 n2: W) (e1 e2 e3 e4 e5 e6: Exp) :
  Conf Exp n1 (IfThenElse e1 e3 e4) =
  Conf Exp n2 (IfThenElse e2 e5 e6) ->
  e1 = e2.
  intros.
  inversion H; subst.
  auto.
 Defined.


Lemma ExpDeterminism :
  forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (e: Exp) (t: VTyp),   
      ExpTyping ftenv tenv fenv e t -> 
      FEnvTyping fenv ftenv ->
  forall (env: valEnv),                      
    EnvTyping env tenv ->
  forall (n n1 n2: W) (e1 e2: Exp), 
         UniqueEStep fenv env n n1 n2 e e1 e2.

Proof.
eapply ExpTypingDet_rect.
- (* SLL *)
  unfold Par_SSL, DPar_E.
  unfold UniqueEStep.
  constructor.
- (* SLL *)
  unfold Par_SSL, DPar_E.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSA *)  
  unfold Par_SSA, DPar_F.
  constructor.
- unfold Par_SSA, DPar_F.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSB *)
  unfold Par_SSB, Par_SSA, DPar_F.
  intros.
  econstructor.
  exact m0.
  exact m1.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
- (* Par_F *)
  unfold DPar_E, DPar_F.
  intros.
  inversion H0; subst.
  inversion H1; subst. 
  intros.
  eauto.
- (* Par_F *)
  unfold DPar_E, DPar_F.
  intros ftenv tenv fenv.
  intros e0 e1 x n t.
  intros K1 K2 K3 HP1 HP2.
  intros fps t0 E3.
  intros i fenv1 x0 e2 e3 E4 n0 env H.
  inversion E3; subst.
  inversion E4; subst.
  eapply HP1.
  eapply updateFEnvLemma.
  assumption.
  assumption.
  assumption.
- (* Par_Q - QF *)
  unfold DPar_F, DPar_Q.
  intros.
  eapply QFDeterminism.
- (* Par_Q - FVar *)  
  unfold DPar_F,  DPar_Q.
  intros.
  eapply QFDeterminism.
- (* modify *)
  unfold DPar_E.
  unfold UniqueEStep.
  intros ftenv tenv fenv T1 T2 VT1 VT2 XF q K H0 env H0'.
  intros n n1 n2 e1 e2.
  intros.  
  inversion X; subst.
  assert (VT4 = VT1).
  eapply loc_pi.
  subst.
  assert (VT5 = VT2).
  eapply loc_pi.
  subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.
  clear XF2.
  inversion X0; subst.
  eapply inj_pair2 in H8; subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.
  auto.
  inversion X1; subst.
  assert (VT4 = VT1).
  eapply loc_pi.
  subst.
  assert (VT5 = VT2).
  eapply loc_pi.
  subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.  
  clear XF2.
  inversion X0; subst.
  clear XF2.
  clear VT4.
  clear VT5.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.  
  inversion X1; subst.  
  assert (VT4 = VT1).
  eapply loc_pi.
  subst.
  assert (VT5 = VT2).
  eapply loc_pi.
  subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.  
  inversion X1; subst.
  inversion X2; subst.
  inversion X3; subst.  
  inversion X4; subst.
  rewrite H in H1.
  inversion H1; subst.
  auto.
  (* return *)
- unfold DPar_E.
  unfold UniqueEStep.
  intros G ftenv tenv fenv q t k1.
  intros H0 env H0'.
  intros n n1 n2 e1 e2.
  intros X X0.
  inversion X; subst.
  inversion X0; subst.
  auto.
  inversion X1; subst.
  inversion X1; subst.
  inversion X0; subst.
  inversion X3; subst.
  inversion X2; subst.
  inversion X4; subst.
  rewrite H in H1.
  inversion H1; subst.
  auto.
(* bindN *)
- unfold DPar_E.
  unfold UniqueEStep.
  intros ftenv tenv fenv e1 e2 t1 t2 K1 K2 HP1 HP2 H0 env H0'.
  intros n n1 n2 e0 e3.
  intros.
  inversion X; subst.
  + inversion X0; subst.
    * auto.
    * inversion X1. 
  + inversion X0; subst.
    * inversion X1. 
    * rename e1'0 into e2'.
      assert (n1 = n2 /\ e1' = e2'). 
      eapply HP1.
      assumption.
      eassumption.
      eassumption.
      assumption.
      destruct H.
      rewrite H1.
      auto.
(* bindS *)        
- unfold DPar_E.
  unfold UniqueEStep.
  intros ftenv tenv fenv x e1 e2 t1 t2.
  intros K1 K2 HP1 HP2 H0 env H0'.
  intros n n1 n2 e0 e3.
  intros.
  inversion X; subst.
    + inversion X0; subst.
      * auto.
      * inversion X1.
    + inversion X0; subst.
      * inversion X1.
      * rename e1'0 into e2'.
        assert (n1 = n2 /\ e1' = e2'). 
        eapply HP1.
        assumption.
        eassumption.
        eassumption.
        assumption.
        destruct H.
        rewrite H1.
        auto.
(* bindMS *)        
  - unfold DPar_E.
    unfold UniqueEStep.
    intros ftenv ftenvP ftenv' tenv tenvP tenv' fenv fenvP fenv' envP.
    intros e t.
    intros K1 K2 K3 K4 K5 K6 K7 HP.
    intros H0 env H0'.
    intros n n1 n2 e1 e2.
    intros.
    inversion X; subst.
    + inversion X0; subst.
      * auto.
      * inversion X1.
    + inversion X0; subst.
      inversion X1.
      rename e'0 into e''.
      assert (n1 = n2 /\ e' = e'').
      eapply HP.
      eapply overrideEnvLemmaT.
      assumption.
      assumption.
      eapply overrideEnvLemmaT.
      eassumption.
      eassumption.
      eassumption.
      assumption.
      destruct H.
      rewrite H1.
      auto.
(* apply *)        
  - unfold DPar_P, DPar_Q, DPar_E.
    unfold UniqueEStep.
    unfold UniqueQFStep.
    unfold UniquePStep.
    intros ftenv tenv fps fenv.
    intros q ps pt t.
    intros K1 K2 K3 K4 HP1 HP2.
    intros H0 env H0'.
    intros n n1 n2 e1 e2.
    intros.
    inversion X; subst.
    + inversion X0; subst.
      * inversion H6; subst.
        inversion H5; subst.
        eapply vlaMapEq in H.  
        rewrite H.
        auto.
      * destruct ps'.
        eapply NoPrmsStep in X1.
        intuition X1.
        apply isValueList2IsValueT in H6.
        assumption.
      * inversion X1.
    + inversion X0; subst.
      * inversion H6; subst.
        inversion H5; subst.
        eapply vlaMapEq in H.  
        rewrite H.
        auto.
      * destruct ps'.
        eapply NoPrmsStep in X1.
        intuition X1.
        apply isValueList2IsValueT in H6.
        assumption.
      * inversion X1.
    + inversion X0; subst.
      * destruct ps'.
        eapply NoPrmsStep in X1.
        intuition X1.
        apply isValueList2IsValueT in H6.
        assumption.
      * destruct ps'.
        eapply NoPrmsStep in X1.
        intuition X1.
        apply isValueList2IsValueT in H6.
        assumption.
      * rename ps'0 into ps''.
        assert (n1 = n2 /\ ps' = ps'').
        eapply HP2.
        assumption.
        eassumption.
        eassumption.
        assumption.
        destruct H.
        rewrite H1.
        auto.
      * inversion X2.
    + inversion X0; subst.
      * inversion X1.
      * inversion X1.
      * inversion X1.
      * rename qf'0 into qf''.
        assert (n1 = n2 /\ qf' = qf'').
        eapply HP1.
        assumption.
        eassumption.
        assumption.
        destruct H.
        rewrite H1.
        auto.
(* val *)
  - unfold DPar_E.
    unfold UniqueEStep.
    intros ftenv tenv fenv.
    intros v t.
    intros K H0 env H0'.
    intros n n1 n2 e1 e2.
    intros.
    inversion X.
  - (* ifthenelse *)
    unfold DPar_E.
    intros.
    unfold UniqueEStep.
    intros.
    inversion X1; subst.
    inversion X2; subst.
    auto.
    eapply deterAux1 in H4.
    unfold cst in H4.
    eapply inj_pair2 in H4.
    inversion H4.
    inversion X2; subst.
    rewrite <- H9.
    rewrite <- H9.
    auto.
    inversion X3.
    inversion X4.
    inversion X2; subst.
    eapply deterAux1 in H4.
    unfold cst in H4.
    eapply inj_pair2 in H4.
    inversion H4.
    auto.
    inversion X3.
    inversion X2; subst.
    inversion X3.
    inversion X1; subst.
    inversion X3.
    rewrite H9 at 2.
    auto.
    inversion X4.
    unfold UniqueEStep in H.
    rename e'0 into e''. 
    assert (n1 = n2 /\ e' = e'').
    eapply H.
    assumption.
    eassumption.
    eassumption.
    assumption.
    destruct H2.
    rewrite H2.
    rewrite H3.
    auto.
  - (* SLL *)
    unfold Par_SSL, DPar_P, DPar_E.
    unfold UniquePStep, UniqueEStep.
    intros ftenv tenv fenv.
    intros es ts K HP H0 env H0'.
    intros n n1 n2 ps1 ps2.
    intros.
    revert K.
    dependent induction HP.
    inversion X0.
    intro K.
    inversion X0; subst.
    inversion X; subst. 
    rename es'0 into es''.
    assert (n1 = n2 /\ PS es'' = PS es').
    eapply IHHP.
    assumption.
    eassumption.
    eassumption.
    assumption.
    inversion K; subst.
    assumption.
    destruct H.
    inversion H1; subst.
    auto.
    (**)
    inversion X2.
    (**)
    inversion X; subst.
    inversion X1.
    rename e'0 into e''.    
    assert (n1 = n2 /\ e'' = e').
    eapply p0.
    assumption.
    eassumption.
    eassumption.
    assumption.
    destruct H.
    rewrite H1.
    auto.
Defined.

(*********************************************************************)

Definition PrmsTypingDet_rect :=
  PrmsTyping_str_rect DPar_F DPar_Q DPar_E DPar_P.


Lemma PrmsDeterminism :
  forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (ps: Prms) (pt: PTyp),   
      PrmsTyping ftenv tenv fenv ps pt -> 
      FEnvTyping fenv ftenv ->
  forall (env: valEnv),                      
    EnvTyping env tenv ->
  forall (n n1 n2: W) (ps1 ps2: Prms), 
         UniquePStep fenv env n n1 n2 ps ps1 ps2.

Proof.
eapply PrmsTypingDet_rect.
- (* SLL *)
  unfold Par_SSL, DPar_E.
  unfold UniqueEStep.
  constructor.
- (* SLL *)
  unfold Par_SSL, DPar_E.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSA *)  
  unfold Par_SSA, DPar_F.
  constructor.
- unfold Par_SSA, DPar_F.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSB *)
  unfold Par_SSB, Par_SSA, DPar_F.
  intros.
  econstructor.
  exact m0.
  exact m1.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
- (* Par_F *)
  unfold DPar_E, DPar_F.
  intros.
  inversion H0; subst.
  inversion H1; subst. 
  intros.
  eauto.
- (* Par_F *)
  unfold DPar_E, DPar_F.
  intros ftenv tenv fenv.
  intros e0 e1 x n t.
  intros K1 K2 K3 HP1 HP2.
  intros fps t0 E3.
  intros i fenv1 x0 e2 e3 E4 n0 env H.
  inversion E3; subst.
  inversion E4; subst.
  eapply HP1.
  eapply updateFEnvLemma.
  assumption.
  assumption.
  assumption.
- (* Par_Q - QF *)
  unfold DPar_F, DPar_Q.
  intros.
  eapply QFDeterminism.
- (* Par_Q - FVar *)  
  unfold DPar_F,  DPar_Q.
  intros.
  eapply QFDeterminism.
- (* modify *)
  unfold DPar_E.
  unfold UniqueEStep.
  intros ftenv tenv fenv T1 T2 VT1 VT2 XF q K H0 env H0'.
  intros n n1 n2 e1 e2.
  intros.  
  inversion X; subst.
  assert (VT4 = VT1).
  eapply loc_pi.
  subst.
  assert (VT5 = VT2).
  eapply loc_pi.
  subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.
  clear XF2.
  inversion X0; subst.
  eapply inj_pair2 in H8; subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.
  auto.
  inversion X1; subst.
  assert (VT4 = VT1).
  eapply loc_pi.
  subst.
  assert (VT5 = VT2).
  eapply loc_pi.
  subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.  
  clear XF2.
  inversion X0; subst.
  clear XF2.
  clear VT4.
  clear VT5.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.  
  inversion X1; subst.  
  assert (VT4 = VT1).
  eapply loc_pi.
  subst.
  assert (VT5 = VT2).
  eapply loc_pi.
  subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.  
  inversion X1; subst.
  inversion X2; subst.
  inversion X3; subst.  
  inversion X4; subst.
  rewrite H in H1.
  inversion H1; subst.
  auto.
  (* return *)
- unfold DPar_E.
  unfold UniqueEStep.
  intros G ftenv tenv fenv q t k1.
  intros H0 env H0'.
  intros n n1 n2 e1 e2.
  intros X X0.
  inversion X; subst.
  inversion X0; subst.
  auto.
  inversion X1; subst.
  inversion X1; subst.
  inversion X0; subst.
  inversion X3; subst.
  inversion X2; subst.
  inversion X4; subst.
  rewrite H in H1.
  inversion H1; subst.
  auto.
(* bindN *)
- unfold DPar_E.
  unfold UniqueEStep.
  intros ftenv tenv fenv e1 e2 t1 t2 K1 K2 HP1 HP2 H0 env H0'.
  intros n n1 n2 e0 e3.
  intros.
  inversion X; subst.
  + inversion X0; subst.
    * auto.
    * inversion X1. 
  + inversion X0; subst.
    * inversion X1. 
    * rename e1'0 into e2'.
      assert (n1 = n2 /\ e1' = e2'). 
      eapply HP1.
      assumption.
      eassumption.
      eassumption.
      assumption.
      destruct H.
      rewrite H1.
      auto.
(* bindS *)        
- unfold DPar_E.
  unfold UniqueEStep.
  intros ftenv tenv fenv x e1 e2 t1 t2.
  intros K1 K2 HP1 HP2 H0 env H0'.
  intros n n1 n2 e0 e3.
  intros.
  inversion X; subst.
    + inversion X0; subst.
      * auto.
      * inversion X1.
    + inversion X0; subst.
      * inversion X1.
      * rename e1'0 into e2'.
        assert (n1 = n2 /\ e1' = e2'). 
        eapply HP1.
        assumption.
        eassumption.
        eassumption.
        assumption.
        destruct H.
        rewrite H1.
        auto.
(* bindMS *)        
  - unfold DPar_E.
    unfold UniqueEStep.
    intros ftenv ftenvP ftenv' tenv tenvP tenv' fenv fenvP fenv' envP.
    intros e t.
    intros K1 K2 K3 K4 K5 K6 K7 HP.
    intros H0 env H0'.
    intros n n1 n2 e1 e2.
    intros.
    inversion X; subst.
    + inversion X0; subst.
      * auto.
      * inversion X1.
    + inversion X0; subst.
      inversion X1.
      rename e'0 into e''.
      assert (n1 = n2 /\ e' = e'').
      eapply HP.
      eapply overrideEnvLemmaT.
      assumption.
      assumption.
      eapply overrideEnvLemmaT.
      eassumption.
      eassumption.
      eassumption.
      assumption.
      destruct H.
      rewrite H1.
      auto.
(* apply *)        
  - unfold DPar_P, DPar_Q, DPar_E.
    unfold UniqueEStep.
    unfold UniqueQFStep.
    unfold UniquePStep.
    intros ftenv tenv fps fenv.
    intros q ps pt t.
    intros K1 K2 K3 K4 HP1 HP2.
    intros H0 env H0'.
    intros n n1 n2 e1 e2.
    intros.
    inversion X; subst.
    + inversion X0; subst.
      * inversion H6; subst.
        inversion H5; subst.
        eapply vlaMapEq in H.  
        rewrite H.
        auto.
      * destruct ps'.
        eapply NoPrmsStep in X1.
        intuition X1.
        apply isValueList2IsValueT in H6.
        assumption.
      * inversion X1.
    + inversion X0; subst.
      * inversion H6; subst.
        inversion H5; subst.
        eapply vlaMapEq in H.  
        rewrite H.
        auto.
      * destruct ps'.
        eapply NoPrmsStep in X1.
        intuition X1.
        apply isValueList2IsValueT in H6.
        assumption.
      * inversion X1.
    + inversion X0; subst.
      * destruct ps'.
        eapply NoPrmsStep in X1.
        intuition X1.
        apply isValueList2IsValueT in H6.
        assumption.
      * destruct ps'.
        eapply NoPrmsStep in X1.
        intuition X1.
        apply isValueList2IsValueT in H6.
        assumption.
      * rename ps'0 into ps''.
        assert (n1 = n2 /\ ps' = ps'').
        eapply HP2.
        assumption.
        eassumption.
        eassumption.
        assumption.
        destruct H.
        rewrite H1.
        auto.
      * inversion X2.
    + inversion X0; subst.
      * inversion X1.
      * inversion X1.
      * inversion X1.
      * rename qf'0 into qf''.
        assert (n1 = n2 /\ qf' = qf'').
        eapply HP1.
        assumption.
        eassumption.
        assumption.
        destruct H.
        rewrite H1.
        auto.
(* val *)
  - unfold DPar_E.
    unfold UniqueEStep.
    intros ftenv tenv fenv.
    intros v t.
    intros K H0 env H0'.
    intros n n1 n2 e1 e2.
    intros.
    inversion X.
  - (* ifthenelse *)
    unfold DPar_E.
    intros.
    unfold UniqueEStep.
    intros.
    inversion X1; subst.
    inversion X2; subst.
    auto.
    eapply deterAux1 in H4.
    unfold cst in H4.
    eapply inj_pair2 in H4.
    inversion H4.
    inversion X2; subst.
    rewrite <- H9.
    rewrite <- H9.
    auto.
    inversion X3.
    inversion X4.
    inversion X2; subst.
    eapply deterAux1 in H4.
    unfold cst in H4.
    eapply inj_pair2 in H4.
    inversion H4.
    auto.
    inversion X3.
    inversion X2; subst.
    inversion X3.
    inversion X1; subst.
    inversion X3.
    rewrite H9 at 2.
    auto.
    inversion X4.
    unfold UniqueEStep in H.
    rename e'0 into e''. 
    assert (n1 = n2 /\ e' = e'').
    eapply H.
    assumption.
    eassumption.
    eassumption.
    assumption.
    destruct H2.
    rewrite H2.
    rewrite H3.
    auto.
  - (* SLL *)
    unfold Par_SSL, DPar_P, DPar_E.
    unfold UniquePStep, UniqueEStep.
    intros ftenv tenv fenv.
    intros es ts K HP H0 env H0'.
    intros n n1 n2 ps1 ps2.
    intros.
    revert K.
    dependent induction HP.
    inversion X0.
    intro K.
    inversion X0; subst.
    inversion X; subst. 
    rename es'0 into es''.
    assert (n1 = n2 /\ PS es'' = PS es').
    eapply IHHP.
    assumption.
    eassumption.
    eassumption.
    assumption.
    inversion K; subst.
    assumption.
    destruct H.
    inversion H1; subst.
    auto.
    (**)
    inversion X2.
    (**)
    inversion X; subst.
    inversion X1.
    rename e'0 into e''.    
    assert (n1 = n2 /\ e'' = e').
    eapply p0.
    assumption.
    eassumption.
    eassumption.
    assumption.
    destruct H.
    rewrite H1.
    auto.
Defined.


(************************************************************************)

(** Confluence of evaluation *)

Definition UniEStep 
                     (fenv: funEnv) (env: valEnv)
                     (p p1 p2 : AConfig Exp) :=
    EStep fenv env p p1 ->
    EStep fenv env p p2 -> 
        p1 = p2.


Lemma ExpDeterminismA :
  forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (e: Exp) (t: VTyp),   
      ExpTyping ftenv tenv fenv e t -> 
      FEnvTyping fenv ftenv ->
  forall (env: valEnv),                      
    EnvTyping env tenv ->
  forall (n: W) (p1 p2 : AConfig Exp), 
         UniEStep fenv env (Conf Exp n e) p1 p2.
intros.
unfold UniEStep.  
destruct p1.
destruct p2.
intros.
assert (state = state0 /\ qq = qq0). 
eapply ExpDeterminism.
exact X.
exact X0.
exact X1.
exact X2.
exact X3.
destruct H.
subst.
auto.
Defined.



Definition UniqueEClos (fenv: funEnv) (env: valEnv)
                        (n n1 n2: W) (e : Exp) (v1 v2: Value) :=
    EClosure fenv env (Conf Exp n e) ((Conf Exp n1 (Val v1))) ->
    EClosure fenv env (Conf Exp n e) ((Conf Exp n2 (Val v2))) -> 
        (n1 = n2) /\ (v1 = v2).


Lemma ExpConfluence :
  forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (e: Exp) (t: VTyp),   
      ExpTyping ftenv tenv fenv e t -> 
      FEnvTyping fenv ftenv ->
  forall (env: valEnv),                      
    EnvTyping env tenv ->
  forall (n n1 n2: W) (v1 v2: Value), 
         UniqueEClos fenv env n n1 n2 e v1 v2.

Proof.
  unfold UniqueEClos.
  intros.
  revert X3.  
  dependent induction X2.
  intros.
  inversion X3; subst.
  auto.
  dependent destruction X4.
  inversion X2.
  inversion X2.
  intros.
  dependent destruction X3.
  inversion e0.

  assert (p0 = p2).
  destruct p0.
  destruct p2.
  eapply ExpDeterminismA.
  exact X.
  assumption.
  exact X1.
  eassumption.
  assumption.
  rewrite H in *; clear H.

  (* need subject reduction *)
  destruct p2.

  assert (ExpTyping ftenv tenv fenv qq t).
  eapply ExpSubjectRed.
  exact X.
  exact X0.
  exact X1.
  exact e1.
   
  eapply IHX2.
  exact X4.
  exact X0.
  exact X1.
  reflexivity.  
  reflexivity.
  exact X3.
Defined.


Definition UniPStep 
                     (fenv: funEnv) (env: valEnv)
                     (p p1 p2 : AConfig Prms) :=
    PrmsStep fenv env p p1 ->
    PrmsStep fenv env p p2 -> 
        p1 = p2.


Lemma PrmsDeterminismA :
  forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (ps: Prms) (pt: PTyp),   
      PrmsTyping ftenv tenv fenv ps pt -> 
      FEnvTyping fenv ftenv ->
  forall (env: valEnv),                      
    EnvTyping env tenv ->
  forall (n: W) (p1 p2 : AConfig Prms), 
         UniPStep fenv env (Conf Prms n ps) p1 p2.
intros.
unfold UniPStep.  
destruct p1.
destruct p2.
intros.
assert (state = state0 /\ qq = qq0). 
eapply PrmsDeterminism.
exact X.
exact X0.
exact X1.
exact X2.
exact X3.
destruct H.
subst.
auto.
Defined.


Definition UniquePClos (fenv: funEnv) (env: valEnv)
                        (n n1 n2: W) (ps : Prms) (vs1 vs2: list Value) :=
  PrmsClosure fenv env (Conf Prms n ps) ((Conf Prms n1 (PS (map Val vs1)))) ->
  PrmsClosure fenv env (Conf Prms n ps) ((Conf Prms n2 (PS (map Val vs2)))) -> 
        (n1 = n2) /\ (vs1 = vs2).


Lemma PrmsConfluence :
  forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (ps: Prms) (pt: PTyp),   
      PrmsTyping ftenv tenv fenv ps pt -> 
      FEnvTyping fenv ftenv ->
  forall (env: valEnv),                      
    EnvTyping env tenv ->
  forall (n n1 n2: W) (vs1 vs2: list Value), 
         UniquePClos fenv env n n1 n2 ps vs1 vs2.

Proof.
  unfold UniquePClos.
  intros.
  revert X3.  
  dependent induction X2.
  intros.
  inversion X3; subst.
  eapply mapEq in H4.
  auto.
  dependent destruction X4.
  eapply NoPrmsStep in X2.
  intuition X2.
  eapply isValueListT_triv.

  destruct p1.
  destruct qq.
  eapply NoPrmsStep in X2.
  intuition X2.
  eapply isValueListT_triv.
  
  intros.
  dependent destruction X3.
  destruct p2.
  destruct qq.
  eapply NoPrmsStep in p.
  intuition p.
  eapply isValueListT_triv.
  
  assert (p0 = p2).
  destruct p0.
  destruct p2.
  eapply PrmsDeterminismA.
  exact X.
  assumption.
  exact X1.
  eassumption.
  assumption.
  rewrite H in *; clear H.

  (* need subject reduction *)
  destruct p2.

  assert (PrmsTyping ftenv tenv fenv qq pt).
  eapply PrmsSubjectRed.
  exact X.
  exact X0.
  exact X1.
  exact p4.
   
  eapply IHX2.
  exact X4.
  exact X0.
  exact X1.
  reflexivity.  
  reflexivity.
  exact X3.
Defined.


(************************************************************************)

(** extractors from the TS proof *)

Definition extractRunValue (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
   (e: Exp) (t: VTyp)
   (k: ExpTyping ftenv tenv fenv e t)
   (m1: MatchEnvsT FunTyping fenv ftenv)
   (env: valEnv)                      
   (m2: MatchEnvsT ValueTyping env tenv)
   (s: W) : Value := projT1 (sigT_of_sigT2
                           (ExpEval ftenv tenv fenv e t k m1 env m2 s)). 

Definition extractRunState (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
   (e: Exp) (t: VTyp)
   (k: ExpTyping ftenv tenv fenv e t)
   (m1: MatchEnvsT FunTyping fenv ftenv)
   (env: valEnv)                      
   (m2: MatchEnvsT ValueTyping env tenv)
   (s: W) : W := projT1 (projT3 (ExpEval ftenv tenv fenv e t k m1 env m2 s)). 

Definition extractRunTyping (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
   (e: Exp) (t: VTyp)
   (k: ExpTyping ftenv tenv fenv e t)
   (m1: MatchEnvsT FunTyping fenv ftenv)
   (env: valEnv)                      
   (m2: MatchEnvsT ValueTyping env tenv)
   (s: W) : ValueTyping
              (extractRunValue ftenv tenv fenv e t k m1 env m2 s) t :=
         projT2 (sigT_of_sigT2
                       (ExpEval ftenv tenv fenv e t k m1 env m2 s)). 


Definition extractPRunValue (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
   (ps: Prms) (pt: PTyp)
   (k: PrmsTyping ftenv tenv fenv ps pt)
   (m1: MatchEnvsT FunTyping fenv ftenv)
   (env: valEnv)                      
   (m2: MatchEnvsT ValueTyping env tenv)
   (s: W) : list Value := projT1 (sigT_of_sigT2
                    (projT2 (PrmsEval ftenv tenv fenv ps pt k m1 env m2 s))). 


Definition extractPRunEValue (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
   (ps: Prms) (pt: PTyp)
   (k: PrmsTyping ftenv tenv fenv ps pt)
   (m1: MatchEnvsT FunTyping fenv ftenv)
   (env: valEnv)                      
   (m2: MatchEnvsT ValueTyping env tenv)
   (s: W) : list Exp :=
                    (projT1 (PrmsEval ftenv tenv fenv ps pt k m1 env m2 s)). 

Definition extractPRunState (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
   (ps: Prms) (pt: PTyp)
   (k: PrmsTyping ftenv tenv fenv ps pt)
   (m1: MatchEnvsT FunTyping fenv ftenv)
   (env: valEnv)                      
   (m2: MatchEnvsT ValueTyping env tenv)
   (s: W) : W := projT1 (snd (projT3 (projT2
                        (PrmsEval ftenv tenv fenv ps pt k m1 env m2 s)))). 


Definition extractPRunTyping (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
   (ps: Prms) (pt: PTyp)
   (k: PrmsTyping ftenv tenv fenv ps pt)
   (m1: MatchEnvsT FunTyping fenv ftenv)
   (env: valEnv)                      
   (m2: MatchEnvsT ValueTyping env tenv)
   (s: W) : PrmsTyping  emptyE emptyE emptyE 
    (PS (projT1 (PrmsEval ftenv tenv fenv ps pt k m1 env m2 s))) pt :=
         fst (projT3  
                 (projT2 (PrmsEval ftenv tenv fenv ps pt k m1 env m2 s))). 


(*************************************************************************)

Lemma extractPRunCons  (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
   (ps: Prms) (pt: PTyp)
   (k: PrmsTyping ftenv tenv fenv ps pt)
   (m1: MatchEnvsT FunTyping fenv ftenv)
   (env: valEnv)                      
   (m2: MatchEnvsT ValueTyping env tenv)
   (s: W) :
  extractPRunEValue ftenv tenv fenv ps pt k m1 env m2 s =
  map Val (extractPRunValue ftenv tenv fenv ps pt k m1 env m2 s).
  generalize (projT2 (sigT_of_sigT2 
                (projT2 (PrmsEval ftenv tenv fenv ps pt k m1 env m2 s)))).
  intros.
  inversion H; subst.
  unfold extractPRunEValue, extractPRunValue.
  auto.
Defined.  


(***********************************************************************)

Lemma EvalIntro 
   (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
   (e: Exp) (t: VTyp)
   (k: ExpTyping ftenv tenv fenv e t)
   (m1: MatchEnvsT FunTyping fenv ftenv)
   (env: valEnv)                      
   (m2: MatchEnvsT ValueTyping env tenv)
   (s: W) :
  EClosure fenv env (Conf Exp s e)
           (Conf Exp (extractRunState ftenv tenv fenv e t k m1 env m2 s)
                     (Val (extractRunValue ftenv tenv fenv e t k m1 env m2 s))).
  unfold extractRunState.
  unfold extractRunValue.
  simpl. 
  destruct (ExpEval ftenv tenv fenv e t k m1 env m2 s).
  destruct s0.
  simpl.
  auto.
Defined.
  

Lemma EvalElim 
   (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
   (e: Exp) (t: VTyp)
   (k: ExpTyping ftenv tenv fenv e t)
   (m1: MatchEnvsT FunTyping fenv ftenv)
   (env: valEnv)                      
   (m2: MatchEnvsT ValueTyping env tenv)
   (s: W) :
  forall (s': W) (v: Value), 
    EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v)) ->
    (s' = extractRunState ftenv tenv fenv e t k m1 env m2 s) /\
    (v = extractRunValue ftenv tenv fenv e t k m1 env m2 s).
  intros.
  unfold extractRunState.
  unfold extractRunValue.
  eapply  ExpConfluence.
  exact k.
  exact m1.
  exact m2.
  exact X.
  eapply EvalIntro.
Defined.
  

Lemma PEvalIntro 
   (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
   (ps: Prms) (pt: PTyp)
   (k: PrmsTyping ftenv tenv fenv ps pt)
   (m1: MatchEnvsT FunTyping fenv ftenv)
   (env: valEnv)                      
   (m2: MatchEnvsT ValueTyping env tenv)
   (s: W) :
  PrmsClosure fenv env (Conf Prms s ps)
     (Conf Prms (extractPRunState ftenv tenv fenv ps pt k m1 env m2 s)
        (PS (map Val (extractPRunValue ftenv tenv fenv ps pt k m1 env m2 s)))).
  unfold extractPRunState.
  unfold extractPRunValue.
  simpl. 
  destruct (PrmsEval ftenv tenv fenv ps pt k m1 env m2 s).
  destruct s0.
  simpl.
  destruct p.
  inversion i; subst.
  simpl in *.  
  destruct s0.
  auto.
Defined.
  

Lemma PEvalElim 
   (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
   (ps: Prms) (pt: PTyp)
   (k: PrmsTyping ftenv tenv fenv ps pt)
   (m1: MatchEnvsT FunTyping fenv ftenv)
   (env: valEnv)                      
   (m2: MatchEnvsT ValueTyping env tenv)
   (s: W) :
  forall (s': W) (vs: list Value), 
    PrmsClosure fenv env (Conf Prms s ps) (Conf Prms s' (PS (map Val vs))) ->
    (s' = extractPRunState ftenv tenv fenv ps pt k m1 env m2 s) /\
    (vs = extractPRunValue ftenv tenv fenv ps pt k m1 env m2 s).
  intros.
  unfold extractPRunState.
  unfold extractPRunValue.
  eapply  PrmsConfluence.
  exact k.
  exact m1.
  exact m2.
  exact X.
  eapply PEvalIntro.
Defined.
  
(***********************************************************************)

Lemma prmsTyping_aux4 (ftenv: funTC) (tenv: valTC)
        (fenv: funEnv) (env: valEnv) (es: list Exp) (vs: list Value)
        (ts: list VTyp) (s0 s1: W) :
    MatchEnvsT FunTyping fenv ftenv ->
    MatchEnvsT ValueTyping env tenv ->
    PrmsTyping ftenv tenv fenv (PS es) (PT ts) -> 
    PrmsClosure fenv env (Conf Prms s0 (PS es))
        (Conf Prms s1 (PS (map Val vs))) -> 
    vlsTyping vs ts.
  intros.
  assert (vs = extractPRunValue ftenv tenv fenv (PS es) (PT ts)
                                X1 X env X0 s0).
  eapply (proj2 (PEvalElim ftenv tenv fenv (PS es) (PT ts)
                                X1 X env X0 s0 s1 vs _)).
  rewrite H.
  assert (PrmsTyping emptyE emptyE emptyE
    (PS
       (projT1
          (PrmsEval ftenv tenv fenv (PS es) (PT ts) X1 X env X0 s0)))
    (PT ts)).
  exact (extractPRunTyping ftenv tenv fenv (PS es) (PT ts)
                                X1 X env X0 s0).
  assert (PrmsTyping ftenv tenv fenv
    (PS
       (projT1
          (PrmsEval ftenv tenv fenv (PS es) (PT ts) X1 X env X0 s0)))
    (PT ts)).
  eapply weakenPrmsTyping in X3. 
  exact X3.
  constructor.
  auto.
  clear X3.
  simpl in *.
  generalize (extractPRunCons ftenv tenv fenv (PS es)
                              (PT ts) X1 X env X0 s0).
  intros.
  unfold extractPRunEValue in H0.
  rewrite H0 in X4.
  eapply matchListsAux02_T.
  instantiate (1:= map Val vs).
  rewrite <- H.
  constructor.
  auto.
  rewrite <- H in X4.
  exact X4.
  Unshelve.
  auto.
Defined.  


(************************************************************************)


Lemma ValueStrongTyping :
  forall (v: Value) (t1: VTyp),   
     ValueTyping v t1 -> 
  forall t2: VTyp,  
    ValueTyping v t2 -> 
        t1 = t2.
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst.
  subst T T0.
  rewrite H1 in H3.
  assert (H2 = H4).
  eapply loc_pi.
  subst.
  destruct t1.
  destruct t2.
  simpl in *.
  revert H1.
  revert H0.
  revert v1.
  rewrite <- H3.
  intros.
  assert (v0 = v1).
  eapply loc_pi.
  subst.
  auto.
Defined.  
  
Lemma IdStrongTyping :
  forall (tenv: valTC) (x: Id) (t1: VTyp),   
     IdTyping tenv x t1 -> 
  forall t2: VTyp,  
    IdTyping tenv x t2 -> 
        t1 = t2.
Proof.
  intros.
  inversion X; subst.
  inversion X0; subst.
  inversion X1; subst.
  inversion X2; subst.
  rewrite H in H0.
  injection H0.
  auto.
Defined.  


Lemma EnvStrongTyping :
  forall (env: valEnv) (tenv1: valTC),   
     EnvTyping env tenv1 -> 
  forall tenv2: valTC,  
    EnvTyping env tenv2 -> 
        tenv1 = tenv2.
Proof.
  intros.
  dependent induction env.
  inversion X; subst.
  inversion X0; subst.
  auto.
  inversion X; subst.
  inversion X0; subst.
  assert (ls2 = ls0).
  eapply IHenv.
  auto.
  auto.
  assert (v2 = v3).
  eapply ValueStrongTyping.
  eauto.
  auto.
  rewrite H.
  rewrite H0.
  auto.
Defined.  
  
(*
Lemma ListStrongTyping (ftenv: funTC) (tenv: valTC) (fenv: funEnv) :
  forall (ls: list Exp) (ts1: list VTyp),   
      Forall2T (ExpTyping ftenv tenv fenv) ls ts1 -> 
  forall ts2: list VTyp,  
      Forall2T (ExpTyping ftenv tenv fenv) ls ts2 -> 
        ts1 = ts2.
Proof.
*)


Definition UniEType :=
  fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
      (e: Exp) (t1: VTyp) (k: ExpTyping ftenv tenv fenv e t1) => 
  FEnvTyping fenv ftenv ->     
  forall (t2: VTyp) (ftenv0: funTC),
    FEnvTyping fenv ftenv0 ->       
    ExpTyping ftenv0 tenv fenv e t2 -> 
        t1 = t2.


Definition UniPType :=
  fun (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
      (ps: Prms) (pt1: PTyp) (k: PrmsTyping ftenv tenv fenv ps pt1) => 
    FEnvTyping fenv ftenv ->
    forall (pt2: PTyp) (ftenv0: funTC),
      FEnvTyping fenv ftenv0 ->  
      PrmsTyping ftenv0 tenv fenv ps pt2 -> 
        pt1 = pt2.


Definition UniQFType :=
  fun (ftenv: funTC) (fenv: funEnv) 
      (qf: QFun) (ft1: FTyp) (k: QFunTyping ftenv fenv qf ft1) => 
    FEnvTyping fenv ftenv ->     
    forall (ft2: FTyp) (ftenv0: funTC),
    FEnvTyping fenv ftenv0 ->  
      QFunTyping ftenv0 fenv qf ft2 -> 
        ft1 = ft2.


Definition UniETypeW (ftenv: funTC)
                      (tenv: valTC) (fenv: funEnv)
                      (e: Exp) (t1: VTyp) := 
  ExpTyping ftenv tenv fenv e t1 ->  
  FEnvTyping fenv ftenv ->     
  forall (t2: VTyp) (ftenv0: funTC),
    FEnvTyping fenv ftenv0 ->       
    ExpTyping ftenv0 tenv fenv e t2 -> 
        t1 = t2.


Definition UniFTypeS :=
  fun (f: Fun) (ft1: FTyp) (k: FunTyping f ft1) => 
    forall (ft2: FTyp),  
      FunTyping f ft2 -> 
        ft1 = ft2.


Definition UniFType :=
  fun (f: Fun) (ft: FTyp) (k: FunTyping f ft) => 
   (forall (fps: valTC) (t: VTyp),
    ft = FT fps t ->      
    forall (ftenv: funTC) (i: nat) (fenv: funEnv) 
           (x: Id) (e0 e1: Exp),
       FEnvTyping fenv ftenv ->      
       f = FC fenv fps e0 e1 x i -> 
       match i with 
       | 0 => UniETypeW ftenv fps fenv e0 t
       | S j => UniETypeW (updateE ftenv x ft) fps
                (updateE fenv x (FC fenv fps e0 e1 x j)) e1 t 
       end).



Definition ExpTypingUni_rect :=
  ExpTyping_str_rect UniFType UniQFType UniEType UniPType.


Lemma ExpStrongTyping :
  forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (e: Exp) (t1: VTyp),   
      ExpTyping ftenv tenv fenv e t1 -> 
      FEnvTyping fenv ftenv ->
  forall (t2: VTyp) (ftenv0: funTC),
    FEnvTyping fenv ftenv0 ->  
    ExpTyping ftenv0 tenv fenv e t2 -> 
        t1 = t2.
Proof.
eapply ExpTypingUni_rect.
- (* SLL *)
  unfold Par_SSL, UniEType.
  intros.
  constructor.
- (* SLL *)
  unfold Par_SSL, UniEType.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSA *)  
  unfold Par_SSA, UniFType.
  constructor.
- unfold Par_SSA, UniFType.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSB *)
  unfold Par_SSB, Par_SSA, UniFType.
  intros.
  econstructor.
  exact m0.
  exact m1.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
- (* Par_F *)
  unfold UniFType, UniETypeW, UniEType.
  intros.
  inversion H0; subst.
  inversion H1; subst. 
  intros.
  eapply H.
  auto.
  Focus 2.
  eauto.
  auto.
- (* Par_F *)
  unfold UniFType, UniETypeW, UniEType.
  intros ftenv tenv fenv.
  intros e0 e1 x n t.
  intros K1 K2 K3 HP1 HP2.
  intros fps t0 E3.
  intros ftenv1 i fenv1 x0 e2 e3 K4 E4.
  inversion E3; subst.
  inversion E4; subst.
  intros.
  eapply HP1.
  eapply updateFEnvLemma.
  assumption.
  assumption.
  eassumption.
  assumption.
- (* Par_Q - QF *)
  unfold UniQFType, UniFType, UniEType, UniETypeW.
  intros.
  inversion X1; subst.
  destruct ft as [fps t].
  specialize (H fps t eq_refl).
  inversion k; subst.
  + inversion X2; subst.
    specialize (H ftenv1 0 fenv0 x e0 e1 X3 eq_refl).  
    simpl in *.
    assert (t = t0).
    eapply H.
    auto.
    auto.
    Focus 2.
    eassumption.
    auto.
    rewrite H0.
    auto.
  + inversion X2; subst.
    subst ftenv' fenv'.
    subst ftenv'0 fenv'0. (* to compare X5 and X8 *)
    specialize (H ftenv1
                  (S n) fenv0 x e0 e1 X3 eq_refl).  
    simpl in *.
    assert (t = t0).
    eapply H.
    auto.
    eapply updateFEnvLemma.
    auto.
    auto.
    Focus 2.
    eauto.
    eapply updateFEnvLemma.
    auto.
    auto.
    rewrite H0.
    auto.

- (* Par_Q - FVar *)  
  unfold  UniQFType, UniFType, UniEType, UniETypeW, Par_SSB, Par_SSA.
  intros.  
  inversion X; subst.
  clear X.
  clear X3 X4.
  destruct ft as [fps t].
  specialize (H1 fps t eq_refl).  
  inversion X2; subst.
  destruct ft2.
  destruct f.

  inversion m; subst.
  inversion X3; subst.
  
  +
    inversion X; subst.
    rewrite H0 in H4.
    (*inversion X2; subst.
    inversion X8; subst. *)
    
(***)    
    assert (f0 = FC fenv fps e0 e1 x0 0).
    eapply (envAppendCompare FunTyping ls0 ls8 ls1 ls3). 
    eauto.
    eauto.
    eauto.
    auto.
    auto.
        
    rewrite H5 in *.
  
    specialize (H1 ftenv).  
    specialize (H1 0 fenv x0 e0 e1). 
    specialize (H1 X6 eq_refl).
    simpl in *.
    inversion X8; subst.

    assert (t = ret_type).
    eapply H1. 
    auto.
    auto.
    Focus 2.
    eauto.
    auto.
    rewrite H5.
    auto.
    
  + inversion X; subst.
    rewrite H0 in H4.
    (* inversion X2; subst. 
    inversion X9; subst. *)

    assert (f0 = FC fenv fps e0 e1 x0 (S n0)).
    eapply (envAppendCompare FunTyping ls0 ls8 ls1 ls3). 
    eauto.
    eauto.
    eauto.
    auto.
    auto.

    rewrite H5 in *.

    specialize (H1 ftenv).  
    specialize (H1 (S n0) fenv x0 e0 e1). 
    specialize (H1 X6 eq_refl).
    simpl in *.
    inversion X9; subst.

    assert (t = ret_type).
    eapply H1. 
    auto.
    eapply updateFEnvLemma.
    auto.
    auto.
    Focus 2.
    eauto.
    subst ftenv'0.
    eapply updateFEnvLemma.
    auto.
    auto.
    rewrite H5.
    auto.
    
- (* modify *)
  unfold UniEType.
  intros ftenv tenv fenv T1 T2 VT1 VT2 XF q K H0 t ftenv0 H0' X.
  inversion X; subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.  
  assert (VT4 = VT1).
  eapply loc_pi.
  subst.
  assert (VT5 = VT2).
  eapply loc_pi.
  subst.
  clear XF2.
  reflexivity.
  (* return *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  inversion X2; subst.
  inversion k; subst.
  eapply ValueStrongTyping.
  eauto.
  eauto.
  inversion k; subst.
  eapply IdStrongTyping.
  eauto.
  auto.
(* bindN *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  eauto.
  auto.
(* bindS *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  subst tenv'.
  assert (t1 = t3).
  eapply H.
  auto.
  Focus 2.
  eauto.
  auto.
  rewrite H1.
  eauto.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H.
  eapply overrideEnvLemmaT.
  assumption.
  assumption.
  Focus 2.
  assert (tenvP = tenvP0).
  eapply EnvStrongTyping.
  eauto.
  auto.
  rewrite H0.
  eauto.
  eapply overrideEnvLemmaT.
  auto.
  auto.
- unfold UniEType, UniQFType, UniPType.
  intros.  
  inversion X1; subst.
  assert (FT fps t = FT fps0 t2).
  eapply H.
  auto.
  eauto.
  auto.
  injection H1.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply ValueStrongTyping.
  eauto.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  eauto.
  auto.
- unfold UniEType, Par_SSL, UniPType.
  intros.
  dependent induction X; subst.
  inversion X2; subst.
  inversion X; subst.
  auto.
  destruct pt2.
  destruct ts.
  + inversion X2; subst.
    inversion X3.
  + inversion m; subst.
    inversion X2; subst.
    inversion X5; subst.
    assert (PT bbs = PT ts).
    {*  eapply IHX.
      auto.
      auto.
      Focus 2.
      econstructor.
      eauto.
      auto.
   }   
   injection H.
   intro.
   assert (b = v).
   {* eapply p0.
      auto.
      Focus 2.
      eauto.
      auto.
   }
   rewrite H0.
   rewrite H1.
   auto.
Qed.   



Definition PrmsTypingUni_rect :=
  PrmsTyping_str_rect UniFType UniQFType UniEType UniPType.


Lemma PrmsStrongTyping :
  forall (ftenv: funTC) (tenv: valTC) (fenv: funEnv)
         (ps: Prms) (pt: PTyp)   
         (k: PrmsTyping ftenv tenv fenv ps pt),  
         UniPType ftenv tenv fenv ps pt k.
Proof.
eapply PrmsTypingUni_rect.
- (* SLL *)
  unfold Par_SSL, UniEType.
  intros.
  constructor.
- (* SLL *)
  unfold Par_SSL, UniEType.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSA *)  
  unfold Par_SSA, UniFType.
  constructor.
- unfold Par_SSA, UniFType.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSB *)
  unfold Par_SSB, Par_SSA, UniFType.
  intros.
  econstructor.
  exact m0.
  exact m1.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
- (* Par_F *)
  unfold UniFType, UniETypeW, UniEType.
  intros.
  inversion H0; subst.
  inversion H1; subst. 
  intros.
  eapply H.
  auto.
  Focus 2.
  eauto.
  auto.
- (* Par_F *)
  unfold UniFType, UniETypeW, UniEType.
  intros ftenv tenv fenv.
  intros e0 e1 x n t.
  intros K1 K2 K3 HP1 HP2.
  intros fps t0 E3.
  intros ftenv1 i fenv1 x0 e2 e3 K4 E4.
  inversion E3; subst.
  inversion E4; subst.
  intros.
  eapply HP1.
  eapply updateFEnvLemma.
  assumption.
  assumption.
  eassumption.
  assumption.
- (* Par_Q - QF *)
  unfold UniQFType, UniFType, UniEType, UniETypeW.
  intros.
  inversion X1; subst.
  destruct ft as [fps t].
  specialize (H fps t eq_refl).
  inversion k; subst.
  + inversion X2; subst.
    specialize (H ftenv1 0 fenv0 x e0 e1 X3 eq_refl).  
    simpl in *.
    assert (t = t0).
    eapply H.
    auto.
    auto.
    Focus 2.
    eassumption.
    auto.
    rewrite H0.
    auto.
  + inversion X2; subst.
    subst ftenv' fenv'.
    subst ftenv'0 fenv'0. (* to compare X5 and X8 *)
    specialize (H ftenv1
                  (S n) fenv0 x e0 e1 X3 eq_refl).  
    simpl in *.
    assert (t = t0).
    eapply H.
    auto.
    eapply updateFEnvLemma.
    auto.
    auto.
    Focus 2.
    eauto.
    eapply updateFEnvLemma.
    auto.
    auto.
    rewrite H0.
    auto.

- (* Par_Q - FVar *)  
  unfold  UniQFType, UniFType, UniEType, UniETypeW, Par_SSB, Par_SSA.
  intros.  
  inversion X; subst.
  clear X.
  clear X3 X4.
  destruct ft as [fps t].
  specialize (H1 fps t eq_refl).  
  inversion X2; subst.
  destruct ft2.
  destruct f.

  inversion m; subst.
  inversion X3; subst.
  
  +
    inversion X; subst.
    rewrite H0 in H4.
    (*inversion X2; subst.
    inversion X8; subst. *)
    
(***)    
    assert (f0 = FC fenv fps e0 e1 x0 0).
    eapply (envAppendCompare FunTyping ls0 ls8 ls1 ls3). 
    eauto.
    eauto.
    eauto.
    auto.
    auto.
    
    rewrite H5 in *.
  
    specialize (H1 ftenv).  
    specialize (H1 0 fenv x0 e0 e1). 
    specialize (H1 X6 eq_refl).
    simpl in *.
    inversion X8; subst.

    assert (t = ret_type).
    eapply H1. 
    auto.
    auto.
    Focus 2.
    eauto.
    auto.
    rewrite H5.
    auto.
    
  + inversion X; subst.
    rewrite H0 in H4.
    (* inversion X2; subst. 
    inversion X9; subst. *)

    assert (f0 = FC fenv fps e0 e1 x0 (S n0)).
    eapply (envAppendCompare FunTyping ls0 ls8 ls1 ls3). 
    eauto.
    eauto.
    eauto.
    auto.
    auto.

    rewrite H5 in *.

    specialize (H1 ftenv).  
    specialize (H1 (S n0) fenv x0 e0 e1). 
    specialize (H1 X6 eq_refl).
    simpl in *.
    inversion X9; subst.

    assert (t = ret_type).
    eapply H1. 
    auto.
    eapply updateFEnvLemma.
    auto.
    auto.
    Focus 2.
    eauto.
    subst ftenv'0.
    eapply updateFEnvLemma.
    auto.
    auto.
    rewrite H5.
    auto.
    
- (* modify *)
  unfold UniEType.
  intros ftenv tenv fenv T1 T2 VT1 VT2 XF q K H0 t ftenv0 H0' X.
  inversion X; subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.  
  assert (VT4 = VT1).
  eapply loc_pi.
  subst.
  assert (VT5 = VT2).
  eapply loc_pi.
  subst.
  clear XF2.
  reflexivity.
  (* return *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  inversion X2; subst.
  inversion k; subst.
  eapply ValueStrongTyping.
  eauto.
  eauto.
  inversion k; subst.
  eapply IdStrongTyping.
  eauto.
  auto.
(* bindN *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  eauto.
  auto.
(* bindS *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  subst tenv'.
  assert (t1 = t3).
  eapply H.
  auto.
  Focus 2.
  eauto.
  auto.
  rewrite H1.
  eauto.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H.
  eapply overrideEnvLemmaT.
  assumption.
  assumption.
  Focus 2.
  assert (tenvP = tenvP0).
  eapply EnvStrongTyping.
  eauto.
  auto.
  rewrite H0.
  eauto.
  eapply overrideEnvLemmaT.
  auto.
  auto.
- unfold UniEType, UniQFType, UniPType.
  intros.  
  inversion X1; subst.
  assert (FT fps t = FT fps0 t2).
  eapply H.
  auto.
  eauto.
  auto.
  injection H1.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply ValueStrongTyping.
  eauto.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  eauto.
  auto.
- unfold UniEType, Par_SSL, UniPType.
  intros.
  dependent induction X; subst.
  inversion X2; subst.
  inversion X; subst.
  auto.
  destruct pt2.
  destruct ts.
  + inversion X2; subst.
    inversion X3.
  + inversion m; subst.
    inversion X2; subst.
    inversion X5; subst.
    assert (PT bbs = PT ts).
    {*  eapply IHX.
      auto.
      auto.
      Focus 2.
      econstructor.
      eauto.
      auto.
   }   
   injection H.
   intro.
   assert (b = v).
   {* eapply p0.
      auto.
      Focus 2.
      eauto.
      auto.
   }
   rewrite H0.
   rewrite H1.
   auto.
Qed.   


Definition QFunTypingUni_rect :=
  QFunTyping_str_rect UniFType UniQFType UniEType UniPType.


Lemma QFunStrongTyping :
  forall (ftenv: funTC) (fenv: funEnv)
         (qf: QFun) (ft: FTyp)  
         (k: QFunTyping ftenv fenv qf ft), 
     UniQFType ftenv fenv qf ft k.    
Proof.
eapply QFunTypingUni_rect.
- (* SLL *)
  unfold Par_SSL, UniEType.
  intros.
  constructor.
- (* SLL *)
  unfold Par_SSL, UniEType.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSA *)  
  unfold Par_SSA, UniFType.
  constructor.
- unfold Par_SSA, UniFType.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSB *)
  unfold Par_SSB, Par_SSA, UniFType.
  intros.
  econstructor.
  exact m0.
  exact m1.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
- (* Par_F *)
  unfold UniFType, UniETypeW, UniEType.
  intros.
  inversion H0; subst.
  inversion H1; subst. 
  intros.
  eapply H.
  auto.
  Focus 2.
  eauto.
  auto.
- (* Par_F *)
  unfold UniFType, UniETypeW, UniEType.
  intros ftenv tenv fenv.
  intros e0 e1 x n t.
  intros K1 K2 K3 HP1 HP2.
  intros fps t0 E3.
  intros ftenv1 i fenv1 x0 e2 e3 K4 E4.
  inversion E3; subst.
  inversion E4; subst.
  intros.
  eapply HP1.
  eapply updateFEnvLemma.
  assumption.
  assumption.
  eassumption.
  assumption.
- (* Par_Q - QF *)
  unfold UniQFType, UniFType, UniEType, UniETypeW.
  intros.
  inversion X1; subst.
  destruct ft as [fps t].
  specialize (H fps t eq_refl).
  inversion k; subst.
  + inversion X2; subst.
    specialize (H ftenv1 0 fenv0 x e0 e1 X3 eq_refl).  
    simpl in *.
    assert (t = t0).
    eapply H.
    auto.
    auto.
    Focus 2.
    eassumption.
    auto.
    rewrite H0.
    auto.
  + inversion X2; subst.
    subst ftenv' fenv'.
    subst ftenv'0 fenv'0. (* to compare X5 and X8 *)
    specialize (H ftenv1
                  (S n) fenv0 x e0 e1 X3 eq_refl).  
    simpl in *.
    assert (t = t0).
    eapply H.
    auto.
    eapply updateFEnvLemma.
    auto.
    auto.
    Focus 2.
    eauto.
    eapply updateFEnvLemma.
    auto.
    auto.
    rewrite H0.
    auto.

- (* Par_Q - FVar *)  
  unfold  UniQFType, UniFType, UniEType, UniETypeW, Par_SSB, Par_SSA.
  intros.  
  inversion X; subst.
  clear X.
  clear X3 X4.
  destruct ft as [fps t].
  specialize (H1 fps t eq_refl).  
  inversion X2; subst.
  destruct ft2.
  destruct f.

  inversion m; subst.
  inversion X3; subst.
  
  +
    inversion X; subst.
    rewrite H0 in H4.
    (*inversion X2; subst.
    inversion X8; subst. *)
    
(***)    
    assert (f0 = FC fenv fps e0 e1 x0 0).
    eapply (envAppendCompare FunTyping ls0 ls8 ls1 ls3). 
    eauto.
    eauto.
    eauto.
    auto.
    auto.
    
    rewrite H5 in *.
  
    specialize (H1 ftenv).  
    specialize (H1 0 fenv x0 e0 e1). 
    specialize (H1 X6 eq_refl).
    simpl in *.
    inversion X8; subst.

    assert (t = ret_type).
    eapply H1. 
    auto.
    auto.
    Focus 2.
    eauto.
    auto.
    rewrite H5.
    auto.
    
  + inversion X; subst.
    rewrite H0 in H4.
    (* inversion X2; subst. 
    inversion X9; subst. *)

    assert (f0 = FC fenv fps e0 e1 x0 (S n0)).
    eapply (envAppendCompare FunTyping ls0 ls8 ls1 ls3). 
    eauto.
    eauto.
    eauto.
    auto.
    auto.
    
    rewrite H5 in *.

    specialize (H1 ftenv).  
    specialize (H1 (S n0) fenv x0 e0 e1). 
    specialize (H1 X6 eq_refl).
    simpl in *.
    inversion X9; subst.

    assert (t = ret_type).
    eapply H1. 
    auto.
    eapply updateFEnvLemma.
    auto.
    auto.
    Focus 2.
    eauto.
    subst ftenv'0.
    eapply updateFEnvLemma.
    auto.
    auto.
    rewrite H5.
    auto.
    
- (* modify *)
  unfold UniEType.
  intros ftenv tenv fenv T1 T2 VT1 VT2 XF q K H0 t ftenv0 H0' X.
  inversion X; subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.  
  assert (VT4 = VT1).
  eapply loc_pi.
  subst.
  assert (VT5 = VT2).
  eapply loc_pi.
  subst.
  clear XF2.
  reflexivity.
  (* return *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  inversion X2; subst.
  inversion k; subst.
  eapply ValueStrongTyping.
  eauto.
  eauto.
  inversion k; subst.
  eapply IdStrongTyping.
  eauto.
  auto.
(* bindN *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  eauto.
  auto.
(* bindS *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  subst tenv'.
  assert (t1 = t3).
  eapply H.
  auto.
  Focus 2.
  eauto.
  auto.
  rewrite H1.
  eauto.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H.
  eapply overrideEnvLemmaT.
  assumption.
  assumption.
  Focus 2.
  assert (tenvP = tenvP0).
  eapply EnvStrongTyping.
  eauto.
  auto.
  rewrite H0.
  eauto.
  eapply overrideEnvLemmaT.
  auto.
  auto.
- unfold UniEType, UniQFType, UniPType.
  intros.  
  inversion X1; subst.
  assert (FT fps t = FT fps0 t2).
  eapply H.
  auto.
  eauto.
  auto.
  injection H1.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply ValueStrongTyping.
  eauto.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  eauto.
  auto.
- unfold UniEType, Par_SSL, UniPType.
  intros.
  dependent induction X; subst.
  inversion X2; subst.
  inversion X; subst.
  auto.
  destruct pt2.
  destruct ts.
  + inversion X2; subst.
    inversion X3.
  + inversion m; subst.
    inversion X2; subst.
    inversion X5; subst.
    assert (PT bbs = PT ts).
    {*  eapply IHX.
      auto.
      auto.
      Focus 2.
      econstructor.
      eauto.
      auto.
   }   
   injection H.
   intro.
   assert (b = v).
   {* eapply p0.
      auto.
      Focus 2.
      eauto.
      auto.
   }
   rewrite H0.
   rewrite H1.
   auto.
Qed.   

 
Definition FunTypingUni_rect :=
  FunTyping_str_rect UniFType UniQFType UniEType UniPType.


Lemma FunStrongTyping :
  forall (f: Fun) (ft: FTyp) (k: FunTyping f ft),
    UniFType f ft k.
Proof.
eapply FunTypingUni_rect.
- (* SLL *)
  unfold Par_SSL, UniEType.
  intros.
  constructor.
- (* SLL *)
  unfold Par_SSL, UniEType.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSA *)  
  unfold Par_SSA, UniFType.
  constructor.
- unfold Par_SSA, UniFType.
  intros.
  constructor.
  assumption.
  assumption.
  assumption.
- (* SSB *)
  unfold Par_SSB, Par_SSA, UniFType.
  intros.
  econstructor.
  exact m0.
  exact m1.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
- (* Par_F *)
  unfold UniFType, UniETypeW, UniEType.
  intros.
  inversion H0; subst.
  inversion H1; subst. 
  intros.
  eapply H.
  auto.
  Focus 2.
  eauto.
  auto.
- (* Par_F *)
  unfold UniFType, UniETypeW, UniEType.
  intros ftenv tenv fenv.
  intros e0 e1 x n t.
  intros K1 K2 K3 HP1 HP2.
  intros fps t0 E3.
  intros ftenv1 i fenv1 x0 e2 e3 K4 E4.
  inversion E3; subst.
  inversion E4; subst.
  intros.
  eapply HP1.
  eapply updateFEnvLemma.
  assumption.
  assumption.
  eassumption.
  assumption.
- (* Par_Q - QF *)
  unfold UniQFType, UniFType, UniEType, UniETypeW.
  intros.
  inversion X1; subst.
  destruct ft as [fps t].
  specialize (H fps t eq_refl).
  inversion k; subst.
  + inversion X2; subst.
    specialize (H ftenv1 0 fenv0 x e0 e1 X3 eq_refl).  
    simpl in *.
    assert (t = t0).
    eapply H.
    auto.
    auto.
    Focus 2.
    eassumption.
    auto.
    rewrite H0.
    auto.
  + inversion X2; subst.
    subst ftenv' fenv'.
    subst ftenv'0 fenv'0. 
    specialize (H ftenv1
                  (S n) fenv0 x e0 e1 X3 eq_refl).  
    simpl in *.
    assert (t = t0).
    eapply H.
    auto.
    eapply updateFEnvLemma.
    auto.
    auto.
    Focus 2.
    eauto.
    eapply updateFEnvLemma.
    auto.
    auto.
    rewrite H0.
    auto.

- (* Par_Q - FVar *)  
  unfold  UniQFType, UniFType, UniEType, UniETypeW, Par_SSB, Par_SSA.
  intros.  
  inversion X; subst.
  clear X.
  clear X3 X4.
  destruct ft as [fps t].
  specialize (H1 fps t eq_refl).  
  inversion X2; subst.
  destruct ft2.
  destruct f.

  inversion m; subst.
  inversion X3; subst.
  
  +
    inversion X; subst.
    rewrite H0 in H4.
    (*inversion X2; subst.
    inversion X8; subst. *)
    
(***)    
    assert (f0 = FC fenv fps e0 e1 x0 0).
    eapply (envAppendCompare FunTyping ls0 ls8 ls1 ls3). 
    eauto.
    eauto.
    eauto.
    auto.
    auto.
       
    rewrite H5 in *.
  
    specialize (H1 ftenv).  
    specialize (H1 0 fenv x0 e0 e1). 
    specialize (H1 X6 eq_refl).
    simpl in *.
    inversion X8; subst.

    assert (t = ret_type).
    eapply H1. 
    auto.
    auto.
    Focus 2.
    eauto.
    auto.
    rewrite H5.
    auto.
    
  + inversion X; subst.
    rewrite H0 in H4.
    (* inversion X2; subst. 
    inversion X9; subst. *)

    assert (f0 = FC fenv fps e0 e1 x0 (S n0)).
    eapply (envAppendCompare FunTyping ls0 ls8 ls1 ls3). 
    eauto.
    eauto.
    eauto.
    auto.
    auto.
    
    rewrite H5 in *.

    specialize (H1 ftenv).  
    specialize (H1 (S n0) fenv x0 e0 e1). 
    specialize (H1 X6 eq_refl).
    simpl in *.
    inversion X9; subst.

    assert (t = ret_type).
    eapply H1. 
    auto.
    eapply updateFEnvLemma.
    auto.
    auto.
    Focus 2.
    eauto.
    subst ftenv'0.
    eapply updateFEnvLemma.
    auto.
    auto.
    rewrite H5.
    auto.
    
- (* modify *)
  unfold UniEType.
  intros ftenv tenv fenv T1 T2 VT1 VT2 XF q K H0 t ftenv0 H0' X.
  inversion X; subst.
  eapply inj_pair2 in H6.
  eapply inj_pair2 in H6; subst.  
  assert (VT4 = VT1).
  eapply loc_pi.
  subst.
  assert (VT5 = VT2).
  eapply loc_pi.
  subst.
  clear XF2.
  reflexivity.
  (* return *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  inversion X2; subst.
  inversion k; subst.
  eapply ValueStrongTyping.
  eauto.
  eauto.
  inversion k; subst.
  eapply IdStrongTyping.
  eauto.
  auto.
(* bindN *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  eauto.
  auto.
(* bindS *)
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  subst tenv'.
  assert (t1 = t3).
  eapply H.
  auto.
  Focus 2.
  eauto.
  auto.
  rewrite H1.
  eauto.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H.
  eapply overrideEnvLemmaT.
  assumption.
  assumption.
  Focus 2.
  assert (tenvP = tenvP0).
  eapply EnvStrongTyping.
  eauto.
  auto.
  rewrite H0.
  eauto.
  eapply overrideEnvLemmaT.
  auto.
  auto.
- unfold UniEType, UniQFType, UniPType.
  intros.  
  inversion X1; subst.
  assert (FT fps t = FT fps0 t2).
  eapply H.
  auto.
  eauto.
  auto.
  injection H1.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply ValueStrongTyping.
  eauto.
  auto.
- unfold UniEType.
  intros.
  inversion X1; subst.
  eapply H0.
  auto.
  Focus 2.
  eauto.
  auto.
- unfold UniEType, Par_SSL, UniPType.
  intros.
  dependent induction X; subst.
  inversion X2; subst.
  inversion X; subst.
  auto.
  destruct pt2.
  destruct ts.
  + inversion X2; subst.
    inversion X3.
  + inversion m; subst.
    inversion X2; subst.
    inversion X5; subst.
    assert (PT bbs = PT ts).
    {*  eapply IHX.
      auto.
      auto.
      Focus 2.
      econstructor.
      eauto.
      auto.
   }   
   injection H.
   intro.
   assert (b = v).
   {* eapply p0.
      auto.
      Focus 2.
      eauto.
      auto.
   }
   rewrite H0.
   rewrite H1.
   auto.
Qed.   
   


Lemma UniFTypeLm0 (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft1: FTyp)
      (k: FunTyping (FC fenv tenv0 e0 e1 x 0) ft1) :
  UniFType (FC fenv tenv0 e0 e1 x 0) ft1 k ->
  UniFTypeS (FC fenv tenv0 e0 e1 x 0) ft1 k.
Proof.
  unfold UniFTypeS.
  unfold UniFType, UniFTypeS, UniETypeW.
  intros.
  destruct ft1 as [tenv t].
  destruct ft2.
  specialize (H tenv t eq_refl).
  inversion k; subst.
  inversion X; subst.
  rename prs_type into tenv.
  rename ret_type into t0.
  specialize (H ftenv 0 fenv x e0 e1 X0 eq_refl).
  simpl in *.
  specialize (H X1 X0).
  specialize (H t0 ftenv0 X2 X3).
  assert (t = t0).
  eapply ExpStrongTyping.
  exact X1.
  auto.
  exact X2.
  auto.
  rewrite H0.
  auto.
Qed.


Lemma UniFTypeLm0a (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft1 ft2: FTyp)
      (k: FunTyping (FC fenv tenv0 e0 e1 x 0) ft1) :
  UniFType (FC fenv tenv0 e0 e1 x 0) ft1 k ->
  FunTyping (FC fenv tenv0 e0 e1 x 0) ft2 -> ft1 = ft2.
  intros.
  eapply UniFTypeLm0.
  eauto.
  auto.
Qed.


Lemma UniFTypeLm0b (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft1 ft2: FTyp)
      (k1: FunTyping (FC fenv tenv0 e0 e1 x 0) ft1) 
      (k2: FunTyping (FC fenv tenv0 e0 e1 x 0) ft2) : ft1 = ft2.
  intros.
  inversion k1; subst.
  inversion k2; subst.
  assert (t = t0).
  eapply ExpStrongTyping.
  exact X0.
  auto.
  exact X1.
  auto.
  rewrite H.
  auto.
Qed.


Lemma UniFTypeLm1 (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft1: FTyp)
      (k1: FunTyping (FC fenv tenv0 e0 e1 x 1) ft1)
      (k0: FunTyping (FC fenv tenv0 e0 e1 x 0) ft1):
  UniFType (FC fenv tenv0 e0 e1 x 1) ft1 k1 ->
  UniFType (FC fenv tenv0 e0 e1 x 0) ft1 k0.
Proof.
  unfold UniFType.
  intros.
  destruct ft1 as [tenv1 t1].

  inversion H1; subst.
  inversion H0; subst.
  clear H1.
  clear H0.
  unfold UniETypeW in *.

  intros.
  eapply ExpStrongTyping.
  exact X0.
  auto.
  exact X2.
  auto.
Qed.


Lemma UniFTypeLmN (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (n: nat) (ft1: FTyp)
      (k1: FunTyping (FC fenv tenv0 e0 e1 x (S n)) ft1)
      (k0: FunTyping (FC fenv tenv0 e0 e1 x n) ft1):
  UniFType (FC fenv tenv0 e0 e1 x (S n)) ft1 k1 ->
  UniFType (FC fenv tenv0 e0 e1 x n) ft1 k0.
Proof.
  unfold UniFType.
  intros.
  destruct ft1 as [tenv1 t1].

  inversion H1; subst.
  inversion H0; subst.
  clear H1.
  clear H0.
  unfold UniETypeW in *.

  destruct i. 
  intros.
  eapply ExpStrongTyping.
  exact X0.
  auto.
  exact X2.
  auto.

  intros.
  inversion k0; subst.
  subst ftenv' fenv'.
  eapply ExpStrongTyping.
  exact X5.
  eapply updateFEnvLemma.
  auto.
  auto.
  eapply X2.
  auto.
Qed.

 

Lemma UniFTypeLm1b (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft1 ft2: FTyp)
      (k1: FunTyping (FC fenv tenv0 e0 e1 x 1) ft1) 
      (k2: FunTyping (FC fenv tenv0 e0 e1 x 0) ft2) : ft1 = ft2.
  intros.
  inversion k1; subst.
  inversion X1; subst.
  inversion k2; subst.
  subst ftenv' fenv'. 
  assert (t = t0).
  eapply ExpStrongTyping.
  exact X3.
  auto.
  exact X4.
  auto.
  rewrite H.
  auto.
Qed.



Lemma UniFTypeLmPb (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (n: nat) (ft1 ft2: FTyp)
      (k1: FunTyping (FC fenv tenv0 e0 e1 x n) ft1) 
      (k2: FunTyping (FC fenv tenv0 e0 e1 x (S n)) ft2) : ft1 = ft2.
Proof.
  intros.
  inversion k1; subst.
  
  - inversion k2; subst.
    inversion X3; subst.
    assert (t = t0).
    {+ eapply ExpStrongTyping.
       exact X0.
       auto.
       exact X4. 
       auto.
    }   
    rewrite H.
    auto.

  - inversion k2; subst.
    subst ftenv' fenv' ftenv'0 fenv'0.
    inversion X4; subst.
    subst ftenv' fenv'. 
    assert (t = t0).
    {+ eapply ExpStrongTyping.
       exact X0.
       eapply updateFEnvLemma.
       auto.
       auto.
       eapply updateFEnvLemma.
       eauto.
       eauto.
       auto.
    }
    rewrite H.
    auto.
Qed.    

Lemma UniFTypeLmNZE1 (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft: FTyp) :
  forall n: nat,
    FunTyping (FC fenv tenv0 e0 e1 x (S n)) ft ->
    sigT (fun ft0 => FunTyping (FC fenv tenv0 e0 e1 x n) ft0).
Proof.
  intros.
  inversion X; subst.  
  econstructor.
  eassumption.
Qed.



Lemma UniFTypeLmNZ1 (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft: FTyp) :
  forall n: nat,
    FunTyping (FC fenv tenv0 e0 e1 x (S n)) ft ->
    FunTyping (FC fenv tenv0 e0 e1 x n) ft.
Proof.
  intros.
  generalize X.
  eapply UniFTypeLmNZE1 in X.
  intro.
  destruct X as [ft0 X].
  eapply UniFTypeLmPb with (ft1:=ft0) (ft2:=ft) in X0.
  rewrite <- X0.
  auto.
  auto.
Qed.  


Lemma UniFTypeLmNZ (fenv: funEnv) (tenv0: valTC)
      (e0 e1: Exp) (x: Id) (ft: FTyp) :
  forall n: nat,
    FunTyping (FC fenv tenv0 e0 e1 x n) ft ->
    FunTyping (FC fenv tenv0 e0 e1 x 0) ft.
Proof.
  intros.
  induction n.
  auto.
  eapply UniFTypeLmNZ1 in X.
  eapply IHn.
  auto.
Qed.



Lemma UniFTypeLm (f: Fun) (ft1 ft2: FTyp) (k: FunTyping f ft1) :
  UniFType f ft1 k ->
  FunTyping f ft2 -> ft1 = ft2.
Proof.
  destruct f.
  induction n.
  eapply UniFTypeLm0a.
  intros.
  inversion k; subst.
  eapply (IHn X2).
  eapply UniFTypeLmN.
  exact H.
  inversion X; subst.
  auto. 
Qed.  


Lemma UniqueFunType (f: Fun) (ft1 ft2: FTyp)
      (k1: FunTyping f ft1) 
      (k2: FunTyping f ft2) :  ft1 = ft2.
Proof.
  eapply UniFTypeLm with (k:=k1).
  eapply FunStrongTyping.
  eauto.
Qed.


End Determ.
