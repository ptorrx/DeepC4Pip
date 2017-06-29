
Require Export Basics.
Require Export EnvLibA.
Require Export RelLibA.

Require Export Coq.Program.Equality.
Require Import Coq.Init.Specif.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import Coq.Lists.List.

Require Import IdModTypeA.
Require Import StaticSemA.
Require Import TRInductA.
Require Import WeakenA.

Import ListNotations.

Module Invert (IdT: IdModType) <: IdModType.

Definition Id := IdT.Id.
Definition IdEqDec := IdT.IdEqDec.
Definition IdEq := IdT.IdEq.
Definition W := IdT.W.
Definition Loc_PI := IdT.Loc_PI.
Definition BInit := IdT.BInit.
Definition WP := IdT.WP.

Module WeakenI := Weaken IdT.
Export WeakenI.


(** inverse big-step lemmas *)

Lemma BindN_BStep1 (fenv: funEnv) (env: valEnv)
      (e1 e2: Exp) (v: Value) (s s': W) : 
  (forall (e:Exp) (s: W), sigT (fun v: Value =>
                 sigT (fun s': W => 
      EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v))))) ->
  (forall (e:Exp) (s s1 s2: W) (v1 v2: Value), 
      EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
      EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) -> 
        (s1 = s2) /\ (v1 = v2)) ->
  EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s' (Val v)) ->
  (sigT2 (fun s1 : W =>
            (sigT (fun v1: Value =>
                     EClosure fenv env (Conf Exp s e1) (Conf Exp s1 (Val v1)))))
         (fun s1 : W =>
            EClosure fenv env (Conf Exp s1 e2) (Conf Exp s' (Val v)))).
  intros X K.
  intros.
  generalize X.
  intro X1.
  specialize (X e1 s).
  destruct X as [v1 X].
  destruct X as [s1 X].
  specialize (X1 e2 s1).  
  destruct X1 as [v2 X1].
  destruct X1 as [s2 X1].

  generalize X.
  intro K1.
  eapply BindN_extended_congruence in X.
  instantiate (1:=e2) in X.
  
  assert (EStep fenv env (Conf Exp s1 (BindN (Val v1) e2)) (Conf Exp s1 e2)).
  constructor.
  eapply StepIsEClos in X2.
  
  assert (EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s1 e2)).
  eapply EClosConcat.
  exact X.
  assumption.  

  assert (EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s2 (Val v2))).
  eapply EClosConcat.
  exact X3.
  assumption.

  assert (s' = s2 /\ v = v2).
  eapply K.
  eauto.
  assumption.
  destruct H.
  subst.

  econstructor.
  econstructor.  
  eauto. 
  auto.
Defined.
  

Lemma BindN_BStep2 (fenv: funEnv) (env: valEnv)
      (e1 e2: Exp) (v: Value) (s s': W) : 
  (forall (e:Exp) (s: W), sigT (fun v: Value =>
                 sigT (fun s': W => 
      EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v))))) ->
  (forall (e:Exp) (s s1 s2: W) (v1 v2: Value), 
      EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
      EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) -> 
        (s1 = s2) /\ (v1 = v2)) ->
  EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s' (Val v)) ->
  forall (s1 : W) (v1: Value),
    EClosure fenv env (Conf Exp s e1) (Conf Exp s1 (Val v1)) ->
    EClosure fenv env (Conf Exp s1 e2) (Conf Exp s' (Val v)).
  intros.
  generalize X1.
  intro X2.
  eapply BindN_extended_congruence in X1.
  instantiate (1:= e2) in X1.

  assert (EStep fenv env (Conf Exp s1 (BindN (Val v1) e2)) (Conf Exp s1 e2)).
  constructor.
  eapply StepIsEClos in X3.
  assert (EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s1 e2)).
  eapply EClosConcat.
  exact X1.
  auto.
  specialize (X e2 s1).
  destruct X as [v2 X].
  destruct X as [s2 X].
  assert (EClosure fenv env (Conf Exp s (BindN e1 e2)) (Conf Exp s2 (Val v2))).
  eapply EClosConcat.
  exact X4.
  auto.
  assert (s' = s2 /\ v = v2).
  eapply H.
  exact X0.
  auto.
  destruct H0.
  subst.
  auto.
Defined.



Lemma BindS_BStep1 (fenv: funEnv) (env: valEnv)
      (e1 e2: Exp) (x: Id) (v: Value) (s s': W) : 
  (forall (fenv: funEnv) (env: valEnv) (e:Exp) (s: W), sigT (fun v: Value =>
                 sigT (fun s': W => 
      EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v))))) ->
  (forall (e:Exp) (s s1 s2: W) (v1 v2: Value), 
      EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
      EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) -> 
        (s1 = s2) /\ (v1 = v2)) ->
  EClosure fenv env (Conf Exp s (BindS x e1 e2)) (Conf Exp s' (Val v)) ->
  sigT (fun s1 : W =>
     (sigT2 (fun v1: Value =>
        EClosure fenv env (Conf Exp s e1) (Conf Exp s1 (Val v1)))
              (fun v1 : Value =>
        EClosure fenv ((x,v1)::env) (Conf Exp s1 e2) (Conf Exp s' (Val v))))).
  intros X K.
  intros.
  generalize X.
  intro X1.
  specialize (X fenv env e1 s).
  destruct X as [v1 X].
  destruct X as [s1 X].
  generalize X.
  intro K1.
  eapply BindS_extended_congruence in X.
  instantiate (1:=e2) in X.
  instantiate (1:=x) in X.
  
  assert (EStep fenv env (Conf Exp s1 (BindS x (Val v1) e2))
                         (Conf Exp s1 (BindMS emptyE [(x,v1)] e2))).
  constructor.
  eapply StepIsEClos in X2.
  
  assert (EClosure fenv env (Conf Exp s (BindS x e1 e2))
                            (Conf Exp s1 (BindMS emptyE [(x,v1)] e2))).
  eapply EClosConcat.
  exact X.
  assumption.  

  specialize (X1 fenv ((x,v1)::env) e2 s1).  
  destruct X1 as [v2 X1].
  destruct X1 as [s2 X1].

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
  exact X4.
  eapply StepIsEClos.
  constructor.
  
  assert (s' = s2 /\ v = v2).
  eapply K.
  eauto.
  assumption.
  destruct H.
  subst.

  econstructor.
  econstructor.  
  eauto. 
  auto.
Defined.



Lemma Apply_BStep1 (fenv: funEnv) (env: valEnv)
      (f: Fun) (es: list Exp) (v: Value) (s s': W) : 
  (forall (fenv: funEnv) (env: valEnv) (e:Exp) (s: W), sigT (fun v: Value =>
                 sigT (fun s': W => 
      EClosure fenv env (Conf Exp s e) (Conf Exp s' (Val v))))) ->
  (forall (fenv: funEnv) (env: valEnv) (es:list Exp) (s: W),
      sigT (fun vs: list Value =>
                 sigT (fun s': W => 
      PrmsClosure fenv env (Conf Prms s (PS es))
                           (Conf Prms s' (PS (map Val vs)))))) ->
   (forall (e:Exp) (s s1 s2: W) (v1 v2: Value), 
      EClosure fenv env (Conf Exp s e) (Conf Exp s1 (Val v1)) ->
      EClosure fenv env (Conf Exp s e) (Conf Exp s2 (Val v2)) -> 
        (s1 = s2) /\ (v1 = v2)) ->

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
  intros P1 P2 P3.
  destruct f.
  intros.

  generalize P2.
  intro P0.
  specialize (P0 fenv env es s).
  destruct P0 as [vs P0].
  destruct P0 as [s1 P0].
  generalize P0. 
  intro X0.
  eapply Apply1_extended_congruence with (f:=(FC fenv0 tenv e0 e1 x n)) in X0.
  
  econstructor.
  instantiate (1:=s1). 

  generalize P0.
  intro P6.
  eapply PrmsClos_aux0 in P6.
  rewrite map_length with (f:=Val) in P6.
  rewrite P6 in H.
  clear P6.

  econstructor.
  instantiate (1:=vs).
  exact P0.
  
  destruct n.
(**)
  generalize P1.
  intro P5.
  specialize (P5 fenv0 (mkVEnv tenv vs) e0 s1).
  destruct P5 as [v2 P5].
  destruct P5 as [s2 P5].
  
  assert (EClosure fenv env (Conf Exp s1
            (Apply (QF (FC fenv0 tenv e0 e1 x 0)) (PS (map Val vs))))
                   (Conf Exp s1 (BindMS fenv0 (mkVEnv tenv vs) e0))).             eapply StepIsEClos.
  econstructor.
  econstructor.
  reflexivity.
  exact H.
  reflexivity.

  assert (EClosure fenv env (Conf Exp s1 (BindMS fenv0 (mkVEnv tenv vs) e0))
                       (Conf Exp s2 (BindMS fenv0 (mkVEnv tenv vs) (Val v2)))).
  eapply BindMS_extended_congruence.
  reflexivity.
  reflexivity.
  eapply weaken.
  exact P5.

  assert (EClosure fenv env
                   (Conf Exp s2 (BindMS fenv0 (mkVEnv tenv vs) (Val v2)))
                   (Conf Exp s2 (Val v2))).
  eapply StepIsEClos.
  econstructor.

  assert (EClosure fenv env
        (Conf Exp s (Apply (QF (FC fenv0 tenv e0 e1 x 0)) (PS es)))
        (Conf Exp s2 (Val v2))).
  eapply EClosConcat.
  exact X0.
  eapply EClosConcat.
  exact X1.  
  eapply EClosConcat.
  exact X2.
  exact X3.

  assert (s' = s2 /\ v = v2).
  eapply P3.
  exact X.
  exact X4.

  destruct H0. 
  subst.
  exact P5.
(**)
 
  generalize P1.
  intro P5.
  set ((x, FC fenv0 tenv e0 e1 x n) :: fenv0) as fenv'.
  
  specialize (P5 fenv' (mkVEnv tenv vs) e1 s1).
  destruct P5 as [v2 P5].
  destruct P5 as [s2 P5].
  
  assert (EClosure fenv env (Conf Exp s1
            (Apply (QF (FC fenv0 tenv e0 e1 x (S n))) (PS (map Val vs))))
                   (Conf Exp s1
                         (BindMS fenv' (mkVEnv tenv vs) e1))).
  eapply StepIsEClos.
  econstructor.
  econstructor.
  reflexivity.
  exact H.
  reflexivity.

  assert (EClosure fenv env (Conf Exp s1 (BindMS fenv' (mkVEnv tenv vs) e1))
                       (Conf Exp s2 (BindMS fenv' (mkVEnv tenv vs) (Val v2)))).
  eapply BindMS_extended_congruence.
  reflexivity.
  reflexivity.
  eapply weaken.
  exact P5.

  assert (EClosure fenv env
                   (Conf Exp s2 (BindMS fenv' (mkVEnv tenv vs) (Val v2)))
                   (Conf Exp s2 (Val v2))).
  eapply StepIsEClos.
  econstructor.

  assert (EClosure fenv env
        (Conf Exp s (Apply (QF (FC fenv0 tenv e0 e1 x (S n))) (PS es)))
        (Conf Exp s2 (Val v2))).
  eapply EClosConcat.
  exact X0.
  eapply EClosConcat.
  exact X1.  
  eapply EClosConcat.
  exact X2.
  exact X3.

  assert (s' = s2 /\ v = v2).
  eapply P3.
  exact X.
  exact X4.

  destruct H0. 
  subst.
  exact P5.
Defined.


End Invert.

