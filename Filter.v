
Module Types.
  Inductive IntersectionType : Set :=
  | Var : nat -> IntersectionType
  | Arr : IntersectionType -> IntersectionType -> IntersectionType
  | Inter : IntersectionType -> IntersectionType -> IntersectionType
  | Omega : IntersectionType.

  Notation "σ → τ" := (Arr σ τ) (at level 88, right associativity).
  Notation "σ ∩ τ" := (Inter σ τ) (at level 80, right associativity).
  Definition ω := (Omega).

  Module SubtypeRelation.
    Reserved Notation "σ ≤ τ" (at level 89).
    Reserved Notation "σ ~ τ" (at level 89).
    
    Require Import Coq.Relations.Relation_Operators.
    Local Reserved Notation "σ ≤[ R ] τ" (at level 89).

    Inductive SubtypeRules {R : IntersectionType -> IntersectionType -> Prop}: IntersectionType -> IntersectionType -> Prop :=
    | R_InterMeetLeft : forall σ τ, σ ∩ τ ≤[R] σ
    | R_InterMeetRight : forall σ τ, σ ∩ τ ≤[R] τ
    | R_InterIdem : forall τ, τ ≤[R] τ ∩ τ
    | R_InterDistrib : forall σ τ ρ,
        (σ → ρ) ∩ (σ → τ) ≤[R] σ → ρ ∩ τ
    | R_SubtyDistrib: forall (σ σ' τ τ' : IntersectionType),
        R σ σ' -> R τ τ' -> σ ∩ τ ≤[R] σ' ∩ τ'
    | R_CoContra : forall σ σ' τ τ',
        R σ σ' -> R τ τ' -> σ' → τ ≤[R] σ → τ'
    | R_OmegaTop : forall σ, σ ≤[R] ω
    | R_OmegaArrow : ω ≤[R] ω → ω
    where "σ ≤[ R ] τ" := (SubtypeRules (R := R) σ τ).

    Definition SubtypeRules_Closure {R : IntersectionType -> IntersectionType -> Prop}: IntersectionType -> IntersectionType -> Prop :=
      clos_refl_trans IntersectionType (@SubtypeRules R).
    Local Notation "σ ≤*[ R ] τ" := (@SubtypeRules_Closure R σ τ) (at level 89).
    Local Reserved Notation "σ ≤* τ" (at level 89).

    Unset Elimination Schemes.
    Inductive Subtypes: IntersectionType -> IntersectionType -> Prop :=
    | ST : forall σ τ, σ ≤* τ -> σ ≤ τ
    where "σ ≤ τ" := (Subtypes σ τ)
      and "σ ≤* τ" := (σ ≤*[Subtypes] τ).
    Set Elimination Schemes.

    Hint Unfold SubtypeRules_Closure.
    Definition unST: forall σ τ, σ ≤ τ -> σ ≤* τ :=
      fun _ _ p =>
        match p with
        | ST _ _ p' => p'
        end.
    
    Coercion unST: Subtypes >-> SubtypeRules_Closure.
    
    Section Subtypes_ind.
      Variable P : IntersectionType -> IntersectionType -> Prop.
      Hypothesis InterMeetLeft_case: 
        forall σ τ : IntersectionType, P (σ ∩ τ) σ.
      Hypothesis InterMeetRight_case:
        forall σ τ : IntersectionType, P (σ ∩ τ) τ.
      Hypothesis InterIdem_case:
        forall τ : IntersectionType, P τ (τ ∩ τ).
      Hypothesis InterDistrib_case:
        forall σ τ ρ : IntersectionType, P ((σ → ρ) ∩ (σ → τ)) (σ → ρ ∩ τ).
      Hypothesis SubtyDistrib_case:
        forall σ σ': IntersectionType, σ ≤ σ' -> P σ σ' ->
          forall τ τ': IntersectionType, τ ≤ τ' -> P τ τ' ->
          P (σ ∩ τ) (σ' ∩ τ').
      Hypothesis CoContra_case:
        forall σ σ': IntersectionType, σ ≤ σ' -> P σ σ' ->
        forall τ τ': IntersectionType, τ ≤ τ' -> P τ τ' ->
        P (σ' → τ) (σ → τ').
      Hypothesis OmegaTop_case:
        forall σ : IntersectionType, P σ ω.
      Hypothesis OmegaArrow_case:
        P ω (ω → ω).
      Hypothesis Refl_case:
        forall σ : IntersectionType, P σ σ.

      Hypothesis Trans_case:
        forall σ τ : IntersectionType, σ ≤ τ -> P σ τ ->
        forall ρ : IntersectionType, τ ≤ ρ -> P τ ρ ->
        P σ ρ.

      Fixpoint Subtypes_ind {σ τ : IntersectionType} (p : σ ≤ τ) {struct p}: P σ τ :=
        match p in σ ≤ τ return P σ τ with
        | ST σ τ p' =>
          ((fix subtypes_closure_ind (σ τ : IntersectionType) (p : σ ≤* τ) {struct p}: P σ τ := 
            match p in (clos_refl_trans _ _ _ τ)return P σ τ with
            | rt_step τ p' =>
                ((fix subtypes_rules_ind (σ τ : IntersectionType) (p : σ ≤[Subtypes] τ) {struct p}: P σ τ :=
                  match p in σ ≤[_] τ return P σ τ with
                  | R_InterMeetLeft σ τ => InterMeetLeft_case σ τ
                  | R_InterMeetRight σ τ  => InterMeetRight_case σ τ
                  | R_InterIdem σ => InterIdem_case σ
                  | R_SubtyDistrib σ σ' τ τ' lteSigmaSigma' lteTauTau' =>
                         SubtyDistrib_case σ σ' lteSigmaSigma' (Subtypes_ind lteSigmaSigma')
                                           τ τ' lteTauTau' (Subtypes_ind lteTauTau')
                  | R_InterDistrib σ τ ρ =>
                      InterDistrib_case σ τ ρ
                  | R_CoContra σ σ' τ τ' lteSigmaSigma' lteTauTau' =>
                      CoContra_case σ σ' lteSigmaSigma' (Subtypes_ind lteSigmaSigma')
                                    τ τ' lteTauTau' (Subtypes_ind lteTauTau')
                  | R_OmegaTop σ =>
                      OmegaTop_case σ
                  | R_Omega_Arrow =>
                      OmegaArrow_case
                  end) σ τ p')
            | rt_refl => Refl_case σ
            | rt_trans τ ρ p1 p2 => 
                Trans_case σ τ (ST σ τ p1) (subtypes_closure_ind σ τ p1)
                           ρ (ST τ ρ p2) (subtypes_closure_ind τ ρ p2)
            end) σ τ p')
        end.
    End Subtypes_ind.
    
    Section Subtypes_ind_left.
      Variable σ : IntersectionType.
      Variable P : IntersectionType -> Prop.
      Hypothesis Start : P σ.
      Hypothesis Step : forall τ ρ, σ ≤ τ -> P τ -> τ ≤[Subtypes] ρ -> P ρ.

      Require Import Relations.Operators_Properties.
      
      Definition Subtypes_ind_left: forall τ, σ ≤ τ -> P τ :=
        let LiftStep : forall τ ρ, σ ≤* τ -> P τ -> τ ≤[Subtypes] ρ -> P ρ :=
          fun τ ρ => fun p1 r p2 => Step τ ρ (ST _ _ p1) r p2 in
        fun τ p =>
          clos_refl_trans_ind_left _ _ σ P Start LiftStep τ (unST _ _ p).
    End Subtypes_ind_left.
    
    Section Subtypes_ind_right.
      Variable ρ : IntersectionType.
      Variable P : IntersectionType -> Prop.
      Hypothesis Start : P ρ.
      Hypothesis Step : forall σ τ, σ ≤[Subtypes] τ -> P τ -> τ ≤ ρ -> P σ.

      Require Import Relations.Operators_Properties.
      Definition Subtypes_ind_right: forall σ, σ ≤ ρ -> P σ :=
        let LiftStep : forall σ τ, σ ≤[Subtypes] τ -> P τ -> τ ≤* ρ -> P σ :=
          fun σ τ => fun p1 r p2 => Step σ τ p1 r (ST _ _ p2) in
        fun σ p =>
          clos_refl_trans_ind_right _ _ P ρ Start LiftStep σ (unST _ _ p).
    End Subtypes_ind_right.
    

    Definition liftSubtypeProof {σ τ} (p : σ ≤[Subtypes] τ): σ ≤ τ :=
      ST _ _ (rt_step _ _ _ _ p).

    Definition InterMeetLeft {σ τ}: σ ∩ τ ≤ σ := 
      liftSubtypeProof (R_InterMeetLeft σ τ).
    Definition InterMeetRight {σ τ}: σ ∩ τ ≤ τ :=
      liftSubtypeProof (R_InterMeetRight σ τ).
    Definition InterIdem {τ}: τ ≤ τ ∩ τ :=
      liftSubtypeProof (R_InterIdem τ).
    Definition InterDistrib {σ τ ρ}: (σ → ρ) ∩ (σ → τ) ≤ σ → ρ ∩ τ :=
      liftSubtypeProof (R_InterDistrib σ τ ρ).
    Definition SubtyDistrib {σ σ' τ τ'}: σ ≤ σ' -> τ ≤ τ' -> σ ∩ τ ≤ σ' ∩ τ' :=
      fun p1 p2 => liftSubtypeProof (R_SubtyDistrib σ σ' τ τ' p1 p2).
    Definition CoContra {σ σ' τ τ'}: σ ≤ σ' -> τ ≤ τ' -> σ' → τ ≤ σ → τ' :=
      fun p1 p2 => liftSubtypeProof (R_CoContra σ σ' τ τ' p1 p2).
    Definition OmegaTop {σ}: σ ≤ ω :=
      liftSubtypeProof (R_OmegaTop σ).
    Definition OmegaArrow: ω ≤ ω → ω :=
      liftSubtypeProof (R_OmegaArrow).
 
    Inductive EqualTypes : IntersectionType -> IntersectionType -> Prop :=
    | InducedEq {σ τ}: σ ≤ τ -> τ ≤ σ -> σ ~ τ
    where "σ ~ τ" := (EqualTypes σ τ).

      
    Definition EqualTypesAreSubtypes_left: forall σ τ, σ ~ τ -> σ ≤ τ :=
      fun _ _ eqtys =>
        match eqtys with
        | InducedEq _ _ l _ => l
        end.
    Definition EqualTypesAreSubtypes_right: forall σ τ, σ ~ τ -> τ ≤ σ :=
      fun _ _ eqtys => 
        match eqtys with
        | InducedEq _ _ _ r => r
        end.
    Coercion EqualTypesAreSubtypes_left : EqualTypes >-> Subtypes.
    Coercion EqualTypesAreSubtypes_right : EqualTypes >-> Subtypes.
     
    Hint Resolve InterMeetLeft InterMeetRight InterIdem InterDistrib OmegaTop OmegaArrow InducedEq.

    Require Import Coq.Classes.RelationClasses.
    Require Import Coq.Relations.Operators_Properties.
    Require Import Coq.Relations.Relation_Definitions.
    Instance Subtypes_Reflexive : Reflexive Subtypes :=
      fun σ => ST _ _ ((clos_rt_is_preorder _ _).(preord_refl _ _) σ).
    Instance Subtypes_Transitive : Transitive Subtypes := 
      fun σ τ ρ p1 p2 => ST _ _ ((clos_rt_is_preorder _ _).(preord_trans _ _) σ τ ρ (unST _ _ p1) (unST _ _ p2)).
    Instance Subtypes_Preorder : PreOrder Subtypes :=
      {| PreOrder_Reflexive := Subtypes_Reflexive; 
         PreOrder_Transitive := Subtypes_Transitive |}.

    Instance EqualTypes_Reflexive: Reflexive EqualTypes :=
      fun σ => InducedEq (reflexivity σ) (reflexivity σ).
    Instance EqualTypes_Transitive: Transitive EqualTypes.
    Proof.
      unfold Transitive.
      intros.
      destruct H.
      destruct H0.
      eapply InducedEq.
      exact (transitivity H H0).
      exact (transitivity H2 H1).
    Qed.
    Instance EqualTypes_Symmetric: Symmetric EqualTypes.
    Proof.
      unfold Symmetric.
      intros.
      destruct H.
      eapply InducedEq.
      exact H0.
      exact H.
    Qed.

    Section BetaLemmas.
      Inductive Ω: IntersectionType -> Prop :=
      | Om : Ω ω
      | OmArr : forall σ ρ, Ω ρ -> Ω (σ → ρ)
      | OmInter : forall σ ρ, Ω σ -> Ω ρ -> Ω (σ ∩ ρ).
   
      Section Omega_equiv.
        Fact Omega_eq: ω ~ ω.
        Proof.
          reflexivity.
        Qed.
        Hint Resolve Omega_eq.

        Fact Arrow_Tgt_Omega_eq {σ ρ : IntersectionType}:
          ω ~ ρ -> ω ~ σ → ρ.
        Proof.
          intro rhoOmega.
          split.
          - apply (transitivity OmegaArrow).
            apply CoContra.
            + exact OmegaTop.
            + exact rhoOmega.
          - exact OmegaTop.
        Qed.
        Hint Resolve Arrow_Tgt_Omega_eq.

        Fact Omega_Inter_Omega_eq {σ ρ : IntersectionType}:
           ω ~ σ -> ω ~ ρ -> ω ~ σ ∩ ρ.
        Proof.
          intros sigmaOmega rhoOmega.
          split.
          - apply (transitivity InterIdem).
            apply SubtyDistrib.
            + exact sigmaOmega.
            + exact rhoOmega.
          - exact OmegaTop.
        Qed.
        Hint Resolve Omega_Inter_Omega_eq.

        Fact Omega_equiv: forall σ, Ω σ -> ω ~ σ.
        Proof.
          intros. 
          induction H; auto.
        Qed.
      End Omega_equiv.

      Fact Omega_closed:
        forall σ τ, σ ≤ τ -> Ω σ -> Ω τ.
      Proof.
        intros σ τ H.
        induction H; intro Hω; try solve [ inversion Hω; auto ].
        - apply OmInter; auto.
        - inversion Hω as [ | | * * σρω στω ].
          inversion σρω as [ | * * ρω | ].
          inversion στω as [ | * * τω | ].
          exact (OmArr _ _ (OmInter _ _ ρω τω)).
        - inversion Hω as [ | | * * ωσ ωτ ].
          exact (OmInter _ _ (IHSubtypes1 ωσ) (IHSubtypes2 ωτ)).
        - inversion Hω as [ | * * ωτ | ].
          exact (OmArr _ _ (IHSubtypes2 ωτ)).
        - exact Om.
        - exact (OmArr _ _ Om).
        - exact Hω.
      Qed.

      Require Import Program.Equality.
      Fact Var_never_omega:
        forall n, ω ≤ Var n -> False.
      Proof.
        intros n ωLEn.
        set (ωn := Omega_closed _ _ ωLEn Om).
        inversion ωn.
      Qed.

      Lemma Beta_Omega:
        forall σ τ, ω ~ σ → τ <-> ω ~ τ.
      Proof.
        intros.
        split.
        - intro στEQω.
          set (στω := Omega_closed _ _ στEQω Om).
          inversion στω as [ | * * ωτ | ].
          exact (Omega_equiv _ ωτ).
        - exact Arrow_Tgt_Omega_eq.
      Qed.

      Reserved Notation "↑α[ n ] σ " (at level 89).
      Inductive VariableSuperset (n : nat): IntersectionType -> Prop :=
        | V_Var : ↑α[n] (Var n)
        | V_Omega : forall σ, σ ~ ω -> ↑α[n] σ
        | V_Inter : forall σ τ, ↑α[n] σ -> ↑α[n] τ -> ↑α[n] σ ∩ τ
      where "↑α[ n ] σ" := (VariableSuperset n σ).

      Fact VariableSuperset_ge : 
        forall n σ, ↑α[n] σ -> (Var n) ≤ σ.
      Proof.
        induction σ; intro.
        - inversion H.
          + reflexivity.
          + contradict (Var_never_omega n0 (EqualTypesAreSubtypes_right _ _ H0)).
        - inversion H.
          transitivity ω .
          + exact OmegaTop.
          + exact (EqualTypesAreSubtypes_right _ _ H0).
        - inversion H.
          + transitivity ω.
            * exact OmegaTop.
            * exact (EqualTypesAreSubtypes_right _ _ H0).  
          + transitivity (Var n ∩ Var n).
            * exact (InterIdem).
            * exact (SubtyDistrib (IHσ1 H2) (IHσ2 H3)).
        - exact OmegaTop.
      Qed.

      Fact ge_VariableSuperset:
        forall σ τ, σ ≤ τ -> forall n, ↑α[n] σ -> ↑α[n] τ.
      Proof.
        intros σ τ σLEτ.
        induction σLEτ.
        - intros n H.
          inversion H.
          + apply (V_Omega _ _).
            split.
            * exact OmegaTop.
            * transitivity (σ ∩ τ).
              { exact (EqualTypesAreSubtypes_right _ _ H0). }
              { exact InterMeetLeft. }
          + exact H2.
        - intros n H.
          inversion H.
          + apply (V_Omega _ _).
            split.
            * exact OmegaTop.
            * transitivity (σ ∩ τ).
              { exact (EqualTypesAreSubtypes_right _ _ H0). }
              { exact InterMeetRight. }
          + exact H3.
        - intros n H.
          exact (V_Inter _ _ _ H H).
        - intros n H.
          inversion H.
          + apply (V_Omega _ _).
            split.
            * exact OmegaTop.
            * transitivity ((σ → ρ) ∩ (σ → τ)).
              { exact (EqualTypesAreSubtypes_right _ _ H0). } 
              { exact InterDistrib. }
          + inversion H2.
            inversion H3.
            apply (V_Omega _ _).
            split.
            * exact OmegaTop.
            * transitivity (ω ∩ ω).
              { exact InterIdem. }
              { transitivity ((σ → ρ) ∩ (σ → τ)).
                - exact (SubtyDistrib (EqualTypesAreSubtypes_right _ _ H4) (EqualTypesAreSubtypes_right _ _ H6)).
                - exact InterDistrib. }
        - intros n H.
          inversion H.
          + apply (V_Omega _ _).
            split.
            * exact OmegaTop.
            * transitivity (σ ∩ τ).
              { exact (EqualTypesAreSubtypes_right _ _ H0). }
              { exact (SubtyDistrib σLEτ1 σLEτ2). }
          + exact (V_Inter _ _ _ (IHσLEτ1 n H2) (IHσLEτ2 n H3)).
        - intros n H.
          inversion H.
          apply (V_Omega _ _).
          split.
          + exact OmegaTop.
          + transitivity (σ' → τ).
            * exact (EqualTypesAreSubtypes_right _ _ H0).
            * exact (CoContra σLEτ1 σLEτ2).
        - intros n H.
          exact (V_Omega _ _ Omega_eq).
        - intros n H.
          apply (V_Omega _ _).
          symmetry.
          exact (Arrow_Tgt_Omega_eq (Omega_eq)).
        - intros n H.
          exact H.
        - intros n H.
          exact (IHσLEτ2 n (IHσLEτ1 n H)).
      Qed.
      
      Reserved Notation "↑[ σ ] → [ τ ] ρ" (at level 89).
      Inductive ArrowSuperset (σ τ : IntersectionType): IntersectionType -> Prop :=
        | A_Arrow : forall σ' τ', σ' ≤ σ -> τ ≤ τ' -> ↑[σ] → [τ] σ' → τ'
        | A_Inter : forall σ' τ' ρ1 ρ2,
            ↑[σ] → [ρ1] σ' -> ↑[σ] → [ρ2] τ' -> ρ1 ∩ ρ2 ≤ τ -> ↑[σ] → [τ] σ' ∩ τ'
      where "↑[ σ ] → [ τ ] ρ" := (ArrowSuperset σ τ ρ).




      Definition ArrowSelection (ρ σ τ: IntersectionType): Prop :=
        let fix sel (ρ : IntersectionType) 
                (contAdd : Prop -> IntersectionType -> Prop)
                (contSkip : Prop): Prop :=
          match ρ with
            | Arr σ' τ' => contAdd (σ ≤ σ') τ'
            | Inter σ' τ' => 
                sel τ' (fun σsel τsel => 
                  sel σ' (fun σsel' τsel' => 
                      contAdd (σsel' /\ σsel) (τsel' ∩ τsel))
                    (contAdd σsel τsel))
                  (sel σ' contAdd contSkip)
            | _ => contSkip
            end in
        sel ρ (fun σsel τsel => σsel /\ (τsel ≤ τ)) (False).
      
      Definition Beta_Arrows:
        forall ρ σ τ, ρ ≤ σ → τ -> ArrowSelection ρ σ τ.
      Proof.
        induction ρ.
        Focus 3.
        - intros σ τ ρLEστ.
          inversion ρLEστ.
          rewrite <- H0 in H.
          inversion H; inversion H2;
            try solve [ rewrite <- H4 in H0 || rewrite <- H6 in H0 || rewrite H2 in H0; discriminate H0 ].
          + 
           
        induction ρLEστ.
        - 


  End SubtypeRelation.


End Types.
