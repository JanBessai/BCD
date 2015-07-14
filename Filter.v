
Module Types.
  Inductive IntersectionType : Set :=
  | Var : nat -> IntersectionType
  | Arr : IntersectionType -> IntersectionType -> IntersectionType
  | Inter : IntersectionType -> IntersectionType -> IntersectionType
  | Omega : IntersectionType.

  Infix "→" := (Arr) (at level 88, right associativity).
  Notation "(→)" := Arr (only parsing).
  Infix "∩" := (Inter) (at level 80, right associativity).
  Notation "(∩)" := (Inter) (only parsing).
  Definition ω := (Omega).

  Module SubtypeRelation.
    Reserved Infix "≤" (at level 89).
    Reserved Infix "~" (at level 89).
    
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
    Notation "(≤[ R ])" := (SubtypeRules (R := R)) (only parsing).

    Definition SubtypeRules_Closure {R : IntersectionType -> IntersectionType -> Prop}: IntersectionType -> IntersectionType -> Prop :=
      clos_refl_trans IntersectionType (@SubtypeRules R).
    Local Notation "σ ≤*[ R ] τ" := (@SubtypeRules_Closure R σ τ) (at level 89).
    Local Notation "(≤*[ R ])" := (@SubtypeRules_Closure R) (only parsing).
    Local Reserved Infix "≤*" (at level 89).

    Unset Elimination Schemes.
    Inductive Subtypes: IntersectionType -> IntersectionType -> Prop :=
    | ST : forall σ τ, σ ≤* τ -> σ ≤ τ
    where "σ ≤ τ" := (Subtypes σ τ)
      and "σ ≤* τ" := (σ ≤*[Subtypes] τ).
    Notation "(≤)" := (Subtypes) (only parsing).
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
    Notation "(~)" := (EqualTypes) (only parsing).

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
    (*Coercion EqualTypesAreSubtypes_right : EqualTypes >-> Subtypes.*)
     
    Create HintDb SubtypeHints.
    Hint Resolve InterMeetLeft InterMeetRight InterIdem InterDistrib OmegaTop OmegaArrow InducedEq: SubtypeHints.

    Require Import Coq.Classes.RelationClasses.
    Require Import Coq.Relations.Operators_Properties.
    Require Import Coq.Relations.Relation_Definitions.
    Instance Subtypes_Reflexive : Reflexive (≤) :=
      fun σ => ST _ _ ((clos_rt_is_preorder _ _).(preord_refl _ _) σ).
    Instance Subtypes_Transitive : Transitive (≤) := 
      fun σ τ ρ p1 p2 => ST _ _ ((clos_rt_is_preorder _ _).(preord_trans _ _) σ τ ρ (unST _ _ p1) (unST _ _ p2)).  
    Instance Subtypes_Preorder : PreOrder (≤) :=
      {| PreOrder_Reflexive := Subtypes_Reflexive; 
         PreOrder_Transitive := Subtypes_Transitive |}.

    Instance EqualTypes_Reflexive: Reflexive (~) :=
      fun σ => InducedEq (reflexivity σ) (reflexivity σ).
    Instance EqualTypes_Transitive: Transitive (~).
    Proof.
      unfold Transitive.
      intros σ τ ρ p1 p2.
      inversion p1.
      inversion p2.
      split; transitivity τ; assumption.
    Defined.
    Instance EqualTypes_Symmetric: Symmetric (~).
    Proof.
      unfold Symmetric.
      intros σ τ p.
      inversion p.
      apply InducedEq; assumption.
    Defined.
    Instance EqualTypes_Equivalence: Equivalence (~) :=
      {| Equivalence_Reflexive := EqualTypes_Reflexive;
         Equivalence_Transitive := EqualTypes_Transitive;
         Equivalence_Symmetric := EqualTypes_Symmetric |}.

    Instance Subtypes_PartialOrder : PartialOrder (~) (≤).
    Proof.
      compute.
      intros.
      split.
      - split.
        + apply EqualTypesAreSubtypes_left.
          assumption.
        + apply EqualTypesAreSubtypes_right.
          assumption.
      - intros [p1 p2].
        apply InducedEq; assumption.
    Defined.

    Require Import Classes.Morphisms.
    Class Monoid {A} (equiv : relation A) `{Equivalence A equiv} (f : A -> A -> A) (unit : A) :=
      { associativity : forall x y z, equiv (f (f x y) z) (f x (f y z));
        identity_left : forall x, equiv x (f unit x);
        identity_right : forall x, equiv x (f x unit);
        f_proper :> Proper (equiv ==> equiv ==> equiv) f }.

    Fact InterAssociative: forall { σ τ ρ }, (σ ∩ τ) ∩ ρ ~ σ ∩ τ ∩ ρ.
    Proof.
      split.
      - apply (transitivity InterIdem).
        apply SubtyDistrib.
        + apply (transitivity InterMeetLeft).
          exact InterMeetLeft.
        + apply (SubtyDistrib).
          * exact InterMeetRight.
          * reflexivity.
      - apply (transitivity InterIdem).
        apply (SubtyDistrib).
        + apply (SubtyDistrib).
          * reflexivity.
          * exact InterMeetLeft.
        + apply (transitivity InterMeetRight).
          exact InterMeetRight.
    Defined.
    Hint Resolve InterAssociative : SubtypeHints.

    Fact InterOmega_Left: forall {σ}, σ ~ ω ∩ σ.
    Proof.
      split.
      - apply (transitivity InterIdem).
        apply SubtyDistrib.
        + exact OmegaTop.
        + reflexivity.
      - exact InterMeetRight.
    Defined.
    Hint Resolve InterOmega_Left : SubtypeHints.

    Fact InterOmega_Right: forall {σ}, σ ~ σ ∩ ω.
    Proof.
      split.
      - apply (transitivity InterIdem).
        apply SubtyDistrib.
        + reflexivity.
        + exact OmegaTop.
      - exact InterMeetLeft.
    Defined.
    Hint Resolve InterOmega_Right : SubtypeHints.
    
    Instance Inter_Proper_ST : Proper ((≤) ==> (≤) ==> (≤)) (∩).
    Proof.
      compute.
      intros.
      apply SubtyDistrib; assumption.
    Defined.

    Instance Inter_Proper_EQ : Proper ((~) ==> (~) ==> (~)) (∩).
    Proof.
      compute.
      intros * * p1; inversion p1.
      intros * * p2; inversion p2.
      split; apply Inter_Proper_ST; assumption.
    Defined.
   
    Instance Arr_Proper_ST : Proper (inverse (≤) ==> (≤) ==> (≤)) (→).
    Proof.
      compute.
      intros * * p1.
      intros * * p2.
      apply CoContra; assumption.
    Defined.
    
    Instance Arr_Proper_EQ : Proper ((~) ==> (~) ==> (~)) (→).
    Proof.
      compute.
      intros * * p1; inversion p1.
      intros * * p2; inversion p2.
      split; apply Arr_Proper_ST; assumption.
    Defined.

    Instance Inter_Monoid : Monoid (~) (∩) ω :=
      {| associativity := @InterAssociative;
         identity_left := @InterOmega_Left;
         identity_right := @InterOmega_Right;
         f_proper := Inter_Proper_EQ |}.
    
    Class AbelianMonoid {A} (equiv : relation A) `{Equivalence A equiv} (f : A -> A -> A) (unit : A) :=
      { monoid :> Monoid equiv f unit;
        commutativity : forall x y, equiv (f x y) (f y x) }.

    Fact InterComm_ST: forall { σ τ }, σ ∩ τ ≤ τ ∩ σ.
    Proof.
      intros σ τ.
      apply (transitivity InterIdem).
      apply SubtyDistrib; auto with SubtypeHints.
    Defined.
    Hint Resolve InterComm_ST : SubtypeHints.

    Fact InterComm_EQ: forall σ τ, σ ∩ τ ~ τ ∩ σ.
    Proof.
      intros σ τ.
      split; apply InterComm_ST.
    Defined.
    Hint Resolve InterComm_EQ : SubtypeHints.

    Instance Inter_AbelianMonoid : AbelianMonoid (~) (∩) ω :=
      {| monoid := Inter_Monoid;
         commutativity := InterComm_EQ |}.
    
    Fact Inter_both : forall {σ τ ρ}, σ ≤ τ -> σ ≤ ρ -> σ ≤ τ ∩ ρ.
    Proof.
      intros.
      apply (transitivity InterIdem).
      apply SubtyDistrib; assumption.
    Defined.
    Hint Resolve Inter_both : SubtypeHints.

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
    Defined.
    Hint Resolve Arrow_Tgt_Omega_eq : SubtypeHints.

    Require Import Setoids.Setoid.
    Fact Omega_Inter_Omega_eq {σ ρ : IntersectionType}:
       ω ~ σ -> ω ~ ρ -> ω ~ σ ∩ ρ.
    Proof.
      intros σω ρω.
      rewrite <- σω.
      rewrite <- ρω.
      apply identity_left.
    Defined.
    Hint Resolve Omega_Inter_Omega_eq : SubtypeHints.


    Section BetaLemmas.
      Reserved Notation "↑ω σ" (at level 89).
      Inductive Ω: IntersectionType -> Prop :=
        | OF_Omega : Ω ω
        | OF_Arrow : forall σ ρ, Ω ρ -> Ω (σ → ρ)
        | OF_Inter : forall σ ρ, Ω σ -> Ω ρ -> Ω (σ ∩ ρ)
      where "↑ω σ" := (Ω σ).   
            
      Fact Ω_principal: forall σ, ↑ω σ -> ω ~ σ.
      Proof.
        intros σ ωσ. 
        induction ωσ; auto with SubtypeHints.
      Defined.

      Fact Ω_upperset:
        forall σ τ, σ ≤ τ -> ↑ω σ -> ↑ω τ.
      Proof.
        intros σ τ H.
        induction H; intro Hω; try solve [ inversion Hω; auto ].
        - apply OF_Inter; assumption.
        - inversion Hω as [ | | * * σρω στω ].
          inversion σρω as [ | * * ρω | ].
          inversion στω as [ | * * τω | ].
          exact (OF_Arrow _ _ (OF_Inter _ _ ρω τω)).
        - inversion Hω as [ | | * * ωσ ωτ ].
          exact (OF_Inter _ _ (IHSubtypes1 ωσ) (IHSubtypes2 ωτ)).
        - inversion Hω as [ | * * ωτ | ].
          exact (OF_Arrow _ _ (IHSubtypes2 ωτ)).
        - exact OF_Omega.
        - exact (OF_Arrow _ _ OF_Omega).
        - exact Hω.
      Defined.

      Corollary Ω_principalElement:
        forall σ, ω ≤ σ -> ↑ω σ.
      Proof.
        intros σ ωLEσ.
        exact (Ω_upperset _ _ ωLEσ OF_Omega).
      Defined.
      
      Fact Ω_directed:
        forall σ τ, ↑ω σ -> ↑ω τ -> (↑ω ω) /\ (ω ≤ σ) /\ (ω ≤ τ).
      Proof.
        intros σ τ ωLEσ ωLEτ.
        split; [|split].
        - exact (OF_Omega).
        - exact (Ω_principal _ ωLEσ).
        - exact (Ω_principal _ ωLEτ).
      Defined.

      Fact Var_never_omega:
        forall n, ω ≤ Var n -> False.
      Proof.
        intros n ωLEn.
        set (ωn := Ω_upperset _ _ ωLEn OF_Omega).
        inversion ωn.
      Defined.

      Lemma Beta_Omega:
        forall σ τ, ω ~ σ → τ <-> ω ~ τ.
      Proof.
        intros.
        split.
        - intro στEQω.
          set (στω := Ω_upperset _ _ στEQω OF_Omega).
          inversion στω as [ | * * ωτ | ].
          exact (Ω_principal _ ωτ).
        - exact Arrow_Tgt_Omega_eq.
      Defined.
     
      Reserved Notation "↓α[ n ] σ" (at level 89).
      Inductive VariableIdeal (n : nat): IntersectionType -> Prop :=
        | VI_Var : ↓α[n] (Var n)
        | VI_InterLeft : forall σ τ, ↓α[n] σ -> ↓α[n] σ ∩ τ
        | VI_InterRight : forall σ τ, ↓α[n] τ -> ↓α[n] σ ∩ τ
      where "↓α[ n ] σ" := (VariableIdeal n σ).

      Fact VariableIdeal_principal:
        forall n σ, ↓α[n] σ -> σ ≤ (Var n).
      Proof.
        intros n σ σLEn.
        induction σLEn.
        - reflexivity.
        - transitivity σ.
          + exact InterMeetLeft.
          + assumption.
        - transitivity τ.
          + exact InterMeetRight.
          + assumption.
      Defined.
      
      Fact VariableIdeal_lowerset:
        forall σ τ, σ ≤ τ -> forall n, ↓α[n] τ -> ↓α[n] σ.
      Proof.
        intros σ τ σLEτ.
        induction σLEτ;
          try solve [ intros n H; inversion H ].
        - intro; apply VI_InterLeft.
        - intro; apply VI_InterRight.
        - intros * H; inversion H; assumption.
        - intros * H.
          inversion H.
          + apply (VI_InterLeft).
            apply (IHσLEτ1).
            assumption.
          + apply (VI_InterRight).
            apply (IHσLEτ2).
            assumption.
        - intros; assumption.
        - intros.
          apply (IHσLEτ1).
          apply (IHσLEτ2).
          assumption.
      Defined.
      
      Corollary VariableIdeal_principalElement:
        forall σ n, σ ≤ (Var n) -> ↓α[n] σ.
      Proof.
        intros σ n σLEn.
        exact (VariableIdeal_lowerset _ _ σLEn _ (VI_Var n)).
      Defined.
      
      Fact VariableIdeal_directed:
        forall n σ τ, ↓α[n] σ -> ↓α[n] τ -> (↓α[n] (Var n)) /\ (σ ≤ (Var n)) /\ (τ ≤ (Var n)).
      Proof.
        intros n σ τ σLEn τLEn.
        split; [|split].
        - exact (VI_Var n).
        - exact (VariableIdeal_principal _ _ σLEn).
        - exact (VariableIdeal_principal _ _ τLEn).
      Defined.

      Fact VariableIdeal_prime:
        forall σ τ n, ↓α[n] σ ∩ τ -> (↓α[n] σ) \/ (↓α[n] τ).
      Proof.
        intros σ τ n στLEn.
        inversion στLEn as [ | * * σLEn | * * τLEn ]; auto.
      Defined.
      
      Reserved Notation "↓[ σ ] → [ τ ] ρ" (at level 89).
      Inductive ArrowIdeal (σ τ : IntersectionType): IntersectionType -> Prop :=
        | AI_Omega : forall ρ, ↑ω τ -> ↓[σ] → [τ] ρ
        | AI_Arrow : forall σ' τ', σ ≤ σ' -> τ' ≤ τ -> ↓[σ] → [τ] σ' → τ'
        | AI_InterLeft : forall σ' τ', ↓[σ] → [τ] σ' -> ↓[σ] → [τ] σ' ∩ τ'
        | AI_InterRight : forall σ' τ', ↓[σ] → [τ] τ' -> ↓[σ] → [τ] σ' ∩ τ'
        | AI_Inter : forall σ' τ' ρ1 ρ2,
            ↓[σ] → [ρ1] σ' -> ↓[σ] → [ρ2] τ' -> ρ1 ∩ ρ2 ≤ τ -> ↓[σ] → [τ] σ' ∩ τ'
      where "↓[ σ ] → [ τ ] ρ" := (ArrowIdeal σ τ ρ).

      Hint Resolve AI_Omega AI_Arrow AI_InterLeft AI_InterRight. 

      Fact ArrowIdeal_principal:
        forall σ τ ρ, ↓[σ] → [τ] ρ -> ρ ≤ σ → τ.
      Proof.
        intros σ τ ρ ρLEστ.
        induction ρLEστ as [ | | | | * * ρ1 * ρ2 ].
        - transitivity ω.
          + exact OmegaTop.
          + apply (EqualTypesAreSubtypes_left).
            apply (Ω_principal).
            apply (OF_Arrow).
            assumption.
        - apply (CoContra); assumption.
        - apply (transitivity InterMeetLeft).
          assumption.
        - apply (transitivity InterMeetRight).
          assumption.
        - transitivity ((σ → ρ1) ∩ (σ → ρ2)).
          + apply (SubtyDistrib); assumption.
          + apply (transitivity InterDistrib).
            apply CoContra.
            * reflexivity. 
            * assumption.
      Defined.

      Fact ArrowIdeal_weaken:
        forall σ τ ρ, ↓[σ] → [τ] ρ -> forall τ', τ ≤ τ' -> ↓[σ] → [τ'] ρ.
      Proof.
        intros σ τ ρ ρLEστ.
        induction ρLEστ; intros τ'' τLEτ''.
        - apply AI_Omega.
          apply (Ω_upperset τ); assumption.
        - apply AI_Arrow.
          + assumption.
          + transitivity τ; assumption.
        - apply AI_InterLeft; auto.
        - apply AI_InterRight; auto. 
        - eapply AI_Inter; eauto.
          etransitivity; eassumption.
      Defined.

      Fact ArrowIdeal_comm:
        forall σ τ1 τ2 ρ, ↓[σ] → [τ1 ∩ τ2] ρ -> ↓[σ] → [τ2 ∩ τ1] ρ.
      Proof.
        intros.
        eapply ArrowIdeal_weaken.
        - eassumption.
        - rewrite commutativity.
          reflexivity.
      Defined.

      Fact ArrowIdeal_merge:
        forall σ τ1 τ2 ρ1 ρ2, 
        forall τ τ',
        τ1 ∩ τ2 ≤ τ ∩ τ' ->
        ↓[σ] → [τ1] ρ1 -> ↓[σ] → [τ2] ρ2 ->
        ↓[σ] → [τ ∩ τ'] ρ1 ∩ ρ2.
      Proof.
        intros.
        eapply ArrowIdeal_weaken.
        - eapply AI_Inter.
          + eassumption.
          + eassumption.
          + eassumption.
        - reflexivity.
      Defined.

      Fact ArrowIdeal_InterOmega_left:
        forall σ τ τ' ρ, Ω τ ->  ↓[σ] → [τ'] ρ -> ↓[σ] → [τ ∩ τ'] ρ.
      Proof.
        intros.
        eapply ArrowIdeal_weaken.
        - eassumption.
        - apply Inter_both.
          transitivity ω .
          + exact (OmegaTop).
          + apply EqualTypesAreSubtypes_left.
            apply Ω_principal.
            assumption.
          + reflexivity.
      Defined.

      Fact ArrowIdeal_InterOmega_right:
        forall σ τ τ' ρ, Ω τ ->  ↓[σ] → [τ'] ρ -> ↓[σ] → [τ' ∩ τ] ρ.
      Proof.
        intros.
        apply ArrowIdeal_comm.
        apply ArrowIdeal_InterOmega_left; assumption.
      Defined.


      Fact ArrowIdeal_both:
        forall τ ρ1 ρ2 σ, ↓[σ] → [ρ1] τ -> ↓[σ] → [ρ2] τ -> ↓[σ] → [ρ1 ∩ ρ2] τ.
      Proof.
        intro τ.
        induction τ as [ | | * IH1 * IH2 | * x * y ];
          intros * * * H1 H2;
          inversion H1 as [ | | | | * * * * p1H1 p2H1 ];
          inversion H2 as [ | | | | * * * * p1H2 p2H2 ];
          try solve [
            apply AI_Omega; apply OF_Inter; assumption
            | apply ArrowIdeal_InterOmega_left; assumption
            | apply ArrowIdeal_InterOmega_right; assumption
            | apply AI_Arrow; auto with SubtypeHints
            | apply AI_InterLeft; auto with SubtypeHints
            | apply AI_InterRight; auto with SubtypeHints ];
          first [ eapply AI_Inter; 
            [ solve [ eauto with SubtypeHints ] |
              solve [ eauto with SubtypeHints ] |
              solve [ eauto with SubtypeHints ] ] || idtac ] .
        - eapply ArrowIdeal_merge.
          rewrite associativity.
          eapply SubtyDistrib.
          + reflexivity.
          + eassumption.
          + eauto.
          + assumption.
        - eapply ArrowIdeal_comm.
          eapply ArrowIdeal_merge.
          rewrite <- associativity.
          eapply SubtyDistrib.
          + eassumption.
          + reflexivity.
          + assumption.
          + eauto.
        - eapply ArrowIdeal_comm.
          eapply ArrowIdeal_merge.
          rewrite associativity.
          eapply SubtyDistrib.
          + reflexivity.
          + eassumption.
          + eauto.
          + assumption.
        - eapply ArrowIdeal_merge.
          rewrite <- associativity.
          eapply SubtyDistrib.
          + eassumption.
          + reflexivity.
          + assumption.
          + eauto.
        - eapply AI_Inter.
          + eapply IH1.
            * exact p1H1.
            * exact p1H2.
          + eapply IH2.
            * exact p2H1.
            * exact p2H2. 
          + apply (transitivity InterIdem).
            apply SubtyDistrib.
            * rewrite <- associativity.
              apply (transitivity InterMeetLeft).
              rewrite commutativity.
              rewrite <- associativity.
              apply (transitivity InterMeetLeft).
              rewrite commutativity.
              assumption.
            * rewrite <- associativity.
              rewrite commutativity.
              rewrite <- associativity.
              apply (transitivity InterMeetLeft).
              rewrite commutativity.
              rewrite associativity.
              apply (transitivity InterMeetRight).
              assumption.
      Defined.

      Fact ArrowIdeal_lowerset:
        forall ρ1 ρ2, ρ1 ≤ ρ2 -> forall σ τ, ↓[σ] → [τ] ρ2 -> ↓[σ] → [τ] ρ1.
      Proof.
        intros ρ1 ρ2 ρ1LEρ2.
        induction ρ1LEρ2; 
          try solve [ auto ];
          intros σ'' τ'' H;
          inversion H;
          auto.
        - eapply ArrowIdeal_weaken; [|eassumption].
          eapply ArrowIdeal_both; eassumption.
        - apply (AI_Inter _ _ _ _ ρ τ).
          + exact (AI_Arrow _ _ _ _ H2 (reflexivity ρ)).
          + exact (AI_Arrow _ _ _ _ H2 (reflexivity τ)). 
          + exact H3.
        - apply (AI_Inter _ _ _ _ ρ1 ρ2).
          + exact (IHρ1LEρ2_1 _ _ H2).
          + exact (IHρ1LEρ2_2 _ _ H3).
          + exact H4.
        - apply AI_Arrow.
          + exact (transitivity H2 ρ1LEρ2_1).
          + exact (transitivity ρ1LEρ2_2 H3).
        - set (ωτ := Ω_upperset _ _ H3 OF_Omega).
          auto.
      Defined.
      
      Corollary ArrowIdeal_principalElement:
        forall ρ σ τ, ρ ≤ σ → τ -> ↓[σ] → [τ] ρ.
      Proof.
        intros ρ σ τ ρLEστ.
        exact (ArrowIdeal_lowerset _ _ ρLEστ _ _ 
          (AI_Arrow _ _ _ _ (reflexivity σ) (reflexivity τ))).
      Defined.
      
      Fact ArrowIdeal_directed:
        forall ρ1 ρ2 σ τ, ↓[σ] → [τ] ρ1 -> ↓[σ] → [τ] ρ2 ->
        (↓[σ] → [τ] σ → τ) /\ (ρ1 ≤ σ → τ) /\ (ρ2 ≤ σ → τ).
      Proof.
        intros ρ1 ρ2 σ τ ρ1LEστ ρ2LEστ.
        split; [|split].
        - exact (AI_Arrow _ _ _ _ (reflexivity σ) (reflexivity τ)).
        - exact (ArrowIdeal_principal _ _ _ ρ1LEστ).
        - exact (ArrowIdeal_principal _ _ _ ρ2LEστ).
      Defined.

      Fact ArrowIdeal_prime:
        forall ρ1 ρ2 σ τ,
          ↓[σ] → [τ] ρ1 ∩ ρ2 ->
          (((↓[σ] → [τ] ρ1) \/ (ρ2 ≤ ρ1)) \/
           ((↓[σ] → [τ] ρ2) \/ (ρ1 ≤ ρ2)) <->
           (↓[σ] → [τ] ρ1) \/ (↓[σ] → [τ] ρ2)).
      Proof.
        intros ρ1 ρ2 σ τ ρ1ρ2LEστ.
        split.
        - intros ρ1ORρ2.
          destruct ρ1ORρ2 as [ [ ρ1LEστ | ρ2LEρ1 ] | [ ρ2LEστ | ρ1LEρ2 ] ];
            inversion ρ1ρ2LEστ;
            auto.
          + right.
            apply (ArrowIdeal_lowerset ρ2 (ρ1 ∩ ρ2)).
            * apply (transitivity InterIdem).
              apply SubtyDistrib.
              { exact ρ2LEρ1. }
              { reflexivity. }
            * exact ρ1ρ2LEστ.
          + left.
            apply (ArrowIdeal_lowerset ρ1 (ρ1 ∩ ρ2)).
            * apply (transitivity InterIdem).
              apply SubtyDistrib.
              { reflexivity. }
              { exact ρ1LEρ2. }
            * exact ρ1ρ2LEστ.
        - intro primality.
          destruct primality as [ ρ1LEστ | ρ2LEστ ].
          + left; auto.
          + right; auto.
      Defined.
      
      Reserved Notation "↓[ σ ] τ" (at level 89).
      Fixpoint Ideal σ: IntersectionType -> Prop :=
        match σ with
          | ω => fun _ => Ω ω
          | Var n => fun τ => ↓α[n] τ
          | σ' → τ' => fun τ => ↓[σ'] → [τ'] τ
          | σ' ∩ τ' => fun τ => (↓[σ'] τ) /\ (↓[τ'] τ)
        end
      where "↓[ σ ] τ" := (Ideal σ τ).

      Definition Filter σ: IntersectionType -> Prop :=
        match σ with
          | ω => Ω
          | _ => fun τ => ↓[τ] σ
        end.
      Notation "↑[ σ ] τ" := (Filter σ τ) (at level 89).
      
      Notation "↑α[ n ] σ " := (↑[Var n] σ) (at level 89).
      Notation "↑[ σ ] → [ τ ] ρ" := (↑[σ → τ] ρ) (at level 89).
      
      Lemma Filter_Ideal:
        forall σ τ, ↑[σ] τ -> ↓[τ] σ.
      Proof.
        intro σ.
        induction σ;
          intro τ;
          induction τ;
          try solve [ trivial ];
          intro σLEτ;
          inversion σLEτ.
        - apply AI_Omega.
          assumption.
        - split.
          + apply IHτ1.
            assumption.
          + apply IHτ2.
            assumption.
      Defined.

      Lemma Ideal_Filter:
        forall σ τ, ↓[σ] τ -> ↑[τ] σ.
      Proof.
        intro σ.
        induction σ;
          intro τ;
          induction τ;
          try solve [ trivial ];
          intro τLEσ;
          inversion τLEσ.
        - apply OF_Arrow.
          assumption.
        - apply OF_Inter.
          + apply (IHσ1 ω).
            assumption.
          + apply (IHσ2 ω).
            assumption.
      Defined.

      Lemma Ideal_principal:
        forall σ τ, ↓[σ] τ -> τ ≤ σ.
      Proof.
        induction σ.
        - exact (VariableIdeal_principal _).
        - exact (ArrowIdeal_principal _ _).
        - intros τ τLEσ1σ2.
          destruct τLEσ1σ2 as [ τLEσ1 τLEσ2 ].
          apply (transitivity InterIdem).
          apply SubtyDistrib; auto.
        - intros; exact OmegaTop.
      Defined.      

      Lemma Filter_principal:
        forall σ τ, ↑[σ] τ -> σ ≤ τ.
      Proof.
        intros.
        apply Ideal_principal.
        apply Filter_Ideal.
        assumption.
      Defined.

      Lemma Ideal_lowerset:
        forall ρ1 ρ2, ρ1 ≤ ρ2 -> forall σ, ↓[σ] ρ2 -> ↓[σ] ρ1.
      Proof.
        intros ρ1 ρ2 ρ1LEρ2 σ.
        induction σ.
        - exact (VariableIdeal_lowerset _ _ ρ1LEρ2 _).
        - exact (ArrowIdeal_lowerset _ _ ρ1LEρ2 _ _).
        - intro ρ2LEσ1σ2.
          destruct ρ2LEσ1σ2 as [ ρ2LEσ1 ρ2LEσ2 ].
          split; auto.
        - trivial.
      Defined.

      Lemma Ideal_refl:
        forall σ, ↓[σ] σ.
      Proof.
        induction σ.
        - exact (VI_Var _).
        - exact (AI_Arrow _ _ _ _ (reflexivity _) (reflexivity _)).
        - split.
          + apply (Ideal_lowerset _ σ1); auto with SubtypeHints.
          + apply (Ideal_lowerset _ σ2); auto with SubtypeHints.
        - exact (OF_Omega).
      Defined.
      
      Instance Ideal_Reflexive : Reflexive Ideal := Ideal_refl.

      Lemma Filter_upperset:
        forall ρ1 ρ2, ρ1 ≤ ρ2 -> forall σ, ↑[σ] ρ1 -> ↑[σ] ρ2.
      Proof.
        intros.
        apply Ideal_Filter.
        apply (Ideal_lowerset _ ρ1).
        - apply Filter_principal.
          assumption.
        - apply (Ideal_lowerset _ ρ2).
          + assumption.
          + reflexivity.
      Defined.
 
      Lemma Filter_refl:
        forall σ, ↑[σ] σ.
      Proof.
        intros.
        apply Ideal_Filter.
        reflexivity.
      Defined.

      Instance Filter_Reflexive : Reflexive Filter := Filter_refl.

      Lemma Ideal_transitive:
        forall σ τ ρ, ↓[σ] τ -> ↓[τ] ρ -> ↓[σ] ρ.
      Proof.
        intros σ τ ρ στ τρ.
        apply (Ideal_lowerset ρ σ).
        - transitivity τ;
            apply Ideal_principal;
            assumption.
        - reflexivity.
      Defined.

      Instance Ideal_Transitive : Transitive Ideal := Ideal_transitive.  

      Lemma Filter_transitive:
        forall σ τ ρ, ↑[σ] τ -> ↑[τ] ρ -> ↑[σ] ρ.
      Proof.
        intros σ τ ρ στ τρ.
        apply Ideal_Filter.
        transitivity τ;
          apply Filter_Ideal; assumption.
      Defined.

      Instance Filter_Transitive : Transitive Filter := Filter_transitive.

      Lemma Ideal_principalElement:
        forall σ τ, τ ≤ σ -> ↓[σ] τ.
      Proof.
        intro σ.
        induction σ.
        - intro.
          exact (VariableIdeal_principalElement _ _).
        - intro.
          exact (ArrowIdeal_principalElement _ _ _).
        - intros τ τLEσ1σ2.
          split; [ apply IHσ1 | apply IHσ2 ];
            transitivity (σ1 ∩ σ2); auto with SubtypeHints.
        - intros.
          exact OF_Omega.
      Defined.

      Lemma Filter_principalElement:
        forall σ τ, σ ≤ τ -> ↑[σ] τ.
      Proof.
        intros.
        apply Ideal_Filter.
        apply Ideal_principalElement.
        assumption.
      Defined.

      Require Import Logic.Decidable.
      Fact Ω_decidable: forall τ, decidable (Ω τ).
      Proof.
        intro τ.
        induction τ.
        - right.
          unfold not.
          intro ωτ.
          inversion ωτ.
        - inversion IHτ2.
          + left.
            apply OF_Arrow.
            assumption.
          + right.
            intro ωτ1τ2.
            inversion ωτ1τ2.
            contradiction.
        - inversion IHτ1; inversion IHτ2;
            solve [ left; apply OF_Inter; assumption
                  | right; intro ωτ1τ2; inversion ωτ1τ2; contradiction ].
        - left; exact OF_Omega.
      Defined.

      Fact ΩIdeal_decidable: forall σ, decidable (↓[ω] σ).
      Proof.
        intros.
        left.
        simpl.
        exact OF_Omega.
      Defined.
      (*
      Fact Ideal_decidable_Filter_decidable:
        forall τ, (forall σ, decidable (↓[σ] τ)) -> forall σ, decidable (↑[σ] τ).
      Proof.
        intros τ στ_dec σ.
        set (στ := στ_dec σ).
        induction σ.
        - inversion στ; left. simpl. inversion H. reflexivity.
        - inversion H.
        - inversion H.*)

      Lemma VariableIdeal_decidable: forall n τ, decidable (↓α[n] τ).
      Proof.
        intros n τ.
        induction τ;
          try solve [ right; intro τLEσ; inversion τLEσ ].
        - assert (varEq : {n = n0} + {~n = n0}).
          * decide equality.
          * inversion varEq as [ equal | notEqual ].
            { rewrite equal. left. fold (Ideal (Var n0) (Var n0)). reflexivity. }
            { right. unfold not. intro n0LEn. inversion n0LEn. contradiction. }
        - inversion IHτ1; inversion IHτ2;
            try solve [ left; apply VI_InterLeft; assumption
                  | left; apply VI_InterRight; assumption
                  | right; unfold not; intro τLEσ; inversion τLEσ; contradiction ].
      Defined.

      Lemma VariableFilter_decidable: forall n τ, decidable (↑α[n] τ).
      Proof.
        intros n τ.
        induction τ.
        - assert (varEq : {n0 = n} + {~n0 = n}).
          * decide equality.
          * inversion varEq as [ equal | notEqual ].
            { rewrite equal. left. fold (Ideal (Var n0) (Var n0)). reflexivity. }
            { right. unfold not. intro nLEn0. inversion nLEn0. contradiction. }
        - destruct (Ω_decidable τ2).
          + left. simpl. apply AI_Omega. assumption.
          + right. unfold not. intro nLEτ1τ2. inversion nLEτ1τ2. contradiction.
        - inversion IHτ1; inversion IHτ2;
            solve [ left; split; assumption
                  | right; unfold not; intros nLEτ1τ2; inversion nLEτ1τ2; contradiction ].
        - simpl. exact (ΩIdeal_decidable (Var n)).
      Defined.
      
      Fixpoint ty_size σ : nat :=
        match σ with
          | Var _ => 1
          | σ' → τ => ty_size σ' + ty_size τ
          | ρ1 ∩ ρ2 => ty_size ρ1 + ty_size ρ2
          | ω => 1
        end.

      Definition ty_pair_size στ : nat :=
        ty_size (fst στ) + ty_size (snd στ).

      Require Import Arith.Wf_nat.
      Fact ty_pair_size_wf: 
        well_founded (fun στ σ'τ' => ty_pair_size στ < ty_pair_size σ'τ').
      Proof.
        apply well_founded_ltof.
      Defined.
       
      Require Import Arith_base.
      Require Import NArith.
      Require Import NZAddOrder.
      Fact ty_size_positive:
        forall σ, ty_size σ >= 1.
      Proof.
        induction σ;
          simpl;
          try solve [ auto ];
          apply le_plus_trans;
          assumption.
      Defined.

      Fact ty_pair_size_dec_any:
        forall σ τ σ' τ',
        (ty_size σ < ty_size σ' /\ ty_size τ <= ty_size τ') +
        (ty_size τ < ty_size τ' /\ ty_size σ <= ty_size σ') ->
        ty_pair_size (σ, τ) < ty_pair_size (σ', τ').
      Proof.
        intros σ τ σ' τ' lt_le_p.
        destruct lt_le_p as [ [σLTσ' τLEτ'] | [τLTτ' σLEσ'] ].
        - apply plus_lt_le_compat; assumption.
        - apply plus_le_lt_compat; assumption.
      Defined.

      Fact ty_pair_size_dec_fst:
        forall σ τ σ' τ',
        (ty_size σ < ty_size σ' /\ ty_size τ <= ty_size τ') ->
        ty_pair_size (σ, τ) < ty_pair_size (σ', τ').
      Proof.
        intros.
        apply ty_pair_size_dec_any.
        left.
        assumption.
      Defined.

      Fact ty_pair_size_dec_snd:
        forall σ τ σ' τ',
        (ty_size τ < ty_size τ' /\ ty_size σ <= ty_size σ') ->
        ty_pair_size (σ, τ) < ty_pair_size (σ', τ').
      Proof.
        intros.
        apply ty_pair_size_dec_any.
        right.
        assumption.
      Defined.

      Fact ty_size_drop_tgt:
        forall σ τ,
        ty_size σ < ty_size (σ → τ).
      Proof.
        intros.
        simpl.
        rewrite <- plus_0_r at 1.
        apply plus_le_lt_compat.
        - reflexivity.
        - apply ty_size_positive.
      Defined.

      Fact ty_size_drop_src:
        forall σ τ,
        ty_size τ < ty_size (σ → τ).
      Proof.
        intros.
        simpl.
        rewrite <- plus_0_l at 1.
        apply plus_lt_le_compat.
        - apply ty_size_positive.
        - reflexivity.
      Defined.

      Fact ty_size_drop_left:
        forall σ τ,
        ty_size σ < ty_size (σ ∩ τ).
      Proof.
        intros.
        simpl.
        rewrite <- plus_0_r at 1.
        apply plus_le_lt_compat.
        - reflexivity.
        - apply ty_size_positive.
      Defined.

      Fact ty_size_drop_right:
        forall σ τ,
        ty_size τ < ty_size (σ ∩ τ).
      Proof.
        intros.
        simpl.
        rewrite <- plus_0_l at 1.
        apply plus_lt_le_compat.
        - apply ty_size_positive.
        - reflexivity.
      Defined.

      Fact ty_pair_size_comm:
        forall σ τ,
        ty_pair_size (σ, τ) = ty_pair_size (τ, σ).
      Proof.
        intros.
        unfold ty_pair_size.
        simpl.
        rewrite plus_comm.
        reflexivity.
      Defined.
     
      
      Fact ty_pair_size_dec_tgt:
        forall σ τ σ' τ',
        ty_pair_size (τ, τ') < ty_pair_size ((σ → τ), (σ' → τ')).
      Proof.
        intros.
        apply ty_pair_size_dec_fst.
        split.
        - apply ty_size_drop_src.
        - apply (transitivity (le_n_Sn _)).
          apply ty_size_drop_src.
      Defined.
      
      Fact ty_pair_size_dec_src:
        forall σ τ σ' τ',
        ty_pair_size (σ', σ) < ty_pair_size ((σ → τ), (σ' → τ')).
      Proof.
        intros.
        rewrite ty_pair_size_comm.
        apply ty_pair_size_dec_fst.
        split.
        - apply ty_size_drop_tgt.
        - apply (transitivity (le_n_Sn _)).
          apply ty_size_drop_tgt.
      Defined.
      

      Fact Pick_Ideal σ ρ (decσ : forall σ', ty_pair_size (σ, σ') < ty_pair_size (σ, ρ) -> decidable (↑[σ] σ')):
        exists τ, (↓[σ] → [τ] ρ) /\ (forall τ', ↓[σ] → [τ'] ρ -> τ ≤ τ') /\ ty_size τ <= ty_size ρ.
      Proof.
        induction ρ as [ | σ' _ τ' _ | | ].
        - exists ω.
          split; [|split].
          + apply AI_Omega.
            exact OF_Omega.
          + intros τ' nLEτ'.
            inversion nLEτ'.
            apply Filter_principal.
            assumption.
          + reflexivity.
        - case (decσ σ').
          + apply ty_pair_size_dec_snd.
            split.
            * apply ty_size_drop_tgt.
            * reflexivity.
          + intro σLEσ'.
            exists τ'.
            split; [|split].
            * apply AI_Arrow.
              { apply Filter_principal; assumption. }
              { reflexivity. }
            * intros τ1 σ'τ'LEστ1.
              inversion σ'τ'LEστ1.
              { transitivity ω.
                - exact OmegaTop.
                - apply Filter_principal.
                  assumption. }
              { assumption. }
            * apply (transitivity (le_n_Sn _)).
              apply ty_size_drop_src.
          + intro σNLEσ'.
            exists ω.
            split; [|split].
            * apply AI_Omega.
              exact OF_Omega.
            * intros τ1 σ'τ'LEστ1.
              inversion σ'τ'LEστ1.
              { apply Filter_principal. assumption. }
              { contradict σNLEσ'.
                apply Filter_principalElement.
                assumption. }
            * apply ty_size_positive.
        - assert (decσρ1 :forall σ' : IntersectionType,
            ty_pair_size (σ, σ') < ty_pair_size (σ, ρ1) -> decidable (↑[σ]σ')).
          { intros σ' leP.
            apply decσ.
            transitivity (ty_pair_size (σ, ρ1)).
            - assumption.
            - apply ty_pair_size_dec_snd.
              split.
              + apply ty_size_drop_left.
              + reflexivity. }
          destruct (IHρ1 decσρ1) as [ τ1 [ ρ1LEστ1 τ1_min ] ].
          assert (decσρ2 :forall σ' : IntersectionType,
            ty_pair_size (σ, σ') < ty_pair_size (σ, ρ2) -> decidable (↑[σ]σ')).
          { intros σ' leP.
            apply decσ.
            transitivity (ty_pair_size (σ, ρ2)).
            - assumption.
            - apply ty_pair_size_dec_snd.
              split.
              + apply ty_size_drop_right.
              + reflexivity. }
          destruct (IHρ2 decσρ2) as [ τ2 [ ρ2LEστ2 τ2_min ] ].
          exists (τ1 ∩ τ2).
          split; [|split].
          + apply (AI_Inter _ _ _ _ τ1 τ2).
            * assumption.
            * assumption. 
            * reflexivity.
          + intros τ' ρ1ρ2LEστ'.
            inversion ρ1ρ2LEστ'.
            * transitivity ω.
              { exact OmegaTop. }
              { apply Filter_principal.
                assumption. }
            * apply (transitivity InterMeetLeft).
              apply τ1_min.
              assumption.
            * apply (transitivity InterMeetRight).
              apply τ2_min.
              assumption.
            * transitivity (ρ0 ∩ ρ3).
              { apply (SubtyDistrib).
                - apply τ1_min.
                  assumption.
                - apply τ2_min.
                  assumption. }
              { assumption. }
          + simpl.
            apply plus_le_compat.
            * exact (proj2 τ1_min).
            * exact (proj2 τ2_min).            
        - exists ω.
          split; [|split].
          + apply AI_Omega.
            exact OF_Omega.
          + intros τ' ωLEστ'.
            inversion ωLEστ'.
            apply Filter_principal.
            assumption.
          + reflexivity.
      Defined.

      Definition Ideal_decidable': 
        forall στ
          (Ideal_decidable'':
            forall σ'τ',
            (ty_pair_size σ'τ' < ty_pair_size στ) ->
            decidable (↓[fst σ'τ'] (snd σ'τ'))), decidable (↓[fst στ] (snd στ)).
      Proof.
        intros [ σ τ Ideal_decidable''].
        case σ as [ | σ' τ' | ρ1 ρ2 | ] eqn:σeq.
        - apply VariableIdeal_decidable.
        - case τ as [ | σ'' τ'' | ρ1 ρ2 | ].
          + case (Ω_decidable τ').
            * intro ωτ'.
              left.
              apply (AI_Omega).
              assumption.
            * intros.
              right.
              unfold not.
              intro nLEσ'τ'.
              inversion nLEσ'τ'.
              contradiction.
          + case (Ideal_decidable'' (τ', τ'')).
            * apply ty_pair_size_dec_tgt.
            * intro τ''LEτ'.
              case (Ideal_decidable'' (σ'', σ') (ty_pair_size_dec_src σ' τ' σ'' τ'')).
              { intro σ'LEσ''.
                left.
                apply (AI_Arrow).
                - apply (Filter_principal).
                  apply (Ideal_Filter).
                  assumption.
                - apply (Ideal_principal).
                  assumption. }
              { intro σ'NLEσ''.
                case (Ω_decidable τ').
                - intro ωτ'.
                  left.
                  apply (AI_Omega).
                  assumption.
                - intros.
                  right.
                  unfold not.
                  intro σ''τ''LEσ'τ'.
                  inversion σ''τ''LEσ'τ'.
                  + contradiction.
                  + contradict σ'NLEσ''.
                    apply Filter_Ideal.
                    apply (Filter_principalElement).
                    assumption. }
            * intro τ''NLEτ'.
              right.
              unfold not.
              intro σ''τ''LEσ'τ'.
              inversion σ''τ''LEσ'τ'.
              { contradict τ''NLEτ'.
                apply (Ideal_principalElement).
                transitivity ω.
                - exact OmegaTop.
                - apply (Filter_principal).
                  assumption. }
              { contradict τ''NLEτ'.
                apply (Ideal_principalElement).
                assumption. }
          + case (Ω_decidable τ').
            * left.
              apply (AI_Omega).
              assumption.
            * assert (Pick_Ideal_Ideal_decidable : forall τ,
                ty_pair_size (σ', τ) < ty_pair_size (σ', ρ1 ∩ ρ2) ->
                decidable (↑[σ']τ)).
              { intros τ ltP.
                case σ' as [ | σ'' τ'' | ρ1' ρ2' | ]; 
                  intros;
                  try solve [ apply Ω_decidable
                            | apply VariableFilter_decidable ].
                - simpl.
                  apply (Ideal_decidable'' (τ, σ'' → τ'')).
                  rewrite (ty_pair_size_comm).
                  apply (transitivity ltP).
                  apply ty_pair_size_dec_fst.
                  split.
                  + apply ty_size_drop_tgt.
                  + reflexivity.
                - simpl.
                  apply (Ideal_decidable'' (τ, ρ1' ∩ ρ2')).
                  rewrite (ty_pair_size_comm).
                  apply (transitivity ltP).
                  apply ty_pair_size_dec_fst.
                  split.
                  + apply ty_size_drop_tgt.
                  + reflexivity. }
              case (Pick_Ideal σ' (ρ1 ∩ ρ2) (Pick_Ideal_Ideal_decidable)).
              intros τ_min [ aiρ1 aiρ1ρ2_min ] ωNLEτ'.
              case (Ideal_decidable'' (τ', τ_min)).
              { apply ty_pair_size_dec_fst.
                split.
                + apply ty_size_drop_src.
                + apply (proj2 aiρ1ρ2_min). }
              { left.
                apply (ArrowIdeal_weaken σ' τ_min).
                + assumption.
                + apply Ideal_principal.
                  assumption. }
              { intro τ_minNLEτ'.
                right.
                unfold not.
                intro ρ1ρ2LEσ'τ'.
                inversion ρ1ρ2LEσ'τ';
                  try solve [ contradiction ];
                  contradict τ_minNLEτ';
                  apply Ideal_principalElement;
                  apply aiρ1ρ2_min.
                + apply AI_InterLeft.
                  assumption.
                + apply AI_InterRight.
                  assumption.
                + eapply AI_Inter; eassumption. }
          + case (Ω_decidable τ').
            * left.
              apply AI_Omega.
              assumption.
            * right.
              unfold not.
              intro ωLEσ'τ'.
              inversion ωLEσ'τ'.
              contradiction.
        - case (Ideal_decidable'' (ρ1, τ)).
          + apply ty_pair_size_dec_fst.
            split.
            * apply ty_size_drop_left.
            * reflexivity. 
          + simpl.
            case (Ideal_decidable'' (ρ2, τ)).
            { apply ty_pair_size_dec_fst.
              split.
              - apply ty_size_drop_right.
              - reflexivity. }
            { intros.
              left.
              split; assumption. }
            { right.
              unfold not.
              intros [ τLEρ1 τLEρ2 ].
              contradiction. }
          + right.
            unfold not.
            intros [ τLEρ1 τLEρ2 ].
            contradiction.
        - left.
          simpl.
          exact OF_Omega.
      Defined.

      Lemma Ideal_decidable:
        forall σ τ, decidable (↓[σ] τ).
      Proof.
        intros σ τ.
        exact (Fix ty_pair_size_wf _ Ideal_decidable' (σ, τ)).
      Defined.

      Lemma Filter_decidable:
        forall σ τ, decidable (↑[σ] τ).
      Proof.
        intro σ.
        case σ;
         solve [ intros; apply Ideal_decidable
               | intros; apply Ω_decidable ].
      Defined.

      Corollary Subtype_decidable:
        forall σ τ, decidable (σ ≤ τ).
      Proof.
        intros.
        case (Ideal_decidable τ σ).
        - intros.
          left.
          apply Ideal_principal.
          assumption.
        - intros σLEτ.
          right.
          unfold not.
          intros.
          contradict σLEτ.
          apply Ideal_principalElement.
          assumption.
      Defined.
    End BetaLemmas.

    Definition α := (Var 1).
    Definition β := (Var 2).
    Definition γ := (Var 3).
    Definition δ := (Var 4).
    Eval compute in Subtype_decidable (((α → β) → δ) ∩ ((α → γ) → δ)) ((α → δ) → δ).
  End SubtypeRelation.


End Types.
