
Require Import Coq.Structures.Equalities.
Module Type SetTyp <: Typ.
  Parameter t : Set.
End SetTyp.
Module Type VariableAlphabet <: UsualDecidableType := 
  SetTyp <+ HasUsualEq <+ UsualIsEq <+ HasEqDec.

Require Import Coq.Structures.Orders.
Module Type OrderedVariableAlphabet <: UsualOrderedType :=
  VariableAlphabet <+ HasLt <+ IsStrOrder <+ HasCompare.

 
Module Types (VAlpha : VariableAlphabet).
  Definition 𝕍 := VAlpha.t.
  Definition 𝕍_eq_dec: forall α β : 𝕍, { α = β } + { α <> β } := VAlpha.eq_dec.

  Local Hint Resolve 𝕍_eq_dec.

  Inductive IntersectionType : Set :=
  | Var : 𝕍 -> IntersectionType
  | Arr : IntersectionType -> IntersectionType -> IntersectionType
  | Inter : IntersectionType -> IntersectionType -> IntersectionType
  | Omega : IntersectionType.

  Lemma IntersectionType_eq_dec: forall σ τ : IntersectionType, { σ = τ } + { σ <> τ }.
  Proof.
    intros σ τ.
    compare σ τ; auto.
  Defined.

  Hint Resolve IntersectionType_eq_dec.

  Infix "→" := (Arr) (at level 88, right associativity).
  Notation "(→)" := Arr (only parsing).
  Infix "∩" := (Inter) (at level 80, right associativity).
  Notation "(∩)" := (Inter) (only parsing).
  Definition ω := (Omega).

  Module SubtypeRelation.
    Reserved Infix "≤" (at level 89).
    Reserved Infix "~=" (at level 89).
    
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
    | InducedEq {σ τ}: σ ≤ τ -> τ ≤ σ -> σ ~= τ
    where "σ ~= τ" := (EqualTypes σ τ).
    Notation "(~=)" := (EqualTypes) (only parsing).

    Definition EqualTypesAreSubtypes_left: forall σ τ, σ ~= τ -> σ ≤ τ :=
      fun _ _ eqtys =>
        match eqtys with
        | InducedEq _ _ l _ => l
        end.
    Definition EqualTypesAreSubtypes_right: forall σ τ, σ ~= τ -> τ ≤ σ :=
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
    Hint Resolve Subtypes_Reflexive: SubtypeHints.
    Instance Subtypes_Transitive : Transitive (≤) := 
      fun σ τ ρ p1 p2 => ST _ _ ((clos_rt_is_preorder _ _).(preord_trans _ _) σ τ ρ (unST _ _ p1) (unST _ _ p2)).
    Instance Subtypes_Preorder : PreOrder (≤) :=
      {| PreOrder_Reflexive := Subtypes_Reflexive; 
         PreOrder_Transitive := Subtypes_Transitive |}.

    Instance EqualTypes_Reflexive: Reflexive (~=) :=
      fun σ => InducedEq (reflexivity σ) (reflexivity σ).
    Instance EqualTypes_Transitive: Transitive (~=).
    Proof.
      unfold Transitive.
      intros σ τ ρ p1 p2.
      inversion p1.
      inversion p2.
      split; transitivity τ; assumption.
    Defined.
    Instance EqualTypes_Symmetric: Symmetric (~=).
    Proof.
      unfold Symmetric.
      intros σ τ p.
      inversion p.
      apply InducedEq; assumption.
    Defined.
    Instance EqualTypes_Equivalence: Equivalence (~=) :=
      {| Equivalence_Reflexive := EqualTypes_Reflexive;
         Equivalence_Transitive := EqualTypes_Transitive;
         Equivalence_Symmetric := EqualTypes_Symmetric |}.

    Instance Subtypes_PartialOrder : PartialOrder (~=) (≤).
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

    Fact InterAssociative: forall { σ τ ρ }, (σ ∩ τ) ∩ ρ ~= σ ∩ τ ∩ ρ.
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

    Fact InterOmega_Left: forall {σ}, σ ~= ω ∩ σ.
    Proof.
      split.
      - apply (transitivity InterIdem).
        apply SubtyDistrib.
        + exact OmegaTop.
        + reflexivity.
      - exact InterMeetRight.
    Defined.
    Hint Resolve InterOmega_Left : SubtypeHints.

    Fact InterOmega_Right: forall {σ}, σ ~= σ ∩ ω.
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

    Instance Inter_Proper_EQ : Proper ((~=) ==> (~=) ==> (~=)) (∩).
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
    
    Instance Arr_Proper_EQ : Proper ((~=) ==> (~=) ==> (~=)) (→).
    Proof.
      compute.
      intros * * p1; inversion p1.
      intros * * p2; inversion p2.
      split; apply Arr_Proper_ST; assumption.
    Defined.

    Instance Inter_Monoid : Monoid (~=) (∩) ω :=
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

    Fact InterComm_EQ: forall σ τ, σ ∩ τ ~= τ ∩ σ.
    Proof.
      intros σ τ.
      split; apply InterComm_ST.
    Defined.
    Hint Resolve InterComm_EQ : SubtypeHints.

    Instance Inter_AbelianMonoid : AbelianMonoid (~=) (∩) ω :=
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
      ω ~= ρ -> ω ~= σ → ρ.
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
       ω ~= σ -> ω ~= ρ -> ω ~= σ ∩ ρ.
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
            
      Fact Ω_principal: forall σ, ↑ω σ -> ω ~= σ.
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
        forall σ τ, ω ~= σ → τ <-> ω ~= τ.
      Proof.
        intros.
        split.
        - intro στEQω.
          set (στω := Ω_upperset _ _ στEQω OF_Omega).
          inversion στω as [ | * * ωτ | ].
          exact (Ω_principal _ ωτ).
        - exact Arrow_Tgt_Omega_eq.
      Defined.
     
      Reserved Notation "↓α[ α ] σ" (at level 89).
      Inductive VariableIdeal (α : 𝕍): IntersectionType -> Prop :=
        | VI_Var : ↓α[α] (Var α)
        | VI_InterLeft : forall σ τ, ↓α[α] σ -> ↓α[α] σ ∩ τ
        | VI_InterRight : forall σ τ, ↓α[α] τ -> ↓α[α] σ ∩ τ
      where "↓α[ α ] σ" := (VariableIdeal α σ).

      Fact VariableIdeal_principal:
        forall α σ, ↓α[α] σ -> σ ≤ (Var α).
      Proof.
        intros α σ σLEα.
        induction σLEα.
        - reflexivity.
        - transitivity σ.
          + exact InterMeetLeft.
          + assumption.
        - transitivity τ.
          + exact InterMeetRight.
          + assumption.
      Defined.
      
      Fact VariableIdeal_lowerset:
        forall σ τ, σ ≤ τ -> forall α, ↓α[α] τ -> ↓α[α] σ.
      Proof.
        intros σ τ σLEτ.
        induction σLEτ;
          try solve [ intros α H; inversion H ].
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
        forall σ α, σ ≤ (Var α) -> ↓α[α] σ.
      Proof.
        intros σ α σLEα.
        exact (VariableIdeal_lowerset _ _ σLEα _ (VI_Var α)).
      Defined.
      
      Fact VariableIdeal_directed:
        forall α σ τ, ↓α[α] σ -> ↓α[α] τ -> (↓α[α] (Var α)) /\ (σ ≤ (Var α)) /\ (τ ≤ (Var α)).
      Proof.
        intros α σ τ σLEα τLEα.
        split; [|split].
        - exact (VI_Var α).
        - exact (VariableIdeal_principal _ _ σLEα).
        - exact (VariableIdeal_principal _ _ τLEα).
      Defined.

      Fact VariableIdeal_prime:
        forall σ τ α, ↓α[α] σ ∩ τ -> (↓α[α] σ) \/ (↓α[α] τ).
      Proof.
        intros σ τ α στLEα.
        inversion στLEα as [ | * * σLEα | * * τLEα ]; auto.
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
            apply CoContra; auto with SubtypeHints.
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
          | Var α => fun τ => ↓α[α] τ
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
      Fact Ω_decidable: forall τ, { Ω τ } + { ~(Ω τ) }.
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

      Fact ΩIdeal_decidable: forall σ, {↓[ω] σ} + {~(↓[ω] σ)}.
      Proof.
        intros.
        left.
        simpl.
        exact OF_Omega.
      Defined.

      Lemma VariableIdeal_decidable: forall α τ, { ↓α[α] τ } + { ~(↓α[α] τ) }.
      Proof.
        intros α τ.
        induction τ as [ β | σ IHσ τ IHτ | ρ1 IHρ1 ρ2 IHρ2 | ];
          try solve [ right; intro τLEσ; inversion τLEσ ].
        - set (varEq := 𝕍_eq_dec α β).
          inversion varEq as [ equal | notEqual ]. 
            { rewrite equal. left. fold (Ideal (Var β) (Var β)). reflexivity. }
            { right. unfold not. intro αLEβ. inversion αLEβ. contradiction. }
        - inversion IHρ1; inversion IHρ2;
            try solve [ left; apply VI_InterLeft; assumption
                  | left; apply VI_InterRight; assumption
                  | right; unfold not; intro τLEσ; inversion τLEσ; contradiction ].
      Defined.

      Lemma VariableFilter_decidable: forall α τ, { ↑α[α] τ } + { ~(↑α[α] τ) }.
      Proof.
        intros α τ.
        induction τ as [ β | σ IHσ τ IH τ | ρ1 IHρ1 ρ2 IHρ2 | ].
        - set (varEq := 𝕍_eq_dec β α).
          inversion varEq as [ equal | notEqual ].
            { rewrite equal. left. fold (Ideal (Var β) (Var β)). reflexivity. }
            { right. unfold not. intro αLEβ. inversion αLEβ. contradiction. }
        - destruct (Ω_decidable τ).
          + left. simpl. apply AI_Omega. assumption.
          + right. unfold not. intro αLEστ. inversion αLEστ. contradiction.
        - inversion IHρ1; inversion IHρ2;
            solve [ left; split; assumption
                  | right; unfold not; intros αLEρ1ρ2; inversion αLEρ1ρ2; contradiction ].
        - simpl. exact (ΩIdeal_decidable (Var α)).
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
      

      Fact Pick_Ideal σ ρ (decσ : forall σ', ty_pair_size (σ, σ') < ty_pair_size (σ, ρ) -> { ↑[σ] σ' } + { ~(↑[σ] σ') } ):
        { τ : IntersectionType | (↓[σ] → [τ] ρ) /\ (forall τ', ↓[σ] → [τ'] ρ -> τ ≤ τ') /\ ty_size τ <= ty_size ρ }.
      Proof.
        induction ρ as [ | σ' _ τ' _ | | ].
        - exists ω.
          split; [|split].
          + apply AI_Omega.
            exact OF_Omega.
          + intros τ' αLEτ'.
            inversion αLEτ'.
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
            ty_pair_size (σ, σ') < ty_pair_size (σ, ρ1) -> { ↑[σ] σ' } + { ~(↑[σ] σ') }).
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
            ty_pair_size (σ, σ') < ty_pair_size (σ, ρ2) -> { ↑[σ]σ' } + { ~(↑[σ]σ') }).
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
            { ↓[fst σ'τ'] (snd σ'τ') } + { ~(↓[fst σ'τ'] (snd σ'τ')) }),
          { ↓[fst στ] (snd στ) } + { ~(↓[fst στ] (snd στ)) }.
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
                { ↑[σ'] τ } + { ~(↑[σ'] τ) }).
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
        forall σ τ, { ↓[σ] τ } + { ~(↓[σ] τ) }.
      Proof.
        intros σ τ.
        exact (Fix ty_pair_size_wf _ Ideal_decidable' (σ, τ)).
      Defined.

      Lemma Filter_decidable:
        forall σ τ, { ↑[σ] τ } + { ~(↑[σ] τ) }.
      Proof.
        intro σ.
        case σ;
         solve [ intros; apply Ideal_decidable
               | intros; apply Ω_decidable ].
      Defined.

      Corollary Subtype_decidable:
        forall σ τ, { σ ≤ τ } + { ~(σ ≤ τ) }.
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

      Inductive tgt : IntersectionType -> IntersectionType -> Prop :=
        | tgt_Id : forall τ, tgt τ τ
        | tgt_Arr : forall σ τ ρ, tgt τ ρ -> tgt (σ → τ) ρ
        | tgt_InterLeft : forall ρ1 ρ2 τ, tgt ρ1 τ -> tgt (ρ1 ∩ ρ2) τ
        | tgt_InterRight : forall ρ1 ρ2 τ, tgt ρ2 τ -> tgt (ρ1 ∩ ρ2) τ.

      Fact tgt_decidable: forall σ τ, {tgt σ τ} + {~(tgt σ τ)}.
      Proof.
        intros σ τ.
        compare σ τ.
        - intro σEqτ.
          left.
          rewrite σEqτ.
          apply tgt_Id.
        - intro σNeqτ.
          induction σ as [ | σ' IHσ' τ' IHτ' | ρ1 IHρ1 ρ2 IHρ2 | ].
          + case τ eqn:τeq;
              right;
              intro inTgt;
              inversion inTgt.
            contradict σNeqτ.
            apply f_equal.
            assumption.
          + compare τ' τ.
            * intro τ'Eqτ.
              left.
              apply tgt_Arr.
              rewrite τ'Eqτ.
              apply tgt_Id.
            * intro τ'Neqτ.
              case (IHτ' τ'Neqτ).
              { left.
                apply tgt_Arr.
                assumption. }
              { intro ninTgt.
                right.
                intro inTgt.
                inversion inTgt.
                + apply σNeqτ.
                  assumption.
                + apply ninTgt.
                  assumption. }
          + compare ρ1 τ.
            * intro ρ1Eqτ.
              rewrite ρ1Eqτ.
              left.
              apply tgt_InterLeft.
              apply tgt_Id.
            * intro ρ1Neqτ.
              case (IHρ1 ρ1Neqτ).
              { left.
                apply tgt_InterLeft.
                assumption. }
              { intro ninTgtρ1.
                compare ρ2 τ.
                - intro ρ2Eqτ.
                  rewrite ρ2Eqτ.
                  left.
                  apply tgt_InterRight.
                  apply tgt_Id.
                - intro ρ2Neqτ.
                  case (IHρ2 ρ2Neqτ).
                  + left.
                    apply tgt_InterRight.
                    assumption.
                  + intro ninTgtρ2.
                    right.
                    intro inTgt.
                    inversion inTgt;
                      [ apply σNeqτ
                      | apply ninTgtρ1
                      | apply ninTgtρ2 ];
                      assumption. } 
          + right.
            intro inTgt.
            inversion inTgt.
            apply σNeqτ.
            assumption.
      Defined.
      

      Inductive Path : IntersectionType -> Prop :=
        | Path_Var : forall α, Path (Var α)
        | Path_Arr : forall σ τ, Path τ -> Path (σ → τ).

      Inductive Organized : IntersectionType -> Prop :=
        | Organized_Path : forall τ, Path τ -> Organized τ
        | Organized_Inter : forall σ τ, Path σ -> Organized τ -> Organized (σ ∩ τ).
      
      Inductive InOrganized: IntersectionType -> IntersectionType -> Prop :=
        | InOrg_HereEnd : forall σ, Path σ -> InOrganized σ σ
        | InOrg_Here : forall σ τ, Organized (σ ∩ τ) -> InOrganized (σ ∩ τ) σ
        | InOrg_There : forall σ τ ρ, InOrganized τ ρ -> InOrganized (σ ∩ τ) ρ.

      Fact tgt_shift: forall τ σ τ', tgt τ (σ → τ') -> tgt τ τ'.
      Proof.
        intros τ.
        induction τ as [ ? | ? ? ? IH | ? IH1 ? IH2 | ]; 
          intros σ τ tgtτστ';
          inversion tgtτστ'.
        - apply tgt_Arr.
          apply tgt_Id.
        - apply tgt_Arr.
          apply (IH σ).
          assumption.
        - apply tgt_InterLeft.
          apply (IH1 σ).
          assumption.
        - apply tgt_InterRight.
          apply (IH2 σ).
          assumption.
      Defined.

      Fact path_tgt_path: forall τ, Path τ -> forall τ', tgt τ τ' -> Path τ'.
      Proof.
        intros τ pτ.
        induction pτ as [ | ? ? pτ IH ] ; intros τ' tgtττ'.
        - inversion tgtττ'.
          apply Path_Var.
        - inversion tgtττ'.
          + apply Path_Arr.
            assumption.
          + apply IH.
            assumption.
      Defined.

      Fact path_not_omega: forall τ, Path τ -> ~ Ω τ.
      Proof.
        intro τ.
        induction τ as [ | σ' ? τ' IHτ' pτ' | ρ1 ? ρ2 | ]; 
          intros pτ; intro ωτ;
          inversion ωτ.
        - inversion pτ as [ | ? ? pτ' ].
          apply (IHτ' pτ').
          assumption.
        - inversion pτ.
        - inversion pτ.
      Qed.

      Fact tgt_organized:
        forall σ τ, Organized τ -> exists τ', (Organized τ') /\ ((σ → τ) ~= τ').
      Proof.
        intros σ τ orgτ.
        induction orgτ as [ | τ1 τ2 pathτ1 orgτ2 [ τ' [ orgτ' τ'Eq ] ] ].
        - exists (σ → τ).
          split.
          + apply Organized_Path.
            apply Path_Arr.
            assumption.
          + reflexivity.
        - exists ((σ → τ1) ∩ τ').
          split.
          + apply Organized_Inter.
            * apply Path_Arr.
              assumption.
            * assumption.
          + rewrite <- τ'Eq.
            split.
            * apply (transitivity (InterIdem)).
              apply SubtyDistrib; 
                apply CoContra;
                auto with SubtypeHints;
                reflexivity.
            * auto with SubtypeHints.
      Defined.

      Fact merge_organized:
        forall ρ1, Organized ρ1 ->
        forall ρ2, Organized ρ2 -> 
        exists τ, Organized τ /\ (ρ1 ∩ ρ2 ~= τ).
      Proof.
        intros ρ1 orgρ1.
        induction orgρ1 as [ τ pathτ | σ τ pathσ orgτ IH ];
          intros ρ2 orgρ2.
        - exists (τ ∩ ρ2).
          split.
          + apply Organized_Inter; assumption.
          + reflexivity.
        - case (IH ρ2 orgρ2) as [ τ' [ orgτ' τ'Eq ] ].
          exists (σ ∩ τ').
          split.
          + apply Organized_Inter; assumption.
          + rewrite <- τ'Eq.
            rewrite associativity.
            reflexivity.
      Defined.

      Definition organization_lemma: 
        forall τ, (τ ~= ω) \/ (exists τ', Organized τ' /\ (τ ~= τ')).
      Proof.
        intros τ.
        induction τ as [ α | σ IHσ τ IHτ | ρ1 IHρ1 ρ2 IHρ2 | ].
        - right.
          exists (Var α).
          split.
          + apply Organized_Path.
            apply Path_Var.
          + reflexivity.
        - case IHτ as [ ωτ | [τ' [ orgτ' τEqτ' ] ] ].
          + left.
            symmetry.
            apply Arrow_Tgt_Omega_eq.
            symmetry.
            assumption.
          + right.
            case (tgt_organized σ τ' orgτ').
            intros τ'' [ orgτ'' στ'Eqτ''].
            exists τ''.
            rewrite τEqτ'.
            split; assumption.
        - case (IHρ1) as [ ωρ1 | [τ'1 [ orgτ'1 ρ1Eqτ'1 ] ] ];
            case (IHρ2) as [ ωρ2 | [τ'2 [ orgτ'2 ρ2Eqτ'2 ] ] ].
          + left.
            rewrite ωρ1.
            rewrite ωρ2.
            auto with SubtypeHints.
          + right.
            exists τ'2.
            split.
            * assumption.
            * rewrite ωρ1.
              rewrite ρ2Eqτ'2.
              symmetry.
              rewrite identity_left at 1.
              reflexivity.
          + right.
            exists τ'1.
            split.
            * assumption.
            * rewrite ωρ2.
              rewrite ρ1Eqτ'1. 
              symmetry.
              rewrite identity_right at 1.
              reflexivity.
          + right.
            case (merge_organized _ orgτ'1 _ orgτ'2) as [ τ' [ τ'org τ'Eq ] ].
            exists τ'.
            split.
            * assumption.
            * rewrite ρ1Eqτ'1.
              rewrite ρ2Eqτ'2.
              assumption.
        - left; reflexivity.
      Defined.

      Fact inOrganized_path: forall σ τ, InOrganized σ τ -> Path τ.
      Proof.
        intros σ τ ioστ.
        induction ioστ as [| ? ? IH|].
        - assumption.
        - inversion IH as [ ? pστ |] .
          + inversion pστ.
          + assumption.
        - assumption.
      Defined.

      Fact Path_Ideal_prime : forall τ,
        (τ ~= ω) \/ Path τ -> 
        forall ρ1 ρ2, 
        ρ1 ∩ ρ2 ≤ τ -> 
        (ρ1 ≤ τ) \/ (ρ2 ≤ τ).
      Proof.
        intro τ.
        induction τ as [ | σ IHσ τ' IHτ' | | ]; 
          intros pτ ρ1 ρ2 ρ1ρ2LEτ;
          try solve [ inversion pτ ];
          set (ρ1ρ2LEτ' := Ideal_principalElement _ _ ρ1ρ2LEτ);
          simpl in ρ1ρ2LEτ'.
        - inversion ρ1ρ2LEτ'.
          + left.
            apply Ideal_principal.
            assumption.
          + right.
            apply Ideal_principal.
            assumption.
        - inversion ρ1ρ2LEτ' as [ | | | | ? ? ρ3 ρ4 aiρ1 aiρ2 ρ3ρ4LEτ' ].
          + left.
            apply (transitivity OmegaTop).
            apply (EqualTypesAreSubtypes_left).
            apply Ω_principal.
            apply OF_Arrow.
            assumption.
          + left.
            apply Ideal_principal.
            assumption.
          + right.
            apply Ideal_principal.
            assumption.
          + inversion pτ as [ωτ | pτ'].
            * left.
              rewrite ωτ.
              exact OmegaTop.
            * inversion pτ' as [ | ? ? pτ'' ].
              case (IHτ' (or_intror pτ'') ρ3 ρ4 ρ3ρ4LEτ') as [ ρ3LEτ' | ρ4LEτ' ].
              { left.
                rewrite <- (CoContra (reflexivity σ) ρ3LEτ').
                apply Ideal_principal.
                assumption. }
              { right.   
                rewrite <- (CoContra (reflexivity σ) ρ4LEτ').
                apply Ideal_principal.
                assumption. }
        - inversion pτ as [ ωτ | pτ' ]. 
          + left.
            rewrite ωτ.
            exact OmegaTop.
          + inversion pτ'.
        - left.
          exact OmegaTop.
      Defined.

      Fact Ideal_prime_path : forall τ,
        (forall ρ1 ρ2, ρ1 ∩ ρ2 ≤ τ -> (ρ1 ≤ τ) \/ (ρ2 ≤ τ)) ->
        exists τ', (τ ~= τ') /\ ((τ' ~= ω) \/ Path τ').
      Proof.
        intro τ.
        induction τ as [α | σ ? τ IHτ | ρ1 IHρ1 ρ2 IHρ2 | ]; intro τprime.
        - intros.
          exists (Var α).
          split.
          + reflexivity.
          + right.
            apply Path_Var.
        - assert (τprimecond : forall ρ1 ρ2, ρ1 ∩ ρ2 ≤ τ -> (ρ1 ≤ τ) \/ (ρ2 ≤ τ)).
          + intros ρ1 ρ2 ρ1ρ2LEτ.
            assert (ρ1ρ2LEστ : (σ → ρ1) ∩ (σ → ρ2) ≤ σ → τ).
            * transitivity (σ → ρ1 ∩ ρ2).
              { apply InterDistrib. } 
              { apply CoContra.
                - reflexivity.
                - assumption. }
            * case (τprime _ _ ρ1ρ2LEστ) as [ σρLEστ | σρLEστ ];
                [ left | right ];
                set (σρLEστ' := Ideal_principalElement _ _ σρLEστ);
                inversion σρLEστ';
                solve [ apply (transitivity OmegaTop);
                  apply (EqualTypesAreSubtypes_left);
                  apply (Ω_principal);
                  assumption
                | assumption ].
          + case (IHτ τprimecond) as [ τ' [ τEqτ' [ ωτ' | pτ' ] ] ].
            { exists τ'.
              split.
              - rewrite τEqτ'.
                rewrite ωτ'.
                symmetry.
                auto with SubtypeHints.
              - left.
                assumption. }
            exists (σ → τ').
            split.
            * rewrite τEqτ'.
              reflexivity.
            * right.
              apply Path_Arr.
              assumption.
        - case (Subtype_decidable ρ1 ρ2);
            [|case (Subtype_decidable ρ2 ρ1)].
          + intro ρ1LEρ2.
            assert (primecond :
              (forall ρ1' ρ2', (ρ1' ∩ ρ2' ≤ ρ1) -> (ρ1' ≤ ρ1) \/ (ρ2' ≤ ρ1))).
            { intros ρ1' ρ2' ρ1'ρ2'LE.
              rewrite (@InterIdem ρ1) in ρ1'ρ2'LE.
              rewrite (SubtyDistrib (reflexivity ρ1) (ρ1LEρ2)) in ρ1'ρ2'LE.
              case (τprime ρ1' ρ2' ρ1'ρ2'LE);
                [ left | right ];
                solve [ transitivity (ρ1 ∩ ρ2); [ assumption | apply InterMeetLeft ] ]. }
            case (IHρ1 primecond) as [ τ' [ ρ1Eqτ' [ ωτ' | pτ' ] ] ].
            * exists τ'.
              split.
              { rewrite ρ1Eqτ'.
                rewrite ωτ'.
                rewrite <- identity_left.
                split.
                - exact OmegaTop.
                - rewrite <- ωτ'.
                  rewrite <- ρ1Eqτ'.
                  assumption. }
              { left.
                assumption. }
            * exists τ'.
              split.
              { split.
                - rewrite <- ρ1Eqτ'.
                  apply InterMeetLeft.
                - rewrite <- ρ1LEρ2.
                  rewrite <- InterIdem.
                  apply EqualTypesAreSubtypes_right.
                  assumption. }
              { right. assumption. }
          + intros ρ1LEρ2 ρ1NLEρ2.
            assert (primecond :
              (forall ρ1' ρ2', (ρ1' ∩ ρ2' ≤ ρ2) -> (ρ1' ≤ ρ2) \/ (ρ2' ≤ ρ2))).
            { intros ρ1' ρ2' ρ1'ρ2'LE.
              rewrite (@InterIdem ρ2) in ρ1'ρ2'LE.
              rewrite (SubtyDistrib (ρ1LEρ2) (reflexivity ρ2)) in ρ1'ρ2'LE.
              case (τprime ρ1' ρ2' ρ1'ρ2'LE);
                [ left | right ];
                solve [ transitivity (ρ1 ∩ ρ2); [ assumption | apply InterMeetRight ] ]. }
            case (IHρ2 primecond) as [ τ' [ ρ2Eqτ' [ ωτ' | pτ' ] ] ].
            * exists τ'.
              split.
              { rewrite ρ2Eqτ'.
                rewrite ωτ'.
                rewrite <- identity_right.
                split.
                - exact OmegaTop.
                - rewrite <- ωτ'.
                  rewrite <- ρ2Eqτ'.
                  assumption. }
              { left.
                assumption. }
            * exists τ'.
              split.
              { split.
                - rewrite <- ρ2Eqτ'.
                  apply InterMeetRight.
                - rewrite <- ρ1LEρ2.
                  rewrite <- InterIdem.
                  apply EqualTypesAreSubtypes_right.
                  assumption. }
              { right. assumption. }
          + intros ρ2NLEρ1 ρ1NLEρ2.
            contradict τprime.
            intro τprime.
            case (τprime ρ1 ρ2 (reflexivity _)).
            * intro ρ1LEρ1ρ2.
              rewrite InterMeetRight in ρ1LEρ1ρ2.
              apply ρ1NLEρ2.
              assumption.
            * intro ρ2LEρ1ρ2.
              rewrite InterMeetLeft in ρ2LEρ1ρ2.
              apply ρ2NLEρ1.
              assumption.
        - exists ω.
          split.
          + reflexivity.
          + left.
            reflexivity.
      Defined.

      Lemma Ideal_prime: forall τ,
        (forall ρ1 ρ2, ρ1 ∩ ρ2 ≤ τ -> (ρ1 ≤ τ) \/ (ρ2 ≤ τ)) <->
        exists τ', (τ ~= τ') /\ ((τ' ~= ω) \/ Path τ').
      Proof.
        split.
        - apply Ideal_prime_path.
        - intros [τ' [ τEqτ' primecond ]] ρ1 ρ2 ρ1ρ2LEτ.
          case (Path_Ideal_prime τ' primecond ρ1 ρ2).
          + rewrite <- τEqτ'.
            assumption.
          + intro ρ1LEτ'.
            left.
            rewrite τEqτ'.
            assumption.
          + intro ρ2LEτ'.
            right.
            rewrite τEqτ'.
            assumption.
      Defined.

      Lemma organization_path_subtype_lemma: forall σ τ,
        Organized σ ->
        Path τ ->
        σ ≤ τ ->
        exists τ', InOrganized σ τ' /\ (τ' ≤ τ).
      Proof.
        intro σ.
        induction σ as [ α | σ' IHσ' τ' | ρ1 IHρ1 ρ2 IHρ2 | ]; intros τ oσ pτ σLEτ.
        - exists (Var α).
          split.
          + apply InOrg_HereEnd.
            apply Path_Var.
          + assumption.
        - exists (σ' → τ').
          split.
          + apply InOrg_HereEnd.
            inversion oσ.
            assumption.
          + assumption.
        - assert (ρ1Orρ2LEτ : (ρ1 ≤ τ) \/ (ρ2 ≤ τ)).
          { apply Path_Ideal_prime.
            - right.
              assumption.
            - assumption. }
          case ρ1Orρ2LEτ as [ρ1LEτ | ρ2LEτ].
          + exists ρ1.
            split.
            * apply InOrg_Here.
              assumption.
            * assumption.
          + inversion oσ as [ ? pρ1ρ2 | ? ? ? orgρ2 ].
            * inversion pρ1ρ2.
            * case (IHρ2 τ orgρ2 pτ ρ2LEτ) as [ τ' [inorgρ2τ' τ'LEτ] ].
              exists τ'.
              split.
              { apply InOrg_There.
                assumption. }
              { assumption. }
        - inversion oσ as [ ? pω |].
          inversion pω.
      Defined.

    End BetaLemmas.

   
  End SubtypeRelation.

  Module FCL.
    
    (*Variable Base : Set.*)
    Definition Base : Set := nat.
    Definition Ctxt : Type := Base -> IntersectionType.
   
    Inductive Term: Set :=
      | TV :  Base -> Term
      | App : Term -> Term -> Term.

    Coercion TV : Base >-> Term.

    Import SubtypeRelation.
    Reserved Notation "Γ '⊢' M : τ" (at level 90, M at level 19, no associativity).
    Inductive FCL (Γ : Ctxt) : Term -> IntersectionType -> Prop :=
      | FCL_Var : forall x τ, τ = Γ(x) -> Γ ⊢ x : τ
      | FCL_MP : forall M N σ τ, Γ ⊢ M : σ → τ -> Γ ⊢ N : σ -> Γ ⊢ (App M N) : τ
      | FCL_ST : forall M σ τ, Γ ⊢ M : σ -> σ ≤ τ -> Γ ⊢ M : τ
      (*| FCL_II : forall M σ τ, Γ ⊢ M : σ -> Γ ⊢ M : τ -> Γ ⊢ M : σ ∩ τ*)
    where "Γ '⊢' M : τ" := (FCL Γ M τ).

    Fact app_types Γ : 
      forall M N τ, Γ ⊢ (App M N) : τ ->
      exists σ, (Γ ⊢ M : σ → τ) /\ (Γ ⊢ N : σ).
    Proof.
      intros M N τ MNτ.
      remember (App M N) eqn:MNEq.
      induction MNτ as [ | M' ? σ ? Mστ ? Nσ | M' σ τ Mσ IHMσ  ].
      - discriminate MNEq.
      - exists σ.
        inversion MNEq as [ [ MEq NEq ] ].
        rewrite MEq in Mστ.
        rewrite NEq in Nσ.
        split; assumption.
      - case (IHMσ MNEq) as [ σ' [ Mσ'σ Nσ' ] ].
        exists σ'.
        split.
        * apply (FCL_ST _ _ (σ' → σ)).
          { assumption. }
          { apply CoContra.
            - reflexivity.
            - assumption. }
        * assumption.
    Defined.

    Fact FCL_II Γ : forall M ρ1, Γ ⊢ M : ρ1 -> forall ρ2, Γ ⊢ M : ρ2 -> Γ ⊢ M : ρ1 ∩ ρ2.
    Proof.
      intro M.
      induction M as [ x | M IHM N IHN ].
      - intros ρ1 xρ1 ρ2 xρ2.
        remember (TV x) eqn:xEq.
        induction xρ1 as [ x' ? Γxρ1 | | ? σ ? xσ IHx σLEτ ].
        + remember (TV x') eqn:x'Eq.
          induction xρ2 as [ ? ? Γxρ2 | | ? σ ? xσ IHx σLEτ ].
          * inversion x'Eq.
            rewrite Γxρ1.
            rewrite Γxρ2.
            apply (FCL_ST _ _ (Γ x')).
            { apply FCL_Var.
              reflexivity. }
            { inversion x'Eq.
              apply InterIdem. }
          * discriminate xEq.
          * apply (FCL_ST _ _ (τ ∩ σ)).
            { exact (IHx x'Eq xEq). }
            { apply SubtyDistrib.
              - reflexivity.
              - exact σLEτ. }
        + discriminate xEq.
        + apply (FCL_ST _ _ (σ ∩ ρ2)).
          * exact (IHx xEq xρ2).
          * apply SubtyDistrib.
            { exact σLEτ. }
            { reflexivity. }
      - intros ρ1 Mρ1 ρ2 Mρ2.
        case (app_types _ _ _ _ Mρ1) as [ σ1 [ Mσ1ρ1 Nσ1 ] ].
        case (app_types _ _ _ _ Mρ2) as [ σ2 [ Mσ2ρ2 Nσ2 ] ].
        set (Mσ1ρ1σ2ρ2 := IHM _ Mσ1ρ1 _ Mσ2ρ2).
        assert (Mσ1σ2ρ1ρ2 : Γ ⊢ M : σ1 ∩ σ2 → ρ1 ∩ ρ2).
        { apply (FCL_ST _ _ ((σ1 → ρ1) ∩ (σ2 → ρ2))).
          - exact Mσ1ρ1σ2ρ2.
          - transitivity ((σ1 ∩ σ2 → ρ1) ∩ (σ1 ∩ σ2 → ρ2)).
            + apply SubtyDistrib.
              * apply (CoContra (InterMeetLeft)).
                reflexivity.
              * apply (CoContra (InterMeetRight)).
                reflexivity.
            + apply InterDistrib. }
        set (Nσ1σ2 := IHN _ Nσ1 _ Nσ2).
        apply (FCL_MP _ _ _ (σ1 ∩ σ2)).
        + exact Mσ1σ2ρ1ρ2.
        + exact Nσ1σ2.
    Defined.


    Section Inhabitation.
      Require Import Logic.Decidable.
      
      
      Require Import Classes.Morphisms.
      Require Import Coq.Program.Basics.
      Instance ST_Proper_FCL {Γ : Ctxt} {M : Term} : Proper ((≤) ==> (impl)) (FCL Γ M).
      Proof.
        compute.
        intros τ τ'.
        intros.
        apply (FCL_ST _ _ τ); assumption.
      Defined.
      Instance STEq_Proper_FCL {Γ : Ctxt} {M : Term} : Proper ((~=) ==> (iff)) (FCL Γ M).
      Proof.
        compute.
        intros τ τ'.
        intro τEqτ'.
        split.
        - rewrite (EqualTypesAreSubtypes_left _ _ τEqτ').
          trivial.
        - rewrite (EqualTypesAreSubtypes_right _ _ τEqτ').
          trivial.
      Defined.
  
      Instance ST_Proper_Dec_FCL {Γ : Ctxt} {M : Term} : Proper ((~=) ==> (impl))  (fun τ => decidable (exists M, Γ ⊢ M : τ)).
      Proof.
        intros τ τ' τEqτ' decτ.
        case decτ.
        - intros [ N Nτ ].
          left.
          exists N.
          rewrite <- τEqτ'.
          assumption.
        - intro nMτ.
          right.
          intros [N Nτ'].
          contradict nMτ.
          exists N.
          rewrite τEqτ'.
          assumption.
      Defined.

      Fixpoint proofContext (Γ : Ctxt) (M : Term) (τ : IntersectionType) (σs : list IntersectionType) {struct σs} : Set :=
        match σs with
          | nil => Γ ⊢ M : τ
          | cons σ σs' => forall N, Γ ⊢ N : σ -> proofContext Γ  (App M N) τ σs'
        end.

      Record ProofTreeGrammarProduction {Γ τ} : Set := {
        c : Base;
        σs : list IntersectionType;
        ctxt : proofContext Γ c τ σs }.

      Import EqNotations.
      Definition ProofTreeGrammarRules Γ :=
        forall τ, @ProofTreeGrammarProduction Γ τ -> Prop.

     Definition filter_context { Γ }:
        forall σs M τ, proofContext Γ M τ σs -> forall τ', τ ≤ τ' -> proofContext Γ M τ' σs.
      Proof.
        intro σs.
        induction σs as [ | σ σs' IH ].
        - intros.
          apply (FCL_ST _ _ τ); assumption.
        - intros M τ p τ' τLEτ' N pN.
          fold proofContext.
          exact (IH (App M N) τ (p N pN) τ' τLEτ').
      Defined.

      Inductive filter_closure {Γ} (rules: ProofTreeGrammarRules Γ): ProofTreeGrammarRules Γ :=
        | fc_lift : forall τ p, rules τ p -> filter_closure rules τ p
        | fc_filter : forall τ p,
            rules τ p ->
            forall τ' τLEτ',
            filter_closure rules τ'
              {|  c := c p;
                  σs := σs p;
                  ctxt := filter_context (σs p) (c p) τ (ctxt p) τ' τLEτ'
              |}.

      Require Import Coq.Lists.List.
      (* Inductive finite_restriction {Γ} (rules: ProofTreeGrammarRules Γ): ProofTreeGrammarRules Γ :=
        | fr_terminal : forall τ p,
            rules τ p ->
            σs p = nil ->
            finite_restriction rules τ p
        | fr_nonterminal : forall τ p,
            rules τ p ->
            (forall σ, In σ (σs p) -> exists p', finite_restriction rules σ p') ->
            finite_restriction rules τ p.
      *)

      Definition fill_ctxt_step {Γ} (σ : IntersectionType) (σs : list IntersectionType):
        forall (fill_ctxt : 
          (forall σ', In σ' σs -> { N : Term | Γ ⊢ N : σ' }) ->
          forall N τ, proofContext Γ N τ σs -> { M : Term | Γ ⊢ M : τ } ),
        (forall σ', In σ' (σ::σs) -> { N : Term | Γ ⊢ N : σ' }) -> 
        forall M τ, proofContext Γ M τ (σ::σs) -> { M : Term | Γ ⊢ M : τ } :=
        fun fill_ctxt => fun σσsSound => fun M τ => fun ctxt =>
          let NNσ := σσsSound σ (@or_introl (σ = σ) (In σ σs) eq_refl) in
          fill_ctxt 
            (fun σ' => fun (σ'Inσs : In σ' σs) => 
              σσsSound σ' (@or_intror (σ = σ') (In σ' σs) σ'Inσs))
            (App M (proj1_sig NNσ)) τ
            (ctxt (proj1_sig NNσ) (proj2_sig NNσ)).

      Function fill_ctxt {Γ} (σs : list IntersectionType) {struct σs}:
        (forall σ, In σ σs -> { N : Term | Γ ⊢ N : σ }) ->
        forall M τ, proofContext Γ M τ σs -> { M : Term | Γ ⊢ M : τ } :=
        match σs with
          | nil => fun _ => fun M τ => fun (ctxt : proofContext Γ M τ nil) => exist _ M ctxt
          | (σ::σs') => fill_ctxt_step σ σs' (fill_ctxt σs')
        end.

      (*

      Proof.
        case σs.
        - intros _ N τ ctxt.
          exists N.
          exact ctxt.
        - intros σ σs' pσs M τ ctxt.
          case (pσs σ (@or_introl (σ = σ) (In σ σs') eq_refl)) as [N pN].
          assert (pσs' : forall σ, In σ σs' -> { N : Term | Γ ⊢ N : σ }).
          { intros σ' σ'inσs'.
            apply pσs.
            apply (@or_intror (σ = σ') (In σ' σs')).
            assumption. }
          apply (fill_ctxt _ σs' pσs' (App M N) τ (ctxt N pN)) .
      Defined.*)
    
      Inductive derivable {Γ} (rules: ProofTreeGrammarRules Γ) (τ : IntersectionType):
        { M : Term | Γ ⊢ M : τ } -> Prop :=
        | derivable_deriv : forall p,
            rules τ p ->
            forall (σs_derivable : forall σ, In σ (σs p) -> { N : Term | Γ ⊢ N : σ }),
            (forall σ inσs, derivable rules σ (σs_derivable σ inσs)) ->
            derivable rules τ (fill_ctxt (σs p) σs_derivable (c p) τ (ctxt p)).

           
      Import ListNotations.
      Definition append_param Γ τ σ σs:
        forall M, proofContext Γ M (σ → τ) σs -> proofContext Γ M τ ( σs ++ [σ] ).
      Proof.
        induction σs as [ | σ' σs' IH ].
        - simpl.
          intros.
          apply (FCL_MP _ _ _ σ); assumption.
        - simpl.
          intros M Mστ N Nσ'.
          apply IH.
          apply Mστ.
          assumption.
      Defined.

          

      Inductive applicative_closure {Γ : Ctxt} (rules : ProofTreeGrammarRules Γ):
        ProofTreeGrammarRules Γ :=
        | ac_lift : forall τ p, rules τ p -> applicative_closure rules τ p
        | ac_app : forall σ τ p, applicative_closure rules (σ → τ) p ->
            (* forall p', applicative_closure rules σ p' -> (*TODO: necessary???*) *)
            applicative_closure rules τ {|
              c := c p;
              σs := (σs p) ++ [ σ ];
              ctxt := append_param Γ τ σ (σs p) (c p) (ctxt p)
            |}.

      (*Definition intersect_params Γ σ τ σs:
        forall σs',
        length σs = length σs' ->
        forall M M',
        M = M' ->
        proofContext Γ M σ σs ->
        proofContext Γ M' τ σs' ->
        proofContext Γ M (σ ∩ τ) (map (prod_curry Inter) (combine σs σs')).
      Proof.
        induction σs as [ | σs_hd σs_tl IH ].
        - intros σs' lengthEq.
          case σs' eqn:p.
          + simpl.
            intros M M' Meq.
            rewrite Meq.
            apply (FCL_II).
          + discriminate lengthEq.
        - intros σs' lengthEq.
          case σs' as [ | σs'_hd σs'_tl] eqn:p.
          + discriminate lengthEq.
          + intros M M' MEq pσ pτ.
            simpl.
            intros N pN.
            inversion lengthEq as [ lengthEq_tl ].
            apply (IH σs'_tl lengthEq_tl (App M N) (App M' N)).
            * rewrite MEq.
              reflexivity.
            * apply pσ.
              apply (FCL_ST _ _ (σs_hd ∩ σs'_hd)).
              { assumption. }
              { apply InterMeetLeft. }
            * apply pτ.
              apply (FCL_ST _ _ (σs_hd ∩ σs'_hd)).
              { assumption. }
              { apply InterMeetRight. }
      Defined.    
      
      Inductive intersection_closure {Γ : Ctxt} (rules : ProofTreeGrammarRules Γ):
        ProofTreeGrammarRules Γ :=
        | ic_lift : forall τ p, rules τ p -> intersection_closure rules τ p
        | ic_inter: forall σ p, intersection_closure rules σ p ->
            forall τ p', intersection_closure rules τ p' ->
            forall (cEq : (TV (c p)) = (TV (c p'))),
            forall (lengthEq : length (σs p) = length (σs p')),
            intersection_closure rules (σ ∩ τ) {|
              c := c p;
              σs := map (prod_curry Inter) (combine (σs p) (σs p'));
              ctxt := intersect_params Γ σ τ (σs p) (σs p')
                lengthEq (c p) (c p') cEq (ctxt p) (ctxt p')
            |}.
      *)
      Inductive fcl_grammar {Γ : Ctxt}: ProofTreeGrammarRules Γ :=
        | fcl_ax : forall c τ (inBase : τ = Γ c), 
            fcl_grammar τ {|
              c := c;
              σs := nil;
              ctxt := FCL_Var _ _ _ inBase
            |}
        | fcl_derived : forall τ p,
            applicative_closure (filter_closure (fcl_grammar)) τ p ->
            fcl_grammar τ p.

      Corollary fcl_grammar_sound {Γ}:
        forall τ p, derivable (@fcl_grammar Γ) τ p -> exists M, Γ ⊢ M : τ.
      Proof.
        intros τ p _.
        exists (proj1_sig p).
        exact (proj2_sig p).
      Defined.

     
      Fact lift_fill_filter: forall Γ σsp σsSound cp σ ctxtp M Mσ τ σLEτ,
        ( fill_ctxt σsp σsSound cp σ ctxtp =
            exist (fun M : Term => Γ ⊢ M : σ) M Mσ ) ->
        ( fill_ctxt σsp σsSound cp τ (filter_context σsp cp σ ctxtp τ σLEτ) =
            exist (fun M : Term => Γ ⊢ M : τ) M (FCL_ST _ _ _ _ Mσ σLEτ) ).
      Proof.
        intros Γ σsp.
        induction σsp as [ | σ' σsp IH ].
        - intros σsSound cp σ ctxtp M Mσ τ σLEτ ctxtEq.
          inversion ctxtEq.
          reflexivity.
        - intros σsSound cp σ ctxtp M Mσ τ σLEτ ctxtEq.
          set (σsSound' :=
            fun σ'' => fun (σ''Inσsp : In σ'' σsp) =>
              σsSound σ'' (@or_intror (σ' = σ'') (In σ'' σsp) σ''Inσsp)).
          set (NNσ := σsSound σ' (@or_introl (σ' = σ') (In σ' σsp) (eq_refl _))).
          set (N := proj1_sig NNσ).
          set (Nσ := proj2_sig NNσ).
          set (ctxtp' := ctxtp N Nσ).
          fold proofContext in ctxtp'.
          set (IH' := IH σsSound' _ σ ctxtp' M Mσ τ σLEτ). 
          inversion ctxtEq as [ ctxtEq' ].
          assert (fillEq :
              fill_ctxt σsp
                (fun (σ0 : IntersectionType) (H : In σ0 σsp) =>
                σsSound σ0 (@or_intror (σ' = σ0) (In σ0 σsp) H))
                (App cp N) σ (ctxtp N Nσ) =
            fill_ctxt σsp σsSound' (App cp N) σ ctxtp').
          { unfold ctxtp'.
            fold σsSound'.
            reflexivity. }.
          rewrite <- fillEq in IH'.
          unfold fill_ctxt_step in ctxtEq'.
          set (IH'' := IH' ctxtEq').
          rewrite <- IH''.
          reflexivity.
      Defined.
      
      (*Fact base_and_args_eq:
        forall Γ σs1 σs2 σsSound1 σsSound2 cp1 cp2 ρ1 ρ2 ctxtp1 ctxtp2 M Mρ1 Mρ2,
        fill_ctxt σs1 σsSound1 cp1 ρ1 ctxtp1 =
          exist (fun M : Term => Γ ⊢ M : ρ1) M Mρ1 ->
        fill_ctxt σs2 σsSound2 cp2 ρ2 ctxtp2 =
          exist (fun M : Term => Γ ⊢ M : ρ2) M Mρ2 ->
        cp1 = cp2 /\ length σs1 = length σs2.
      Proof.
        intros Γ σs1.
        induction (length σs1) eqn:lenσs1Eq.
        - intros σs2.
          induction σs2 as [ | σ'2 σs'2 IHσ2 ].
          + case σs1 eqn:σs1Eq.
            * intros σsSound1 σsSound2 cp1 cp2 ρ1 ρ2 ctxtp1 ctxtp2 M Mρ1 Mρ2 fillEq1 fillEq2.
              inversion fillEq1 as [ tvCp1EqM ].
              inversion fillEq2 as [ tvCp2EqM ].
              inversion tvCp1EqM.
              inversion tvCp2EqM.
              split; reflexivity.
            * discriminate lenσs1Eq.
          + intros σsSound1 σsSound2 cp1 cp2 ρ1 ρ2 ctxtp1 ctxtp2 M Mρ1 Mρ2 fillEq1 fillEq2.
            set (NNσ := σsSound2 σ'2 (or_introl (eq_refl _))).
            assert (fillEq'2Eq :
              ((let (N, pN) := σsSound2 σ'2 (or_introl eq_refl) in
                fill_ctxt σs'2
                (fun (σ0 : IntersectionType) (H : In σ0 σs'2) =>
                  σsSound2 σ0 (or_intror H)) (App cp2 N) ρ2 (ctxtp2 N pN)) =
                exist (fun M : Term => Γ ⊢ M : ρ2) M Mρ2) =
              (fill_ctxt σs'2 
                (fun (σ' : IntersectionType) (σ'Inσs'2 : In σ' σs'2) =>
                  σsSound2 σ' (or_intror σ'Inσs'2)) (App cp2 (proj1_sig NNσ)) ρ2
                    (ctxtp2 (proj1_sig NNσ) (proj2_sig NNσ)) =
               exist (fun M : Term => Γ ⊢ M : ρ2) M Mρ2)).
            { fold NNσ.
              case NNσ.
              intros.
              reflexivity. }
            set (IH' := IHσ2 σsSound1 
              (fun σ' => fun σ'Inσs'2 => σsSound2 _ (or_intror σ'Inσs'2))
              cp1 (App cp2 (proj1_sig NNσ))
              ρ1 ρ2 
              ctxtp1 (ctxtp2 (proj1_sig NNσ) (proj2_sig NNσ))
              M Mρ1 Mρ2 
              fillEq1).
            rewrite <- fillEq'2Eq in IH'.
            inversion fillEq2 as [ cp2EqM ].
            case (IH' cp2EqM) as [ cp1Eq len_σs'2Eq].
            case σs'2 eqn:σs'2Eq.
            * simpl in cp2EqM.
              
            inversion len_σs'2Eq as [ σs2'Eq ].

            set (cp1Eq := proj1 IH'')
            set 
            set (MEq := eq_sym (eq_trans (eq_sym cp1Eq) cp1EqM)).
            inversion MEq in cp2EqM.
            inversion cp1Eq.
        - intros σs2.
          induction σs2 as [ | σ'2 σs'2 IHσ2 ];
            intros σsSound1 σsSound2 cp1 cp2 ρ1 ρ2 ctxtp1 ctxtp2 M Mρ1 Mρ2 fillEq1 fillEq2;
            inversion fillEq1 as [ cp1EqM ];
            inversion fillEq2 as [ cp2EqM ].
          +  


          induction σs2 as [ | σ'2 σs'2 IHσ2 ].
      *)

      Fact append_sound Γ :
        forall N σ, Γ ⊢ N : σ ->
        forall σs, (forall σ', In σ' σs -> { N : Term | Γ ⊢ N : σ' }) -> 
        forall σ', In σ' ( σs ++ [σ] ) -> { N : Term | Γ ⊢ N : σ' }. 
      Proof.
        intros N σ Nσ σs σsSound σ' σ'Inσsσ.
        set (σ'Inσσs := proj1 (in_rev _ _) σ'Inσsσ).
        rewrite (rev_unit _ _) in σ'Inσσs.
        case (IntersectionType_eq_dec σ' σ) as [ σ'Eqσ | σ'Neqσ ].
        - exists N.
          rewrite σ'Eqσ.
          exact Nσ.
        - apply σsSound.
          inversion σ'Inσσs as [ σ'Eqσ | σInσs ].
          + contradict (σ'Neqσ (eq_sym σ'Eqσ)).
          + apply in_rev.
            assumption.
      Defined.
(*
      Fact foo: forall Γ n σs σ,
        n = length (σs ++ [σ] ) -> 
        forall τ M σsSound ctxt N Nσ,
        proj1_sig 
          (fill_ctxt (σs ++ [σ] ) 
            (append_sound Γ N σ Nσ σs σsSound) M τ 
            (append_param Γ τ σ σs M ctxt)) =
        (App (proj1_sig (fill_ctxt σs σsSound M (σ → τ) ctxt)) N).
      Proof.
        intros Γ n.
        induction n as [ | n' IHn' ].
        Focus 2.
        - intros σs σ nEq τ M σsSound ctxt N Nσ.
          set (σsSound' := fun σ'' => fun (σ''inσs' : In σ'' σs') => 
            σsSound σ'' (@or_intror (σ' = σ'') (In σ'' σs') σ''inσs')).
          set (N'N'σ' := σsSound σ' (or_introl eq_refl)).
          set (N' := proj1_sig N'N'σ').
          set (N'σ' := proj2_sig N'N'σ').
          (*set (ainaσs0 := (@or_introl (a = a) (In a ( σs0 ++ [σ] )) eq_refl)).
          case (σsSound a (@or_introl (a = a) (In a σs0) eq_refl)) as [ N''' N'''a ].            
          (*case (append_sound Γ N σ Nσ (a :: σs0) σsSound a (ainaσs0)) as [ N'' N''a ].*)
          (*case (fill_ctxt σs0 σsSound' (App M N''') (σ → τ) (ctxt0 N''' N'''a)) as [ M' M'στ ] eqn:M'M'στEq.
          set (ctxt0' := ctxt0 N''' N'''a).
          fold proofContext in ctxt0'.*)
          case (fill_ctxt σs0 σsSound' (App M N''') (σ → τ) (ctxt0 N''' N'''a)) as [ M' M'στ ] eqn:M'Eq. *)
          set (IH := IHσs' σ τ (App M N') σsSound' (ctxt N' N'σ') N Nσ).
          rewrite M'Eq in IH.
          case IH as [ IHderiv IHEq ].
          case σs0.
          unfold append_sound at 1.
          case (IntersectionType_eq_dec a σ) as [ aEqσ | aNEqσ ].
          + simpl.
            unfold append_sound at 1.
          exists IHderiv.
          rewrite <- IHEq.
          unfold (
          + simpl.

          
          rewrite M'M'στEq in IH.
          unfold σsSound' in IH.

          intros M' M'σ.
          rewrite <- IH. 

      Fact lift_fill_append: forall Γ σsp σ τ cp σsSound σsσSound ctxtp ctxtp' M Mστ,
        ( fill_ctxt σsp σsSound cp (σ → τ) ctxtp =
            exist (fun M : Term => Γ ⊢ M : σ → τ) M Mστ ) ->
        exists N deriv,
        ( fill_ctxt (σsp ++ [σ] ) (σsσSound) cp τ ctxtp' =
            exist (fun M : Term => Γ ⊢ M : τ) (App M N) deriv ).
      Proof.
        intros Γ σsp σ.
        induction (σsp ++ [σ] ) eqn:σsσEq using rev_ind .
        - contradict (app_cons_not_nil σsp [] σ (eq_sym σsσEq)).
        - 
          rewrite 
          intros cp σ τ σsSound σsσSound ctxtp ctxtp' M Mστ ctxtEq.
          simpl.
          case (σsσSound σ (or_introl eq_refl)) as [ N Nσ ].
          exists N.
          inversion ctxtEq.
          exists (ctxtp' N Nσ).
          reflexivity.
        - intros cp σ.
          rewrite <- (app_comm_cons σsp [σ] a).
          intros τ σsSound σsσSound ctxtp ctxtp' M Mστ ctxtEq.
          set (IH := cp σ τ σsSound 
          unfold fill_ctxt.

          set (N := proj1_sig NNσ).
          set (Nσ := proj2_sig NNσ).
          exists N.
          exists Nσ.
          

          unfold append_sound.
          simpl.
          case (IntersectionType_eq_dec σ σ).
          + intro σEqσ.
            simpl.
            exists (eq_ind_r (fun σ' : IntersectionType => Γ ⊢ N : σ') Nσ σEqσ).
            inversion ctxtEq.
            reflexivity.
          + intro σNeqσ.
            contradict (σNeqσ (eq_refl σ)).
        - intros σsSound cp σ τ ctxtp M N Mστ Nσ ctxtEq.
            set (p := eq_ind_r (fun σ' : IntersectionType => Γ ⊢ N : σ') Nσ σEqσ).
            inversion p.
            * unfold p.
              simpl.


      Lemma fcl_grammar_complete {Γ}:
        forall τ M, Γ ⊢ M : τ -> exists deriv, derivable (@fcl_grammar Γ) τ (exist _ M deriv).
      Proof.
        intros τ M Mτ.
        induction Mτ as [ x τ xτ | M N σ τ ? [ Mστ derivableM ] ? [ Nσ derivableN ] | M σ τ ? [ Mσ derivableM ] σLEτ (* | M ρ1 ρ2 ? [ Mρ1 derivableMρ1 ] ? [ Mρ2 derivableMρ2 ] *) ].
        (*Focus 4.
        - inversion derivableMρ1 as [ p1 rulesp1 σsSound1 σsDeriv1 ctxtEq1 ].
          inversion derivableMρ2 as [ p2 rulesp2 σsSound2 σsDeriv2 ctxtEq2 ].
          case p1 as [ cp1 σsp1 ctxtp1 ] eqn:p1Eq.
          case p2 as [ cp2 σsp2 ctxtp2 ] eqn:p2Eq.

          inversion ctxtEq2.
          set (prodρ1ρ2 := fcl_derived (ρ1 ∩ ρ2) _
            (ic_inter  *)

        Focus 3.
        - inversion derivableM as [ p rulesp σsSound σsDeriv ctxtEq ].
          case p as [ cp σsp ctxtp ] eqn:pEq.
          set (prodτ := fcl_derived τ _ 
              (*(ic_lift (applicative_closure (filter_closure (@fcl_grammar Γ))) τ _ *)
                (ac_lift (filter_closure (@fcl_grammar Γ)) _ _
                  (fc_filter _ _ _ rulesp _ σLEτ)))(*)*).
          set (res := derivable_deriv fcl_grammar τ _ prodτ σsSound σsDeriv).
          simpl in res.
          inversion ctxtEq as [ ctxtEq' ].
          rewrite (lift_fill_filter _ _ _ _ _ _ _ _ _ σLEτ ctxtEq') in res.
          exists (FCL_ST Γ M σ τ Mσ σLEτ).
          exact res.
        - exists (FCL_Var _ _ _ xτ).
          set (deriv_ax := fcl_ax x τ xτ).
          set (σsSound := fun σ' => fun (σ'Inσs : In σ' [] ) => False_rec { N | Γ ⊢ N : σ' } σ'Inσs).
          set (σsDeriv := fun σ' => fun (σ'Inσs : In σ' [] ) => False_ind (derivable (@fcl_grammar Γ) σ' (σsSound σ' σ'Inσs)) σ'Inσs).
          exact (derivable_deriv fcl_grammar τ _ deriv_ax σsSound σsDeriv).
        - inversion derivableM as [ p rulesp σsSound σsDeriv ctxtEq ].
          set (prodτ := fcl_derived τ _
                (ac_app _ _ _ p
                  (ac_lift (filter_closure (@fcl_grammar Γ)) _ _
                     (fc_lift (@fcl_grammar Γ) _ _ rulesp)))).
          set (σsσSound := append_sound Γ N σ Nσ (σs p) σsSound). 
          assert (σsσDeriv : forall σ' inσsσ,
            derivable (@fcl_grammar Γ) σ' (σsσSound σ' inσsσ)).
          { intros σ' σ'Inσsσ.
            unfold σsσSound.
            unfold append_sound.
            case (IntersectionType_eq_dec σ' σ).
            + intro σ'Eqσ.
              rewrite σ'Eqσ.
              exact derivableN.
            + intro σ'Neqσ.
              case (eq_ind 
                (rev (σs p ++ [σ] )) (fun l : list IntersectionType => In σ' l)
                  (proj1 (in_rev (σs p ++ [σ] ) σ') σ'Inσsσ) (σ :: rev (σs p))
                  (rev_unit (σs p) σ)).
              * intro σEqσ'.
                contradict (σ'Neqσ (eq_sym σEqσ')).
              * intro σ'Inrevσs.
                apply σsDeriv. }
          set (res := derivable_deriv fcl_grammar τ _ prodτ σsσSound σsσDeriv).
          simpl in res.
          case p as [ cp σsp ctxtp ] eqn:pEq.
          exists (proj2_sig (fill_ctxt (σs p ++ [σ] ) σsσSound (c p) τ
                   (append_param Γ τ σ (σs p) (c p) (ctxt p)))).

        
        
          inversion derivableM as [ p rulesp σspEmpty cpEqM | ].
          Focus 2.
          + set (p' := {| c := c p; σs := []; ctxt := rew σspEmpty in ctxt p |}).
            assert (pEqp' : p = p').
            { destruct p eqn:pEq.
              unfold p'.
              rewrite <- σspEmpty.
              reflexivity. }
            set (prodτ := fcl_derived τ _ 
              (ic_lift (applicative_closure (filter_closure (@fcl_grammar Γ))) τ _ 
                (ac_app (filter_closure (@fcl_grammar Γ)) _ _ _
                  (ac_lift (filter_closure (@fcl_grammar Γ)) _ _
                    (fc_lift _ _ p' (rew pEqp' in rulesp)))))).
            set (σsSound : forall σ', In σ' [σ] ->  { N : Term | Γ ⊢ N : σ' } :=
              Proof.
              { intros σ' σ'Inσ.
                exists N.
                inversion σ'Inσ as [ σEqσ' | inσ'Empty ].
                - rewrite <- σEqσ'.
                  assumption.
                - contradict inσ'Empty. }).
              Defined.).
            assert (σsDerivable : 
              forall σ inσs, derivable (@fcl_grammar Γ) σ (σsSound σ inσs)).
            { intros σ' σ'Inσ.
              destruct σ'Inσ as [ | inσ'Empty ].
              - 

              
              
            set (derivableτ := derivable_nonterminal (@fcl_grammar Γ) τ _ prodτ).
            simpl in derivableτ.
            
            contradict derivableτ.
            rewrite <- σspEmpty.
            rewrite <- σspEmpty in derivableτ.

          eapply (derivable_nonterminal fcl_grammar τ).
        

      Require Coq.Vectors.Fin.
      Record FiniteInhabitantSubset Γ τ : Set := {
        cardinality : nat;
        getAt : Fin.t cardinality -> { M : Term | Γ ⊢ M : τ }
      }.
      Require Import Coq.Lists.Streams.
      Record InhabitantEnumeration Γ τ : Set := {
        enumeration : Stream (option (FiniteInhabitantSubset Γ τ));
        endStable : forall n,
          Str_nth n enumeration = None ->
          ForAll (fun x => hd x = None) (Str_nth_tl n enumeration)
      }.

      Require Import Coq.Lists.List.
      Class ProductionEnumerable {Γ} (rules : ProofTreeGrammarRules Γ) :=
        { enumerateProductions: forall τ, 
            { ps : list (@ProofTreeGrammarProduction Γ τ) |
              forall p, In p ps <-> rules τ p 
            } 
        }.

      Definition toInhabitantEnumeration {Γ} (rules : ProofTreeGrammarRules Γ) `{ProductionEnumerable Γ rules}: 
        forall τ, InhabitantEnumeration Γ τ.
        

      Axiom bailOut : forall {Γ τ}, FiniteInhabitantSubset Γ τ.

      Fixpoint index {Γ} 
        FiniteInhabitantSubset Γ τ :=
        fun τ p =>
          match projT2 p with
            | PCtxt_Closed prf =>
                {|  cardinality := 1;
                    getAt n := exist _ (projT1 p) prf
                |}
            | PCtxt_Hole σ cont =>
                {|  
              PCtxt_
          end.


      Definition filter_rules { Γ }:
        forall (rules : ProofTreeGrammarRules Γ),
        (forall σ, decidable (inhabited { p | rules σ p })) ->
        { rules' : ProofTreeGrammarRules Γ | 
            forall σ p, rules σ p -> forall τ, σ ≤ τ -> exists p', rules τ p' }.
      Proof.
        intros rules decrules.
        assert (rules' : ProofTreeGrammarRules Γ ).
        - intros σ p.
          set (previously_allowed := decrules σ).
          inversion previously_allowed.

      Definition filter_rules {Γ} (rules : ProofTreeGrammarRules Γ): ProofTreeGrammarRules Γ :=
        fun τ p =>
          rules τ p \/ 
          (exists σ , ↑[σ] τ /\ 


      Variable Γ : Ctxt.
      Notation "Γ '⊢' '?' : τ" := (exists M, Γ ⊢ M : τ) (at level 90, no associativity).
      Require Import Coq.Sets.Image.
      Definition Γ_domainFinite : forall τ, Finite _ (fun x => Γ x = τ ).

      Fixpoint outermost_combinator (M : Term): Base :=
        match M with
          | TV c => c
          | App c1 c2 => outermost_combinator c1
        end.

      Fact tgt_ex': forall M τ,
        Γ ⊢ M : τ ->
        exists σ τ', ((σ ~ ω) \/ Organized σ) /\ (σ ~ Γ (outermost_combinator M)) /\ tgt σ τ' /\ (τ' ≤ τ).
      Proof.
        intros M τ Mτ.
        induction Mτ as [ ? ? xτ | M N σ τ Mτ IHM | ? σ ? xσ IH σLEτ | ]. (*; intro pτ.*)
        - case (organization_lemma τ) as [ωτ | [τ' [orgτ' τ'Eqτ ] ] ].
          + exists τ.
            exists τ.
            split; [|split; [|split]].
            * left; assumption.
            * rewrite xτ.
              reflexivity.
            * apply tgt_Id.
            * reflexivity.
          + exists τ'.
            exists τ'.
            split; [|split; [|split]].
            * right; assumption.
            * rewrite <- τ'Eqτ.
              rewrite xτ.
              reflexivity.
            * apply tgt_Id.
            * rewrite τ'Eqτ.
              reflexivity.
        - case (IHM) as [σ' [ τ' [ωorgσ' [σ'Eq [tgtσ'τ' τ'LEστ]]]]].
          set (τ'LEστ_ideal := Ideal_principalElement _ _ τ'LEστ).
          inversion τ'LEστ_ideal as [ | σ_τ' τ_τ' ? ? τ'Eq | ρ1 ? aiρ1 τ'Eq | | ].
          + exists σ'.
            exists τ'.
            split; [|split; [|split]]; try solve [ assumption ].
            apply (transitivity OmegaTop).  
            apply (EqualTypesAreSubtypes_left).
            apply (Ω_principal).
            assumption.
          + exists σ'.
            exists τ_τ'.
            split; [|split; [|split]]; try solve [ assumption ].
            apply (tgt_shift _ σ_τ').
            rewrite τ'Eq.
            assumption.
          + inversion ωorgσ' as [ ωσ' | ].
            set (ωσ'_filter := Ω_principalElement _ (EqualTypesAreSubtypes_right _ _ ωσ')). 
            rewrite <- τ'Eq in tgtσ'τ'.
            inversion ωσ'_filter as [ σ'Eq2 | ? ? ? σ'Eq2 | ];
              try rewrite <- σ'Eq2 in tgtσ'τ'.
            * inversion tgtσ'τ'.
            * inversion tgtσ'τ'. 
          
            exists σ'.
            exists ρ1.
            split; [|split; [|split]]; try solve [ assumption ].
            * apply 


          set (pτ' := path_tgt_path _ pσ' _ tgtσ'τ').
          inversion pτ' as [ ? τ'Eq | σ'' τ'' pτ'' σ''τ''Eqτ' ].
          * rewrite <- τ'Eq in τ'LEστ.
            set (τ'LEστ_ideal := Ideal_principalElement _ _ τ'LEστ).
            inversion τ'LEστ_ideal as [ ? ωτ | | | | ].
            contradict (path_not_omega τ pτ ωτ).
          * exists σ'.
            exists τ''.  
            split; [|split; [|split]]; try solve [ assumption ].
            { rewrite <- σ''τ''Eqτ' in *.
              inversion tgtσ'τ' as [ | ? τ0 ? tgtτ0 | | ].
              - apply tgt_Arr.
                apply tgt_Id.
              - apply tgt_Arr.
                apply (tgt_shift _ σ'').
                assumption.
              - apply tgt_InterLeft. 
                apply (tgt_shift _ σ'').
                assumption.
              - apply tgt_InterRight.
                apply (tgt_shift _ σ'').
                assumption. }
            { rewrite <- σ''τ''Eqτ' in τ'LEστ.
              set (τ'LEστ_ideal := Ideal_principalElement _ _ τ'LEστ).
              inversion τ'LEστ_ideal as [ ? ωτ | | | | ].
              - contradict (path_not_omega τ pτ ωτ).
              - assumption. }
          + 



          case (path_lemma τ' (σ → τ)) as [ τ'' [ inOrgτ'τ'' τ''LEστ ] ].
          case (organization_lemma τ') as [ωτ' | [ τ'' [ orgτ'' τ'Eqτ''] ] ].
          * rewrite ωτ' in τ'LEστ.
            contradict (path_not_omega (σ → τ)
              (Path_Arr _ _ pτ)
              (Ω_principalElement _ τ'LEστ)).
          * exists σ'.
            exists (σ → τ').
            split; [|split; [|split]]; try solve [ assumption ].
            { assumption.
          * assumption.
          * assumption.
          * assumption. 
        
        
        
        
        
        case (organization_lemma σ) as [ ωσ | [ σ' [ orgσ' σ'Eqσ ] ] ].
            * rewrite ωσ in σLEτ.
              contradict (path_not_omega τ pτ (Ω_principalElement _ σLEτ)).
            * exists σ'.
              exists σ'.
              split; [|split; [|split]].
              { assumption. }
              { symmetry.
                
            exists σ.
            exists σ.
            split; [|split; [|split]].
            * 
              
      * apply Organized_Path.     

          remember (TV x) as M eqn:M_eq.
          induction Mτ as [ x' τ τEq | | M σ τ Mσ IH σLEτ | M σ τ Mσ IHσ Mτ IHτ  ].
          + exists τ.
            exists τ.
            split; [|split].
            * simpl.
              rewrite τEq.
              reflexivity.
            * apply tgt_Id.
            * reflexivity.
          + discriminate M_eq.
          + case (IH M_eq) as [σ' [τ' [σEq [tgtσ'τ' τ'LE]]]].
            exists σ'.
            exists τ'.
            split; [|split].
            * assumption.
            * assumption. 
            * exact (transitivity τ'LE σLEτ).
          + case (IHσ M_eq) as [σ1 [τ1' [σ1Eq [tgtσ1τ1' τ1'LEσ] ] ] ].
            case (IHτ M_eq) as [σ2 [τ2' [σ2Eq [tgtσ2τ2' τ2'LEτ] ] ] ].
            inversion tgtσ1τ1'.
            { 
            exists (σ1 ∩ σ2).
            exists (τ1' ∩ τ2').
            split;[|split].
            * split.
              { rewrite InterMeetLeft.
                apply EqualTypesAreSubtypes_left.
                assumption. }
              { rewrite InterIdem.
                apply SubtyDistrib;
                  apply EqualTypesAreSubtypes_right;
                  assumption. }
            * 

            * 
            * exact (transitivity τ'LEσ σLEτ).
            * assumption.
            * assumption. 
          +  
            { assumption. }
            { 
            assumption.
          + 
          case (IH ) as [x [σ' [τ' [τ'LEστ [tgtσ'τ' xσ']]]]].
          exists x.
          exists σ'.
          case (Ideal_principalElement _ _ τ'LEστ).
          + intros.
            exists τ'.
            split; [|split].
            * transitivity ω; 
              [ exact OmegaTop 
              | apply EqualTypesAreSubtypes_left;
                apply Ω_principal;
                assumption ].
            * assumption.
            * assumption.
          + 
          inversion tgtσ'τ'.
          + exists τ'.


        induction Mτ as [x | M N σ τ Mστ IH | | ].
        - contradict nExσ.
          exists x.
          exists τ.
          exists τ.
          split; [|split].
          + reflexivity.
          + apply tgt_Id.
          + assumption.
        - apply IH.
          intros [x [σ' [τ' [τ'LEστ [tgtσ'τ xσ']]]]].
          set (τ'LEστ_ideal := Ideal_principalElement _ _ τ'LEστ).
          inversion τ'LEστ_ideal.
          + 
          apply nExσ.
          exists x.
          exists σ'.
          exists 



      Theorem FCL_decidable : forall τ, decidable (Γ ⊢ ? : τ).
      Proof.
        intro τ.
        case (path_lemma τ) as [ ωτ |  τ' [ orgτ' τEqτ' ] ].
        - assert (decidable (Γ ⊢ ? : ω)).
          + case (Γ_decidable ω).
            * intros [ x [ σ [ _ [ _ [ _ p ] ] ] ] ].
              left.
              exists x.
              rewrite <- (@OmegaTop σ).
              apply (FCL_Var).
              assumption.
            * intros nExx.
              right.
              intros [M ωM].
              case M as [ x' | M' N' ].


              apply (FCL_Var.
          + intros [ x [ σ [ _ [ _ [ _ p ] ] ] ] ].
            left.
            exists x.
            apply (FCL_if_subtype σ).
            * rewrite ωτ.
              exact OmegaTop.
            * apply FCL_Var.
              assumption.
          + 
        apply FCL_iff_equal.
        case (Γ_decidable τ).
        - intros [ x [ σ [ τ' [ τ'LEτ [ tgtστ' xσ ] ] ] ] ].
          induction   
        
          inversion existsC as [x [τ' [τ'LEτ xτ']]].
          exists x.    
          apply (FCL_ST _ _ τ' τ).
          + apply (FCL_Var).
            assumption.
          + assumption.
        - induction τ.
          + intro.
            *)

    End Inhabitation.


  End FCL.

End Types.

Module HSTy.
  Extraction Language Haskell.
  Module MachineIntVar <: VariableAlphabet.
    Axiom t : Set.
    Axiom eq_dec: forall α β : t, { α = β } + { ~ (α = β) }.

    Include HasUsualEq.
    Include UsualIsEq.
    Extract Constant t => "GHC.Base.Int".
    Extract Constant eq_dec => "(\ x y -> if x GHC.Base.== y then Specif.Coq_left else Specif.Coq_right)".
  End MachineIntVar.

  Module T := MachineIntVar <+ Types.
  Include T.
End HSTy.

Module OcamlTy.
  Extraction Language Ocaml.
  Module MachineIntVar <: VariableAlphabet.
    Axiom t : Set.
    Axiom eq_dec: forall α β : t, { α = β } + { ~ (α = β) }.
    Include HasUsualEq.
    Include UsualIsEq.

    Extract Constant t => "int".
    Extract Constant eq_dec => "(fun x y -> if x = y then Coq_left else Coq_right)".
  End MachineIntVar.

  Module T := MachineIntVar <+ Types.
End OcamlTy.

Module CoqExample.
  Module NatVar <: VariableAlphabet.
    Definition t := nat.
    Require Import Coq.Arith.Peano_dec.
    Definition eq_dec := eq_nat_dec.
    Include HasUsualEq.
    Include UsualIsEq.
  End NatVar.
  Module NatVarTypes := NatVar <+ Types.
  Import NatVarTypes.
  
  Definition α := (Var 1).
  Definition β := (Var 2).
  Definition γ := (Var 3).
  Definition δ := (Var 4).
  Definition ε := (Var 5).
  Definition ζ := (Var 6).
  
  Import NatVarTypes.SubtypeRelation.
  Eval hnf in Subtype_decidable (((α → β) → δ) ∩ ((α → γ) → δ) ∩ (ε → ζ)) (((α → β → ε) → δ) ∩ (ε → ζ)).
End CoqExample.
