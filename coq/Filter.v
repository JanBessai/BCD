
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
            | rt_step _ _ _ τ p' =>
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
            | rt_refl _ _ _ => Refl_case σ
            | rt_trans _ _ _ τ ρ p1 p2 => 
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
        | InducedEq l _ => l
        end.
    Definition EqualTypesAreSubtypes_right: forall σ τ, σ ~= τ -> τ ≤ σ :=
      fun _ _ eqtys => 
        match eqtys with
        | InducedEq _ r => r
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
   
    Instance Arr_Proper_ST : Proper (transp _ (≤) ==> (≤) ==> (≤)) (→).
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
        induction ρLEστ as [ | | | | ].
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
          | Omega => fun _ => Ω ω
          | Var α => fun τ => ↓α[α] τ
          | σ' → τ' => fun τ => ↓[σ'] → [τ'] τ
          | σ' ∩ τ' => fun τ => (↓[σ'] τ) /\ (↓[τ'] τ)
        end
      where "↓[ σ ] τ" := (Ideal σ τ).

      Definition Filter σ: IntersectionType -> Prop :=
        match σ with
          | Omega => Ω
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

      Lemma Ideal_directed:
        forall σ τ ρ, ↓[σ] τ -> ↓[σ] ρ -> (↓[σ] σ) /\ (τ ≤ σ) /\ (ρ ≤ σ).
      Proof.
        intro σ.
        induction σ as [ | | σ₁ IHσ₁ σ₂ IHσ₂ | ]; intros τ ρ στ σρ.
        - apply VariableIdeal_directed; assumption.
        - apply ArrowIdeal_directed; assumption.
        - destruct (IHσ₁ _ _ (proj1 στ) (proj1 σρ)) as [ _ [τσ₁ ρσ₁] ].
          destruct (IHσ₂ _ _ (proj2 στ) (proj2 σρ)) as [ _ [τσ₂ ρσ₂] ].
          split; [ | split ].
          + reflexivity.
          + apply Inter_both; assumption.
          + apply Inter_both; assumption.
        - split; [ | split ]; solve [ auto with SubtypeHints ].
      Qed.

      Lemma Filter_directed:
        forall σ τ ρ, ↑[σ] τ -> ↑[σ] ρ -> (↑[σ] σ) /\ (σ ≤ τ) /\ (σ ≤ ρ).
      Proof.
        intros σ τ ρ στ σρ.
        destruct (Ideal_directed τ σ σ (Filter_Ideal _ _ στ) (Filter_Ideal _ _ στ))
          as [ _ [ στ' _ ] ].
        destruct (Ideal_directed ρ σ σ (Filter_Ideal _ _ σρ) (Filter_Ideal _ _ σρ))
          as [ _ [ σρ' _ ] ].        
        split; [ | split ]; auto using reflexivity.
      Qed.
        
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

      Corollary decide_subtypes:
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

      Fact organized_inter: forall σ τ, Organized (σ ∩ τ) -> Organized σ /\ Organized τ.
      Proof.
        intros σ τ orgστ.
        inversion orgστ as [ στ pathστ | σ' τ' pathσ' orgτ' ].
        - inversion pathστ.
        - split.
          + apply Organized_Path.
            assumption.
          + assumption.
      Qed.

      Fact inter_organized:
        forall σ τ, Organized σ -> Organized τ ->
               { στ : _ | Organized στ /\ ((σ ∩ τ) ~= στ) }.
      Proof.
        intro σ.
        induction σ as [ α | σ' IHσ' τ' IHτ' | σ₁ IHσ₁ σ₂ IHσ₂ | ];
          intros τ orgσ orgτ.
        - exists ((Var α) ∩ τ).
          split.
          + apply Organized_Inter.
            * apply Path_Var.
            * assumption.
          + reflexivity.
        - exists ((σ' → τ') ∩ τ).
          split.
          + apply Organized_Inter.
            * inversion orgσ; assumption.
            * assumption.
          + reflexivity.
        - destruct (IHσ₂ _ (proj2 (organized_inter _ _ orgσ)) orgτ)
            as [ σ₂τ [ orgσ₂τ σ₂τ_eq ]].
          exists (σ₁ ∩ σ₂τ).
          split.
          + apply Organized_Inter.
            * inversion orgσ as [ σ' pathσ' | ].
              { inversion pathσ'. }
              { assumption. }
            * assumption.
          + rewrite associativity.
            rewrite σ₂τ_eq.
            reflexivity.
        - contradict orgσ.
          unfold not; intro orgσ.
          inversion orgσ as [ σ' pathσ' | ].
          inversion pathσ'.
      Defined.
          
      Fact tgt_organized:
        forall σ τ, Organized τ -> { τ' : _ | (Organized τ') /\ ((σ → τ) ~= τ') }.
      Proof.
        intros σ τ.
        revert σ.
        induction τ as [ α | σ' IHσ' τ' IHτ' | τ₁ IHτ₁ τ₂ IHτ₂ | ];
          intros σ orgτ.
        - exists (σ → Var α).
          split.
          + apply Organized_Path.
            apply Path_Arr.
            apply Path_Var.
          + reflexivity.
        - exists (σ → σ' → τ').
          split.
          + apply Organized_Path.
            inversion orgτ as [ τ pathτ | ].
            apply Path_Arr.
            assumption.
          + reflexivity.
        - destruct (IHτ₁ σ (proj1 (organized_inter _ _ orgτ)))
            as [ στ₁ [ orgστ₁ στ₁_eq ] ].
          destruct (IHτ₂ σ (proj2 (organized_inter _ _ orgτ)))
            as [ στ₂ [ orgστ₂ στ₂_eq ] ].
          destruct (inter_organized _ _ orgστ₁ orgστ₂)
            as [ στ₁τ₂ [ orgστ₁τ₂ στ₁τ₂_eq ] ].
          exists στ₁τ₂.
          split.
          + assumption.
          + split.
            * transitivity ((σ → τ₁) ∩ (σ → τ₂)).
              { apply Inter_both.
                - apply CoContra.
                  + reflexivity.
                  + apply InterMeetLeft.
                - apply CoContra.
                  + reflexivity.
                  + apply InterMeetRight.
              }
              { rewrite στ₁_eq.
                rewrite στ₂_eq.
                rewrite στ₁τ₂_eq.
                reflexivity. }
            * rewrite <- στ₁τ₂_eq.
              rewrite <- στ₁_eq.
              rewrite <- στ₂_eq.
              apply InterDistrib.
        - contradict orgτ.
          unfold not; intro orgτ.
          inversion orgτ as [ τ' pathτ' | ]; inversion pathτ'.
      Qed.

     
      Definition organization_lemma: 
        forall τ, (τ ~= ω) + ({ τ': _ | Organized τ' /\ (τ ~= τ') }).
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
            case (inter_organized _ _ orgτ'1 orgτ'2) as [ τ' [ τ'org τ'Eq ] ].
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
        ↓[τ] (ρ1 ∩ ρ2) -> 
        (ρ1 ≤ τ) \/ (ρ2 ≤ τ).
      Proof.
        intro τ.
        induction τ as [ | σ IHσ τ' IHτ' | | ]; 
          intros pτ ρ1 ρ2 ρ1ρ2LEτ;
          try solve [ inversion pτ ];
          simpl in ρ1ρ2LEτ.
        - inversion ρ1ρ2LEτ.
          + left.
            apply Ideal_principal.
            assumption.
          + right.
            apply Ideal_principal.
            assumption.
        - inversion ρ1ρ2LEτ as [ | | | | ? ? ρ3 ρ4 aiρ1 aiρ2 ρ3ρ4LEτ' ].
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
              case (IHτ' (or_intror pτ'') ρ3 ρ4
                         (Ideal_principalElement _ _ ρ3ρ4LEτ'))
                as [ ρ3LEτ' | ρ4LEτ' ].
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
        (forall ρ1 ρ2, ↓[τ] (ρ1 ∩ ρ2) -> (ρ1 ≤ τ) \/ (ρ2 ≤ τ)) ->
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
        - assert (τprimecond : forall ρ1 ρ2, ↓[τ] (ρ1 ∩ ρ2) -> (ρ1 ≤ τ) \/ (ρ2 ≤ τ)).
          + intros ρ1 ρ2 ρ1ρ2LEτ.
            assert (ρ1ρ2LEστ : (σ → ρ1) ∩ (σ → ρ2) ≤ σ → τ).
            * transitivity (σ → ρ1 ∩ ρ2).
              { apply InterDistrib. } 
              { apply CoContra.
                - reflexivity.
                - apply Ideal_principal.
                  assumption. }
            * case (τprime _ _ (Ideal_principalElement _ _ ρ1ρ2LEστ))
                as [ σρLEστ | σρLEστ ];
                [ left | right ];
                set (σρLEστ' := Ideal_principalElement _ _ σρLEστ);
                inversion σρLEστ';
                solve [ apply (transitivity OmegaTop);
                  apply (EqualTypesAreSubtypes_left);
                  apply (Ω_principal);
                  assumption
                | assumption ].
          + case (IHτ τprimecond)
              as [ τ' [ τEqτ' [ ωτ' | pτ' ] ] ].
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
        - case (decide_subtypes ρ1 ρ2);
            [|case (decide_subtypes ρ2 ρ1)].
          + intro ρ1LEρ2.
            assert (primecond :
              (forall ρ1' ρ2', ↓[ρ1] (ρ1' ∩ ρ2') -> (ρ1' ≤ ρ1) \/ (ρ2' ≤ ρ1))).
            { intros ρ1' ρ2' ρ1'ρ2'LE.
              set (ρ1'ρ2'LE' := Ideal_principal _ _ ρ1'ρ2'LE).
              rewrite (@InterIdem ρ1) in ρ1'ρ2'LE'.
              rewrite (SubtyDistrib (reflexivity ρ1) (ρ1LEρ2)) in ρ1'ρ2'LE'.
              case (τprime ρ1' ρ2' (Ideal_principalElement _ _ ρ1'ρ2'LE'));
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
              (forall ρ1' ρ2', ↓[ρ2] (ρ1' ∩ ρ2') -> (ρ1' ≤ ρ2) \/ (ρ2' ≤ ρ2))).
            { intros ρ1' ρ2' ρ1'ρ2'LE.
              set (ρ1'ρ2'LE' := Ideal_principal _ _ ρ1'ρ2'LE).
              rewrite (@InterIdem ρ2) in ρ1'ρ2'LE'.
              rewrite (SubtyDistrib (ρ1LEρ2) (reflexivity ρ2)) in ρ1'ρ2'LE'.
              case (τprime ρ1' ρ2' (Ideal_principalElement _ _ ρ1'ρ2'LE'));
                [ left | right ];
                solve [ transitivity (ρ1 ∩ ρ2); [ assumption | apply InterMeetRight ] ]. }
            case (IHρ2 primecond)
              as [ τ' [ ρ2Eqτ' [ ωτ' | pτ' ] ] ].
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
        (forall ρ1 ρ2, ↓[τ] (ρ1 ∩ ρ2) -> (ρ1 ≤ τ) \/ (ρ2 ≤ τ)) <->
        exists τ', (τ ~= τ') /\ ((τ' ~= ω) \/ Path τ').
      Proof.
        split.
        - apply Ideal_prime_path.
        - intros [τ' [ τEqτ' primecond ]] ρ1 ρ2 ρ1ρ2LEτ.
          case (Path_Ideal_prime τ' primecond ρ1 ρ2).
          + apply Ideal_principalElement.
            rewrite <- τEqτ'.
            apply Ideal_principal.
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
        { τ' | InOrganized σ τ' /\ (τ' ≤ τ) }.
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
            - apply Ideal_principalElement.
              assumption. }
          destruct (decide_subtypes ρ1 τ) as [ρ1LEτ | ρ1NLEτ ].
          + exists ρ1.
            split.
            * apply InOrg_Here.
              assumption.
            * assumption.
          + assert (ρ2LEτ : ρ2 ≤ τ).
            { destruct ρ1Orρ2LEτ as [ ρ1LEτ | ].
              - contradict ρ1LEτ; assumption.
              - assumption.
            }
            case (IHρ2 τ (proj2 (organized_inter _ _ oσ)) pτ ρ2LEτ)
              as [ τ' [inorgρ2τ' τ'LEτ] ].
            exists τ'.
            split.
            * apply InOrg_There.
              assumption.
            * assumption.
        - contradict oσ.
          unfold not; intro oσ.
          inversion oσ as [ ? pω |].
          inversion pω.
      Defined.
  
    End BetaLemmas.

   
  End SubtypeRelation.
End Types.

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

  Example pick_ideal: IntersectionType.
  Proof.
    set (τ := (β → γ ∩ α) ∩ (δ → ε ∩ α)).
    eapply proj1_sig.
    apply (Pick_Ideal δ τ (fun σ' p => Filter_decidable δ σ')). 
  Defined.

  Example subtype_proof :=
    decide_subtypes
      (((α → β) → δ) ∩ ((α → γ) → δ) ∩ (ε → ζ) ∩ (ε → α))
      (((α → β ∩ ε) → δ) ∩ (ε → ζ ∩ α)).

  Example non_subtype_proof :=
    decide_subtypes
      (((α → β) → δ) ∩ ((α → γ) → δ) ∩ (ε → ζ) ∩ (ε → α))
      (((α → β → ε) → δ) ∩ (ε → ζ ∩ α)).
  
  (* Run this:  Eval compute in subtype_proof *)
End CoqExample.

