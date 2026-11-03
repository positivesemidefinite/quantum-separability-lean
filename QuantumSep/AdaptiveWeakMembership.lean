import QuantumSep.AdaptiveOptimization
import QuantumSep.SeparableWeakMembership

/-!
# End-to-end adaptive weak membership

This file turns the concrete product optimizer into a fresh-coin support
oracle, amplifies every call, and composes the calls adaptively through the
finite Frank--Wolfe execution.
-/

namespace QuantumSep

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

noncomputable section

/-- A separable output, with feasibility carried in the type and erased by
the measurable projection. -/
def SeparableOracleOutput (d : ℕ) :=
  {P : MatrixHilbert d // P ∈ separableStates d}

instance (d : ℕ) : MeasurableSpace (SeparableOracleOutput d) :=
  MeasurableSpace.comap Subtype.val inferInstance

/-- Operational contract for a single fresh support-oracle call.  Unlike an
external assumption, this structure will be instantiated below from the two
already proved concrete optimizer branches. -/
structure MeasurableSupportOracle (d : ℕ) (tau : ℝ) where
  Seed : Type
  seedMeasurableSpace : MeasurableSpace Seed
  seedMeasure : @Measure Seed seedMeasurableSpace
  seedProbability :
    @IsProbabilityMeasure Seed seedMeasurableSpace seedMeasure
  output : SeparableOracleQuery d × Seed → SeparableOracleOutput d
  core : Set (SeparableOracleQuery d × Seed)
  output_measurable :
    @Measurable
      (SeparableOracleQuery d × Seed) (SeparableOracleOutput d)
      (@Prod.instMeasurableSpace
        (SeparableOracleQuery d) Seed inferInstance seedMeasurableSpace)
      inferInstance output
  core_measurable :
    @MeasurableSet
      (SeparableOracleQuery d × Seed)
      (@Prod.instMeasurableSpace
        (SeparableOracleQuery d) Seed inferInstance seedMeasurableSpace)
      core
  core_probability :
    ∀ A,
      @Measure.real Seed seedMeasurableSpace seedMeasure
        {seed | (A, seed) ∈ core} ≥ 2 / 3
  core_correct :
    ∀ A seed, (A, seed) ∈ core →
      ∀ P ∈ separableStates d,
        ⟪A.1, P⟫ ≤ ⟪A.1, (output (A, seed)).1⟫ + tau

/-- The direct branch as a measurable support oracle. -/
def directMeasurableSupportOracle
    (ptas : DenseMaxFourCSPPTASContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d) :
    MeasurableSupportOracle d tau where
  Seed := ptas.Seed
  seedMeasurableSpace := ptas.seedMeasurableSpace
  seedMeasure := ptas.seedMeasure
  seedProbability := ptas.seedProbability
  output := fun z =>
    ⟨directSeparableOracleOutput ptas tau htau d hd z,
      directSeparableOracleOutput_mem
        ptas tau htau d hd z.1 z.2⟩
  core := {z | directSeparableOracleCore ptas tau htau d hd z}
  output_measurable := by
    exact (measurable_directSeparableOracleOutput
      ptas tau htau d hd).subtype_mk
  core_measurable :=
    measurableSet_directSeparableOracleCore ptas tau htau d hd
  core_probability := by
    intro A
    change ptas.seedMeasure.real
      {seed |
        directSeparableOracleCore ptas tau htau d hd (A, seed)} ≥
      2 / 3
    have h :=
      directSeparableOracleCore_probability
        ptas tau htau d hd A
    exact (show (2 / 3 : ℝ) ≤ 5 / 6 by norm_num).trans h
  core_correct :=
    directSeparableOracleCore_correct ptas tau htau d hd

/-- The instantiated high-dimensional branch as a measurable support
oracle. -/
def highMeasurableSupportOracle
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d) :
    MeasurableSupportOracle d tau := by
  let haar := efficientHaarPairProcedure sampler d
  exact {
    Seed := haar.Seed × ptas.Seed
    seedMeasurableSpace :=
      @Prod.instMeasurableSpace haar.Seed ptas.Seed
        haar.seedMeasurableSpace ptas.seedMeasurableSpace
    seedMeasure :=
      @Measure.prod haar.Seed ptas.Seed
        haar.seedMeasurableSpace ptas.seedMeasurableSpace
        haar.seedMeasure ptas.seedMeasure
    seedProbability := by
      letI : MeasurableSpace haar.Seed := haar.seedMeasurableSpace
      letI : IsProbabilityMeasure haar.seedMeasure := haar.seedProbability
      letI : MeasurableSpace ptas.Seed := ptas.seedMeasurableSpace
      letI : IsProbabilityMeasure ptas.seedMeasure := ptas.seedProbability
      infer_instance
    output := fun z =>
      ⟨highSeparableOracleOutput
          sampler ptas hc tau htau d hlarge z,
        highSeparableOracleOutput_mem
          sampler ptas hc tau htau d hlarge z⟩
    core := {z |
      highSeparableOracleCore
        sampler ptas hc tau htau d hlarge z}
    output_measurable := by
      exact (measurable_highSeparableOracleOutput
        sampler ptas hc tau htau d hlarge).subtype_mk
    core_measurable :=
      measurableSet_highSeparableOracleCore
        sampler ptas hc tau htau d hlarge
    core_probability :=
      highSeparableOracleCore_probability
        sampler ptas hc tau htau d hlarge
    core_correct :=
      highSeparableOracleCore_correct
        sampler ptas hc tau htau d hlarge
  }

/-- Dimension-adaptive concrete support oracle.  The branch choice is
deterministic; both branches have already been instantiated from the three
authorized analytic/algorithmic contracts. -/
def adaptiveMeasurableSupportOracle
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d) :
    MeasurableSupportOracle d tau :=
  if hlarge : mainDimensionCutoff hc tau ≤ d then
    highMeasurableSupportOracle
      sampler ptas hc tau htau d hlarge
  else
    directMeasurableSupportOracle ptas tau htau d hd

/-- Explicit number of Frank--Wolfe calls used by weak membership. -/
def weakMembershipIterations (eta : ℝ) : ℕ :=
  max 1 (Nat.ceil (256 / eta ^ 2))

theorem weakMembershipIterations_one_le
    (eta : ℝ) :
    1 ≤ weakMembershipIterations eta := by
  unfold weakMembershipIterations
  exact le_max_left _ _

theorem weakMembershipIterations_bound
    (eta : ℝ) :
    256 / eta ^ 2 ≤ (weakMembershipIterations eta : ℝ) := by
  have hceil :
      256 / eta ^ 2 ≤
        (Nat.ceil (256 / eta ^ 2) : ℝ) :=
    Nat.le_ceil _
  have hnat :
      Nat.ceil (256 / eta ^ 2) ≤
        weakMembershipIterations eta := by
    unfold weakMembershipIterations
    exact le_max_right _ _
  exact hceil.trans (by exact_mod_cast hnat)

/-- Deterministic tie-breaking maximum over `n+1` candidates. -/
def bestOracleOutput
    {d : ℕ} (A : SeparableOracleQuery d) :
    (n : ℕ) → (Fin (n + 1) → SeparableOracleOutput d) →
      SeparableOracleOutput d
  | 0, trial => trial 0
  | n + 1, trial =>
      let previous :=
        bestOracleOutput A n (fun i => trial i.castSucc)
      let last := trial (Fin.last (n + 1))
      if ⟪A.1, previous.1⟫ ≤ ⟪A.1, last.1⟫ then last
      else previous

theorem bestOracleOutput_score_max
    {d : ℕ} (A : SeparableOracleQuery d)
    (n : ℕ) (trial : Fin (n + 1) → SeparableOracleOutput d)
    (i : Fin (n + 1)) :
    ⟪A.1, (trial i).1⟫ ≤
      ⟪A.1, (bestOracleOutput A n trial).1⟫ := by
  induction n with
  | zero =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl
  | succ n ih =>
      by_cases hilast : i = Fin.last (n + 1)
      · subst i
        simp only [bestOracleOutput]
        split_ifs with h
        · exact le_rfl
        · exact le_of_not_ge h
      · let j : Fin (n + 1) :=
          ⟨i.val, by
            have hi : i.val < n + 2 := i.isLt
            have hne : i.val ≠ n + 1 := by
              intro heq
              apply hilast
              apply Fin.ext
              simpa using heq
            omega⟩
        have hij : j.castSucc = i := by
          apply Fin.ext
          rfl
        have hprev :=
          ih (fun k : Fin (n + 1) => trial k.castSucc) j
        simp only [bestOracleOutput]
        split_ifs with h
        · calc
            ⟪A.1, (trial i).1⟫ =
                ⟪A.1, (trial j.castSucc).1⟫ := by rw [hij]
            _ ≤
                ⟪A.1,
                  (bestOracleOutput A n
                    (fun k => trial k.castSucc)).1⟫ := hprev
            _ ≤ ⟪A.1, (trial (Fin.last (n + 1))).1⟫ := h
        · simpa [hij] using hprev

theorem measurable_bestOracleOutput
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ}
    (A : Ω → SeparableOracleQuery d)
    (hA : Measurable A)
    (n : ℕ)
    (trial : Ω → Fin (n + 1) → SeparableOracleOutput d)
    (htrial : ∀ i, Measurable fun ω => trial ω i) :
    Measurable fun ω => bestOracleOutput (A ω) n (trial ω) := by
  classical
  induction n with
  | zero =>
      simpa [bestOracleOutput] using htrial 0
  | succ n ih =>
      let previous : Ω → SeparableOracleOutput d :=
        fun ω =>
          bestOracleOutput (A ω) n
            (fun i => trial ω i.castSucc)
      have hprevious : Measurable previous :=
        ih (fun ω i => trial ω i.castSucc)
          (fun i => htrial i.castSucc)
      let last : Ω → SeparableOracleOutput d :=
        fun ω => trial ω (Fin.last (n + 1))
      have hlast : Measurable last :=
        htrial (Fin.last (n + 1))
      have hscorePrevious :
          Measurable fun ω => ⟪(A ω).1, (previous ω).1⟫ := by
        fun_prop
      have hscoreLast :
          Measurable fun ω => ⟪(A ω).1, (last ω).1⟫ := by
        fun_prop
      letI : DecidablePred
          (fun ω =>
            ⟪(A ω).1, (previous ω).1⟫ ≤
              ⟪(A ω).1, (last ω).1⟫) :=
        Classical.decPred _
      have hite :=
        @Measurable.ite Ω (SeparableOracleOutput d)
          last previous inferInstance inferInstance
          (fun ω =>
            ⟪(A ω).1, (previous ω).1⟫ ≤
              ⟪(A ω).1, (last ω).1⟫)
          (Classical.decPred _)
          (measurableSet_le hscorePrevious hscoreLast)
          hlast hprevious
      simpa [bestOracleOutput, previous, last] using hite

/-- At least one certified repetition implies that the selected maximum is
correct. -/
theorem bestOracleOutput_correct
    {d : ℕ} {tau : ℝ}
    (oracle : MeasurableSupportOracle d tau)
    (A : SeparableOracleQuery d)
    (n : ℕ) (seeds : Fin (n + 1) → oracle.Seed)
    (hgood : ∃ i, (A, seeds i) ∈ oracle.core) :
    ∀ P ∈ separableStates d,
      ⟪A.1, P⟫ ≤
        ⟪A.1,
          (bestOracleOutput A n
            (fun i => oracle.output (A, seeds i))).1⟫ + tau := by
  obtain ⟨i, hi⟩ := hgood
  intro P hP
  have hcore := oracle.core_correct A (seeds i) hi P hP
  have hmax :=
    bestOracleOutput_score_max A n
      (fun j => oracle.output (A, seeds j)) i
  linarith

/-- The measurable event that at least one repetition hits the certification
core. -/
theorem measurableSet_exists_oracleCore
    {d : ℕ} {tau : ℝ}
    (oracle : MeasurableSupportOracle d tau)
    (n : ℕ) :
    @MeasurableSet
      (SeparableOracleQuery d × (Fin (n + 1) → oracle.Seed))
      (@Prod.instMeasurableSpace
        (SeparableOracleQuery d) (Fin (n + 1) → oracle.Seed)
        inferInstance
        (@MeasurableSpace.pi (Fin (n + 1))
          (fun _ => oracle.Seed) fun _ => oracle.seedMeasurableSpace))
      {z | ∃ i, (z.1, z.2 i) ∈ oracle.core} := by
  letI : MeasurableSpace oracle.Seed := oracle.seedMeasurableSpace
  have heq :
      {z : SeparableOracleQuery d × (Fin (n + 1) → oracle.Seed) |
        ∃ i, (z.1, z.2 i) ∈ oracle.core} =
        ⋃ i, {z | (z.1, z.2 i) ∈ oracle.core} := by
    ext z
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun i =>
    oracle.core_measurable.preimage
      (measurable_fst.prodMk
        ((measurable_pi_apply i).comp measurable_snd))

/-- Independent coins for `n+1` repetitions of one oracle call. -/
def oracleRepetitionMeasure
    {d : ℕ} {tau : ℝ}
    (oracle : MeasurableSupportOracle d tau) (n : ℕ) :
    @Measure (Fin (n + 1) → oracle.Seed)
      (@MeasurableSpace.pi (Fin (n + 1))
        (fun _ => oracle.Seed) fun _ => oracle.seedMeasurableSpace) :=
  @Measure.pi (Fin (n + 1)) (fun _ => oracle.Seed)
    inferInstance (fun _ => oracle.seedMeasurableSpace)
    (fun _ => oracle.seedMeasure)

theorem oracleRepetitionMeasure_probability
    {d : ℕ} {tau : ℝ}
    (oracle : MeasurableSupportOracle d tau) (n : ℕ) :
    @IsProbabilityMeasure (Fin (n + 1) → oracle.Seed)
      (@MeasurableSpace.pi (Fin (n + 1))
        (fun _ => oracle.Seed) fun _ => oracle.seedMeasurableSpace)
      (oracleRepetitionMeasure oracle n) := by
  letI : MeasurableSpace oracle.Seed := oracle.seedMeasurableSpace
  letI : IsProbabilityMeasure oracle.seedMeasure :=
    oracle.seedProbability
  change IsProbabilityMeasure
    (@Measure.pi (Fin (n + 1)) (fun _ => oracle.Seed)
      inferInstance (fun _ => oracle.seedMeasurableSpace)
      (fun _ => oracle.seedMeasure))
  infer_instance

/-- Output selected from `n+1` independent repetitions. -/
def amplifiedOracleOutput
    {d : ℕ} {tau : ℝ}
    (oracle : MeasurableSupportOracle d tau) (n : ℕ)
    (z : SeparableOracleQuery d × (Fin (n + 1) → oracle.Seed)) :
    SeparableOracleOutput d :=
  bestOracleOutput z.1 n fun i => oracle.output (z.1, z.2 i)

theorem measurable_amplifiedOracleOutput
    {d : ℕ} {tau : ℝ}
    (oracle : MeasurableSupportOracle d tau) (n : ℕ) :
    @Measurable
      (SeparableOracleQuery d × (Fin (n + 1) → oracle.Seed))
      (SeparableOracleOutput d)
      (@Prod.instMeasurableSpace
        (SeparableOracleQuery d) (Fin (n + 1) → oracle.Seed)
        inferInstance
        (@MeasurableSpace.pi (Fin (n + 1))
          (fun _ => oracle.Seed) fun _ => oracle.seedMeasurableSpace))
      inferInstance
      (amplifiedOracleOutput oracle n) := by
  letI : MeasurableSpace oracle.Seed := oracle.seedMeasurableSpace
  unfold amplifiedOracleOutput
  exact measurable_bestOracleOutput
    (fun z : SeparableOracleQuery d ×
      (Fin (n + 1) → oracle.Seed) => z.1)
    measurable_fst n
    (fun z i => oracle.output (z.1, z.2 i))
    (fun i =>
      oracle.output_measurable.comp
        (measurable_fst.prodMk
          ((measurable_pi_apply i).comp measurable_snd)))

/-- Fixed-query amplification probability. -/
theorem amplifiedOracleCore_probability
    {d : ℕ} {tau : ℝ}
    (oracle : MeasurableSupportOracle d tau)
    (n : ℕ) (A : SeparableOracleQuery d) :
    @Measure.real (Fin (n + 1) → oracle.Seed)
      (@MeasurableSpace.pi (Fin (n + 1))
        (fun _ => oracle.Seed) fun _ => oracle.seedMeasurableSpace)
      (oracleRepetitionMeasure oracle n)
      {seeds | ∃ i, (A, seeds i) ∈ oracle.core} ≥
        1 - (1 / 3 : ℝ) ^ (n + 1) := by
  letI : MeasurableSpace oracle.Seed := oracle.seedMeasurableSpace
  letI : IsProbabilityMeasure oracle.seedMeasure :=
    oracle.seedProbability
  let oneCore : Set oracle.Seed :=
    {seed | (A, seed) ∈ oracle.core}
  have honeCore : MeasurableSet oneCore :=
    oracle.core_measurable.preimage
      (measurable_const.prodMk measurable_id)
  have h :=
    measureReal_exists_core_ge oracle.seedMeasure oneCore honeCore
      (n + 1) (oracle.core_probability A)
  simpa [oracleRepetitionMeasure, oneCore] using h

/-- Amplification remains valid when the query is selected measurably from
an independent earlier random state. -/
theorem amplifiedOracleCore_probability_random
    {S : Type*} [MeasurableSpace S]
    (mu : Measure S) [IsProbabilityMeasure mu]
    {d : ℕ} {tau : ℝ}
    (oracle : MeasurableSupportOracle d tau)
    (n : ℕ)
    (A : S → SeparableOracleQuery d)
    (hA : Measurable A) :
    let repetitionMeasure := oracleRepetitionMeasure oracle n
    @Measure.real
      (S × (Fin (n + 1) → oracle.Seed))
      (@Prod.instMeasurableSpace
        S (Fin (n + 1) → oracle.Seed) inferInstance
        (@MeasurableSpace.pi (Fin (n + 1))
          (fun _ => oracle.Seed) fun _ => oracle.seedMeasurableSpace))
      (@Measure.prod S (Fin (n + 1) → oracle.Seed)
        inferInstance
        (@MeasurableSpace.pi (Fin (n + 1))
          (fun _ => oracle.Seed) fun _ => oracle.seedMeasurableSpace)
        mu repetitionMeasure)
      {z | ∃ i, (A z.1, z.2 i) ∈ oracle.core} ≥
        1 - (1 / 3 : ℝ) ^ (n + 1) := by
  dsimp only
  letI : MeasurableSpace oracle.Seed := oracle.seedMeasurableSpace
  let repetitionMeasure := oracleRepetitionMeasure oracle n
  letI : IsProbabilityMeasure repetitionMeasure :=
    oracleRepetitionMeasure_probability oracle n
  let event :
      Set (S × (Fin (n + 1) → oracle.Seed)) :=
    {z | ∃ i, (A z.1, z.2 i) ∈ oracle.core}
  have hevent : MeasurableSet event := by
    have hbase := measurableSet_exists_oracleCore oracle n
    exact hbase.preimage
      ((hA.comp measurable_fst).prodMk measurable_snd)
  apply measureReal_prod_ge_of_forall
    mu repetitionMeasure event hevent
      (1 - (1 / 3 : ℝ) ^ (n + 1))
  intro s
  simpa [event] using amplifiedOracleCore_probability oracle n (A s)

/-- Two oracle histories which agree before `t` have the same Frank--Wolfe
iterate at `t`. -/
theorem separableFrankWolfeIterate_congr_at
    {d : ℕ} (omega₁ omega₂ : ℕ → MatrixHilbert d) :
    ∀ t,
      (∀ s, 1 ≤ s → s < t → omega₁ s = omega₂ s) →
      separableFrankWolfeIterate omega₁ t =
        separableFrankWolfeIterate omega₂ t := by
  intro t
  induction t with
  | zero =>
      intro _h
      rfl
  | succ n ih =>
      intro h
      by_cases hn : n = 0
      · simp [separableFrankWolfeIterate, hn]
      · rw [separableFrankWolfeIterate, separableFrankWolfeIterate]
        simp only [dif_neg hn]
        rw [ih (fun s hs hsn =>
          h s hs (hsn.trans (Nat.lt_succ_self n)))]
        rw [h n (Nat.one_le_iff_ne_zero.2 hn)
          (Nat.lt_succ_self n)]

theorem separableFrankWolfeIterate_update_same
    {d : ℕ} (omega : ℕ → MatrixHilbert d)
    (t : ℕ) (output : MatrixHilbert d) :
    separableFrankWolfeIterate
        (Function.update omega t output) t =
      separableFrankWolfeIterate omega t := by
  apply separableFrankWolfeIterate_congr_at
  intro s _hs hst
  simp [Function.update, show s ≠ t by omega]

theorem measurable_separableFrankWolfeIterate
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ}
    (omega : Ω → ℕ → MatrixHilbert d)
    (homega : ∀ t, Measurable fun z => omega z t) :
    ∀ t, Measurable fun z =>
      separableFrankWolfeIterate (omega z) t := by
  intro t
  induction t with
  | zero =>
      exact measurable_const
  | succ n ih =>
      by_cases hn : n = 0
      · simpa [separableFrankWolfeIterate, hn] using
          (measurable_const :
            Measurable fun _z : Ω => initialSeparableState d)
      · simp only [separableFrankWolfeIterate, dif_neg hn]
        fun_prop

/-- Data and proof invariant after all calls with indices `< t` have been
processed. -/
def CertifiedWeakState
    (d : ℕ) (rho : MatrixHilbert d) (tau : ℝ) (t : ℕ) :=
  {x : (ℕ → MatrixHilbert d) × Bool //
    (∀ s, 1 ≤ s → s < t → x.1 s ∈ separableStates d) ∧
    (x.2 = true →
      ∀ s, 1 ≤ s → s < t →
        separableOracleCallSucceeds rho x.1 tau s)}

instance (d : ℕ) (rho : MatrixHilbert d) (tau : ℝ) (t : ℕ) :
    MeasurableSpace (CertifiedWeakState d rho tau t) :=
  MeasurableSpace.comap Subtype.val inferInstance

def CertifiedWeakState.omega
    {d : ℕ} {rho : MatrixHilbert d} {tau : ℝ} {t : ℕ}
    (state : CertifiedWeakState d rho tau t) :
    ℕ → MatrixHilbert d :=
  state.1.1

def CertifiedWeakState.good
    {d : ℕ} {rho : MatrixHilbert d} {tau : ℝ} {t : ℕ}
    (state : CertifiedWeakState d rho tau t) : Bool :=
  state.1.2

theorem CertifiedWeakState.output_mem
    {d : ℕ} {rho : MatrixHilbert d} {tau : ℝ} {t : ℕ}
    (state : CertifiedWeakState d rho tau t)
    {s : ℕ} (hs : 1 ≤ s) (hst : s < t) :
    state.omega s ∈ separableStates d :=
  state.2.1 s hs hst

theorem CertifiedWeakState.calls_correct
    {d : ℕ} {rho : MatrixHilbert d} {tau : ℝ} {t : ℕ}
    (state : CertifiedWeakState d rho tau t)
    (hgood : state.good = true)
    {s : ℕ} (hs : 1 ≤ s) (hst : s < t) :
    separableOracleCallSucceeds rho state.omega tau s :=
  state.2.2 hgood s hs hst

/-- Initial state before call `1`. -/
def initialCertifiedWeakState
    (d : ℕ) (rho : MatrixHilbert d) (tau : ℝ) :
    CertifiedWeakState d rho tau 1 :=
  ⟨((fun _ => initialSeparableState d), true),
    by
      constructor
      · intro s hs hlt
        omega
      · intro _h s hs hlt
        omega⟩

/-- The normalized query determined by a certified state. -/
def certifiedStateQuery
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrhoHerm : rho ∈ hermitianMatrices d)
    (hrhoNorm : ‖rho‖ ≤ 1)
    (tau : ℝ) (t : ℕ) (ht : 1 ≤ t)
    (state : CertifiedWeakState d rho tau t) :
    SeparableOracleQuery d := by
  let sigma := separableFrankWolfeIterate state.omega t
  have hsigmaMem : sigma ∈ separableStates d :=
    separableFrankWolfeIterate_mem_at state.omega t
      (fun s hs hst => state.output_mem hs hst)
  have hsigmaHerm : sigma ∈ hermitianMatrices d :=
    separableStates_hermitian d hsigmaMem
  refine ⟨separableOracleDirection rho sigma, ?_, ?_⟩
  · exact separableOracleDirection_hermitian
      hrhoHerm hsigmaHerm
  · by_cases heq : rho = sigma
    · simp [separableOracleDirection, heq]
    · rw [separableOracleDirection_norm heq]

theorem measurable_certifiedStateQuery
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrhoHerm : rho ∈ hermitianMatrices d)
    (hrhoNorm : ‖rho‖ ≤ 1)
    (tau : ℝ) (t : ℕ) (ht : 1 ≤ t) :
    Measurable
      (certifiedStateQuery d hd rho hrhoHerm hrhoNorm tau t ht) := by
  apply Measurable.subtype_mk
  let stateValue :
      CertifiedWeakState d rho tau t →
        (ℕ → MatrixHilbert d) × Bool :=
    fun state => state.1
  have hstateValue : Measurable stateValue := measurable_subtype_coe
  have homega : ∀ s, Measurable fun
      state : CertifiedWeakState d rho tau t =>
      state.omega s := by
    intro s
    exact (measurable_pi_apply s).comp hstateValue.fst
  have hsigma : Measurable fun
      state : CertifiedWeakState d rho tau t =>
      separableFrankWolfeIterate state.omega t :=
    measurable_separableFrankWolfeIterate
      (fun state : CertifiedWeakState d rho tau t =>
        state.omega) homega t
  change Measurable fun state : CertifiedWeakState d rho tau t =>
    ‖rho - separableFrankWolfeIterate state.omega t‖⁻¹ •
      (rho - separableFrankWolfeIterate state.omega t)
  fun_prop

/-- One amplified adaptive transition.  The proof component records both
feasibility and the meaning of the accumulated good flag. -/
def certifiedWeakTransition
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrhoHerm : rho ∈ hermitianMatrices d)
    (hrhoNorm : ‖rho‖ ≤ 1)
    (tau : ℝ)
    (oracle : MeasurableSupportOracle d tau)
    (repetitionIndex : ℕ)
    (t : ℕ) (ht : 1 ≤ t)
    (z : CertifiedWeakState d rho tau t ×
      (Fin (repetitionIndex + 1) → oracle.Seed)) :
    CertifiedWeakState d rho tau (t + 1) := by
  classical
  let state := z.1
  let query :=
    certifiedStateQuery d hd rho hrhoHerm hrhoNorm tau t ht state
  let selected :=
    amplifiedOracleOutput oracle repetitionIndex (query, z.2)
  let freshGood : Prop :=
    ∃ i, (query, z.2 i) ∈ oracle.core
  let sigma := separableFrankWolfeIterate state.omega t
  let callGood : Prop := rho = sigma ∨ freshGood
  let nextGood : Bool := if callGood then state.good else false
  let nextOmega : ℕ → MatrixHilbert d :=
    Function.update state.omega t selected.1
  refine ⟨(nextOmega, nextGood), ?_, ?_⟩
  · intro s hs hst
    by_cases hstEq : s = t
    · subst s
      simp [nextOmega, selected]
    · simp [nextOmega, hstEq]
      exact state.output_mem hs (by omega)
  · intro hgood s hs hst
    have hcallGood : callGood := by
      by_contra hnot
      simp [nextGood, hnot] at hgood
    have holdGood : state.good = true := by
      simpa [nextGood, hcallGood] using hgood
    by_cases hstEq : s = t
    · subst s
      have hsigma :
          separableFrankWolfeIterate nextOmega t = sigma := by
        exact separableFrankWolfeIterate_update_same
          state.omega t selected.1
      rcases hcallGood with heq | hfresh
      · left
        rw [hsigma]
        exact heq
      · right
        have hbest :=
          bestOracleOutput_correct oracle query repetitionIndex z.2
            hfresh
        intro P hP
        rw [hsigma]
        change
          ⟪separableOracleDirection rho sigma, P⟫ ≤
            ⟪separableOracleDirection rho sigma, nextOmega t⟫ + tau
        have hnext : nextOmega t = selected.1 := by
          simp [nextOmega, Function.update]
        rw [hnext]
        simpa [query, certifiedStateQuery, sigma, selected,
          amplifiedOracleOutput] using
          hbest P hP
    · have hstOld : s < t := by omega
      have hold := state.calls_correct holdGood hs hstOld
      have hiter :
          separableFrankWolfeIterate nextOmega s =
            separableFrankWolfeIterate state.omega s := by
        apply separableFrankWolfeIterate_congr_at
        intro r _hr hrs
        simp [nextOmega, Function.update, show r ≠ t by omega]
      have hout : nextOmega s = state.omega s := by
        simp [nextOmega, Function.update, hstEq]
      change separableOracleCallSucceeds rho nextOmega tau s
      unfold separableOracleCallSucceeds at hold ⊢
      rw [hiter, hout]
      exact hold

theorem measurable_certifiedWeakTransition
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrhoHerm : rho ∈ hermitianMatrices d)
    (hrhoNorm : ‖rho‖ ≤ 1)
    (tau : ℝ)
    (oracle : MeasurableSupportOracle d tau)
    (repetitionIndex : ℕ)
    (t : ℕ) (ht : 1 ≤ t) :
    @Measurable
      (CertifiedWeakState d rho tau t ×
        (Fin (repetitionIndex + 1) → oracle.Seed))
      (CertifiedWeakState d rho tau (t + 1))
      (@Prod.instMeasurableSpace
        (CertifiedWeakState d rho tau t)
        (Fin (repetitionIndex + 1) → oracle.Seed)
        inferInstance
        (@MeasurableSpace.pi (Fin (repetitionIndex + 1))
          (fun _ => oracle.Seed) fun _ => oracle.seedMeasurableSpace))
      inferInstance
      (certifiedWeakTransition d hd rho hrhoHerm hrhoNorm tau
        oracle repetitionIndex t ht) := by
  classical
  letI : MeasurableSpace oracle.Seed := oracle.seedMeasurableSpace
  let stateValue :
      CertifiedWeakState d rho tau t ×
          (Fin (repetitionIndex + 1) → oracle.Seed) →
        (ℕ → MatrixHilbert d) × Bool :=
    fun z => z.1.1
  have hstateValue : Measurable stateValue :=
    measurable_subtype_coe.comp measurable_fst
  have homega : ∀ s, Measurable fun
      z : CertifiedWeakState d rho tau t ×
        (Fin (repetitionIndex + 1) → oracle.Seed) =>
      z.1.omega s := by
    intro s
    exact (measurable_pi_apply s).comp hstateValue.fst
  have hsigma : Measurable fun
      z : CertifiedWeakState d rho tau t ×
        (Fin (repetitionIndex + 1) → oracle.Seed) =>
      separableFrankWolfeIterate z.1.omega t :=
    measurable_separableFrankWolfeIterate
      (fun z : CertifiedWeakState d rho tau t ×
          (Fin (repetitionIndex + 1) → oracle.Seed) =>
        z.1.omega) homega t
  have hquery : Measurable fun
      z : CertifiedWeakState d rho tau t ×
        (Fin (repetitionIndex + 1) → oracle.Seed) =>
      certifiedStateQuery d hd rho hrhoHerm hrhoNorm tau t ht z.1 :=
    (measurable_certifiedStateQuery
      d hd rho hrhoHerm hrhoNorm tau t ht).comp measurable_fst
  have hselected : Measurable fun
      z : CertifiedWeakState d rho tau t ×
        (Fin (repetitionIndex + 1) → oracle.Seed) =>
      amplifiedOracleOutput oracle repetitionIndex
        (certifiedStateQuery d hd rho hrhoHerm hrhoNorm tau t ht z.1,
          z.2) :=
    (measurable_amplifiedOracleOutput oracle repetitionIndex).comp
      (hquery.prodMk measurable_snd)
  have hfresh : MeasurableSet
      {z : CertifiedWeakState d rho tau t ×
          (Fin (repetitionIndex + 1) → oracle.Seed) |
        ∃ i,
          (certifiedStateQuery d hd rho hrhoHerm hrhoNorm tau t ht z.1,
            z.2 i) ∈ oracle.core} :=
    (measurableSet_exists_oracleCore oracle repetitionIndex).preimage
      (hquery.prodMk measurable_snd)
  have hequal : MeasurableSet
      {z : CertifiedWeakState d rho tau t ×
          (Fin (repetitionIndex + 1) → oracle.Seed) |
        rho = separableFrankWolfeIterate z.1.omega t} :=
    measurableSet_eq_fun measurable_const hsigma
  have hcallGood := hequal.union hfresh
  let nextOmega :
      CertifiedWeakState d rho tau t ×
          (Fin (repetitionIndex + 1) → oracle.Seed) →
        ℕ → MatrixHilbert d :=
    fun z =>
      Function.update z.1.omega t
        (amplifiedOracleOutput oracle repetitionIndex
          (certifiedStateQuery d hd rho hrhoHerm hrhoNorm tau t ht z.1,
            z.2)).1
  have hnextOmega : Measurable nextOmega := by
    apply measurable_pi_lambda
    intro s
    by_cases hst : s = t
    · subst s
      simpa [nextOmega] using hselected.subtype_val
    · simpa [nextOmega, hst] using homega s
  let nextGood :
      CertifiedWeakState d rho tau t ×
          (Fin (repetitionIndex + 1) → oracle.Seed) → Bool :=
    fun z =>
      if rho = separableFrankWolfeIterate z.1.omega t ∨
          ∃ i,
            (certifiedStateQuery d hd rho hrhoHerm hrhoNorm tau t ht z.1,
              z.2 i) ∈ oracle.core
      then z.1.good else false
  have hnextGood : Measurable nextGood := by
    apply Measurable.ite hcallGood
    · exact hstateValue.snd
    · exact measurable_const
  have hraw : Measurable fun z => (nextOmega z, nextGood z) :=
    hnextOmega.prodMk hnextGood
  have hinvariant : ∀ z :
      CertifiedWeakState d rho tau t ×
        (Fin (repetitionIndex + 1) → oracle.Seed),
      (∀ s, 1 ≤ s → s < t + 1 →
          nextOmega z s ∈ separableStates d) ∧
        (nextGood z = true →
          ∀ s, 1 ≤ s → s < t + 1 →
            separableOracleCallSucceeds rho (nextOmega z) tau s) := by
    intro z
    simpa [certifiedWeakTransition, nextOmega, nextGood] using
      (certifiedWeakTransition d hd rho hrhoHerm hrhoNorm tau
        oracle repetitionIndex t ht z).2
  let lifted :
      CertifiedWeakState d rho tau t ×
          (Fin (repetitionIndex + 1) → oracle.Seed) →
        CertifiedWeakState d rho tau (t + 1) :=
    fun z => ⟨(nextOmega z, nextGood z), hinvariant z⟩
  have hlifted : Measurable lifted := hraw.subtype_mk
  have heq :
      certifiedWeakTransition d hd rho hrhoHerm hrhoNorm tau
          oracle repetitionIndex t ht =
        lifted := by
    funext z
    apply Subtype.ext
    simp [certifiedWeakTransition, lifted, nextOmega, nextGood]
  rw [heq]
  exact hlifted

/-- Distribution of the certified state after `k` adaptive calls.  At every
successor step the old state is paired with a fresh independent block of
oracle seeds before the measurable transition is applied. -/
def certifiedWeakLaw
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrhoHerm : rho ∈ hermitianMatrices d)
    (hrhoNorm : ‖rho‖ ≤ 1)
    (tau : ℝ)
    (oracle : MeasurableSupportOracle d tau)
    (repetitionIndex : ℕ) :
    (k : ℕ) → Measure (CertifiedWeakState d rho tau (k + 1))
  | 0 => Measure.dirac (initialCertifiedWeakState d rho tau)
  | k + 1 =>
      letI : MeasurableSpace oracle.Seed :=
        oracle.seedMeasurableSpace
      let previous :=
        certifiedWeakLaw d hd rho hrhoHerm hrhoNorm tau
          oracle repetitionIndex k
      let fresh := oracleRepetitionMeasure oracle repetitionIndex
      (previous.prod fresh).map
        (certifiedWeakTransition d hd rho hrhoHerm hrhoNorm tau
          oracle repetitionIndex (k + 1) (Nat.succ_pos k))

theorem certifiedWeakLaw_probability
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrhoHerm : rho ∈ hermitianMatrices d)
    (hrhoNorm : ‖rho‖ ≤ 1)
    (tau : ℝ)
    (oracle : MeasurableSupportOracle d tau)
    (repetitionIndex : ℕ) :
    ∀ k, IsProbabilityMeasure
      (certifiedWeakLaw d hd rho hrhoHerm hrhoNorm tau
        oracle repetitionIndex k) := by
  intro k
  induction k with
  | zero =>
      simp only [certifiedWeakLaw]
      infer_instance
  | succ k ih =>
      letI : MeasurableSpace oracle.Seed :=
        oracle.seedMeasurableSpace
      let fresh := oracleRepetitionMeasure oracle repetitionIndex
      letI : IsProbabilityMeasure fresh :=
        oracleRepetitionMeasure_probability oracle repetitionIndex
      let previous :=
        certifiedWeakLaw d hd rho hrhoHerm hrhoNorm tau
          oracle repetitionIndex k
      letI : IsProbabilityMeasure previous := ih
      rw [certifiedWeakLaw]
      exact Measure.isProbabilityMeasure_map
        (measurable_certifiedWeakTransition
          d hd rho hrhoHerm hrhoNorm tau oracle repetitionIndex
          (k + 1) (Nat.succ_pos k)).aemeasurable

theorem measurableSet_certifiedWeakState_good
    {d : ℕ} {rho : MatrixHilbert d} {tau : ℝ} {t : ℕ} :
    MeasurableSet
      {state : CertifiedWeakState d rho tau t |
        state.good = true} := by
  have hvalue : Measurable fun
      state : CertifiedWeakState d rho tau t => state.1 :=
    measurable_subtype_coe
  exact measurableSet_eq_fun hvalue.snd measurable_const

theorem measurableSet_certifiedWeakState_accept
    {d : ℕ} {rho : MatrixHilbert d} {tau eta : ℝ}
    {stateIndex : ℕ} (T : ℕ) :
    MeasurableSet
      {state : CertifiedWeakState d rho tau stateIndex |
        separableWeakMembershipAccept rho state.omega eta T} := by
  have hvalue : Measurable fun
      state : CertifiedWeakState d rho tau stateIndex => state.1 :=
    measurable_subtype_coe
  have homega : ∀ s, Measurable fun
      state : CertifiedWeakState d rho tau stateIndex =>
        state.omega s := by
    intro s
    exact (measurable_pi_apply s).comp hvalue.fst
  have hsigma : ∀ s, Measurable fun
      state : CertifiedWeakState d rho tau stateIndex =>
        separableFrankWolfeIterate state.omega s := by
    intro s
    exact measurable_separableFrankWolfeIterate
      (fun state : CertifiedWeakState d rho tau stateIndex =>
        state.omega) homega s
  let early :
      Set (CertifiedWeakState d rho tau stateIndex) :=
    {state |
      ∃ t, 1 ≤ t ∧ t ≤ T ∧
        rho = separableFrankWolfeIterate state.omega t}
  have hearly :
      early =
        ⋃ i : Fin (T + 1),
          if hi : 1 ≤ i.val then
            {state |
              rho =
                separableFrankWolfeIterate state.omega i.val}
          else ∅ := by
    ext state
    constructor
    · rintro ⟨t, ht, htT, heq⟩
      rw [Set.mem_iUnion]
      let i : Fin (T + 1) := ⟨t, by omega⟩
      refine ⟨i, ?_⟩
      simp [i, ht, heq]
    · rw [Set.mem_iUnion]
      rintro ⟨i, hi⟩
      by_cases hiOne : 1 ≤ i.val
      · simp [hiOne] at hi
        exact ⟨i.val, hiOne, by omega, hi⟩
      · simp [hiOne] at hi
  have hearlyMeas : MeasurableSet early := by
    rw [hearly]
    apply MeasurableSet.iUnion
    intro i
    by_cases hi : 1 ≤ i.val
    · simp only [dif_pos hi]
      exact measurableSet_eq_fun measurable_const (hsigma i.val)
    · simp [hi]
  let terminal :
      Set (CertifiedWeakState d rho tau stateIndex) :=
    {state |
      ‖rho - separableFrankWolfeIterate state.omega T‖ ≤ eta / 2}
  have hterminalMeas : MeasurableSet terminal := by
    exact measurableSet_le
      (by
        change Measurable fun
          state : CertifiedWeakState d rho tau stateIndex =>
            ‖rho - separableFrankWolfeIterate state.omega T‖
        fun_prop)
      measurable_const
  have haccept :
      {state : CertifiedWeakState d rho tau stateIndex |
        separableWeakMembershipAccept rho state.omega eta T} =
        early ∪ terminal := by
    ext state
    rfl
  rw [haccept]
  exact hearlyMeas.union hterminalMeas

theorem certifiedWeakTransition_good_iff
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrhoHerm : rho ∈ hermitianMatrices d)
    (hrhoNorm : ‖rho‖ ≤ 1)
    (tau : ℝ)
    (oracle : MeasurableSupportOracle d tau)
    (repetitionIndex : ℕ)
    (t : ℕ) (ht : 1 ≤ t)
    (z : CertifiedWeakState d rho tau t ×
      (Fin (repetitionIndex + 1) → oracle.Seed)) :
    (certifiedWeakTransition d hd rho hrhoHerm hrhoNorm tau
        oracle repetitionIndex t ht z).good = true ↔
      z.1.good = true ∧
        (rho = separableFrankWolfeIterate z.1.omega t ∨
          ∃ i,
            (certifiedStateQuery d hd rho hrhoHerm hrhoNorm tau t ht z.1,
              z.2 i) ∈ oracle.core) := by
  classical
  by_cases hcall :
      rho = separableFrankWolfeIterate z.1.omega t ∨
        ∃ i,
          (certifiedStateQuery d hd rho hrhoHerm hrhoNorm tau t ht z.1,
            z.2 i) ∈ oracle.core
  · simp [certifiedWeakTransition, CertifiedWeakState.good, hcall]
  · simp [certifiedWeakTransition, CertifiedWeakState.good, hcall]

/-- One adaptive step loses at most the failure probability of its fresh
amplified oracle block. -/
theorem certifiedWeakTransition_good_probability
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrhoHerm : rho ∈ hermitianMatrices d)
    (hrhoNorm : ‖rho‖ ≤ 1)
    (tau : ℝ)
    (oracle : MeasurableSupportOracle d tau)
    (repetitionIndex : ℕ)
    (t : ℕ) (ht : 1 ≤ t)
    (mu : Measure (CertifiedWeakState d rho tau t))
    [IsProbabilityMeasure mu]
    (a : ℝ)
    (hprevious :
      mu.real
        {state : CertifiedWeakState d rho tau t |
          state.good = true} ≥ 1 - a) :
    letI : MeasurableSpace oracle.Seed := oracle.seedMeasurableSpace
    let fresh := oracleRepetitionMeasure oracle repetitionIndex
    ((mu.prod fresh).map
      (certifiedWeakTransition d hd rho hrhoHerm hrhoNorm tau
        oracle repetitionIndex t ht)).real
      {state : CertifiedWeakState d rho tau (t + 1) |
        state.good = true} ≥
      1 - a - (1 / 3 : ℝ) ^ (repetitionIndex + 1) := by
  dsimp only
  classical
  letI : MeasurableSpace oracle.Seed := oracle.seedMeasurableSpace
  let fresh := oracleRepetitionMeasure oracle repetitionIndex
  letI : IsProbabilityMeasure fresh :=
    oracleRepetitionMeasure_probability oracle repetitionIndex
  let productMeasure := mu.prod fresh
  let oldGood :
      Set (CertifiedWeakState d rho tau t) :=
    {state | state.good = true}
  let oldGoodProduct :
      Set (CertifiedWeakState d rho tau t ×
        (Fin (repetitionIndex + 1) → oracle.Seed)) :=
    {z | z.1.good = true}
  let freshGood :
      Set (CertifiedWeakState d rho tau t ×
        (Fin (repetitionIndex + 1) → oracle.Seed)) :=
    {z |
      ∃ i,
        (certifiedStateQuery d hd rho hrhoHerm hrhoNorm tau t ht z.1,
          z.2 i) ∈ oracle.core}
  have holdMeas : MeasurableSet oldGood :=
    measurableSet_certifiedWeakState_good
  have holdProductMeas : MeasurableSet oldGoodProduct :=
    holdMeas.preimage measurable_fst
  have hfreshMeas : MeasurableSet freshGood := by
    exact
      (measurableSet_exists_oracleCore oracle repetitionIndex).preimage
        (((measurable_certifiedStateQuery
          d hd rho hrhoHerm hrhoNorm tau t ht).comp measurable_fst).prodMk
          measurable_snd)
  have holdProductEq :
      productMeasure.real oldGoodProduct = mu.real oldGood := by
    have heq :
        oldGoodProduct =
          oldGood ×ˢ
            (Set.univ :
              Set (Fin (repetitionIndex + 1) → oracle.Seed)) := by
      ext z
      simp [oldGoodProduct, oldGood]
    unfold productMeasure
    rw [heq, measureReal_prod_prod, probReal_univ, mul_one]
  have holdProduct :
      productMeasure.real oldGoodProduct ≥ 1 - a := by
    rw [holdProductEq]
    exact hprevious
  have hfresh :
      productMeasure.real freshGood ≥
        1 - (1 / 3 : ℝ) ^ (repetitionIndex + 1) := by
    simpa [productMeasure, freshGood, fresh] using
      amplifiedOracleCore_probability_random
        mu oracle repetitionIndex
        (certifiedStateQuery d hd rho hrhoHerm hrhoNorm tau t ht)
        (measurable_certifiedStateQuery
          d hd rho hrhoHerm hrhoNorm tau t ht)
  have hinter :
      productMeasure.real (oldGoodProduct ∩ freshGood) ≥
        1 - a - (1 / 3 : ℝ) ^ (repetitionIndex + 1) :=
    probability_inter_ge productMeasure oldGoodProduct freshGood
      holdProductMeas hfreshMeas a
      ((1 / 3 : ℝ) ^ (repetitionIndex + 1))
      holdProduct hfresh
  let transition :=
    certifiedWeakTransition d hd rho hrhoHerm hrhoNorm tau
      oracle repetitionIndex t ht
  let finalGood :
      Set (CertifiedWeakState d rho tau (t + 1)) :=
    {state | state.good = true}
  have htransition : Measurable transition :=
    measurable_certifiedWeakTransition
      d hd rho hrhoHerm hrhoNorm tau oracle repetitionIndex t ht
  have hfinalMeas : MeasurableSet finalGood :=
    measurableSet_certifiedWeakState_good
  have hsubset :
      oldGoodProduct ∩ freshGood ⊆ transition ⁻¹' finalGood := by
    intro z hz
    change (transition z).good = true
    rw [certifiedWeakTransition_good_iff]
    exact ⟨hz.1, Or.inr hz.2⟩
  calc
    (productMeasure.map transition).real finalGood =
        productMeasure.real (transition ⁻¹' finalGood) := by
      unfold Measure.real
      rw [Measure.map_apply htransition hfinalMeas]
    _ ≥ productMeasure.real (oldGoodProduct ∩ freshGood) :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ ≥ 1 - a - (1 / 3 : ℝ) ^ (repetitionIndex + 1) :=
      hinter

/-- Union-bound form of adaptive amplification: after `k` fresh calls, the
entire certified history is good except with probability at most `k` times
the amplified one-call failure. -/
theorem certifiedWeakLaw_good_probability
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrhoHerm : rho ∈ hermitianMatrices d)
    (hrhoNorm : ‖rho‖ ≤ 1)
    (tau : ℝ)
    (oracle : MeasurableSupportOracle d tau)
    (repetitionIndex : ℕ) :
    ∀ k,
      (certifiedWeakLaw d hd rho hrhoHerm hrhoNorm tau
        oracle repetitionIndex k).real
        {state : CertifiedWeakState d rho tau (k + 1) |
          state.good = true} ≥
        1 - (k : ℝ) *
          (1 / 3 : ℝ) ^ (repetitionIndex + 1) := by
  intro k
  induction k with
  | zero =>
      rw [certifiedWeakLaw]
      norm_num only [Nat.cast_zero, zero_mul, sub_zero]
      change
        (Measure.dirac
          (initialCertifiedWeakState d rho tau)).real
            {state : CertifiedWeakState d rho tau 1 |
              state.good = true} ≥ 1
      unfold Measure.real
      rw [Measure.dirac_apply_of_mem]
      · norm_num
      · rfl
  | succ k ih =>
      letI : MeasurableSpace oracle.Seed :=
        oracle.seedMeasurableSpace
      let previous :=
        certifiedWeakLaw d hd rho hrhoHerm hrhoNorm tau
          oracle repetitionIndex k
      letI : IsProbabilityMeasure previous :=
        certifiedWeakLaw_probability
          d hd rho hrhoHerm hrhoNorm tau oracle repetitionIndex k
      have hstep :=
        certifiedWeakTransition_good_probability
          d hd rho hrhoHerm hrhoNorm tau oracle repetitionIndex
          (k + 1) (Nat.succ_pos k) previous
          ((k : ℝ) * (1 / 3 : ℝ) ^ (repetitionIndex + 1)) ih
      rw [certifiedWeakLaw]
      convert hstep using 1 <;> push_cast <;> ring

/-- Measurable Boolean terminal decision. -/
def certifiedWeakDecision
    {d : ℕ} {rho : MatrixHilbert d} {tau : ℝ}
    {stateIndex : ℕ}
    (eta : ℝ) (T : ℕ)
    (state : CertifiedWeakState d rho tau stateIndex) : Bool :=
  by
    classical
    exact
      if separableWeakMembershipAccept rho state.omega eta T
      then true else false

theorem measurable_certifiedWeakDecision
    {d : ℕ} {rho : MatrixHilbert d} {tau : ℝ}
    {stateIndex : ℕ}
    (eta : ℝ) (T : ℕ) :
    Measurable
      (certifiedWeakDecision
        (d := d) (rho := rho) (tau := tau)
        (stateIndex := stateIndex) eta T) := by
  classical
  unfold certifiedWeakDecision
  exact Measurable.ite
    (measurableSet_certifiedWeakState_accept T)
    measurable_const measurable_const

theorem certifiedWeakDecision_eq_true_iff
    {d : ℕ} {rho : MatrixHilbert d} {tau : ℝ}
    {stateIndex : ℕ}
    (eta : ℝ) (T : ℕ)
    (state : CertifiedWeakState d rho tau stateIndex) :
    certifiedWeakDecision eta T state = true ↔
      separableWeakMembershipAccept rho state.omega eta T := by
  classical
  unfold certifiedWeakDecision
  by_cases h :
      separableWeakMembershipAccept rho state.omega eta T <;>
    simp [h]

/-- Completeness of the finite adaptive execution for any instantiated
measurable support oracle. -/
theorem certifiedAdaptiveWeakMembership_complete
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrhoHerm : rho ∈ hermitianMatrices d)
    (hrhoNorm : ‖rho‖ ≤ 1)
    (hrho : rho ∈ separableStates d)
    (eta tau : ℝ) (T : ℕ)
    (heta : 0 < eta)
    (htau : tau = eta ^ 2 / 64)
    (hTbound : 256 / eta ^ 2 ≤ (T : ℝ))
    (hTone : 1 ≤ T)
    (oracle : MeasurableSupportOracle d tau) :
    (certifiedWeakLaw d hd rho hrhoHerm hrhoNorm tau
      oracle T T).real
      {state : CertifiedWeakState d rho tau (T + 1) |
        certifiedWeakDecision eta T state = true} ≥
      2 / 3 := by
  let law :=
    certifiedWeakLaw d hd rho hrhoHerm hrhoNorm tau oracle T T
  letI : IsProbabilityMeasure law :=
    certifiedWeakLaw_probability
      d hd rho hrhoHerm hrhoNorm tau oracle T T
  have hgoodRaw :=
    certifiedWeakLaw_good_probability
      d hd rho hrhoHerm hrhoNorm tau oracle T T
  have hpNonneg :
      0 ≤ (1 / 3 : ℝ) ^ T := by positivity
  have hpowStep :
      (1 / 3 : ℝ) ^ (T + 1) ≤
        (1 / 3 : ℝ) ^ T := by
    rw [pow_succ]
    nlinarith
  have hbudgetBase :=
    repetitions_equal_iterations_budget T hTone
  have hbudget :
      (T : ℝ) * (1 / 3 : ℝ) ^ (T + 1) ≤ 1 / 3 := by
    exact
      (mul_le_mul_of_nonneg_left hpowStep
        (Nat.cast_nonneg T)).trans hbudgetBase
  have hgood :
      law.real
          {state : CertifiedWeakState d rho tau (T + 1) |
            state.good = true} ≥
        2 / 3 := by
    dsimp [law]
    linarith
  have hsubset :
      {state : CertifiedWeakState d rho tau (T + 1) |
        state.good = true} ⊆
      {state : CertifiedWeakState d rho tau (T + 1) |
        certifiedWeakDecision eta T state = true} := by
    intro state hstate
    change state.good = true at hstate
    change certifiedWeakDecision eta T state = true
    rw [certifiedWeakDecision_eq_true_iff]
    apply separableWeakMembership_complete_on_success
      d hd rho hrho state.omega eta tau T
      heta htau hTbound
    · intro t ht htT
      exact state.output_mem ht (by omega)
    · intro t ht htT
      exact state.calls_correct hstate ht (by omega)
    · exact hTone
  exact hgood.trans
    (measureReal_mono hsubset (measure_ne_top _ _))

/-- Soundness is pointwise: no random execution can accept an input that is
farther than `eta` from every separable state. -/
theorem certifiedAdaptiveWeakMembership_sound
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrhoHerm : rho ∈ hermitianMatrices d)
    (hrhoNorm : ‖rho‖ ≤ 1)
    (eta tau : ℝ) (T : ℕ)
    (heta : 0 ≤ eta)
    (oracle : MeasurableSupportOracle d tau)
    (repetitionIndex : ℕ)
    (hfar : ∀ psi ∈ separableStates d,
      eta < ‖rho - psi‖) :
    (certifiedWeakLaw d hd rho hrhoHerm hrhoNorm tau
      oracle repetitionIndex T).real
      {state : CertifiedWeakState d rho tau (T + 1) |
        certifiedWeakDecision eta T state = true} = 0 := by
  have hempty :
      {state : CertifiedWeakState d rho tau (T + 1) |
        certifiedWeakDecision eta T state = true} = ∅ := by
    ext state
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false]
    rw [certifiedWeakDecision_eq_true_iff]
    exact separableWeakMembership_sound
      d rho state.omega eta T heta
        (fun t ht htT => state.output_mem ht (by omega))
        hfar
  rw [hempty, measureReal_empty]

/-- The concrete weak-membership law assembled from exactly the authorized
contracts, using the explicit tolerance and iteration count. -/
def randomizedSeparableWeakMembershipLaw
    (assumptions : AllowedAssumptions)
    (eta : ℝ) (heta : 0 < eta)
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrhoHerm : rho ∈ hermitianMatrices d)
    (hrhoNorm : ‖rho‖ ≤ 1) :
    Measure
      (CertifiedWeakState d rho (eta ^ 2 / 64)
        (weakMembershipIterations eta + 1)) := by
  let tau := eta ^ 2 / 64
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  let oracle :=
    adaptiveMeasurableSupportOracle
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      tau htau d hd
  exact certifiedWeakLaw
    d hd rho hrhoHerm hrhoNorm tau oracle
      (weakMembershipIterations eta)
      (weakMembershipIterations eta)

theorem randomizedSeparableWeakMembershipLaw_probability
    (assumptions : AllowedAssumptions)
    (eta : ℝ) (heta : 0 < eta)
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrhoHerm : rho ∈ hermitianMatrices d)
    (hrhoNorm : ‖rho‖ ≤ 1) :
    IsProbabilityMeasure
      (randomizedSeparableWeakMembershipLaw
        assumptions eta heta d hd rho hrhoHerm hrhoNorm) := by
  let tau := eta ^ 2 / 64
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  let oracle :=
    adaptiveMeasurableSupportOracle
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      tau htau d hd
  unfold randomizedSeparableWeakMembershipLaw
  exact certifiedWeakLaw_probability
    d hd rho hrhoHerm hrhoNorm tau oracle
      (weakMembershipIterations eta)
      (weakMembershipIterations eta)

/-- End-to-end completeness of the weak-membership corollary. -/
theorem randomizedSeparableWeakMembership_complete
    (assumptions : AllowedAssumptions)
    (eta : ℝ) (heta : 0 < eta)
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrhoHerm : rho ∈ hermitianMatrices d)
    (hrhoNorm : ‖rho‖ ≤ 1)
    (hrho : rho ∈ separableStates d) :
    (randomizedSeparableWeakMembershipLaw
      assumptions eta heta d hd rho hrhoHerm hrhoNorm).real
      {state |
        certifiedWeakDecision eta
          (weakMembershipIterations eta) state = true} ≥
      2 / 3 := by
  let tau := eta ^ 2 / 64
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  let oracle :=
    adaptiveMeasurableSupportOracle
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      tau htau d hd
  have hcore :=
    certifiedAdaptiveWeakMembership_complete
      d hd rho hrhoHerm hrhoNorm hrho eta tau
      (weakMembershipIterations eta) heta rfl
      (weakMembershipIterations_bound eta)
      (weakMembershipIterations_one_le eta) oracle
  simpa [randomizedSeparableWeakMembershipLaw, tau, oracle] using hcore

/-- End-to-end soundness of the weak-membership corollary. -/
theorem randomizedSeparableWeakMembership_sound
    (assumptions : AllowedAssumptions)
    (eta : ℝ) (heta : 0 < eta)
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrhoHerm : rho ∈ hermitianMatrices d)
    (hrhoNorm : ‖rho‖ ≤ 1)
    (hfar : ∀ psi ∈ separableStates d,
      eta < ‖rho - psi‖) :
    (randomizedSeparableWeakMembershipLaw
      assumptions eta heta d hd rho hrhoHerm hrhoNorm).real
      {state |
        certifiedWeakDecision eta
          (weakMembershipIterations eta) state = true} = 0 := by
  let tau := eta ^ 2 / 64
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  let oracle :=
    adaptiveMeasurableSupportOracle
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      tau htau d hd
  have hcore :=
    certifiedAdaptiveWeakMembership_sound
      d hd rho hrhoHerm hrhoNorm eta tau
      (weakMembershipIterations eta) heta.le oracle
      (weakMembershipIterations eta) hfar
  simpa [randomizedSeparableWeakMembershipLaw, tau, oracle] using hcore

end

end QuantumSep
