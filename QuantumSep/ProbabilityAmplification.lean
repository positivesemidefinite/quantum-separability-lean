import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Independent repetition and success amplification

This module proves the amplification calculation used for the dense-CSP
algorithm.  It is not part of the trusted boundary: independent repetitions
are represented by the finite product probability measure.
-/

open scoped BigOperators ENNReal

namespace QuantumSep

open MeasureTheory Set

/-- Under the finite product probability measure, the event that every
independent trial lies in `failure` has measure `μ failure ^ repetitions`. -/
theorem measure_allFailures
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (failure : Set Ω)
    (repetitions : ℕ) :
    (Measure.pi (fun _ : Fin repetitions => μ))
        (Set.pi Set.univ (fun _ : Fin repetitions => failure)) =
      μ failure ^ repetitions := by
  rw [Measure.pi_pi]
  simp

/-- If one run fails with probability at most `1/3`, all independent runs fail
with probability at most `3^{-repetitions}`. -/
theorem independentRepetition_failure_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (failure : Set Ω)
    (repetitions : ℕ)
    (hone : μ failure ≤ (1 / 3 : ℝ≥0∞)) :
    (Measure.pi (fun _ : Fin repetitions => μ))
        (Set.pi Set.univ (fun _ : Fin repetitions => failure)) ≤
      (1 / 3 : ℝ≥0∞) ^ repetitions := by
  rw [measure_allFailures μ failure repetitions]
  gcongr

/-- A chosen index attaining the maximum score among a nonempty finite family
of trials. -/
noncomputable def maximizingRepetitionIndex
    {Ω : Type*}
    (repetitions : ℕ) (hrepetitions : 0 < repetitions)
    (score : Ω → ℝ) (trials : Fin repetitions → Ω) :
    Fin repetitions :=
  Classical.choose
    (Finset.exists_max_image Finset.univ
      (fun i => score (trials i))
      ⟨⟨0, hrepetitions⟩, Finset.mem_univ _⟩)

theorem maximizingRepetitionIndex_max
    {Ω : Type*}
    (repetitions : ℕ) (hrepetitions : 0 < repetitions)
    (score : Ω → ℝ) (trials : Fin repetitions → Ω)
    (i : Fin repetitions) :
    score (trials i) ≤
      score (trials
        (maximizingRepetitionIndex repetitions hrepetitions score trials)) := by
  exact
    (Classical.choose_spec
      (Finset.exists_max_image Finset.univ
        (fun j => score (trials j))
        ⟨⟨0, hrepetitions⟩, Finset.mem_univ _⟩)).2
      i (Finset.mem_univ i)

/-- Selecting the largest observed objective preserves any correctness
predicate which is monotone in that objective. -/
theorem maximizingRepetition_correct
    {Ω : Type*}
    (repetitions : ℕ) (hrepetitions : 0 < repetitions)
    (score : Ω → ℝ) (good : Ω → Prop)
    (hmono : ∀ a b, good a → score a ≤ score b → good b)
    (trials : Fin repetitions → Ω)
    (hexists : ∃ i, good (trials i)) :
    good (trials
      (maximizingRepetitionIndex repetitions hrepetitions score trials)) := by
  obtain ⟨i, hi⟩ := hexists
  exact hmono _ _ hi
    (maximizingRepetitionIndex_max
      repetitions hrepetitions score trials i)

/-- The event that at least one independent repetition lies in a measurable
core has the expected exact probability. -/
theorem measureReal_exists_mem_independent
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (core : Set Ω) (hcore : MeasurableSet core)
    (repetitions : ℕ) :
    (Measure.pi (fun _ : Fin repetitions => μ)).real
        {trials | ∃ i, trials i ∈ core} =
      1 - (μ.real coreᶜ) ^ repetitions := by
  let allFailure : Set (Fin repetitions → Ω) :=
    Set.pi Set.univ (fun _ : Fin repetitions => coreᶜ)
  have hfailureMeas : MeasurableSet allFailure := by
    exact MeasurableSet.univ_pi (fun _ => hcore.compl)
  have hevent :
      {trials : Fin repetitions → Ω | ∃ i, trials i ∈ core} =
        allFailureᶜ := by
    ext trials
    simp [allFailure, Set.mem_pi]
  rw [hevent, probReal_compl_eq_one_sub hfailureMeas]
  congr 1
  unfold Measure.real
  rw [measure_allFailures μ coreᶜ repetitions,
    ENNReal.toReal_pow]

/-- If one run has a measurable correctness core of probability at least
`2/3`, choosing the largest score among independent repetitions succeeds
except with probability `3^{-repetitions}`. -/
theorem measureReal_exists_core_ge
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (core : Set Ω) (hcore : MeasurableSet core)
    (repetitions : ℕ)
    (hprob : μ.real core ≥ (2 / 3 : ℝ)) :
    (Measure.pi (fun _ : Fin repetitions => μ)).real
        {trials | ∃ i, trials i ∈ core} ≥
      1 - (1 / 3 : ℝ) ^ repetitions := by
  rw [measureReal_exists_mem_independent μ core hcore repetitions]
  have hfailure : μ.real coreᶜ ≤ 1 / 3 := by
    rw [probReal_compl_eq_one_sub hcore]
    linarith
  have hfailure0 : 0 ≤ μ.real coreᶜ :=
    measureReal_nonneg
  have hpow :
      (μ.real coreᶜ) ^ repetitions ≤
        (1 / 3 : ℝ) ^ repetitions :=
    pow_le_pow_left₀ hfailure0 hfailure repetitions
  linarith

/-- Finite union bound for a family of failure events. -/
theorem finiteUnion_failure_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (failure : ι → Set Ω) (bound : ι → ℝ≥0∞)
    (hbound : ∀ i, μ (failure i) ≤ bound i) :
    μ (⋃ i, failure i) ≤ ∑ i, bound i := by
  calc
    μ (⋃ i, failure i) ≤ ∑ i, μ (failure i) :=
      MeasureTheory.measure_iUnion_fintype_le μ failure
    _ ≤ ∑ i, bound i := Finset.sum_le_sum fun i _ => hbound i

/-- Constant-probability form of the finite union bound used across the
Frank--Wolfe iterations. -/
theorem finiteUnion_failure_le_const
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (failure : ι → Set Ω) (p : ℝ≥0∞)
    (hbound : ∀ i, μ (failure i) ≤ p) :
    μ (⋃ i, failure i) ≤ Fintype.card ι * p := by
  calc
    μ (⋃ i, failure i) ≤ ∑ _i : ι, p :=
      finiteUnion_failure_le μ failure (fun _ => p) hbound
    _ = Fintype.card ι * p := by simp

/-- Real-probability union bound, presented as the probability that every
one of finitely many measurable success events occurs. -/
theorem measureReal_allSuccess_ge
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (success : ι → Set Ω)
    (hsuccess : ∀ i, MeasurableSet (success i))
    (p : ℝ)
    (hfailure : ∀ i, μ.real (success i)ᶜ ≤ p) :
    μ.real {ω | ∀ i, ω ∈ success i} ≥
      1 - Fintype.card ι * p := by
  let failure : Set Ω := ⋃ i, (success i)ᶜ
  have hfailureMeas : MeasurableSet failure := by
    exact MeasurableSet.iUnion fun i => (hsuccess i).compl
  have hall :
      {ω | ∀ i, ω ∈ success i} = failureᶜ := by
    ext ω
    simp [failure]
  have hunion :
      μ.real failure ≤ Fintype.card ι * p := by
    calc
      μ.real failure ≤ ∑ i, μ.real (success i)ᶜ := by
        exact measureReal_iUnion_fintype_le
          (fun i => (success i)ᶜ)
      _ ≤ ∑ _i : ι, p :=
        Finset.sum_le_sum fun i _ => hfailure i
      _ = Fintype.card ι * p := by simp
  rw [hall, probReal_compl_eq_one_sub hfailureMeas]
  linarith

theorem nat_le_three_pow_pred
    (n : ℕ) (hn : 1 ≤ n) :
    3 * n ≤ 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      have hone : 1 ≤ 3 ^ n := one_le_pow₀ (by norm_num)
      omega

/-- Repeating each of `T` calls `T` times is already sufficient for the
manuscript's final `1/3` union-bound budget. -/
theorem repetitions_equal_iterations_budget
    (T : ℕ) (hT : 1 ≤ T) :
    (T : ℝ) * (1 / 3 : ℝ) ^ T ≤ 1 / 3 := by
  have hnat := nat_le_three_pow_pred T hT
  have hcast : 3 * (T : ℝ) ≤ (3 : ℝ) ^ T := by
    exact_mod_cast hnat
  have hpow : 0 < (3 : ℝ) ^ T := by positivity
  rw [one_div, inv_pow]
  apply (mul_inv_le_iff₀ hpow).2
  norm_num at ⊢
  nlinarith

/-- Conditional first-moment selection on a finite probability space.  If
`f` is bounded by `B`, its expectation is `q`, and the bad set has probability
at most `r < 1`, then some good outcome has value within
`2Br/(1-r) + ε` of `q`. -/
theorem exists_good_value_of_expectation
    {Ω : Type*} [MeasurableSpace Ω] [Finite Ω]
    [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (failure : Set Ω)
    (B q r ε : ℝ)
    (hB : 0 ≤ B) (hr0 : 0 ≤ r) (hr1 : r < 1) (hε : 0 < ε)
    (hbound : ∀ ω, |f ω| ≤ B)
    (hexpect : (∫ ω, f ω ∂μ) = q)
    (hfailure : μ.real failure ≤ r) :
    ∃ ω, ω ∉ failure ∧
      q - (2 * B * r / (1 - r) + ε) < f ω := by
  classical
  let loss := 2 * B * r / (1 - r) + ε
  have hden : 0 < 1 - r := by linarith
  have hloss0 : 0 < loss := by
    dsimp [loss]
    have : 0 ≤ 2 * B * r / (1 - r) := by positivity
    linarith
  have hfint : Integrable f μ := by
    rw [← integrableOn_univ]
    exact IntegrableOn.of_finite Set.finite_univ
  have hqLower : -B ≤ q := by
    rw [← hexpect]
    calc
      -B = ∫ _ω : Ω, -B ∂μ := by simp
      _ ≤ ∫ ω, f ω ∂μ := by
        apply integral_mono
        · exact integrable_const _
        · exact hfint
        · intro ω
          exact (abs_le.mp (hbound ω)).1
  by_contra hno
  push Not at hno
  have hpoint : ∀ ω,
      f ω ≤
        q - loss +
          (if ω ∈ failure then 2 * B + loss else 0) := by
    intro ω
    by_cases hω : ω ∈ failure
    · rw [if_pos hω]
      have hupper := (abs_le.mp (hbound ω)).2
      linarith
    · rw [if_neg hω]
      simpa [loss] using hno ω hω
  have hgint :
      Integrable
        (fun ω =>
          q - loss +
            (if ω ∈ failure then 2 * B + loss else 0)) μ := by
    rw [← integrableOn_univ]
    exact IntegrableOn.of_finite Set.finite_univ
  have hintegral :
      q ≤
        q - loss +
          (2 * B + loss) * μ.real failure := by
    calc
      q = ∫ ω, f ω ∂μ := hexpect.symm
      _ ≤
          ∫ ω,
            q - loss +
              (if ω ∈ failure then 2 * B + loss else 0)
            ∂μ := by
        exact integral_mono hfint hgint hpoint
      _ = q - loss +
          (2 * B + loss) * μ.real failure := by
        have hmeas : MeasurableSet failure :=
          Set.toFinite failure |>.measurableSet
        rw [integral_add (integrable_const _) (by
          rw [← integrableOn_univ]
          exact IntegrableOn.of_finite Set.finite_univ)]
        simp only [integral_const]
        rw [show (fun ω : Ω =>
            if ω ∈ failure then 2 * B + loss else 0) =
            failure.indicator (fun _ => 2 * B + loss) by
          funext ω
          simp [Set.indicator]]
        rw [integral_indicator hmeas]
        simp [mul_comm, measureReal_def]
  have hcoef : 0 ≤ 2 * B + loss := by positivity
  have hupper :
      q - loss + (2 * B + loss) * μ.real failure ≤
        q - loss + (2 * B + loss) * r := by
    gcongr
  have halgebra :
      q - loss + (2 * B + loss) * r < q := by
    have hid :
        -loss + (2 * B + loss) * r =
          -ε * (1 - r) := by
      dsimp [loss]
      field_simp [ne_of_gt hden]
      ring
    rw [show q - loss + (2 * B + loss) * r =
        q + (-loss + (2 * B + loss) * r) by ring, hid]
    have : 0 < ε * (1 - r) := mul_pos hε hden
    linarith
  linarith

end QuantumSep
