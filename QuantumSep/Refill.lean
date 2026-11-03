import QuantumSep.RandomPhases

/-!
# Random norm refill

The refill uses independent fourth-root phases.  The first theorem computes
the exact expected rank-one matrix after adding the missing amplitude.
-/

open scoped BigOperators ComplexConjugate

open MeasureTheory ProbabilityTheory Set

namespace QuantumSep

noncomputable section

theorem integrable_phaseVector_any
    {ι : Type*} [Fintype ι]
    (f : (ι → Fin 4) → ℂ) :
    Integrable f (phaseVectorMeasure ι) := by
  rw [← integrableOn_univ]
  exact IntegrableOn.of_finite Set.finite_univ

/-- Add a fixed real amplitude times an independent unit phase in every
coordinate. -/
def refillVector {ι : Type*} (u : ι → ℂ) (amplitude : ℝ)
    (ω : ι → Fin 4) : ι → ℂ :=
  fun i => u i + (amplitude : ℂ) * phaseCoordinate i ω

/-- The manuscript's missing-norm amplitude. -/
def refillAmplitude
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (u : ι → ℂ) : ℝ :=
  Real.sqrt
    (1 - vectorNormSq u / Fintype.card ι)

theorem refillAmplitude_nonneg
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (u : ι → ℂ) :
    0 ≤ refillAmplitude u :=
  Real.sqrt_nonneg _

theorem refillAmplitude_sq
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (u : ι → ℂ)
    (hnorm : vectorNormSq u ≤ Fintype.card ι) :
    refillAmplitude u ^ 2 =
      1 - vectorNormSq u / Fintype.card ι := by
  unfold refillAmplitude
  rw [Real.sq_sqrt]
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  exact sub_nonneg.mpr ((div_le_one hd).2 hnorm)

theorem refillAmplitude_sq_le_one
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (u : ι → ℂ) :
    refillAmplitude u ^ 2 ≤ 1 := by
  have hnorm0 : 0 ≤ vectorNormSq u := by
    unfold vectorNormSq
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (u i)
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  unfold refillAmplitude
  rw [Real.sq_sqrt']
  apply max_le
  · have : 0 ≤ vectorNormSq u / Fintype.card ι :=
      div_nonneg hnorm0 hd.le
    linarith
  · norm_num

theorem refillAmplitude_le_one
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (u : ι → ℂ) :
    refillAmplitude u ≤ 1 := by
  apply (sq_le_sq₀ (refillAmplitude_nonneg u) (by norm_num)).1
  simpa using refillAmplitude_sq_le_one u

theorem refillAmplitude_balance
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (u : ι → ℂ)
    (hnorm : vectorNormSq u ≤ Fintype.card ι) :
    vectorNormSq u +
        Fintype.card ι * refillAmplitude u ^ 2 =
      Fintype.card ι := by
  rw [refillAmplitude_sq u hnorm]
  have hd : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [hd]
  ring

/-- A refill of a vector bounded coordinatewise by `sigma` is bounded by
`sigma + 1`. -/
theorem refillVector_norm_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (u : ι → ℂ) (sigma : ℝ) (ω : ι → Fin 4)
    (hu : ∀ i, ‖u i‖ ≤ sigma) (i : ι) :
    ‖refillVector u (refillAmplitude u) ω i‖ ≤ sigma + 1 := by
  unfold refillVector
  calc
    ‖u i + (refillAmplitude u : ℂ) * phaseCoordinate i ω‖ ≤
        ‖u i‖ +
          ‖(refillAmplitude u : ℂ) * phaseCoordinate i ω‖ :=
      norm_add_le _ _
    _ = ‖u i‖ + refillAmplitude u := by
      rw [norm_mul]
      simp [phaseCoordinate, abs_of_nonneg (refillAmplitude_nonneg u)]
    _ ≤ sigma + 1 :=
      add_le_add (hu i) (refillAmplitude_le_one u)

/-- Exact second moment of a refilled vector:
`E[breve u breve u*] = u u* + amplitude² I`. -/
theorem refillVector_pair_integral
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℂ) (amplitude : ℝ) (a b : ι) :
    (∫ ω,
      star (refillVector u amplitude ω a) *
        refillVector u amplitude ω b
      ∂phaseVectorMeasure ι) =
      star (u a) * u b +
        amplitude ^ 2 * (if a = b then 1 else 0) := by
  let A : (ι → Fin 4) → ℂ := fun _ => star (u a) * u b
  let B : (ι → Fin 4) → ℂ := fun ω =>
    (amplitude : ℂ) * star (u a) * phaseCoordinate b ω
  let C : (ι → Fin 4) → ℂ := fun ω =>
    (amplitude : ℂ) * star (phaseCoordinate a ω) * u b
  let D : (ι → Fin 4) → ℂ := fun ω =>
    ((amplitude : ℂ) ^ 2) *
      (star (phaseCoordinate a ω) * phaseCoordinate b ω)
  have hexpand : ∀ ω,
      star (refillVector u amplitude ω a) *
          refillVector u amplitude ω b =
        A ω + B ω + C ω + D ω := by
    intro ω
    dsimp [refillVector, A, B, C, D]
    rw [map_add, map_mul, starRingEnd_apply, Complex.conj_ofReal]
    ring
  have hA := integrable_phaseVector_any A
  have hB := integrable_phaseVector_any B
  have hC := integrable_phaseVector_any C
  have hD := integrable_phaseVector_any D
  rw [integral_congr_ae (Filter.Eventually.of_forall hexpand)]
  change (∫ ω, (A + B + C) ω + D ω ∂phaseVectorMeasure ι) =
    star (u a) * u b + amplitude ^ 2 * (if a = b then 1 else 0)
  rw [integral_add ((hA.add hB).add hC) hD]
  change
    (∫ ω, (A + B) ω + C ω ∂phaseVectorMeasure ι) +
        ∫ ω, D ω ∂phaseVectorMeasure ι =
      star (u a) * u b + amplitude ^ 2 * (if a = b then 1 else 0)
  rw [integral_add (hA.add hB) hC]
  change
    ((∫ ω, A ω + B ω ∂phaseVectorMeasure ι) +
          ∫ ω, C ω ∂phaseVectorMeasure ι) +
        ∫ ω, D ω ∂phaseVectorMeasure ι =
      star (u a) * u b + amplitude ^ 2 * (if a = b then 1 else 0)
  rw [integral_add hA hB]
  have hIA :
      (∫ ω, A ω ∂phaseVectorMeasure ι) = star (u a) * u b := by
    simp [A]
  have hIB :
      (∫ ω, B ω ∂phaseVectorMeasure ι) = 0 := by
    have heq : ∀ ω,
        B ω =
          ((amplitude : ℂ) * star (u a)) * phaseCoordinate b ω := by
      intro ω
      dsimp [B]
    rw [integral_congr_ae (Filter.Eventually.of_forall heq)]
    rw [integral_const_mul, integral_phaseCoordinate, mul_zero]
  have hIC :
      (∫ ω, C ω ∂phaseVectorMeasure ι) = 0 := by
    have heq : ∀ ω,
        C ω =
          ((amplitude : ℂ) * u b) * star (phaseCoordinate a ω) := by
      intro ω
      dsimp [C]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall heq)]
    rw [integral_const_mul, integral_star_phaseCoordinate, mul_zero]
  have hID :
      (∫ ω, D ω ∂phaseVectorMeasure ι) =
        ((amplitude : ℂ) ^ 2) * (if a = b then 1 else 0) := by
    dsimp [D]
    rw [integral_const_mul]
    congr 1
    exact integral_star_phase_mul_phase a b
  rw [hIA, hIB, hIC, hID]
  ring

/-- The coefficient matrix of the rank-one operator `x x*`, in the index
convention used by `matrixQuarticForm`. -/
def pairCoefficients {ι : Type*} (x : ι → ℂ) : ι → ι → ℂ :=
  fun a b => star (x a) * x b

/-- The complex numerator of the bipartite quartic form.  Keeping the
normalizing cardinality and real part out of this definition makes its
bilinearity transparent. -/
def complexQuarticNumerator
    {ι : Type*} [Fintype ι]
    (M : BipartiteMatrix ι)
    (X Y : ι → ι → ℂ) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ e, M (a, c) (b, e) * X a b * Y c e

/-- Averaging one refill replaces its rank-one coefficient matrix by the
original coefficient matrix plus a scalar diagonal. -/
theorem integral_complexQuarticNumerator_refill_second
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : BipartiteMatrix ι) (X : ι → ι → ℂ)
    (v : ι → ℂ) (amplitude : ℝ) :
    (∫ ω,
      complexQuarticNumerator M X
        (pairCoefficients (refillVector v amplitude ω))
      ∂phaseVectorMeasure ι) =
      complexQuarticNumerator M X
        (fun c e =>
          pairCoefficients v c e +
            amplitude ^ 2 * (if c = e then 1 else 0)) := by
  unfold complexQuarticNumerator
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _ha
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro b _hb
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro c _hc
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro e _he
          unfold pairCoefficients
          rw [integral_const_mul]
          rw [refillVector_pair_integral]
        · intro e _he
          exact integrable_phaseVector_any _
      · intro c _hc
        exact integrable_phaseVector_any _
    · intro b _hb
      exact integrable_phaseVector_any _
  · intro a _ha
    exact integrable_phaseVector_any _

/-- Swap the two tensor factors of a bipartite matrix. -/
def swapBipartiteFactors
    {ι : Type*} (M : BipartiteMatrix ι) : BipartiteMatrix ι :=
  fun (c, a) (e, b) => M (a, c) (b, e)

theorem complexQuarticNumerator_swap
    {ι : Type*} [Fintype ι]
    (M : BipartiteMatrix ι) (X Y : ι → ι → ℂ) :
    complexQuarticNumerator M X Y =
      complexQuarticNumerator (swapBipartiteFactors M) Y X := by
  unfold complexQuarticNumerator swapBipartiteFactors
  calc
    (∑ a, ∑ b, ∑ c, ∑ e,
        M (a, c) (b, e) * X a b * Y c e) =
        ∑ a, ∑ c, ∑ b, ∑ e,
          M (a, c) (b, e) * X a b * Y c e := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ e,
          M (a, c) (b, e) * X a b * Y c e := by
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ e, ∑ b,
          M (a, c) (b, e) * X a b * Y c e := by
      apply Finset.sum_congr rfl
      intro c _hc
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ e, ∑ a, ∑ b,
          M (a, c) (b, e) * X a b * Y c e := by
      apply Finset.sum_congr rfl
      intro c _hc
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ e, ∑ a, ∑ b,
          M (a, c) (b, e) * Y c e * X a b := by
      apply Finset.sum_congr rfl
      intro c _hc
      apply Finset.sum_congr rfl
      intro e _he
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      ring

/-- Exact expectation after independently refilling both vectors. -/
theorem integral_complexQuarticNumerator_refill_both
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : BipartiteMatrix ι) (u v : ι → ℂ)
    (amplitudeU amplitudeV : ℝ) :
    (∫ ξ,
      ∫ ζ,
        complexQuarticNumerator M
          (pairCoefficients (refillVector u amplitudeU ξ))
          (pairCoefficients (refillVector v amplitudeV ζ))
        ∂phaseVectorMeasure ι
      ∂phaseVectorMeasure ι) =
      complexQuarticNumerator M
        (fun a b =>
          pairCoefficients u a b +
            amplitudeU ^ 2 * (if a = b then 1 else 0))
        (fun c e =>
          pairCoefficients v c e +
            amplitudeV ^ 2 * (if c = e then 1 else 0)) := by
  simp_rw [integral_complexQuarticNumerator_refill_second]
  let Y : ι → ι → ℂ := fun c e =>
    pairCoefficients v c e +
      amplitudeV ^ 2 * (if c = e then 1 else 0)
  simp_rw [complexQuarticNumerator_swap M]
  rw [integral_complexQuarticNumerator_refill_second
    (swapBipartiteFactors M) Y u amplitudeU]

/-- The matrix coefficients of the identity. -/
def deltaCoefficients
    {ι : Type*} [DecidableEq ι] : ι → ι → ℂ :=
  fun a b => if a = b then 1 else 0

theorem partialTrace1_swapBipartiteFactors
    {ι : Type*} [Fintype ι]
    (M : BipartiteMatrix ι) :
    partialTrace1 (swapBipartiteFactors M) = partialTrace0 M := by
  ext c e
  rfl

theorem complexQuarticNumerator_delta_right_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : BipartiteMatrix ι) (X : ι → ι → ℂ)
    (htrace : partialTrace1 M = 0) :
    complexQuarticNumerator M X deltaCoefficients = 0 := by
  unfold complexQuarticNumerator deltaCoefficients
  simp only [mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq]
  have hentry (a b : ι) : (∑ c, M (a, c) (b, c)) = 0 := by
    simpa [partialTrace1] using congrFun (congrFun htrace a) b
  simp_rw [← Finset.sum_mul, hentry, zero_mul]
  simp

theorem complexQuarticNumerator_delta_left_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : BipartiteMatrix ι) (Y : ι → ι → ℂ)
    (htrace : partialTrace0 M = 0) :
    complexQuarticNumerator M deltaCoefficients Y = 0 := by
  rw [complexQuarticNumerator_swap]
  apply complexQuarticNumerator_delta_right_eq_zero
  rw [partialTrace1_swapBipartiteFactors, htrace]

theorem complexQuarticNumerator_add_right
    {ι : Type*} [Fintype ι]
    (M : BipartiteMatrix ι) (X Y Z : ι → ι → ℂ) :
    complexQuarticNumerator M X (fun c e => Y c e + Z c e) =
      complexQuarticNumerator M X Y +
        complexQuarticNumerator M X Z := by
  simp [complexQuarticNumerator, mul_add, Finset.sum_add_distrib]

theorem complexQuarticNumerator_add_left
    {ι : Type*} [Fintype ι]
    (M : BipartiteMatrix ι) (X Z Y : ι → ι → ℂ) :
    complexQuarticNumerator M (fun a b => X a b + Z a b) Y =
      complexQuarticNumerator M X Y +
        complexQuarticNumerator M Z Y := by
  rw [complexQuarticNumerator_swap]
  rw [complexQuarticNumerator_add_right]
  rw [← complexQuarticNumerator_swap M X Y]
  rw [← complexQuarticNumerator_swap M Z Y]

theorem complexQuarticNumerator_scaled_delta_right_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : BipartiteMatrix ι) (X : ι → ι → ℂ) (beta : ℂ)
    (htrace : partialTrace1 M = 0) :
    complexQuarticNumerator M X
      (fun c e => beta * deltaCoefficients c e) = 0 := by
  unfold complexQuarticNumerator deltaCoefficients
  simp only [mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq]
  have hentry (a b : ι) : (∑ c, M (a, c) (b, c)) = 0 := by
    simpa [partialTrace1] using congrFun (congrFun htrace a) b
  simp only [mul_assoc]
  simp_rw [← Finset.sum_mul, hentry, zero_mul]
  simp

theorem complexQuarticNumerator_scaled_delta_left_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : BipartiteMatrix ι) (Y : ι → ι → ℂ) (alpha : ℂ)
    (htrace : partialTrace0 M = 0) :
    complexQuarticNumerator M
      (fun a b => alpha * deltaCoefficients a b) Y = 0 := by
  rw [complexQuarticNumerator_swap]
  apply complexQuarticNumerator_scaled_delta_right_eq_zero
  rw [partialTrace1_swapBipartiteFactors, htrace]

/-- If both partial traces vanish, all diagonal covariance corrections in the
refill expectation vanish. -/
theorem complexQuarticNumerator_diagonal_corrections
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : BipartiteMatrix ι) (X Y : ι → ι → ℂ)
    (alpha beta : ℂ)
    (htrace0 : partialTrace0 M = 0)
    (htrace1 : partialTrace1 M = 0) :
    complexQuarticNumerator M
        (fun a b => X a b + alpha * deltaCoefficients a b)
        (fun c e => Y c e + beta * deltaCoefficients c e) =
      complexQuarticNumerator M X Y := by
  rw [complexQuarticNumerator_add_left]
  rw [complexQuarticNumerator_add_right]
  rw [complexQuarticNumerator_add_right]
  have hrightX :
      complexQuarticNumerator M X
        (fun c e => beta * deltaCoefficients c e) = 0 :=
    complexQuarticNumerator_scaled_delta_right_eq_zero
      M X beta htrace1
  have hleft :
      complexQuarticNumerator M
        (fun a b => alpha * deltaCoefficients a b) Y = 0 :=
    complexQuarticNumerator_scaled_delta_left_eq_zero
      M Y alpha htrace0
  have hboth :
      complexQuarticNumerator M
        (fun a b => alpha * deltaCoefficients a b)
        (fun c e => beta * deltaCoefficients c e) = 0 :=
    complexQuarticNumerator_scaled_delta_left_eq_zero
      M _ alpha htrace0
  rw [hrightX, hleft, hboth]
  simp

/-- The central refill identity: under zero partial traces, independent
random-phase refill preserves the quartic objective in expectation exactly. -/
theorem integral_complexQuarticNumerator_refill_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : BipartiteMatrix ι) (u v : ι → ℂ)
    (amplitudeU amplitudeV : ℝ)
    (htrace0 : partialTrace0 M = 0)
    (htrace1 : partialTrace1 M = 0) :
    (∫ ξ,
      ∫ ζ,
        complexQuarticNumerator M
          (pairCoefficients (refillVector u amplitudeU ξ))
          (pairCoefficients (refillVector v amplitudeV ζ))
        ∂phaseVectorMeasure ι
      ∂phaseVectorMeasure ι) =
      complexQuarticNumerator M
        (pairCoefficients u) (pairCoefficients v) := by
  rw [integral_complexQuarticNumerator_refill_both]
  simpa [deltaCoefficients] using
    complexQuarticNumerator_diagonal_corrections
      M (pairCoefficients u) (pairCoefficients v)
      (amplitudeU ^ 2) (amplitudeV ^ 2) htrace0 htrace1

/-- The real quartic form is the real part of the complex numerator divided
by `d²`. -/
theorem matrixQuarticForm_eq_complexNumerator
    {ι : Type*} [Fintype ι]
    (M : BipartiteMatrix ι) (x y : ι → ℂ) :
    matrixQuarticForm M x y =
      (complexQuarticNumerator M
        (pairCoefficients x) (pairCoefficients y)).re /
          cardR (ι := ι) ^ 2 := by
  unfold matrixQuarticForm complexQuarticNumerator
  simp only [Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  apply Finset.sum_congr rfl
  intro c _hc
  apply Finset.sum_congr rfl
  intro e _he
  unfold quarticSummand pairCoefficients
  ring

/-- Under zero partial traces, random-phase refill preserves the manuscript's
real quartic form in expectation. -/
theorem integral_matrixQuarticForm_refill_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : BipartiteMatrix ι) (u v : ι → ℂ)
    (amplitudeU amplitudeV : ℝ)
    (htrace0 : partialTrace0 M = 0)
    (htrace1 : partialTrace1 M = 0) :
    (∫ ξ,
      ∫ ζ,
        matrixQuarticForm M
          (refillVector u amplitudeU ξ)
          (refillVector v amplitudeV ζ)
        ∂phaseVectorMeasure ι
      ∂phaseVectorMeasure ι) =
      matrixQuarticForm M u v := by
  have hc := integral_complexQuarticNumerator_refill_eq
    M u v amplitudeU amplitudeV htrace0 htrace1
  have houter :
      Integrable
        (fun ξ =>
          ∫ ζ,
            complexQuarticNumerator M
              (pairCoefficients (refillVector u amplitudeU ξ))
              (pairCoefficients (refillVector v amplitudeV ζ))
            ∂phaseVectorMeasure ι)
        (phaseVectorMeasure ι) :=
    integrable_phaseVector_any _
  have hinner (ξ : ι → Fin 4) :
      Integrable
        (fun ζ =>
          complexQuarticNumerator M
            (pairCoefficients (refillVector u amplitudeU ξ))
            (pairCoefficients (refillVector v amplitudeV ζ)))
        (phaseVectorMeasure ι) :=
    integrable_phaseVector_any _
  have hrOuter :
      (∫ ξ,
        (∫ ζ,
          complexQuarticNumerator M
            (pairCoefficients (refillVector u amplitudeU ξ))
            (pairCoefficients (refillVector v amplitudeV ζ))
          ∂phaseVectorMeasure ι).re
        ∂phaseVectorMeasure ι) =
        (complexQuarticNumerator M
          (pairCoefficients u) (pairCoefficients v)).re := by
    calc
      _ = (∫ ξ,
          ∫ ζ,
            complexQuarticNumerator M
              (pairCoefficients (refillVector u amplitudeU ξ))
              (pairCoefficients (refillVector v amplitudeV ζ))
            ∂phaseVectorMeasure ι
          ∂phaseVectorMeasure ι).re :=
        integral_re (𝕜 := ℂ) houter
      _ = _ := congrArg Complex.re hc
  have hr :
      (∫ ξ,
        ∫ ζ,
          (complexQuarticNumerator M
            (pairCoefficients (refillVector u amplitudeU ξ))
            (pairCoefficients (refillVector v amplitudeV ζ))).re
          ∂phaseVectorMeasure ι
        ∂phaseVectorMeasure ι) =
        (complexQuarticNumerator M
          (pairCoefficients u) (pairCoefficients v)).re := by
    calc
      _ = ∫ ξ,
          (∫ ζ,
            complexQuarticNumerator M
              (pairCoefficients (refillVector u amplitudeU ξ))
              (pairCoefficients (refillVector v amplitudeV ζ))
            ∂phaseVectorMeasure ι).re
          ∂phaseVectorMeasure ι := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ξ =>
          integral_re (𝕜 := ℂ) (hinner ξ)
      _ = _ := hrOuter
  rw [matrixQuarticForm_eq_complexNumerator]
  simp_rw [matrixQuarticForm_eq_complexNumerator]
  simp_rw [div_eq_inv_mul]
  simp_rw [integral_const_mul ((cardR (ι := ι) ^ 2)⁻¹)]
  rw [hr]

/-- Inner product with the random phase vector, in the orientation occurring
in the refill norm expansion. -/
def phaseInner
    {ι : Type*} [Fintype ι]
    (u : ι → ℂ) (ω : ι → Fin 4) : ℂ :=
  ∑ i, u i * star (phaseCoordinate i ω)

theorem phaseInner_star_mul_expand
    {ι : Type*} [Fintype ι]
    (u : ι → ℂ) (ω : ι → Fin 4) :
    star (phaseInner u ω) * phaseInner u ω =
      ∑ a, ∑ b,
        (star (u a) * u b) *
          (phaseCoordinate a ω * star (phaseCoordinate b ω)) := by
  unfold phaseInner
  change
    (starRingEnd ℂ) (∑ i, u i * star (phaseCoordinate i ω)) *
        ∑ i, u i * star (phaseCoordinate i ω) = _
  rw [map_sum (starRingEnd ℂ)
    (fun i => u i * star (phaseCoordinate i ω)) Finset.univ]
  simp_rw [map_mul, starRingEnd_apply, star_star]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _hb
  ring

/-- Exact second moment of the phase inner product. -/
theorem integral_phaseInner_star_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℂ) :
    (∫ ω, star (phaseInner u ω) * phaseInner u ω
        ∂phaseVectorMeasure ι) =
      (vectorNormSq u : ℂ) := by
  rw [show (vectorNormSq u : ℂ) =
      ∑ i, (Complex.normSq (u i) : ℂ) by
    simp [vectorNormSq]]
  rw [integral_congr_ae
    (Filter.Eventually.of_forall (phaseInner_star_mul_expand u))]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _ha
    rw [integral_finsetSum]
    · have hcov (b : ι) :
          (∫ ω,
            phaseCoordinate a ω * star (phaseCoordinate b ω)
            ∂phaseVectorMeasure ι) =
            if b = a then 1 else 0 := by
          rw [show (fun ω =>
              phaseCoordinate a ω * star (phaseCoordinate b ω)) =
              (fun ω =>
                star (phaseCoordinate b ω) * phaseCoordinate a ω) by
            funext ω
            ring]
          exact integral_star_phase_mul_phase b a
      simp_rw [integral_const_mul, hcov]
      simp only [mul_ite, mul_one, mul_zero,
        Fintype.sum_ite_eq']
      rw [Complex.normSq_eq_conj_mul_self]
      simp only [starRingEnd_apply]
    · intro b _hb
      exact integrable_phaseVector_any _
  · intro a _ha
    exact integrable_phaseVector_any _

theorem integral_phaseInner_normSq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℂ) :
    (∫ ω, Complex.normSq (phaseInner u ω)
        ∂phaseVectorMeasure ι) =
      vectorNormSq u := by
  have hc := integral_phaseInner_star_mul u
  calc
    (∫ ω, Complex.normSq (phaseInner u ω)
        ∂phaseVectorMeasure ι) =
        ∫ ω, (star (phaseInner u ω) * phaseInner u ω).re
          ∂phaseVectorMeasure ι := by
      congr 1
      funext ω
      simpa using congrArg Complex.re
        (Complex.normSq_eq_conj_mul_self
          (z := phaseInner u ω))
    _ = (∫ ω, star (phaseInner u ω) * phaseInner u ω
          ∂phaseVectorMeasure ι).re :=
      integral_re (𝕜 := ℂ)
        (integrable_phaseVector_any (ι := ι)
          (fun ω =>
            star (phaseInner u ω) * phaseInner u ω))
    _ = vectorNormSq u := by
      rw [hc]
      simp

/-- Exact pointwise norm expansion for a refilled vector. -/
theorem vectorNormSq_refill_expand
    {ι : Type*} [Fintype ι]
    (u : ι → ℂ) (amplitude : ℝ) (ω : ι → Fin 4) :
    vectorNormSq (refillVector u amplitude ω) =
      vectorNormSq u +
        Fintype.card ι * amplitude ^ 2 +
        2 * amplitude * (phaseInner u ω).re := by
  unfold vectorNormSq refillVector phaseInner
  simp_rw [Complex.normSq_add]
  have hphase (i : ι) :
      Complex.normSq ((amplitude : ℂ) * phaseCoordinate i ω) =
        amplitude ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    simp [phaseCoordinate, Complex.normSq_eq_norm_sq]
    ring_nf
  simp_rw [hphase]
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul]
  have hcross (i : ι) :
      2 * (u i * (starRingEnd ℂ)
        ((amplitude : ℂ) * phaseCoordinate i ω)).re =
        2 * amplitude *
          (u i * star (phaseCoordinate i ω)).re := by
    have hc :
        u i * (starRingEnd ℂ)
            ((amplitude : ℂ) * phaseCoordinate i ω) =
          (amplitude : ℂ) *
            (u i * star (phaseCoordinate i ω)) := by
      rw [map_mul, RCLike.star_def, Complex.conj_ofReal]
      ring
    rw [hc]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    ring
  simp_rw [hcross]
  simp only [Complex.re_sum, Finset.card_univ]
  rw [← Finset.mul_sum]

/-- The squared norm deviation is controlled pointwise by the squared phase
inner product. -/
theorem vectorNormSq_refill_deviation_sq_le
    {ι : Type*} [Fintype ι]
    (u : ι → ℂ) (amplitude : ℝ) (ω : ι → Fin 4)
    (hbalance :
      vectorNormSq u + Fintype.card ι * amplitude ^ 2 =
        Fintype.card ι) :
    (vectorNormSq (refillVector u amplitude ω) -
        Fintype.card ι) ^ 2 ≤
      4 * amplitude ^ 2 * Complex.normSq (phaseInner u ω) := by
  rw [vectorNormSq_refill_expand, hbalance]
  have hre : |(phaseInner u ω).re| ≤ ‖phaseInner u ω‖ :=
    Complex.abs_re_le_norm _
  have hreSq :
      (phaseInner u ω).re ^ 2 ≤ ‖phaseInner u ω‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    nlinarith [sq_nonneg (phaseInner u ω).im]
  have hmul := mul_le_mul_of_nonneg_left hreSq
    (show 0 ≤ 4 * amplitude ^ 2 by positivity)
  rw [Complex.normSq_eq_norm_sq]
  nlinarith

/-- Integrated Chebyshev numerator for the refill norm. -/
theorem integral_refill_deviation_sq_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℂ) (amplitude : ℝ)
    (hbalance :
      vectorNormSq u + Fintype.card ι * amplitude ^ 2 =
        Fintype.card ι) :
    (∫ ω,
      (vectorNormSq (refillVector u amplitude ω) -
        Fintype.card ι) ^ 2
      ∂phaseVectorMeasure ι) ≤
      4 * amplitude ^ 2 * vectorNormSq u := by
  calc
    (∫ ω,
      (vectorNormSq (refillVector u amplitude ω) -
        Fintype.card ι) ^ 2
      ∂phaseVectorMeasure ι) ≤
        ∫ ω, 4 * amplitude ^ 2 *
          Complex.normSq (phaseInner u ω)
          ∂phaseVectorMeasure ι := by
      apply integral_mono
      · rw [← integrableOn_univ]
        exact IntegrableOn.of_finite Set.finite_univ
      · rw [← integrableOn_univ]
        exact IntegrableOn.of_finite Set.finite_univ
      · exact fun ω => vectorNormSq_refill_deviation_sq_le
          u amplitude ω hbalance
    _ = 4 * amplitude ^ 2 * vectorNormSq u := by
      rw [integral_const_mul, integral_phaseInner_normSq]

/-- Chebyshev's inequality specialized to the refill norm.  In the
manuscript's balanced case, the probability of raw squared-norm error greater
than `t*d` is at most `4/(t² d)`. -/
theorem refill_norm_failure_measureReal_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (u : ι → ℂ) (amplitude t : ℝ)
    (ht : 0 < t)
    (hamp : amplitude ^ 2 ≤ 1)
    (hnorm : vectorNormSq u ≤ Fintype.card ι)
    (hbalance :
      vectorNormSq u + Fintype.card ι * amplitude ^ 2 =
        Fintype.card ι) :
    (phaseVectorMeasure ι).real
        {ω |
          t * Fintype.card ι <
            |vectorNormSq (refillVector u amplitude ω) -
              Fintype.card ι|} ≤
      4 / (t ^ 2 * Fintype.card ι) := by
  let d : ℝ := Fintype.card ι
  let deviation : (ι → Fin 4) → ℝ := fun ω =>
    vectorNormSq (refillVector u amplitude ω) - d
  let failure : Set (ι → Fin 4) := {ω | t * d < |deviation ω|}
  let markovEvent : Set (ι → Fin 4) :=
    {ω | (t * d) ^ 2 ≤ (deviation ω) ^ 2}
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Fintype.card_pos
  have hsubset : failure ⊆ markovEvent := by
    intro ω hω
    dsimp [failure, markovEvent] at hω ⊢
    have hsquare :
        (t * d) ^ 2 ≤ |deviation ω| ^ 2 :=
      (sq_le_sq₀ (mul_pos ht hd).le (abs_nonneg _)).2 hω.le
    simpa [sq_abs] using hsquare
  have hf_nonneg :
      0 ≤ᵐ[phaseVectorMeasure ι] fun ω => (deviation ω) ^ 2 :=
    Filter.Eventually.of_forall fun _ => sq_nonneg _
  have hf_int :
      Integrable (fun ω => (deviation ω) ^ 2)
        (phaseVectorMeasure ι) := by
    rw [← integrableOn_univ]
    exact IntegrableOn.of_finite Set.finite_univ
  have hmarkov :=
    mul_meas_ge_le_integral_of_nonneg
      (μ := phaseVectorMeasure ι) hf_nonneg hf_int ((t * d) ^ 2)
  have hfailure :
      (phaseVectorMeasure ι).real failure ≤
        (phaseVectorMeasure ι).real markovEvent :=
    measureReal_mono hsubset
  have hexpect :
      (∫ ω, (deviation ω) ^ 2 ∂phaseVectorMeasure ι) ≤ 4 * d := by
    have hraw := integral_refill_deviation_sq_le
      u amplitude hbalance
    dsimp [deviation, d]
    calc
      (∫ ω,
        (vectorNormSq (refillVector u amplitude ω) -
          ↑(Fintype.card ι)) ^ 2
        ∂phaseVectorMeasure ι) ≤
          4 * amplitude ^ 2 * vectorNormSq u := hraw
      _ ≤ 4 * 1 * Fintype.card ι := by
        have hnorm0 : 0 ≤ vectorNormSq u := by
          unfold vectorNormSq
          exact Finset.sum_nonneg fun i _ =>
            Complex.normSq_nonneg (u i)
        have hproduct := mul_le_mul hamp hnorm hnorm0 (by norm_num)
        nlinarith
      _ = 4 * ↑(Fintype.card ι) := by ring
  change (phaseVectorMeasure ι).real failure ≤ 4 / (t ^ 2 * d)
  have hmul :
      (t * d) ^ 2 * (phaseVectorMeasure ι).real failure ≤ 4 * d := by
    calc
      (t * d) ^ 2 * (phaseVectorMeasure ι).real failure ≤
          (t * d) ^ 2 *
            (phaseVectorMeasure ι).real markovEvent := by
        gcongr
      _ ≤ ∫ ω, (deviation ω) ^ 2 ∂phaseVectorMeasure ι := hmarkov
      _ ≤ 4 * d := hexpect
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos ht) hd)).2
  calc
    (phaseVectorMeasure ι).real failure * (t ^ 2 * d) =
        ((t * d) ^ 2 *
          (phaseVectorMeasure ι).real failure) / d := by
      field_simp [ne_of_gt hd]
    _ ≤ (4 * d) / d := by
      gcongr
    _ = 4 := by
      field_simp [ne_of_gt hd]

/-- Union bound for one failure event in each coordinate of a product
probability space. -/
theorem measureReal_prod_failure_union_le
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ : Measure Ω₁) (ν : Measure Ω₂)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set Ω₁) (B : Set Ω₂) :
    (μ.prod ν).real
        ((A ×ˢ Set.univ) ∪ (Set.univ ×ˢ B)) ≤
      μ.real A + ν.real B := by
  calc
    (μ.prod ν).real
        ((A ×ˢ Set.univ) ∪ (Set.univ ×ˢ B)) ≤
        (μ.prod ν).real (A ×ˢ Set.univ) +
          (μ.prod ν).real (Set.univ ×ˢ B) :=
      measureReal_union_le _ _
    _ = μ.real A + ν.real B := by
      rw [measureReal_prod_prod, measureReal_prod_prod]
      simp

/-- A failure event of probability strictly less than one omits an outcome. -/
theorem exists_outside_of_measureReal_lt_one
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (failure : Set Ω)
    (hfailure : μ.real failure < 1) :
    ∃ ω, ω ∉ failure := by
  by_contra hno
  push Not at hno
  have hall : failure = Set.univ := Set.eq_univ_of_forall hno
  rw [hall] at hfailure
  simpa using hfailure

/-- If `t² d > 8`, there is a simultaneous phase outcome for which both
refilled vectors have squared norms within `t d` of `d`. -/
theorem exists_refill_pair_with_good_norms
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (u v : ι → ℂ) (amplitudeU amplitudeV t : ℝ)
    (ht : 0 < t)
    (hampU : amplitudeU ^ 2 ≤ 1)
    (hampV : amplitudeV ^ 2 ≤ 1)
    (hnormU : vectorNormSq u ≤ Fintype.card ι)
    (hnormV : vectorNormSq v ≤ Fintype.card ι)
    (hbalanceU :
      vectorNormSq u + Fintype.card ι * amplitudeU ^ 2 =
        Fintype.card ι)
    (hbalanceV :
      vectorNormSq v + Fintype.card ι * amplitudeV ^ 2 =
        Fintype.card ι)
    (hdimension : 8 < t ^ 2 * Fintype.card ι) :
    ∃ ξ ζ,
      |vectorNormSq (refillVector u amplitudeU ξ) -
          Fintype.card ι| ≤ t * Fintype.card ι ∧
      |vectorNormSq (refillVector v amplitudeV ζ) -
          Fintype.card ι| ≤ t * Fintype.card ι := by
  let μ := phaseVectorMeasure ι
  let failureU : Set (ι → Fin 4) := {ξ |
    t * Fintype.card ι <
      |vectorNormSq (refillVector u amplitudeU ξ) -
        Fintype.card ι|}
  let failureV : Set (ι → Fin 4) := {ζ |
    t * Fintype.card ι <
      |vectorNormSq (refillVector v amplitudeV ζ) -
        Fintype.card ι|}
  let failurePair : Set ((ι → Fin 4) × (ι → Fin 4)) :=
    (failureU ×ˢ Set.univ) ∪ (Set.univ ×ˢ failureV)
  have hU : μ.real failureU ≤
      4 / (t ^ 2 * Fintype.card ι) := by
    exact refill_norm_failure_measureReal_le
      u amplitudeU t ht hampU hnormU hbalanceU
  have hV : μ.real failureV ≤
      4 / (t ^ 2 * Fintype.card ι) := by
    exact refill_norm_failure_measureReal_le
      v amplitudeV t ht hampV hnormV hbalanceV
  have hden : 0 < t ^ 2 * (Fintype.card ι : ℝ) := by
    have hd : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast Fintype.card_pos
    positivity
  have hfrac : 8 / (t ^ 2 * (Fintype.card ι : ℝ)) < 1 :=
    (div_lt_one hden).2 hdimension
  have hpair :
      (μ.prod μ).real failurePair < 1 := by
    calc
      (μ.prod μ).real failurePair ≤
          μ.real failureU + μ.real failureV :=
        measureReal_prod_failure_union_le μ μ failureU failureV
      _ ≤ 4 / (t ^ 2 * Fintype.card ι) +
          4 / (t ^ 2 * Fintype.card ι) := add_le_add hU hV
      _ = 8 / (t ^ 2 * Fintype.card ι) := by ring
      _ < 1 := hfrac
  obtain ⟨⟨ξ, ζ⟩, hgood⟩ :=
    exists_outside_of_measureReal_lt_one
      (μ.prod μ) failurePair hpair
  refine ⟨ξ, ζ, ?_, ?_⟩
  · have : ξ ∉ failureU := by
      intro hξ
      exact hgood (Or.inl ⟨hξ, Set.mem_univ ζ⟩)
    dsimp [failureU] at this
    exact le_of_not_gt this
  · have : ζ ∉ failureV := by
      intro hζ
      exact hgood (Or.inr ⟨Set.mem_univ ξ, hζ⟩)
    dsimp [failureV] at this
    exact le_of_not_gt this

end

end QuantumSep
