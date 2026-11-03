import QuantumSep.MatrixPrelim
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal ComplexConjugate

/-!
# Standard complex Gaussian moments and Wick's identity

This file constructs standard complex Gaussian coordinates from independent
real `N(0, 1/2)` variables.  The real moments are derived from mathlib's
Gaussian moment-generating function; Wick's quadratic identity is therefore
not an assumption.
-/

namespace QuantumSep

noncomputable section

private lemma deriv_exp_quadratic_chain (v : ℝ) :
    let f0 : ℝ → ℝ := fun t => rexp (v * t ^ 2 / 2)
    let f1 : ℝ → ℝ := fun t => v * t * f0 t
    let f2 : ℝ → ℝ := fun t => (v + v ^ 2 * t ^ 2) * f0 t
    let f3 : ℝ → ℝ := fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * f0 t
    let f4 : ℝ → ℝ := fun t =>
      (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * f0 t
    deriv f0 = f1 ∧ deriv f1 = f2 ∧ deriv f2 = f3 ∧ deriv f3 = f4 := by
  dsimp only
  let f0 : ℝ → ℝ := fun t => rexp (v * t ^ 2 / 2)
  let f1 : ℝ → ℝ := fun t => v * t * f0 t
  let f2 : ℝ → ℝ := fun t => (v + v ^ 2 * t ^ 2) * f0 t
  let f3 : ℝ → ℝ := fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * f0 t
  let f4 : ℝ → ℝ := fun t =>
    (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * f0 t
  have h0 : deriv f0 = f1 := by
    funext t
    dsimp [f0, f1]
    rw [_root_.deriv_exp (by fun_prop)]
    rw [deriv_div_const]
    rw [deriv_const_mul_field]
    rw [deriv_pow_field]
    ring
  have h1 : deriv f1 = f2 := by
    funext t
    change deriv (fun s : ℝ => (v * s) * f0 s) t =
      (v + v ^ 2 * t ^ 2) * f0 t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    rw [deriv_const_mul_id, h0]
    dsimp [f1]
    ring
  have h2 : deriv f2 = f3 := by
    funext t
    change deriv (fun s : ℝ => (v + v ^ 2 * s ^ 2) * f0 s) t =
      (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * f0 t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    have hp :
        deriv (fun s : ℝ => v + v ^ 2 * s ^ 2) t =
          2 * v ^ 2 * t := by
      rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_const']
      rw [deriv_const_mul_field, deriv_pow_field]
      ring
    rw [hp, h0]
    dsimp [f1]
    ring
  have h3 : deriv f3 = f4 := by
    funext t
    change deriv
      (fun s : ℝ => (3 * v ^ 2 * s + v ^ 3 * s ^ 3) * f0 s) t =
      (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * f0 t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    have hp :
        deriv (fun s : ℝ => 3 * v ^ 2 * s + v ^ 3 * s ^ 3) t =
          3 * v ^ 2 + 3 * v ^ 3 * t ^ 2 := by
      rw [deriv_fun_add (by fun_prop) (by fun_prop)]
      rw [deriv_const_mul_id]
      rw [deriv_const_mul_field, deriv_pow_field]
      ring
    rw [hp, h0]
    dsimp [f1]
    ring
  exact ⟨h0, h1, h2, h3⟩

/-- The second raw moment of a centered real Gaussian is its variance. -/
theorem integral_sq_gaussianReal_zero (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

/-- Centered real Gaussians have vanishing third moment. -/
theorem integral_cube_gaussianReal_zero (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 3 ∂gaussianReal 0 v) = 0 := by
  have hm := iteratedDeriv_mgf_zero
    (X := fun x : ℝ => x) (μ := gaussianReal 0 v) (by simp) 3
  have hm' :
      iteratedDeriv 3 (mgf (fun x : ℝ => x) (gaussianReal 0 v)) 0 =
        ∫ x : ℝ, x ^ 3 ∂gaussianReal 0 v := by simpa using hm
  rw [← hm', mgf_fun_id_gaussianReal]
  rw [show (fun t : ℝ => rexp (0 * t + v * t ^ 2 / 2)) =
      fun t => rexp ((v : ℝ) * t ^ 2 / 2) by ext t; simp]
  let f0 : ℝ → ℝ := fun t => rexp ((v : ℝ) * t ^ 2 / 2)
  let f1 : ℝ → ℝ := fun t => (v : ℝ) * t * f0 t
  let f2 : ℝ → ℝ := fun t => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * f0 t
  let f3 : ℝ → ℝ := fun t =>
    (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * f0 t
  obtain ⟨h1, h2, h3, _h4⟩ := deriv_exp_quadratic_chain (v : ℝ)
  change iteratedDeriv 3 f0 0 = 0
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_zero, h1, h2, h3]
  simp

/-- The fourth moment of a centered real Gaussian is `3 v²`. -/
theorem integral_fourth_gaussianReal_zero (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have hm := iteratedDeriv_mgf_zero
    (X := fun x : ℝ => x) (μ := gaussianReal 0 v) (by simp) 4
  have hm' :
      iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 v)) 0 =
        ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v := by simpa using hm
  rw [← hm', mgf_fun_id_gaussianReal]
  rw [show (fun t : ℝ => rexp (0 * t + v * t ^ 2 / 2)) =
      fun t => rexp ((v : ℝ) * t ^ 2 / 2) by ext t; simp]
  let f0 : ℝ → ℝ := fun t => rexp ((v : ℝ) * t ^ 2 / 2)
  let f1 : ℝ → ℝ := fun t => (v : ℝ) * t * f0 t
  let f2 : ℝ → ℝ := fun t => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * f0 t
  let f3 : ℝ → ℝ := fun t =>
    (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * f0 t
  let f4 : ℝ → ℝ := fun t =>
    (3 * (v : ℝ) ^ 2 + 6 * (v : ℝ) ^ 3 * t ^ 2 +
      (v : ℝ) ^ 4 * t ^ 4) * f0 t
  obtain ⟨h1, h2, h3, h4⟩ := deriv_exp_quadratic_chain (v : ℝ)
  change iteratedDeriv 4 f0 0 = 3 * (v : ℝ) ^ 2
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_succ, iteratedDeriv_zero, h1, h2, h3, h4]
  simp

/-- The variance parameter for the real and imaginary parts of a standard
complex Gaussian. -/
def gaussianHalfVariance : ℝ≥0 := ⟨1 / 2, by norm_num⟩

/-- A centered real Gaussian of variance `1/2`. -/
def realGaussianHalf : Measure ℝ :=
  gaussianReal 0 gaussianHalfVariance

instance : IsProbabilityMeasure realGaussianHalf := by
  unfold realGaussianHalf
  infer_instance

/-- One standard complex Gaussian is represented by two independent centered
real Gaussians of variance `1/2`. -/
def complexGaussianPairMeasure : Measure (ℝ × ℝ) :=
  realGaussianHalf.prod realGaussianHalf

instance : IsProbabilityMeasure complexGaussianPairMeasure := by
  unfold complexGaussianPairMeasure
  infer_instance

/-- Convert the two real coordinates into a complex Gaussian. -/
def complexGaussianOfPair (p : ℝ × ℝ) : ℂ := ⟨p.1, p.2⟩

theorem measurable_complexGaussianOfPair :
    Measurable complexGaussianOfPair := by
  have hfun :
      complexGaussianOfPair = Complex.equivRealProdCLM.symm := by
    funext p
    apply Complex.ext <;> rfl
  rw [hfun]
  exact Complex.equivRealProdCLM.symm.continuous.measurable

theorem continuous_complexGaussianOfPair :
    Continuous complexGaussianOfPair := by
  have hfun :
      complexGaussianOfPair = Complex.equivRealProdCLM.symm := by
    funext p
    apply Complex.ext <;> rfl
  rw [hfun]
  exact Complex.equivRealProdCLM.symm.continuous

@[simp] theorem integral_pow_zero_realGaussianHalf :
    (∫ x : ℝ, x ^ 0 ∂realGaussianHalf) = 1 := by simp

@[simp] theorem integral_pow_one_realGaussianHalf :
    (∫ x : ℝ, x ^ 1 ∂realGaussianHalf) = 0 := by
  simp [realGaussianHalf]

@[simp] theorem integral_pow_two_realGaussianHalf :
    (∫ x : ℝ, x ^ 2 ∂realGaussianHalf) = 1 / 2 := by
  unfold realGaussianHalf
  rw [integral_sq_gaussianReal_zero]
  change (gaussianHalfVariance : ℝ) = 1 / 2
  rfl

@[simp] theorem integral_pow_three_realGaussianHalf :
    (∫ x : ℝ, x ^ 3 ∂realGaussianHalf) = 0 := by
  simpa [realGaussianHalf] using
    integral_cube_gaussianReal_zero gaussianHalfVariance

@[simp] theorem integral_pow_four_realGaussianHalf :
    (∫ x : ℝ, x ^ 4 ∂realGaussianHalf) = 3 / 4 := by
  unfold realGaussianHalf
  rw [integral_fourth_gaussianReal_zero]
  have hhalf : (gaussianHalfVariance : ℝ) = 1 / 2 := rfl
  rw [hhalf]
  norm_num

/-- Every polynomial moment of the centered real Gaussian is integrable. -/
theorem integrable_pow_realGaussianHalf (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) realGaussianHalf := by
  have hnorm :
      Integrable (fun x : ℝ => ‖x‖ ^ n) realGaussianHalf := by
    exact
      (memLp_id_gaussianReal'
        (μ := 0) (v := gaussianHalfVariance)
        (p := (n : ℝ≥0∞)) (by simp)).integrable_norm_pow'
  apply Integrable.mono' hnorm (by fun_prop)
  filter_upwards with x
  simp only [norm_pow]
  exact le_rfl

/-- All absolute moments of the half-variance real Gaussian are integrable. -/
theorem integrable_norm_pow_realGaussianHalf (n : ℕ) :
    Integrable (fun x : ℝ => ‖x‖ ^ n) realGaussianHalf := by
  exact
    (memLp_id_gaussianReal'
      (μ := 0) (v := gaussianHalfVariance)
      (p := (n : ℝ≥0∞)) (by simp)).integrable_norm_pow'

/-- Bivariate real Gaussian monomials are integrable. -/
theorem integrable_pair_monomial (a b : ℕ) :
    Integrable
      (fun p : ℝ × ℝ => p.1 ^ a * p.2 ^ b)
      complexGaussianPairMeasure := by
  exact (integrable_pow_realGaussianHalf a).mul_prod
    (integrable_pow_realGaussianHalf b)

/-- The integral of a bivariate monomial factors into the two real moments. -/
theorem integral_pair_monomial (a b : ℕ) :
    (∫ p : ℝ × ℝ, p.1 ^ a * p.2 ^ b
        ∂complexGaussianPairMeasure) =
      (∫ x : ℝ, x ^ a ∂realGaussianHalf) *
        ∫ y : ℝ, y ^ b ∂realGaussianHalf := by
  unfold complexGaussianPairMeasure
  exact integral_prod_mul (fun x : ℝ => x ^ a) (fun y : ℝ => y ^ b)

/-- Complex-valued form of a bivariate real monomial. -/
def pairMonomialC (a b : ℕ) (p : ℝ × ℝ) : ℂ :=
  (p.1 ^ a * p.2 ^ b : ℝ)

theorem integrable_pairMonomialC (a b : ℕ) :
    Integrable (pairMonomialC a b) complexGaussianPairMeasure := by
  exact (integrable_pair_monomial a b).ofReal

theorem integral_pairMonomialC (a b : ℕ) :
    (∫ p, pairMonomialC a b p ∂complexGaussianPairMeasure) =
      ((∫ x : ℝ, x ^ a ∂realGaussianHalf) *
        ∫ y : ℝ, y ^ b ∂realGaussianHalf : ℝ) := by
  unfold pairMonomialC
  rw [integral_complex_ofReal, integral_pair_monomial]

theorem complexGaussianOfPair_eq (p : ℝ × ℝ) :
    complexGaussianOfPair p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [complexGaussianOfPair]

/-- A single standard complex Gaussian is centered. -/
theorem integral_complexGaussianOfPair :
    (∫ p, complexGaussianOfPair p ∂complexGaussianPairMeasure) = 0 := by
  have hfun :
      complexGaussianOfPair =
        fun p =>
          pairMonomialC 1 0 p +
            pairMonomialC 0 1 p * Complex.I := by
    funext p
    rw [complexGaussianOfPair_eq]
    simp [pairMonomialC]
  rw [hfun, integral_add
    (integrable_pairMonomialC 1 0)
    ((integrable_pairMonomialC 0 1).mul_const Complex.I)]
  rw [integral_mul_const, integral_pairMonomialC, integral_pairMonomialC]
  rw [integral_pow_one_realGaussianHalf]
  simp

theorem integral_star_complexGaussianOfPair :
    (∫ p, star (complexGaussianOfPair p)
        ∂complexGaussianPairMeasure) = 0 := by
  change (∫ p, conj (complexGaussianOfPair p)
        ∂complexGaussianPairMeasure) = 0
  rw [integral_conj, integral_complexGaussianOfPair]
  simp

/-- The covariance of one standard complex Gaussian is one. -/
theorem integral_star_mul_complexGaussianOfPair :
    (∫ p, star (complexGaussianOfPair p) * complexGaussianOfPair p
        ∂complexGaussianPairMeasure) = 1 := by
  have hfun :
      (fun p =>
        star (complexGaussianOfPair p) * complexGaussianOfPair p) =
      fun p => pairMonomialC 2 0 p + pairMonomialC 0 2 p := by
    funext p
    apply Complex.ext <;>
      norm_num [complexGaussianOfPair, pairMonomialC, pow_two, pow_succ] <;>
        ring
  rw [hfun, integral_add
    (integrable_pairMonomialC 2 0)
    (integrable_pairMonomialC 0 2)]
  rw [integral_pairMonomialC, integral_pairMonomialC]
  norm_num

/-- The nonconjugated second moment vanishes. -/
theorem integral_sq_complexGaussianOfPair :
    (∫ p, complexGaussianOfPair p ^ 2
        ∂complexGaussianPairMeasure) = 0 := by
  have hfun :
      (fun p => complexGaussianOfPair p ^ 2) =
      fun p =>
        pairMonomialC 2 0 p - pairMonomialC 0 2 p +
          (2 * Complex.I) * pairMonomialC 1 1 p := by
    funext p
    apply Complex.ext <;>
      norm_num [complexGaussianOfPair, pairMonomialC, pow_two, pow_succ] <;>
        ring
  have h20 := integrable_pairMonomialC 2 0
  have h02 := integrable_pairMonomialC 0 2
  have h11 := integrable_pairMonomialC 1 1
  rw [hfun]
  change
    (∫ p,
      (pairMonomialC 2 0 - pairMonomialC 0 2) p +
        ((fun p => (2 * Complex.I) * pairMonomialC 1 1 p) p)
      ∂complexGaussianPairMeasure) = 0
  rw [integral_add (h20.sub h02) (h11.const_mul (2 * Complex.I))]
  change
    (∫ a, pairMonomialC 2 0 a - pairMonomialC 0 2 a
      ∂complexGaussianPairMeasure) +
      (∫ a, (2 * Complex.I) * pairMonomialC 1 1 a
        ∂complexGaussianPairMeasure) = 0
  rw [integral_sub h20 h02, integral_const_mul]
  rw [integral_pairMonomialC, integral_pairMonomialC,
    integral_pairMonomialC]
  rw [integral_pow_one_realGaussianHalf]
  norm_num

theorem integral_star_sq_complexGaussianOfPair :
    (∫ p, star (complexGaussianOfPair p) ^ 2
        ∂complexGaussianPairMeasure) = 0 := by
  have hpoint :
      (fun p => star (complexGaussianOfPair p) ^ 2) =
        fun p => star (complexGaussianOfPair p ^ 2) := by
    funext p
    simp
  rw [hpoint]
  change
    (∫ p, conj (complexGaussianOfPair p ^ 2)
      ∂complexGaussianPairMeasure) = 0
  rw [integral_conj, integral_sq_complexGaussianOfPair]
  simp

/-- A cubic mixed moment of a standard complex Gaussian vanishes. -/
theorem integral_star_mul_sq_complexGaussianOfPair :
    (∫ p, star (complexGaussianOfPair p) * complexGaussianOfPair p ^ 2
        ∂complexGaussianPairMeasure) = 0 := by
  have hfun :
      (fun p =>
        star (complexGaussianOfPair p) * complexGaussianOfPair p ^ 2) =
      fun p =>
        (pairMonomialC 3 0 p + pairMonomialC 1 2 p) +
          (pairMonomialC 2 1 p + pairMonomialC 0 3 p) * Complex.I := by
    funext p
    apply Complex.ext <;>
      norm_num [complexGaussianOfPair, pairMonomialC, pow_two, pow_succ] <;>
        ring
  have h30 := integrable_pairMonomialC 3 0
  have h12 := integrable_pairMonomialC 1 2
  have h21 := integrable_pairMonomialC 2 1
  have h03 := integrable_pairMonomialC 0 3
  rw [hfun]
  change
    (∫ p,
      (pairMonomialC 3 0 + pairMonomialC 1 2) p +
        ((fun p =>
          (pairMonomialC 2 1 + pairMonomialC 0 3) p * Complex.I) p)
      ∂complexGaussianPairMeasure) = 0
  rw [integral_add (h30.add h12)
    ((h21.add h03).mul_const Complex.I)]
  change
    (∫ p, pairMonomialC 3 0 p + pairMonomialC 1 2 p
      ∂complexGaussianPairMeasure) +
      (∫ p,
        (pairMonomialC 2 1 p + pairMonomialC 0 3 p) * Complex.I
        ∂complexGaussianPairMeasure) = 0
  rw [integral_add h30 h12, integral_mul_const, integral_add h21 h03]
  rw [integral_pairMonomialC, integral_pairMonomialC,
    integral_pairMonomialC, integral_pairMonomialC]
  rw [integral_pow_one_realGaussianHalf]
  simp

/-- The conjugate cubic mixed moment also vanishes. -/
theorem integral_star_sq_mul_complexGaussianOfPair :
    (∫ p, star (complexGaussianOfPair p) ^ 2 * complexGaussianOfPair p
        ∂complexGaussianPairMeasure) = 0 := by
  have hpoint :
      (fun p =>
        star (complexGaussianOfPair p) ^ 2 * complexGaussianOfPair p) =
      fun p =>
        star
          (star (complexGaussianOfPair p) * complexGaussianOfPair p ^ 2) := by
    funext p
    apply Complex.ext <;>
      norm_num [complexGaussianOfPair, pow_two] <;> ring
  rw [hpoint]
  change
    (∫ p,
      conj
        (star (complexGaussianOfPair p) * complexGaussianOfPair p ^ 2)
      ∂complexGaussianPairMeasure) = 0
  rw [integral_conj, integral_star_mul_sq_complexGaussianOfPair]
  simp

/-- The balanced fourth moment of a standard complex Gaussian equals two. -/
theorem integral_star_sq_mul_sq_complexGaussianOfPair :
    (∫ p, star (complexGaussianOfPair p) ^ 2 *
        complexGaussianOfPair p ^ 2
        ∂complexGaussianPairMeasure) = 2 := by
  have hfun :
      (fun p =>
        star (complexGaussianOfPair p) ^ 2 *
          complexGaussianOfPair p ^ 2) =
      fun p =>
        pairMonomialC 4 0 p +
          (2 : ℂ) * pairMonomialC 2 2 p +
            pairMonomialC 0 4 p := by
    funext p
    apply Complex.ext <;>
      norm_num [complexGaussianOfPair, pairMonomialC, pow_two, pow_succ] <;>
        ring
  have h40 := integrable_pairMonomialC 4 0
  have h22 := integrable_pairMonomialC 2 2
  have h04 := integrable_pairMonomialC 0 4
  rw [hfun]
  change
    (∫ p,
      (pairMonomialC 4 0 + fun p => (2 : ℂ) * pairMonomialC 2 2 p) p +
        pairMonomialC 0 4 p
      ∂complexGaussianPairMeasure) = 2
  rw [integral_add
    (h40.add (h22.const_mul (2 : ℂ))) h04]
  change
    (∫ p, pairMonomialC 4 0 p + (2 : ℂ) * pairMonomialC 2 2 p
      ∂complexGaussianPairMeasure) +
      (∫ p, pairMonomialC 0 4 p
        ∂complexGaussianPairMeasure) = 2
  rw [integral_add h40 (h22.const_mul (2 : ℂ)),
    integral_const_mul]
  rw [integral_pairMonomialC, integral_pairMonomialC,
    integral_pairMonomialC]
  norm_num

/-- The product probability space carrying one independent complex Gaussian
at each coordinate. -/
def complexGaussianVectorMeasure (ι : Type*) [Fintype ι] :
    Measure (ι → ℝ × ℝ) :=
  Measure.pi (fun _ : ι => complexGaussianPairMeasure)

instance (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (complexGaussianVectorMeasure ι) := by
  unfold complexGaussianVectorMeasure
  infer_instance

/-- The complex Gaussian at coordinate `i` of the product probability space. -/
def complexGaussianCoordinate {ι : Type*} (i : ι) :
    (ι → ℝ × ℝ) → ℂ :=
  fun ω => complexGaussianOfPair (ω i)

theorem measurable_complexGaussianCoordinate
    {ι : Type*} [Fintype ι] (i : ι) :
    Measurable (complexGaussianCoordinate i) :=
  measurable_complexGaussianOfPair.comp (measurable_pi_apply i)

/-- The coordinate complex Gaussians are mutually independent. -/
theorem iIndepFun_complexGaussianCoordinate
    {ι : Type*} [Fintype ι] :
    iIndepFun (fun i : ι => complexGaussianCoordinate i)
      (complexGaussianVectorMeasure ι) := by
  unfold complexGaussianCoordinate complexGaussianVectorMeasure
  exact iIndepFun_pi
    (X := fun _ : ι => complexGaussianOfPair)
    (μ := fun _ : ι => complexGaussianPairMeasure)
    (fun _ => measurable_complexGaussianOfPair.aemeasurable)

/-- A mixed moment of one coordinate in the product space is the corresponding
one-dimensional complex Gaussian moment. -/
theorem integral_coordinate_mixed_eq_pair
    {ι : Type*} [Fintype ι] (i : ι) (a b : ℕ) :
    (∫ ω,
      star (complexGaussianCoordinate i ω) ^ a *
        complexGaussianCoordinate i ω ^ b
      ∂complexGaussianVectorMeasure ι) =
      ∫ p,
        star (complexGaussianOfPair p) ^ a *
          complexGaussianOfPair p ^ b
      ∂complexGaussianPairMeasure := by
  unfold complexGaussianCoordinate complexGaussianVectorMeasure
  simpa using
    (integral_comp_eval
      (ι := ι)
      (X := fun _ : ι => ℝ × ℝ)
      (μ := fun _ : ι => complexGaussianPairMeasure)
      (i := i)
      (f := fun p =>
        star (complexGaussianOfPair p) ^ a *
          complexGaussianOfPair p ^ b)
      (((continuous_complexGaussianOfPair.star.pow a).mul
        (continuous_complexGaussianOfPair.pow b)).aestronglyMeasurable))

/-- Complete mixed-moment table needed for a fourth-order Wick contraction. -/
theorem integral_mixed_complexGaussianOfPair_of_le_two
    (a b : ℕ) (ha : a ≤ 2) (hb : b ≤ 2) :
    (∫ p,
      star (complexGaussianOfPair p) ^ a *
        complexGaussianOfPair p ^ b
      ∂complexGaussianPairMeasure) =
      if a = b then (Nat.factorial a : ℂ) else 0 := by
  interval_cases a <;> interval_cases b
  all_goals norm_num
  · simpa only [starRingEnd_apply] using
      integral_complexGaussianOfPair
  · simpa only [starRingEnd_apply] using
      integral_sq_complexGaussianOfPair
  · simpa only [starRingEnd_apply] using
      integral_star_complexGaussianOfPair
  · simpa only [starRingEnd_apply] using
      integral_star_mul_complexGaussianOfPair
  · simpa only [starRingEnd_apply] using
      integral_star_mul_sq_complexGaussianOfPair
  · simpa only [starRingEnd_apply] using
      integral_star_sq_complexGaussianOfPair
  · simpa only [starRingEnd_apply] using
      integral_star_sq_mul_complexGaussianOfPair
  · simpa only [starRingEnd_apply] using
      integral_star_sq_mul_sq_complexGaussianOfPair

/-- Every mixed complex moment is integrable.  This is proved by dominating
the complex norm by the sum of the absolute values of the two real Gaussian
coordinates. -/
theorem integrable_mixed_complexGaussianOfPair (a b : ℕ) :
    Integrable
      (fun p =>
        star (complexGaussianOfPair p) ^ a *
          complexGaussianOfPair p ^ b)
      complexGaussianPairMeasure := by
  let n := a + b
  have hx :
      Integrable (fun p : ℝ × ℝ => ‖p.1‖ ^ n)
        complexGaussianPairMeasure := by
    unfold complexGaussianPairMeasure
    simpa using
      (integrable_norm_pow_realGaussianHalf n).mul_prod
        (integrable_const (μ := realGaussianHalf) (1 : ℝ))
  have hy :
      Integrable (fun p : ℝ × ℝ => ‖p.2‖ ^ n)
        complexGaussianPairMeasure := by
    unfold complexGaussianPairMeasure
    simpa using
      (integrable_const (μ := realGaussianHalf) (1 : ℝ)).mul_prod
        (integrable_norm_pow_realGaussianHalf n)
  have hdom :
      Integrable
        (fun p : ℝ × ℝ =>
          (2 : ℝ) ^ (n - 1) * (‖p.1‖ ^ n + ‖p.2‖ ^ n))
        complexGaussianPairMeasure :=
    (hx.add hy).const_mul ((2 : ℝ) ^ (n - 1))
  apply Integrable.mono' hdom
    (((continuous_complexGaussianOfPair.star.pow a).mul
      (continuous_complexGaussianOfPair.pow b)).aestronglyMeasurable)
  filter_upwards with p
  have hz :
      ‖complexGaussianOfPair p‖ ≤ ‖p.1‖ + ‖p.2‖ := by
    rw [complexGaussianOfPair_eq]
    calc
      ‖(p.1 : ℂ) + (p.2 : ℂ) * Complex.I‖ ≤
          ‖(p.1 : ℂ)‖ + ‖(p.2 : ℂ) * Complex.I‖ :=
        norm_add_le _ _
      _ = ‖p.1‖ + ‖p.2‖ := by simp
  calc
    ‖star (complexGaussianOfPair p) ^ a *
        complexGaussianOfPair p ^ b‖ =
        ‖complexGaussianOfPair p‖ ^ n := by
      simp only [norm_mul, norm_pow, norm_star, n]
      rw [← pow_add]
    _ ≤ (‖p.1‖ + ‖p.2‖) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) hz n
    _ ≤ (2 : ℝ) ^ (n - 1) * (‖p.1‖ ^ n + ‖p.2‖ ^ n) :=
      add_pow_le (norm_nonneg _) (norm_nonneg _) n

/-- Number of conjugated occurrences of coordinate `r` in the four-index
Gaussian monomial. -/
def conjugateMultiplicity {ι : Type*} [DecidableEq ι] (i l r : ι) : ℕ :=
  (if r = i then 1 else 0) + if r = l then 1 else 0

/-- Number of unconjugated occurrences of coordinate `r` in the four-index
Gaussian monomial. -/
def directMultiplicity {ι : Type*} [DecidableEq ι] (j k r : ι) : ℕ :=
  (if r = j then 1 else 0) + if r = k then 1 else 0

theorem conjugateMultiplicity_le_two
    {ι : Type*} [DecidableEq ι] (i l r : ι) :
    conjugateMultiplicity i l r ≤ 2 := by
  simp only [conjugateMultiplicity]
  split_ifs <;> omega

theorem directMultiplicity_le_two
    {ι : Type*} [DecidableEq ι] (j k r : ι) :
    directMultiplicity j k r ≤ 2 := by
  simp only [directMultiplicity]
  split_ifs <;> omega

/-- Regroup the four scalar factors by their coordinate. -/
theorem prod_coordinate_monomials_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j k l : ι) (ω : ι → ℝ × ℝ) :
    (∏ r : ι,
      star (complexGaussianCoordinate r ω) ^
          conjugateMultiplicity i l r *
        complexGaussianCoordinate r ω ^
          directMultiplicity j k r) =
      star (complexGaussianCoordinate i ω) *
        complexGaussianCoordinate j ω *
        complexGaussianCoordinate k ω *
        star (complexGaussianCoordinate l ω) := by
  classical
  simp only [conjugateMultiplicity, directMultiplicity, pow_add]
  calc
    (∏ r : ι,
      (star (complexGaussianCoordinate r ω) ^
          (if r = i then 1 else 0) *
        star (complexGaussianCoordinate r ω) ^
          (if r = l then 1 else 0)) *
        (complexGaussianCoordinate r ω ^
            (if r = j then 1 else 0) *
          complexGaussianCoordinate r ω ^
            (if r = k then 1 else 0))) =
        (∏ r : ι,
          star (complexGaussianCoordinate r ω) ^
            (if r = i then 1 else 0)) *
        (∏ r : ι,
          star (complexGaussianCoordinate r ω) ^
            (if r = l then 1 else 0)) *
        (∏ r : ι,
          complexGaussianCoordinate r ω ^
            (if r = j then 1 else 0)) *
        (∏ r : ι,
          complexGaussianCoordinate r ω ^
            (if r = k then 1 else 0)) := by
          repeat rw [Finset.prod_mul_distrib]
          ring
    _ =
        star (complexGaussianCoordinate i ω) *
          star (complexGaussianCoordinate l ω) *
          complexGaussianCoordinate j ω *
          complexGaussianCoordinate k ω := by
      simp
    _ =
        star (complexGaussianCoordinate i ω) *
          complexGaussianCoordinate j ω *
          complexGaussianCoordinate k ω *
          star (complexGaussianCoordinate l ω) := by
      ring

/-- The local moment supplied by a coordinate after the four factors have been
regrouped. -/
def gaussianMultiplicityMoment
    {ι : Type*} [DecidableEq ι] (i j k l r : ι) : ℂ :=
  if conjugateMultiplicity i l r = directMultiplicity j k r then
    Nat.factorial (conjugateMultiplicity i l r)
  else
    0

/-- The product of the local factorials for a two-element multiset is `2`
when its two elements coincide and `1` otherwise. -/
theorem prod_factorial_twoMultiplicity
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) :
    (∏ r : ι,
      (Nat.factorial
        ((if r = a then 1 else 0) + if r = b then 1 else 0) : ℂ)) =
      if a = b then 2 else 1 := by
  by_cases hab : a = b
  · subst b
    calc
      (∏ r : ι,
        (Nat.factorial
          ((if r = a then 1 else 0) + if r = a then 1 else 0) : ℂ)) =
          ∏ r : ι, if r = a then (2 : ℂ) else 1 := by
            apply Finset.prod_congr rfl
            intro r _
            by_cases hra : r = a <;> simp [hra, Nat.factorial]
      _ = 2 := by simp
      _ = if a = a then 2 else 1 := by simp
  · have hfactor :
        ∀ r : ι,
          (Nat.factorial
            ((if r = a then 1 else 0) + if r = b then 1 else 0) : ℂ) =
            1 := by
      intro r
      by_cases hra : r = a <;> by_cases hrb : r = b <;>
        simp_all [Nat.factorial]
    rw [Finset.prod_eq_one (fun r _ => hfactor r)]
    simp [hab]

/-- A mismatch at one coordinate makes the product of all local Gaussian
moments vanish. -/
theorem prod_gaussianMultiplicityMoment_eq_zero_of_mismatch
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j k l r : ι)
    (hneq :
      conjugateMultiplicity i l r ≠ directMultiplicity j k r) :
    (∏ s : ι, gaussianMultiplicityMoment i j k l s) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ r)
  simp [gaussianMultiplicityMoment, hneq]

/-- If the two two-element multisets are not related by either matching,
some coordinate has unequal multiplicity. -/
theorem exists_multiplicity_mismatch_of_no_matching
    {ι : Type*} [DecidableEq ι] (i j k l : ι)
    (h₁ : ¬(i = j ∧ k = l)) (h₂ : ¬(i = k ∧ j = l)) :
    ∃ r : ι,
      conjugateMultiplicity i l r ≠ directMultiplicity j k r := by
  by_contra hno
  have hall :
      ∀ r : ι,
        conjugateMultiplicity i l r = directMultiplicity j k r := by
    intro r
    by_contra hneq
    exact hno ⟨r, hneq⟩
  have hmultiset :
      i ::ₘ l ::ₘ (0 : Multiset ι) =
        j ::ₘ k ::ₘ (0 : Multiset ι) := by
    apply Multiset.ext.2
    intro r
    simpa [Multiset.count_cons, Multiset.count_singleton,
      conjugateMultiplicity,
      directMultiplicity, add_comm] using hall r
  have hmatch :
      (i = j ∧ l = k) ∨ (i = k ∧ l = j) := by
    have hraw :
        (i = j ∧ l = k) ∨ (i ≠ j ∧ l = j ∧ k = i) := by
      simpa [Multiset.cons_eq_cons] using hmultiset
    rcases hraw with hraw | hraw
    · exact Or.inl hraw
    · exact Or.inr ⟨hraw.2.2.symm, hraw.2.1⟩
  rcases hmatch with hmatch | hmatch
  · exact h₁ ⟨hmatch.1, hmatch.2.symm⟩
  · exact h₂ ⟨hmatch.1, hmatch.2.symm⟩

/-- The purely finite combinatorial part of the fourth-order Wick formula. -/
theorem prod_gaussianMultiplicityMoment
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j k l : ι) :
    (∏ r : ι, gaussianMultiplicityMoment i j k l r) =
      (if i = j then 1 else 0) * (if k = l then 1 else 0) +
        (if i = k then 1 else 0) * (if j = l then 1 else 0) := by
  classical
  by_cases h₁ : i = j ∧ k = l
  · rcases h₁ with ⟨hij, hkl⟩
    subst j
    subst l
    rw [show
      (∏ r : ι, gaussianMultiplicityMoment i i k k r) =
        ∏ r : ι,
          (Nat.factorial
            ((if r = i then 1 else 0) + if r = k then 1 else 0) : ℂ) by
      apply Finset.prod_congr rfl
      intro r _
      simp [gaussianMultiplicityMoment, conjugateMultiplicity,
        directMultiplicity]]
    rw [prod_factorial_twoMultiplicity]
    by_cases hik : i = k <;> simp [hik] <;> norm_num
  · by_cases h₂ : i = k ∧ j = l
    · rcases h₂ with ⟨hik, hjl⟩
      subst k
      subst l
      rw [show
        (∏ r : ι, gaussianMultiplicityMoment i j i j r) =
          ∏ r : ι,
            (Nat.factorial
              ((if r = i then 1 else 0) + if r = j then 1 else 0) : ℂ) by
        apply Finset.prod_congr rfl
        intro r _
        simp [gaussianMultiplicityMoment, conjugateMultiplicity,
          directMultiplicity, add_comm]]
      rw [prod_factorial_twoMultiplicity]
      by_cases hij : i = j <;> simp_all [hij] <;> norm_num
    · obtain ⟨r, hr⟩ :=
        exists_multiplicity_mismatch_of_no_matching i j k l h₁ h₂
      rw [prod_gaussianMultiplicityMoment_eq_zero_of_mismatch i j k l r hr]
      by_cases hij : i = j <;> by_cases hkl : k = l <;>
        by_cases hik : i = k <;> by_cases hjl : j = l <;>
        simp_all

/-- Fourth-order Wick contraction for the explicitly constructed independent
standard complex Gaussian vector. -/
theorem integral_four_coordinate_wick
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j k l : ι) :
    (∫ ω,
      star (complexGaussianCoordinate i ω) *
        complexGaussianCoordinate j ω *
        complexGaussianCoordinate k ω *
        star (complexGaussianCoordinate l ω)
      ∂complexGaussianVectorMeasure ι) =
      (if i = j then 1 else 0) * (if k = l then 1 else 0) +
        (if i = k then 1 else 0) * (if j = l then 1 else 0) := by
  let localMoment : ι → ℂ → ℂ := fun r z =>
    star z ^ conjugateMultiplicity i l r *
      z ^ directMultiplicity j k r
  have hX :
      ∀ r : ι,
        AEMeasurable (complexGaussianCoordinate r)
          (complexGaussianVectorMeasure ι) :=
    fun r => (measurable_complexGaussianCoordinate r).aemeasurable
  have hlocal :
      ∀ r : ι,
        AEStronglyMeasurable (localMoment r)
          ((complexGaussianVectorMeasure ι).map
            (complexGaussianCoordinate r)) := by
    intro r
    exact
      (((continuous_id.star.pow (conjugateMultiplicity i l r)).mul
        (continuous_id.pow
          (directMultiplicity j k r))).aestronglyMeasurable)
  calc
    (∫ ω,
      star (complexGaussianCoordinate i ω) *
        complexGaussianCoordinate j ω *
        complexGaussianCoordinate k ω *
        star (complexGaussianCoordinate l ω)
      ∂complexGaussianVectorMeasure ι) =
        ∫ ω,
          ∏ r : ι,
            localMoment r (complexGaussianCoordinate r ω)
          ∂complexGaussianVectorMeasure ι := by
      apply integral_congr_ae
      filter_upwards with ω
      exact (prod_coordinate_monomials_eq i j k l ω).symm
    _ =
        ∏ r : ι,
          ∫ ω,
            localMoment r (complexGaussianCoordinate r ω)
            ∂complexGaussianVectorMeasure ι :=
      (iIndepFun_complexGaussianCoordinate.integral_fun_prod_comp
        hX hlocal)
    _ = ∏ r : ι, gaussianMultiplicityMoment i j k l r := by
      apply Finset.prod_congr rfl
      intro r _
      unfold localMoment
      rw [integral_coordinate_mixed_eq_pair]
      simpa [gaussianMultiplicityMoment] using
        integral_mixed_complexGaussianOfPair_of_le_two
          (conjugateMultiplicity i l r)
          (directMultiplicity j k r)
          (conjugateMultiplicity_le_two i l r)
          (directMultiplicity_le_two j k r)
    _ =
        (if i = j then 1 else 0) * (if k = l then 1 else 0) +
          (if i = k then 1 else 0) * (if j = l then 1 else 0) :=
      prod_gaussianMultiplicityMoment i j k l

/-- Each coordinate is centered in the product model. -/
theorem integral_complexGaussianCoordinate
    {ι : Type*} [Fintype ι] (i : ι) :
    (∫ ω, complexGaussianCoordinate i ω
      ∂complexGaussianVectorMeasure ι) = 0 := by
  calc
    (∫ ω, complexGaussianCoordinate i ω
      ∂complexGaussianVectorMeasure ι) =
        ∫ ω,
          star (complexGaussianCoordinate i ω) ^ 0 *
            complexGaussianCoordinate i ω ^ 1
          ∂complexGaussianVectorMeasure ι := by simp
    _ =
        ∫ p,
          star (complexGaussianOfPair p) ^ 0 *
            complexGaussianOfPair p ^ 1
          ∂complexGaussianPairMeasure :=
      integral_coordinate_mixed_eq_pair i 0 1
    _ = 0 := by simpa using integral_complexGaussianOfPair

theorem integral_star_complexGaussianCoordinate
    {ι : Type*} [Fintype ι] (i : ι) :
    (∫ ω, star (complexGaussianCoordinate i ω)
      ∂complexGaussianVectorMeasure ι) = 0 := by
  calc
    (∫ ω, star (complexGaussianCoordinate i ω)
      ∂complexGaussianVectorMeasure ι) =
        ∫ ω,
          star (complexGaussianCoordinate i ω) ^ 1 *
            complexGaussianCoordinate i ω ^ 0
          ∂complexGaussianVectorMeasure ι := by simp
    _ =
        ∫ p,
          star (complexGaussianOfPair p) ^ 1 *
            complexGaussianOfPair p ^ 0
          ∂complexGaussianPairMeasure :=
      integral_coordinate_mixed_eq_pair i 1 0
    _ = 0 := by simpa using integral_star_complexGaussianOfPair

/-- Two-index covariance of the independent complex Gaussian coordinates. -/
theorem integral_two_coordinate_covariance
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    (∫ ω,
      star (complexGaussianCoordinate i ω) *
        complexGaussianCoordinate j ω
      ∂complexGaussianVectorMeasure ι) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    calc
      (∫ ω,
        star (complexGaussianCoordinate i ω) *
          complexGaussianCoordinate i ω
        ∂complexGaussianVectorMeasure ι) =
          ∫ p,
            star (complexGaussianOfPair p) ^ 1 *
              complexGaussianOfPair p ^ 1
            ∂complexGaussianPairMeasure := by
        simpa using integral_coordinate_mixed_eq_pair i 1 1
      _ = 1 := by simpa using integral_star_mul_complexGaussianOfPair
  · rw [if_neg hij]
    have hindep :=
      iIndepFun_complexGaussianCoordinate.indepFun hij
    have hfactor := hindep.integral_comp_mul_comp
      (measurable_complexGaussianCoordinate i).aemeasurable
      (measurable_complexGaussianCoordinate j).aemeasurable
      (continuous_id.star.aestronglyMeasurable)
      (continuous_id.aestronglyMeasurable)
    simpa [Function.comp_def, integral_star_complexGaussianCoordinate,
      integral_complexGaussianCoordinate] using hfactor

/-- Regroup a two-coordinate covariance monomial by coordinate. -/
theorem prod_two_coordinate_monomials_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (ω : ι → ℝ × ℝ) :
    (∏ r : ι,
      star (complexGaussianCoordinate r ω) ^
          (if r = i then 1 else 0) *
        complexGaussianCoordinate r ω ^
          (if r = j then 1 else 0)) =
      star (complexGaussianCoordinate i ω) *
        complexGaussianCoordinate j ω := by
  rw [Finset.prod_mul_distrib]
  simp

/-- A two-coordinate covariance monomial is integrable. -/
theorem integrable_two_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    Integrable
      (fun ω =>
        star (complexGaussianCoordinate i ω) *
          complexGaussianCoordinate j ω)
      (complexGaussianVectorMeasure ι) := by
  have hprod :
      Integrable
        (fun ω : ι → ℝ × ℝ =>
          ∏ r : ι,
            star (complexGaussianOfPair (ω r)) ^
                (if r = i then 1 else 0) *
              complexGaussianOfPair (ω r) ^
                (if r = j then 1 else 0))
        (complexGaussianVectorMeasure ι) := by
    unfold complexGaussianVectorMeasure
    exact Integrable.fintype_prod fun r =>
      integrable_mixed_complexGaussianOfPair
        (if r = i then 1 else 0) (if r = j then 1 else 0)
  apply hprod.congr
  filter_upwards with ω
  exact prod_two_coordinate_monomials_eq i j ω

/-- The fourth-coordinate monomial in Wick's formula is integrable. -/
theorem integrable_four_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j k l : ι) :
    Integrable
      (fun ω =>
        star (complexGaussianCoordinate i ω) *
          complexGaussianCoordinate j ω *
          complexGaussianCoordinate k ω *
          star (complexGaussianCoordinate l ω))
      (complexGaussianVectorMeasure ι) := by
  have hprod :
      Integrable
        (fun ω : ι → ℝ × ℝ =>
          ∏ r : ι,
            star (complexGaussianOfPair (ω r)) ^
                conjugateMultiplicity i l r *
              complexGaussianOfPair (ω r) ^
                directMultiplicity j k r)
        (complexGaussianVectorMeasure ι) := by
    unfold complexGaussianVectorMeasure
    exact Integrable.fintype_prod fun r =>
      integrable_mixed_complexGaussianOfPair
        (conjugateMultiplicity i l r)
        (directMultiplicity j k r)
  apply hprod.congr
  filter_upwards with ω
  exact prod_coordinate_monomials_eq i j k l ω

/-- Complex-valued Kronecker delta. -/
def kroneckerC {ι : Type*} [DecidableEq ι] (i j : ι) : ℂ :=
  if i = j then 1 else 0

theorem kroneckerC_comm
    {ι : Type*} [DecidableEq ι] (i j : ι) :
    kroneckerC i j = kroneckerC j i := by
  by_cases hij : i = j <;> simp [kroneckerC, hij, eq_comm]

/-- Centered Gaussian matrix entry `conj(Gᵢ) Gⱼ - δᵢⱼ`. -/
def gaussianCenteredEntry
    {ι : Type*} [DecidableEq ι] (i j : ι) :
    (ι → ℝ × ℝ) → ℂ :=
  fun ω =>
    star (complexGaussianCoordinate i ω) *
        complexGaussianCoordinate j ω -
      kroneckerC i j

/-- The centered Gaussian matrix entries have identity covariance. -/
theorem integral_centeredEntry_covariance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j k l : ι) :
    (∫ ω,
      star (gaussianCenteredEntry i j ω) *
        gaussianCenteredEntry k l ω
      ∂complexGaussianVectorMeasure ι) =
      kroneckerC i k * kroneckerC j l := by
  let four : (ι → ℝ × ℝ) → ℂ := fun ω =>
    star (complexGaussianCoordinate k ω) *
      complexGaussianCoordinate l ω *
      complexGaussianCoordinate i ω *
      star (complexGaussianCoordinate j ω)
  let twoJI : (ι → ℝ × ℝ) → ℂ := fun ω =>
    star (complexGaussianCoordinate j ω) *
      complexGaussianCoordinate i ω
  let twoKL : (ι → ℝ × ℝ) → ℂ := fun ω =>
    star (complexGaussianCoordinate k ω) *
      complexGaussianCoordinate l ω
  have hfun :
      (fun ω =>
        star (gaussianCenteredEntry i j ω) *
          gaussianCenteredEntry k l ω) =
        fun ω =>
          four ω - kroneckerC k l * twoJI ω -
              kroneckerC i j * twoKL ω +
            kroneckerC i j * kroneckerC k l := by
    funext ω
    unfold gaussianCenteredEntry kroneckerC four twoJI twoKL
    split_ifs <;> simp <;> ring
  have hfour : Integrable four (complexGaussianVectorMeasure ι) := by
    unfold four
    exact integrable_four_coordinate k l i j
  have hji : Integrable twoJI (complexGaussianVectorMeasure ι) := by
    unfold twoJI
    exact integrable_two_coordinate j i
  have hkl : Integrable twoKL (complexGaussianVectorMeasure ι) := by
    unfold twoKL
    exact integrable_two_coordinate k l
  have hc :
      Integrable
        (fun _ : ι → ℝ × ℝ =>
          kroneckerC i j * kroneckerC k l)
        (complexGaussianVectorMeasure ι) :=
    integrable_const _
  rw [hfun]
  change
    (∫ ω,
      (((four - fun ω => kroneckerC k l * twoJI ω) -
          fun ω => kroneckerC i j * twoKL ω) ω) +
        (fun _ : ι → ℝ × ℝ =>
          kroneckerC i j * kroneckerC k l) ω
      ∂complexGaussianVectorMeasure ι) =
      kroneckerC i k * kroneckerC j l
  rw [integral_add
    ((hfour.sub (hji.const_mul (kroneckerC k l))).sub
      (hkl.const_mul (kroneckerC i j))) hc]
  change
    (∫ ω,
      (four - fun ω => kroneckerC k l * twoJI ω) ω -
        kroneckerC i j * twoKL ω
      ∂complexGaussianVectorMeasure ι) +
      (∫ _ : ι → ℝ × ℝ,
        kroneckerC i j * kroneckerC k l
        ∂complexGaussianVectorMeasure ι) =
      kroneckerC i k * kroneckerC j l
  rw [integral_sub
    (hfour.sub (hji.const_mul (kroneckerC k l)))
    (hkl.const_mul (kroneckerC i j))]
  change
    ((∫ ω, four ω - kroneckerC k l * twoJI ω
        ∂complexGaussianVectorMeasure ι) -
      ∫ ω, kroneckerC i j * twoKL ω
        ∂complexGaussianVectorMeasure ι) +
      (∫ _ : ι → ℝ × ℝ,
        kroneckerC i j * kroneckerC k l
        ∂complexGaussianVectorMeasure ι) =
      kroneckerC i k * kroneckerC j l
  rw [integral_sub hfour (hji.const_mul (kroneckerC k l))]
  rw [integral_const_mul, integral_const_mul]
  unfold four twoJI twoKL
  rw [integral_four_coordinate_wick,
    integral_two_coordinate_covariance,
    integral_two_coordinate_covariance]
  simp only [integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]
  change
    (kroneckerC k l * kroneckerC i j +
          kroneckerC k i * kroneckerC l j -
        kroneckerC k l * kroneckerC j i -
      kroneckerC i j * kroneckerC k l) +
        kroneckerC i j * kroneckerC k l =
      kroneckerC i k * kroneckerC j l
  rw [kroneckerC_comm k i, kroneckerC_comm l j,
    kroneckerC_comm j i]
  ring

/-- Products of two centered Gaussian matrix entries are integrable. -/
theorem integrable_centeredEntry_covariance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j k l : ι) :
    Integrable
      (fun ω =>
        star (gaussianCenteredEntry i j ω) *
          gaussianCenteredEntry k l ω)
      (complexGaussianVectorMeasure ι) := by
  let four : (ι → ℝ × ℝ) → ℂ := fun ω =>
    star (complexGaussianCoordinate k ω) *
      complexGaussianCoordinate l ω *
      complexGaussianCoordinate i ω *
      star (complexGaussianCoordinate j ω)
  let twoJI : (ι → ℝ × ℝ) → ℂ := fun ω =>
    star (complexGaussianCoordinate j ω) *
      complexGaussianCoordinate i ω
  let twoKL : (ι → ℝ × ℝ) → ℂ := fun ω =>
    star (complexGaussianCoordinate k ω) *
      complexGaussianCoordinate l ω
  have hfour : Integrable four (complexGaussianVectorMeasure ι) := by
    unfold four
    exact integrable_four_coordinate k l i j
  have hji : Integrable twoJI (complexGaussianVectorMeasure ι) := by
    unfold twoJI
    exact integrable_two_coordinate j i
  have hkl : Integrable twoKL (complexGaussianVectorMeasure ι) := by
    unfold twoKL
    exact integrable_two_coordinate k l
  have hsum :
      Integrable
        (fun ω =>
          four ω - kroneckerC k l * twoJI ω -
              kroneckerC i j * twoKL ω +
            kroneckerC i j * kroneckerC k l)
        (complexGaussianVectorMeasure ι) :=
    ((hfour.sub (hji.const_mul (kroneckerC k l))).sub
      (hkl.const_mul (kroneckerC i j))).add (integrable_const _)
  apply hsum.congr
  filter_upwards with ω
  unfold gaussianCenteredEntry kroneckerC four twoJI twoKL
  split_ifs <;> simp <;> ring

/-- Centered quadratic form associated with a complex matrix. -/
def gaussianCenteredQuadraticForm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CMatrix ι) : (ι → ℝ × ℝ) → ℂ :=
  fun ω =>
    ∑ i : ι, ∑ j : ι,
      A i j * gaussianCenteredEntry i j ω

/-- Exact quadratic Wick identity: the centered Gaussian quadratic form has
second moment equal to the squared Frobenius norm. -/
theorem integral_gaussianCenteredQuadraticForm_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CMatrix ι) :
    (∫ ω,
      star (gaussianCenteredQuadraticForm A ω) *
        gaussianCenteredQuadraticForm A ω
      ∂complexGaussianVectorMeasure ι) =
      (frobeniusSq A : ℂ) := by
  let term : ι → ι → ι → ι → (ι → ℝ × ℝ) → ℂ :=
    fun i j k l ω =>
      star (A i j) * A k l *
        (star (gaussianCenteredEntry i j ω) *
          gaussianCenteredEntry k l ω)
  have hterm :
      ∀ i j k l,
        Integrable (term i j k l)
          (complexGaussianVectorMeasure ι) := by
    intro i j k l
    exact
      (integrable_centeredEntry_covariance i j k l).const_mul
        (star (A i j) * A k l)
  have hfun :
      (fun ω =>
        star (gaussianCenteredQuadraticForm A ω) *
          gaussianCenteredQuadraticForm A ω) =
        fun ω => ∑ i : ι, ∑ j : ι, ∑ k : ι, ∑ l : ι,
          term i j k l ω := by
    funext ω
    unfold gaussianCenteredQuadraticForm term
    rw [show
      star (∑ i : ι, ∑ j : ι,
        A i j * gaussianCenteredEntry i j ω) =
        ∑ i : ι, ∑ j : ι,
          star (A i j * gaussianCenteredEntry i j ω) by
      change
        (starRingEnd ℂ)
          (∑ i : ι, ∑ j : ι,
            A i j * gaussianCenteredEntry i j ω) = _
      simp]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [star_mul]
    ring
  have hdistribute :
      (∫ ω, ∑ i : ι, ∑ j : ι, ∑ k : ι, ∑ l : ι,
        term i j k l ω
        ∂complexGaussianVectorMeasure ι) =
        ∑ i : ι, ∑ j : ι, ∑ k : ι, ∑ l : ι,
          ∫ ω, term i j k l ω
            ∂complexGaussianVectorMeasure ι := by
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro j _
        rw [integral_finsetSum Finset.univ]
        · apply Finset.sum_congr rfl
          intro k _
          rw [integral_finsetSum Finset.univ]
          intro l _
          exact hterm i j k l
        · intro k _
          exact integrable_finsetSum Finset.univ fun l _ =>
            hterm i j k l
      · intro j _
        exact integrable_finsetSum Finset.univ fun k _ =>
          integrable_finsetSum Finset.univ fun l _ =>
            hterm i j k l
    · intro i _
      exact integrable_finsetSum Finset.univ fun j _ =>
        integrable_finsetSum Finset.univ fun k _ =>
          integrable_finsetSum Finset.univ fun l _ =>
            hterm i j k l
  rw [hfun, hdistribute]
  unfold term
  simp_rw [integral_const_mul, integral_centeredEntry_covariance]
  calc
    (∑ i : ι, ∑ j : ι, ∑ k : ι, ∑ l : ι,
      star (A i j) * A k l *
        (kroneckerC i k * kroneckerC j l)) =
        hsInner A A := by
      simp [kroneckerC, hsInner]
    _ = (frobeniusSq A : ℂ) := hsInner_self A

/-- The usual Gaussian quadratic form `Gᴴ A G`. -/
def gaussianQuadraticForm
    {ι : Type*} [Fintype ι]
    (A : CMatrix ι) : (ι → ℝ × ℝ) → ℂ :=
  fun ω =>
    ∑ i : ι, ∑ j : ι,
      star (complexGaussianCoordinate i ω) *
        A i j * complexGaussianCoordinate j ω

theorem sum_mul_kroneckerC_eq_trace
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CMatrix ι) :
    (∑ i : ι, ∑ j : ι, A i j * kroneckerC i j) = A.trace := by
  simp [kroneckerC, Matrix.trace]

/-- The centered-entry presentation of the quadratic form is exactly the
usual quadratic form minus its trace. -/
theorem gaussianCenteredQuadraticForm_eq_sub_trace
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CMatrix ι) (ω : ι → ℝ × ℝ) :
    gaussianCenteredQuadraticForm A ω =
      gaussianQuadraticForm A ω - A.trace := by
  unfold gaussianCenteredQuadraticForm gaussianQuadraticForm
  calc
    (∑ i : ι, ∑ j : ι,
      A i j * gaussianCenteredEntry i j ω) =
        ∑ i : ι, ∑ j : ι, (
          (A i j *
              (star (complexGaussianCoordinate i ω) *
                complexGaussianCoordinate j ω)) -
            A i j * kroneckerC i j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      unfold gaussianCenteredEntry
      ring
    _ =
        (∑ i : ι, ∑ j : ι,
          A i j *
            (star (complexGaussianCoordinate i ω) *
              complexGaussianCoordinate j ω)) -
          ∑ i : ι, ∑ j : ι, A i j * kroneckerC i j := by
      simp_rw [Finset.sum_sub_distrib]
    _ =
        (∑ i : ι, ∑ j : ι,
          star (complexGaussianCoordinate i ω) *
            A i j * complexGaussianCoordinate j ω) -
          A.trace := by
      rw [sum_mul_kroneckerC_eq_trace]
      apply congrArg (· - A.trace)
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Complex form of the exact Gaussian quadratic variance identity. -/
theorem integral_gaussianQuadraticForm_sub_trace_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CMatrix ι) :
    (∫ ω,
      star (gaussianQuadraticForm A ω - A.trace) *
        (gaussianQuadraticForm A ω - A.trace)
      ∂complexGaussianVectorMeasure ι) =
      (frobeniusSq A : ℂ) := by
  simpa only [gaussianCenteredQuadraticForm_eq_sub_trace] using
    integral_gaussianCenteredQuadraticForm_sq A

/-- Real form of the exact Gaussian quadratic variance identity. -/
theorem integral_normSq_gaussianQuadraticForm_sub_trace
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : CMatrix ι) :
    (∫ ω,
      Complex.normSq (gaussianQuadraticForm A ω - A.trace)
      ∂complexGaussianVectorMeasure ι) =
      frobeniusSq A := by
  have hcomplex :
      ((∫ ω,
        Complex.normSq (gaussianQuadraticForm A ω - A.trace)
        ∂complexGaussianVectorMeasure ι : ℝ) : ℂ) =
        (frobeniusSq A : ℂ) := by
    rw [← integral_complex_ofReal]
    simpa only [Complex.normSq_eq_conj_mul_self, starRingEnd_apply] using
      integral_gaussianQuadraticForm_sub_trace_sq A
  exact_mod_cast hcomplex

end

end QuantumSep
