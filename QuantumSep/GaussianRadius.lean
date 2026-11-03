import QuantumSep.GaussianWick
import QuantumSep.GaussianMoments
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Moments.ComplexMGF

/-!
# The radial law of the explicit complex Gaussian model

This file starts the analytic bridge from the coordinate model constructed in
`GaussianWick` to the Gamma radial law.  We first compute the Laplace transform
of one real half-variance Gaussian directly from its density, and then combine
the two independent real coordinates of one complex Gaussian.
-/

open MeasureTheory Real Filter
open ProbabilityTheory
open scoped NNReal

namespace QuantumSep

/-- The Laplace transform of the square of a centered real Gaussian of
variance `1/2`.  The proof unfolds the Gaussian density and uses the
formalized Gaussian integral; no distributional identity is assumed. -/
theorem integral_exp_neg_mul_sq_realGaussianHalf (t : ℝ) (ht : -1 < t) :
    (∫ x : ℝ, Real.exp (-t * x ^ 2) ∂realGaussianHalf) =
      1 / Real.sqrt (1 + t) := by
  unfold realGaussianHalf
  rw [integral_gaussianReal_eq_integral_smul
    (show gaussianHalfVariance ≠ 0 by
      intro h
      have h' := congrArg (fun v : ℝ≥0 => (v : ℝ)) h
      change (1 / 2 : ℝ) = 0 at h'
      norm_num at h')]
  simp only [smul_eq_mul]
  have hpdf : ∀ x : ℝ,
      gaussianPDFReal 0 gaussianHalfVariance x =
        (Real.sqrt Real.pi)⁻¹ * Real.exp (-x ^ 2) := by
    intro x
    rw [gaussianPDFReal]
    simp only [sub_zero]
    congr 1
    · congr 2
      change 2 * Real.pi * (1 / 2 : ℝ) = Real.pi
      ring
    · congr 1
      change -x ^ 2 / (2 * (1 / 2 : ℝ)) = -x ^ 2
      ring
  have hpi : 0 < Real.pi := Real.pi_pos
  have hone : 0 < 1 + t := by linarith
  simp_rw [hpdf]
  calc
    (∫ x : ℝ,
        (((Real.sqrt Real.pi)⁻¹ *
            Real.exp (-x ^ 2)) *
          Real.exp (-t * x ^ 2))) =
        (Real.sqrt Real.pi)⁻¹ *
          ∫ x : ℝ, Real.exp (-(1 + t) * x ^ 2) := by
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring
    _ = (Real.sqrt Real.pi)⁻¹ *
          Real.sqrt (Real.pi / (1 + t)) := by
      rw [integral_gaussian]
    _ = 1 / Real.sqrt (1 + t) := by
      rw [Real.sqrt_div (le_of_lt hpi)]
      field_simp [Real.sqrt_ne_zero'.mpr hpi, Real.sqrt_ne_zero'.mpr hone]

/-- The squared Euclidean norm of the real pair underlying one standard
complex Gaussian. -/
def complexGaussianPairRadiusSq (p : ℝ × ℝ) : ℝ :=
  p.1 ^ 2 + p.2 ^ 2

/-- Exact Laplace transform of the squared norm of one standard complex
Gaussian. -/
theorem integral_exp_neg_mul_complexGaussianPairRadiusSq
    (t : ℝ) (ht : -1 < t) :
    (∫ p : ℝ × ℝ,
        Real.exp (-t * complexGaussianPairRadiusSq p)
        ∂complexGaussianPairMeasure) =
      1 / (1 + t) := by
  unfold complexGaussianPairMeasure
  calc
    (∫ p : ℝ × ℝ,
        Real.exp (-t * complexGaussianPairRadiusSq p)
        ∂realGaussianHalf.prod realGaussianHalf) =
        ∫ p : ℝ × ℝ,
          Real.exp (-t * p.1 ^ 2) * Real.exp (-t * p.2 ^ 2)
          ∂realGaussianHalf.prod realGaussianHalf := by
      apply integral_congr_ae
      filter_upwards with p
      rw [← Real.exp_add]
      congr 1
      simp only [complexGaussianPairRadiusSq]
      ring
    _ =
        (∫ x : ℝ, Real.exp (-t * x ^ 2) ∂realGaussianHalf) *
          ∫ y : ℝ, Real.exp (-t * y ^ 2) ∂realGaussianHalf := by
      simpa only using
        (MeasureTheory.integral_prod_mul
          (μ := realGaussianHalf) (ν := realGaussianHalf)
          (fun x : ℝ => Real.exp (-t * x ^ 2))
          (fun y : ℝ => Real.exp (-t * y ^ 2)))
    _ = (1 / Real.sqrt (1 + t)) *
          (1 / Real.sqrt (1 + t)) := by
      rw [integral_exp_neg_mul_sq_realGaussianHalf t ht]
    _ = 1 / (1 + t) := by
      have hone : 0 ≤ 1 + t := by linarith
      rw [one_div_mul_one_div, ← sq, Real.sq_sqrt hone]

/-- Squared Euclidean radius of the explicitly constructed finite complex
Gaussian vector. -/
def complexGaussianVectorRadiusSq
    {ι : Type*} [Fintype ι] (ω : ι → ℝ × ℝ) : ℝ :=
  ∑ i : ι, complexGaussianPairRadiusSq (ω i)

theorem complexGaussianVectorRadiusSq_eq_sum_normSq
    {ι : Type*} [Fintype ι] (ω : ι → ℝ × ℝ) :
    complexGaussianVectorRadiusSq ω =
      ∑ i : ι, Complex.normSq (complexGaussianCoordinate i ω) := by
  apply Finset.sum_congr rfl
  intro i _
  simp [complexGaussianPairRadiusSq, complexGaussianCoordinate,
    complexGaussianOfPair, Complex.normSq_apply, pow_two]

/-- The exponential of the negative radius splits coordinatewise. -/
theorem exp_neg_mul_complexGaussianVectorRadiusSq_eq_prod
    {ι : Type*} [Fintype ι] (t : ℝ) (ω : ι → ℝ × ℝ) :
    Real.exp (-t * complexGaussianVectorRadiusSq ω) =
      ∏ i : ι,
        Real.exp (-t * complexGaussianPairRadiusSq (ω i)) := by
  rw [complexGaussianVectorRadiusSq]
  have h :
      -t * (∑ i : ι, complexGaussianPairRadiusSq (ω i)) =
        ∑ i : ι, -t * complexGaussianPairRadiusSq (ω i) := by
    rw [Finset.mul_sum]
  rw [h, Real.exp_sum]

/-- Exact finite-dimensional Laplace transform of the squared radius.  This
is the characteristic transform of a unit-rate Gamma law of integer shape,
proved here directly from the product Gaussian density. -/
theorem integral_exp_neg_mul_complexGaussianVectorRadiusSq
    {ι : Type*} [Fintype ι] (t : ℝ) (ht : -1 < t) :
    (∫ ω : ι → ℝ × ℝ,
        Real.exp (-t * complexGaussianVectorRadiusSq ω)
        ∂complexGaussianVectorMeasure ι) =
      (1 / (1 + t)) ^ Fintype.card ι := by
  classical
  unfold complexGaussianVectorMeasure
  calc
    (∫ ω : ι → ℝ × ℝ,
        Real.exp (-t * complexGaussianVectorRadiusSq ω)
        ∂Measure.pi (fun _ : ι => complexGaussianPairMeasure)) =
        ∫ ω : ι → ℝ × ℝ,
          ∏ i : ι,
            Real.exp (-t * complexGaussianPairRadiusSq (ω i))
          ∂Measure.pi (fun _ : ι => complexGaussianPairMeasure) := by
      apply integral_congr_ae
      filter_upwards with ω
      exact exp_neg_mul_complexGaussianVectorRadiusSq_eq_prod t ω
    _ =
        ∏ i : ι,
          ∫ p : ℝ × ℝ,
            Real.exp (-t * complexGaussianPairRadiusSq p)
            ∂complexGaussianPairMeasure := by
      simpa only using
        (MeasureTheory.integral_fintype_prod_eq_prod
          (μ := fun _ : ι => complexGaussianPairMeasure)
          (fun _ : ι => fun p : ℝ × ℝ =>
            Real.exp (-t * complexGaussianPairRadiusSq p)))
    _ = ∏ _i : ι, (1 / (1 + t)) := by
      apply Finset.prod_congr rfl
      intro i _
      exact integral_exp_neg_mul_complexGaussianPairRadiusSq t ht
    _ = (1 / (1 + t)) ^ Fintype.card ι := by simp

/-- The real moment-generating integral of an integer-shape unit-rate Gamma
law, throughout its finite range. -/
theorem integral_exp_mul_gammaMeasure_nat
    (d : ℕ) (hd : 0 < d) (u : ℝ) (hu : u < 1) :
    (∫ x : ℝ, Real.exp (u * x) ∂gammaMeasure d 1) =
      (1 / (1 - u)) ^ d := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul]
  · simp only [smul_eq_mul, gammaPDF]
    simp_rw [ENNReal.toReal_ofReal
      (gammaPDFReal_nonneg hdR one_pos _)]
    let g : ℝ → ℝ := fun x =>
      (1 / Real.Gamma d) *
        (x ^ ((d : ℝ) - 1) * Real.exp (-((1 - u) * x)))
    calc
      (∫ x : ℝ, gammaPDFReal d 1 x * Real.exp (u * x)) =
          ∫ x : ℝ, (Set.Ici 0).indicator g x := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : 0 ≤ x
        · rw [Set.indicator_of_mem (by simpa using hx)]
          unfold gammaPDFReal g
          rw [if_pos hx]
          rw [show (1 : ℝ) ^ (d : ℝ) = 1 by simp, one_div,
            one_mul]
          calc
            (Real.Gamma d)⁻¹ * x ^ ((d : ℝ) - 1) *
                  Real.exp (-x) * Real.exp (u * x) =
                (Real.Gamma d)⁻¹ * x ^ ((d : ℝ) - 1) *
                  (Real.exp (-x) * Real.exp (u * x)) := by ring
            _ = (Real.Gamma d)⁻¹ * x ^ ((d : ℝ) - 1) *
                  Real.exp (-((1 - u) * x)) := by
              rw [← Real.exp_add]
              congr 2
              ring
            _ = (Real.Gamma d)⁻¹ *
                  (x ^ ((d : ℝ) - 1) *
                    Real.exp (-((1 - u) * x))) := by ring
        · rw [Set.indicator_of_notMem (by simpa using hx)]
          unfold gammaPDFReal
          rw [if_neg hx]
          simp
      _ = ∫ x : ℝ in Set.Ici 0, g x :=
        integral_indicator measurableSet_Ici
      _ = ∫ x : ℝ in Set.Ioi 0, g x := by
        rw [integral_Ici_eq_integral_Ioi]
      _ = (1 / Real.Gamma d) *
          ∫ x : ℝ in Set.Ioi 0,
            x ^ ((d : ℝ) - 1) *
              Real.exp (-((1 - u) * x)) := by
        rw [MeasureTheory.integral_const_mul]
      _ = (1 / Real.Gamma d) *
          ((1 / (1 - u)) ^ (d : ℝ) * Real.Gamma d) := by
        rw [Real.integral_rpow_mul_exp_neg_mul_Ioi
          hdR (sub_pos.mpr hu)]
      _ = (1 / (1 - u)) ^ d := by
        have hGamma : Real.Gamma (d : ℝ) ≠ 0 :=
          (Real.Gamma_pos_of_pos hdR).ne'
        rw [Real.rpow_natCast]
        field_simp [hGamma]
  · exact (measurable_gammaPDFReal d 1).ennreal_ofReal
  · filter_upwards with x
    simp [gammaPDF]

/-- Exponential integrability of the Gaussian radius throughout the maximal
open half-line needed for its MGF.  Positivity of the already-computed
integral rules out the `integral_undef` branch. -/
theorem integrable_exp_mul_complexGaussianVectorRadiusSq
    {ι : Type*} [Fintype ι] (u : ℝ) (hu : u < 1) :
    Integrable
      (fun ω : ι → ℝ × ℝ =>
        Real.exp (u * complexGaussianVectorRadiusSq ω))
      (complexGaussianVectorMeasure ι) := by
  have hEq :
      (∫ ω : ι → ℝ × ℝ,
          Real.exp (u * complexGaussianVectorRadiusSq ω)
          ∂complexGaussianVectorMeasure ι) =
        (1 / (1 - u)) ^ Fintype.card ι := by
    convert
      integral_exp_neg_mul_complexGaussianVectorRadiusSq
        (ι := ι) (-u) (by linarith)
      using 1
    · congr 1
      ring
    · ring
  by_contra hnot
  rw [integral_undef hnot] at hEq
  have hpos : 0 < (1 / (1 - u)) ^ Fintype.card ι := by positivity
  exact hpos.ne' hEq.symm

/-- Exponential integrability of the positive integer-shape Gamma law on the
same half-line. -/
theorem integrable_exp_mul_gammaMeasure_nat
    (d : ℕ) (hd : 0 < d) (u : ℝ) (hu : u < 1) :
    Integrable (fun x : ℝ => Real.exp (u * x)) (gammaMeasure d 1) := by
  have hEq := integral_exp_mul_gammaMeasure_nat d hd u hu
  by_contra hnot
  rw [integral_undef hnot] at hEq
  have hpos : 0 < (1 / (1 - u)) ^ d := by positivity
  exact hpos.ne' hEq.symm

/-- Real MGF formula for the explicit finite complex Gaussian radius. -/
theorem mgf_complexGaussianVectorRadiusSq
    {ι : Type*} [Fintype ι] (u : ℝ) (hu : u < 1) :
    mgf complexGaussianVectorRadiusSq
        (complexGaussianVectorMeasure ι) u =
      (1 / (1 - u)) ^ Fintype.card ι := by
  unfold mgf
  convert
    integral_exp_neg_mul_complexGaussianVectorRadiusSq
      (ι := ι) (-u) (by linarith)
    using 1 <;> ring

/-- Real MGF formula for the matching Gamma law. -/
theorem mgf_gammaMeasure_nat
    (d : ℕ) (hd : 0 < d) (u : ℝ) (hu : u < 1) :
    mgf id (gammaMeasure d 1) u =
      (1 / (1 - u)) ^ d := by
  simpa [mgf] using integral_exp_mul_gammaMeasure_nat d hd u hu

/-- The open half-line `(-∞,1)` lies in the interior of the Gaussian
radius's exponential-integrability set. -/
theorem Iio_one_subset_interior_integrableExpSet_gaussianRadius
    {ι : Type*} [Fintype ι] :
    Set.Iio (1 : ℝ) ⊆
      interior
        (integrableExpSet complexGaussianVectorRadiusSq
          (complexGaussianVectorMeasure ι)) := by
  apply interior_maximal ?_ isOpen_Iio
  intro u hu
  exact integrable_exp_mul_complexGaussianVectorRadiusSq u hu

/-- The same open half-line lies in the interior of the matching Gamma
law's exponential-integrability set. -/
theorem Iio_one_subset_interior_integrableExpSet_gamma
    (d : ℕ) (hd : 0 < d) :
    Set.Iio (1 : ℝ) ⊆
      interior (integrableExpSet id (gammaMeasure d 1)) := by
  apply interior_maximal ?_ isOpen_Iio
  intro u hu
  exact integrable_exp_mul_gammaMeasure_nat d hd u hu

/-- The squared-radius function is continuous, hence measurable. -/
theorem continuous_complexGaussianVectorRadiusSq
    {ι : Type*} [Fintype ι] :
    Continuous (complexGaussianVectorRadiusSq :
      (ι → ℝ × ℝ) → ℝ) := by
  unfold complexGaussianVectorRadiusSq complexGaussianPairRadiusSq
  fun_prop

theorem measurable_complexGaussianVectorRadiusSq
    {ι : Type*} [Fintype ι] :
    Measurable (complexGaussianVectorRadiusSq :
      (ι → ℝ × ℝ) → ℝ) :=
  continuous_complexGaussianVectorRadiusSq.measurable

/-- The complex MGFs of the explicit Gaussian radius and the matching Gamma
law agree on the connected half-plane containing the imaginary axis.

The equality on the real interval comes from the two direct integral
computations above; the extension is the analytic identity theorem. -/
theorem eqOn_complexMGF_gaussianRadius_gamma
    (d : ℕ) (hd : 0 < d) :
    Set.EqOn
      (complexMGF
        (complexGaussianVectorRadiusSq :
          (Fin d → ℝ × ℝ) → ℝ)
        (complexGaussianVectorMeasure (Fin d)))
      (complexMGF id (gammaMeasure d 1))
      {z : ℂ | z.re ∈ Set.Iio (1 : ℝ)} := by
  letI : IsProbabilityMeasure (gammaMeasure d 1) :=
    isProbabilityMeasure_gammaMeasure (by exact_mod_cast hd) one_pos
  let U : Set ℂ := {z : ℂ | z.re ∈ Set.Iio (1 : ℝ)}
  have hGaussian :
      AnalyticOnNhd ℂ
        (complexMGF
          (complexGaussianVectorRadiusSq :
            (Fin d → ℝ × ℝ) → ℝ)
          (complexGaussianVectorMeasure (Fin d))) U := by
    apply analyticOnNhd_complexMGF.mono
    intro z hz
    exact Iio_one_subset_interior_integrableExpSet_gaussianRadius hz
  have hGamma :
      AnalyticOnNhd ℂ (complexMGF id (gammaMeasure d 1)) U := by
    apply analyticOnNhd_complexMGF.mono
    intro z hz
    exact Iio_one_subset_interior_integrableExpSet_gamma d hd hz
  have hU : IsPreconnected U := by
    simpa [U] using (convex_halfSpace_re_lt (1 : ℝ)).isPreconnected
  have hzero : (0 : ℂ) ∈ U := by simp [U]
  apply hGaussian.eqOn_of_preconnected_of_frequently_eq
    hGamma hU hzero
  rw [frequently_iff_seq_forall]
  refine ⟨
    fun n : ℕ => ((-(1 / ((n : ℝ) + 1)) : ℝ) : ℂ),
    ?_, ?_⟩
  · rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa using
        (tendsto_one_div_add_atTop_nhds_zero_nat
          (𝕜 := ℝ)).neg.ofReal
    · filter_upwards with n
      have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hsum : 0 < (n : ℝ) + 1 :=
        add_pos_of_nonneg_of_pos hnR one_pos
      change ((-(1 / ((n : ℝ) + 1)) : ℝ) : ℂ) ≠ 0
      rw [Complex.ofReal_ne_zero]
      exact neg_ne_zero.mpr (one_div_ne_zero hsum.ne')
  · intro n
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hu : -(1 / ((n : ℝ) + 1)) < 1 := by
      have hinv : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    rw [complexMGF_ofReal, complexMGF_ofReal]
    rw [mgf_complexGaussianVectorRadiusSq
      (u := -(1 / ((n : ℝ) + 1))) hu]
    rw [mgf_gammaMeasure_nat d hd
      (u := -(1 / ((n : ℝ) + 1))) hu]
    simp

/-- The squared norm of the explicit standard complex Gaussian vector has
exactly the unit-rate Gamma law of integer shape. -/
theorem map_complexGaussianVectorRadiusSq_eq_gammaMeasure
    (d : ℕ) (hd : 0 < d) :
    (complexGaussianVectorMeasure (Fin d)).map
        (complexGaussianVectorRadiusSq :
          (Fin d → ℝ × ℝ) → ℝ) =
      gammaMeasure d 1 := by
  letI : IsProbabilityMeasure (gammaMeasure d 1) :=
    isProbabilityMeasure_gammaMeasure (by exact_mod_cast hd) one_pos
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_mul_I
    measurable_complexGaussianVectorRadiusSq.aemeasurable t]
  rw [← complexMGF_id_mul_I (μ := gammaMeasure d 1) t]
  exact eqOn_complexMGF_gaussianRadius_gamma d hd
    (by simp)

/-- A fixed real power is Borel measurable even for a negative exponent;
the only discontinuity can be at zero. -/
theorem measurable_rpow_const (s : ℝ) :
    Measurable (fun x : ℝ => x ^ s) := by
  apply measurable_of_continuousOn_compl_singleton 0
  apply continuousOn_id.rpow_const
  intro x hx
  exact Or.inl (by simpa using hx)

/-- Transfer any real-power radial integral to the matching Gamma law. -/
theorem integral_rpow_complexGaussianVectorRadiusSq_eq_gamma
    (d : ℕ) (hd : 0 < d) (s : ℝ) :
    (∫ ω : Fin d → ℝ × ℝ,
        complexGaussianVectorRadiusSq ω ^ s
        ∂complexGaussianVectorMeasure (Fin d)) =
      ∫ x : ℝ, x ^ s ∂gammaMeasure d 1 := by
  calc
    (∫ ω : Fin d → ℝ × ℝ,
        complexGaussianVectorRadiusSq ω ^ s
        ∂complexGaussianVectorMeasure (Fin d)) =
        ∫ x : ℝ, x ^ s
          ∂((complexGaussianVectorMeasure (Fin d)).map
            (complexGaussianVectorRadiusSq :
              (Fin d → ℝ × ℝ) → ℝ)) := by
      rw [integral_map
        measurable_complexGaussianVectorRadiusSq.aemeasurable
        (measurable_rpow_const s).aestronglyMeasurable]
    _ = ∫ x : ℝ, x ^ s ∂gammaMeasure d 1 := by
      rw [map_complexGaussianVectorRadiusSq_eq_gammaMeasure d hd]

/-- Exact negative even moment of the explicit Gaussian vector's squared
radius. -/
theorem gaussianVectorRadiusSq_negative_even_moment
    (d q : ℕ) (hd : 0 < d) (hq : 0 < q) (hqd : 2 * q < d) :
    (∫ ω : Fin d → ℝ × ℝ,
        complexGaussianVectorRadiusSq ω ^
          (-(2 * q : ℕ) : ℝ)
        ∂complexGaussianVectorMeasure (Fin d)) =
      (Nat.factorial (d - 2 * q - 1) : ℝ) /
        Nat.factorial (d - 1) := by
  rw [integral_rpow_complexGaussianVectorRadiusSq_eq_gamma d hd]
  exact gamma_negative_even_moment d q hq hqd

/-- The inverse-radius moment bound in the explicit Gaussian probability
space.  No Gamma-law premise remains. -/
theorem gaussianVectorRadiusSq_negative_even_moment_le
    (d q : ℕ) (hq : 0 < q) (hfour : 4 * q ≤ d) :
    (∫ ω : Fin d → ℝ × ℝ,
        complexGaussianVectorRadiusSq ω ^
          (-(2 * q : ℕ) : ℝ)
        ∂complexGaussianVectorMeasure (Fin d)) ≤
      (2 / (d : ℝ)) ^ (2 * q) := by
  have hd : 0 < d := by omega
  rw [integral_rpow_complexGaussianVectorRadiusSq_eq_gamma d hd]
  exact gamma_negative_even_moment_le d q hq hfour

/-- Root form of the inverse-radius estimate used in Hölder's inequality. -/
theorem gaussianVector_inverse_radius_Lp_le
    (d q : ℕ) (hq : 0 < q) (hfour : 4 * q ≤ d) :
    ((∫ ω : Fin d → ℝ × ℝ,
        complexGaussianVectorRadiusSq ω ^
          (-(2 * q : ℕ) : ℝ)
        ∂complexGaussianVectorMeasure (Fin d)) ^
      (((2 * q : ℕ) : ℝ)⁻¹)) ≤
      2 / (d : ℝ) := by
  have hd : 0 < d := by omega
  rw [integral_rpow_complexGaussianVectorRadiusSq_eq_gamma d hd]
  exact gamma_inverse_radius_Lp_le d q hq hfour

end QuantumSep
