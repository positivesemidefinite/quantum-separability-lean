import QuantumSep.PaperInterfaces
import QuantumSep.HaarGaussian
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal

namespace QuantumSep

noncomputable section

theorem integral_mul_pow_root_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (f g : Ω → ℝ) (q : ℕ) (hq : 0 < q)
    (hf_nonneg : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    (hg_nonneg : ∀ᵐ ω ∂μ, 0 ≤ g ω)
    (hf : MemLp (fun ω => f ω ^ q) (ENNReal.ofReal 2) μ)
    (hg : MemLp (fun ω => g ω ^ q) (ENNReal.ofReal 2) μ) :
    ((∫ ω, (f ω * g ω) ^ q ∂μ) ^
        (((q : ℝ))⁻¹)) ≤
      ((∫ ω, f ω ^ (2 * q) ∂μ) ^
          (((2 * q : ℕ) : ℝ)⁻¹)) *
        ((∫ ω, g ω ^ (2 * q) ∂μ) ^
          (((2 * q : ℕ) : ℝ)⁻¹)) := by
  have hfq_nonneg : ∀ᵐ ω ∂μ, 0 ≤ f ω ^ q :=
    hf_nonneg.mono fun ω hω => pow_nonneg hω q
  have hgq_nonneg : ∀ᵐ ω ∂μ, 0 ≤ g ω ^ q :=
    hg_nonneg.mono fun ω hω => pow_nonneg hω q
  have hholder :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      Real.HolderConjugate.two_two hfq_nonneg hgq_nonneg hf hg
  have hleft_nonneg :
      0 ≤ ∫ ω, (f ω * g ω) ^ q ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hf_nonneg, hg_nonneg] with ω hfω hgω
    positivity
  have hIf :
      0 ≤ ∫ ω, (f ω ^ q) ^ (2 : ℝ) ∂μ := by
    apply integral_nonneg_of_ae
    exact hfq_nonneg.mono fun ω hω => Real.rpow_nonneg hω 2
  have hIg :
      0 ≤ ∫ ω, (g ω ^ q) ^ (2 : ℝ) ∂μ := by
    apply integral_nonneg_of_ae
    exact hgq_nonneg.mono fun ω hω => Real.rpow_nonneg hω 2
  have hright_nonneg :
      0 ≤
        (∫ ω, (f ω ^ q) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ ω, (g ω ^ q) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    exact mul_nonneg (Real.rpow_nonneg hIf _) (Real.rpow_nonneg hIg _)
  have hholder' :
      (∫ ω, (f ω * g ω) ^ q ∂μ) ≤
        (∫ ω, (f ω ^ q) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ ω, (g ω ^ q) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    simpa [mul_pow] using hholder
  calc
    ((∫ ω, (f ω * g ω) ^ q ∂μ) ^ (((q : ℝ))⁻¹)) ≤
        (((∫ ω, (f ω ^ q) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) *
          ((∫ ω, (g ω ^ q) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)))) ^
          (((q : ℝ))⁻¹) :=
      Real.rpow_le_rpow hleft_nonneg hholder' (by positivity)
    _ = ((∫ ω, f ω ^ (2 * q) ∂μ) ^
          (((2 * q : ℕ) : ℝ)⁻¹)) *
        ((∫ ω, g ω ^ (2 * q) ∂μ) ^
          (((2 * q : ℕ) : ℝ)⁻¹)) := by
      rw [Real.mul_rpow
        (Real.rpow_nonneg hIf _) (Real.rpow_nonneg hIg _)]
      congr 1
      · rw [← Real.rpow_mul (integral_nonneg_of_ae
            (hfq_nonneg.mono fun ω hω => Real.rpow_nonneg hω 2))]
        congr 1
        · apply integral_congr_ae
          filter_upwards [hf_nonneg] with ω hω
          rw [Real.rpow_two]
          ring
        · push_cast
          ring
      · rw [← Real.rpow_mul (integral_nonneg_of_ae
            (hgq_nonneg.mono fun ω hω => Real.rpow_nonneg hω 2))]
        congr 1
        · apply integral_congr_ae
          filter_upwards [hg_nonneg] with ω hω
          rw [Real.rpow_two]
          ring
        · push_cast
          ring

def vectorQuadraticForm
    {ι : Type*} [Fintype ι]
    (A : CMatrix ι) (x : ι → ℂ) : ℂ :=
  ∑ i : ι, ∑ j : ι, star (x i) * A i j * x j

def gaussianQuadraticFamilyNorm
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (ω : Fin d → ℝ × ℝ) : ℝ :=
  Real.sqrt (gaussianQuadraticFamilyNormSq d A ω)

def sphereQuadraticFamilyNorm
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (x : Fin d → ℂ) : ℝ :=
  Real.sqrt
    (∑ k : κ,
      Complex.normSq
        (vectorQuadraticForm (tracelessPart (A k)) x))

theorem measurable_gaussianQuadraticFamilyNormSq
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d)) :
    Measurable (gaussianQuadraticFamilyNormSq d A) := by
  unfold gaussianQuadraticFamilyNormSq
  apply Finset.measurable_sum
  intro k _
  apply Complex.continuous_normSq.measurable.comp
  unfold gaussianQuadraticForm
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact
    (((Complex.continuous_conj.measurable.comp
      (measurable_complexGaussianCoordinate i)).mul
        measurable_const).mul
      (measurable_complexGaussianCoordinate j))

theorem measurable_gaussianQuadraticFamilyNorm
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d)) :
    Measurable (gaussianQuadraticFamilyNorm d A) := by
  exact Real.continuous_sqrt.measurable.comp
    (measurable_gaussianQuadraticFamilyNormSq d A)

theorem measurable_sphereQuadraticFamilyNorm
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d)) :
    Measurable (sphereQuadraticFamilyNorm d A) := by
  unfold sphereQuadraticFamilyNorm vectorQuadraticForm
  fun_prop

theorem gaussianQuadraticFamilyNorm_nonneg
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (ω : Fin d → ℝ × ℝ) :
    0 ≤ gaussianQuadraticFamilyNorm d A ω :=
  Real.sqrt_nonneg _

theorem gaussianQuadraticFamilyNorm_pow_two
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (ω : Fin d → ℝ × ℝ) :
    gaussianQuadraticFamilyNorm d A ω ^ 2 =
      gaussianQuadraticFamilyNormSq d A ω := by
  rw [gaussianQuadraticFamilyNorm, Real.sq_sqrt]
  unfold gaussianQuadraticFamilyNormSq
  exact Finset.sum_nonneg fun k _ =>
    Complex.normSq_nonneg _

theorem vectorQuadraticForm_complexGaussianVector
    (d : ℕ) (A : CMatrix (Fin d))
    (ω : Fin d → ℝ × ℝ) :
    vectorQuadraticForm A (complexGaussianVector ω) =
      gaussianQuadraticForm A ω := by
  rfl

theorem vectorQuadraticForm_complexGaussianDirection_of_pos
    (d : ℕ) (A : CMatrix (Fin d))
    (ω : Fin d → ℝ × ℝ)
    (hω : 0 < complexGaussianVectorRadiusSq ω) :
    vectorQuadraticForm A (complexGaussianDirection ω) =
      ((complexGaussianVectorRadiusSq ω)⁻¹ : ℝ) •
        gaussianQuadraticForm A ω := by
  let c : ℝ :=
    1 / Real.sqrt (complexGaussianVectorRadiusSq ω)
  have hc :
    c * c = (complexGaussianVectorRadiusSq ω)⁻¹ := by
    dsimp [c]
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hω.le]
    simp [div_eq_mul_inv]
  rw [Complex.real_smul]
  change
    vectorQuadraticForm A (complexGaussianDirection ω) =
      (((complexGaussianVectorRadiusSq ω)⁻¹ : ℝ) : ℂ) *
        gaussianQuadraticForm A ω
  unfold vectorQuadraticForm complexGaussianDirection
  change
    (∑ i : Fin d, ∑ j : Fin d,
      star ((c : ℂ) * complexGaussianCoordinate i ω) *
        A i j * ((c : ℂ) * complexGaussianCoordinate j ω)) =
      (((complexGaussianVectorRadiusSq ω)⁻¹ : ℝ) : ℂ) *
        gaussianQuadraticForm A ω
  unfold gaussianQuadraticForm
  rw [← hc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [star_mul, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

theorem sphereQuadraticFamilyNorm_direction_of_pos
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (ω : Fin d → ℝ × ℝ)
    (hω : 0 < complexGaussianVectorRadiusSq ω) :
    sphereQuadraticFamilyNorm d A (complexGaussianDirection ω) =
      (complexGaussianVectorRadiusSq ω)⁻¹ *
        gaussianQuadraticFamilyNorm d A ω := by
  have hRinv : 0 ≤ (complexGaussianVectorRadiusSq ω)⁻¹ :=
    inv_nonneg.mpr hω.le
  unfold sphereQuadraticFamilyNorm
  rw [gaussianQuadraticFamilyNorm]
  have hsum :
    (∑ k : κ,
      Complex.normSq
        (vectorQuadraticForm
          (tracelessPart (A k))
          (complexGaussianDirection ω))) =
      (complexGaussianVectorRadiusSq ω)⁻¹ ^ 2 *
        gaussianQuadraticFamilyNormSq d A ω := by
    unfold gaussianQuadraticFamilyNormSq
    calc
      (∑ k : κ,
        Complex.normSq
          (vectorQuadraticForm
            (tracelessPart (A k))
            (complexGaussianDirection ω))) =
          ∑ k : κ,
            (complexGaussianVectorRadiusSq ω)⁻¹ ^ 2 *
              Complex.normSq
                (gaussianQuadraticForm
                  (tracelessPart (A k)) ω) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [vectorQuadraticForm_complexGaussianDirection_of_pos
          d (tracelessPart (A k)) ω hω]
        change
          Complex.normSq
            ((((complexGaussianVectorRadiusSq ω)⁻¹ : ℝ) : ℂ) *
              gaussianQuadraticForm (tracelessPart (A k)) ω) =
            (complexGaussianVectorRadiusSq ω)⁻¹ ^ 2 *
              Complex.normSq
                (gaussianQuadraticForm
                  (tracelessPart (A k)) ω)
        rw [Complex.normSq_mul, Complex.normSq_ofReal]
        ring
      _ = (complexGaussianVectorRadiusSq ω)⁻¹ ^ 2 *
          ∑ k : κ,
            Complex.normSq
              (gaussianQuadraticForm
                (tracelessPart (A k)) ω) := by
        rw [Finset.mul_sum]
  calc
    Real.sqrt
        (∑ k : κ,
          Complex.normSq
            (vectorQuadraticForm
              (tracelessPart (A k))
              (complexGaussianDirection ω))) =
        Real.sqrt
          ((complexGaussianVectorRadiusSq ω)⁻¹ ^ 2 *
            gaussianQuadraticFamilyNormSq d A ω) := by
      rw [hsum]
    _ = (complexGaussianVectorRadiusSq ω)⁻¹ *
        Real.sqrt (gaussianQuadraticFamilyNormSq d A ω) := by
      rw [Real.sqrt_mul (sq_nonneg _)]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hRinv]

theorem inverse_radius_pow_sq
    (d q : ℕ) (ω : Fin d → ℝ × ℝ) :
    ((complexGaussianVectorRadiusSq ω)⁻¹ ^ q) ^ 2 =
      complexGaussianVectorRadiusSq ω ^
        (-(2 * q : ℕ) : ℝ) := by
  calc
    ((complexGaussianVectorRadiusSq ω)⁻¹ ^ q) ^ 2 =
        (complexGaussianVectorRadiusSq ω)⁻¹ ^ (q * 2) := by
      rw [pow_mul]
    _ = (complexGaussianVectorRadiusSq ω)⁻¹ ^ (2 * q) := by
      rw [Nat.mul_comm]
    _ = (complexGaussianVectorRadiusSq ω)⁻¹ ^
        ((2 * q : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    _ = complexGaussianVectorRadiusSq ω ^
        (-((2 * q : ℕ) : ℝ)) := by
      rw [Real.rpow_neg_eq_inv_rpow]

theorem integrable_gaussianVectorRadiusSq_negative_even
    (d q : ℕ) (hd : 0 < d) (hq : 0 < q)
    (hqd : 2 * q < d) :
    Integrable
      (fun ω : Fin d → ℝ × ℝ =>
        complexGaussianVectorRadiusSq ω ^
          (-(2 * q : ℕ) : ℝ))
      (complexGaussianVectorMeasure (Fin d)) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussianVectorRadiusSq_negative_even_moment d q hd hq hqd]
  positivity

theorem memLp_inverseRadius_pow
    (d q : ℕ) (hd : 0 < d) (hq : 0 < q)
    (hqd : 2 * q < d) :
    MemLp
      (fun ω : Fin d → ℝ × ℝ =>
        (complexGaussianVectorRadiusSq ω)⁻¹ ^ q)
      (ENNReal.ofReal 2)
      (complexGaussianVectorMeasure (Fin d)) := by
  have hmeas :
      AEStronglyMeasurable
        (fun ω : Fin d → ℝ × ℝ =>
          (complexGaussianVectorRadiusSq ω)⁻¹ ^ q)
        (complexGaussianVectorMeasure (Fin d)) := by
    exact
      (measurable_complexGaussianVectorRadiusSq.aestronglyMeasurable
        |>.inv₀.pow q)
  have hint :=
    integrable_gaussianVectorRadiusSq_negative_even
      d q hd hq hqd
  have hint' :
      Integrable
        (fun ω : Fin d → ℝ × ℝ =>
          ((complexGaussianVectorRadiusSq ω)⁻¹ ^ q) ^ 2)
        (complexGaussianVectorMeasure (Fin d)) := by
    apply hint.congr
    filter_upwards with ω
    exact (inverse_radius_pow_sq d q ω).symm
  convert (memLp_two_iff_integrable_sq hmeas).2 hint' using 1 <;>
    norm_num

theorem memLp_gaussianQuadraticFamilyNorm_pow
    (hc : GaussianHypercontractivityContract)
    {κ : Type} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (q : ℕ) (hq : 1 ≤ q) :
    MemLp
      (fun ω : Fin d → ℝ × ℝ =>
        gaussianQuadraticFamilyNorm d A ω ^ q)
      (ENNReal.ofReal 2)
      (complexGaussianVectorMeasure (Fin d)) := by
  have hmeas :
      AEStronglyMeasurable
        (fun ω : Fin d → ℝ × ℝ =>
          gaussianQuadraticFamilyNorm d A ω ^ q)
        (complexGaussianVectorMeasure (Fin d)) :=
    ((measurable_gaussianQuadraticFamilyNorm d A).pow_const q)
      |>.aestronglyMeasurable
  have hint :=
    hc.degreeTwo_moment_integrable d κ A q hq
  have hint' :
      Integrable
        (fun ω : Fin d → ℝ × ℝ =>
          (gaussianQuadraticFamilyNorm d A ω ^ q) ^ 2)
        (complexGaussianVectorMeasure (Fin d)) := by
    apply hint.congr
    filter_upwards with ω
    rw [← pow_mul, Nat.mul_comm, pow_mul,
      gaussianQuadraticFamilyNorm_pow_two]
  convert (memLp_two_iff_integrable_sq hmeas).2 hint' using 1 <;>
    norm_num

theorem inverse_radius_pow_even
    (d q : ℕ) (ω : Fin d → ℝ × ℝ) :
    (complexGaussianVectorRadiusSq ω)⁻¹ ^ (2 * q) =
      complexGaussianVectorRadiusSq ω ^
        (-(2 * q : ℕ) : ℝ) := by
  calc
    (complexGaussianVectorRadiusSq ω)⁻¹ ^ (2 * q) =
        (complexGaussianVectorRadiusSq ω)⁻¹ ^
          ((2 * q : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    _ = complexGaussianVectorRadiusSq ω ^
        (-((2 * q : ℕ) : ℝ)) := by
      rw [Real.rpow_neg_eq_inv_rpow]

theorem gaussianQuadraticFamilyNorm_pow_even
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (q : ℕ) (ω : Fin d → ℝ × ℝ) :
    gaussianQuadraticFamilyNorm d A ω ^ (2 * q) =
      gaussianQuadraticFamilyNormSq d A ω ^ q := by
  rw [pow_mul, gaussianQuadraticFamilyNorm_pow_two]

theorem normalizedGaussianQuadraticFamily_moment_le
    (hc : GaussianHypercontractivityContract)
    {κ : Type} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (q : ℕ) (hq : 0 < q) (hfour : 4 * q ≤ d) :
    ((∫ ω : Fin d → ℝ × ℝ,
        sphereQuadraticFamilyNorm d A
            (complexGaussianDirection ω) ^ q
        ∂complexGaussianVectorMeasure (Fin d)) ^
      (((q : ℝ))⁻¹)) ≤
      (2 * hc.constant * q / (d : ℝ)) *
        ((∑ k : κ, frobeniusSq (A k)) ^
          ((2 : ℝ)⁻¹)) := by
  have hd : 0 < d := by omega
  let μ := complexGaussianVectorMeasure (Fin d)
  let f : (Fin d → ℝ × ℝ) → ℝ :=
    fun ω => (complexGaussianVectorRadiusSq ω)⁻¹
  let g : (Fin d → ℝ × ℝ) → ℝ :=
    gaussianQuadraticFamilyNorm d A
  have hf_nonneg : ∀ᵐ ω ∂μ, 0 ≤ f ω := by
    filter_upwards with ω
    exact inv_nonneg.mpr
      (complexGaussianVectorRadiusSq_nonneg ω)
  have hg_nonneg : ∀ᵐ ω ∂μ, 0 ≤ g ω := by
    filter_upwards with ω
    exact gaussianQuadraticFamilyNorm_nonneg d A ω
  have hf :
      MemLp (fun ω => f ω ^ q) (ENNReal.ofReal 2) μ := by
    dsimp [f, μ]
    exact memLp_inverseRadius_pow d q hd hq (by omega)
  have hg :
      MemLp (fun ω => g ω ^ q) (ENNReal.ofReal 2) μ := by
    dsimp [g, μ]
    exact memLp_gaussianQuadraticFamilyNorm_pow
      hc d A q (by omega)
  have hholder :=
    integral_mul_pow_root_le μ f g q hq
      hf_nonneg hg_nonneg hf hg
  have hdir :
      (∫ ω : Fin d → ℝ × ℝ,
          sphereQuadraticFamilyNorm d A
              (complexGaussianDirection ω) ^ q
          ∂μ) =
        ∫ ω, (f ω * g ω) ^ q ∂μ := by
    apply integral_congr_ae
    filter_upwards
      [ae_complexGaussianVectorRadiusSq_pos d hd] with ω hω
    rw [sphereQuadraticFamilyNorm_direction_of_pos
      d A ω hω]
  have hinv :
      (∫ ω, f ω ^ (2 * q) ∂μ) =
        ∫ ω : Fin d → ℝ × ℝ,
          complexGaussianVectorRadiusSq ω ^
            (-(2 * q : ℕ) : ℝ)
          ∂complexGaussianVectorMeasure (Fin d) := by
    apply integral_congr_ae
    filter_upwards with ω
    exact inverse_radius_pow_even d q ω
  have hpoly :
      (∫ ω, g ω ^ (2 * q) ∂μ) =
        ∫ ω : Fin d → ℝ × ℝ,
          gaussianQuadraticFamilyNormSq d A ω ^ q
          ∂complexGaussianVectorMeasure (Fin d) := by
    apply integral_congr_ae
    filter_upwards with ω
    exact gaussianQuadraticFamilyNorm_pow_even d A q ω
  rw [← hdir, hinv, hpoly] at hholder
  have hinverse :=
    gaussianVector_inverse_radius_Lp_le d q hq hfour
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hhyper :=
    hc.degreeTwo_L2_to_frobenius d A q (by omega)
  have hpoly_nonneg :
      0 ≤
        ((∫ ω : Fin d → ℝ × ℝ,
          gaussianQuadraticFamilyNormSq d A ω ^ q
          ∂complexGaussianVectorMeasure (Fin d)) ^
            (((2 * q : ℕ) : ℝ)⁻¹)) := by
    apply Real.rpow_nonneg
    apply integral_nonneg
    intro ω
    exact pow_nonneg
      (Finset.sum_nonneg fun k _ =>
        Complex.normSq_nonneg _) q
  calc
    _ ≤
        ((∫ ω : Fin d → ℝ × ℝ,
          complexGaussianVectorRadiusSq ω ^
            (-(2 * q : ℕ) : ℝ)
          ∂complexGaussianVectorMeasure (Fin d)) ^
            (((2 * q : ℕ) : ℝ)⁻¹)) *
        ((∫ ω : Fin d → ℝ × ℝ,
          gaussianQuadraticFamilyNormSq d A ω ^ q
          ∂complexGaussianVectorMeasure (Fin d)) ^
            (((2 * q : ℕ) : ℝ)⁻¹)) :=
      hholder
    _ ≤ (2 / (d : ℝ)) *
        ((∫ ω : Fin d → ℝ × ℝ,
          gaussianQuadraticFamilyNormSq d A ω ^ q
          ∂complexGaussianVectorMeasure (Fin d)) ^
            (((2 * q : ℕ) : ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_right hinverse hpoly_nonneg
    _ ≤ (2 / (d : ℝ)) *
        (hc.constant * q *
          ((∑ k : κ, frobeniusSq (A k)) ^
            ((2 : ℝ)⁻¹))) := by
      exact mul_le_mul_of_nonneg_left hhyper (by positivity)
    _ = (2 * hc.constant * q / (d : ℝ)) *
        ((∑ k : κ, frobeniusSq (A k)) ^
          ((2 : ℝ)⁻¹)) := by ring

theorem onePartyHaar_rankOne_moment_le
    (hc : GaussianHypercontractivityContract)
    {κ : Type} [Fintype κ]
    (d : ℕ) (a : Fin d)
    (A : κ → CMatrix (Fin d))
    (q : ℕ) (hq : 0 < q) (hfour : 4 * q ≤ d) :
    ((∫ x : Fin d → ℂ,
        sphereQuadraticFamilyNorm d A x ^ q
        ∂haarColumnMeasure d a) ^
      (((q : ℝ))⁻¹)) ≤
      (2 * hc.constant * q / (d : ℝ)) *
        ((∑ k : κ, frobeniusSq (A k)) ^
          ((2 : ℝ)⁻¹)) := by
  have hd : 0 < d := by omega
  have hmeasure :=
    complexGaussianDirectionMeasure_eq_haarColumnMeasure
      d hd a
  have hmeas :
      AEStronglyMeasurable
        (fun x : Fin d → ℂ =>
          sphereQuadraticFamilyNorm d A x ^ q)
        (complexGaussianDirectionMeasure d) :=
    ((measurable_sphereQuadraticFamilyNorm d A).pow_const q)
      |>.aestronglyMeasurable
  have hintegral :
      (∫ x : Fin d → ℂ,
          sphereQuadraticFamilyNorm d A x ^ q
          ∂haarColumnMeasure d a) =
        ∫ ω : Fin d → ℝ × ℝ,
          sphereQuadraticFamilyNorm d A
              (complexGaussianDirection ω) ^ q
          ∂complexGaussianVectorMeasure (Fin d) := by
    rw [← hmeasure]
    unfold complexGaussianDirectionMeasure
    rw [integral_map
      measurable_complexGaussianDirection.aemeasurable
      hmeas]
  rw [hintegral]
  exact normalizedGaussianQuadraticFamily_moment_le
    hc d A q hq hfour

end

end QuantumSep
