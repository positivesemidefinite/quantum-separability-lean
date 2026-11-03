import QuantumSep.GaussianRadius
import QuantumSep.Normalization

/-!
# Normalizing the explicit complex Gaussian vector

The radial law from `GaussianRadius` implies that the Gaussian vector is
nonzero almost surely.  This file defines its direction and proves directly
that the direction has squared norm one almost surely.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ComplexConjugate

namespace QuantumSep

noncomputable section

/-- The explicit complex Gaussian vector, extracted from the real-pair
product probability space. -/
def complexGaussianVector {ι : Type*} (ω : ι → ℝ × ℝ) : ι → ℂ :=
  fun i => complexGaussianCoordinate i ω

theorem vectorNormSq_complexGaussianVector
    {ι : Type*} [Fintype ι] (ω : ι → ℝ × ℝ) :
    vectorNormSq (complexGaussianVector ω) =
      complexGaussianVectorRadiusSq ω := by
  rw [complexGaussianVectorRadiusSq_eq_sum_normSq]
  rfl

theorem complexGaussianVectorRadiusSq_nonneg
    {ι : Type*} [Fintype ι] (ω : ι → ℝ × ℝ) :
    0 ≤ complexGaussianVectorRadiusSq ω := by
  unfold complexGaussianVectorRadiusSq complexGaussianPairRadiusSq
  positivity

/-- A positive-shape Gamma law has no atom at zero. -/
theorem gammaMeasure_singleton_zero
    (d : ℕ) (_hd : 0 < d) :
    gammaMeasure d 1 ({0} : Set ℝ) = 0 := by
  unfold gammaMeasure
  exact withDensity_absolutelyContinuous volume (gammaPDF d 1)
    (measure_singleton 0)

/-- The explicit finite complex Gaussian vector has nonzero squared radius
almost surely. -/
theorem ae_complexGaussianVectorRadiusSq_ne_zero
    (d : ℕ) (hd : 0 < d) :
    ∀ᵐ ω : Fin d → ℝ × ℝ
      ∂complexGaussianVectorMeasure (Fin d),
      complexGaussianVectorRadiusSq ω ≠ 0 := by
  rw [ae_iff]
  have hzero :
      (complexGaussianVectorMeasure (Fin d))
          ((complexGaussianVectorRadiusSq :
            (Fin d → ℝ × ℝ) → ℝ) ⁻¹' ({0} : Set ℝ)) = 0 := by
    calc
      (complexGaussianVectorMeasure (Fin d))
          ((complexGaussianVectorRadiusSq :
            (Fin d → ℝ × ℝ) → ℝ) ⁻¹' ({0} : Set ℝ)) =
          ((complexGaussianVectorMeasure (Fin d)).map
            (complexGaussianVectorRadiusSq :
              (Fin d → ℝ × ℝ) → ℝ)) ({0} : Set ℝ) := by
        rw [Measure.map_apply_of_aemeasurable
          measurable_complexGaussianVectorRadiusSq.aemeasurable
          (measurableSet_singleton (0 : ℝ))]
      _ = gammaMeasure d 1 ({0} : Set ℝ) := by
        rw [map_complexGaussianVectorRadiusSq_eq_gammaMeasure d hd]
      _ = 0 := gammaMeasure_singleton_zero d hd
  rw [show
    {ω : Fin d → ℝ × ℝ |
      ¬complexGaussianVectorRadiusSq ω ≠ 0} =
      (complexGaussianVectorRadiusSq :
        (Fin d → ℝ × ℝ) → ℝ) ⁻¹' ({0} : Set ℝ) by
      ext ω
      simp]
  exact hzero

theorem ae_complexGaussianVectorRadiusSq_pos
    (d : ℕ) (hd : 0 < d) :
    ∀ᵐ ω : Fin d → ℝ × ℝ
      ∂complexGaussianVectorMeasure (Fin d),
      0 < complexGaussianVectorRadiusSq ω := by
  filter_upwards [ae_complexGaussianVectorRadiusSq_ne_zero d hd] with ω hω
  exact lt_of_le_of_ne
    (complexGaussianVectorRadiusSq_nonneg ω) (Ne.symm hω)

/-- Normalize the Gaussian vector to the complex unit sphere.  On the null
zero-radius event this definition returns the zero vector. -/
def complexGaussianDirection
    {ι : Type*} [Fintype ι]
    (ω : ι → ℝ × ℝ) : ι → ℂ :=
  fun i =>
    ((1 / Real.sqrt (complexGaussianVectorRadiusSq ω) : ℝ) : ℂ) *
      complexGaussianVector ω i

theorem vectorNormSq_complexGaussianDirection_of_pos
    {ι : Type*} [Fintype ι]
    (ω : ι → ℝ × ℝ)
    (hω : 0 < complexGaussianVectorRadiusSq ω) :
    vectorNormSq (complexGaussianDirection ω) = 1 := by
  unfold vectorNormSq complexGaussianDirection
  simp_rw [Complex.normSq_mul, Complex.normSq_ofReal]
  rw [← Finset.mul_sum]
  rw [← pow_two]
  change
    (1 / Real.sqrt (complexGaussianVectorRadiusSq ω)) ^ 2 *
        vectorNormSq (complexGaussianVector ω) = 1
  rw [vectorNormSq_complexGaussianVector]
  rw [div_pow, one_pow, Real.sq_sqrt hω.le]
  field_simp [hω.ne']

/-- The normalized explicit Gaussian vector lies on the unit sphere almost
surely. -/
theorem ae_vectorNormSq_complexGaussianDirection_eq_one
    (d : ℕ) (hd : 0 < d) :
    ∀ᵐ ω : Fin d → ℝ × ℝ
      ∂complexGaussianVectorMeasure (Fin d),
      vectorNormSq (complexGaussianDirection ω) = 1 := by
  filter_upwards [ae_complexGaussianVectorRadiusSq_pos d hd] with ω hω
  exact vectorNormSq_complexGaussianDirection_of_pos ω hω

/-- The explicit complex Gaussian vector is measurable. -/
theorem measurable_complexGaussianVector
    {ι : Type*} [Fintype ι] :
    Measurable (complexGaussianVector :
      (ι → ℝ × ℝ) → (ι → ℂ)) := by
  exact measurable_pi_lambda _ fun i =>
    measurable_complexGaussianCoordinate i

/-- Normalizing by the measurable squared radius preserves measurability. -/
theorem measurable_complexGaussianDirection
    {ι : Type*} [Fintype ι] :
    Measurable (complexGaussianDirection :
      (ι → ℝ × ℝ) → (ι → ℂ)) := by
  apply measurable_pi_lambda
  intro i
  exact
    (Complex.measurable_ofReal.comp
      (measurable_const.div
        (Real.continuous_sqrt.measurable.comp
          measurable_complexGaussianVectorRadiusSq))).mul
      (measurable_complexGaussianCoordinate i)

/-- The normalized-Gaussian direction law on the complex unit sphere. -/
noncomputable def complexGaussianDirectionMeasure (d : ℕ) :
    Measure (Fin d → ℂ) :=
  (complexGaussianVectorMeasure (Fin d)).map
    (complexGaussianDirection :
      (Fin d → ℝ × ℝ) → (Fin d → ℂ))

noncomputable instance isProbabilityMeasure_complexGaussianDirectionMeasure
    (d : ℕ) :
    IsProbabilityMeasure (complexGaussianDirectionMeasure d) := by
  unfold complexGaussianDirectionMeasure
  exact Measure.isProbabilityMeasure_map
    measurable_complexGaussianDirection.aemeasurable

/-- In positive dimension the normalized-Gaussian direction measure is
concentrated on the complex unit sphere. -/
theorem ae_vectorNormSq_complexGaussianDirectionMeasure_eq_one
    (d : ℕ) (hd : 0 < d) :
    ∀ᵐ x ∂complexGaussianDirectionMeasure d,
      vectorNormSq x = 1 := by
  have hp :
      MeasurableSet {x : Fin d → ℂ | vectorNormSq x = 1} := by
    have hv :
        Measurable (fun x : Fin d → ℂ => vectorNormSq x) := by
      unfold vectorNormSq
      fun_prop
    exact hv (measurableSet_singleton (1 : ℝ))
  unfold complexGaussianDirectionMeasure
  rw [MeasureTheory.ae_map_iff
    measurable_complexGaussianDirection.aemeasurable hp]
  exact ae_vectorNormSq_complexGaussianDirection_eq_one d hd

end

end QuantumSep
