import QuantumSep.GaussianWick
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Finite products of Gaussian measures

Mathlib proves that a binary product of Gaussian measures is Gaussian.  The
finite dependent-product result needed for the explicit complex Gaussian
sample space is established here from characteristic functions, component
means, and the variance formula for independent coordinates.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace QuantumSep

noncomputable section

/-- A finite product of Gaussian probability measures is Gaussian. -/
theorem isGaussian_pi
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)]
    [∀ i, CompleteSpace (E i)]
    [∀ i, SecondCountableTopology (E i)]
    {mE : ∀ i, MeasurableSpace (E i)}
    [∀ i, BorelSpace (E i)]
    (μ : (i : ι) → Measure (E i))
    [∀ i, IsGaussian (μ i)] :
    IsGaussian (Measure.pi μ) := by
  apply isGaussian_of_charFunDual_eq
  intro L
  rw [charFunDual_pi]
  simp_rw [IsGaussian.charFunDual_eq]
  rw [← Complex.exp_sum]
  congr 1
  have hLfun :
      (fun x : ∀ i, E i => L x) =
        ∑ i, fun x => (L.comp (.single ℝ E i)) (x i) := by
    funext x
    simpa only [Finset.sum_apply] using
      (ContinuousLinearMap.sum_comp_single ℝ E L x).symm
  have hmean :
      (Measure.pi μ)[L] =
        ∑ i, (μ i)[L.comp (.single ℝ E i)] := by
    change (∫ x, L x ∂Measure.pi μ) =
      ∑ i, ∫ y, (L.comp (.single ℝ E i)) y ∂μ i
    rw [hLfun]
    have hpoint :
        (∑ i, fun x : ∀ i, E i =>
          (L.comp (.single ℝ E i)) (x i)) =
        fun x => ∑ i, (L.comp (.single ℝ E i)) (x i) := by
      funext x
      simp
    rw [hpoint, integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro i _
      exact integral_comp_eval
        (IsGaussian.integrable_dual (μ i)
          (L.comp (.single ℝ E i))).aestronglyMeasurable
    · intro i _
      exact integrable_comp_eval
        (IsGaussian.integrable_dual (μ i)
          (L.comp (.single ℝ E i)))
  have hvar :
      Var[L; Measure.pi μ] =
        ∑ i, Var[L.comp (.single ℝ E i); μ i] := by
    change variance (fun x => L x) (Measure.pi μ) = _
    rw [hLfun]
    exact variance_sum_pi fun i =>
      IsGaussian.memLp_dual (μ i)
        (L.comp (.single ℝ E i)) 2 (by norm_num)
  have hmeanC := congrArg (fun r : ℝ => (r : ℂ)) hmean
  rw [Complex.ofReal_sum] at hmeanC
  have hvarC := congrArg (fun r : ℝ => (r : ℂ)) hvar
  rw [Complex.ofReal_sum] at hvarC
  have hmeanC' :
      (∫ x, (L x : ℂ) ∂Measure.pi μ) =
        ∑ i, ∫ y,
          ((L.comp (.single ℝ E i)) y : ℂ) ∂μ i := by
    simpa only [← integral_complex_ofReal] using hmeanC
  rw [hmeanC', hvarC]
  rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_div]

noncomputable instance isGaussian_realGaussianHalf :
    IsGaussian realGaussianHalf := by
  unfold realGaussianHalf
  infer_instance

noncomputable instance isGaussian_complexGaussianPairMeasure :
    IsGaussian complexGaussianPairMeasure := by
  unfold complexGaussianPairMeasure
  infer_instance

noncomputable instance isGaussian_complexGaussianVectorMeasure
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    IsGaussian (complexGaussianVectorMeasure ι) := by
  unfold complexGaussianVectorMeasure
  exact isGaussian_pi fun _ => complexGaussianPairMeasure

end

end QuantumSep
