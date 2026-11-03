import QuantumSep.HaarTwoParty
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Haar flat/tail decomposition

This file proves the manuscript's high-probability Hermitian flat/tail
decomposition from the two-party Haar moment theorem.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal

namespace QuantumSep

noncomputable section

def thresholdTail
    {ι : Type*} [Fintype ι]
    (τ : ℝ) (A : CMatrix ι) : CMatrix ι :=
  fun i j => if τ < ‖A i j‖ then A i j else 0

def thresholdFlat
    {ι : Type*} [Fintype ι]
    (τ : ℝ) (A : CMatrix ι) : CMatrix ι :=
  A - thresholdTail τ A

theorem thresholdTail_add_thresholdFlat
    {ι : Type*} [Fintype ι]
    (τ : ℝ) (A : CMatrix ι) :
    thresholdFlat τ A + thresholdTail τ A = A := by
  unfold thresholdFlat
  abel

theorem thresholdTail_isHermitian
    {ι : Type*} [Fintype ι]
    (τ : ℝ) (A : CMatrix ι)
    (hA : A.IsHermitian) :
    (thresholdTail τ A).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  have hij : star (A j i) = A i j :=
    congrFun (congrFun hA.eq i) j
  have hnorm : ‖A j i‖ = ‖A i j‖ := by
    rw [← hij, norm_star]
  unfold thresholdTail
  simp only [Matrix.conjTranspose_apply]
  by_cases h : τ < ‖A i j‖
  · have h' : τ < ‖A j i‖ := by simpa only [hnorm] using h
    simp [h, h', hij]
  · have h' : ¬ τ < ‖A j i‖ := by simpa only [hnorm] using h
    simp [h, h']

theorem thresholdFlat_isHermitian
    {ι : Type*} [Fintype ι]
    (τ : ℝ) (A : CMatrix ι)
    (hA : A.IsHermitian) :
    (thresholdFlat τ A).IsHermitian :=
  hA.sub (thresholdTail_isHermitian τ A hA)

theorem thresholdFlat_entryNorm_le
    {ι : Type*} [Fintype ι]
    (τ : ℝ) (hτ : 0 ≤ τ) (A : CMatrix ι) :
    entryNorm (thresholdFlat τ A) ≤ τ := by
  unfold entryNorm
  rw [Matrix.norm_le_iff hτ]
  intro i j
  unfold thresholdFlat thresholdTail
  simp only [Matrix.sub_apply]
  by_cases h : τ < ‖A i j‖
  · simp [h, hτ]
  · simpa [h] using not_lt.mp h

theorem bipartiteUnitaryConjugate_isHermitian
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    (bipartiteUnitaryConjugate d M UV).IsHermitian := by
  let W :=
    tensor (UV.1 : CMatrix (Fin d))
      (UV.2 : CMatrix (Fin d))
  change (Matrix.conjTranspose W * (M * W)).IsHermitian
  rw [← Matrix.mul_assoc]
  exact Matrix.isHermitian_conjTranspose_mul_mul W hM

theorem hsInner_eq_trace_conjTranspose_mul
    {ι : Type*} [Fintype ι]
    (A B : CMatrix ι) :
    hsInner A B = (Matrix.conjTranspose A * B).trace := by
  unfold hsInner Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  exact Finset.sum_comm

theorem frobeniusSq_unitaryConjugate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W M : CMatrix ι)
    (hW : W ∈ Matrix.unitaryGroup ι ℂ) :
    frobeniusSq (Matrix.conjTranspose W * (M * W)) =
      frobeniusSq M := by
  have hWW :
      W * Matrix.conjTranspose W = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hW
  apply Complex.ofReal_injective
  rw [← hsInner_self, ← hsInner_self,
    hsInner_eq_trace_conjTranspose_mul,
    hsInner_eq_trace_conjTranspose_mul]
  simp only [Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  calc
    (Matrix.conjTranspose W * Matrix.conjTranspose M * W *
        (Matrix.conjTranspose W * (M * W))).trace =
      (Matrix.conjTranspose W *
        (Matrix.conjTranspose M *
          (W * (Matrix.conjTranspose W * (M * W))))).trace := by
        simp only [Matrix.mul_assoc]
    _ = ((Matrix.conjTranspose M *
          (W * (Matrix.conjTranspose W * (M * W)))) *
        Matrix.conjTranspose W).trace :=
      Matrix.trace_mul_comm _ _
    _ = (Matrix.conjTranspose M * M).trace := by
      simp only [← Matrix.mul_assoc, hWW, Matrix.one_mul]
      rw [Matrix.mul_assoc, hWW, Matrix.mul_one]

theorem tensor_unitary
    (d : ℕ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    tensor (U : CMatrix (Fin d)) (V : CMatrix (Fin d)) ∈
      Matrix.unitaryGroup (Fin d × Fin d) ℂ := by
  exact Matrix.kronecker_mem_unitary U.property V.property

theorem frobeniusSq_bipartiteUnitaryConjugate
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    frobeniusSq (bipartiteUnitaryConjugate d M UV) =
      frobeniusSq M := by
  exact frobeniusSq_unitaryConjugate
    (tensor (UV.1 : CMatrix (Fin d))
      (UV.2 : CMatrix (Fin d))) M
    (tensor_unitary d UV.1 UV.2)

def frobeniusNorm
    {ι : Type*} [Fintype ι]
    (A : CMatrix ι) : ℝ :=
  √(frobeniusSq A)

theorem entryNorm_le_frobeniusNorm
    {ι : Type*} [Fintype ι]
    (A : CMatrix ι) :
    entryNorm A ≤ frobeniusNorm A := by
  unfold entryNorm frobeniusNorm
  rw [Matrix.norm_le_iff (Real.sqrt_nonneg _)]
  intro i j
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  unfold frobeniusSq
  calc
    Complex.normSq (A i j) ≤
        ∑ k : ι, Complex.normSq (A i k) := by
      exact Finset.single_le_sum
        (fun k _ => Complex.normSq_nonneg (A i k))
        (Finset.mem_univ j)
    _ ≤ ∑ k : ι, ∑ l : ι, Complex.normSq (A k l) := by
      exact Finset.single_le_sum
        (fun k _ => Finset.sum_nonneg fun l _ =>
          Complex.normSq_nonneg (A k l))
        (Finset.mem_univ i)

theorem frobeniusNorm_bipartiteUnitaryConjugate
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    frobeniusNorm (bipartiteUnitaryConjugate d M UV) =
      frobeniusNorm M := by
  unfold frobeniusNorm
  rw [frobeniusSq_bipartiteUnitaryConjugate]

theorem frobeniusNorm_lt_mul_of_frobeniusSq_lt
    {ι : Type*} [Fintype ι]
    (A B : CMatrix ι) (δ : ℝ) (hδ : 0 < δ)
    (h :
      frobeniusSq A < δ ^ 2 * frobeniusSq B) :
    frobeniusNorm A < δ * frobeniusNorm B := by
  unfold frobeniusNorm
  calc
    √(frobeniusSq A) <
        √(δ ^ 2 * frobeniusSq B) :=
      Real.sqrt_lt_sqrt (frobeniusSq_nonneg A) h
    _ = δ * √(frobeniusSq B) := by
      rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ.le]

def haarThresholdTail
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (τ : ℝ)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    BipartiteMatrix (Fin d) :=
  thresholdTail τ (bipartiteUnitaryConjugate d M UV)

def haarThresholdFlat
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (τ : ℝ)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    BipartiteMatrix (Fin d) :=
  thresholdFlat τ (bipartiteUnitaryConjugate d M UV)

theorem haarThreshold_decomposition
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (τ : ℝ)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    haarThresholdFlat d M τ UV +
        haarThresholdTail d M τ UV =
      bipartiteUnitaryConjugate d M UV :=
  thresholdTail_add_thresholdFlat τ _

theorem haarThresholdTail_isHermitian
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian) (τ : ℝ)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    (haarThresholdTail d M τ UV).IsHermitian :=
  thresholdTail_isHermitian τ _
    (bipartiteUnitaryConjugate_isHermitian d M hM UV)

theorem haarThresholdFlat_isHermitian
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian) (τ : ℝ)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    (haarThresholdFlat d M τ UV).IsHermitian :=
  thresholdFlat_isHermitian τ _
    (bipartiteUnitaryConjugate_isHermitian d M hM UV)

theorem haarThresholdFlat_entryNorm_le
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (τ : ℝ) (hτ : 0 ≤ τ)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    entryNorm (haarThresholdFlat d M τ UV) ≤ τ :=
  thresholdFlat_entryNorm_le τ hτ _

theorem sq_indicator_gt_le_moment_div
    (p : ℕ) (hp : 0 < p) (τ x : ℝ)
    (hτ : 0 < τ) (hx : 0 ≤ x) :
    (if τ < x then x ^ 2 else 0) ≤
      x ^ (2 * p) / τ ^ (2 * p - 2) := by
  by_cases h : τ < x
  · simp only [h, if_true]
    have hexp : 2 + (2 * p - 2) = 2 * p := by omega
    have hpow :
        τ ^ (2 * p - 2) ≤ x ^ (2 * p - 2) :=
      pow_le_pow_left₀ hτ.le h.le _
    have hden : 0 < τ ^ (2 * p - 2) :=
      pow_pos hτ _
    apply (le_div_iff₀ hden).2
    calc
      x ^ 2 * τ ^ (2 * p - 2) ≤
          x ^ 2 * x ^ (2 * p - 2) :=
        mul_le_mul_of_nonneg_left hpow (sq_nonneg x)
      _ = x ^ (2 * p) := by rw [← pow_add, hexp]
  · simp only [h, if_false]
    exact div_nonneg (pow_nonneg hx _) (pow_nonneg hτ.le _)

def scalarTailEnergy
    {α E : Type*} [Norm E]
    (τ : ℝ) (f : α → E) (x : α) : ℝ :=
  if τ < ‖f x‖ then ‖f x‖ ^ 2 else 0

theorem measurable_scalarTailEnergy
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (τ : ℝ) (f : α → E) (hf : Measurable f) :
    Measurable (scalarTailEnergy τ f) := by
  unfold scalarTailEnergy
  exact (hf.norm.pow_const 2).ite
    (measurableSet_lt measurable_const hf.norm) measurable_const

theorem integrable_scalarTailEnergy
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure α) (p : ℕ) (hp : 0 < p)
    (τ : ℝ) (hτ : 0 < τ) (f : α → E)
    (hf : Measurable f)
    (hint : Integrable (fun x => ‖f x‖ ^ (2 * p)) μ) :
    Integrable (scalarTailEnergy τ f) μ := by
  have hupper :
      Integrable
        (fun x => ‖f x‖ ^ (2 * p) /
          τ ^ (2 * p - 2)) μ :=
    hint.div_const _
  apply Integrable.mono' hupper
    (measurable_scalarTailEnergy τ f hf).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact sq_indicator_gt_le_moment_div
      p hp τ ‖f x‖ hτ (norm_nonneg _)
  · unfold scalarTailEnergy
    split_ifs
    · positivity
    · exact le_rfl

theorem scalarTailEnergy_integral_le
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure α) (p : ℕ) (hp : 0 < p)
    (τ : ℝ) (hτ : 0 < τ) (f : α → E)
    (hf : Measurable f)
    (hint : Integrable (fun x => ‖f x‖ ^ (2 * p)) μ) :
    (∫ x, scalarTailEnergy τ f x ∂μ) ≤
      (∫ x, ‖f x‖ ^ (2 * p) ∂μ) /
        τ ^ (2 * p - 2) := by
  have hden : 0 < τ ^ (2 * p - 2) := pow_pos hτ _
  have hupper :
      Integrable
        (fun x => ‖f x‖ ^ (2 * p) /
          τ ^ (2 * p - 2)) μ :=
    hint.div_const _
  have htail :=
    integrable_scalarTailEnergy μ p hp τ hτ f hf hint
  calc
    (∫ x, scalarTailEnergy τ f x ∂μ) ≤
        ∫ x, ‖f x‖ ^ (2 * p) /
          τ ^ (2 * p - 2) ∂μ := by
      apply integral_mono htail hupper
      intro x
      exact sq_indicator_gt_le_moment_div
        p hp τ ‖f x‖ hτ (norm_nonneg _)
    _ = (∫ x, ‖f x‖ ^ (2 * p) ∂μ) /
          τ ^ (2 * p - 2) := by
      rw [integral_div]

theorem integral_norm_pow_eq_lpNorm_pow
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure α) (n : ℕ) (hn : 0 < n)
    (f : α → E) (hf : Measurable f) :
    (∫ x, ‖f x‖ ^ n ∂μ) =
      lpNorm f (n : ℝ≥0∞) μ ^ n := by
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (by simp [hn.ne']) (by simp) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
  have hnonneg :
      0 ≤ ∫ x, ‖f x‖ ^ n ∂μ :=
    integral_nonneg fun x => pow_nonneg (norm_nonneg _) _
  exact (Real.rpow_inv_natCast_pow hnonneg hn.ne').symm

theorem integral_norm_pow_le_of_lpNorm_le
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure α) (n : ℕ) (hn : 0 < n)
    (f : α → E) (hf : Measurable f)
    (B : ℝ) (_hB : 0 ≤ B)
    (hlp : lpNorm f (n : ℝ≥0∞) μ ≤ B) :
    (∫ x, ‖f x‖ ^ n ∂μ) ≤ B ^ n := by
  rw [integral_norm_pow_eq_lpNorm_pow μ n hn f hf]
  exact pow_le_pow_left₀ lpNorm_nonneg hlp n

theorem integrable_norm_bipartiteHaarEntry_pow
    (d q : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (a b c e : Fin d) :
    Integrable
      (fun UV =>
        ‖bipartiteHaarEntry d M a b c e UV‖ ^ q)
      ((unitaryHaarMeasure d).prod
        (unitaryHaarMeasure d)) := by
  apply
    (integrable_norm_twoPartyHaarVector_pow
      d q M a b c e).congr
  filter_upwards with UV
  rw [norm_twoPartyHaarVector_eq_norm_bipartiteHaarEntry
    d M hzero0 hzero1 a b c e UV]

def manuscriptHaarMomentBound
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (p : ℕ) : ℝ :=
  (256 * hc.constant ^ 2 * (p : ℝ) ^ 2 /
      (d : ℝ) ^ 2) *
    (frobeniusSq M ^ ((2 : ℝ)⁻¹))

def flatMomentConstant
    (hc : GaussianHypercontractivityContract) : ℝ :=
  1 + 256 * hc.constant ^ 2

def flatMomentScale
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (p : ℕ) : ℝ :=
  flatMomentConstant hc * (p : ℝ) ^ 2 /
      (d : ℝ) ^ 2 * frobeniusNorm M

def flatThreshold
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (p : ℕ) : ℝ :=
  8 * flatMomentScale hc d M p

theorem flatMomentConstant_pos
    (hc : GaussianHypercontractivityContract) :
    0 < flatMomentConstant hc := by
  unfold flatMomentConstant
  positivity

theorem flatMomentScale_pos
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d)) (hM0 : M ≠ 0)
    (p : ℕ) (hp : 0 < p) :
    0 < flatMomentScale hc d M p := by
  have hFsq : 0 < frobeniusSq M := by
    exact lt_of_le_of_ne (frobeniusSq_nonneg M)
      (Ne.symm (mt (frobeniusSq_eq_zero_iff M).mp hM0))
  unfold flatMomentScale frobeniusNorm
  exact mul_pos
    (div_pos
      (mul_pos (flatMomentConstant_pos hc)
        (sq_pos_of_pos (by exact_mod_cast hp)))
      (sq_pos_of_pos (by exact_mod_cast hd)))
    (Real.sqrt_pos.2 hFsq)

theorem flatThreshold_pos
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d)) (hM0 : M ≠ 0)
    (p : ℕ) (hp : 0 < p) :
    0 < flatThreshold hc d M p := by
  unfold flatThreshold
  exact mul_pos (by norm_num)
    (flatMomentScale_pos hc d hd M hM0 p hp)

theorem manuscriptHaarMomentBound_le_flatMomentScale
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (p : ℕ) :
    manuscriptHaarMomentBound hc d M p ≤
      flatMomentScale hc d M p := by
  have hcoef :
      256 * hc.constant ^ 2 ≤ flatMomentConstant hc := by
    unfold flatMomentConstant
    linarith
  unfold manuscriptHaarMomentBound flatMomentScale
  have hhalf : (2 : ℝ)⁻¹ = 1 / (2 : ℝ) := by ring
  rw [hhalf, ← Real.sqrt_eq_rpow]
  have hrest :
      0 ≤ (p : ℝ) ^ 2 / (d : ℝ) ^ 2 * √(frobeniusSq M) := by
    positivity
  calc
    (256 * hc.constant ^ 2 * (p : ℝ) ^ 2 /
        (d : ℝ) ^ 2) * √(frobeniusSq M) =
      (256 * hc.constant ^ 2) *
        ((p : ℝ) ^ 2 / (d : ℝ) ^ 2 *
          √(frobeniusSq M)) := by ring
    _ ≤ flatMomentConstant hc *
        ((p : ℝ) ^ 2 / (d : ℝ) ^ 2 *
          √(frobeniusSq M)) :=
      mul_le_mul_of_nonneg_right hcoef hrest
    _ = flatMomentConstant hc * (p : ℝ) ^ 2 /
        (d : ℝ) ^ 2 * √(frobeniusSq M) := by ring

theorem pow_div_mul_pow_sub_two
    (x : ℝ) (hx : x ≠ 0)
    (p : ℕ) (hp : 0 < p) :
    x ^ (2 * p) / (8 * x) ^ (2 * p - 2) =
      x ^ 2 / 8 ^ (2 * p - 2) := by
  have hexp : (2 * p - 2) + 2 = 2 * p := by omega
  have hnum :
      x ^ (2 * p) = x ^ (2 * p - 2) * x ^ 2 := by
    rw [← pow_add, hexp]
  rw [hnum, mul_pow]
  field_simp [pow_ne_zero _ hx]

theorem inv_eight_pow_sub_two
    (p : ℕ) (hp : 0 < p) :
    1 / (8 : ℝ) ^ (2 * p - 2) =
      64 / (8 : ℝ) ^ (2 * p) := by
  have hexp : (2 * p - 2) + 2 = 2 * p := by omega
  rw [← hexp, pow_add]
  norm_num
  field_simp

theorem dimension_mul_flatMomentScale_sq
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (p : ℕ) :
    (d : ℝ) ^ 4 * flatMomentScale hc d M p ^ 2 =
      flatMomentConstant hc ^ 2 * (p : ℝ) ^ 4 *
        frobeniusSq M := by
  unfold flatMomentScale frobeniusNorm
  simp only [mul_pow, div_pow]
  rw [Real.sq_sqrt (frobeniusSq_nonneg M)]
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  field_simp [hd0]

theorem flatThreshold_expectedTailBound
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d)) (hM0 : M ≠ 0)
    (p : ℕ) (hp : 0 < p)
    (δ : ℝ)
    (hdecay :
      64 * flatMomentConstant hc ^ 2 * (p : ℝ) ^ 4 /
          (8 : ℝ) ^ (2 * p) ≤ δ ^ 4) :
    (d : ℝ) ^ 4 *
        (manuscriptHaarMomentBound hc d M p ^ (2 * p) /
          flatThreshold hc d M p ^ (2 * p - 2)) ≤
      δ ^ 4 * frobeniusSq M := by
  let S := flatMomentScale hc d M p
  have hS : 0 < S :=
    flatMomentScale_pos hc d hd M hM0 p hp
  have hmomentNonneg :
      0 ≤ manuscriptHaarMomentBound hc d M p := by
    unfold manuscriptHaarMomentBound
    apply mul_nonneg
    · exact div_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (sq_nonneg hc.constant))
          (sq_nonneg (p : ℝ)))
        (sq_nonneg (d : ℝ))
    · exact Real.rpow_nonneg (frobeniusSq_nonneg M) _
  have hmoment :
      manuscriptHaarMomentBound hc d M p ^ (2 * p) ≤
        S ^ (2 * p) :=
    pow_le_pow_left₀
      hmomentNonneg
      (manuscriptHaarMomentBound_le_flatMomentScale hc d M p)
      _
  calc
    (d : ℝ) ^ 4 *
        (manuscriptHaarMomentBound hc d M p ^ (2 * p) /
          flatThreshold hc d M p ^ (2 * p - 2)) ≤
      (d : ℝ) ^ 4 *
        (S ^ (2 * p) /
          flatThreshold hc d M p ^ (2 * p - 2)) := by
      gcongr
      exact pow_nonneg
        (flatThreshold_pos hc d hd M hM0 p hp).le _
    _ = (d : ℝ) ^ 4 *
        (S ^ 2 / (8 : ℝ) ^ (2 * p - 2)) := by
      unfold flatThreshold
      change _ * (S ^ (2 * p) / (8 * S) ^ (2 * p - 2)) = _
      rw [pow_div_mul_pow_sub_two S hS.ne' p hp]
    _ = ((d : ℝ) ^ 4 * S ^ 2) *
        (1 / (8 : ℝ) ^ (2 * p - 2)) := by ring
    _ = (flatMomentConstant hc ^ 2 * (p : ℝ) ^ 4 *
          frobeniusSq M) *
        (1 / (8 : ℝ) ^ (2 * p - 2)) := by
      rw [show (d : ℝ) ^ 4 * S ^ 2 =
        flatMomentConstant hc ^ 2 * (p : ℝ) ^ 4 *
          frobeniusSq M by
        exact dimension_mul_flatMomentScale_sq hc d hd M p]
    _ = (64 * flatMomentConstant hc ^ 2 * (p : ℝ) ^ 4 /
          (8 : ℝ) ^ (2 * p)) * frobeniusSq M := by
      rw [inv_eight_pow_sub_two p hp]
      ring
    _ ≤ δ ^ 4 * frobeniusSq M :=
      mul_le_mul_of_nonneg_right hdecay (frobeniusSq_nonneg M)

theorem manuscriptHaarMomentBound_nonneg
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (p : ℕ) :
    0 ≤ manuscriptHaarMomentBound hc d M p := by
  unfold manuscriptHaarMomentBound
  apply mul_nonneg
  · exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg hc.constant))
        (sq_nonneg (p : ℝ)))
      (sq_nonneg (d : ℝ))
  · exact Real.rpow_nonneg (frobeniusSq_nonneg M) _

theorem integral_bipartiteHaarEntry_pow_le
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (a b c e : Fin d)
    (p : ℕ) (hp : 0 < p) (height : 8 * p ≤ d) :
    (∫ UV,
      ‖bipartiteHaarEntry d M a b c e UV‖ ^ (2 * p)
      ∂((unitaryHaarMeasure d).prod
        (unitaryHaarMeasure d))) ≤
      manuscriptHaarMomentBound hc d M p ^ (2 * p) := by
  apply integral_norm_pow_le_of_lpNorm_le
    _ (2 * p) (by omega) _ 
    (measurable_bipartiteHaarEntry
      d M hzero0 hzero1 a b c e)
    _ (manuscriptHaarMomentBound_nonneg hc d M p)
  exact twoPartyHaar_manuscript_moment_le
    hc d M hzero0 hzero1 a b c e p hp height

theorem integral_bipartiteHaarEntry_tail_le
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (a b c e : Fin d)
    (p : ℕ) (hp : 0 < p) (height : 8 * p ≤ d)
    (τ : ℝ) (hτ : 0 < τ) :
    (∫ UV,
      scalarTailEnergy τ
        (bipartiteHaarEntry d M a b c e) UV
      ∂((unitaryHaarMeasure d).prod
        (unitaryHaarMeasure d))) ≤
      manuscriptHaarMomentBound hc d M p ^ (2 * p) /
        τ ^ (2 * p - 2) := by
  let μ :=
    (unitaryHaarMeasure d).prod (unitaryHaarMeasure d)
  have hbase :=
    scalarTailEnergy_integral_le μ p hp τ hτ
      (bipartiteHaarEntry d M a b c e)
      (measurable_bipartiteHaarEntry
        d M hzero0 hzero1 a b c e)
      (integrable_norm_bipartiteHaarEntry_pow
        d (2 * p) M hzero0 hzero1 a b c e)
  calc
    (∫ UV,
      scalarTailEnergy τ
        (bipartiteHaarEntry d M a b c e) UV ∂μ) ≤
        (∫ UV,
          ‖bipartiteHaarEntry d M a b c e UV‖ ^ (2 * p)
          ∂μ) / τ ^ (2 * p - 2) := hbase
    _ ≤ manuscriptHaarMomentBound hc d M p ^ (2 * p) /
          τ ^ (2 * p - 2) := by
      exact div_le_div_of_nonneg_right
        (integral_bipartiteHaarEntry_pow_le
          hc d M hzero0 hzero1 a b c e p hp height)
        (pow_nonneg hτ.le _)

theorem frobeniusSq_haarThresholdTail
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (τ : ℝ)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    frobeniusSq (haarThresholdTail d M τ UV) =
      ∑ ac : Fin d × Fin d, ∑ be : Fin d × Fin d,
        scalarTailEnergy τ
          (bipartiteHaarEntry d M ac.1 be.1 ac.2 be.2) UV := by
  unfold frobeniusSq haarThresholdTail thresholdTail
  apply Finset.sum_congr rfl
  intro ac _
  apply Finset.sum_congr rfl
  intro be _
  unfold scalarTailEnergy
  rw [bipartiteHaarEntry_eq_unitaryConjugate_apply]
  simp only [Prod.eta]
  by_cases h :
      τ < ‖bipartiteUnitaryConjugate d M UV ac be‖
  · simp [h, Complex.normSq_eq_norm_sq]
  · simp [h, Complex.normSq_eq_norm_sq]

theorem integrable_frobeniusSq_haarThresholdTail
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (p : ℕ) (hp : 0 < p)
    (τ : ℝ) (hτ : 0 < τ) :
    Integrable
      (fun UV => frobeniusSq (haarThresholdTail d M τ UV))
      ((unitaryHaarMeasure d).prod
        (unitaryHaarMeasure d)) := by
  rw [show
    (fun UV => frobeniusSq (haarThresholdTail d M τ UV)) =
      fun UV =>
        ∑ ac : Fin d × Fin d, ∑ be : Fin d × Fin d,
          scalarTailEnergy τ
            (bipartiteHaarEntry
              d M ac.1 be.1 ac.2 be.2) UV by
    funext UV
    exact frobeniusSq_haarThresholdTail d M τ UV]
  apply integrable_finsetSum
  intro ac _
  apply integrable_finsetSum
  intro be _
  exact integrable_scalarTailEnergy
    ((unitaryHaarMeasure d).prod (unitaryHaarMeasure d))
    p hp τ hτ
    (bipartiteHaarEntry d M ac.1 be.1 ac.2 be.2)
    (measurable_bipartiteHaarEntry
      d M hzero0 hzero1 ac.1 be.1 ac.2 be.2)
    (integrable_norm_bipartiteHaarEntry_pow
      d (2 * p) M hzero0 hzero1 ac.1 be.1 ac.2 be.2)

theorem measurable_frobeniusSq_haarThresholdTail
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (τ : ℝ) :
    Measurable
      (fun UV => frobeniusSq (haarThresholdTail d M τ UV)) := by
  rw [show
    (fun UV => frobeniusSq (haarThresholdTail d M τ UV)) =
      fun UV =>
        ∑ ac : Fin d × Fin d, ∑ be : Fin d × Fin d,
          scalarTailEnergy τ
            (bipartiteHaarEntry
              d M ac.1 be.1 ac.2 be.2) UV by
    funext UV
    exact frobeniusSq_haarThresholdTail d M τ UV]
  apply Finset.measurable_sum
  intro ac _
  apply Finset.measurable_sum
  intro be _
  exact measurable_scalarTailEnergy τ _
    (measurable_bipartiteHaarEntry
      d M hzero0 hzero1 ac.1 be.1 ac.2 be.2)

theorem integral_frobeniusSq_haarThresholdTail_le
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (p : ℕ) (hp : 0 < p) (height : 8 * p ≤ d)
    (τ : ℝ) (hτ : 0 < τ) :
    (∫ UV, frobeniusSq (haarThresholdTail d M τ UV)
      ∂((unitaryHaarMeasure d).prod
        (unitaryHaarMeasure d))) ≤
      (d : ℝ) ^ 4 *
        (manuscriptHaarMomentBound hc d M p ^ (2 * p) /
          τ ^ (2 * p - 2)) := by
  let μ :=
    (unitaryHaarMeasure d).prod (unitaryHaarMeasure d)
  have hentry (ac be : Fin d × Fin d) :
      (∫ UV,
        scalarTailEnergy τ
          (bipartiteHaarEntry d M ac.1 be.1 ac.2 be.2) UV
        ∂μ) ≤
        manuscriptHaarMomentBound hc d M p ^ (2 * p) /
          τ ^ (2 * p - 2) :=
    integral_bipartiteHaarEntry_tail_le
      hc d M hzero0 hzero1 ac.1 be.1 ac.2 be.2
      p hp height τ hτ
  have htail (ac be : Fin d × Fin d) :
      Integrable
        (scalarTailEnergy τ
          (bipartiteHaarEntry d M ac.1 be.1 ac.2 be.2)) μ :=
    integrable_scalarTailEnergy μ p hp τ hτ
      (bipartiteHaarEntry d M ac.1 be.1 ac.2 be.2)
      (measurable_bipartiteHaarEntry
        d M hzero0 hzero1 ac.1 be.1 ac.2 be.2)
      (integrable_norm_bipartiteHaarEntry_pow
        d (2 * p) M hzero0 hzero1 ac.1 be.1 ac.2 be.2)
  calc
    (∫ UV, frobeniusSq (haarThresholdTail d M τ UV) ∂μ) =
        ∑ ac : Fin d × Fin d, ∑ be : Fin d × Fin d,
          ∫ UV,
            scalarTailEnergy τ
              (bipartiteHaarEntry
                d M ac.1 be.1 ac.2 be.2) UV ∂μ := by
      rw [show
        (fun UV => frobeniusSq (haarThresholdTail d M τ UV)) =
          fun UV =>
            ∑ ac : Fin d × Fin d, ∑ be : Fin d × Fin d,
              scalarTailEnergy τ
                (bipartiteHaarEntry
                  d M ac.1 be.1 ac.2 be.2) UV by
        funext UV
        exact frobeniusSq_haarThresholdTail d M τ UV]
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro ac _
        rw [integral_finsetSum]
        intro be _
        exact htail ac be
      · intro ac _
        exact integrable_finsetSum _ fun be _ => htail ac be
    _ ≤ ∑ ac : Fin d × Fin d, ∑ be : Fin d × Fin d,
          (manuscriptHaarMomentBound hc d M p ^ (2 * p) /
            τ ^ (2 * p - 2)) := by
      gcongr with ac be
      exact hentry ac be
    _ = (d : ℝ) ^ 4 *
        (manuscriptHaarMomentBound hc d M p ^ (2 * p) /
          τ ^ (2 * p - 2)) := by
      simp [Finset.sum_const, Fintype.card_prod, nsmul_eq_mul]
      ring

theorem haarThresholdTail_failure_measureReal_le
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (p : ℕ) (hp : 0 < p) (height : 8 * p ≤ d)
    (τ : ℝ) (hτ : 0 < τ)
    (s : ℝ) (hs : 0 < s) :
    ((unitaryHaarMeasure d).prod
      (unitaryHaarMeasure d)).real
        {UV | s ≤ frobeniusSq (haarThresholdTail d M τ UV)} ≤
      ((d : ℝ) ^ 4 *
        (manuscriptHaarMomentBound hc d M p ^ (2 * p) /
          τ ^ (2 * p - 2))) / s := by
  let μ :=
    (unitaryHaarMeasure d).prod (unitaryHaarMeasure d)
  let F := fun UV => frobeniusSq (haarThresholdTail d M τ UV)
  have hF_nonneg : 0 ≤ᵐ[μ] F :=
    Filter.Eventually.of_forall fun UV =>
      frobeniusSq_nonneg (haarThresholdTail d M τ UV)
  have hF_int : Integrable F μ :=
    integrable_frobeniusSq_haarThresholdTail
      d M hzero0 hzero1 p hp τ hτ
  have hmarkov :=
    mul_meas_ge_le_integral_of_nonneg hF_nonneg hF_int s
  apply (le_div_iff₀ hs).2
  calc
    μ.real {UV | s ≤ F UV} * s =
        s * μ.real {UV | s ≤ F UV} := by ring
    _ ≤ ∫ UV, F UV ∂μ := hmarkov
    _ ≤ (d : ℝ) ^ 4 *
        (manuscriptHaarMomentBound hc d M p ^ (2 * p) /
          τ ^ (2 * p - 2)) :=
      integral_frobeniusSq_haarThresholdTail_le
        hc d M hzero0 hzero1 p hp height τ hτ

theorem haarThresholdTail_failure_measureReal_le_of_expectation
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (p : ℕ) (hp : 0 < p) (height : 8 * p ≤ d)
    (τ : ℝ) (hτ : 0 < τ)
    (s ρ : ℝ) (hs : 0 < s) (_hρ : 0 ≤ ρ)
    (hexpect :
      (d : ℝ) ^ 4 *
        (manuscriptHaarMomentBound hc d M p ^ (2 * p) /
          τ ^ (2 * p - 2)) ≤ ρ * s) :
    ((unitaryHaarMeasure d).prod
      (unitaryHaarMeasure d)).real
        {UV | s ≤ frobeniusSq (haarThresholdTail d M τ UV)} ≤ ρ := by
  calc
    _ ≤ ((d : ℝ) ^ 4 *
        (manuscriptHaarMomentBound hc d M p ^ (2 * p) /
          τ ^ (2 * p - 2))) / s :=
      haarThresholdTail_failure_measureReal_le
        hc d M hzero0 hzero1 p hp height τ hτ s hs
    _ ≤ (ρ * s) / s :=
      div_le_div_of_nonneg_right hexpect hs.le
    _ = ρ := by field_simp [hs.ne']

def HaarFlatTailGood
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (τ s : ℝ)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) : Prop :=
  haarThresholdFlat d M τ UV +
      haarThresholdTail d M τ UV =
        bipartiteUnitaryConjugate d M UV ∧
  (haarThresholdFlat d M τ UV).IsHermitian ∧
  (haarThresholdTail d M τ UV).IsHermitian ∧
  entryNorm (haarThresholdFlat d M τ UV) ≤ τ ∧
  frobeniusSq (haarThresholdTail d M τ UV) < s

def HaarFlatTailConclusion
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (τ δ : ℝ)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) : Prop :=
  haarThresholdFlat d M τ UV +
      haarThresholdTail d M τ UV =
        bipartiteUnitaryConjugate d M UV ∧
  (haarThresholdFlat d M τ UV).IsHermitian ∧
  (haarThresholdTail d M τ UV).IsHermitian ∧
  entryNorm (haarThresholdFlat d M τ UV) ≤ τ ∧
  frobeniusNorm (haarThresholdTail d M τ UV) ≤
    δ * frobeniusNorm M

/-- The canonical flat/tail good event is measurable.  Its first four
conjuncts hold deterministically, so it is exactly the strict sublevel event
for the tail Frobenius square. -/
theorem measurableSet_haarFlatTailGood
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian)
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (τ : ℝ) (hτ : 0 ≤ τ) (s : ℝ) :
    MeasurableSet {UV | HaarFlatTailGood d M τ s UV} := by
  have heq :
      {UV | HaarFlatTailGood d M τ s UV} =
        {UV | frobeniusSq (haarThresholdTail d M τ UV) < s} := by
    ext UV
    constructor
    · intro h
      exact h.2.2.2.2
    · intro h
      exact ⟨haarThreshold_decomposition d M τ UV,
        haarThresholdFlat_isHermitian d M hM τ UV,
        haarThresholdTail_isHermitian d M hM τ UV,
        haarThresholdFlat_entryNorm_le d M τ hτ UV, h⟩
  rw [heq]
  exact measurableSet_lt
    (measurable_frobeniusSq_haarThresholdTail
      d M hzero0 hzero1 τ) measurable_const

/-- The canonical non-strict flat/tail conclusion is measurable.  This is
the event used by the algorithm, including the degenerate zero-matrix case
where the strict square-tail event would be empty. -/
theorem measurableSet_haarFlatTailConclusion
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian)
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (τ : ℝ) (hτ : 0 ≤ τ) (δ : ℝ) :
    MeasurableSet {UV | HaarFlatTailConclusion d M τ δ UV} := by
  have heq :
      {UV | HaarFlatTailConclusion d M τ δ UV} =
        {UV | frobeniusNorm (haarThresholdTail d M τ UV) ≤
          δ * frobeniusNorm M} := by
    ext UV
    constructor
    · intro h
      exact h.2.2.2.2
    · intro h
      exact ⟨haarThreshold_decomposition d M τ UV,
        haarThresholdFlat_isHermitian d M hM τ UV,
        haarThresholdTail_isHermitian d M hM τ UV,
        haarThresholdFlat_entryNorm_le d M τ hτ UV, h⟩
  rw [heq]
  exact measurableSet_le
    ((measurable_frobeniusSq_haarThresholdTail
      d M hzero0 hzero1 τ).sqrt) measurable_const

def FlatTailDecomposition
    {ι : Type*} [Fintype ι]
    (A reference flat tail : CMatrix ι)
    (γ δ : ℝ) : Prop :=
  flat + tail = A ∧
  flat.IsHermitian ∧
  tail.IsHermitian ∧
  entryNorm flat ≤ γ ∧
  frobeniusNorm tail ≤ δ * frobeniusNorm reference

theorem haarFlatTailConclusion_iff_decomposition
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (τ δ : ℝ)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    HaarFlatTailConclusion d M τ δ UV ↔
      FlatTailDecomposition
        (bipartiteUnitaryConjugate d M UV) M
        (haarThresholdFlat d M τ UV)
        (haarThresholdTail d M τ UV) τ δ :=
  Iff.rfl

theorem exists_flatTailDecomposition_of_gamma_ge
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ)
    (γ δ : ℝ) (hγ : frobeniusNorm M ≤ γ)
    (hδ : 0 ≤ δ) :
    ∃ flat tail,
      FlatTailDecomposition
        (bipartiteUnitaryConjugate d M UV) M
        flat tail γ δ := by
  refine ⟨bipartiteUnitaryConjugate d M UV, 0,
    add_zero _, bipartiteUnitaryConjugate_isHermitian d M hM UV,
    Matrix.isHermitian_zero, ?_, ?_⟩
  · exact (entryNorm_le_frobeniusNorm _).trans
      ((frobeniusNorm_bipartiteUnitaryConjugate d M UV).le.trans hγ)
  · unfold frobeniusNorm frobeniusSq
    simp
    exact mul_nonneg hδ (Real.sqrt_nonneg _)

theorem haarFlatTailGood_measureReal_ge
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian)
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (p : ℕ) (hp : 0 < p) (height : 8 * p ≤ d)
    (τ : ℝ) (hτ : 0 < τ)
    (s ρ : ℝ) (hs : 0 < s) (hρ : 0 ≤ ρ)
    (hexpect :
      (d : ℝ) ^ 4 *
        (manuscriptHaarMomentBound hc d M p ^ (2 * p) /
          τ ^ (2 * p - 2)) ≤ ρ * s) :
    ((unitaryHaarMeasure d).prod
      (unitaryHaarMeasure d)).real
        {UV | HaarFlatTailGood d M τ s UV} ≥ 1 - ρ := by
  let μ :=
    (unitaryHaarMeasure d).prod (unitaryHaarMeasure d)
  let failure : Set
      (Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :=
    {UV | s ≤ frobeniusSq (haarThresholdTail d M τ UV)}
  have hfailure : μ.real failure ≤ ρ :=
    haarThresholdTail_failure_measureReal_le_of_expectation
      hc d M hzero0 hzero1 p hp height τ hτ
      s ρ hs hρ hexpect
  have hfailureMeas : MeasurableSet failure := by
    exact measurableSet_le measurable_const
      (measurable_frobeniusSq_haarThresholdTail
        d M hzero0 hzero1 τ)
  have hgood :
      {UV | HaarFlatTailGood d M τ s UV} = failureᶜ := by
    ext UV
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff,
      HaarFlatTailGood, failure]
    constructor
    · intro hgood hfail
      exact (not_le_of_gt hgood.2.2.2.2) hfail
    · intro hgood
      refine ⟨haarThreshold_decomposition d M τ UV,
        haarThresholdFlat_isHermitian d M hM τ UV,
        haarThresholdTail_isHermitian d M hM τ UV,
        haarThresholdFlat_entryNorm_le d M τ hτ.le UV, ?_⟩
      exact lt_of_not_ge hgood
  rw [hgood, measureReal_compl hfailureMeas, probReal_univ]
  linarith

theorem haarFlatTailConclusion_measureReal_ge
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian) (hM0 : M ≠ 0)
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (p : ℕ) (hp : 0 < p) (height : 8 * p ≤ d)
    (τ : ℝ) (hτ : 0 < τ)
    (δ : ℝ) (hδ : 0 < δ)
    (hexpect :
      (d : ℝ) ^ 4 *
        (manuscriptHaarMomentBound hc d M p ^ (2 * p) /
          τ ^ (2 * p - 2)) ≤
        δ ^ 2 * (δ ^ 2 * frobeniusSq M)) :
    ((unitaryHaarMeasure d).prod
      (unitaryHaarMeasure d)).real
        {UV | HaarFlatTailConclusion d M τ δ UV} ≥
      1 - δ ^ 2 := by
  let μ :=
    (unitaryHaarMeasure d).prod (unitaryHaarMeasure d)
  let s := δ ^ 2 * frobeniusSq M
  have hMsq : 0 < frobeniusSq M := by
    exact lt_of_le_of_ne (frobeniusSq_nonneg M)
      (Ne.symm (mt (frobeniusSq_eq_zero_iff M).mp hM0))
  have hs : 0 < s := mul_pos (sq_pos_of_pos hδ) hMsq
  have hsqGood :
      μ.real {UV | HaarFlatTailGood d M τ s UV} ≥
        1 - δ ^ 2 :=
    haarFlatTailGood_measureReal_ge
      hc d M hM hzero0 hzero1 p hp height τ hτ
      s (δ ^ 2) hs (sq_nonneg δ) hexpect
  have hsubset :
      {UV | HaarFlatTailGood d M τ s UV} ⊆
        {UV | HaarFlatTailConclusion d M τ δ UV} := by
    intro UV hgood
    refine ⟨hgood.1, hgood.2.1, hgood.2.2.1,
      hgood.2.2.2.1, ?_⟩
    exact (frobeniusNorm_lt_mul_of_frobeniusSq_lt
      (haarThresholdTail d M τ UV) M δ hδ hgood.2.2.2.2).le
  exact hsqGood.trans (measureReal_mono hsubset)

theorem exists_flatTailDecomposition_measureReal_ge
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian) (hM0 : M ≠ 0)
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (p : ℕ) (hp : 0 < p) (height : 8 * p ≤ d)
    (τ : ℝ) (hτ : 0 < τ)
    (δ : ℝ) (hδ : 0 < δ)
    (hexpect :
      (d : ℝ) ^ 4 *
        (manuscriptHaarMomentBound hc d M p ^ (2 * p) /
          τ ^ (2 * p - 2)) ≤
        δ ^ 2 * (δ ^ 2 * frobeniusSq M)) :
    ((unitaryHaarMeasure d).prod
      (unitaryHaarMeasure d)).real
        {UV | ∃ flat tail,
          FlatTailDecomposition
            (bipartiteUnitaryConjugate d M UV) M
            flat tail τ δ} ≥
      1 - δ ^ 2 := by
  have hthreshold :=
    haarFlatTailConclusion_measureReal_ge
      hc d M hM hM0 hzero0 hzero1 p hp height
      τ hτ δ hδ hexpect
  have hsubset :
      {UV | HaarFlatTailConclusion d M τ δ UV} ⊆
        {UV | ∃ flat tail,
          FlatTailDecomposition
            (bipartiteUnitaryConjugate d M UV) M
            flat tail τ δ} := by
    intro UV hUV
    exact ⟨haarThresholdFlat d M τ UV,
      haarThresholdTail d M τ UV,
      (haarFlatTailConclusion_iff_decomposition d M τ δ UV).mp hUV⟩
  exact hthreshold.trans
    (measureReal_mono hsubset (measure_ne_top _ _))

theorem exists_flatTailDecomposition_at_flatThreshold
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian) (hM0 : M ≠ 0)
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (p : ℕ) (hp : 0 < p) (height : 8 * p ≤ d)
    (δ : ℝ) (hδ : 0 < δ)
    (hdecay :
      64 * flatMomentConstant hc ^ 2 * (p : ℝ) ^ 4 /
          (8 : ℝ) ^ (2 * p) ≤ δ ^ 4) :
    ((unitaryHaarMeasure d).prod
      (unitaryHaarMeasure d)).real
        {UV | ∃ flat tail,
          FlatTailDecomposition
            (bipartiteUnitaryConjugate d M UV) M
            flat tail (flatThreshold hc d M p) δ} ≥
      1 - δ ^ 2 := by
  have hd : 0 < d := by omega
  apply exists_flatTailDecomposition_measureReal_ge
    hc d M hM hM0 hzero0 hzero1 p hp height
    (flatThreshold hc d M p)
    (flatThreshold_pos hc d hd M hM0 p hp)
    δ hδ
  convert flatThreshold_expectedTailBound
    hc d hd M hM0 p hp δ hdecay using 1
  ring

theorem exists_flatDecayInteger
    (C : ℝ) :
    ∃ m : ℕ, 4 ≤ m ∧
      64 * C ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 4 /
          (64 : ℝ) ^ m ≤ 1 := by
  have htend :
      Tendsto
        (fun m : ℕ =>
          1024 * C ^ 2 * (m : ℝ) ^ 4 / (64 : ℝ) ^ m)
        atTop (nhds 0) := by
    have hconst :
        Tendsto (fun _ : ℕ => 1024 * C ^ 2)
          atTop (nhds (1024 * C ^ 2)) :=
      tendsto_const_nhds
    have hbase :=
      tendsto_pow_const_div_const_pow_of_one_lt
        4 (by norm_num : (1 : ℝ) < 64)
    convert hconst.mul hbase using 1
    · ext m
      ring
    · simp
  have hevent :
      ∀ᶠ m : ℕ in atTop,
        1024 * C ^ 2 * (m : ℝ) ^ 4 / (64 : ℝ) ^ m < 1 :=
    htend.eventually_lt_const zero_lt_one
  obtain ⟨m, hm4, hmdecay⟩ :
      ∃ m : ℕ, 4 ≤ m ∧
        1024 * C ^ 2 * (m : ℝ) ^ 4 / (64 : ℝ) ^ m < 1 := by
    exact ((eventually_ge_atTop 4).and hevent).exists
  refine ⟨m, hm4, ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (le_trans (by omega) hm4)
  have hadd : ((m + 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
    push_cast
    linarith
  have hpow :
      ((m + 1 : ℕ) : ℝ) ^ 4 ≤
        (2 * (m : ℝ)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hadd 4
  have hcoef : 0 ≤ 64 * C ^ 2 := by positivity
  calc
    64 * C ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 4 /
        (64 : ℝ) ^ m ≤
      64 * C ^ 2 * (2 * (m : ℝ)) ^ 4 /
        (64 : ℝ) ^ m := by
      gcongr
    _ = 1024 * C ^ 2 * (m : ℝ) ^ 4 /
        (64 : ℝ) ^ m := by ring
    _ ≤ 1 := hmdecay.le

theorem logarithmic_decay_aux
    (m : ℕ) (hm : 4 ≤ m)
    (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ 4 /
        (8 : ℝ) ^ (2 * (m : ℝ) * (1 + x)) ≤
      (1 / (8 : ℝ) ^ (2 * (m : ℝ))) *
        Real.exp (-4 * x) := by
  have hlog8 : 1 < Real.log 8 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 8)]
    exact Real.exp_one_lt_three.trans (by norm_num)
  let a : ℝ := 2 * (m : ℝ) * Real.log 8
  have ha : 8 ≤ a := by
    dsimp [a]
    have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hlinear :
      4 * x - a * (1 + x) ≤ -a - 4 * x := by
    nlinarith
  have hbase :
      1 + x ≤ Real.exp x :=
    by simpa [add_comm] using Real.add_one_le_exp x
  have hpow :
      (1 + x) ^ 4 ≤ (Real.exp x) ^ 4 :=
    pow_le_pow_left₀ (by linarith) hbase 4
  calc
    (1 + x) ^ 4 /
        (8 : ℝ) ^ (2 * (m : ℝ) * (1 + x)) =
      (1 + x) ^ 4 *
        Real.exp (-a * (1 + x)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 8)]
      dsimp [a]
      rw [div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring
    _ ≤ (Real.exp x) ^ 4 *
        Real.exp (-a * (1 + x)) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = Real.exp (4 * x - a * (1 + x)) := by
      rw [← Real.exp_nat_mul]
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-a - 4 * x) :=
      Real.exp_le_exp.mpr hlinear
    _ = Real.exp (-a) * Real.exp (-4 * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = (1 / (8 : ℝ) ^ (2 * (m : ℝ))) *
        Real.exp (-4 * x) := by
      rw [one_div,
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 8),
        ← Real.exp_neg]
      dsimp [a]
      congr 2
      ring

def flatMomentOrder
    (m : ℕ) (δ : ℝ) : ℕ :=
  ⌈(m : ℝ) * (1 + Real.log (1 / δ))⌉₊

theorem flatMomentOrder_bounds
    (m : ℕ) (hm : 0 < m)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < flatMomentOrder m δ ∧
    (m : ℝ) * (1 + Real.log (1 / δ)) ≤
      flatMomentOrder m δ ∧
    (flatMomentOrder m δ : ℝ) ≤
      (m + 1 : ℕ) * (1 + Real.log (1 / δ)) := by
  let x := Real.log (1 / δ)
  have hinv : 1 < 1 / δ := by
    exact (lt_div_iff₀ hδ).2 (by simpa using hδ1)
  have hx : 0 < x := by
    exact Real.log_pos hinv
  have hL : 1 ≤ 1 + x := by linarith
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have harg : 0 < (m : ℝ) * (1 + x) :=
    mul_pos hmR (lt_of_lt_of_le zero_lt_one hL)
  have hlower :
      (m : ℝ) * (1 + x) ≤
        (flatMomentOrder m δ : ℝ) := by
    exact Nat.le_ceil _
  have hceil :
      (flatMomentOrder m δ : ℝ) <
        (m : ℝ) * (1 + x) + 1 := by
    exact Nat.ceil_lt_add_one harg.le
  have hupper :
      (flatMomentOrder m δ : ℝ) ≤
        ((m + 1 : ℕ) : ℝ) * (1 + x) := by
    push_cast
    calc
      (flatMomentOrder m δ : ℝ) ≤
          (m : ℝ) * (1 + x) + 1 := hceil.le
      _ ≤ ((m : ℝ) + 1) * (1 + x) := by
        nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have : 0 < (flatMomentOrder m δ : ℝ) :=
      harg.trans_le hlower
    exact_mod_cast this
  · simpa [flatMomentOrder, x] using hlower
  · simpa [x] using hupper

theorem flatMomentOrder_dimension
    (m : ℕ) (hm : 0 < m)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (d : ℕ)
    (hd :
      8 * ((m + 1 : ℕ) : ℝ) *
          (1 + Real.log (1 / δ)) ≤ d) :
    8 * flatMomentOrder m δ ≤ d := by
  have hupper :=
    (flatMomentOrder_bounds m hm δ hδ hδ1).2.2
  exact_mod_cast
    (calc
      (8 : ℝ) * flatMomentOrder m δ ≤
          8 * (((m + 1 : ℕ) : ℝ) *
            (1 + Real.log (1 / δ))) := by gcongr
      _ = 8 * ((m + 1 : ℕ) : ℝ) *
          (1 + Real.log (1 / δ)) := by ring
      _ ≤ d := hd)

theorem exp_neg_four_log_inv
    (δ : ℝ) (hδ : 0 < δ) :
    Real.exp (-4 * Real.log (1 / δ)) = δ ^ 4 := by
  rw [one_div, Real.log_inv, mul_neg]
  have hneg :
      -(-4 * Real.log δ) = 4 * Real.log δ := by ring
  rw [hneg]
  calc
    Real.exp (4 * Real.log δ) =
        Real.exp (Real.log δ) ^ 4 := by
      rw [← Real.exp_nat_mul]
      congr 1
    _ = δ ^ 4 := by rw [Real.exp_log hδ]

theorem eight_rpow_two_nat
    (n : ℕ) :
    (8 : ℝ) ^ (2 * (n : ℝ)) =
      (8 : ℝ) ^ (2 * n) := by
  rw [← Real.rpow_natCast]
  congr 1
  push_cast
  ring

theorem eight_rpow_two_nat_eq_sixtyFour_pow
    (n : ℕ) :
    (8 : ℝ) ^ (2 * (n : ℝ)) =
      (64 : ℝ) ^ n := by
  rw [eight_rpow_two_nat, pow_mul]
  norm_num

theorem flatMomentOrder_decay
    (C : ℝ) (m : ℕ) (hm : 4 ≤ m)
    (hmchoice :
      64 * C ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 4 /
          (64 : ℝ) ^ m ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    64 * C ^ 2 * (flatMomentOrder m δ : ℝ) ^ 4 /
        (8 : ℝ) ^ (2 * flatMomentOrder m δ) ≤
      δ ^ 4 := by
  let x := Real.log (1 / δ)
  let L := 1 + x
  let p := flatMomentOrder m δ
  have hbounds :=
    flatMomentOrder_bounds m (by omega) δ hδ hδ1
  have hp : 0 < p := hbounds.1
  have hlower : (m : ℝ) * L ≤ p := by
    simpa [p, L, x] using hbounds.2.1
  have hupper : (p : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * L := by
    simpa [p, L, x] using hbounds.2.2
  have hx : 0 ≤ x := by
    have hinv : 1 < 1 / δ :=
      (lt_div_iff₀ hδ).2 (by simpa using hδ1)
    exact (Real.log_pos hinv).le
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hnum :
      (p : ℝ) ^ 4 ≤
        (((m + 1 : ℕ) : ℝ) * L) ^ 4 :=
    pow_le_pow_left₀ (Nat.cast_nonneg p) hupper 4
  have hexponent :
      2 * (m : ℝ) * L ≤ 2 * (p : ℝ) := by
    nlinarith
  have hden :
      (8 : ℝ) ^ (2 * (m : ℝ) * L) ≤
        (8 : ℝ) ^ (2 * p) := by
    rw [← eight_rpow_two_nat p]
    exact Real.rpow_le_rpow_of_exponent_le
      (by norm_num) hexponent
  have hdenNatPos : 0 < (8 : ℝ) ^ (2 * p) := by positivity
  have hdenRealPos :
      0 < (8 : ℝ) ^ (2 * (m : ℝ) * L) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hratio :
      (p : ℝ) ^ 4 / (8 : ℝ) ^ (2 * p) ≤
        (((m + 1 : ℕ) : ℝ) * L) ^ 4 /
          (8 : ℝ) ^ (2 * (m : ℝ) * L) := by
    apply (div_le_div_iff₀ hdenNatPos hdenRealPos).2
    exact mul_le_mul hnum hden
      (Real.rpow_nonneg (by norm_num) _)
      (pow_nonneg
        (mul_nonneg (Nat.cast_nonneg _) hL) _)
  have hlog :=
    logarithmic_decay_aux m hm x hx
  have hcoef :
      0 ≤ 64 * C ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 4 := by
    positivity
  calc
    64 * C ^ 2 * (p : ℝ) ^ 4 /
        (8 : ℝ) ^ (2 * p) =
      (64 * C ^ 2) *
        ((p : ℝ) ^ 4 / (8 : ℝ) ^ (2 * p)) := by ring
    _ ≤ (64 * C ^ 2) *
        ((((m + 1 : ℕ) : ℝ) * L) ^ 4 /
          (8 : ℝ) ^ (2 * (m : ℝ) * L)) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (64 * C ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 4) *
        (L ^ 4 /
          (8 : ℝ) ^ (2 * (m : ℝ) * L)) := by ring
    _ ≤ (64 * C ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 4) *
        ((1 / (8 : ℝ) ^ (2 * (m : ℝ))) *
          Real.exp (-4 * x)) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [L] using hlog) hcoef
    _ = (64 * C ^ 2 * ((m + 1 : ℕ) : ℝ) ^ 4 /
          (64 : ℝ) ^ m) * Real.exp (-4 * x) := by
      rw [eight_rpow_two_nat_eq_sixtyFour_pow]
      ring
    _ ≤ 1 * Real.exp (-4 * x) :=
      mul_le_mul_of_nonneg_right hmchoice (Real.exp_pos _).le
    _ = δ ^ 4 := by
      rw [one_mul]
      exact exp_neg_four_log_inv δ hδ

noncomputable def flatDecayInteger
    (hc : GaussianHypercontractivityContract) : ℕ :=
  Classical.choose
    (exists_flatDecayInteger (flatMomentConstant hc))

theorem flatDecayInteger_ge_four
    (hc : GaussianHypercontractivityContract) :
    4 ≤ flatDecayInteger hc :=
  (Classical.choose_spec
    (exists_flatDecayInteger (flatMomentConstant hc))).1

theorem flatDecayInteger_choice
    (hc : GaussianHypercontractivityContract) :
    64 * flatMomentConstant hc ^ 2 *
        ((flatDecayInteger hc + 1 : ℕ) : ℝ) ^ 4 /
        (64 : ℝ) ^ flatDecayInteger hc ≤ 1 :=
  (Classical.choose_spec
    (exists_flatDecayInteger (flatMomentConstant hc))).2

def flatDecompositionConstant
    (hc : GaussianHypercontractivityContract) : ℝ :=
  (64 + 8 * flatMomentConstant hc) *
    ((flatDecayInteger hc + 1 : ℕ) : ℝ) ^ 2

theorem flatDecompositionConstant_pos
    (hc : GaussianHypercontractivityContract) :
    0 < flatDecompositionConstant hc := by
  unfold flatDecompositionConstant
  have hm : 0 < flatDecayInteger hc + 1 := by omega
  exact mul_pos
    (by
      have := flatMomentConstant_pos hc
      linarith)
    (sq_pos_of_pos (by exact_mod_cast hm))

def flatGamma
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (δ : ℝ) : ℝ :=
  flatDecompositionConstant hc *
      (1 + Real.log (1 / δ)) ^ 2 /
      (d : ℝ) ^ 2 *
    frobeniusNorm M

theorem FlatTailDecomposition.mono_gamma
    {ι : Type*} [Fintype ι]
    {A reference flat tail : CMatrix ι}
    {γ γ' δ : ℝ}
    (h : FlatTailDecomposition
      A reference flat tail γ δ)
    (hγ : γ ≤ γ') :
    FlatTailDecomposition A reference flat tail γ' δ :=
  ⟨h.1, h.2.1, h.2.2.1,
    h.2.2.2.1.trans hγ, h.2.2.2.2⟩

theorem flatThreshold_le_flatGamma
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    flatThreshold hc d M
        (flatMomentOrder (flatDecayInteger hc) δ) ≤
      flatGamma hc d M δ := by
  let m := flatDecayInteger hc
  let L := 1 + Real.log (1 / δ)
  let p := flatMomentOrder m δ
  have hm : 0 < m := by
    have hm4 : 4 ≤ m := by
      simpa [m] using flatDecayInteger_ge_four hc
    omega
  have hL : 0 ≤ L := by
    have hinv : 1 < 1 / δ :=
      (lt_div_iff₀ hδ).2 (by simpa using hδ1)
    dsimp [L]
    linarith [Real.log_pos hinv]
  have hpupper : (p : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * L := by
    simpa [p, m, L] using
      (flatMomentOrder_bounds m hm δ hδ hδ1).2.2
  have hpSq :
      (p : ℝ) ^ 2 ≤
        (((m + 1 : ℕ) : ℝ) * L) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg p) hpupper 2
  have hC : 0 ≤ flatMomentConstant hc :=
    (flatMomentConstant_pos hc).le
  have hfactor :
      8 * flatMomentConstant hc * (p : ℝ) ^ 2 ≤
        flatDecompositionConstant hc * L ^ 2 := by
    calc
      8 * flatMomentConstant hc * (p : ℝ) ^ 2 ≤
          8 * flatMomentConstant hc *
            ((((m + 1 : ℕ) : ℝ) * L) ^ 2) :=
        mul_le_mul_of_nonneg_left hpSq (by positivity)
      _ ≤ (64 + 8 * flatMomentConstant hc) *
            ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 2 := by
        have hmSq : 0 ≤ (((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 2) := by
          positivity
        calc
          8 * flatMomentConstant hc *
              ((((m + 1 : ℕ) : ℝ) * L) ^ 2) =
            (8 * flatMomentConstant hc) *
              (((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 2) := by ring
          _ ≤ (64 + 8 * flatMomentConstant hc) *
              (((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 2) := by
            gcongr
            linarith
          _ = _ := by ring
      _ = flatDecompositionConstant hc * L ^ 2 := by
        unfold flatDecompositionConstant
        dsimp [m]
  unfold flatThreshold flatMomentScale flatGamma
  change
    8 * (flatMomentConstant hc * (p : ℝ) ^ 2 /
        (d : ℝ) ^ 2 * frobeniusNorm M) ≤
      flatDecompositionConstant hc * L ^ 2 /
        (d : ℝ) ^ 2 * frobeniusNorm M
  have hden : 0 ≤ (d : ℝ) ^ 2 := sq_nonneg _
  have hnorm : 0 ≤ frobeniusNorm M := Real.sqrt_nonneg _
  calc
    8 * (flatMomentConstant hc * (p : ℝ) ^ 2 /
        (d : ℝ) ^ 2 * frobeniusNorm M) =
      (8 * flatMomentConstant hc * (p : ℝ) ^ 2) /
        (d : ℝ) ^ 2 * frobeniusNorm M := by ring
    _ ≤ (flatDecompositionConstant hc * L ^ 2) /
        (d : ℝ) ^ 2 * frobeniusNorm M := by
      gcongr
    _ = _ := rfl

theorem frobeniusNorm_le_flatGamma_of_small_dimension
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsmall :
      (d : ℝ) <
        8 * ((flatDecayInteger hc + 1 : ℕ) : ℝ) *
          (1 + Real.log (1 / δ))) :
    frobeniusNorm M ≤ flatGamma hc d M δ := by
  let m := flatDecayInteger hc
  let L := 1 + Real.log (1 / δ)
  have hL : 0 < L := by
    have hinv : 1 < 1 / δ :=
      (lt_div_iff₀ hδ).2 (by simpa using hδ1)
    dsimp [L]
    linarith [Real.log_pos hinv]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdsq :
      (d : ℝ) ^ 2 ≤
        64 * ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 2 := by
    have hsquare :=
      (sq_le_sq₀ hdR.le
        (mul_nonneg (by positivity) hL.le)).2 hsmall.le
    nlinarith
  have hconst :
      64 * ((m + 1 : ℕ) : ℝ) ^ 2 ≤
        flatDecompositionConstant hc := by
    unfold flatDecompositionConstant
    dsimp [m]
    have hsquare :
        0 ≤ ((flatDecayInteger hc + 1 : ℕ) : ℝ) ^ 2 := by
      positivity
    have hC := (flatMomentConstant_pos hc).le
    nlinarith
  have hnumerator :
      (d : ℝ) ^ 2 ≤
        flatDecompositionConstant hc * L ^ 2 := by
    calc
      (d : ℝ) ^ 2 ≤
          64 * ((m + 1 : ℕ) : ℝ) ^ 2 * L ^ 2 := hdsq
      _ ≤ flatDecompositionConstant hc * L ^ 2 := by
        gcongr
  have hcoefficient :
      1 ≤ flatDecompositionConstant hc * L ^ 2 /
        (d : ℝ) ^ 2 :=
    (one_le_div (sq_pos_of_pos hdR)).2 hnumerator
  unfold flatGamma
  change frobeniusNorm M ≤
    (flatDecompositionConstant hc * L ^ 2 /
      (d : ℝ) ^ 2) * frobeniusNorm M
  calc
    frobeniusNorm M = 1 * frobeniusNorm M := by ring
    _ ≤ (flatDecompositionConstant hc * L ^ 2 /
        (d : ℝ) ^ 2) * frobeniusNorm M :=
      mul_le_mul_of_nonneg_right hcoefficient (Real.sqrt_nonneg _)

theorem flat_decomposition_manuscript
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian)
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ((unitaryHaarMeasure d).prod
      (unitaryHaarMeasure d)).real
        {UV | ∃ flat tail,
          FlatTailDecomposition
            (bipartiteUnitaryConjugate d M UV) M
            flat tail (flatGamma hc d M δ) δ} ≥
      1 - δ ^ 2 := by
  let μ :=
    (unitaryHaarMeasure d).prod (unitaryHaarMeasure d)
  have hδ1 : δ < 1 := hδhalf.trans (by norm_num)
  by_cases hM0 : M = 0
  · have hall :
        {UV | ∃ flat tail,
          FlatTailDecomposition
            (bipartiteUnitaryConjugate d M UV) M
            flat tail (flatGamma hc d M δ) δ} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro UV
      subst M
      have hgamma0 :
          flatGamma hc d (0 : BipartiteMatrix (Fin d)) δ = 0 := by
        unfold flatGamma frobeniusNorm frobeniusSq
        simp
      refine ⟨0, 0, ?_, Matrix.isHermitian_zero,
        Matrix.isHermitian_zero, ?_, ?_⟩
      · simp [bipartiteUnitaryConjugate]
      · rw [hgamma0]
        unfold entryNorm
        rw [Matrix.norm_le_iff (le_refl 0)]
        intro i j
        simp
      · unfold frobeniusNorm frobeniusSq
        simp
    rw [hall, probReal_univ]
    nlinarith [sq_nonneg δ]
  · have hd : 0 < d := by
      by_contra hnot
      have hd0 : d = 0 := by omega
      subst d
      exact hM0 (Subsingleton.elim _ _)
    let m := flatDecayInteger hc
    let L := 1 + Real.log (1 / δ)
    let p := flatMomentOrder m δ
    have hm : 0 < m := by
      have : 4 ≤ m := by
        simpa [m] using flatDecayInteger_ge_four hc
      omega
    by_cases hlarge :
        8 * ((m + 1 : ℕ) : ℝ) * L ≤ d
    · have hp : 0 < p := by
        simpa [p, m] using
          (flatMomentOrder_bounds m hm δ hδ hδ1).1
      have height : 8 * p ≤ d := by
        apply flatMomentOrder_dimension m hm δ hδ hδ1 d
        simpa [L] using hlarge
      have hdecay :
          64 * flatMomentConstant hc ^ 2 * (p : ℝ) ^ 4 /
              (8 : ℝ) ^ (2 * p) ≤ δ ^ 4 := by
        exact flatMomentOrder_decay
          (flatMomentConstant hc) m
          (by simpa [m] using flatDecayInteger_ge_four hc)
          (by simpa [m] using flatDecayInteger_choice hc)
          δ hδ hδ1
      have hthreshold :=
        exists_flatTailDecomposition_at_flatThreshold
          hc d M hM hM0 hzero0 hzero1
          p hp height δ hδ hdecay
      apply hthreshold.trans
      apply measureReal_mono
      · intro UV hUV
        rcases hUV with ⟨flat, tail, hdecomp⟩
        exact ⟨flat, tail,
          hdecomp.mono_gamma
            (by
              simpa [p, m] using
                flatThreshold_le_flatGamma
                  hc d M δ hδ hδ1)⟩
      · exact measure_ne_top _ _
    · have hsmall :
          (d : ℝ) <
            8 * ((flatDecayInteger hc + 1 : ℕ) : ℝ) *
              (1 + Real.log (1 / δ)) := by
        simpa [m, L] using lt_of_not_ge hlarge
      have hgamma :
          frobeniusNorm M ≤ flatGamma hc d M δ :=
        frobeniusNorm_le_flatGamma_of_small_dimension
          hc d hd M δ hδ hδ1 hsmall
      have hall :
          {UV | ∃ flat tail,
            FlatTailDecomposition
              (bipartiteUnitaryConjugate d M UV) M
              flat tail (flatGamma hc d M δ) δ} =
            Set.univ := by
        apply Set.eq_univ_of_forall
        intro UV
        exact exists_flatTailDecomposition_of_gamma_ge
          d M hM UV (flatGamma hc d M δ) δ hgamma hδ.le
      rw [hall, probReal_univ]
      nlinarith [sq_nonneg δ]

end

end QuantumSep
