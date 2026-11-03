import QuantumSep.ReductionComparison
import QuantumSep.RandomizedCSPOptimization

/-!
# Correctness of a successful run of the main reduction

This file joins the local decomposition, Haar flat/tail comparison, and the
successful dense-CSP output.  It contains no probability or complexity
assumption.
-/

namespace QuantumSep

open scoped Matrix

noncomputable section

/-- Applying a unitary after its inverse recovers the original vector. -/
theorem unitaryVectorAction_inv_left
    (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (x : Fin d → ℂ) :
    unitaryVectorAction d U
        (unitaryVectorAction d U⁻¹ x) = x := by
  rw [unitaryVectorAction_assoc]
  rw [mul_inv_cancel]
  change (1 : CMatrix (Fin d)) *ᵥ x = x
  exact Matrix.one_mulVec x

/-- The output in the original basis. -/
def rotateProductOutput
    (d : ℕ)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ)
    (x y : Fin d → ℂ) :
    (Fin d → ℂ) × (Fin d → ℂ) :=
  (unitaryVectorAction d UV.1 x,
    unitaryVectorAction d UV.2 y)

theorem rotateProductOutput_normalized
    (d : ℕ)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ)
    (x y : Fin d → ℂ)
    (hx : vectorNormSq x = d)
    (hy : vectorNormSq y = d) :
    vectorNormSq (rotateProductOutput d UV x y).1 = d ∧
      vectorNormSq (rotateProductOutput d UV x y).2 = d := by
  constructor
  · simpa [rotateProductOutput] using
      (vectorNormSq_unitaryVectorAction d UV.1 x).trans hx
  · simpa [rotateProductOutput] using
      (vectorNormSq_unitaryVectorAction d UV.2 y).trans hy

/-- Once the Haar decomposition and the dense-CSP call both succeed, the
rotated normalized output approximates every product vector.  The error
contains exactly two tail charges and the two local evaluations. -/
theorem successfulReduction_approximates
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ)
    (flat tail : BipartiteMatrix (Fin d))
    (gamma delta cspError : ℝ)
    (hdelta : 0 ≤ delta)
    (hdecomp :
      FlatTailDecomposition
        (bipartiteUnitaryConjugate d (correlationPart M) UV)
        (correlationPart M) flat tail gamma delta)
    (outputX outputY : Fin d → ℂ)
    (houtputX : vectorNormSq outputX = d)
    (houtputY : vectorNormSq outputY = d)
    (hcsp :
      ∀ x y : Fin d → ℂ,
        vectorNormSq x = d →
        vectorNormSq y = d →
        matrixQuarticForm (correlationPart flat) x y ≤
          matrixQuarticForm (correlationPart flat)
            outputX outputY + cspError) :
    ∀ x y : Fin d → ℂ,
      vectorNormSq x = d →
      vectorNormSq y = d →
      matrixQuarticForm M x y ≤
        matrixQuarticForm M
          (rotateProductOutput d UV outputX outputY).1
          (rotateProductOutput d UV outputX outputY).2 +
        cspError + 2 * delta + 4 / Real.sqrt d := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let C := correlationPart M
  let total := bipartiteUnitaryConjugate d C UV
  let D := correlationPart flat
  have hzero0C : partialTrace0 C = 0 :=
    partialTrace0_correlationPart M
  have hzero1C : partialTrace1 C = 0 :=
    partialTrace1_correlationPart M
  have hzero0Total : partialTrace0 total = 0 := by
    exact partialTrace0_bipartiteUnitaryConjugate_eq_zero
      d C hzero0C UV
  have hzero1Total : partialTrace1 total = 0 := by
    exact partialTrace1_bipartiteUnitaryConjugate_eq_zero
      d C hzero1C UV
  have hCnorm : frobeniusNorm C ≤ 1 :=
    (correlationPart_frobeniusNorm_le M).trans hMnorm
  have htail
      (u v : Fin d → ℂ)
      (hu : vectorNormSq u = d)
      (hv : vectorNormSq v = d) :
      |matrixQuarticForm total u v -
          matrixQuarticForm D u v| ≤ delta := by
    have h :=
      abs_total_sub_projectedFlat_quartic_le
        d hd total C flat tail gamma delta
        (by simpa [total, C] using hdecomp)
        hzero0Total hzero1Total u v hu hv
    exact h.trans
      (by
        calc
          delta * frobeniusNorm C ≤ delta * 1 :=
            mul_le_mul_of_nonneg_left hCnorm hdelta
          _ = delta := mul_one _)
  intro x y hx hy
  let preX := unitaryVectorAction d UV.1⁻¹ x
  let preY := unitaryVectorAction d UV.2⁻¹ y
  have hpreX : vectorNormSq preX = d := by
    simpa [preX] using
      (vectorNormSq_unitaryVectorAction d UV.1⁻¹ x).trans hx
  have hpreY : vectorNormSq preY = d := by
    simpa [preY] using
      (vectorNormSq_unitaryVectorAction d UV.2⁻¹ y).trans hy
  have hpreXBack :
      unitaryVectorAction d UV.1 preX = x := by
    simpa [preX] using unitaryVectorAction_inv_left d UV.1 x
  have hpreYBack :
      unitaryVectorAction d UV.2 preY = y := by
    simpa [preY] using unitaryVectorAction_inv_left d UV.2 y
  have htailPre := htail preX preY hpreX hpreY
  have htailOut := htail outputX outputY houtputX houtputY
  have hCSP := hcsp preX preY hpreX hpreY
  have hcorrPre :
      matrixQuarticForm total preX preY =
        matrixQuarticForm C x y := by
    rw [show total = bipartiteUnitaryConjugate d C UV by rfl,
      matrixQuarticForm_bipartiteUnitaryConjugate,
      hpreXBack, hpreYBack]
  have hcorrOut :
      matrixQuarticForm total outputX outputY =
        matrixQuarticForm C
          (rotateProductOutput d UV outputX outputY).1
          (rotateProductOutput d UV outputX outputY).2 := by
    rw [show total = bipartiteUnitaryConjugate d C UV by rfl,
      matrixQuarticForm_bipartiteUnitaryConjugate]
    rfl
  have hcorr :
      matrixQuarticForm C x y ≤
        matrixQuarticForm C
          (rotateProductOutput d UV outputX outputY).1
          (rotateProductOutput d UV outputX outputY).2 +
        cspError + 2 * delta := by
    rw [← hcorrPre, ← hcorrOut]
    have hpreUpper := (abs_le.mp htailPre).2
    have houtLower := (abs_le.mp htailOut).1
    linarith
  have houtNorm :=
    rotateProductOutput_normalized d UV outputX outputY
      houtputX houtputY
  have hlocalInput :=
    abs_localTerms_quartic_le d hd M hMnorm x y hx hy
  have hlocalOutput :=
    abs_localTerms_quartic_le d hd M hMnorm
      (rotateProductOutput d UV outputX outputY).1
      (rotateProductOutput d UV outputX outputY).2
      houtNorm.1 houtNorm.2
  rw [matrixQuarticForm_localDecomposition d hd M x y hx hy,
    matrixQuarticForm_localDecomposition d hd M
      (rotateProductOutput d UV outputX outputY).1
      (rotateProductOutput d UV outputX outputY).2
      houtNorm.1 houtNorm.2]
  have hlocalInputUpper := (abs_le.mp hlocalInput).2
  have hlocalOutputLower := (abs_le.mp hlocalOutput).1
  dsimp [C] at hcorr
  have hlocalDiff :
      matrixQuarticForm
          (tensor (localA M) (1 : CMatrix (Fin d)) +
            tensor (1 : CMatrix (Fin d)) (localB M)) x y ≤
        matrixQuarticForm
          (tensor (localA M) (1 : CMatrix (Fin d)) +
            tensor (1 : CMatrix (Fin d)) (localB M))
          (rotateProductOutput d UV outputX outputY).1
          (rotateProductOutput d UV outputX outputY).2 +
        4 / Real.sqrt d := by
    have hsum :
        2 / Real.sqrt d + 2 / Real.sqrt d =
          4 / Real.sqrt d := by ring
    linarith
  linarith [hcorr, hlocalDiff]

end

end QuantumSep
