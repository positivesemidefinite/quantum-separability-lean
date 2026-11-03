import QuantumSep.SeparableGeometry

/-!
# A separable linear-optimization oracle

The all-dimensional product optimizer is repackaged as a randomized procedure
whose output is a normalized pure product state.  Its quartic guarantee is
lifted, without a further assumption, to the full separable convex hull.
-/

namespace QuantumSep

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

noncomputable section

private theorem matrixOfHilbert_frobeniusNorm_le
    (d : ℕ) (A : MatrixHilbert d)
    (hA : ‖A‖ ≤ 1) :
    frobeniusNorm (matrixOfHilbert d A) ≤ 1 := by
  rw [← matrixHilbertOf_norm,
    matrixHilbertOf_matrixOfHilbert]
  exact hA

/-- The final product optimizer, with its pair of vectors converted to the
corresponding pure product density matrix. -/
def separableLinearOracleProcedure
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (A : MatrixHilbert d)
    (hAnorm : ‖A‖ ≤ 1) :
    RandomizedProcedure Unit (MatrixHilbert d) := by
  let base :=
    productOptimizationProcedure sampler ptas hc tau htau d hd
      (matrixOfHilbert d A)
      (matrixOfHilbert_frobeniusNorm_le d A hAnorm)
  exact {
    Seed := base.Seed
    seedMeasurableSpace := base.seedMeasurableSpace
    seedMeasure := base.seedMeasure
    seedProbability := base.seedProbability
    run := fun _ seed =>
      matrixHilbertOf d
        (productDensityMatrix d
          (base.run () seed).1 (base.run () seed).2)
    runtime := fun _ seed => base.runtime () seed + 8 * d ^ 4 + 4
  }

theorem separableLinearOracleProcedure_output_mem
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (A : MatrixHilbert d)
    (hAnorm : ‖A‖ ≤ 1)
    (seed :
      (separableLinearOracleProcedure
        sampler ptas hc tau htau d hd A hAnorm).Seed) :
    (separableLinearOracleProcedure
        sampler ptas hc tau htau d hd A hAnorm).run () seed ∈
      separableStates d := by
  let base :=
    productOptimizationProcedure sampler ptas hc tau htau d hd
      (matrixOfHilbert d A)
      (matrixOfHilbert_frobeniusNorm_le d A hAnorm)
  have hnorm :=
    productOptimizationProcedure_output_normalized
      sampler ptas hc tau htau d hd (matrixOfHilbert d A)
      (matrixOfHilbert_frobeniusNorm_le d A hAnorm)
      seed
  apply pureProductState_mem_separable
  exact
    ⟨(base.run () seed).1, (base.run () seed).2,
      hnorm.1, hnorm.2, rfl⟩

theorem separableLinearOracleProcedure_output_norm
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (A : MatrixHilbert d)
    (hAnorm : ‖A‖ ≤ 1)
    (seed :
      (separableLinearOracleProcedure
        sampler ptas hc tau htau d hd A hAnorm).Seed) :
    ‖(separableLinearOracleProcedure
        sampler ptas hc tau htau d hd A hAnorm).run () seed‖ = 1 :=
  pureProductStates_norm d hd
    (show
      (separableLinearOracleProcedure
          sampler ptas hc tau htau d hd A hAnorm).run () seed ∈
        pureProductStates d by
      let base :=
        productOptimizationProcedure sampler ptas hc tau htau d hd
          (matrixOfHilbert d A)
          (matrixOfHilbert_frobeniusNorm_le d A hAnorm)
      have hnorm :=
        productOptimizationProcedure_output_normalized
          sampler ptas hc tau htau d hd (matrixOfHilbert d A)
          (matrixOfHilbert_frobeniusNorm_le d A hAnorm)
          seed
      exact
        ⟨(base.run () seed).1, (base.run () seed).2,
          hnorm.1, hnorm.2, rfl⟩)

/-- With probability at least `2/3`, the returned pure state maximizes the
linear functional over the entire separable set up to additive `tau`. -/
theorem separableLinearOracleProcedure_success
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (A : MatrixHilbert d)
    (hAherm : (matrixOfHilbert d A).IsHermitian)
    (hAnorm : ‖A‖ ≤ 1) :
    let alg :=
      separableLinearOracleProcedure
        sampler ptas hc tau htau d hd A hAnorm
    alg.eventProbability
      {seed |
        ∀ P ∈ separableStates d,
          ⟪A, P⟫ ≤ ⟪A, alg.run () seed⟫ + tau} ≥
      2 / 3 := by
  dsimp only
  let M := matrixOfHilbert d A
  have hMnorm := matrixOfHilbert_frobeniusNorm_le d A hAnorm
  let base :=
    productOptimizationProcedure sampler ptas hc tau htau d hd M hMnorm
  letI : MeasurableSpace base.Seed := base.seedMeasurableSpace
  letI : IsProbabilityMeasure base.seedMeasure := base.seedProbability
  let goodProduct : Set base.Seed :=
    {seed |
      ∀ x y : Fin d → ℂ,
        vectorNormSq x = d →
        vectorNormSq y = d →
        matrixQuarticForm M x y ≤
          matrixQuarticForm M
            (base.run () seed).1 (base.run () seed).2 + tau}
  let goodSeparable : Set base.Seed :=
    {seed |
      ∀ P ∈ separableStates d,
        ⟪A, P⟫ ≤
          ⟪A, matrixHilbertOf d
            (productDensityMatrix d
              (base.run () seed).1 (base.run () seed).2)⟫ + tau}
  have hsubset : goodProduct ⊆ goodSeparable := by
    intro seed hseed P hP
    have hnorm :=
      productOptimizationProcedure_output_normalized
        sampler ptas hc tau htau d hd M hMnorm seed
    have hbound :=
      product_quartic_bound_extends_to_separable
        d hd M hAherm
        (base.run () seed).1 (base.run () seed).2
        hnorm.1 hnorm.2 tau hseed hP
    simpa [M] using hbound
  have hbase :=
    productOptimizationProcedure_success
      sampler ptas hc tau htau d hd M hAherm hMnorm
  change base.eventProbability goodSeparable ≥ 2 / 3
  calc
    2 / 3 ≤ base.eventProbability goodProduct := by
      simpa [goodProduct, base] using hbase
    _ ≤ base.eventProbability goodSeparable := by
      exact measureReal_mono hsubset (measure_ne_top _ _)

end

end QuantumSep
