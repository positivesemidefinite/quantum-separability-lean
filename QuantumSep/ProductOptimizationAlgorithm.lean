import QuantumSep.LowDimensionalOptimization

/-!
# Product-state optimization in every positive dimension

The final algorithm uses the Haar-flattening branch above the explicit cutoff
and the direct finite-CSP branch below it.
-/

namespace QuantumSep

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The final product-vector optimization procedure in every positive
dimension. -/
def productOptimizationProcedure
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1) :
    RandomizedProcedure Unit ((Fin d → ℂ) × (Fin d → ℂ)) :=
  if hlarge : mainDimensionCutoff hc tau ≤ d then
    instantiatedHighDimensionalProcedure
      sampler ptas hc tau htau d hlarge M hMnorm
  else
    directOptimizationProcedure ptas tau htau d hd M hMnorm

theorem productOptimizationProcedure_eq_high
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (hlarge : mainDimensionCutoff hc tau ≤ d) :
    productOptimizationProcedure sampler ptas hc tau htau d hd M hMnorm =
      instantiatedHighDimensionalProcedure
        sampler ptas hc tau htau d hlarge M hMnorm := by
  simp [productOptimizationProcedure, hlarge]

theorem productOptimizationProcedure_eq_low
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (hsmall : ¬ mainDimensionCutoff hc tau ≤ d) :
    productOptimizationProcedure sampler ptas hc tau htau d hd M hMnorm =
      directOptimizationProcedure ptas tau htau d hd M hMnorm := by
  simp [productOptimizationProcedure, hsmall]

def OutputsNormalized
    (d : ℕ)
    (alg : RandomizedProcedure Unit
      ((Fin d → ℂ) × (Fin d → ℂ))) : Prop :=
  ∀ seed : alg.Seed,
    vectorNormSq (alg.run () seed).1 = d ∧
      vectorNormSq (alg.run () seed).2 = d

/-- For every positive dimension, the final procedure returns an additive
`tau` product-vector maximizer with probability at least `2/3`. -/
theorem productOptimizationProcedure_success
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian)
    (hMnorm : frobeniusNorm M ≤ 1) :
    let alg :=
      productOptimizationProcedure
        sampler ptas hc tau htau d hd M hMnorm
    alg.eventProbability
      {seed |
        ∀ x y : Fin d → ℂ,
          vectorNormSq x = d →
          vectorNormSq y = d →
          matrixQuarticForm M x y ≤
            matrixQuarticForm M
              (alg.run () seed).1 (alg.run () seed).2 + tau} ≥
      2 / 3 := by
  by_cases hlarge : mainDimensionCutoff hc tau ≤ d
  · rw [productOptimizationProcedure_eq_high
      sampler ptas hc tau htau d hd M hMnorm hlarge]
    exact
      instantiatedHighDimensionalProcedure_success
        sampler ptas hc tau htau d hlarge M hM hMnorm
  · rw [productOptimizationProcedure_eq_low
      sampler ptas hc tau htau d hd M hMnorm hlarge]
    exact
      directOptimizationProcedure_success
        ptas tau htau d hd M hMnorm

/-- Every branch returns scaled unit vectors on every seed, independently of
the success event. -/
theorem productOptimizationProcedure_output_normalized
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1) :
    OutputsNormalized d
      (productOptimizationProcedure
        sampler ptas hc tau htau d hd M hMnorm) := by
  by_cases hlarge : mainDimensionCutoff hc tau ≤ d
  · rw [productOptimizationProcedure_eq_high
      sampler ptas hc tau htau d hd M hMnorm hlarge]
    intro seed
    exact instantiatedHighDimensionalProcedure_output_normalized
      sampler ptas hc tau htau d hlarge M hMnorm seed
  · rw [productOptimizationProcedure_eq_low
      sampler ptas hc tau htau d hd M hMnorm hlarge]
    intro seed
    exact directOptimizationProcedure_output_normalized
      ptas tau htau d hd M hMnorm seed

end

end QuantumSep
