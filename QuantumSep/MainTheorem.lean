import QuantumSep.RuntimeAnalysis
import QuantumSep.SeparableWeakMembership

/-!
# End-to-end theorem

This is the manuscript's randomized product-state optimization theorem,
assembled from exactly the four authorized external contracts.
-/

namespace QuantumSep

noncomputable section

/-- For every positive dimension and positive additive accuracy, the concrete
procedure always outputs normalized vectors, succeeds with probability at
least `2/3`, and belongs to a dimension-polynomial family for fixed accuracy.
-/
theorem randomizedProductOptimization_main
    (assumptions : AllowedAssumptions)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian)
    (hMnorm : frobeniusNorm M ≤ 1) :
    let alg :=
      productOptimizationProcedure
        assumptions.efficient_haar_sampling
        assumptions.dense_max_four_csp_ptas
        assumptions.gaussian_hypercontractivity
        tau htau d hd M hMnorm
    OutputsNormalized d alg ∧
      alg.eventProbability
        {seed |
          ∀ x y : Fin d → ℂ,
            vectorNormSq x = d →
            vectorNormSq y = d →
            matrixQuarticForm M x y ≤
              matrixQuarticForm M
                (alg.run () seed).1 (alg.run () seed).2 + tau} ≥
        2 / 3 ∧
      ProductOptimizerPolynomialRuntime
        assumptions.efficient_haar_sampling
        assumptions.dense_max_four_csp_ptas
        assumptions.gaussian_hypercontractivity
        tau htau := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact productOptimizationProcedure_output_normalized
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      tau htau d hd M hMnorm
  · exact productOptimizationProcedure_success
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      tau htau d hd M hM hMnorm
  · exact productOptimizationProcedure_polynomial_runtime
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      assumptions.real_ram_model tau htau

end

end QuantumSep
