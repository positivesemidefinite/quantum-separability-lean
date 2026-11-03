import QuantumSep.SeparableOracle

/-!
# Uniform polynomial runtime

For fixed requested accuracy, the high-dimensional alphabet and CSP accuracy
are constants.  The finitely many dimensions below the explicit cutoff are
absorbed into one finite runtime constant.
-/

namespace QuantumSep

noncomputable section

def selectedHighRuntimeNet
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau) :
    ComplexDiskNet
      (2 * (selectedSigma
        (mainCSPGamma hc (mainMomentOrder hc tau))
        (mainDiscretizationAccuracy tau) + 1))
      (selectedMesh
        (mainCSPGamma hc (mainMomentOrder hc tau))
        (mainDiscretizationAccuracy tau)) :=
  explicitComplexDiskNet _ _
    (selectedMesh_pos
      (mainCSPGamma_nonneg hc (mainMomentOrder hc tau))
      (by
        unfold mainDiscretizationAccuracy
        exact div_pos (effectiveAccuracy_pos htau) (by norm_num)))

def selectedHighRuntimeAlphabet
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau) : ℕ :=
  Fintype.card
    (MatrixCSPAlphabet (selectedHighRuntimeNet hc tau htau))

def selectedHighRuntimeAccuracy
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) : ℕ :=
  Nat.ceil
    (1 / selectedCSPError
      (mainCSPGamma hc (mainMomentOrder hc tau))
      (mainDiscretizationAccuracy tau))

def selectedHighRuntimeDegree
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau) : ℕ :=
  max 1
    (max sampler.runtimeDegree
      (ptas.runtimeDegree
        (selectedHighRuntimeAlphabet hc tau htau)
        (selectedHighRuntimeAccuracy hc tau)))

def selectedHighRuntimeConstant
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau) : ℕ :=
  2 * sampler.runtimeConstant +
    ptas.runtimeConstant
      (selectedHighRuntimeAlphabet hc tau htau)
      (selectedHighRuntimeAccuracy hc tau) +
    12

def directRuntimeBound
    (ptas : DenseMaxFourCSPPTASContract)
    (tau : ℝ) (htau : 0 < tau) (d : ℕ) : ℕ :=
  let eta := effectiveAccuracy tau
  let gamma := directGamma d
  let kappa := (d : ℝ)
  let mesh := directMesh gamma kappa eta
  let net := explicitComplexDiskNet kappa mesh
    (directMesh_pos
      (by
        dsimp [gamma, directGamma]
        positivity)
      (by
        dsimp [kappa]
        positivity)
      (effectiveAccuracy_pos htau))
  ptas.runtimeConstant
      (Fintype.card (MatrixCSPAlphabet net))
      (Nat.ceil (1 / directCSPError gamma kappa eta)) *
    (d + 1) ^
      ptas.runtimeDegree
        (Fintype.card (MatrixCSPAlphabet net))
        (Nat.ceil (1 / directCSPError gamma kappa eta)) +
    8 * d + 4

def boundedDimensionRuntimeConstant
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau) : ℕ :=
  ∑ d ∈ Finset.range (mainDimensionCutoff hc tau),
    directRuntimeBound ptas tau htau d

def finalProductRuntimeConstant
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau) : ℕ :=
  selectedHighRuntimeConstant sampler ptas hc tau htau +
    boundedDimensionRuntimeConstant ptas hc tau htau

/-- Runtime bounded by a natural number, phrased as a property of the whole
procedure so dependent seed types rewrite cleanly across the dimension
branch. -/
def ProcedureRuntimeBound
    {Output : Type*}
    (alg : RandomizedProcedure Unit Output)
    (bound : ℕ) : Prop :=
  ∀ seed : alg.Seed, alg.runtime () seed ≤ bound

/-- The precise family-level meaning of polynomial time in the matrix
dimension for a fixed accuracy. -/
def ProductOptimizerPolynomialRuntime
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau) : Prop :=
  ∃ C degree : ℕ,
    ∀ (d : ℕ) (hd : 0 < d)
      (M : BipartiteMatrix (Fin d))
      (hMnorm : frobeniusNorm M ≤ 1),
      ProcedureRuntimeBound
        (productOptimizationProcedure
          sampler ptas hc tau htau d hd M hMnorm)
        (C * (d + 1) ^ degree)

private theorem highParameter_runtime_data
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hdim : mainDimensionCutoff hc tau ≤ d) :
    let p := mainMomentOrder hc tau
    let hdata := mainDimensionCutoff_data hc htau hdim
    let params :=
      selectedHighDimensionalParameters hc p
        (mainDiscretizationAccuracy tau)
        (by
          unfold mainDiscretizationAccuracy
          exact div_pos (effectiveAccuracy_pos htau) (by norm_num))
        d hdata.2.2.1
    Fintype.card
        (MatrixCSPAlphabet (highDimensionalNet params)) =
          selectedHighRuntimeAlphabet hc tau htau ∧
      Nat.ceil (1 / params.cspError) =
        selectedHighRuntimeAccuracy hc tau := by
  dsimp only
  constructor <;> rfl

private theorem instantiatedHigh_runtime_polynomial
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hdim : mainDimensionCutoff hc tau ≤ d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1) :
    ProcedureRuntimeBound
      (instantiatedHighDimensionalProcedure
        sampler ptas hc tau htau d hdim M hMnorm)
      (selectedHighRuntimeConstant sampler ptas hc tau htau *
        (d + 1) ^
          selectedHighRuntimeDegree sampler ptas hc tau htau) := by
  intro seed
  let D := selectedHighRuntimeDegree sampler ptas hc tau htau
  let A := selectedHighRuntimeAlphabet hc tau htau
  let E := selectedHighRuntimeAccuracy hc tau
  let C :=
    selectedHighRuntimeConstant sampler ptas hc tau htau
  have hraw :=
    instantiatedHighDimensionalProcedure_runtime_bound
      sampler ptas hc tau htau d hdim M hMnorm seed
  dsimp only at hraw
  have hdata := highParameter_runtime_data hc tau htau d hdim
  dsimp only at hdata
  rw [hdata.1, hdata.2] at hraw
  have hn : 1 ≤ d + 1 := by omega
  have hD1 : 1 ≤ D := by
    dsimp [D, selectedHighRuntimeDegree]
    exact le_max_left _ _
  have hDs : sampler.runtimeDegree ≤ D := by
    dsimp [D, selectedHighRuntimeDegree]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hDp : ptas.runtimeDegree A E ≤ D := by
    dsimp [D, A, E, selectedHighRuntimeDegree]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hpowS :
      (d + 1) ^ sampler.runtimeDegree ≤ (d + 1) ^ D :=
    pow_le_pow_right' hn hDs
  have hpowP :
      (d + 1) ^ ptas.runtimeDegree A E ≤ (d + 1) ^ D :=
    pow_le_pow_right' hn hDp
  have hdPow : d ≤ (d + 1) ^ D := by
    calc
      d ≤ d + 1 := by omega
      _ = (d + 1) ^ 1 := (pow_one _).symm
      _ ≤ (d + 1) ^ D := pow_le_pow_right' hn hD1
  have honePow : 1 ≤ (d + 1) ^ D := one_le_pow₀ hn
  have hsScaled :=
    Nat.mul_le_mul_left (2 * sampler.runtimeConstant) hpowS
  have hpScaled :=
    Nat.mul_le_mul_left (ptas.runtimeConstant A E) hpowP
  have hdScaled := Nat.mul_le_mul_left 8 hdPow
  have hfourScaled := Nat.mul_le_mul_left 4 honePow
  change
    (instantiatedHighDimensionalProcedure
      sampler ptas hc tau htau d hdim M hMnorm).runtime () seed ≤
        C * (d + 1) ^ D
  calc
    _ ≤
        2 * sampler.runtimeConstant *
            (d + 1) ^ sampler.runtimeDegree +
          ptas.runtimeConstant A E *
            (d + 1) ^ ptas.runtimeDegree A E +
          8 * d + 4 := by
      simpa [A, E] using hraw
    _ ≤
        2 * sampler.runtimeConstant * (d + 1) ^ D +
          ptas.runtimeConstant A E * (d + 1) ^ D +
          8 * (d + 1) ^ D + 4 * (d + 1) ^ D := by
      omega
    _ = C * (d + 1) ^ D := by
      dsimp [C, selectedHighRuntimeConstant, A, E]
      ring

private theorem direct_runtime_le_aggregate
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (hsmall : ¬ mainDimensionCutoff hc tau ≤ d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1) :
    ProcedureRuntimeBound
      (directOptimizationProcedure ptas tau htau d hd M hMnorm)
      (boundedDimensionRuntimeConstant ptas hc tau htau) := by
  intro seed
  have hraw :=
    directOptimizationProcedure_runtime_bound
      ptas tau htau d hd M hMnorm seed
  have hdmem :
      d ∈ Finset.range (mainDimensionCutoff hc tau) := by
    simp only [Finset.mem_range]
    omega
  have hterm :
      directRuntimeBound ptas tau htau d ≤
        boundedDimensionRuntimeConstant ptas hc tau htau := by
    unfold boundedDimensionRuntimeConstant
    exact Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) hdmem
  exact hraw.trans hterm

theorem productOptimizationProcedure_polynomial_runtime
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (ram : RealRAMModelContract)
    (tau : ℝ) (htau : 0 < tau) :
    ProductOptimizerPolynomialRuntime sampler ptas hc tau htau := by
  have _hRAM : ∀ op, ram.primitiveCost op = 1 :=
    ram.primitiveCost_eq_one
  refine
    ⟨finalProductRuntimeConstant sampler ptas hc tau htau,
      selectedHighRuntimeDegree sampler ptas hc tau htau, ?_⟩
  intro d hd M hMnorm
  by_cases hlarge : mainDimensionCutoff hc tau ≤ d
  · rw [productOptimizationProcedure_eq_high
      sampler ptas hc tau htau d hd M hMnorm hlarge]
    have hhigh :=
      instantiatedHigh_runtime_polynomial
        sampler ptas hc tau htau d hlarge M hMnorm
    intro seed
    have hbase := hhigh seed
    have hcoeff :
        selectedHighRuntimeConstant sampler ptas hc tau htau ≤
          finalProductRuntimeConstant sampler ptas hc tau htau := by
      unfold finalProductRuntimeConstant
      omega
    exact hbase.trans
      (Nat.mul_le_mul_right
        ((d + 1) ^
          selectedHighRuntimeDegree sampler ptas hc tau htau)
        hcoeff)
  · rw [productOptimizationProcedure_eq_low
      sampler ptas hc tau htau d hd M hMnorm hlarge]
    have hlow :=
      direct_runtime_le_aggregate
        ptas hc tau htau d hd hlarge M hMnorm
    intro seed
    have hbase := hlow seed
    let C := finalProductRuntimeConstant sampler ptas hc tau htau
    let D := selectedHighRuntimeDegree sampler ptas hc tau htau
    have hlowC :
        boundedDimensionRuntimeConstant ptas hc tau htau ≤ C := by
      dsimp [C, finalProductRuntimeConstant]
      omega
    have hn : 1 ≤ d + 1 := by omega
    have hone : 1 ≤ (d + 1) ^ D := one_le_pow₀ hn
    have hC : C ≤ C * (d + 1) ^ D := by
      simpa using Nat.mul_le_mul_left C hone
    exact hbase.trans (hlowC.trans hC)

/-- The explicit uniform bound witnessed by
`productOptimizationProcedure_polynomial_runtime`. -/
theorem productOptimizationProcedure_runtime_bound
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (ram : RealRAMModelContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1) :
    ProcedureRuntimeBound
      (productOptimizationProcedure
        sampler ptas hc tau htau d hd M hMnorm)
      (finalProductRuntimeConstant sampler ptas hc tau htau *
        (d + 1) ^
          selectedHighRuntimeDegree sampler ptas hc tau htau) := by
  have _hRAM : ∀ op, ram.primitiveCost op = 1 :=
    ram.primitiveCost_eq_one
  by_cases hlarge : mainDimensionCutoff hc tau ≤ d
  · rw [productOptimizationProcedure_eq_high
      sampler ptas hc tau htau d hd M hMnorm hlarge]
    have hhigh :=
      instantiatedHigh_runtime_polynomial
        sampler ptas hc tau htau d hlarge M hMnorm
    intro seed
    have hbase := hhigh seed
    have hcoeff :
        selectedHighRuntimeConstant sampler ptas hc tau htau ≤
          finalProductRuntimeConstant sampler ptas hc tau htau := by
      unfold finalProductRuntimeConstant
      omega
    exact hbase.trans
      (Nat.mul_le_mul_right
        ((d + 1) ^
          selectedHighRuntimeDegree sampler ptas hc tau htau)
        hcoeff)
  · rw [productOptimizationProcedure_eq_low
      sampler ptas hc tau htau d hd M hMnorm hlarge]
    have hlow :=
      direct_runtime_le_aggregate
        ptas hc tau htau d hd hlarge M hMnorm
    intro seed
    have hbase := hlow seed
    let C := finalProductRuntimeConstant sampler ptas hc tau htau
    let D := selectedHighRuntimeDegree sampler ptas hc tau htau
    have hlowC :
        boundedDimensionRuntimeConstant ptas hc tau htau ≤ C := by
      dsimp [C, finalProductRuntimeConstant]
      omega
    have hn : 1 ≤ d + 1 := by omega
    have hone : 1 ≤ (d + 1) ^ D := one_le_pow₀ hn
    have hC : C ≤ C * (d + 1) ^ D := by
      simpa using Nat.mul_le_mul_left C hone
    exact hbase.trans (hlowC.trans hC)

end

end QuantumSep
