import QuantumSep.FinalOptimization
import QuantumSep.CompactOptimization

/-!
# Direct optimization in bounded dimension

For dimensions below the accuracy-dependent cutoff, every normalized
coordinate is bounded by the dimension itself.  A direct disk-net CSP
therefore gives the required approximation, with an alphabet whose size is
constant for each fixed requested accuracy.
-/

namespace QuantumSep

open MeasureTheory ProbabilityTheory

noncomputable section

def directGamma (d : ℕ) : ℝ :=
  (d : ℝ) ^ 2

def directPenalty (gamma kappa eta : ℝ) : ℝ :=
  (gamma ^ 2 + gamma ^ 2 * kappa ^ 4) / eta + 1

def directRoundingCoefficient
    (gamma kappa eta : ℝ) : ℝ :=
  4 * gamma * kappa ^ 3 +
    8 * directPenalty gamma kappa eta * kappa * (kappa ^ 2 + 1)

def directMesh (gamma kappa eta : ℝ) : ℝ :=
  eta / (4 * (directRoundingCoefficient gamma kappa eta + 1))

def directCSPError (gamma kappa eta : ℝ) : ℝ :=
  eta /
    (8 * matrixPredicateScale gamma kappa
      (directPenalty gamma kappa eta))

theorem directPenalty_pos
    {gamma kappa eta : ℝ} (heta : 0 < eta) :
    0 < directPenalty gamma kappa eta := by
  unfold directPenalty
  have hnum : 0 ≤ gamma ^ 2 + gamma ^ 2 * kappa ^ 4 := by
    positivity
  have := div_nonneg hnum heta.le
  linarith

theorem directRoundingCoefficient_nonneg
    {gamma kappa eta : ℝ}
    (hgamma : 0 ≤ gamma) (hkappa : 0 ≤ kappa)
    (heta : 0 < eta) :
    0 ≤ directRoundingCoefficient gamma kappa eta := by
  unfold directRoundingCoefficient
  have hp := (directPenalty_pos
    (gamma := gamma) (kappa := kappa) heta).le
  positivity

theorem directMesh_pos
    {gamma kappa eta : ℝ}
    (hgamma : 0 ≤ gamma) (hkappa : 0 ≤ kappa)
    (heta : 0 < eta) :
    0 < directMesh gamma kappa eta := by
  unfold directMesh
  exact div_pos heta
    (mul_pos (by norm_num)
      (by
        have := directRoundingCoefficient_nonneg
          hgamma hkappa heta
        linarith))

theorem directCSPError_pos
    {gamma kappa eta : ℝ}
    (hgamma : 0 ≤ gamma) (hkappa : 0 ≤ kappa)
    (heta : 0 < eta) :
    0 < directCSPError gamma kappa eta := by
  unfold directCSPError
  have hp := (directPenalty_pos
    (gamma := gamma) (kappa := kappa) heta).le
  have hscale :
      0 < matrixPredicateScale gamma kappa
        (directPenalty gamma kappa eta) := by
    unfold matrixPredicateScale
    positivity
  exact div_pos heta (mul_pos (by norm_num) hscale)

def directOptimizationError
    (gamma kappa eta : ℝ) : ℝ :=
  (4 * gamma * kappa ^ 3 * directMesh gamma kappa eta +
    8 * directPenalty gamma kappa eta * kappa *
      (kappa ^ 2 + 1) * directMesh gamma kappa eta) +
  2 * matrixPredicateScale gamma kappa
      (directPenalty gamma kappa eta) *
    directCSPError gamma kappa eta +
  (gamma ^ 2 + gamma ^ 2 * kappa ^ 4) /
    (4 * directPenalty gamma kappa eta)

theorem directOptimizationError_le
    {gamma kappa eta : ℝ}
    (hgamma : 0 ≤ gamma) (hkappa : 0 ≤ kappa)
    (heta : 0 < eta) :
    directOptimizationError gamma kappa eta ≤ eta := by
  let R := directRoundingCoefficient gamma kappa eta
  let P := directPenalty gamma kappa eta
  let S := matrixPredicateScale gamma kappa P
  have hR : 0 ≤ R :=
    directRoundingCoefficient_nonneg hgamma hkappa heta
  have hP : 0 < P :=
    directPenalty_pos heta
  have hS : 0 < S := by
    dsimp [S]
    unfold matrixPredicateScale
    positivity
  have hround :
      R * directMesh gamma kappa eta ≤ eta / 4 := by
    unfold directMesh
    change R * (eta / (4 * (R + 1))) ≤ eta / 4
    calc
      R * (eta / (4 * (R + 1))) =
          (R * eta) / (4 * (R + 1)) := by ring
      _ ≤ eta / 4 := by
        apply (div_le_iff₀ (by positivity : 0 < 4 * (R + 1))).2
        nlinarith
  have hcsp :
      2 * S * directCSPError gamma kappa eta = eta / 4 := by
    unfold directCSPError
    change 2 * S * (eta / (8 * S)) = eta / 4
    field_simp [hS.ne']
    ring
  have hpen :
      (gamma ^ 2 + gamma ^ 2 * kappa ^ 4) / (4 * P) ≤
        eta / 4 := by
    let numerator := gamma ^ 2 + gamma ^ 2 * kappa ^ 4
    have hnum : 0 ≤ numerator := by
      dsimp [numerator]
      positivity
    have hcore : numerator ≤ eta * P := by
      dsimp [P]
      unfold directPenalty
      dsimp [numerator]
      field_simp [heta.ne']
      nlinarith
    apply (div_le_iff₀ (mul_pos (by norm_num) hP)).2
    nlinarith
  have hround' :
      4 * gamma * kappa ^ 3 * directMesh gamma kappa eta +
          8 * directPenalty gamma kappa eta * kappa *
            (kappa ^ 2 + 1) * directMesh gamma kappa eta ≤
        eta / 4 := by
    calc
      4 * gamma * kappa ^ 3 * directMesh gamma kappa eta +
          8 * directPenalty gamma kappa eta * kappa *
            (kappa ^ 2 + 1) * directMesh gamma kappa eta =
        R * directMesh gamma kappa eta := by
          dsimp [R]
          unfold directRoundingCoefficient
          ring
      _ ≤ eta / 4 := hround
  unfold directOptimizationError
  dsimp [S, P] at hcsp hpen
  linarith

theorem directMatrix_entry_bound
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (a b c e : Fin d) :
    ‖M (a, c) (b, e)‖ ≤
      directGamma d / cardR (ι := Fin d) ^ 2 := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hentry :
      ‖M (a, c) (b, e)‖ ≤ frobeniusNorm M :=
    (norm_entry_le_entryNorm M (a, c) (b, e)).trans
      (entryNorm_le_frobeniusNorm M)
  calc
    ‖M (a, c) (b, e)‖ ≤ 1 := hentry.trans hMnorm
    _ = directGamma d / cardR (ι := Fin d) ^ 2 := by
      unfold directGamma cardR
      simp only [Fintype.card_fin]
      field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hd]

/-- The direct bounded-dimensional CSP optimizer. -/
def directOptimizationProcedure
    (ptas : DenseMaxFourCSPPTASContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1) :
    RandomizedProcedure Unit ((Fin d → ℂ) × (Fin d → ℂ)) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
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
  letI := matrixCSPAlphabet_nonempty net (by
    dsimp [kappa]
    positivity)
  let csp :=
    matrixDenseMaxFourCSP net M
      (directPenalty gamma kappa eta) gamma
      (by
        dsimp [gamma, directGamma]
        positivity)
      (by
        dsimp [kappa]
        positivity)
      (directPenalty_pos (effectiveAccuracy_pos htau)).le
      (directMatrix_entry_bound d hd M hMnorm)
  let base :=
    ptas.procedure (Fin d) (MatrixCSPAlphabet net) csp
      (directCSPError gamma kappa eta)
  exact {
    Seed := base.Seed
    seedMeasurableSpace := base.seedMeasurableSpace
    seedMeasure := base.seedMeasure
    seedProbability := base.seedProbability
    run := fun _ seed =>
      (normalizedCSPOutputX net (base.run () seed),
        normalizedCSPOutputY net (base.run () seed))
    runtime := fun _ seed =>
      base.runtime () seed + 8 * d + 4
  }

theorem directOptimizationProcedure_output_normalized
    (ptas : DenseMaxFourCSPPTASContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (seed :
      (directOptimizationProcedure ptas tau htau d hd M hMnorm).Seed) :
    vectorNormSq
        ((directOptimizationProcedure ptas tau htau d hd M hMnorm).run ()
          seed).1 = d ∧
      vectorNormSq
        ((directOptimizationProcedure ptas tau htau d hd M hMnorm).run ()
          seed).2 = d := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
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
  letI := matrixCSPAlphabet_nonempty net (by
    dsimp [kappa]
    positivity)
  let csp :=
    matrixDenseMaxFourCSP net M
      (directPenalty gamma kappa eta) gamma
      (by
        dsimp [gamma, directGamma]
        positivity)
      (by
        dsimp [kappa]
        positivity)
      (directPenalty_pos (effectiveAccuracy_pos htau)).le
      (directMatrix_entry_bound d hd M hMnorm)
  let base :=
    ptas.procedure (Fin d) (MatrixCSPAlphabet net) csp
      (directCSPError gamma kappa eta)
  change
    vectorNormSq
        (normalizedCSPOutputX net (base.run () seed)) = d ∧
      vectorNormSq
        (normalizedCSPOutputY net (base.run () seed)) = d
  constructor
  · simpa using normalizedCSPOutputX_normSq net (base.run () seed)
  · simpa using normalizedCSPOutputY_normSq net (base.run () seed)

theorem directOptimizationProcedure_runtime_bound
    (ptas : DenseMaxFourCSPPTASContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (seed :
      (directOptimizationProcedure ptas tau htau d hd M hMnorm).Seed) :
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
    (directOptimizationProcedure ptas tau htau d hd M hMnorm).runtime ()
        seed ≤
      ptas.runtimeConstant
          (Fintype.card (MatrixCSPAlphabet net))
          (Nat.ceil (1 / directCSPError gamma kappa eta)) *
        (d + 1) ^
          ptas.runtimeDegree
            (Fintype.card (MatrixCSPAlphabet net))
            (Nat.ceil (1 / directCSPError gamma kappa eta)) +
        8 * d + 4 := by
  dsimp only
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
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
  letI := matrixCSPAlphabet_nonempty net (by
    dsimp [kappa]
    positivity)
  let csp :=
    matrixDenseMaxFourCSP net M
      (directPenalty gamma kappa eta) gamma
      (by
        dsimp [gamma, directGamma]
        positivity)
      (by
        dsimp [kappa]
        positivity)
      (directPenalty_pos (effectiveAccuracy_pos htau)).le
      (directMatrix_entry_bound d hd M hMnorm)
  have hcsp :=
    ptas.polynomial_runtime
      (Fin d) (MatrixCSPAlphabet net) csp
      (directCSPError gamma kappa eta) seed
  change
    ptas.runtime (Fin d) (MatrixCSPAlphabet net) csp
          (directCSPError gamma kappa eta) seed +
        8 * d + 4 ≤ _
  simpa [Nat.add_assoc] using
    (Nat.add_le_add_right hcsp (8 * d + 4))

/-- The PTAS-success event underlying the direct bounded-dimensional
optimizer. -/
def directOptimizationCoreSuccess
    (ptas : DenseMaxFourCSPPTASContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (seed : ptas.Seed) : Prop := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let eta := effectiveAccuracy tau
  let gamma := directGamma d
  let kappa := (d : ℝ)
  let mesh := directMesh gamma kappa eta
  let net := explicitComplexDiskNet kappa mesh
    (directMesh_pos (by
      dsimp [gamma, directGamma]
      positivity) (by
      dsimp [kappa]
      positivity) (effectiveAccuracy_pos htau))
  letI := matrixCSPAlphabet_nonempty net (by
    dsimp [kappa]
    positivity)
  let csp :=
    matrixDenseMaxFourCSP net M
      (directPenalty gamma kappa eta) gamma
      (by
        dsimp [gamma, directGamma]
        positivity)
      (by
        dsimp [kappa]
        positivity)
      (directPenalty_pos (effectiveAccuracy_pos htau)).le
      (directMatrix_entry_bound d hd M hMnorm)
  exact ∀ assignment,
    csp.value assignment ≤
      csp.value
        (ptas.solve (Fin d) (MatrixCSPAlphabet net)
          csp (directCSPError gamma kappa eta) seed) +
      directCSPError gamma kappa eta

/-- Deterministic correctness of the direct procedure on its measurable PTAS
success core. -/
theorem directOptimizationProcedure_correct_of_core
    (ptas : DenseMaxFourCSPPTASContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (seed :
      (directOptimizationProcedure ptas tau htau d hd M hMnorm).Seed)
    (hcspGood :
      directOptimizationCoreSuccess
        ptas tau htau d hd M hMnorm seed) :
    ∀ x y : Fin d → ℂ,
      vectorNormSq x = d →
      vectorNormSq y = d →
      matrixQuarticForm M x y ≤
        matrixQuarticForm M
          ((directOptimizationProcedure
            ptas tau htau d hd M hMnorm).run () seed).1
          ((directOptimizationProcedure
            ptas tau htau d hd M hMnorm).run () seed).2 + tau := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let eta := effectiveAccuracy tau
  let gamma := directGamma d
  let kappa := (d : ℝ)
  let mesh := directMesh gamma kappa eta
  have hgamma : 0 ≤ gamma := by
    dsimp [gamma, directGamma]
    positivity
  have hkappa : 0 ≤ kappa := by positivity
  have heta : 0 < eta := effectiveAccuracy_pos htau
  have hmesh : 0 < mesh :=
    directMesh_pos hgamma hkappa heta
  let net := explicitComplexDiskNet kappa mesh hmesh
  letI := matrixCSPAlphabet_nonempty net (by
    dsimp [kappa]
    positivity)
  let csp :=
    matrixDenseMaxFourCSP net M
      (directPenalty gamma kappa eta) gamma
      hgamma hkappa (directPenalty_pos heta).le
      (directMatrix_entry_bound d hd M hMnorm)
  let assignment :=
    ptas.solve (Fin d) (MatrixCSPAlphabet net)
      csp (directCSPError gamma kappa eta) seed
  have hcspGood' : ∀ other,
      csp.value other ≤
        csp.value assignment +
          directCSPError gamma kappa eta := by
    simpa [directOptimizationCoreSuccess, eta, gamma, kappa, mesh,
      net, csp, assignment] using hcspGood
  intro x y hx hy
  have hxcoord : ∀ i, ‖x i‖ ≤ kappa := by
    intro i
    simpa [kappa] using
      norm_coordinate_le_card_of_scaledUnit
        (show x ∈ scaledUnitVectors (Fin d) by
          simpa [scaledUnitVectors] using hx) i
  have hycoord : ∀ i, ‖y i‖ ≤ kappa := by
    intro i
    simpa [kappa] using
      norm_coordinate_le_card_of_scaledUnit
        (show y ∈ scaledUnitVectors (Fin d) by
          simpa [scaledUnitVectors] using hy) i
  have hsuccessful :=
    successfulCSP_output_approximates_bounded
      net M (directPenalty gamma kappa eta) gamma
      (directCSPError gamma kappa eta)
      hgamma hkappa hmesh.le (directPenalty_pos heta)
      (directMatrix_entry_bound d hd M hMnorm)
      assignment hcspGood'
      x y (by simpa using hx) (by simpa using hy)
      hxcoord hycoord
  have herr :=
    directOptimizationError_le hgamma hkappa heta
  have hetaTau := effectiveAccuracy_le_tau tau
  dsimp [directOptimizationError] at herr
  have htarget :
      matrixQuarticForm M x y ≤
        matrixQuarticForm M
          (normalizedCSPOutputX net assignment)
          (normalizedCSPOutputY net assignment) + tau := by
    linarith
  simpa [directOptimizationProcedure,
    DenseMaxFourCSPPTASContract.procedure,
    eta, gamma, kappa, mesh, net, csp, assignment] using htarget

/-- The direct procedure succeeds with probability at least `2/3` and
additive error at most the requested tolerance. -/
theorem directOptimizationProcedure_success
    (ptas : DenseMaxFourCSPPTASContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1) :
    let alg :=
      directOptimizationProcedure ptas tau htau d hd M hMnorm
    alg.eventProbability
      {seed |
        ∀ x y : Fin d → ℂ,
          vectorNormSq x = d →
          vectorNormSq y = d →
          matrixQuarticForm M x y ≤
            matrixQuarticForm M
              (alg.run () seed).1 (alg.run () seed).2 + tau} ≥
      2 / 3 := by
  dsimp only
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  letI : MeasurableSpace ptas.Seed := ptas.seedMeasurableSpace
  letI : IsProbabilityMeasure ptas.seedMeasure := ptas.seedProbability
  let eta := effectiveAccuracy tau
  let gamma := directGamma d
  let kappa := (d : ℝ)
  let mesh := directMesh gamma kappa eta
  have hgamma : 0 ≤ gamma := by
    dsimp [gamma, directGamma]
    positivity
  have hkappa : 0 ≤ kappa := by positivity
  have heta : 0 < eta := effectiveAccuracy_pos htau
  have hmesh : 0 < mesh :=
    directMesh_pos hgamma hkappa heta
  let net := explicitComplexDiskNet kappa mesh hmesh
  letI := matrixCSPAlphabet_nonempty net (by
    dsimp [kappa]
    positivity)
  let csp :=
    matrixDenseMaxFourCSP net M
      (directPenalty gamma kappa eta) gamma
      hgamma hkappa (directPenalty_pos heta).le
      (directMatrix_entry_bound d hd M hMnorm)
  let base :=
    ptas.procedure (Fin d) (MatrixCSPAlphabet net) csp
      (directCSPError gamma kappa eta)
  let goodCSP : Set base.Seed :=
    {seed | ∀ assignment,
      csp.value assignment ≤
        csp.value (base.run () seed) +
          directCSPError gamma kappa eta}
  let goodOutput : Set base.Seed :=
    {seed |
      ∀ x y : Fin d → ℂ,
        vectorNormSq x = d →
        vectorNormSq y = d →
        matrixQuarticForm M x y ≤
          matrixQuarticForm M
            (normalizedCSPOutputX net (base.run () seed))
            (normalizedCSPOutputY net (base.run () seed)) + tau}
  have hsubset : goodCSP ⊆ goodOutput := by
    intro seed hseed
    intro x y hx hy
    have hxcoord : ∀ i, ‖x i‖ ≤ kappa := by
      intro i
      simpa [kappa] using
        norm_coordinate_le_card_of_scaledUnit
          (show x ∈ scaledUnitVectors (Fin d) by
            simpa [scaledUnitVectors] using hx) i
    have hycoord : ∀ i, ‖y i‖ ≤ kappa := by
      intro i
      simpa [kappa] using
        norm_coordinate_le_card_of_scaledUnit
          (show y ∈ scaledUnitVectors (Fin d) by
            simpa [scaledUnitVectors] using hy) i
    have hsuccessful :=
      successfulCSP_output_approximates_bounded
        net M (directPenalty gamma kappa eta) gamma
        (directCSPError gamma kappa eta)
        hgamma hkappa hmesh.le (directPenalty_pos heta)
        (directMatrix_entry_bound d hd M hMnorm)
        (base.run () seed) hseed x y
        (by simpa using hx) (by simpa using hy)
        hxcoord hycoord
    have herr :=
      directOptimizationError_le hgamma hkappa heta
    have hetaTau := (effectiveAccuracy_le_tau tau)
    dsimp [directOptimizationError] at herr
    linarith
  have hptas :=
    ptas.success (Fin d) (MatrixCSPAlphabet net) csp
      (directCSPError gamma kappa eta)
      (directCSPError_pos hgamma hkappa heta)
  change
    @Measure.real ptas.Seed ptas.seedMeasurableSpace
      ptas.seedMeasure goodOutput ≥ 2 / 3
  calc
    2 / 3 ≤
        @Measure.real ptas.Seed ptas.seedMeasurableSpace
          ptas.seedMeasure goodCSP := by
      have h23 : (2 / 3 : ℝ) ≤ 5 / 6 := by norm_num
      have hfive :
          5 / 6 ≤
            @Measure.real ptas.Seed ptas.seedMeasurableSpace
              ptas.seedMeasure goodCSP := by
        convert hptas using 1
        congr 1
      exact h23.trans hfive
    _ ≤
        @Measure.real ptas.Seed ptas.seedMeasurableSpace
          ptas.seedMeasure goodOutput :=
      measureReal_mono hsubset (measure_ne_top _ _)

end

end QuantumSep
