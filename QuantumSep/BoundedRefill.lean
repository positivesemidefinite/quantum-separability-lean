import QuantumSep.Refill
import QuantumSep.ProbabilityAmplification

/-!
# Bounded refill with a good objective value

This module combines the exact refill expectation, Chebyshev's inequality,
the product-space union bound, and a finite conditional first-moment argument.
-/

open scoped BigOperators ComplexConjugate ENNReal

open MeasureTheory ProbabilityTheory Set

namespace QuantumSep

noncomputable section

/-- There is a simultaneous refill outcome with both squared norms close to
`d` and quartic value close to its exact expectation. -/
theorem exists_refill_pair_good_norms_and_value
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : BipartiteMatrix ι) (u v : ι → ℂ)
    (gamma sigma t ε : ℝ)
    (hgamma : 0 ≤ gamma) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) (hε : 0 < ε)
    (hnormU : vectorNormSq u ≤ Fintype.card ι)
    (hnormV : vectorNormSq v ≤ Fintype.card ι)
    (hu : ∀ i, ‖u i‖ ≤ sigma)
    (hv : ∀ i, ‖v i‖ ≤ sigma)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤
        gamma / cardR (ι := ι) ^ 2)
    (htrace0 : partialTrace0 M = 0)
    (htrace1 : partialTrace1 M = 0)
    (hdimension : 8 < t ^ 2 * Fintype.card ι) :
    let r := 8 / (t ^ 2 * Fintype.card ι)
    let B := gamma * (sigma + 1) ^ 4
    ∃ ξ ζ,
      |vectorNormSq
          (refillVector u (refillAmplitude u) ξ) -
            Fintype.card ι| ≤ t * Fintype.card ι ∧
      |vectorNormSq
          (refillVector v (refillAmplitude v) ζ) -
            Fintype.card ι| ≤ t * Fintype.card ι ∧
      matrixQuarticForm M
          (refillVector u (refillAmplitude u) ξ)
          (refillVector v (refillAmplitude v) ζ) >
        matrixQuarticForm M u v -
          (2 * B * r / (1 - r) + ε) := by
  dsimp only
  let μ := phaseVectorMeasure ι
  let failureU : Set (ι → Fin 4) := {ξ |
    t * Fintype.card ι <
      |vectorNormSq
          (refillVector u (refillAmplitude u) ξ) -
        Fintype.card ι|}
  let failureV : Set (ι → Fin 4) := {ζ |
    t * Fintype.card ι <
      |vectorNormSq
          (refillVector v (refillAmplitude v) ζ) -
        Fintype.card ι|}
  let failure : Set ((ι → Fin 4) × (ι → Fin 4)) :=
    (failureU ×ˢ Set.univ) ∪ (Set.univ ×ˢ failureV)
  let objective : ((ι → Fin 4) × (ι → Fin 4)) → ℝ :=
    fun phases =>
      matrixQuarticForm M
        (refillVector u (refillAmplitude u) phases.1)
        (refillVector v (refillAmplitude v) phases.2)
  let r : ℝ := 8 / (t ^ 2 * Fintype.card ι)
  let B : ℝ := gamma * (sigma + 1) ^ 4
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hden : 0 < t ^ 2 * (Fintype.card ι : ℝ) := by
    positivity
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact (div_lt_one hden).2 hdimension
  have hU :
      μ.real failureU ≤
        4 / (t ^ 2 * Fintype.card ι) := by
    exact refill_norm_failure_measureReal_le
      u (refillAmplitude u) t ht
        (refillAmplitude_sq_le_one u) hnormU
        (refillAmplitude_balance u hnormU)
  have hV :
      μ.real failureV ≤
        4 / (t ^ 2 * Fintype.card ι) := by
    exact refill_norm_failure_measureReal_le
      v (refillAmplitude v) t ht
        (refillAmplitude_sq_le_one v) hnormV
        (refillAmplitude_balance v hnormV)
  have hfailure :
      (μ.prod μ).real failure ≤ r := by
    calc
      (μ.prod μ).real failure ≤
          μ.real failureU + μ.real failureV :=
        measureReal_prod_failure_union_le μ μ failureU failureV
      _ ≤ 4 / (t ^ 2 * Fintype.card ι) +
          4 / (t ^ 2 * Fintype.card ι) :=
        add_le_add hU hV
      _ = r := by
        dsimp [r]
        ring
  have hK : 0 ≤ sigma + 1 := by linarith
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hbound : ∀ phases, |objective phases| ≤ B := by
    intro phases
    dsimp [objective, B]
    apply abs_matrixQuarticForm_le_of_coordinate_bound
      M _ _ gamma (sigma + 1) hgamma hK hentry
    · exact refillVector_norm_le u sigma phases.1 hu
    · exact refillVector_norm_le v sigma phases.2 hv
  have hobjIntegrable :
      Integrable objective (μ.prod μ) := by
    rw [← integrableOn_univ]
    exact IntegrableOn.of_finite Set.finite_univ
  have hexpect :
      (∫ phases, objective phases ∂μ.prod μ) =
        matrixQuarticForm M u v := by
    rw [MeasureTheory.integral_prod objective hobjIntegrable]
    exact integral_matrixQuarticForm_refill_eq
      M u v (refillAmplitude u) (refillAmplitude v)
        htrace0 htrace1
  obtain ⟨⟨ξ, ζ⟩, hgood, hvalue⟩ :=
    exists_good_value_of_expectation
      (μ.prod μ) objective failure B
      (matrixQuarticForm M u v) r ε
      hB hr0 hr1 hε hbound hexpect hfailure
  refine ⟨ξ, ζ, ?_, ?_, ?_⟩
  · have hnot : ξ ∉ failureU := by
      intro hξ
      exact hgood (Or.inl ⟨hξ, Set.mem_univ ζ⟩)
    exact le_of_not_gt hnot
  · have hnot : ζ ∉ failureV := by
      intro hζ
      exact hgood (Or.inr ⟨Set.mem_univ ξ, hζ⟩)
    exact le_of_not_gt hnot
  · exact hvalue

end

end QuantumSep
