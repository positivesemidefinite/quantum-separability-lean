import QuantumSep.BoundedAmplitude
import QuantumSep.PaperInterfaces
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact

/-!
# Compact product-state optimization

The manuscript's scaled unit vectors form a nonempty compact set, and the
quartic matrix objective is continuous.  Consequently the mathematical
product-state optimum is attained.  This is independent of the algorithmic
approximation theorem.
-/

open scoped BigOperators

namespace QuantumSep

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Scaled unit vectors, in the manuscript's normalization
`∑ i, ‖x i‖² = |ι|`. -/
def scaledUnitVectors (ι : Type*) [Fintype ι] : Set (ι → ℂ) :=
  {x | vectorNormSq x = Fintype.card ι}

/-- The constant-one vector witnesses nonemptiness of the scaled unit sphere. -/
theorem scaledUnitVectors_nonempty :
    (scaledUnitVectors ι).Nonempty := by
  refine ⟨fun _ => 1, ?_⟩
  simp [scaledUnitVectors, vectorNormSq]

/-- The squared Euclidean norm used by the development is continuous. -/
theorem continuous_vectorNormSq :
    Continuous (vectorNormSq : (ι → ℂ) → ℝ) := by
  unfold vectorNormSq
  apply continuous_finset_sum
  intro i _hi
  change Continuous (fun a : ι → ℂ =>
    (a i).re * (a i).re + (a i).im * (a i).im)
  exact
    (((Complex.continuous_re.comp (continuous_apply i)).mul
      (Complex.continuous_re.comp (continuous_apply i))).add
      ((Complex.continuous_im.comp (continuous_apply i)).mul
      (Complex.continuous_im.comp (continuous_apply i))))

/-- Every coordinate of a scaled unit vector is bounded by the dimension. -/
theorem norm_coordinate_le_card_of_scaledUnit
    {x : ι → ℂ} (hx : x ∈ scaledUnitVectors ι) (i : ι) :
    ‖x i‖ ≤ Fintype.card ι := by
  have hterm :
      Complex.normSq (x i) ≤ vectorNormSq x := by
    unfold vectorNormSq
    exact Finset.single_le_sum
      (fun j _hj => Complex.normSq_nonneg (x j))
      (Finset.mem_univ i)
  have hcardOne : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hsq :
      ‖x i‖ ^ 2 ≤ (Fintype.card ι : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa [scaledUnitVectors] using hx ▸ hterm
  nlinarith [norm_nonneg (x i)]

/-- The scaled unit sphere is compact. -/
theorem isCompact_scaledUnitVectors :
    IsCompact (scaledUnitVectors ι) := by
  let box : Set (ι → ℂ) :=
    Set.pi Set.univ
      (fun _ => Metric.closedBall (0 : ℂ) (Fintype.card ι))
  have hbox : IsCompact box := by
    dsimp [box]
    exact isCompact_univ_pi
      (fun _ => isCompact_closedBall (0 : ℂ) (Fintype.card ι))
  have hclosed : IsClosed (scaledUnitVectors ι) := by
    exact isClosed_eq continuous_vectorNormSq continuous_const
  apply hbox.of_isClosed_subset hclosed
  intro x hx
  simp only [box, Set.mem_pi, Set.mem_univ, forall_const]
  intro i
  simpa [Metric.mem_closedBall, dist_zero_right] using
    norm_coordinate_le_card_of_scaledUnit hx i

/-- One concrete quartic summand is continuous in both vector arguments. -/
theorem continuous_quarticSummand
    (M : BipartiteMatrix ι) (a b c e : ι) :
    Continuous (fun p : (ι → ℂ) × (ι → ℂ) =>
      quarticSummand M p.1 p.2 a b c e) := by
  unfold quarticSummand
  fun_prop

/-- The concrete quartic objective is continuous in both vector arguments. -/
theorem continuous_matrixQuarticForm
    (M : BipartiteMatrix ι) :
    Continuous (fun p : (ι → ℂ) × (ι → ℂ) =>
      matrixQuarticForm M p.1 p.2) := by
  unfold matrixQuarticForm
  apply Continuous.div_const
  apply continuous_finset_sum
  intro a _ha
  apply continuous_finset_sum
  intro b _hb
  apply continuous_finset_sum
  intro c _hc
  apply continuous_finset_sum
  intro e _he
  exact continuous_quarticSummand M a b c e

/-- Every continuous real function on a pair of scaled unit spheres attains
its maximum.  Keeping this theorem abstract prevents the extreme-value proof
from repeatedly unfolding the fourfold matrix sum. -/
theorem exists_scaledUnit_pair_maximizer
    (f : ((ι → ℂ) × (ι → ℂ)) → ℝ)
    (hf : Continuous f) :
    ∃ p,
      p.1 ∈ scaledUnitVectors ι ∧
      p.2 ∈ scaledUnitVectors ι ∧
      ∀ q,
        q.1 ∈ scaledUnitVectors ι →
        q.2 ∈ scaledUnitVectors ι →
        f q ≤ f p := by
  let S : Set ((ι → ℂ) × (ι → ℂ)) :=
    scaledUnitVectors ι ×ˢ scaledUnitVectors ι
  have hS : IsCompact S :=
    isCompact_scaledUnitVectors.prod isCompact_scaledUnitVectors
  have hSne : S.Nonempty :=
    scaledUnitVectors_nonempty.prod scaledUnitVectors_nonempty
  obtain ⟨p, hpS, hpmax⟩ :=
    hS.exists_isMaxOn hSne hf.continuousOn
  refine ⟨p, hpS.1, hpS.2, ?_⟩
  intro q hq1 hq2
  exact hpmax ⟨hq1, hq2⟩

/-- The product-state quartic objective attains an exact maximum on the
scaled unit sphere. -/
theorem exists_scaledUnit_quartic_maximizer
    (M : BipartiteMatrix ι) :
    ∃ x y,
      x ∈ scaledUnitVectors ι ∧
      y ∈ scaledUnitVectors ι ∧
      ∀ u v,
        u ∈ scaledUnitVectors ι →
        v ∈ scaledUnitVectors ι →
        matrixQuarticForm M u v ≤ matrixQuarticForm M x y := by
  obtain ⟨p, hp1, hp2, hpmax⟩ :=
    exists_scaledUnit_pair_maximizer
      (fun p => matrixQuarticForm M p.1 p.2)
      (continuous_matrixQuarticForm M)
  refine ⟨p.1, p.2, hp1, hp2, ?_⟩
  intro u v hu hv
  exact hpmax (u, v) hu hv

/-- In particular, an additive approximate maximizer exists for every
nonnegative accuracy. -/
theorem productApproximationSpec_matrixQuarticForm
    (M : BipartiteMatrix ι) (τ : ℝ) (hτ : 0 ≤ τ) :
    ProductApproximationSpec
      (matrixQuarticForm M)
      (fun x => x ∈ scaledUnitVectors ι)
      τ := by
  obtain ⟨x, y, hx, hy, hmax⟩ :=
    exists_scaledUnit_quartic_maximizer M
  refine ⟨x, y, hx, hy, ?_⟩
  intro u v hu hv
  linarith [hmax u v hu hv]

end

end QuantumSep
