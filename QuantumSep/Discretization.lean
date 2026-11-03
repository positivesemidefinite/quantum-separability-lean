import QuantumSep.MatrixObjective
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Finite complex alphabets and coordinatewise rounding

Compactness of the closed complex disk supplies a finite alphabet independent
of the matrix dimension.  The selected rounding map stays inside the disk and
is then connected to the concrete penalized-objective Lipschitz theorem.
-/

namespace QuantumSep

open Metric Set

noncomputable section

/-- A finite `epsilon`-net whose centers remain inside the closed complex
disk of radius `kappa`. -/
structure ComplexDiskNet (kappa epsilon : ℝ) where
  points : Finset ℂ
  points_mem : ∀ z ∈ points, ‖z‖ ≤ kappa
  approximates : ∀ z : ℂ, ‖z‖ ≤ kappa →
    ∃ w ∈ points, ‖z - w‖ < epsilon

/-- Every closed complex disk has a finite internal net at positive scale. -/
theorem exists_complexDiskNet (kappa epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Nonempty (ComplexDiskNet kappa epsilon) := by
  let s : Set ℂ := Metric.closedBall 0 kappa
  obtain ⟨t, hts, htfinite, hcover⟩ :=
    (isCompact_closedBall (0 : ℂ) kappa).finite_cover_balls hepsilon
  let points : Finset ℂ := htfinite.toFinset
  refine ⟨{
    points := points
    points_mem := ?_
    approximates := ?_
  }⟩
  · intro z hz
    have hzt : z ∈ t := by
      simpa [points] using hz
    have hzs : z ∈ s := hts hzt
    simpa [s, Metric.mem_closedBall, dist_zero_right] using hzs
  · intro z hz
    have hzs : z ∈ s := by
      simpa [s, Metric.mem_closedBall, dist_zero_right] using hz
    have hzcover := hcover hzs
    simp only [Set.mem_iUnion] at hzcover
    obtain ⟨w, hwcover⟩ := hzcover
    obtain ⟨hwt, hball⟩ := hwcover
    refine ⟨w, ?_, ?_⟩
    · simpa [points] using hwt
    · simpa [Metric.mem_ball, dist_eq_norm] using hball

/-- A choice of a nearby alphabet point; outside the disk it defaults to
zero, though all later uses supply the disk hypothesis. -/
def ComplexDiskNet.round {kappa epsilon : ℝ}
    (net : ComplexDiskNet kappa epsilon) (z : ℂ) : ℂ :=
  if hz : ‖z‖ ≤ kappa then
    Classical.choose (net.approximates z hz)
  else 0

theorem ComplexDiskNet.round_mem {kappa epsilon : ℝ}
    (net : ComplexDiskNet kappa epsilon) {z : ℂ}
    (hz : ‖z‖ ≤ kappa) :
    net.round z ∈ net.points := by
  rw [ComplexDiskNet.round, dif_pos hz]
  exact (Classical.choose_spec (net.approximates z hz)).1

theorem ComplexDiskNet.round_norm_le {kappa epsilon : ℝ}
    (net : ComplexDiskNet kappa epsilon) {z : ℂ}
    (hz : ‖z‖ ≤ kappa) :
    ‖net.round z‖ ≤ kappa :=
  net.points_mem _ (net.round_mem hz)

theorem ComplexDiskNet.norm_sub_round_lt {kappa epsilon : ℝ}
    (net : ComplexDiskNet kappa epsilon) {z : ℂ}
    (hz : ‖z‖ ≤ kappa) :
    ‖z - net.round z‖ < epsilon := by
  rw [ComplexDiskNet.round, dif_pos hz]
  exact (Classical.choose_spec (net.approximates z hz)).2

/-- Coordinatewise rounding of a vector into a finite complex alphabet. -/
def ComplexDiskNet.roundVector {kappa epsilon : ℝ}
    (net : ComplexDiskNet kappa epsilon)
    {ι : Type*} (x : ι → ℂ) : ι → ℂ :=
  fun i => net.round (x i)

theorem ComplexDiskNet.roundVector_mem {kappa epsilon : ℝ}
    (net : ComplexDiskNet kappa epsilon)
    {ι : Type*} (x : ι → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ kappa) :
    ∀ i, net.roundVector x i ∈ net.points :=
  fun i => net.round_mem (hx i)

theorem ComplexDiskNet.roundVector_norm_le {kappa epsilon : ℝ}
    (net : ComplexDiskNet kappa epsilon)
    {ι : Type*} (x : ι → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ kappa) :
    ∀ i, ‖net.roundVector x i‖ ≤ kappa :=
  fun i => net.round_norm_le (hx i)

theorem ComplexDiskNet.roundVector_error_le {kappa epsilon : ℝ}
    (net : ComplexDiskNet kappa epsilon)
    {ι : Type*} (x : ι → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ kappa) :
    ∀ i, ‖x i - net.roundVector x i‖ ≤ epsilon :=
  fun i => (net.norm_sub_round_lt (hx i)).le

/-- Rounding two bounded vectors into any chosen disk net incurs the concrete
Lipschitz loss. -/
theorem matrixPenalizedObjective_roundVector
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {kappa epsilon : ℝ}
    (net : ComplexDiskNet kappa epsilon)
    (M : BipartiteMatrix ι) (penalty gamma : ℝ)
    (x y : ι → ℂ)
    (hgamma : 0 ≤ gamma) (hkappa : 0 ≤ kappa)
    (hepsilon : 0 ≤ epsilon) (hpenalty : 0 ≤ penalty)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (hx : ∀ i, ‖x i‖ ≤ kappa)
    (hy : ∀ i, ‖y i‖ ≤ kappa) :
    |matrixPenalizedObjective M penalty x y -
        matrixPenalizedObjective M penalty
          (net.roundVector x) (net.roundVector y)| ≤
      4 * gamma * kappa ^ 3 * epsilon +
        8 * penalty * kappa * (kappa ^ 2 + 1) * epsilon := by
  exact abs_matrixPenalizedObjective_sub_le
    M penalty x y (net.roundVector x) (net.roundVector y)
    gamma kappa epsilon hgamma hkappa hepsilon hpenalty hentry
    hx hy (net.roundVector_norm_le x hx) (net.roundVector_norm_le y hy)
    (net.roundVector_error_le x hx) (net.roundVector_error_le y hy)

/-- For the manuscript's particular mesh, coordinatewise net rounding loses
at most `η/4` in the actual penalized matrix objective. -/
theorem matrixPenalizedObjective_roundVector_mesh
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (M : BipartiteMatrix ι) (penalty gamma kappa η : ℝ)
    (net : ComplexDiskNet kappa
      (η /
        (16 * gamma * kappa ^ 3 +
          32 * penalty * kappa * (kappa ^ 2 + 1))))
    (x y : ι → ℂ)
    (hgamma : 0 ≤ gamma) (hkappa : 0 < kappa)
    (hη : 0 ≤ η) (hpenalty : 0 < penalty)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (hx : ∀ i, ‖x i‖ ≤ kappa)
    (hy : ∀ i, ‖y i‖ ≤ kappa) :
    |matrixPenalizedObjective M penalty x y -
        matrixPenalizedObjective M penalty
          (net.roundVector x) (net.roundVector y)| ≤ η / 4 := by
  exact abs_matrixPenalizedObjective_mesh_choice
    M penalty x y (net.roundVector x) (net.roundVector y)
    gamma kappa η hgamma hkappa hη hpenalty hentry hx hy
    (net.roundVector_norm_le x hx) (net.roundVector_norm_le y hy)
    (net.roundVector_error_le x hx) (net.roundVector_error_le y hy)

end

end QuantumSep
