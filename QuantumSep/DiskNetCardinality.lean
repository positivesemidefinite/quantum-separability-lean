import QuantumSep.Discretization
import Mathlib.Algebra.Order.Floor.Ring

/-!
# An explicit polynomial-size net for the complex disk

The compactness construction in `Discretization` is enough for the analytic
rounding argument, but it does not expose the alphabet size needed by the
algorithmic reduction.  Here we use the square grid of mesh `ε / 2`, rounding
each real coordinate towards zero.  Coordinatewise contraction keeps the
rounded complex number inside the original disk.
-/

namespace QuantumSep

noncomputable section

/-- The number of nonnegative mesh points required in each coordinate. -/
def complexDiskGridRadius (kappa epsilon : ℝ) : ℕ :=
  Nat.ceil (2 * kappa / epsilon)

/-- Indices for two signs and two nonnegative coordinate magnitudes. -/
abbrev ComplexDiskGridIndex (kappa epsilon : ℝ) :=
  Bool × Bool ×
    Fin (complexDiskGridRadius kappa epsilon + 1) ×
    Fin (complexDiskGridRadius kappa epsilon + 1)

/-- A signed real grid coordinate. -/
def signedGridCoordinate (epsilon : ℝ) (positive : Bool) (n : ℕ) : ℝ :=
  if positive then (n : ℝ) * (epsilon / 2)
  else -((n : ℝ) * (epsilon / 2))

/-- The complex point represented by a grid index. -/
def indexedComplexDiskGridPoint (kappa epsilon : ℝ)
    (q : ComplexDiskGridIndex kappa epsilon) : ℂ :=
  ⟨signedGridCoordinate epsilon q.1 q.2.2.1,
    signedGridCoordinate epsilon q.2.1 q.2.2.2⟩

/-- The raw square grid. -/
def rawComplexDiskGrid (kappa epsilon : ℝ) : Finset ℂ :=
  Finset.univ.image (indexedComplexDiskGridPoint kappa epsilon)

/-- The internal grid obtained by retaining only points in the disk. -/
def complexDiskGrid (kappa epsilon : ℝ) : Finset ℂ :=
  (rawComplexDiskGrid kappa epsilon).filter (fun z => ‖z‖ ≤ kappa)

theorem complexDiskGrid_points_mem (kappa epsilon : ℝ) :
    ∀ z ∈ complexDiskGrid kappa epsilon, ‖z‖ ≤ kappa := by
  intro z hz
  exact (Finset.mem_filter.mp hz).2

/-- The explicit grid has at most four sign choices times the square of the
number of coordinate magnitudes. -/
theorem complexDiskGrid_card_le (kappa epsilon : ℝ) :
    (complexDiskGrid kappa epsilon).card ≤
      4 * (complexDiskGridRadius kappa epsilon + 1) ^ 2 := by
  calc
    (complexDiskGrid kappa epsilon).card
        ≤ (rawComplexDiskGrid kappa epsilon).card :=
      Finset.card_filter_le _ _
    _ ≤ Fintype.card (ComplexDiskGridIndex kappa epsilon) := by
      simpa [rawComplexDiskGrid] using
        (Finset.card_image_le :
          (Finset.univ.image
            (indexedComplexDiskGridPoint kappa epsilon)).card ≤
              Finset.univ.card)
    _ = 4 * (complexDiskGridRadius kappa epsilon + 1) ^ 2 := by
      simp [ComplexDiskGridIndex, pow_two]
      omega

/-- The nonnegative grid index used when rounding one real coordinate
towards zero. -/
def scalarGridMagnitude (epsilon x : ℝ) : ℕ :=
  Nat.floor (|x| / (epsilon / 2))

/-- Rounding a real coordinate towards zero on the mesh `epsilon / 2`. -/
def scalarGridRound (epsilon x : ℝ) : ℝ :=
  signedGridCoordinate epsilon (decide (0 ≤ x))
    (scalarGridMagnitude epsilon x)

private theorem scalarGridMagnitude_bounds
    {epsilon x : ℝ} (hepsilon : 0 < epsilon) :
    ((scalarGridMagnitude epsilon x : ℕ) : ℝ) * (epsilon / 2) ≤ |x| ∧
      |x| <
        (((scalarGridMagnitude epsilon x : ℕ) : ℝ) + 1) *
          (epsilon / 2) := by
  have hstep : 0 < epsilon / 2 := by positivity
  have hquot : 0 ≤ |x| / (epsilon / 2) := div_nonneg (abs_nonneg _) hstep.le
  have hfloor :
      ((scalarGridMagnitude epsilon x : ℕ) : ℝ) ≤
        |x| / (epsilon / 2) := by
    exact Nat.floor_le hquot
  have hnext :
      |x| / (epsilon / 2) <
        ((scalarGridMagnitude epsilon x : ℕ) : ℝ) + 1 := by
    simpa [scalarGridMagnitude] using
      (Nat.lt_floor_add_one (|x| / (epsilon / 2)))
  constructor
  · exact (le_div_iff₀ hstep).mp hfloor
  · exact (div_lt_iff₀ hstep).mp hnext

theorem abs_scalarGridRound_le
    {epsilon x : ℝ} (hepsilon : 0 < epsilon) :
    |scalarGridRound epsilon x| ≤ |x| := by
  obtain ⟨hlower, _hupper⟩ :=
    scalarGridMagnitude_bounds (x := x) hepsilon
  by_cases hx : 0 ≤ x
  · simpa [scalarGridRound, signedGridCoordinate, hx, abs_of_nonneg hx,
      abs_of_pos (show 0 < epsilon / 2 by positivity),
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity))]
      using hlower
  · have hxlt : x < 0 := lt_of_not_ge hx
    simpa [scalarGridRound, signedGridCoordinate, hx, abs_of_neg hxlt,
      abs_of_pos (show 0 < epsilon / 2 by positivity),
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity))]
      using hlower

theorem abs_sub_scalarGridRound_lt
    {epsilon x : ℝ} (hepsilon : 0 < epsilon) :
    |x - scalarGridRound epsilon x| < epsilon / 2 := by
  obtain ⟨hlower, hupper⟩ :=
    scalarGridMagnitude_bounds (x := x) hepsilon
  have hmesh_nonneg :
      0 ≤ ((scalarGridMagnitude epsilon x : ℕ) : ℝ) * (epsilon / 2) :=
    mul_nonneg (Nat.cast_nonneg _) (by positivity)
  by_cases hx : 0 ≤ x
  · have hdiff :
        0 ≤ x -
          ((scalarGridMagnitude epsilon x : ℕ) : ℝ) * (epsilon / 2) := by
      simpa [abs_of_nonneg hx] using
        sub_nonneg.mpr hlower
    rw [scalarGridRound, signedGridCoordinate]
    simp only [decide_eq_true_eq, if_pos hx]
    rw [abs_of_nonneg hdiff]
    rw [abs_of_nonneg hx] at hupper
    nlinarith
  · have hxlt : x < 0 := lt_of_not_ge hx
    have hdiff :
        x + ((scalarGridMagnitude epsilon x : ℕ) : ℝ) *
          (epsilon / 2) ≤ 0 := by
      have := hlower
      rw [abs_of_neg hxlt] at this
      linarith
    rw [scalarGridRound, signedGridCoordinate]
    simp only [decide_eq_true_eq, if_neg hx, sub_neg_eq_add]
    rw [abs_of_nonpos hdiff]
    rw [abs_of_neg hxlt] at hupper
    linarith

/-- The coordinate index of a point in the disk fits in the explicitly
chosen finite range. -/
theorem scalarGridMagnitude_le_radius
    {kappa epsilon x : ℝ}
    (hepsilon : 0 < epsilon) (hx : |x| ≤ kappa) :
    scalarGridMagnitude epsilon x ≤ complexDiskGridRadius kappa epsilon := by
  have hstep : 0 < epsilon / 2 := by positivity
  have hdiv :
      |x| / (epsilon / 2) ≤ kappa / (epsilon / 2) :=
    div_le_div_of_nonneg_right hx hstep.le
  have hfloor :
      Nat.floor (|x| / (epsilon / 2)) ≤
        Nat.floor (kappa / (epsilon / 2)) :=
    Nat.floor_mono hdiv
  have hceil :
      Nat.floor (kappa / (epsilon / 2)) ≤
        Nat.ceil (kappa / (epsilon / 2)) :=
    Nat.floor_le_ceil _
  have hratio :
      kappa / (epsilon / 2) = 2 * kappa / epsilon := by
    field_simp [ne_of_gt hepsilon]
  rw [scalarGridMagnitude, complexDiskGridRadius]
  simpa [hratio] using hfloor.trans hceil

/-- Coordinatewise rounding of a complex number towards zero. -/
def complexDiskGridRound (epsilon : ℝ) (z : ℂ) : ℂ :=
  ⟨scalarGridRound epsilon z.re, scalarGridRound epsilon z.im⟩

theorem complexDiskGridRound_norm_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (z : ℂ) :
    ‖complexDiskGridRound epsilon z‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [complexDiskGridRound]
  have hre := abs_scalarGridRound_le (epsilon := epsilon) (x := z.re) hepsilon
  have him := abs_scalarGridRound_le (epsilon := epsilon) (x := z.im) hepsilon
  nlinarith [sq_le_sq.mpr hre, sq_le_sq.mpr him]

theorem complexDiskGridRound_error_lt
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (z : ℂ) :
    ‖z - complexDiskGridRound epsilon z‖ < epsilon := by
  apply (sq_lt_sq₀ (norm_nonneg _) hepsilon.le).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [complexDiskGridRound, Complex.sub_re, Complex.sub_im]
  have hre :=
    abs_sub_scalarGridRound_lt (epsilon := epsilon) (x := z.re) hepsilon
  have him :=
    abs_sub_scalarGridRound_lt (epsilon := epsilon) (x := z.im) hepsilon
  have hstep : 0 ≤ epsilon / 2 := by positivity
  have hre_sq :
      |z.re - scalarGridRound epsilon z.re| ^ 2 < (epsilon / 2) ^ 2 :=
    (sq_lt_sq₀ (abs_nonneg _) hstep).mpr hre
  have him_sq :
      |z.im - scalarGridRound epsilon z.im| ^ 2 < (epsilon / 2) ^ 2 :=
    (sq_lt_sq₀ (abs_nonneg _) hstep).mpr him
  nlinarith [sq_abs (z.re - scalarGridRound epsilon z.re),
    sq_abs (z.im - scalarGridRound epsilon z.im)]

/-- The explicit rounded point is represented by one of the raw grid
indices whenever the original point lies in the disk. -/
theorem complexDiskGridRound_mem_raw
    {kappa epsilon : ℝ} (hepsilon : 0 < epsilon)
    {z : ℂ} (hz : ‖z‖ ≤ kappa) :
    complexDiskGridRound epsilon z ∈ rawComplexDiskGrid kappa epsilon := by
  have hre : |z.re| ≤ kappa :=
    (Complex.abs_re_le_norm z).trans hz
  have him : |z.im| ≤ kappa :=
    (Complex.abs_im_le_norm z).trans hz
  have hre_index :
      scalarGridMagnitude epsilon z.re <
        complexDiskGridRadius kappa epsilon + 1 :=
    Nat.lt_succ_of_le (scalarGridMagnitude_le_radius hepsilon hre)
  have him_index :
      scalarGridMagnitude epsilon z.im <
        complexDiskGridRadius kappa epsilon + 1 :=
    Nat.lt_succ_of_le (scalarGridMagnitude_le_radius hepsilon him)
  let ire : Fin (complexDiskGridRadius kappa epsilon + 1) :=
    ⟨scalarGridMagnitude epsilon z.re, hre_index⟩
  let iim : Fin (complexDiskGridRadius kappa epsilon + 1) :=
    ⟨scalarGridMagnitude epsilon z.im, him_index⟩
  let q : ComplexDiskGridIndex kappa epsilon :=
    (decide (0 ≤ z.re), decide (0 ≤ z.im), ire, iim)
  rw [rawComplexDiskGrid]
  refine Finset.mem_image.mpr ⟨q, Finset.mem_univ _, ?_⟩
  apply Complex.ext
  · simp [indexedComplexDiskGridPoint, complexDiskGridRound,
      scalarGridRound, q, ire]
  · simp [indexedComplexDiskGridPoint, complexDiskGridRound,
      scalarGridRound, q, iim]

theorem complexDiskGridRound_mem
    {kappa epsilon : ℝ} (hepsilon : 0 < epsilon)
    {z : ℂ} (hz : ‖z‖ ≤ kappa) :
    complexDiskGridRound epsilon z ∈ complexDiskGrid kappa epsilon := by
  rw [complexDiskGrid, Finset.mem_filter]
  exact ⟨complexDiskGridRound_mem_raw hepsilon hz,
    (complexDiskGridRound_norm_le hepsilon z).trans hz⟩

/-- The explicit internal grid is an `epsilon`-net of the disk. -/
def explicitComplexDiskNet
    (kappa epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ComplexDiskNet kappa epsilon where
  points := complexDiskGrid kappa epsilon
  points_mem := complexDiskGrid_points_mem kappa epsilon
  approximates := by
    intro z hz
    exact ⟨complexDiskGridRound epsilon z,
      complexDiskGridRound_mem hepsilon hz,
      complexDiskGridRound_error_lt hepsilon z⟩

/-- A complex disk has an internal `epsilon`-net with an explicit,
dimension-independent polynomial cardinality bound. -/
theorem exists_complexDiskNet_card_le
    (kappa epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ net : ComplexDiskNet kappa epsilon,
      net.points.card ≤
        4 * (Nat.ceil (2 * kappa / epsilon) + 1) ^ 2 := by
  refine ⟨explicitComplexDiskNet kappa epsilon hepsilon, ?_⟩
  exact complexDiskGrid_card_le kappa epsilon

end

end QuantumSep
