import QuantumSep.BoundedRefill

/-!
# Renormalization to squared norm `d`

These lemmas formalize the last deterministic step of the bounded-amplitude
argument, including homogeneity of the quartic form and the `8t` loss.
-/

open scoped BigOperators ComplexConjugate

namespace QuantumSep

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def scaleVector (r : ℝ) (x : ι → ℂ) : ι → ℂ :=
  fun i => (r : ℂ) * x i

theorem vectorNormSq_scaleVector (r : ℝ) (x : ι → ℂ) :
    vectorNormSq (scaleVector r x) = r ^ 2 * vectorNormSq x := by
  unfold vectorNormSq scaleVector
  simp_rw [Complex.normSq_mul, Complex.normSq_ofReal]
  rw [Finset.mul_sum]
  congr 1
  ring

theorem norm_scaleVector (r : ℝ) (x : ι → ℂ) (i : ι) :
    ‖scaleVector r x i‖ = |r| * ‖x i‖ := by
  simp [scaleVector]

def normalizeVectorToCard (x : ι → ℂ) : ι → ℂ :=
  scaleVector
    (1 / Real.sqrt (vectorNormSq x / Fintype.card ι)) x

theorem vectorNormSq_nonneg (x : ι → ℂ) :
    0 ≤ vectorNormSq x := by
  unfold vectorNormSq
  exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (x i)

theorem vectorNormSq_eq_zero_iff (x : ι → ℂ) :
    vectorNormSq x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    funext i
    have hi :
        Complex.normSq (x i) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Complex.normSq_nonneg (x j))).mp hx
          i (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp hi
  · rintro rfl
    simp [vectorNormSq]

/-- Total normalization: a zero vector is replaced by the constant-one
scaled unit vector. -/
def normalizeVectorOrOne (x : ι → ℂ) : ι → ℂ :=
  if 0 < vectorNormSq x then normalizeVectorToCard x else fun _ => 1

@[simp] theorem matrixQuarticForm_zero_left
    (M : BipartiteMatrix ι) (y : ι → ℂ) :
    matrixQuarticForm M 0 y = 0 := by
  simp [matrixQuarticForm, quarticSummand]

@[simp] theorem matrixQuarticForm_zero_right
    (M : BipartiteMatrix ι) (x : ι → ℂ) :
    matrixQuarticForm M x 0 = 0 := by
  simp [matrixQuarticForm, quarticSummand]

theorem vectorNormSq_normalizeVectorToCard
    (x : ι → ℂ) (hnorm : 0 < vectorNormSq x) :
    vectorNormSq (normalizeVectorToCard x) = Fintype.card ι := by
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hratio : 0 < vectorNormSq x / Fintype.card ι :=
    div_pos hnorm hd
  unfold normalizeVectorToCard
  rw [vectorNormSq_scaleVector]
  rw [div_pow, one_pow, Real.sq_sqrt hratio.le]
  field_simp [ne_of_gt hratio, ne_of_gt hd]

theorem vectorNormSq_normalizeVectorOrOne (x : ι → ℂ) :
    vectorNormSq (normalizeVectorOrOne x) = Fintype.card ι := by
  rw [normalizeVectorOrOne]
  split_ifs with hx
  · exact vectorNormSq_normalizeVectorToCard x hx
  · simp [vectorNormSq]

theorem quarticSummand_scaleVector
    (M : BipartiteMatrix ι) (x y : ι → ℂ)
    (r s : ℝ) (a b c e : ι) :
    quarticSummand M (scaleVector r x) (scaleVector s y) a b c e =
      r ^ 2 * s ^ 2 * quarticSummand M x y a b c e := by
  unfold quarticSummand scaleVector
  have hxstar :
      star ((r : ℂ) * x a) = (r : ℂ) * star (x a) := by
    change (starRingEnd ℂ) ((r : ℂ) * x a) = _
    rw [map_mul, RCLike.star_def, Complex.conj_ofReal]
  have hystar :
      star ((s : ℂ) * y c) = (s : ℂ) * star (y c) := by
    change (starRingEnd ℂ) ((s : ℂ) * y c) = _
    rw [map_mul, RCLike.star_def, Complex.conj_ofReal]
  have hreal (q : ℝ) (z : ℂ) :
      ((q : ℂ) * z).re = q * z.re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hxstar, hystar]
  rw [show
    M (a, c) (b, e) * ((r : ℂ) * star (x a)) *
        ((r : ℂ) * x b) * ((s : ℂ) * star (y c)) *
        ((s : ℂ) * y e) =
      ((r ^ 2 * s ^ 2 : ℝ) : ℂ) *
        (M (a, c) (b, e) * star (x a) * x b *
          star (y c) * y e) by
    push_cast
    ring]
  rw [hreal]

theorem matrixQuarticForm_scaleVector
    (M : BipartiteMatrix ι) (x y : ι → ℂ)
    (r s : ℝ) :
    matrixQuarticForm M (scaleVector r x) (scaleVector s y) =
      r ^ 2 * s ^ 2 * matrixQuarticForm M x y := by
  unfold matrixQuarticForm
  simp_rw [quarticSummand_scaleVector]
  simp_rw [← Finset.mul_sum]
  ring

theorem matrixQuarticForm_normalizeVectorToCard
    (M : BipartiteMatrix ι) (x y : ι → ℂ)
    (hx : 0 < vectorNormSq x) (hy : 0 < vectorNormSq y) :
    matrixQuarticForm M
        (normalizeVectorToCard x) (normalizeVectorToCard y) =
      (1 / (vectorNormSq x / Fintype.card ι)) *
        (1 / (vectorNormSq y / Fintype.card ι)) *
          matrixQuarticForm M x y := by
  unfold normalizeVectorToCard
  rw [matrixQuarticForm_scaleVector]
  rw [div_pow, one_pow, div_pow, one_pow]
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [Real.sq_sqrt (div_pos hx hd).le,
    Real.sq_sqrt (div_pos hy hd).le]

/-- Exact homogeneity identity for the total normalization, including both
zero-vector fallback branches. -/
theorem matrixQuarticForm_eq_normRatios_mul_normalizeVectorOrOne
    (M : BipartiteMatrix ι) (x y : ι → ℂ) :
    matrixQuarticForm M x y =
      (vectorNormSq x / Fintype.card ι) *
        (vectorNormSq y / Fintype.card ι) *
          matrixQuarticForm M
            (normalizeVectorOrOne x) (normalizeVectorOrOne y) := by
  by_cases hx : 0 < vectorNormSq x
  · by_cases hy : 0 < vectorNormSq y
    · simp only [normalizeVectorOrOne, if_pos hx, if_pos hy]
      rw [matrixQuarticForm_normalizeVectorToCard M x y hx hy]
      have hd : (Fintype.card ι : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      have hrx : vectorNormSq x / Fintype.card ι ≠ 0 :=
        ne_of_gt (div_pos hx (by exact_mod_cast Fintype.card_pos))
      have hry : vectorNormSq y / Fintype.card ι ≠ 0 :=
        ne_of_gt (div_pos hy (by exact_mod_cast Fintype.card_pos))
      field_simp
    · have hy0 : vectorNormSq y = 0 :=
        le_antisymm (le_of_not_gt hy) (vectorNormSq_nonneg y)
      have hyv : y = 0 := (vectorNormSq_eq_zero_iff y).mp hy0
      rw [hyv, matrixQuarticForm_zero_right]
      simp [vectorNormSq]
  · have hx0 : vectorNormSq x = 0 :=
      le_antisymm (le_of_not_gt hx) (vectorNormSq_nonneg x)
    have hxv : x = 0 := (vectorNormSq_eq_zero_iff x).mp hx0
    rw [hxv, matrixQuarticForm_zero_left]
    simp [vectorNormSq]

theorem normRatio_deviation_of_raw
    (x : ι → ℂ) (t : ℝ)
    (hdev :
      |vectorNormSq x - Fintype.card ι| ≤
        t * Fintype.card ι) :
    |vectorNormSq x / Fintype.card ι - 1| ≤ t := by
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [show vectorNormSq x / Fintype.card ι - 1 =
      (vectorNormSq x - Fintype.card ι) /
        Fintype.card ι by
    field_simp [ne_of_gt hd]]
  rw [abs_div, abs_of_pos hd]
  exact (div_le_iff₀ hd).2 hdev

theorem vectorNormSq_pos_of_raw_deviation
    (x : ι → ℂ) (t : ℝ)
    (ht : t < 1)
    (hdev :
      |vectorNormSq x - Fintype.card ι| ≤
        t * Fintype.card ι) :
    0 < vectorNormSq x := by
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hratioDev := normRatio_deviation_of_raw x t hdev
  have hratio :
      0 < vectorNormSq x / Fintype.card ι :=
    one_sub_pos_of_deviation ht hratioDev
  rcases div_pos_iff.mp hratio with hpos | hneg
  · exact hpos.1
  · linarith [hneg.2]

/-- Under `t ≤ 1/2`, renormalization increases every coordinate by a factor
of at most two. -/
theorem norm_normalizeVectorToCard_le_two_mul
    (x : ι → ℂ) (K t : ℝ)
    (_ht0 : 0 ≤ t) (ht : t ≤ 1 / 2)
    (hcoord : ∀ i, ‖x i‖ ≤ K)
    (hdev :
      |vectorNormSq x - Fintype.card ι| ≤
        t * Fintype.card ι)
    (i : ι) :
    ‖normalizeVectorToCard x i‖ ≤ 2 * K := by
  let ratio := vectorNormSq x / Fintype.card ι
  have hratioDev : |ratio - 1| ≤ t :=
    normRatio_deviation_of_raw x t hdev
  have hratioLower : 1 - t ≤ ratio := by
    rw [abs_le] at hratioDev
    linarith
  have hratioHalf : 1 / 2 ≤ ratio := by linarith
  have hratioPos : 0 < ratio := by linarith
  have hsqrtSq : Real.sqrt ratio ^ 2 = ratio :=
    Real.sq_sqrt hratioPos.le
  have hsqrtHalf : 1 / 2 ≤ Real.sqrt ratio := by
    have hsqrt0 := Real.sqrt_nonneg ratio
    nlinarith
  have hsqrtPos : 0 < Real.sqrt ratio := by linarith
  have hfactor : 1 / Real.sqrt ratio ≤ 2 := by
    apply (div_le_iff₀ hsqrtPos).2
    nlinarith
  unfold normalizeVectorToCard
  rw [norm_scaleVector, abs_of_nonneg (div_nonneg (by norm_num)
    (Real.sqrt_nonneg _))]
  calc
    (1 / Real.sqrt ratio) * ‖x i‖ ≤
        2 * ‖x i‖ := by
      gcongr
    _ ≤ 2 * K :=
      mul_le_mul_of_nonneg_left (hcoord i) (by norm_num)

/-- The exact homogeneity and inverse-product estimate imply the manuscript's
`8t B` renormalization loss. -/
theorem matrixQuarticForm_normalize_lower_bound
    (M : BipartiteMatrix ι) (x y : ι → ℂ)
    (t B : ℝ)
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2)
    (hdevX :
      |vectorNormSq x - Fintype.card ι| ≤
        t * Fintype.card ι)
    (hdevY :
      |vectorNormSq y - Fintype.card ι| ≤
        t * Fintype.card ι)
    (hQ : |matrixQuarticForm M x y| ≤ B) :
    matrixQuarticForm M (normalizeVectorToCard x)
        (normalizeVectorToCard y) ≥
      matrixQuarticForm M x y - 8 * t * B := by
  have htlt : t < 1 := by linarith
  have hxPos := vectorNormSq_pos_of_raw_deviation x t htlt hdevX
  have hyPos := vectorNormSq_pos_of_raw_deviation y t htlt hdevY
  let rx := vectorNormSq x / Fintype.card ι
  let ry := vectorNormSq y / Fintype.card ι
  have hrx := normRatio_deviation_of_raw x t hdevX
  have hry := normRatio_deviation_of_raw y t hdevY
  have hinv :
      |1 / (rx * ry) - 1| ≤ 8 * t :=
    inverse_product_deviation ht0 ht hrx hry
  rw [matrixQuarticForm_normalizeVectorToCard M x y hxPos hyPos]
  have hfactor :
      (1 / rx) * (1 / ry) = 1 / (rx * ry) := by
    ring
  rw [hfactor]
  have habs :
      |1 / (rx * ry) * matrixQuarticForm M x y -
          matrixQuarticForm M x y| ≤
        8 * t * B := by
    rw [show
      1 / (rx * ry) * matrixQuarticForm M x y -
          matrixQuarticForm M x y =
        (1 / (rx * ry) - 1) *
          matrixQuarticForm M x y by ring]
    rw [abs_mul]
    exact mul_le_mul hinv hQ (abs_nonneg _) (by positivity)
  linarith [neg_le_of_abs_le habs]

end

end QuantumSep
