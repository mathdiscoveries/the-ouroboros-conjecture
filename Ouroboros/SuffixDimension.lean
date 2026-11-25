module
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic
public import Ouroboros.Defs
public import Ouroboros.BasinOne

@[expose] public section

/-!
# Section 7 (Corollary `cor:suffix-dimension`): Exact Hausdorff and box dimension in every base

Formalizes Corollary `cor:suffix-dimension` of the Ouroboros paper:
for every integer base `b ≥ 2` factored as `b = 2^t * u` (`u` odd), letting `λ = 1 / a*` be the
unique positive root of `λ^4 = λ^3 + 2`, the reversed base-`b` suffix closure `ℰ_b ⊂ [0, 1]` of
the basin `ℬ_1` has exact Hausdorff dimension and box-counting dimension
`dim_H(ℰ_b) = dim_B(ℰ_b) = (log u + t * log λ) / log b`, with positive finite `s`-dimensional
Hausdorff measure. Furthermore:
- `dim ℰ_2 = β` lies strictly in `(0.626382135, 0.626382145)` (`0.62638214` to 8 d.p., `> 0.6245`);
- `dim ℰ_10` lies strictly in `(0.887529815, 0.887529825)` (`0.88752982` to 8 d.p.);
- `dim ℰ_7 = 1` with `ℰ_7 = [0, 1]`;
- the analogous closure `ℰ_{5,b}` for `ℬ_5` equals `[0, 1]` in every base `b ≥ 2`.
-/

namespace Ouroboros

open scoped MeasureTheory ENNReal NNReal Topology
open MeasureTheory Set Filter

/-! ## Section 1: The quartic root `λ = 1 / a*` and dimension formula -/

/-- The unique positive root `λ = 1 / a* ≈ 1.543689` of `λ^4 = λ^3 + 2`. -/
noncomputable def suffixLambda : ℝ := 1 / aStar

lemma suffixLambda_pos : 0 < suffixLambda :=
  div_pos one_pos aStar_spec.1

lemma suffixLambda_gt_one : 1 < suffixLambda := by
  unfold suffixLambda
  rw [one_lt_div aStar_spec.1]
  exact aStar_spec.2.1

lemma suffixLambda_lt_two : suffixLambda < 2 := by
  unfold suffixLambda
  rw [div_lt_iff₀ aStar_spec.1]
  linarith [aStar_bounds.1]

/-- `λ = 1 / a*` satisfies `λ^4 = λ^3 + 2`. -/
theorem suffixLambda_spec : 0 < suffixLambda ∧ suffixLambda ^ 4 = suffixLambda ^ 3 + 2 := by
  refine ⟨suffixLambda_pos, ?_⟩
  have ha0 : aStar ≠ 0 := ne_of_gt aStar_spec.1
  have hq : aStar + 2 * aStar ^ 4 = 1 := aStar_quartic
  unfold suffixLambda
  field_simp [ha0]
  linarith

/-- Uniqueness of the positive root `λ` of `λ^4 = λ^3 + 2`. -/
theorem exists_unique_suffixLambda : ∃! lam : ℝ, 0 < lam ∧ lam ^ 4 = lam ^ 3 + 2 := by
  refine ⟨suffixLambda, suffixLambda_spec, ?_⟩
  intro x ⟨hx0, hxeq⟩
  have hx1 : 1 < x := by
    by_contra hle
    push Not at hle
    have hx3 : 0 ≤ x ^ 3 := by positivity
    have hmul : x ^ 3 * (x - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx3 (by linarith)
    nlinarith
  have hl1 : 1 < suffixLambda := suffixLambda_gt_one
  have hlq : suffixLambda ^ 4 = suffixLambda ^ 3 + 2 := suffixLambda_spec.2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h3 : x ^ 3 < suffixLambda ^ 3 := by gcongr
    have hsub : x - 1 < suffixLambda - 1 := by linarith
    have hmul : x ^ 3 * (x - 1) < suffixLambda ^ 3 * (suffixLambda - 1) :=
      mul_lt_mul'' h3 hsub (by positivity) (by linarith)
    linarith
  · have h3 : suffixLambda ^ 3 < x ^ 3 := by gcongr
    have hsub : suffixLambda - 1 < x - 1 := by linarith
    have hmul : suffixLambda ^ 3 * (suffixLambda - 1) < x ^ 3 * (x - 1) :=
      mul_lt_mul'' h3 hsub (by positivity) (by linarith)
    linarith

/-- Branching factor `θ_b = u * λ^t` where `b = 2^t * u` with `u` odd. -/
noncomputable def suffixTheta (b : ℕ) : ℝ :=
  ((splitTwo b).2 : ℝ) * suffixLambda ^ (splitTwo b).1

/-- Target dimension `(log u + t * log λ) / log b` where `b = 2^t * u` (`u` odd). -/
noncomputable def suffixDimVal (b : ℕ) : ℝ :=
  (Real.log ((splitTwo b).2 : ℝ) + ((splitTwo b).1 : ℝ) * Real.log suffixLambda) / Real.log (b : ℝ)

lemma suffixTheta_eq_of_fac {b t u : ℕ} (hb : 2 ≤ b) (hu : u % 2 = 1) (hfac : b = 2 ^ t * u) :
    suffixTheta b = (u : ℝ) * suffixLambda ^ t := by
  obtain ⟨hu_sp, hfac_sp⟩ := splitTwo_spec (by omega : 0 < b)
  have hinj := two_pow_mul_odd_inj hu_sp hu (hfac_sp.symm.trans hfac)
  simp [suffixTheta, hinj.1, hinj.2]

lemma suffixDimVal_eq_of_fac {b t u : ℕ} (hb : 2 ≤ b) (hu : u % 2 = 1) (hfac : b = 2 ^ t * u) :
    suffixDimVal b = (Real.log (u : ℝ) + (t : ℝ) * Real.log suffixLambda) / Real.log (b : ℝ) := by
  obtain ⟨hu_sp, hfac_sp⟩ := splitTwo_spec (by omega : 0 < b)
  have hinj := two_pow_mul_odd_inj hu_sp hu (hfac_sp.symm.trans hfac)
  simp [suffixDimVal, hinj.1, hinj.2]

lemma suffixTheta_gt_one {b : ℕ} (hb : 2 ≤ b) : 1 < suffixTheta b := by
  obtain ⟨hu_odd, hfac⟩ := splitTwo_spec (by omega : 0 < b)
  unfold suffixTheta
  set t := (splitTwo b).1
  set u := (splitTwo b).2
  have hu1 : 1 ≤ u := by omega
  have huR : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu1
  by_cases ht : t = 0
  · rw [ht, pow_zero, mul_one]
    have hu2 : 2 ≤ u := by
      have : b = u := by simpa [ht] using hfac
      omega
    exact_mod_cast (by omega : 1 < u)
  · have ht1 : 1 ≤ t := by omega
    have hlam : 1 < suffixLambda ^ t := one_lt_pow₀ suffixLambda_gt_one ht
    nlinarith

lemma suffixTheta_pos {b : ℕ} (hb : 2 ≤ b) : 0 < suffixTheta b :=
  lt_trans zero_lt_one (suffixTheta_gt_one hb)

lemma suffixTheta_le_base {b : ℕ} (hb : 2 ≤ b) : suffixTheta b ≤ (b : ℝ) := by
  obtain ⟨_, hfac⟩ := splitTwo_spec (by omega : 0 < b)
  unfold suffixTheta
  have hpow : suffixLambda ^ (splitTwo b).1 ≤ (2 : ℝ) ^ (splitTwo b).1 :=
    pow_le_pow_left₀ suffixLambda_pos.le suffixLambda_lt_two.le _
  have hbR : (b : ℝ) = (2 : ℝ) ^ (splitTwo b).1 * ((splitTwo b).2 : ℝ) := by exact_mod_cast hfac
  rw [hbR, mul_comm]
  exact mul_le_mul_of_nonneg_right hpow (by positivity)

lemma log_suffixTheta {b : ℕ} (hb : 2 ≤ b) :
    Real.log (suffixTheta b) =
      Real.log ((splitTwo b).2 : ℝ) + ((splitTwo b).1 : ℝ) * Real.log suffixLambda := by
  obtain ⟨hu_odd, _⟩ := splitTwo_spec (by omega : 0 < b)
  have hu_pos : (0 : ℝ) < ((splitTwo b).2 : ℝ) := by exact_mod_cast (by omega : 0 < (splitTwo b).2)
  have hlam_pos : 0 < suffixLambda := suffixLambda_pos
  unfold suffixTheta
  rw [Real.log_mul hu_pos.ne' (pow_pos hlam_pos _).ne', Real.log_pow]

lemma suffixDimVal_eq_log_div {b : ℕ} (hb : 2 ≤ b) :
    suffixDimVal b = Real.log (suffixTheta b) / Real.log (b : ℝ) := by
  unfold suffixDimVal
  rw [log_suffixTheta hb]

lemma suffixDimVal_pos {b : ℕ} (hb : 2 ≤ b) : 0 < suffixDimVal b := by
  rw [suffixDimVal_eq_log_div hb]
  exact div_pos (Real.log_pos (suffixTheta_gt_one hb))
    (Real.log_pos (by exact_mod_cast (by omega : 1 < b)))

lemma suffixDimVal_le_one {b : ℕ} (hb : 2 ≤ b) : suffixDimVal b ≤ 1 := by
  rw [suffixDimVal_eq_log_div hb]
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < b))
  rw [div_le_one hlogb]
  exact Real.log_le_log (suffixTheta_pos hb) (suffixTheta_le_base hb)

lemma base_rpow_suffixDimVal {b : ℕ} (hb : 2 ≤ b) :
    (b : ℝ) ^ suffixDimVal b = suffixTheta b := by
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hlogb : Real.log (b : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < b)))
  rw [suffixDimVal_eq_log_div hb, Real.rpow_def_of_pos hb_pos, mul_div_cancel₀ _ hlogb,
      Real.exp_log (suffixTheta_pos hb)]

lemma base_inv_rpow_suffixDimVal {b : ℕ} (hb : 2 ≤ b) (k : ℕ) :
    ((1 : ℝ) / (b : ℝ) ^ k) ^ suffixDimVal b = (1 : ℝ) / (suffixTheta b) ^ k := by
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  rw [one_div, one_div, Real.inv_rpow (pow_nonneg hb_pos.le k), ← Real.rpow_natCast (b : ℝ) k,
      ← Real.rpow_mul hb_pos.le, mul_comm (k : ℝ), Real.rpow_mul hb_pos.le,
      base_rpow_suffixDimVal hb, Real.rpow_natCast]

/-! ## Section 2: Reversed base-`b` expansions, intervals, and closures `ℰ_b`, `ℰ_{5,b}` -/

/-- The `j`-th base-`b` digit of `n` (starting from the units digit at `j = 0`). -/
def baseDigit (b j n : ℕ) : ℕ := (n / b ^ j) % b

/-- Reversed base-`b` expansion `∑_{j ≥ 0} d_j(n) * b^{-(j+1)} ∈ [0, 1]`. -/
noncomputable def revExp (b n : ℕ) : ℝ :=
  ∑' j : ℕ, (baseDigit b j n : ℝ) / (b : ℝ) ^ (j + 1)

/-- The reversed base-`b` suffix closure `ℰ_b ⊂ [0, 1]` of the full basin `ℬ_1`. -/
def suffixClosure1 (b : ℕ) : Set ℝ :=
  closure (revExp b '' {n : ℕ | 0 < n ∧ InBasin1 n})

/-- The analogous reversed base-`b` suffix closure `ℰ_{5,b} ⊂ [0, 1]` of `ℬ_5`. -/
def suffixClosure5 (b : ℕ) : Set ℝ :=
  closure (revExp b '' {n : ℕ | 0 < n ∧ InBasin5 n})

/-- Reversal of the lowest `k` base-`b` digits of `w` into an integer in `[0, b^k)`. -/
def revNat (b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, w => (w % b) * b ^ k + revNat b k (w / b)

/-- Closed level-`k` base-`b` prefix interval corresponding to trailing digits `w mod b^k`. -/
def suffixInterval (b k w : ℕ) : Set ℝ :=
  Set.Icc ((revNat b k w : ℝ) / (b : ℝ) ^ k) (((revNat b k w : ℝ) + 1) / (b : ℝ) ^ k)

lemma revNat_lt {b : ℕ} (hb : 1 ≤ b) (k w : ℕ) : revNat b k w < b ^ k := by
  induction k generalizing w with
  | zero => simp [revNat]
  | succ k ih =>
    simp only [revNat]
    have hmod : w % b < b := Nat.mod_lt w (by omega)
    have hih : revNat b k (w / b) < b ^ k := ih (w / b)
    have hmul : (w % b) * b ^ k + b ^ k ≤ b * b ^ k := by
      have : w % b + 1 ≤ b := by omega
      calc (w % b) * b ^ k + b ^ k = (w % b + 1) * b ^ k := by ring
        _ ≤ b * b ^ k := Nat.mul_le_mul_right _ this
    rw [pow_succ']
    omega

lemma revNat_mod {b : ℕ} (_hb : 1 ≤ b) (k w : ℕ) : revNat b k (w % b ^ k) = revNat b k w := by
  induction k generalizing w with
  | zero => simp [revNat]
  | succ k ih =>
    simp only [revNat]
    have h1 : (w % b ^ (k + 1)) % b = w % b := by
      have hdvd : b ∣ b ^ (k + 1) := by rw [pow_succ']; exact dvd_mul_right b _
      exact Nat.mod_mod_of_dvd w hdvd
    have h2 : (w % b ^ (k + 1)) / b = (w / b) % b ^ k := by
      rw [pow_succ', Nat.mod_mul_right_div_self]
    rw [h1, h2, ih (w / b)]

lemma revNat_injOn {b : ℕ} (hb : 1 ≤ b) (k : ℕ) :
    Set.InjOn (revNat b k) (Finset.range (b ^ k) : Set ℕ) := by
  induction k with
  | zero =>
    intro x hx y hy _
    simp only [Finset.coe_range, Set.mem_Iio, pow_zero] at hx hy
    omega
  | succ k ih =>
    intro x hx y hy heq
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    simp only [revNat] at heq
    have hrx : revNat b k (x / b) < b ^ k := revNat_lt hb k (x / b)
    have hry : revNat b k (y / b) < b ^ k := revNat_lt hb k (y / b)
    have hbk : 0 < b ^ k := Nat.pow_pos (by omega)
    have hmod_eq : x % b = y % b := by
      have hdivx : ((x % b) * b ^ k + revNat b k (x / b)) / b ^ k = x % b := by
        rw [mul_comm (x % b), Nat.mul_add_div hbk, Nat.div_eq_of_lt hrx, add_zero]
      have hdivy : ((y % b) * b ^ k + revNat b k (y / b)) / b ^ k = y % b := by
        rw [mul_comm (y % b), Nat.mul_add_div hbk, Nat.div_eq_of_lt hry, add_zero]
      rw [← hdivx, heq, hdivy]
    have hrem_eq : revNat b k (x / b) = revNat b k (y / b) := by
      rw [hmod_eq] at heq; omega
    have hdx : x / b < b ^ k := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; rwa [← pow_succ]
    have hdy : y / b < b ^ k := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; rwa [← pow_succ]
    have hdiv_eq : x / b = y / b :=
      ih (Finset.mem_coe.mpr (Finset.mem_range.mpr hdx))
         (Finset.mem_coe.mpr (Finset.mem_range.mpr hdy)) hrem_eq
    have hx_rec := Nat.div_add_mod x b
    have hy_rec := Nat.div_add_mod y b
    rw [← hx_rec, ← hy_rec, hdiv_eq, hmod_eq]

lemma revNat_surj {b : ℕ} (hb : 1 ≤ b) (k m : ℕ) (hm : m < b ^ k) :
    ∃ w < b ^ k, revNat b k w = m := by
  have himg : (Finset.range (b ^ k)).image (revNat b k) = Finset.range (b ^ k) := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_image, Finset.mem_range] at hy ⊢
      rcases hy with ⟨w, _, rfl⟩
      exact revNat_lt hb k w
    · rw [Finset.card_image_of_injOn (revNat_injOn hb k)]
  have hm_mem : m ∈ (Finset.range (b ^ k)).image (revNat b k) := by
    rw [himg]; exact Finset.mem_range.mpr hm
  simp only [Finset.mem_image, Finset.mem_range] at hm_mem
  exact hm_mem

lemma revNat_nest {b : ℕ} (hb : 1 ≤ b) (k d w : ℕ) :
    revNat b k w * b ^ d ≤ revNat b (k + d) w ∧
    revNat b (k + d) w < (revNat b k w + 1) * b ^ d := by
  induction k generalizing w with
  | zero =>
    simp only [revNat, zero_mul, zero_add, one_mul, zero_le, true_and]
    exact revNat_lt hb d w
  | succ k ih =>
    have hadd : k + 1 + d = (k + d) + 1 := by omega
    rw [hadd]
    simp only [revNat]
    obtain ⟨hlo, hhi⟩ := ih (w / b)
    have hpow : b ^ (k + d) = b ^ k * b ^ d := pow_add b k d
    rw [hpow]
    constructor
    · calc ((w % b) * b ^ k + revNat b k (w / b)) * b ^ d
          = (w % b) * (b ^ k * b ^ d) + revNat b k (w / b) * b ^ d := by ring
        _ ≤ (w % b) * (b ^ k * b ^ d) + revNat b (k + d) (w / b) := by omega
    · calc (w % b) * (b ^ k * b ^ d) + revNat b (k + d) (w / b)
          < (w % b) * (b ^ k * b ^ d) + (revNat b k (w / b) + 1) * b ^ d := by omega
        _ = ((w % b) * b ^ k + revNat b k (w / b) + 1) * b ^ d := by ring

lemma revExp_eq_sum {b n L : ℕ} (hb : 2 ≤ b) (hL : n < b ^ L) :
    revExp b n = ∑ j ∈ Finset.range L, (baseDigit b j n : ℝ) / (b : ℝ) ^ (j + 1) := by
  unfold revExp
  refine tsum_eq_sum fun j hj => ?_
  simp only [Finset.mem_range, not_lt] at hj
  have hle : b ^ L ≤ b ^ j := Nat.pow_le_pow_right (by omega) hj
  have hdiv : n / b ^ j = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hL hle)
  simp [baseDigit, hdiv]

lemma revExp_step {b n : ℕ} (hb : 2 ≤ b) :
    revExp b n = ((n % b : ℕ) : ℝ) / (b : ℝ) + revExp b (n / b) / (b : ℝ) := by
  have hL : n < b ^ (n + 1) := by
    calc n < 2 ^ n := Nat.lt_two_pow_self
      _ ≤ b ^ n := Nat.pow_le_pow_left hb n
      _ ≤ b ^ (n + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ n)
  have hL' : n / b < b ^ n := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; rwa [← pow_succ]
  rw [revExp_eq_sum hb hL, revExp_eq_sum hb hL', Finset.sum_range_succ', Finset.sum_div, add_comm]
  congr 1
  · simp [baseDigit]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hdig : baseDigit b (j + 1) n = baseDigit b j (n / b) := by
      unfold baseDigit
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
    rw [hdig, div_div, pow_succ]

lemma revExp_nonneg {b n : ℕ} (hb : 2 ≤ b) : 0 ≤ revExp b n := by
  have hL : n < b ^ (n + 1) := by
    calc n < 2 ^ n := Nat.lt_two_pow_self
      _ ≤ b ^ n := Nat.pow_le_pow_left hb n
      _ ≤ b ^ (n + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ n)
  rw [revExp_eq_sum hb hL]
  exact Finset.sum_nonneg fun j _ => by positivity

lemma revExp_lt_one {b n : ℕ} (hb : 2 ≤ b) : revExp b n < 1 := by
  have hL : n < b ^ (n + 1) := by
    calc n < 2 ^ n := Nat.lt_two_pow_self
      _ ≤ b ^ n := Nat.pow_le_pow_left hb n
      _ ≤ b ^ (n + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ n)
  rw [revExp_eq_sum hb hL]
  have hbR : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hstep : ∀ L : ℕ,
      ∑ j ∈ Finset.range L, ((b : ℝ) - 1) / (b : ℝ) ^ (j + 1) = 1 - 1 / (b : ℝ) ^ L := by
    intro L
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have hb0 : (b : ℝ) ≠ 0 := by linarith
      have hbp0 : (b : ℝ) ^ L ≠ 0 := pow_ne_zero L hb0
      field_simp [hb0, hbp0]
      ring
  have hle : ∑ j ∈ Finset.range (n + 1), (baseDigit b j n : ℝ) / (b : ℝ) ^ (j + 1) ≤
      ∑ j ∈ Finset.range (n + 1), ((b : ℝ) - 1) / (b : ℝ) ^ (j + 1) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hdig : baseDigit b j n + 1 ≤ b := Nat.mod_lt _ (by omega)
    have hdigR : (baseDigit b j n : ℝ) ≤ (b : ℝ) - 1 := by
      have : (baseDigit b j n : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hdig
      linarith
    exact div_le_div_of_nonneg_right hdigR (by positivity)
  rw [hstep] at hle
  have hpos : (0 : ℝ) < 1 / (b : ℝ) ^ (n + 1) := by positivity
  linarith

/-- Reversed base-`b` expansion of `n` lies in the half-open level-`k` interval for `n % b^k`. -/
lemma revExp_mem_Ico {b : ℕ} (hb : 2 ≤ b) (k n : ℕ) :
    (revNat b k n : ℝ) / (b : ℝ) ^ k ≤ revExp b n ∧
    revExp b n < ((revNat b k n : ℝ) + 1) / (b : ℝ) ^ k := by
  induction k generalizing n with
  | zero =>
    simp only [revNat, Nat.cast_zero, pow_zero, div_one, zero_add]
    exact ⟨revExp_nonneg hb, revExp_lt_one hb⟩
  | succ k ih =>
    obtain ⟨hlo, hhi⟩ := ih (n / b)
    have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
    have hbp_pos : (0 : ℝ) < (b : ℝ) ^ k := pow_pos hb_pos k
    rw [revExp_step hb]
    simp only [revNat, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, pow_succ']
    constructor
    · have h1 : (revNat b k (n / b) : ℝ) / ((b : ℝ) * (b : ℝ) ^ k) ≤ revExp b (n / b) / (b : ℝ) := by
        rw [div_mul_eq_div_div, div_right_comm]
        exact div_le_div_of_nonneg_right hlo hb_pos.le
      have h2 : ((n % b : ℕ) : ℝ) * (b : ℝ) ^ k / ((b : ℝ) * (b : ℝ) ^ k) =
          ((n % b : ℕ) : ℝ) / (b : ℝ) := by
        field_simp [hb_pos.ne', hbp_pos.ne']
      rw [add_div, h2]
      linarith
    · have h1 : revExp b (n / b) / (b : ℝ) <
          ((revNat b k (n / b) : ℝ) + 1) / ((b : ℝ) * (b : ℝ) ^ k) := by
        rw [div_mul_eq_div_div, div_right_comm]
        exact div_lt_div_of_pos_right hhi hb_pos
      have h2 : ((n % b : ℕ) : ℝ) * (b : ℝ) ^ k / ((b : ℝ) * (b : ℝ) ^ k) =
          ((n % b : ℕ) : ℝ) / (b : ℝ) := by
        field_simp [hb_pos.ne', hbp_pos.ne']
      rw [add_assoc, add_div, h2]
      linarith

lemma revExp_mem_suffixInterval {b : ℕ} (hb : 2 ≤ b) (k n : ℕ) :
    revExp b n ∈ suffixInterval b k (n % b ^ k) := by
  obtain ⟨hlo, hhi⟩ := revExp_mem_Ico hb k n
  unfold suffixInterval
  rw [revNat_mod (by omega) k n]
  exact ⟨hlo, hhi.le⟩

lemma suffixClosure1_subset_Icc {b : ℕ} (hb : 2 ≤ b) :
    suffixClosure1 b ⊆ Set.Icc (0 : ℝ) 1 := by
  refine closure_minimal ?_ isClosed_Icc
  rintro _ ⟨n, _, rfl⟩
  exact ⟨revExp_nonneg hb, (revExp_lt_one hb).le⟩

lemma suffixClosure5_subset_Icc {b : ℕ} (hb : 2 ≤ b) :
    suffixClosure5 b ⊆ Set.Icc (0 : ℝ) 1 := by
  refine closure_minimal ?_ isClosed_Icc
  rintro _ ⟨n, _, rfl⟩
  exact ⟨revExp_nonneg hb, (revExp_lt_one hb).le⟩

lemma isCompact_suffixClosure1 {b : ℕ} (hb : 2 ≤ b) : IsCompact (suffixClosure1 b) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (suffixClosure1_subset_Icc hb)

/-- If every depth-`k` base-`b` suffix is occupied by `P ⊆ ℕ`, then the reversed closure is `[0, 1]`. -/
lemma closure_eq_Icc_of_all_occupied {b : ℕ} (hb : 2 ≤ b) {P : Set ℕ}
    (hocc : ∀ k ≥ 1, ∀ w < b ^ k, ∃ n ∈ P, n % b ^ k = w) :
    closure (revExp b '' P) = Set.Icc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · refine closure_minimal ?_ isClosed_Icc
    rintro _ ⟨n, _, rfl⟩
    exact ⟨revExp_nonneg hb, (revExp_lt_one hb).le⟩
  · intro y ⟨hy0, hy1⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
    have htend : Tendsto (fun k : ℕ => ((b : ℝ) ^ k)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hb1)
    obtain ⟨k0, hk0⟩ := (htend.eventually (gt_mem_nhds hε)).exists
    set k := max 1 k0
    have hk1 : 1 ≤ k := le_max_left 1 k0
    have hbk_inv : ((b : ℝ) ^ k)⁻¹ < ε := by
      have hpow : (b : ℝ) ^ k0 ≤ (b : ℝ) ^ k :=
        pow_le_pow_right₀ hb1.le (le_max_right 1 k0)
      exact lt_of_le_of_lt (inv_anti₀ (pow_pos (by linarith) k0) hpow) hk0
    set m := min (b ^ k - 1) ⌊y * (b : ℝ) ^ k⌋₊
    have hbk_pos : 0 < b ^ k := Nat.pow_pos (by omega)
    have hbkR_pos : (0 : ℝ) < (b : ℝ) ^ k := by exact_mod_cast hbk_pos
    have hm_lt : m < b ^ k := by
      have : m ≤ b ^ k - 1 := min_le_left _ _
      omega
    have hy_in : (m : ℝ) / (b : ℝ) ^ k ≤ y ∧ y ≤ ((m : ℝ) + 1) / (b : ℝ) ^ k := by
      by_cases hlt1 : y < 1
      · have hfl_lt : ⌊y * (b : ℝ) ^ k⌋₊ < b ^ k := by
          rw [Nat.floor_lt (mul_nonneg hy0 hbkR_pos.le)]
          calc y * (b : ℝ) ^ k < 1 * (b : ℝ) ^ k := mul_lt_mul_of_pos_right hlt1 hbkR_pos
            _ = ((b ^ k : ℕ) : ℝ) := by push_cast; ring
        have hm_eq : m = ⌊y * (b : ℝ) ^ k⌋₊ := min_eq_right (by omega)
        rw [hm_eq, div_le_iff₀ hbkR_pos, le_div_iff₀ hbkR_pos]
        exact ⟨Nat.floor_le (mul_nonneg hy0 hbkR_pos.le), (Nat.lt_floor_add_one _).le⟩
      · have hy_eq : y = 1 := le_antisymm hy1 (not_lt.mp hlt1)
        have hfl_eq : ⌊y * (b : ℝ) ^ k⌋₊ = b ^ k := by
          rw [hy_eq, one_mul]
          exact_mod_cast Nat.floor_natCast (b ^ k)
        have hm_eq : m = b ^ k - 1 := min_eq_left (by omega)
        rw [hy_eq, hm_eq, div_le_iff₀ hbkR_pos, le_div_iff₀ hbkR_pos, one_mul]
        have hmR : ((b ^ k - 1 : ℕ) : ℝ) + 1 = (b : ℝ) ^ k := by
          have h1 : (b ^ k - 1) + 1 = b ^ k := by omega
          exact_mod_cast h1
        exact ⟨by linarith, by linarith⟩
    obtain ⟨w, hw_lt, hw_rev⟩ := revNat_surj (by omega) k m hm_lt
    obtain ⟨n, hnP, hnw⟩ := hocc k hk1 w hw_lt
    refine ⟨revExp b n, ⟨n, hnP, rfl⟩, ?_⟩
    have hn_in := revExp_mem_suffixInterval hb k n
    unfold suffixInterval at hn_in
    rw [hnw, hw_rev] at hn_in
    rw [Real.dist_eq, abs_lt]
    have hdiff : ((m : ℝ) + 1) / (b : ℝ) ^ k - (m : ℝ) / (b : ℝ) ^ k = ((b : ℝ) ^ k)⁻¹ := by
      rw [← sub_div, add_sub_cancel_left, one_div]
    constructor <;> linarith [hn_in.1, hn_in.2, hy_in.1, hy_in.2]

/-! ## Section 3: Exact suffix occupancy for `ℬ_1` and `ℬ_5` -/

/-- The 8 live residue classes modulo `30` reaching `1 mod 30` under `T`. -/
def inLiveS (r : ℕ) : Bool :=
  let m := r % 30
  m == 0 || m == 1 || m == 2 || m == 4 || m == 8 || m == 15 || m == 16 || m == 17

lemma f_iter_zero (k : ℕ) : f^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; decide

lemma pos_of_inBasin1 {n : ℕ} (h : InBasin1 n) : 0 < n := by
  by_contra h0
  have hn0 : n = 0 := by omega
  subst hn0
  rcases h with ⟨k, hk⟩
  rw [f_iter_zero] at hk
  omega

lemma pos_of_inBasin5 {n : ℕ} (h : InBasin5 n) : 0 < n := by
  by_contra h0
  have hn0 : n = 0 := by omega
  subst hn0
  rcases h with ⟨k, hk⟩
  rw [f_iter_zero] at hk
  omega

lemma inBasin1_T_iff (n : ℕ) : InBasin1 (T n) ↔ InBasin1 n := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := T_iter_is_f_iter 1 n
    simp only [Function.iterate_one] at hm
    exact reaches_trans ⟨m, hm.symm⟩ h
  · intro ⟨k, hk⟩
    by_cases hn1 : n = 1
    · subst hn1; exact ⟨0, by decide⟩
    · by_cases hev : n % 2 = 0
      · have hT : T n = f n := by simp [T, f_even hev, hev]
        cases k with
        | zero => simp at hk; exact absurd hk hn1
        | succ k =>
          rw [Function.iterate_succ_apply, ← hT] at hk
          exact ⟨k, hk⟩
      · have hodd : n % 2 = 1 := by omega
        have hT : T n = f (f n) := by
          have := T_eq_f_or_ff n
          simp only [hev, ↓reduceIte] at this
          exact this
        cases k with
        | zero => simp at hk; exact absurd hk hn1
        | succ k =>
          cases k with
          | zero =>
            change f n = 1 at hk
            have hfe := f_odd_even hodd
            rw [hk] at hfe
            omega
          | succ k =>
            rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← hT] at hk
            exact ⟨k, hk⟩

lemma inBasin1_T_iter_iff (k n : ℕ) : InBasin1 (T^[k] n) ↔ InBasin1 n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, ih, inBasin1_T_iff]

lemma inBasin5_of_T_iter {k n : ℕ} (h : InBasin5 (T^[k] n)) : InBasin5 n := by
  obtain ⟨m, hm⟩ := T_iter_is_f_iter k n
  exact reaches_trans ⟨m, hm.symm⟩ h

lemma inBasin1_inLiveS {n : ℕ} (h : InBasin1 n) : inLiveS n = true := by
  have hpos : 0 < n := pos_of_inBasin1 h
  obtain ⟨ho_odd, hfac⟩ := splitTwo_spec hpos
  set v := (splitTwo n).1
  set o := (splitTwo n).2
  have ho_reach : InBasin1 o := by
    rcases h with ⟨k, hk⟩
    rw [hfac] at hk
    exact ⟨k - v, (f_iter_two_pow_eq_odd (by decide) hk).2⟩
  have ho_abc : InABC o := thm_residue_law ho_odd ho_reach
  by_cases hv : v = 0
  · have hno : n = o := by simpa [hv] using hfac
    rw [hno]
    rcases ho_abc with h1 | h1 | h1 <;> simp only [InA, InB, InC] at h1 <;>
      (unfold inLiveS; rw [h1]; decide)
  · have h2v := two_pow_mod_30 (by omega : 1 ≤ v)
    have hmod : n % 30 = ((2 ^ v % 30) * (o % 30)) % 30 := by
      rw [hfac, Nat.mul_mod]
    unfold inLiveS
    rw [hmod]
    rcases h2v with h2 | h2 | h2 | h2 <;> rcases ho_abc with h1 | h1 | h1 <;>
      simp only [InA, InB, InC] at h1 <;> rw [h2, h1] <;> decide

/-- One-step odd multiplier of `T`: `1` on even inputs, `d(x)` on odd inputs. -/
def stepMultT (x : ℕ) : ℕ := if x % 2 = 0 then 1 else d x

lemma stepMultT_odd (x : ℕ) : stepMultT x % 2 = 1 := by
  unfold stepMultT d
  split_ifs <;> omega

lemma T_add_30_mul (x q : ℕ) : T (x + 30 * q) = T x + 15 * stepMultT x * q := by
  unfold T stepMultT
  by_cases hx : x % 2 = 0
  · have hx' : (x + 30 * q) % 2 = 0 := by omega
    simp only [hx, hx', ↓reduceIte, mul_one]
    omega
  · have hx' : (x + 30 * q) % 2 ≠ 0 := by omega
    have hd : d (x + 30 * q) = d x := by unfold d; omega
    have hev : (d x * x + 1) % 2 = 0 := by
      have h1 := f_odd_even (by omega : x % 2 = 1)
      rwa [f_odd (by omega)] at h1
    simp only [hx, hx', ↓reduceIte, hd]
    have hmul : d x * (x + 30 * q) + 1 = (d x * x + 1) + 2 * (15 * d x * q) := by ring
    omega

/-- Multi-step odd multiplier of `T^[h]` at `x`. -/
def iterMultT : ℕ → ℕ → ℕ
  | 0, _ => 1
  | h + 1, x => stepMultT x * iterMultT h (T x)

lemma iterMultT_odd (h x : ℕ) : iterMultT h x % 2 = 1 := by
  induction h generalizing x with
  | zero => simp [iterMultT]
  | succ h ih =>
    simp only [iterMultT]
    rw [Nat.mul_mod, stepMultT_odd x, ih (T x)]

lemma T_iter_affine_suffix (h x q : ℕ) :
    T^[h] (x + 30 * 2 ^ h * q) = T^[h] x + 30 * iterMultT h x * q := by
  induction h generalizing x q with
  | zero => simp [iterMultT]
  | succ h ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have harg : x + 30 * 2 ^ (h + 1) * q = x + 30 * (2 * 2 ^ h * q) := by rw [pow_succ']; ring
    rw [harg, T_add_30_mul]
    have harg2 : T x + 15 * stepMultT x * (2 * 2 ^ h * q) =
        T x + 30 * 2 ^ h * (stepMultT x * q) := by ring
    rw [harg2, ih (T x) (stepMultT x * q)]
    simp only [iterMultT]
    ring

lemma T_iter_mod30_of_modEq {h x y : ℕ} (hmod : x % (30 * 2 ^ h) = y % (30 * 2 ^ h)) :
    T^[h] x % 30 = T^[h] y % 30 := by
  have hx : x = x % (30 * 2 ^ h) + 30 * 2 ^ h * (x / (30 * 2 ^ h)) := by
    have := Nat.div_add_mod x (30 * 2 ^ h); linarith
  have hy : y = y % (30 * 2 ^ h) + 30 * 2 ^ h * (y / (30 * 2 ^ h)) := by
    have := Nat.div_add_mod y (30 * 2 ^ h); linarith
  conv_lhs => rw [hx, T_iter_affine_suffix]
  conv_rhs => rw [hy, T_iter_affine_suffix]
  rw [hmod]
  simp [Nat.add_mul_mod_self_left, mul_assoc]

/-! ### Commutator translation `+30` on odd progressions -/

/-- Backward digit-`1` move `L(u) = 2*u - 1`. -/
def sdimCommL (u : ℕ) : ℕ := 2 * u - 1
/-- Backward digit-`1` move `H(u) = 32*u - 1`. -/
def sdimCommH (u : ℕ) : ℕ := 32 * u - 1
/-- Commutator base operator `P(u) = H(L(u)) = 64*u - 33`. -/
def sdimCommP (u : ℕ) : ℕ := 64 * u - 33
/-- Shifted commutator operator `Q(u) = L(H(u)) = 64*u - 3 = P(u) + 30`. -/
def sdimCommQ (u : ℕ) : ℕ := 64 * u - 3

private lemma commL_props {u : ℕ} (hu1 : 1 ≤ u) (hu10 : u % 10 = 1) :
    1 ≤ sdimCommL u ∧ sdimCommL u % 10 = 1 ∧ f^[2] (sdimCommL u) = u := by
  unfold sdimCommL
  refine ⟨by omega, by omega, ?_⟩
  have h1 : f (2 * u - 1) = 2 * u := by
    rw [f_odd (by omega)]
    have hd : d (2 * u - 1) = 1 := by unfold d; omega
    rw [hd]; omega
  rw [Function.iterate_succ_apply, Function.iterate_one, h1, f_even (by omega)]
  omega

private lemma commH_props {u : ℕ} (hu1 : 1 ≤ u) (hu10 : u % 10 = 1) :
    1 ≤ sdimCommH u ∧ sdimCommH u % 10 = 1 ∧ f^[6] (sdimCommH u) = u := by
  unfold sdimCommH
  refine ⟨by omega, by omega, ?_⟩
  rw [Function.iterate_succ_apply, f_odd (by omega)]
  have hd : d (32 * u - 1) = 1 := by unfold d; omega
  rw [hd, one_mul, show 32 * u - 1 + 1 = 2 ^ 5 * u by omega, f_iter_two_pow]

private lemma commP_props {u : ℕ} (hu1 : 1 ≤ u) (hu10 : u % 10 = 1) :
    u < sdimCommP u ∧ sdimCommP u % 10 = 1 ∧ Reaches f (sdimCommP u) u := by
  have heq : sdimCommP u = sdimCommH (sdimCommL u) := by unfold sdimCommP sdimCommH sdimCommL; omega
  obtain ⟨hL1, hL10, hLf⟩ := commL_props hu1 hu10
  obtain ⟨_, hH10, hHf⟩ := commH_props hL1 hL10
  refine ⟨by unfold sdimCommP; omega, by rwa [heq], ?_⟩
  rw [heq]
  exact reaches_trans ⟨6, hHf⟩ ⟨2, hLf⟩

private lemma commQ_props {u : ℕ} (hu1 : 1 ≤ u) (hu10 : u % 10 = 1) :
    sdimCommQ u = sdimCommP u + 30 ∧ sdimCommQ u % 10 = 1 ∧ Reaches f (sdimCommQ u) u := by
  have heq : sdimCommQ u = sdimCommL (sdimCommH u) := by unfold sdimCommQ sdimCommH sdimCommL; omega
  obtain ⟨hH1, hH10, hHf⟩ := commH_props hu1 hu10
  obtain ⟨_, hL10, hLf⟩ := commL_props hH1 hH10
  refine ⟨by unfold sdimCommQ sdimCommP; omega, by rwa [heq], ?_⟩
  rw [heq]
  exact reaches_trans ⟨2, hLf⟩ ⟨6, hHf⟩

private lemma commP_iter_props (k : ℕ) {u : ℕ} (_hu1 : 1 ≤ u) (hu10 : u % 10 = 1) :
    u + k ≤ sdimCommP^[k] u ∧ (sdimCommP^[k] u) % 10 = 1 ∧ Reaches f (sdimCommP^[k] u) u := by
  induction k with
  | zero => exact ⟨by simp, hu10, reaches_refl f u⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨hge, h10, hr⟩ := ih
    obtain ⟨hgt, h10', hr'⟩ := commP_props (by omega) h10
    exact ⟨by omega, h10', reaches_trans hr' hr⟩

/-- Modular commutator hitting lemma: for every odd `E ≥ 1`, seed `u ≥ 1` with `u % 10 = 1`,
    target `b` with `b % 30 = u % 30`, and lower bound `B`, there exists `o ≥ B` with
    `o % (30 * E) = b % (30 * E)` and `Reaches f o u`. -/
lemma commutator_hit_progression {E u b : ℕ} (hE : E % 2 = 1) (hu1 : 1 ≤ u) (hu10 : u % 10 = 1)
    (hb30 : b % 30 = u % 30) (B : ℕ) :
    ∃ o : ℕ, B ≤ o ∧ o % (30 * E) = b % (30 * E) ∧ Reaches f o u := by
  set q := 15 * E
  have hq_odd : q % 2 = 1 := by omega
  have hq_pos : 0 < q := by omega
  have : NeZero q := ⟨by omega⟩
  have hcop64 : Nat.Coprime 64 q := by
    have h2q : Nat.Coprime 2 q := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
    simpa [show (64 : ℕ) = 2 ^ 6 by norm_num] using h2q.pow_left 6
  let Pmod : ZMod q → ZMod q := fun x => 64 * x - 33
  have hPmod_inj : Function.Injective Pmod := by
    intro x y hxy
    dsimp only [Pmod] at hxy
    have hmul : (64 : ZMod q) * x = (64 : ZMod q) * y := sub_left_inj.mp hxy
    let u64 : (ZMod q)ˣ := ZMod.unitOfCoprime 64 hcop64
    have hu64 : (u64 : ZMod q) = (64 : ZMod q) := by simp [u64]
    rw [← hu64] at hmul
    have := congr_arg (fun z : ZMod q => ((u64⁻¹ : (ZMod q)ˣ) : ZMod q) * z) hmul
    simpa [← mul_assoc] using this
  -- Find positive period s ≥ 1 with Pmod^[s] = id
  obtain ⟨i, j, hne, hij⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => Pmod^[n])
  have hex_s : ∃ s : ℕ, 1 ≤ s ∧ ∀ x : ZMod q, Pmod^[s] x = x := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine ⟨j - i, by omega, fun x => ?_⟩
      have hadd : i + (j - i) = j := by omega
      have h1 : Pmod^[i] (Pmod^[j - i] x) = Pmod^[i] x := by
        rw [← Function.iterate_add_apply, hadd, hij]
      exact hPmod_inj.iterate i h1
    · refine ⟨i - j, by omega, fun x => ?_⟩
      have hadd : j + (i - j) = i := by omega
      have h1 : Pmod^[j] (Pmod^[i - j] x) = Pmod^[j] x := by
        rw [← Function.iterate_add_apply, hadd, hij]
      exact hPmod_inj.iterate j h1
  obtain ⟨s, hs1, hs_id⟩ := hex_s
  have hPcast : ∀ k v : ℕ, 1 ≤ v → v % 10 = 1 →
      ((sdimCommP^[k] v : ℕ) : ZMod q) = Pmod^[k] (v : ZMod q) := by
    intro k
    induction k with
    | zero => intro v _ _; simp
    | succ k ih =>
      intro v hv1 hv10
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      obtain ⟨hge, _, _⟩ := commP_iter_props k hv1 hv10
      have h64 : 33 ≤ 64 * sdimCommP^[k] v := by omega
      change ((64 * sdimCommP^[k] v - 33 : ℕ) : ZMod q) = 64 * Pmod^[k] (v : ZMod q) - 33
      rw [Nat.cast_sub h64]
      push_cast
      rw [ih v hv1 hv10]
  -- Define R(v) = Q(P^[s-1](v)): adds 30 mod q while preserving % 10 = 1 and reaching v
  let R : ℕ → ℕ := fun v => sdimCommQ (sdimCommP^[s - 1] v)
  have hR_props : ∀ v : ℕ, 1 ≤ v → v % 10 = 1 →
      1 ≤ R v ∧ R v % 10 = 1 ∧ Reaches f (R v) v ∧ ((R v : ℕ) : ZMod q) = (v : ZMod q) + 30 := by
    intro v hv1 hv10
    obtain ⟨hge, h10, hrP⟩ := commP_iter_props (s - 1) hv1 hv10
    obtain ⟨hQeq, hQ10, hrQ⟩ := commQ_props (by omega) h10
    have hR1 : 1 ≤ R v := by dsimp only [R]; rw [hQeq]; omega
    refine ⟨hR1, hQ10, reaches_trans hrQ hrP, ?_⟩
    dsimp only [R]
    rw [hQeq, Nat.cast_add]
    have hPs : sdimCommP (sdimCommP^[s - 1] v) = sdimCommP^[s] v := by
      rw [← Function.iterate_succ_apply' sdimCommP (s - 1) v, show (s - 1).succ = s by omega]
    rw [hPs, hPcast s v hv1 hv10, hs_id]
    norm_cast
  have hR_iter : ∀ k : ℕ,
      1 ≤ R^[k] u ∧ (R^[k] u) % 10 = 1 ∧ Reaches f (R^[k] u) u ∧
      ((R^[k] u : ℕ) : ZMod q) = (u : ZMod q) + 30 * (k : ZMod q) := by
    intro k
    induction k with
    | zero => exact ⟨hu1, hu10, reaches_refl f u, by simp⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨hv1, hv10, hrv, hvz⟩ := ih
      obtain ⟨h1, h10, hr, hz⟩ := hR_props (R^[k] u) hv1 hv10
      refine ⟨h1, h10, reaches_trans hr hrv, ?_⟩
      rw [hz, hvz]; push_cast; ring
  -- Solve (u + 30 * k) % q = b % q using invertibility of 2 mod E
  have hE_pos : 0 < E := by omega
  have : NeZero E := ⟨by omega⟩
  have hcop2E : Nat.Coprime 2 E := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
  let u2 : (ZMod E)ˣ := ZMod.unitOfCoprime 2 hcop2E
  let zE : ZMod E := (((b / 15 : ℕ) : ZMod E) - ((u / 15 : ℕ) : ZMod E)) * (u2⁻¹ : (ZMod E)ˣ)
  let k := zE.val
  have hk_modE : (u / 15 + 2 * k) % E = (b / 15) % E := by
    have h1 : ((u / 15 + 2 * k : ℕ) : ZMod E) = ((b / 15 : ℕ) : ZMod E) := by
      push_cast
      have hk_eq : (k : ZMod E) = zE := ZMod.natCast_zmod_val zE
      rw [hk_eq]
      have hu2 : (2 : ZMod E) = (u2 : ZMod E) := by simp [u2]
      rw [hu2]
      dsimp only [zE]
      have : (u2 : ZMod E) * ((((b / 15 : ℕ) : ZMod E) - ((u / 15 : ℕ) : ZMod E)) *
          (u2⁻¹ : (ZMod E)ˣ)) = ((b / 15 : ℕ) : ZMod E) - ((u / 15 : ℕ) : ZMod E) := by
        rw [mul_left_comm, Units.mul_inv, mul_one]
      rw [this, add_sub_cancel]
    exact (ZMod.natCast_eq_natCast_iff' _ _ E).mp h1
  have hmodq : (u + 30 * k) % q = b % q := by
    have hu_split : u + 30 * k = 15 * (u / 15 + 2 * k) + u % 15 := by omega
    have hb_split : b = 15 * (b / 15) + b % 15 := by omega
    have h15 : u % 15 = b % 15 := by omega
    rw [hu_split, hb_split, Nat.add_mod, Nat.add_mod (15 * (b / 15)), h15]
    congr 2
    dsimp only [q]
    rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hk_modE]
  -- Let v = R^[k] u, then lift above B via P^[s * B]
  set v := R^[k] u
  obtain ⟨hv1, hv10, hrv, hvz⟩ := hR_iter k
  have hv_modq : v % q = b % q := by
    have h1 : (v : ZMod q) = ((u + 30 * k : ℕ) : ZMod q) := by rw [hvz]; push_cast; ring
    have h2 : v % q = (u + 30 * k) % q := (ZMod.natCast_eq_natCast_iff' _ _ q).mp h1
    rw [h2, hmodq]
  set o := (sdimCommP^[s])^[B] v
  have ho_eq : o = sdimCommP^[s * B] v := by
    dsimp only [o]; rw [← Function.iterate_mul]
  obtain ⟨ho_ge, ho10, hro⟩ := commP_iter_props (s * B) hv1 hv10
  have ho_B : B ≤ o := by
    rw [ho_eq]
    calc B ≤ s * B := Nat.le_mul_of_pos_left B hs1
      _ ≤ v + s * B := Nat.le_add_left _ _
      _ ≤ sdimCommP^[s * B] v := ho_ge
  have ho_modq : o % q = b % q := by
    have hPs_id : ∀ m : ℕ, Pmod^[s * m] (v : ZMod q) = (v : ZMod q) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, hs_id, ih]
    have h1 : (o : ZMod q) = (v : ZMod q) := by
      rw [ho_eq, hPcast (s * B) v hv1 hv10, hPs_id B]
    have h2 : o % q = v % q := (ZMod.natCast_eq_natCast_iff' _ _ q).mp h1
    rw [h2, hv_modq]
  have ho_mod30E : o % (30 * E) = b % (30 * E) := by
    have hb2 : b % 2 = 1 := by omega
    have ho2 : (sdimCommP^[s * B] v) % 2 = 1 := by
      have : (sdimCommP^[s * B] v) % 10 = 1 := ho10
      omega
    have h1 : o % 2 = b % 2 := by rw [ho_eq, ho2, hb2]
    have h2 : o % (15 * E) = b % (15 * E) := ho_modq
    have hcop : Nat.Coprime 2 (15 * E) := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
    have hmod_mul : o ≡ b [MOD 2 * (15 * E)] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩
    simpa [Nat.ModEq, show 2 * (15 * E) = 30 * E by ring] using hmod_mul
  refine ⟨o, ho_B, ho_mod30E, ?_⟩
  rw [ho_eq]
  exact reaches_trans hro hrv

/-! ### Routing tables modulo 30 for `ℬ_1` and `ℬ_5` -/

private lemma mul_15_mod_30_of_even {m : ℕ} (hm : m % 2 = 0) : (15 * m) % 30 = 0 := by omega

private lemma mul_15_mod_30_of_odd {m : ℕ} (hm : m % 2 = 1) : (15 * m) % 30 = 15 := by omega

private lemma T_mod30_cases (b : ℕ) :
    T b % 30 = T (b % 30) % 30 ∨ T b % 30 = (T (b % 30) + 15) % 30 := by
  have hsplit : b = b % 30 + 30 * (b / 30) := by
    have := Nat.div_add_mod b 30; linarith
  have hm := stepMultT_odd (b % 30)
  by_cases hq : (b / 30) % 2 = 0
  · left
    conv_lhs => rw [hsplit, T_add_30_mul]
    have hev : (stepMultT (b % 30) * (b / 30)) % 2 = 0 := by rw [Nat.mul_mod, hq]; simp
    have h0 : (15 * (stepMultT (b % 30) * (b / 30))) % 30 = 0 := mul_15_mod_30_of_even hev
    rw [mul_assoc, Nat.add_mod, h0, add_zero, Nat.mod_mod]
  · right
    conv_lhs => rw [hsplit, T_add_30_mul]
    have hodd : (stepMultT (b % 30) * (b / 30)) % 2 = 1 := by
      rw [Nat.mul_mod, hm]; omega
    have h15 : (15 * (stepMultT (b % 30) * (b / 30))) % 30 = 15 := mul_15_mod_30_of_odd hodd
    rw [mul_assoc, Nat.add_mod, h15]; omega

private lemma progression_step_target {b E t : ℕ} (hE : E % 2 = 1)
    (ht : t = T (b % 30) % 30 ∨ t = (T (b % 30) + 15) % 30) :
    ∃ bit : ℕ, bit < 2 ∧
      stepMultT (b + 30 * E * bit) * E % 2 = 1 ∧
      T (b + 30 * E * bit) % 30 = t ∧
      ∀ j : ℕ, T (b + 30 * E * (2 * j + bit)) =
        T (b + 30 * E * bit) + 30 * (stepMultT (b + 30 * E * bit) * E) * j := by
  let bit := if T b % 30 = t then 0 else 1
  have hbit_lt : bit < 2 := by dsimp [bit]; split_ifs <;> omega
  have hE' : stepMultT (b + 30 * E * bit) * E % 2 = 1 := by
    rw [Nat.mul_mod, stepMultT_odd, hE]
  have hmod : T (b + 30 * E * bit) % 30 = t := by
    dsimp only [bit]
    split_ifs with heq
    · simpa using heq
    · simp only [mul_one]
      rw [T_add_30_mul]
      have hodd : (stepMultT b * E) % 2 = 1 := by rw [Nat.mul_mod, stepMultT_odd, hE]
      have h15 : (15 * (stepMultT b * E)) % 30 = 15 := mul_15_mod_30_of_odd hodd
      have hadd15 : (T b + 15 * stepMultT b * E) % 30 = (T b + 15) % 30 := by
        rw [mul_assoc, Nat.add_mod, h15]; omega
      rw [hadd15]
      have hcases := T_mod30_cases b
      rcases hcases with h1 | h1 <;> rcases ht with h2 | h2 <;> omega
  refine ⟨bit, hbit_lt, hE', hmod, fun j => ?_⟩
  have harg : b + 30 * E * (2 * j + bit) = (b + 30 * E * bit) + 30 * (2 * E * j) := by ring
  rw [harg, T_add_30_mul]
  ring

/-- Shortest-path step table inside `S` toward `1 mod 30`. -/
private def nextToB1 (r : ℕ) : ℕ :=
  match r % 30 with
  | 0 => 15
  | 1 => 1
  | 2 => 1
  | 4 => 2
  | 8 => 4
  | 15 => 8
  | 16 => 8
  | 17 => 15
  | _ => 1

private def distToB1 (r : ℕ) : ℕ :=
  match r % 30 with
  | 1 => 0
  | 2 => 1
  | 4 => 2
  | 8 => 3
  | 15 | 16 => 4
  | 0 | 17 => 5
  | _ => 0

private lemma nextToB1_spec : ∀ r : Fin 30, inLiveS r.val = true → r.val ≠ 1 →
    (nextToB1 r.val = T r.val % 30 ∨ nextToB1 r.val = (T r.val + 15) % 30) ∧
    inLiveS (nextToB1 r.val) = true ∧
    distToB1 (nextToB1 r.val) < distToB1 r.val ∧
    nextToB1 r.val < 30 := by
  decide

private lemma liveS_progression_to_one (b E : ℕ) (hE : E % 2 = 1) (hS : inLiveS b = true) :
    ∃ (k j0 b' E' : ℕ), E' % 2 = 1 ∧ b' % 30 = 1 ∧
      ∀ j : ℕ, T^[k] (b + 30 * E * (j0 + 2 ^ k * j)) = b' + 30 * E' * j := by
  suffices h : ∀ d : ℕ, ∀ b E : ℕ, distToB1 b ≤ d → E % 2 = 1 → inLiveS b = true →
      ∃ (k j0 b' E' : ℕ), E' % 2 = 1 ∧ b' % 30 = 1 ∧
        ∀ j : ℕ, T^[k] (b + 30 * E * (j0 + 2 ^ k * j)) = b' + 30 * E' * j from
    h (distToB1 b) b E le_rfl hE hS
  intro d
  induction d with
  | zero =>
    intro b E hd hE hS
    have hb1 : b % 30 = 1 := by
      have : b % 30 < 30 := Nat.mod_lt b (by omega)
      unfold inLiveS at hS
      unfold distToB1 at hd
      interval_cases h : b % 30 <;> simp_all
    exact ⟨0, 0, b, E, hE, hb1, fun j => by simp⟩
  | succ d ih =>
    intro b E hd hE hS
    by_cases hb1 : b % 30 = 1
    · exact ⟨0, 0, b, E, hE, hb1, fun j => by simp⟩
    · have hr := nextToB1_spec ⟨b % 30, Nat.mod_lt b (by omega)⟩
        (by simpa [inLiveS] using hS) hb1
      have ht : nextToB1 (b % 30) = T (b % 30) % 30 ∨
          nextToB1 (b % 30) = (T (b % 30) + 15) % 30 := hr.1
      obtain ⟨bit, _, hE1, hmod1, hstep⟩ := progression_step_target hE ht
      set b1 := T (b + 30 * E * bit)
      set E1 := stepMultT (b + 30 * E * bit) * E
      have hmod1' : b1 % 30 = nextToB1 (b % 30) % 30 := by
        rw [hmod1, Nat.mod_eq_of_lt hr.2.2.2]
      have hS1 : inLiveS b1 = true := by
        have := hr.2.1; unfold inLiveS at this ⊢; rwa [hmod1']
      have hd1 : distToB1 b1 ≤ d := by
        have hlt : distToB1 (nextToB1 (b % 30)) < distToB1 (b % 30) := hr.2.2.1
        have hdb : distToB1 b = distToB1 (b % 30) := by unfold distToB1; simp
        have hdb1 : distToB1 b1 = distToB1 (nextToB1 (b % 30)) := by
          unfold distToB1; rw [hmod1']
        omega
      obtain ⟨k, j0, b', E', hE', hb', hiter⟩ := ih b1 E1 hd1 hE1 hS1
      refine ⟨k + 1, 2 * j0 + bit, b', E', hE', hb', fun j => ?_⟩
      rw [Function.iterate_succ_apply]
      have harg : 2 * j0 + bit + 2 ^ (k + 1) * j = 2 * (j0 + 2 ^ k * j) + bit := by
        rw [pow_succ']; ring
      rw [harg, hstep, hiter]

/-- Shortest-path step table on all of `Fin 30` toward `{1, 11, 21} mod 30`. -/
private def nextToB5 (r : ℕ) : ℕ :=
  match r % 30 with
  | 0 => 15 | 1 => 1  | 2 => 1  | 3 => 5  | 4 => 2
  | 5 => 28 | 6 => 18 | 7 => 25 | 8 => 19 | 9 => 11
  | 10 => 5 | 11 => 11 | 12 => 21 | 13 => 5 | 14 => 22
  | 15 => 8 | 16 => 8 | 17 => 15 | 18 => 9 | 19 => 11
  | 20 => 25 | 21 => 21 | 22 => 11 | 23 => 5 | 24 => 12
  | 25 => 18 | 26 => 28 | 27 => 5 | 28 => 29 | 29 => 11
  | _ => 1

private def distToB5 (r : ℕ) : ℕ :=
  match r % 30 with
  | 1 | 11 | 21 => 0
  | 2 | 9 | 12 | 19 | 22 | 29 => 1
  | 4 | 8 | 14 | 18 | 24 | 28 => 2
  | 5 | 6 | 15 | 16 | 25 | 26 => 3
  | _ => 4

private lemma nextToB5_spec : ∀ r : Fin 30, r.val % 10 ≠ 1 →
    (nextToB5 r.val = T r.val % 30 ∨ nextToB5 r.val = (T r.val + 15) % 30) ∧
    distToB5 (nextToB5 r.val) < distToB5 r.val ∧
    nextToB5 r.val < 30 := by
  decide

private lemma any_progression_to_mod10_one (b E : ℕ) (hE : E % 2 = 1) :
    ∃ (k j0 b' E' : ℕ), E' % 2 = 1 ∧ b' % 10 = 1 ∧
      ∀ j : ℕ, T^[k] (b + 30 * E * (j0 + 2 ^ k * j)) = b' + 30 * E' * j := by
  suffices h : ∀ d : ℕ, ∀ b E : ℕ, distToB5 b ≤ d → E % 2 = 1 →
      ∃ (k j0 b' E' : ℕ), E' % 2 = 1 ∧ b' % 10 = 1 ∧
        ∀ j : ℕ, T^[k] (b + 30 * E * (j0 + 2 ^ k * j)) = b' + 30 * E' * j from
    h (distToB5 b) b E le_rfl hE
  intro d
  induction d with
  | zero =>
    intro b E hd hE
    have hb10 : b % 10 = 1 := by
      have : b % 30 < 30 := Nat.mod_lt b (by omega)
      unfold distToB5 at hd
      interval_cases h : b % 30 <;> simp_all <;> omega
    exact ⟨0, 0, b, E, hE, hb10, fun j => by simp⟩
  | succ d ih =>
    intro b E hd hE
    by_cases hb10 : b % 10 = 1
    · exact ⟨0, 0, b, E, hE, hb10, fun j => by simp⟩
    · have hb30_10 : (b % 30) % 10 ≠ 1 := by omega
      have hr := nextToB5_spec ⟨b % 30, Nat.mod_lt b (by omega)⟩ hb30_10
      obtain ⟨bit, _, hE1, hmod1, hstep⟩ := progression_step_target hE hr.1
      set b1 := T (b + 30 * E * bit)
      set E1 := stepMultT (b + 30 * E * bit) * E
      have hmod1' : b1 % 30 = nextToB5 (b % 30) % 30 := by
        rw [hmod1, Nat.mod_eq_of_lt hr.2.2]
      have hd1 : distToB5 b1 ≤ d := by
        have hlt : distToB5 (nextToB5 (b % 30)) < distToB5 (b % 30) := hr.2.1
        have hdb : distToB5 b = distToB5 (b % 30) := by unfold distToB5; simp
        have hdb1 : distToB5 b1 = distToB5 (nextToB5 (b % 30)) := by
          unfold distToB5; rw [hmod1']
        omega
      obtain ⟨k, j0, b', E', hE', hb', hiter⟩ := ih b1 E1 hd1 hE1
      refine ⟨k + 1, 2 * j0 + bit, b', E', hE', hb', fun j => ?_⟩
      rw [Function.iterate_succ_apply]
      have harg : 2 * j0 + bit + 2 ^ (k + 1) * j = 2 * (j0 + 2 ^ k * j) + bit := by
        rw [pow_succ']; ring
      rw [harg, hstep, hiter]

private lemma eq_add_mul_of_le_of_mod_eq {o b m : ℕ} (hle : b ≤ o) (hmod : o % m = b % m) :
    ∃ j : ℕ, o = b + m * j := by
  refine ⟨o / m - b / m, ?_⟩
  have h1 := Nat.div_add_mod o m
  have h2 := Nat.div_add_mod b m
  have hq : b / m ≤ o / m := Nat.div_le_div_right hle
  rw [Nat.mul_sub_left_distrib]
  omega

lemma liveS_progression_hits_basin1 {b E : ℕ} (hE : E % 2 = 1) (hS : inLiveS b = true) :
    ∃ j : ℕ, 0 < b + 30 * E * j ∧ InBasin1 (b + 30 * E * j) := by
  obtain ⟨k, j0, b', E', hE', hb', hiter⟩ := liveS_progression_to_one b E hE hS
  obtain ⟨o, ho_ge, ho_mod, ho_reach⟩ :=
    commutator_hit_progression hE' (u := 1) (by decide) (by decide) (by omega) b'
  obtain ⟨j, ho_eq⟩ := eq_add_mul_of_le_of_mod_eq ho_ge ho_mod
  refine ⟨j0 + 2 ^ k * j, ?_, ?_⟩
  · have hT : InBasin1 (T^[k] (b + 30 * E * (j0 + 2 ^ k * j))) := by
      rw [hiter, ← ho_eq]; exact ho_reach
    exact pos_of_inBasin1 ((inBasin1_T_iter_iff k _).mp hT)
  · have hT : InBasin1 (T^[k] (b + 30 * E * (j0 + 2 ^ k * j))) := by
      rw [hiter, ← ho_eq]; exact ho_reach
    exact (inBasin1_T_iter_iff k _).mp hT

private lemma f_iter_211_reaches_5 : f^[9] 211 = 5 := by decide
private lemma f_iter_11_reaches_5' : f^[5] 11 = 5 := by decide
private lemma f_iter_21_reaches_5 : f^[7] 21 = 5 := by decide

lemma any_progression_hits_basin5 {b E : ℕ} (hE : E % 2 = 1) :
    ∃ j : ℕ, 0 < b + 30 * E * j ∧ InBasin5 (b + 30 * E * j) := by
  obtain ⟨k, j0, b', E', hE', hb10, hiter⟩ := any_progression_to_mod10_one b E hE
  have hseed : ∃ u : ℕ, 1 ≤ u ∧ u % 10 = 1 ∧ b' % 30 = u % 30 ∧ InBasin5 u := by
    have hcases : b' % 30 = 1 ∨ b' % 30 = 11 ∨ b' % 30 = 21 := by omega
    rcases hcases with h1 | h11 | h21
    · exact ⟨211, by omega, by decide, by omega, ⟨9, f_iter_211_reaches_5⟩⟩
    · exact ⟨11, by omega, by decide, by omega, ⟨5, f_iter_11_reaches_5'⟩⟩
    · exact ⟨21, by omega, by decide, by omega, ⟨7, f_iter_21_reaches_5⟩⟩
  obtain ⟨u, hu1, hu10, hb30, hu5⟩ := hseed
  obtain ⟨o, ho_ge, ho_mod, ho_reach⟩ :=
    commutator_hit_progression hE' hu1 hu10 hb30 b'
  obtain ⟨j, ho_eq⟩ := eq_add_mul_of_le_of_mod_eq ho_ge ho_mod
  have h5 : InBasin5 (b + 30 * E * (j0 + 2 ^ k * j)) := by
    apply inBasin5_of_T_iter (k := k)
    rw [hiter, ← ho_eq]
    exact reaches_trans ho_reach hu5
  exact ⟨j0 + 2 ^ k * j, pos_of_inBasin5 h5, h5⟩

/-! ### Refined modulus `ℓ_k = lcm(30, b^k)` and exact occupancy -/

/-- Number of forced halving steps at base-`b` digit depth `k`: `h_k = max(0, t*k - 1)`. -/
def hDepth (b k : ℕ) : ℕ := (splitTwo b).1 * k - 1

/-- Refined modulus `ℓ_k = lcm(30, b^k)`. -/
def ellMod (b k : ℕ) : ℕ := Nat.lcm 30 (b ^ k)

/-- Odd quotient factor `D_k = u^k / gcd(u^k, 15)`. -/
def oddFactor (b k : ℕ) : ℕ := (splitTwo b).2 ^ k / Nat.gcd ((splitTwo b).2 ^ k) 15

lemma gcd_pow_15 (u k : ℕ) (hk : 1 ≤ k) : Nat.gcd (u ^ k) 15 = Nat.gcd u 15 := by
  have hdvd3 : ∀ m : ℕ, 3 ∣ Nat.gcd m 15 ↔ 3 ∣ m := fun m => by
    constructor
    · intro h; exact dvd_trans h (Nat.gcd_dvd_left m 15)
    · intro h; exact Nat.dvd_gcd h (by decide)
  have hdvd5 : ∀ m : ℕ, 5 ∣ Nat.gcd m 15 ↔ 5 ∣ m := fun m => by
    constructor
    · intro h; exact dvd_trans h (Nat.gcd_dvd_left m 15)
    · intro h; exact Nat.dvd_gcd h (by decide)
  have h3 : 3 ∣ Nat.gcd (u ^ k) 15 ↔ 3 ∣ Nat.gcd u 15 := by
    rw [hdvd3, hdvd3]
    exact ⟨fun h => Nat.prime_three.dvd_of_dvd_pow h,
           fun h => dvd_trans h (dvd_pow_self u (by omega))⟩
  have h5 : 5 ∣ Nat.gcd (u ^ k) 15 ↔ 5 ∣ Nat.gcd u 15 := by
    rw [hdvd5, hdvd5]
    exact ⟨fun h => (by decide : Nat.Prime 5).dvd_of_dvd_pow h,
           fun h => dvd_trans h (dvd_pow_self u (by omega))⟩
  have h15_divs : ∀ d : ℕ, d ∣ 15 → d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 15 := by
    intro d hd
    have hle : d ≤ 15 := Nat.le_of_dvd (by decide) hd
    interval_cases d <;> simp_all
  rcases h15_divs _ (Nat.gcd_dvd_right (u ^ k) 15) with ha | ha | ha | ha <;>
  rcases h15_divs _ (Nat.gcd_dvd_right u 15) with hb | hb | hb | hb <;>
    simp_all

lemma oddFactor_odd {b : ℕ} (hb : 2 ≤ b) (k : ℕ) : oddFactor b k % 2 = 1 := by
  obtain ⟨hu_odd, _⟩ := splitTwo_spec (by omega : 0 < b)
  have hpow_odd : (splitTwo b).2 ^ k % 2 = 1 := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Nat.mul_mod, ih, hu_odd]
  have hmul : Nat.gcd ((splitTwo b).2 ^ k) 15 * oddFactor b k = (splitTwo b).2 ^ k :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  by_contra h
  have hev : oddFactor b k % 2 = 0 := by omega
  have : ((splitTwo b).2 ^ k) % 2 = 0 := by rw [← hmul, Nat.mul_mod, hev]; simp
  omega

lemma ellMod_eq {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) :
    ellMod b k = 30 * 2 ^ hDepth b k * oddFactor b k := by
  obtain ⟨hu_odd, hfac⟩ := splitTwo_spec (by omega : 0 < b)
  set t := (splitTwo b).1
  set u := (splitTwo b).2
  have hbk : b ^ k = 2 ^ (t * k) * u ^ k := by
    rw [hfac, mul_pow, ← pow_mul]
  have hgu_pos : 0 < Nat.gcd (u ^ k) 15 := Nat.gcd_pos_of_pos_right _ (by decide)
  have hgu_mul : oddFactor b k * Nat.gcd (u ^ k) 15 = u ^ k := by
    unfold oddFactor; exact Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hlm := Nat.gcd_mul_lcm 30 (b ^ k)
  by_cases ht : t = 0
  · have hbk' : b ^ k = u ^ k := by simpa [ht] using hbk
    have hcop2 : Nat.Coprime 2 (u ^ k) := by
      have h2u : Nat.Coprime 2 u := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
      exact h2u.pow_right k
    have hgcd : Nat.gcd 30 (b ^ k) = Nat.gcd (u ^ k) 15 := by
      rw [hbk', show (30 : ℕ) = 2 * 15 by norm_num, Nat.Coprime.gcd_mul_left_cancel 15 hcop2,
          Nat.gcd_comm]
    rw [hgcd, hbk'] at hlm
    have hmul : Nat.gcd (u ^ k) 15 * ellMod b k =
        Nat.gcd (u ^ k) 15 * (30 * 2 ^ hDepth b k * oddFactor b k) := by
      unfold ellMod hDepth
      rw [hbk']
      have ht0 : (splitTwo b).1 = 0 := ht
      simp only [ht0, zero_mul, Nat.zero_sub, pow_zero, mul_one]
      calc Nat.gcd (u ^ k) 15 * Nat.lcm 30 (u ^ k) = 30 * u ^ k := hlm
        _ = 30 * (oddFactor b k * Nat.gcd (u ^ k) 15) := by rw [hgu_mul]
        _ = Nat.gcd (u ^ k) 15 * (30 * oddFactor b k) := by ring
    exact Nat.eq_of_mul_eq_mul_left hgu_pos hmul
  · have htk1 : 1 ≤ t * k := Nat.mul_pos (by omega) hk
    have h2pow : 2 ^ (t * k) = 2 * 2 ^ hDepth b k := by
      unfold hDepth
      have : t * k = (t * k - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    have hcop15 : Nat.Coprime 15 (2 ^ hDepth b k) :=
      (by decide : Nat.Coprime 15 2).pow_right _
    have hgcd : Nat.gcd 30 (b ^ k) = 2 * Nat.gcd (u ^ k) 15 := by
      rw [hbk, h2pow, mul_assoc, show (30 : ℕ) = 2 * 15 by norm_num, Nat.gcd_mul_left,
          Nat.gcd_comm 15 _, Nat.Coprime.gcd_mul_left_cancel (u ^ k) hcop15.symm]
    rw [hgcd, hbk, h2pow] at hlm
    have hmul : (2 * Nat.gcd (u ^ k) 15) * ellMod b k =
        (2 * Nat.gcd (u ^ k) 15) * (30 * 2 ^ hDepth b k * oddFactor b k) := by
      unfold ellMod
      rw [hbk, h2pow]
      calc 2 * Nat.gcd (u ^ k) 15 * Nat.lcm 30 (2 * 2 ^ hDepth b k * u ^ k)
          = 30 * (2 * 2 ^ hDepth b k * u ^ k) := hlm
        _ = 30 * (2 * 2 ^ hDepth b k * (oddFactor b k * Nat.gcd (u ^ k) 15)) := by rw [hgu_mul]
        _ = 2 * Nat.gcd (u ^ k) 15 * (30 * 2 ^ hDepth b k * oddFactor b k) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) hmul

lemma ellMod_pos {b : ℕ} (hb : 2 ≤ b) (k : ℕ) : 0 < ellMod b k :=
  Nat.lcm_pos (by decide) (Nat.pow_pos (by omega))

lemma hDepth_succ {b k : ℕ} (hk : 1 ≤ k) : hDepth b (k + 1) = hDepth b k + (splitTwo b).1 := by
  unfold hDepth
  by_cases ht : (splitTwo b).1 = 0
  · simp [ht]
  · have : 1 ≤ (splitTwo b).1 * k := Nat.mul_pos (by omega) hk
    have : (splitTwo b).1 * (k + 1) = (splitTwo b).1 * k + (splitTwo b).1 := by ring
    omega

lemma oddFactor_succ {b k : ℕ} (hk : 1 ≤ k) :
    oddFactor b (k + 1) = (splitTwo b).2 * oddFactor b k := by
  unfold oddFactor
  rw [gcd_pow_15 _ (k + 1) (by omega), gcd_pow_15 _ k hk, pow_succ']
  have hdvd : Nat.gcd (splitTwo b).2 15 ∣ (splitTwo b).2 ^ k := by
    rw [← gcd_pow_15 _ k hk]; exact Nat.gcd_dvd_left _ _
  exact Nat.mul_div_assoc _ hdvd

lemma ellMod_succ {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) :
    ellMod b (k + 1) = b * ellMod b k := by
  obtain ⟨_, hfac⟩ := splitTwo_spec (by omega : 0 < b)
  rw [ellMod_eq hb (by omega), ellMod_eq hb hk, hDepth_succ hk, oddFactor_succ hk, pow_add]
  conv_rhs => enter [1]; rw [hfac]
  ring

lemma ellMod_le_30_mul {b k : ℕ} : ellMod b k ≤ 30 * b ^ k := by
  unfold ellMod
  have hdvd : Nat.lcm 30 (b ^ k) ∣ 30 * b ^ k :=
    Nat.lcm_dvd (dvd_mul_right 30 _) (dvd_mul_left _ 30)
  by_cases h0 : b ^ k = 0
  · simp [h0]
  · exact Nat.le_of_dvd (Nat.mul_pos (by decide) (Nat.pos_of_ne_zero h0)) hdvd

/-- Exact characterization of occupied base-`b` depth-`k` suffixes of `ℬ_1`. -/
lemma occupied1_iff_refined {b k w : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (_hw : w < b ^ k) :
    (∃ n : ℕ, 0 < n ∧ InBasin1 n ∧ n % b ^ k = w) ↔
    (∃ x < ellMod b k, x % b ^ k = w ∧ inLiveS (T^[hDepth b k] x) = true) := by
  constructor
  · rintro ⟨n, _, hn1, hnw⟩
    refine ⟨n % ellMod b k, Nat.mod_lt n (ellMod_pos hb k), ?_, ?_⟩
    · unfold ellMod; rw [Nat.mod_mod_of_dvd n (Nat.dvd_lcm_right 30 (b ^ k)), hnw]
    · have h30dvd : 30 * 2 ^ hDepth b k ∣ ellMod b k := by
        rw [ellMod_eq hb hk]; exact dvd_mul_right _ _
      have hmod : (n % ellMod b k) % (30 * 2 ^ hDepth b k) = n % (30 * 2 ^ hDepth b k) :=
        Nat.mod_mod_of_dvd n h30dvd
      have hT30 := T_iter_mod30_of_modEq hmod
      have hlive := inBasin1_inLiveS ((inBasin1_T_iter_iff (hDepth b k) n).mpr hn1)
      unfold inLiveS at hlive ⊢
      rwa [hT30]
  · rintro ⟨x, _, hxw, hlive⟩
    have hDodd : oddFactor b k % 2 = 1 := oddFactor_odd hb k
    have hEodd : (iterMultT (hDepth b k) x * oddFactor b k) % 2 = 1 := by
      rw [Nat.mul_mod, iterMultT_odd, hDodd]
    obtain ⟨j, _, hj1⟩ := liveS_progression_hits_basin1 hEodd hlive
    set n := x + ellMod b k * j
    have hTn : T^[hDepth b k] n =
        T^[hDepth b k] x + 30 * (iterMultT (hDepth b k) x * oddFactor b k) * j := by
      dsimp only [n]
      rw [ellMod_eq hb hk, show 30 * 2 ^ hDepth b k * oddFactor b k * j =
          30 * 2 ^ hDepth b k * (oddFactor b k * j) by ring, T_iter_affine_suffix]
      ring
    have hn1 : InBasin1 n := (inBasin1_T_iter_iff (hDepth b k) n).mp (by rwa [hTn])
    refine ⟨n, pos_of_inBasin1 hn1, hn1, ?_⟩
    obtain ⟨q, hq⟩ := Nat.dvd_lcm_right 30 (b ^ k)
    change (x + ellMod b k * j) % b ^ k = w
    rw [show ellMod b k = b ^ k * q from hq, mul_assoc, Nat.add_mul_mod_self_left, hxw]

/-- Every congruence class modulo `b^k` meets `ℬ_5` (Theorem 29 for `ℬ_5`). -/
lemma all_occupied5 {b k w : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (hw : w < b ^ k) :
    ∃ n : ℕ, 0 < n ∧ InBasin5 n ∧ n % b ^ k = w := by
  have hDodd : oddFactor b k % 2 = 1 := oddFactor_odd hb k
  have hEodd : (iterMultT (hDepth b k) w * oddFactor b k) % 2 = 1 := by
    rw [Nat.mul_mod, iterMultT_odd, hDodd]
  obtain ⟨j, _, hj5⟩ := any_progression_hits_basin5 (b := T^[hDepth b k] w) hEodd
  set n := w + ellMod b k * j
  have hTn : T^[hDepth b k] n =
      T^[hDepth b k] w + 30 * (iterMultT (hDepth b k) w * oddFactor b k) * j := by
    dsimp only [n]
    rw [ellMod_eq hb hk, show 30 * 2 ^ hDepth b k * oddFactor b k * j =
        30 * 2 ^ hDepth b k * (oddFactor b k * j) by ring, T_iter_affine_suffix]
    ring
  have hn5 : InBasin5 n := inBasin5_of_T_iter (k := hDepth b k) (by rwa [hTn])
  refine ⟨n, pos_of_inBasin5 hn5, hn5, ?_⟩
  obtain ⟨q, hq⟩ := Nat.dvd_lcm_right 30 (b ^ k)
  change (w + ellMod b k * j) % b ^ k = w
  rw [show ellMod b k = b ^ k * q from hq, mul_assoc, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hw]

/-- In base `7`, every depth-`k` suffix is occupied by `ℬ_1`. -/
lemma all_occupied1_base7 {k w : ℕ} (hk : 1 ≤ k) (hw : w < 7 ^ k) :
    ∃ n : ℕ, 0 < n ∧ InBasin1 n ∧ n % 7 ^ k = w := by
  rw [occupied1_iff_refined (by norm_num) hk hw]
  have hcop : Nat.Coprime 30 (7 ^ k) := (by decide : Nat.Coprime 30 7).pow_right k
  have hell : ellMod 7 k = 30 * 7 ^ k := by
    unfold ellMod; exact hcop.lcm_eq_mul
  have hh : hDepth 7 k = 0 := by
    unfold hDepth splitTwo; simp
  let e := ZMod.chineseRemainder hcop
  let x_z : ZMod (30 * 7 ^ k) := e.symm ((1 : ZMod 30), (w : ZMod (7 ^ k)))
  have h7pos : 0 < 7 ^ k := Nat.pow_pos (by decide)
  have : NeZero (30 * 7 ^ k) := ⟨by omega⟩
  have : NeZero (7 ^ k) := ⟨by omega⟩
  refine ⟨x_z.val, ?_, ?_, ?_⟩
  · rw [hell]; exact x_z.val_lt
  · have hcast : ((x_z.val : ℕ) : ZMod (30 * 7 ^ k)) = x_z := ZMod.natCast_zmod_val x_z
    have hmap : e ((x_z.val : ℕ) : ZMod (30 * 7 ^ k)) =
        (((x_z.val : ℕ) : ZMod 30), ((x_z.val : ℕ) : ZMod (7 ^ k))) := map_natCast e x_z.val
    rw [hcast, e.apply_symm_apply] at hmap
    have h2 : ((x_z.val : ℕ) : ZMod (7 ^ k)) = (w : ZMod (7 ^ k)) := (congr_arg Prod.snd hmap).symm
    have hmod := (ZMod.natCast_eq_natCast_iff' x_z.val w (7 ^ k)).mp h2
    rwa [Nat.mod_eq_of_lt hw] at hmod
  · rw [hh, Function.iterate_zero, id_eq]
    have hcast : ((x_z.val : ℕ) : ZMod (30 * 7 ^ k)) = x_z := ZMod.natCast_zmod_val x_z
    have hmap : e ((x_z.val : ℕ) : ZMod (30 * 7 ^ k)) =
        (((x_z.val : ℕ) : ZMod 30), ((x_z.val : ℕ) : ZMod (7 ^ k))) := map_natCast e x_z.val
    rw [hcast, e.apply_symm_apply] at hmap
    have h1 : ((x_z.val : ℕ) : ZMod 30) = (1 : ZMod 30) := (congr_arg Prod.fst hmap).symm
    have hmod : x_z.val % 30 = 1 % 30 := (ZMod.natCast_eq_natCast_iff' x_z.val 1 30).mp h1
    unfold inLiveS; rw [hmod]; decide

/-- Corollary 30 (`ℬ_5` part): the reversed suffix closure of `ℬ_5` is `[0, 1]` in every base `b ≥ 2`. -/
theorem suffixClosure5_eq_Icc {b : ℕ} (hb : 2 ≤ b) :
    suffixClosure5 b = Set.Icc (0 : ℝ) 1 :=
  closure_eq_Icc_of_all_occupied hb fun k hk w hw => by
    obtain ⟨n, hpos, h5, hmod⟩ := all_occupied5 hb hk hw
    exact ⟨n, ⟨hpos, h5⟩, hmod⟩

/-- Corollary 30 (base `7` part): `ℰ_7 = [0, 1]`. -/
theorem suffixClosure1_base7_eq_Icc :
    suffixClosure1 7 = Set.Icc (0 : ℝ) 1 :=
  closure_eq_Icc_of_all_occupied (by norm_num) fun k hk w hw => by
    obtain ⟨n, hpos, h1, hmod⟩ := all_occupied1_base7 hk hw
    exact ⟨n, ⟨hpos, h1⟩, hmod⟩

/-! ## Section 4: Exact 4-state Perron weights and Kolmogorov consistency -/

/-- Exact right Perron eigenvector weight on `ℤ / 30ℤ` for the 4-state collapse of `S`. -/
noncomputable def stateWeight (r : ℕ) : ℝ :=
  match r % 30 with
  | 0 | 1 | 2 | 17 => 1
  | 15 | 16 => 2 * aStar ^ 3
  | 8 => 2 * aStar ^ 2
  | 4 => 2 * aStar
  | _ => 0

lemma stateWeight_mod30 (r : ℕ) : stateWeight (r % 30) = stateWeight r := by
  unfold stateWeight; simp

lemma stateWeight_nonneg (r : ℕ) : 0 ≤ stateWeight r := by
  have ha0 := aStar_spec.1
  unfold stateWeight
  split <;> positivity

lemma stateWeight_eq_zero_of_not_live {r : ℕ} (h : inLiveS r = false) : stateWeight r = 0 := by
  have hlt : r % 30 < 30 := Nat.mod_lt r (by decide)
  unfold inLiveS at h
  unfold stateWeight
  interval_cases hr : r % 30 <;> simp_all

lemma stateWeight_bounds_of_live {r : ℕ} (h : inLiveS r = true) :
    2 * aStar ^ 3 ≤ stateWeight r ∧ stateWeight r ≤ 2 * aStar := by
  obtain ⟨hlo, hhi⟩ := aStar_bounds
  have ha0 := aStar_spec.1
  have h2a3_le_2a2 : 2 * aStar ^ 3 ≤ 2 * aStar ^ 2 := by nlinarith [sq_nonneg aStar]
  have h2a2_le_1 : 2 * aStar ^ 2 ≤ 1 := by nlinarith
  have h1_le_2a : 1 ≤ 2 * aStar := by linarith
  have hlt : r % 30 < 30 := Nat.mod_lt r (by decide)
  unfold inLiveS at h
  unfold stateWeight
  interval_cases r % 30 <;>
    first | (exact absurd h (by decide)) | (constructor <;> (norm_num; try linarith))

/-- Exact 1-step Perron eigenvector identity on ALL `r : ℕ`. -/
lemma stateWeight_step (r : ℕ) :
    stateWeight (T r) + stateWeight (T r + 15) = suffixLambda * stateWeight r := by
  -- First reduce to r % 30 using T_mod30_cases
  have hred : stateWeight (T r) + stateWeight (T r + 15) =
      stateWeight (T (r % 30)) + stateWeight (T (r % 30) + 15) := by
    rcases T_mod30_cases r with h1 | h1
    · rw [← stateWeight_mod30 (T r), ← stateWeight_mod30 (T r + 15),
          ← stateWeight_mod30 (T (r % 30)), ← stateWeight_mod30 (T (r % 30) + 15)]
      have h2 : (T r + 15) % 30 = (T (r % 30) + 15) % 30 := by omega
      rw [h1, h2]
    · rw [← stateWeight_mod30 (T r), ← stateWeight_mod30 (T r + 15),
          ← stateWeight_mod30 (T (r % 30)), ← stateWeight_mod30 (T (r % 30) + 15)]
      have h2 : (T r + 15) % 30 = T (r % 30) % 30 := by omega
      rw [h1, h2, add_comm]
  rw [hred, ← stateWeight_mod30 r]
  have ha0 : aStar ≠ 0 := ne_of_gt aStar_spec.1
  have hq : aStar + 2 * aStar ^ 4 = 1 := aStar_quartic
  have hlt : r % 30 < 30 := Nat.mod_lt r (by decide)
  interval_cases r % 30 <;> (simp only [T, d, stateWeight, suffixLambda]; norm_num)
  all_goals (field_simp [ha0]; try linarith)

private lemma sum_range_two_mul (g : ℕ → ℝ) (n : ℕ) :
    ∑ s ∈ Finset.range (2 * n), g s =
      ∑ s ∈ Finset.range n, g (2 * s) + ∑ s ∈ Finset.range n, g (2 * s + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
        ih, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- Exact `j`-step Perron weight sum over `2^j` progressions `y + 30 * D * s` (`D` odd). -/
lemma stateWeight_iter_sum (j y D : ℕ) (hD : D % 2 = 1) :
    ∑ s ∈ Finset.range (2 ^ j), stateWeight (T^[j] (y + 30 * D * s)) =
      suffixLambda ^ j * stateWeight y := by
  induction j generalizing y D with
  | zero => simp
  | succ j ih =>
    have hsplit : ∑ s ∈ Finset.range (2 ^ (j + 1)), stateWeight (T^[j + 1] (y + 30 * D * s)) =
        ∑ s ∈ Finset.range (2 ^ j), stateWeight (T^[j + 1] (y + 30 * D * (2 * s))) +
        ∑ s ∈ Finset.range (2 ^ j), stateWeight (T^[j + 1] (y + 30 * D * (2 * s + 1))) := by
      rw [pow_succ']
      exact sum_range_two_mul _ (2 ^ j)
    rw [hsplit]
    have hD' : (stepMultT y * D) % 2 = 1 := by rw [Nat.mul_mod, stepMultT_odd, hD]
    have heven : ∑ s ∈ Finset.range (2 ^ j), stateWeight (T^[j + 1] (y + 30 * D * (2 * s))) =
        suffixLambda ^ j * stateWeight (T y) := by
      have hcongr : ∀ s, T^[j + 1] (y + 30 * D * (2 * s)) =
          T^[j] (T y + 30 * (stepMultT y * D) * s) := fun s => by
        rw [Function.iterate_succ_apply, show y + 30 * D * (2 * s) = y + 30 * (2 * D * s) by ring,
            T_add_30_mul]
        congr 1; ring
      simp_rw [hcongr]
      exact ih (T y) (stepMultT y * D) hD'
    have hodd : ∑ s ∈ Finset.range (2 ^ j), stateWeight (T^[j + 1] (y + 30 * D * (2 * s + 1))) =
        suffixLambda ^ j * stateWeight (T y + 15) := by
      have hcongr : ∀ s, T^[j + 1] (y + 30 * D * (2 * s + 1)) =
          T^[j] ((T y + 15 * stepMultT y * D) + 30 * (stepMultT y * D) * s) := fun s => by
        rw [Function.iterate_succ_apply,
            show y + 30 * D * (2 * s + 1) = y + 30 * (2 * D * s + D) by ring, T_add_30_mul]
        congr 1; ring
      simp_rw [hcongr]
      rw [ih (T y + 15 * stepMultT y * D) (stepMultT y * D) hD']
      congr 1
      rw [← stateWeight_mod30 (T y + 15 * stepMultT y * D), ← stateWeight_mod30 (T y + 15)]
      have h15 : (15 * (stepMultT y * D)) % 30 = 15 := mul_15_mod_30_of_odd hD'
      have hmod : (T y + 15 * stepMultT y * D) % 30 = (T y + 15) % 30 := by
        rw [mul_assoc, Nat.add_mod, h15]; omega
      rw [hmod]
    rw [heven, hodd, ← mul_add, stateWeight_step, pow_succ, mul_assoc]

/-- Consistent depth-`k` cylinder weight `ν_k(w)` on `w < b^k`. -/
noncomputable def nuWeight (b k w : ℕ) : ℝ :=
  (∑ x ∈ (Finset.range (ellMod b k)).filter (fun x => x % b ^ k = w),
    stateWeight (T^[hDepth b k] x)) / (suffixTheta b) ^ k

/-- Total weight `M_0(b) = ∑_{w < b} ν_1(w) > 0`. -/
noncomputable def totalMass (b : ℕ) : ℝ :=
  ∑ w ∈ Finset.range b, nuWeight b 1 w

/-- Finite set of occupied base-`b` depth-`k` suffixes of `ℬ_1`. -/
noncomputable def occupiedFinset1 (b k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (b ^ k)).filter (fun w => ∃ n : ℕ, 0 < n ∧ InBasin1 n ∧ n % b ^ k = w)

private lemma sum_range_mul (g : ℕ → ℝ) (a b : ℕ) :
    ∑ m ∈ Finset.range (a * b), g m =
      ∑ q ∈ Finset.range b, ∑ r ∈ Finset.range a, g (r + a * q) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [mul_add, mul_one, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [add_comm]

private lemma sum_filter_range_mul (g : ℕ → ℝ) {M m b w : ℕ} (hdvd : m ∣ M) :
    ∑ x' ∈ (Finset.range (M * b)).filter (fun x' => x' % m = w), g x' =
      ∑ x ∈ (Finset.range M).filter (fun x => x % m = w),
        ∑ q ∈ Finset.range b, g (x + M * q) := by
  rw [Finset.sum_filter, sum_range_mul, Finset.sum_comm]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hmod : ∀ q : ℕ, (x + M * q) % m = x % m := fun q => by
    obtain ⟨c, rfl⟩ := hdvd
    rw [mul_assoc, Nat.add_mul_mod_self_left]
  simp_rw [hmod]
  split_ifs <;> simp

/-- Exact 1-digit lift weight identity: summing `stateWeight` over the `b` lifts of `x mod ℓ_k`
    modulo `ℓ_{k+1} = b * ℓ_k` multiplies by `θ_b = u * λ^t`. -/
lemma stateWeight_lift_sum {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (x : ℕ) :
    ∑ m ∈ Finset.range b, stateWeight (T^[hDepth b (k + 1)] (x + ellMod b k * m)) =
      suffixTheta b * stateWeight (T^[hDepth b k] x) := by
  obtain ⟨hu_odd, hfac⟩ := splitTwo_spec (by omega : 0 < b)
  set t := (splitTwo b).1
  set u := (splitTwo b).2
  conv_lhs => enter [1]; rw [hfac]
  rw [sum_range_mul]
  set y := T^[hDepth b k] x
  set D := iterMultT (hDepth b k) x * oddFactor b k
  have hD : D % 2 = 1 := by
    dsimp only [D]
    rw [Nat.mul_mod, iterMultT_odd, oddFactor_odd hb k]
  have hinner : ∀ q : ℕ,
      ∑ s ∈ Finset.range (2 ^ t),
        stateWeight (T^[hDepth b (k + 1)] (x + ellMod b k * (s + 2 ^ t * q))) =
      suffixLambda ^ t * stateWeight y := by
    intro q
    have hcongr : ∀ s : ℕ,
        stateWeight (T^[hDepth b (k + 1)] (x + ellMod b k * (s + 2 ^ t * q))) =
        stateWeight (T^[t] (y + 30 * D * s)) := fun s => by
      rw [hDepth_succ hk, add_comm (hDepth b k) t, Function.iterate_add_apply]
      have hfirst : T^[hDepth b k] (x + ellMod b k * (s + 2 ^ t * q)) =
          (y + 30 * D * s) + 30 * 2 ^ t * (D * q) := by
        rw [ellMod_eq hb hk,
            show 30 * 2 ^ hDepth b k * oddFactor b k * (s + 2 ^ t * q) =
              30 * 2 ^ hDepth b k * (oddFactor b k * (s + 2 ^ t * q)) by ring,
            T_iter_affine_suffix]
        dsimp only [y, D]; ring
      rw [hfirst, T_iter_affine_suffix]
      rw [← stateWeight_mod30, ← stateWeight_mod30 (T^[t] (y + 30 * D * s))]
      congr 1; simp [Nat.add_mul_mod_self_left, mul_assoc]
    simp_rw [hcongr]
    exact stateWeight_iter_sum t y D hD
  rw [Finset.sum_congr rfl (fun q _ => hinner q)]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold suffixTheta
  dsimp only [t, u, y]
  ring

lemma nuWeight_nonneg {b : ℕ} (hb : 2 ≤ b) (k w : ℕ) : 0 ≤ nuWeight b k w := by
  unfold nuWeight
  exact div_nonneg (Finset.sum_nonneg fun _ _ => stateWeight_nonneg _)
    (pow_nonneg (suffixTheta_pos hb).le k)

/-- Exact 1-step Kolmogorov consistency: `∑_{d < b} ν_{k+1}(w + d * b^k) = ν_k(w)`. -/
lemma nuWeight_consistent {b k w : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (hw : w < b ^ k) :
    ∑ d ∈ Finset.range b, nuWeight b (k + 1) (w + d * b ^ k) = nuWeight b k w := by
  unfold nuWeight
  rw [← Finset.sum_div]
  have hpart :
      ∑ d ∈ Finset.range b,
        ∑ x' ∈ (Finset.range (ellMod b (k + 1))).filter (fun x' => x' % b ^ (k + 1) = w + d * b ^ k),
          stateWeight (T^[hDepth b (k + 1)] x') =
      ∑ x' ∈ (Finset.range (ellMod b (k + 1))).filter (fun x' => x' % b ^ k = w),
        stateWeight (T^[hDepth b (k + 1)] x') := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    by_cases hxk : x' % b ^ k = w
    · simp only [hxk, ↓reduceIte]
      have hd0 : (x' / b ^ k) % b ∈ Finset.range b :=
        Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
      rw [Finset.sum_eq_single ((x' / b ^ k) % b)]
      · have hmod : x' % b ^ (k + 1) = w + (x' / b ^ k) % b * b ^ k := by
          rw [pow_succ, Nat.mod_mul, hxk]; ring
        simp [hmod]
      · intro d hd hne
        have hneq : x' % b ^ (k + 1) ≠ w + d * b ^ k := by
          intro heq
          have hmod : x' % b ^ (k + 1) = w + (x' / b ^ k) % b * b ^ k := by
            rw [pow_succ, Nat.mod_mul, hxk]; ring
          have hmul : d * b ^ k = (x' / b ^ k) % b * b ^ k := by omega
          exact hne (Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by omega)) hmul)
        simp [hneq]
      · intro hnot; exact absurd hd0 hnot
    · simp only [hxk, ↓reduceIte]
      refine Finset.sum_eq_zero fun d _ => ?_
      have hneq : x' % b ^ (k + 1) ≠ w + d * b ^ k := by
        intro heq
        apply hxk
        have hdvd : b ^ k ∣ b ^ (k + 1) := by rw [pow_succ]; exact dvd_mul_right _ _
        have h1 := congr_arg (· % b ^ k) heq
        rw [Nat.mod_mod_of_dvd x' hdvd, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hw] at h1
        exact h1
      simp [hneq]
  rw [hpart, ellMod_succ hb hk, mul_comm b (ellMod b k)]
  rw [sum_filter_range_mul _ (show b ^ k ∣ ellMod b k from Nat.dvd_lcm_right 30 (b ^ k))]
  simp_rw [stateWeight_lift_sum hb hk]
  rw [← Finset.mul_sum, pow_succ', mul_div_mul_left _ _ (suffixTheta_pos hb).ne']

/-- Multi-step Kolmogorov consistency: summing `ν_{k+j}(w)` over extensions of `v < b^k` gives `ν_k(v)`. -/
lemma nuWeight_consistent_add {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (j : ℕ) {v : ℕ} (hv : v < b ^ k) :
    ∑ w ∈ (Finset.range (b ^ (k + j))).filter (fun w => w % b ^ k = v), nuWeight b (k + j) w =
      nuWeight b k v := by
  induction j with
  | zero =>
    simp only [add_zero]
    rw [Finset.sum_filter, Finset.sum_eq_single v]
    · simp [Nat.mod_eq_of_lt hv]
    · intro w hw hne
      simp only [Finset.mem_range] at hw
      have : w % b ^ k ≠ v := by rw [Nat.mod_eq_of_lt hw]; exact hne
      simp [this]
    · intro hnot; exact absurd (Finset.mem_range.mpr hv) hnot
  | succ j ih =>
    have hpow : b ^ (k + (j + 1)) = b ^ (k + j) * b := by
      rw [← add_assoc, pow_succ]
    have hdvd : b ^ k ∣ b ^ (k + j) := by
      rw [pow_add]; exact dvd_mul_right _ _
    rw [hpow, sum_filter_range_mul _ hdvd]
    have hcongr : ∀ w ∈ (Finset.range (b ^ (k + j))).filter (fun w => w % b ^ k = v),
        ∑ d ∈ Finset.range b, nuWeight b (k + (j + 1)) (w + b ^ (k + j) * d) =
          nuWeight b (k + j) w := by
      intro w hw
      have hw_lt : w < b ^ (k + j) := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
      rw [show k + (j + 1) = (k + j) + 1 by omega]
      simpa [mul_comm (b ^ (k + j))] using nuWeight_consistent hb (by omega : 1 ≤ k + j) hw_lt
    rw [Finset.sum_congr rfl hcongr, ih]

/-- Constant total weight at every depth `k ≥ 1`. -/
lemma nuWeight_total_mass {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) :
    ∑ w ∈ Finset.range (b ^ k), nuWeight b k w = totalMass b := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => simp [totalMass]
    | succ k =>
      have hk1 : 1 ≤ k + 1 := by omega
      rw [pow_succ, sum_range_mul, Finset.sum_comm]
      have hcongr : ∀ w ∈ Finset.range (b ^ (k + 1)),
          ∑ d ∈ Finset.range b, nuWeight b (k + 1 + 1) (w + b ^ (k + 1) * d) =
            nuWeight b (k + 1) w := by
        intro w hw
        simpa [mul_comm (b ^ (k + 1))] using
          nuWeight_consistent hb hk1 (Finset.mem_range.mp hw)
      rw [Finset.sum_congr rfl hcongr, ih hk1]

lemma nuWeight_eq_zero_of_not_occupied {b k w : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (hw : w < b ^ k)
    (hnot : w ∉ occupiedFinset1 b k) : nuWeight b k w = 0 := by
  unfold nuWeight
  apply div_eq_zero_iff.mpr
  left
  refine Finset.sum_eq_zero fun x hx => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hx
  have hfalse : inLiveS (T^[hDepth b k] x) = false := by
    by_contra hne
    have htrue : inLiveS (T^[hDepth b k] x) = true := by
      cases h : inLiveS (T^[hDepth b k] x) <;> simp_all
    have hocc := (occupied1_iff_refined hb hk hw).mpr ⟨x, hx.1, hx.2, htrue⟩
    apply hnot
    classical
    unfold occupiedFinset1
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw, hocc⟩
  exact stateWeight_eq_zero_of_not_live hfalse

lemma nuWeight_upper {b k w : ℕ} (hb : 2 ≤ b) (_hk : 1 ≤ k) :
    nuWeight b k w ≤ 60 * aStar / (suffixTheta b) ^ k := by
  unfold nuWeight
  refine div_le_div_of_nonneg_right ?_ (pow_nonneg (suffixTheta_pos hb).le k)
  set F := (Finset.range (ellMod b k)).filter (fun x => x % b ^ k = w)
  have hterm : ∀ x ∈ F, stateWeight (T^[hDepth b k] x) ≤ 2 * aStar := by
    intro x _
    cases h : inLiveS (T^[hDepth b k] x)
    · rw [stateWeight_eq_zero_of_not_live h]; linarith [aStar_spec.1]
    · exact (stateWeight_bounds_of_live h).2
  have hcard : F.card ≤ 30 := by
    have hinj : Set.InjOn (fun x => x / b ^ k) (F : Set ℕ) := by
      intro x hx y hy heq
      simp only [Finset.mem_coe, F, Finset.mem_filter] at hx hy
      have h1 := Nat.div_add_mod x (b ^ k)
      have h2 := Nat.div_add_mod y (b ^ k)
      dsimp only at heq
      rw [← h1, ← h2, heq, hx.2, hy.2]
    have hmaps : Set.MapsTo (fun x => x / b ^ k) (F : Set ℕ) (Finset.range 30 : Set ℕ) := by
      intro x hx
      simp only [Finset.mem_coe, F, Finset.mem_filter, Finset.mem_range] at hx ⊢
      have hle : ellMod b k ≤ b ^ k * 30 := by rw [mul_comm]; exact ellMod_le_30_mul
      exact Nat.div_lt_of_lt_mul (lt_of_lt_of_le hx.1 hle)
    have := Finset.card_le_card_of_injOn (fun x => x / b ^ k) hmaps hinj
    simpa using this
  have hsum : ∑ x ∈ F, stateWeight (T^[hDepth b k] x) ≤ (F.card : ℝ) * (2 * aStar) := by
    calc ∑ x ∈ F, stateWeight (T^[hDepth b k] x)
        ≤ ∑ _x ∈ F, (2 * aStar) := Finset.sum_le_sum hterm
      _ = (F.card : ℝ) * (2 * aStar) := by simp
  have hcardR : (F.card : ℝ) ≤ 30 := by exact_mod_cast hcard
  have ha0 := aStar_spec.1
  nlinarith

lemma nuWeight_lower_of_occupied {b k w : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hw : w ∈ occupiedFinset1 b k) :
    2 * aStar ^ 3 / (suffixTheta b) ^ k ≤ nuWeight b k w := by
  classical
  unfold occupiedFinset1 at hw
  simp only [Finset.mem_filter, Finset.mem_range] at hw
  obtain ⟨x, hx_lt, hxw, hlive⟩ := (occupied1_iff_refined hb hk hw.1).mp hw.2
  unfold nuWeight
  refine div_le_div_of_nonneg_right ?_ (pow_nonneg (suffixTheta_pos hb).le k)
  have hx_mem : x ∈ (Finset.range (ellMod b k)).filter (fun x => x % b ^ k = w) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hx_lt, hxw⟩
  calc 2 * aStar ^ 3
      ≤ stateWeight (T^[hDepth b k] x) := (stateWeight_bounds_of_live hlive).1
    _ ≤ ∑ y ∈ (Finset.range (ellMod b k)).filter (fun y => y % b ^ k = w),
          stateWeight (T^[hDepth b k] y) :=
        Finset.single_le_sum (fun _ _ => stateWeight_nonneg _) hx_mem

lemma totalMass_pos {b : ℕ} (hb : 2 ≤ b) : 0 < totalMass b := by
  classical
  have h1mem : 1 % b ∈ occupiedFinset1 b 1 := by
    unfold occupiedFinset1
    simp only [pow_one, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mod_lt 1 (by omega), ⟨1, by omega, ⟨0, rfl⟩, rfl⟩⟩
  have hlow := nuWeight_lower_of_occupied hb (by omega) h1mem
  have hpos : 0 < 2 * aStar ^ 3 / (suffixTheta b) ^ 1 :=
    div_pos (mul_pos two_pos (pow_pos aStar_spec.1 3)) (pow_pos (suffixTheta_pos hb) 1)
  have hle : nuWeight b 1 (1 % b) ≤ totalMass b :=
    Finset.single_le_sum (fun w _ => nuWeight_nonneg hb 1 w)
      (Finset.mem_range.mpr (Nat.mod_lt 1 (by omega)))
  linarith

lemma sum_occupied_nuWeight {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) :
    ∑ w ∈ occupiedFinset1 b k, nuWeight b k w = totalMass b := by
  rw [← nuWeight_total_mass hb hk]
  refine Finset.sum_subset ?_ ?_
  · intro w hw
    classical
    unfold occupiedFinset1 at hw
    exact (Finset.mem_filter.mp hw).1
  · intro w hw hnot
    exact nuWeight_eq_zero_of_not_occupied hb hk (Finset.mem_range.mp hw) hnot

/-- Exact exponential scaling `C_1 * θ^k ≤ |Occ_b(k)| ≤ C_2 * θ^k` for all `k ≥ 1`. -/
lemma occupiedFinset1_card_bounds {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) :
    (totalMass b / (60 * aStar)) * (suffixTheta b) ^ k ≤ ((occupiedFinset1 b k).card : ℝ) ∧
    ((occupiedFinset1 b k).card : ℝ) ≤ (totalMass b / (2 * aStar ^ 3)) * (suffixTheta b) ^ k := by
  have ha0 := aStar_spec.1
  have hth_pos : 0 < (suffixTheta b) ^ k := pow_pos (suffixTheta_pos hb) k
  have hsum := sum_occupied_nuWeight hb hk
  constructor
  · have hup : totalMass b ≤ ((occupiedFinset1 b k).card : ℝ) * (60 * aStar / (suffixTheta b) ^ k) := by
      rw [← hsum]
      calc ∑ w ∈ occupiedFinset1 b k, nuWeight b k w
          ≤ ∑ _w ∈ occupiedFinset1 b k, (60 * aStar / (suffixTheta b) ^ k) :=
            Finset.sum_le_sum fun _ _ => nuWeight_upper hb hk
        _ = ((occupiedFinset1 b k).card : ℝ) * (60 * aStar / (suffixTheta b) ^ k) := by simp
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 60 * aStar)]
    have := mul_le_mul_of_nonneg_right hup hth_pos.le
    rw [mul_assoc, div_mul_cancel₀ _ hth_pos.ne'] at this
    exact this
  · have hlo : ((occupiedFinset1 b k).card : ℝ) * (2 * aStar ^ 3 / (suffixTheta b) ^ k) ≤ totalMass b := by
      rw [← hsum]
      calc ((occupiedFinset1 b k).card : ℝ) * (2 * aStar ^ 3 / (suffixTheta b) ^ k)
          = ∑ _w ∈ occupiedFinset1 b k, (2 * aStar ^ 3 / (suffixTheta b) ^ k) := by simp
        _ ≤ ∑ w ∈ occupiedFinset1 b k, nuWeight b k w :=
            Finset.sum_le_sum fun w hw => nuWeight_lower_of_occupied hb hk hw
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * aStar ^ 3)]
    have := mul_le_mul_of_nonneg_right hlo hth_pos.le
    rw [mul_assoc, div_mul_cancel₀ _ hth_pos.ne'] at this
    exact this

/-! ## Section 5: Exact Hausdorff measure and Hausdorff dimension `dim_H(ℰ_b)` -/

lemma suffixInterval_ediam_le {b : ℕ} (_hb : 2 ≤ b) (k w : ℕ) :
    Metric.ediam (suffixInterval b k w) ≤ ENNReal.ofReal (1 / (b : ℝ) ^ k) := by
  refine Metric.ediam_le fun x hx y hy => ?_
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  unfold suffixInterval at hx hy
  rw [Real.dist_eq, abs_le]
  have hdiff : ((revNat b k w : ℝ) + 1) / (b : ℝ) ^ k - (revNat b k w : ℝ) / (b : ℝ) ^ k =
      1 / (b : ℝ) ^ k := by
    rw [← sub_div, add_sub_cancel_left]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma suffixClosure1_subset_iUnion_occupied {b k : ℕ} (hb : 2 ≤ b) :
    suffixClosure1 b ⊆ ⋃ w : {w // w ∈ occupiedFinset1 b k}, suffixInterval b k w.1 := by
  have hclosed : IsClosed (⋃ w : {w // w ∈ occupiedFinset1 b k}, suffixInterval b k w.1) :=
    isClosed_iUnion_of_finite fun _ => isClosed_Icc
  refine closure_minimal ?_ hclosed
  rintro _ ⟨n, ⟨hn_pos, hn1⟩, rfl⟩
  have hmem : n % b ^ k ∈ occupiedFinset1 b k := by
    classical
    unfold occupiedFinset1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.mod_lt n (Nat.pow_pos (by omega))), ⟨n, hn_pos, hn1, rfl⟩⟩
  exact Set.mem_iUnion.mpr ⟨⟨n % b ^ k, hmem⟩, revExp_mem_suffixInterval hb k n⟩

/-- Positive finite upper bound on `μH[s](ℰ_b)`: `μH[s](ℰ_b) ≤ totalMass b / (2 * aStar^3) < ∞`. -/
lemma hausdorffMeasure_suffixClosure1_le {b : ℕ} (hb : 2 ≤ b) :
    μH[suffixDimVal b] (suffixClosure1 b) ≤ ENNReal.ofReal (totalMass b / (2 * aStar ^ 3)) := by
  set s := suffixDimVal b
  have hs_pos : 0 < s := suffixDimVal_pos hb
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
  let r : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / (b : ℝ) ^ (n + 1))
  have hr_tend : Tendsto r atTop (nhds 0) := by
    have h0 : Tendsto (fun n : ℕ => 1 / (b : ℝ) ^ (n + 1)) atTop (nhds 0) := by
      simp_rw [one_div]
      exact (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hb1)).comp
        (tendsto_add_atTop_nat 1)
    have hcomp : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (b : ℝ) ^ (n + 1))) atTop (nhds (ENNReal.ofReal 0)) :=
      (ENNReal.continuous_ofReal.tendsto 0).comp h0
    simpa [r, ENNReal.ofReal_zero] using hcomp
  let t : ∀ n : ℕ, {w // w ∈ occupiedFinset1 b (n + 1)} → Set ℝ :=
    fun n i => suffixInterval b (n + 1) i.1
  have hle := Measure.hausdorffMeasure_le_liminf_sum s (suffixClosure1 b) r hr_tend t
    (Eventually.of_forall fun n i => suffixInterval_ediam_le hb (n + 1) i.1)
    (Eventually.of_forall fun n => suffixClosure1_subset_iUnion_occupied hb)
  refine hle.trans ?_
  have hbound : ∀ n : ℕ,
      ∑ i : {w // w ∈ occupiedFinset1 b (n + 1)}, Metric.ediam (t n i) ^ s ≤
        ENNReal.ofReal (totalMass b / (2 * aStar ^ 3)) := by
    intro n
    have hstep1 : ∑ i : {w // w ∈ occupiedFinset1 b (n + 1)}, Metric.ediam (t n i) ^ s ≤
        ∑ _i : {w // w ∈ occupiedFinset1 b (n + 1)}, (r n) ^ s :=
      Finset.sum_le_sum fun i _ => ENNReal.rpow_le_rpow (suffixInterval_ediam_le hb (n + 1) i.1) hs_pos.le
    refine hstep1.trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    have hrs : (r n) ^ s = ENNReal.ofReal (1 / (suffixTheta b) ^ (n + 1)) := by
      dsimp only [r]
      rw [ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < 1 / (b : ℝ) ^ (n + 1)),
          base_inv_rpow_suffixDimVal hb (n + 1)]
    rw [hrs, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hcard := (occupiedFinset1_card_bounds hb (by omega : 1 ≤ n + 1)).2
    have hth_pos : 0 < (suffixTheta b) ^ (n + 1) := pow_pos (suffixTheta_pos hb) (n + 1)
    calc ((occupiedFinset1 b (n + 1)).card : ℝ) * (1 / (suffixTheta b) ^ (n + 1))
        ≤ ((totalMass b / (2 * aStar ^ 3)) * (suffixTheta b) ^ (n + 1)) *
            (1 / (suffixTheta b) ^ (n + 1)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = totalMass b / (2 * aStar ^ 3) := by field_simp [hth_pos.ne']
  exact liminf_le_of_le (by isBoundedDefault) fun c hc => by
    obtain ⟨n, hcn⟩ := (hc.and (Eventually.of_forall hbound)).exists
    exact hcn.1.trans hcn.2

lemma hausdorffMeasure_suffixClosure1_ne_top {b : ℕ} (hb : 2 ≤ b) :
    μH[suffixDimVal b] (suffixClosure1 b) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hausdorffMeasure_suffixClosure1_le hb)

/-- Subadditivity `(x + y)^s ≤ x^s + y^s` for `x, y ≥ 0` and `0 < s ≤ 1`. -/
private lemma rpow_add_le_add_rpow {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs0 : 0 < s) (hs1 : s ≤ 1) : (x + y) ^ s ≤ x ^ s + y ^ s := by
  by_cases hxy : x + y = 0
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0, Real.zero_rpow hs0.ne']
  · have hpos : 0 < x + y := lt_of_le_of_ne (by linarith) (Ne.symm hxy)
    have h1 : x / (x + y) ≤ (x / (x + y)) ^ s :=
      Real.self_le_rpow_of_le_one (div_nonneg hx hpos.le) (div_le_one_of_le₀ (by linarith) hpos.le) hs1
    have h2 : y / (x + y) ≤ (y / (x + y)) ^ s :=
      Real.self_le_rpow_of_le_one (div_nonneg hy hpos.le) (div_le_one_of_le₀ (by linarith) hpos.le) hs1
    rw [Real.div_rpow hx hpos.le] at h1
    rw [Real.div_rpow hy hpos.le] at h2
    have hsum : (x + y) / (x + y) ≤ (x ^ s + y ^ s) / (x + y) ^ s := by
      rw [add_div, add_div]; linarith
    rw [div_self hpos.ne', one_le_div (Real.rpow_pos_of_pos hpos s)] at hsum
    exact hsum

private lemma sum_biUnion_le_nonneg {α β : Type*} [DecidableEq β] (s : Finset α)
    (t : α → Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hu := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    have hinter : 0 ≤ ∑ b ∈ t a ∩ s.biUnion t, f b := Finset.sum_nonneg fun b _ => hf b
    have hstep : ∑ b ∈ t a ∪ s.biUnion t, f b ≤ ∑ b ∈ t a, f b + ∑ b ∈ s.biUnion t, f b := by
      linarith
    exact hstep.trans (add_le_add le_rfl ih)

/-- An open ball of radius `δ` with `2 * δ < b^(-k)` meets at most `2` level-`k` intervals. -/
private lemma card_suffixIntervals_meeting_ball_le {b k : ℕ} (hb : 2 ≤ b) {x δ : ℝ}
    [DecidablePred fun v => (Metric.ball x δ ∩ suffixInterval b k v).Nonempty]
    (h2δ : 2 * δ < 1 / (b : ℝ) ^ k) :
    ((Finset.range (b ^ k)).filter (fun v => (Metric.ball x δ ∩ suffixInterval b k v).Nonempty)).card ≤ 2 := by
  classical
  set S := (Finset.range (b ^ k)).filter (fun v => (Metric.ball x δ ∩ suffixInterval b k v).Nonempty)
  have hcard_eq : S.card = (S.image (revNat b k)).card := by
    rw [Finset.card_image_of_injOn]
    exact (revNat_injOn (by omega) k).mono (fun v hv => (Finset.mem_filter.mp hv).1)
  rw [hcard_eq]
  by_cases hempty : (S.image (revNat b k)).Nonempty
  · set m0 := (S.image (revNat b k)).min' hempty
    have hsub : S.image (revNat b k) ⊆ {m0, m0 + 1} := by
      intro m hm
      have hm0_le : m0 ≤ m := Finset.min'_le _ m hm
      have hm0_mem : m0 ∈ S.image (revNat b k) := Finset.min'_mem _ hempty
      simp only [Finset.mem_image, S, Finset.mem_filter] at hm hm0_mem
      obtain ⟨v0, ⟨_, ⟨y0, hy0_ball, hy0_int⟩⟩, hv0⟩ := hm0_mem
      obtain ⟨v, ⟨_, ⟨y, hy_ball, hy_int⟩⟩, hv⟩ := hm
      have hbk_pos : (0 : ℝ) < (b : ℝ) ^ k := by positivity
      have hy_dist : y - y0 < 2 * δ := by
        have h1 : |y - x| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hy_ball
        have h2 : |y0 - x| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hy0_ball
        rw [abs_lt] at h1 h2
        linarith
      unfold suffixInterval at hy0_int hy_int
      rw [hv0] at hy0_int
      rw [hv] at hy_int
      have hgap : (m : ℝ) - ((m0 : ℝ) + 1) < 1 := by
        have hdiv : ((m : ℝ) - ((m0 : ℝ) + 1)) / (b : ℝ) ^ k < 1 / (b : ℝ) ^ k := by
          rw [sub_div]
          linarith [hy0_int.2, hy_int.1, hy_dist, h2δ]
        exact (div_lt_div_iff_of_pos_right hbk_pos).mp hdiv
      have hm_le : m ≤ m0 + 1 := by
        have hcast : (m : ℝ) < (m0 + 2 : ℕ) := by push_cast; linarith
        have hnat : m < m0 + 2 := by exact_mod_cast hcast
        omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · simp [Finset.not_nonempty_iff_eq_empty.mp hempty]

/-- Positive lower bound on `μH[s](ℰ_b)` via compactness and consistent Perron weights `ν_k`. -/
lemma hausdorffMeasure_suffixClosure1_pos {b : ℕ} (hb : 2 ≤ b) :
    0 < μH[suffixDimVal b] (suffixClosure1 b) := by
  classical
  set s := suffixDimVal b
  set θ := suffixTheta b
  have hs_pos : 0 < s := suffixDimVal_pos hb
  have hs_le1 : s ≤ 1 := suffixDimVal_le_one hb
  have hθ_pos : 0 < θ := suffixTheta_pos hb
  have hθ_gt1 : 1 < θ := suffixTheta_gt_one hb
  have hM0_pos : 0 < totalMass b := totalMass_pos hb
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
  set C0 : ℝ := max (240 * aStar * θ) (2 * totalMass b * θ)
  have hC0_pos : 0 < C0 := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have h2s_le : (2 : ℝ) ^ s ≤ 2 := by
    calc (2 : ℝ) ^ s ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs_le1
      _ = 2 := Real.rpow_one 2
  suffices hmain : ENNReal.ofReal (totalMass b / C0) ≤ μH[s] (suffixClosure1 b) by
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (div_pos hM0_pos hC0_pos)) hmain
  rw [Measure.hausdorffMeasure_apply]
  refine le_iSup₂_of_le (1 : ℝ≥0∞) zero_lt_one ?_
  refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hdiam => ?_
  set S_rhs : ℝ≥0∞ := ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s
  by_cases htop : S_rhs = ⊤
  · rw [htop]; exact le_top
  · -- Show totalMass b ≤ C0 * S_rhs.toReal via arbitrary η > 0
    have hrhs_eq : S_rhs = ENNReal.ofReal S_rhs.toReal := (ENNReal.ofReal_toReal htop).symm
    rw [hrhs_eq]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ hC0_pos, mul_comm]
    have ha0 := aStar_spec.1
    set r2 : ℝ := (1 / 2 : ℝ) ^ s
    have hr2_pos : 0 < r2 := Real.rpow_pos_of_pos (by norm_num) s
    have hr2_lt1 : r2 < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hs_pos
    set G : ℝ := r2 / (1 - r2)
    have hG_pos : 0 < G := div_pos hr2_pos (by linarith)
    have hfor_eta : ∀ η : ℝ, 0 < η → totalMass b ≤ C0 * S_rhs.toReal + C0 * G * η ^ s := by
      intro η hη
      -- Open cover V n ⊇ t n
      let δ : ℕ → ℝ := fun n => Metric.diam (t n) + η * (1 / 2 : ℝ) ^ (n + 1)
      have hδ_pos : ∀ n, 0 < δ n := fun n => by
        dsimp only [δ]
        have : 0 ≤ Metric.diam (t n) := Metric.diam_nonneg
        have : 0 < η * (1 / 2 : ℝ) ^ (n + 1) := by positivity
        linarith
      let V : ℕ → Set ℝ := fun n =>
        if hne : (t n).Nonempty then Metric.ball hne.some (δ n) else ∅
      have hV_open : ∀ n, IsOpen (V n) := fun n => by
        dsimp only [V]; split_ifs
        · exact Metric.isOpen_ball
        · exact isOpen_empty
      have ht_sub_V : ∀ n, t n ⊆ V n := fun n y hy => by
        have hne : (t n).Nonempty := ⟨y, hy⟩
        dsimp only [V]
        simp only [hne, ↓reduceDIte, Metric.mem_ball]
        have hbd : Bornology.IsBounded (t n) :=
          Metric.isBounded_iff_ediam_ne_top.mpr (ne_top_of_le_ne_top ENNReal.one_ne_top (hdiam n))
        have hdist : dist y hne.some ≤ Metric.diam (t n) :=
          Metric.dist_le_diam_of_mem hbd hy hne.some_mem
        have : 0 < η * (1 / 2 : ℝ) ^ (n + 1) := by positivity
        dsimp only [δ]; linarith
      have hopen_cov : suffixClosure1 b ⊆ ⋃ n, V n :=
        hcov.trans (Set.iUnion_mono ht_sub_V)
      obtain ⟨F, hF_cov⟩ := (isCompact_suffixClosure1 hb).elim_finite_subcover V hV_open hopen_cov
      set F' := F.filter (fun n => (t n).Nonempty)
      have hF'_cov : suffixClosure1 b ⊆ ⋃ n ∈ F', V n := by
        intro y hy
        obtain ⟨n, hnF, hyV⟩ := Set.mem_iUnion₂.mp (hF_cov hy)
        have hne : (t n).Nonempty := by
          by_contra hnot
          dsimp only [V] at hyV
          simp only [hnot, ↓reduceDIte] at hyV
          exact hyV
        exact Set.mem_iUnion₂.mpr ⟨n, Finset.mem_filter.mpr ⟨hnF, hne⟩, hyV⟩
      -- Choose depth kOf n ≥ 1 for each n
      have hex_k : ∀ n : ℕ, ∃ k : ℕ, 1 / (b : ℝ) ^ (k + 1) ≤ 2 * δ n := by
        intro n
        have h0 : Tendsto (fun k : ℕ => 1 / (b : ℝ) ^ (k + 1)) atTop (nhds 0) := by
          simp_rw [one_div]
          exact (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hb1)).comp
            (tendsto_add_atTop_nat 1)
        have h2δ_pos : (0 : ℝ) < 2 * δ n := by linarith [hδ_pos n]
        obtain ⟨k, hk⟩ := (h0.eventually (gt_mem_nhds h2δ_pos)).exists
        exact ⟨k, hk.le⟩
      let kOf : ℕ → ℕ := fun n =>
        if 2 * δ n < 1 / (b : ℝ) then Nat.find (hex_k n) else 1
      have hkOf_ge1 : ∀ n, 1 ≤ kOf n := fun n => by
        dsimp only [kOf]
        split_ifs with hsmall
        · have hne0 : Nat.find (hex_k n) ≠ 0 := by
            intro h0
            have hspec := Nat.find_spec (hex_k n)
            rw [h0, zero_add, pow_one] at hspec
            linarith
          omega
        · exact le_rfl
      set K := max 1 (F'.sup kOf)
      have hK_ge1 : 1 ≤ K := le_max_left _ _
      have hkOf_le_K : ∀ n ∈ F', kOf n ≤ K := fun n hn =>
        (Finset.le_sup (f := kOf) hn).trans (le_max_right _ _)
      -- Every occupied w < b^K belongs to some n ∈ F' and its ancestor v = w % b^(kOf n) meets V n
      let hitIntervals (n : ℕ) : Finset ℕ :=
        (Finset.range (b ^ kOf n)).filter (fun v => (V n ∩ suffixInterval b (kOf n) v).Nonempty)
      let descSet (n v : ℕ) : Finset ℕ :=
        (Finset.range (b ^ K)).filter (fun w => w % b ^ kOf n = v)
      have hocc_sub : occupiedFinset1 b K ⊆
          F'.biUnion (fun n => (hitIntervals n).biUnion (fun v => descSet n v)) := by
        intro w hw
        have hw_mem := hw
        unfold occupiedFinset1 at hw_mem
        simp only [Finset.mem_filter, Finset.mem_range] at hw_mem
        obtain ⟨hw_lt, m_w, hm_pos, hm1, hmw⟩ := hw_mem
        have hy_cl : revExp b m_w ∈ suffixClosure1 b :=
          subset_closure ⟨m_w, ⟨hm_pos, hm1⟩, rfl⟩
        obtain ⟨n, hnF', hyV⟩ := Set.mem_iUnion₂.mp (hF'_cov hy_cl)
        set k := kOf n
        have hk_le : k ≤ K := hkOf_le_K n hnF'
        set v := w % b ^ k
        have hv_lt : v < b ^ k := Nat.mod_lt w (Nat.pow_pos (by omega))
        have hmk : m_w % b ^ k = v := by
          have hdvd : b ^ k ∣ b ^ K := Nat.pow_dvd_pow b hk_le
          dsimp only [v]
          rw [← hmw, Nat.mod_mod_of_dvd m_w hdvd]
        have hy_int : revExp b m_w ∈ suffixInterval b k v := by
          rw [← hmk]; exact revExp_mem_suffixInterval hb k m_w
        simp only [Finset.mem_biUnion, hitIntervals, descSet, Finset.mem_filter, Finset.mem_range]
        exact ⟨n, hnF', v, ⟨hv_lt, ⟨revExp b m_w, hyV, hy_int⟩⟩, ⟨hw_lt, rfl⟩⟩
      -- Sum nuWeight b K w over occupiedFinset1 b K
      have hmass_le : totalMass b ≤
          ∑ n ∈ F', ∑ v ∈ hitIntervals n, nuWeight b (kOf n) v := by
        rw [← sum_occupied_nuWeight hb hK_ge1]
        calc ∑ w ∈ occupiedFinset1 b K, nuWeight b K w
            ≤ ∑ w ∈ F'.biUnion (fun n => (hitIntervals n).biUnion (fun v => descSet n v)),
                nuWeight b K w :=
              Finset.sum_le_sum_of_subset_of_nonneg hocc_sub fun _ _ _ => nuWeight_nonneg hb K _
          _ ≤ ∑ n ∈ F', ∑ w ∈ (hitIntervals n).biUnion (fun v => descSet n v), nuWeight b K w :=
              sum_biUnion_le_nonneg F' _ _ (fun _ => nuWeight_nonneg hb K _)
          _ ≤ ∑ n ∈ F', ∑ v ∈ hitIntervals n, ∑ w ∈ descSet n v, nuWeight b K w :=
              Finset.sum_le_sum fun n _ =>
                sum_biUnion_le_nonneg (hitIntervals n) _ _ (fun _ => nuWeight_nonneg hb K _)
          _ = ∑ n ∈ F', ∑ v ∈ hitIntervals n, nuWeight b (kOf n) v := by
              refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun v hv => ?_
              have hk_le : kOf n ≤ K := hkOf_le_K n hn
              have hv_lt : v < b ^ kOf n := Finset.mem_range.mp (Finset.mem_filter.mp hv).1
              have hKeq : K = kOf n + (K - kOf n) := by omega
              dsimp only [descSet]
              conv_lhs => rw [hKeq]
              exact nuWeight_consistent_add hb (hkOf_ge1 n) (K - kOf n) hv_lt
      -- Bound each term n ∈ F' by C0 * (δ n)^s
      have hterm_n : ∀ n ∈ F', ∑ v ∈ hitIntervals n, nuWeight b (kOf n) v ≤ C0 * (δ n) ^ s := by
        intro n hn
        have hne : (t n).Nonempty := (Finset.mem_filter.mp hn).2
        have hVeq : V n = Metric.ball hne.some (δ n) := by dsimp only [V]; simp [hne]
        by_cases hsmall : 2 * δ n < 1 / (b : ℝ)
        · have hk_eq : kOf n = Nat.find (hex_k n) := by dsimp only [kOf]; simp only [hsmall, ↓reduceIte]
          have hk1 : 1 ≤ kOf n := hkOf_ge1 n
          have hlo_δ : 1 / (b : ℝ) ^ (kOf n + 1) ≤ 2 * δ n := by
            rw [hk_eq]; exact Nat.find_spec (hex_k n)
          have hhi_δ : 2 * δ n < 1 / (b : ℝ) ^ (kOf n) := by
            have hpred_lt : kOf n - 1 < Nat.find (hex_k n) := by omega
            have hnot := Nat.find_min (hex_k n) hpred_lt
            have hadd : kOf n - 1 + 1 = kOf n := by omega
            rw [hadd] at hnot
            exact lt_of_not_ge hnot
          have hcard2 : (hitIntervals n).card ≤ 2 := by
            dsimp only [hitIntervals]
            rw [hVeq]
            exact card_suffixIntervals_meeting_ball_le hb hhi_δ
          have hsum_le : ∑ v ∈ hitIntervals n, nuWeight b (kOf n) v ≤
              2 * (60 * aStar / θ ^ (kOf n)) := by
            calc ∑ v ∈ hitIntervals n, nuWeight b (kOf n) v
                ≤ ∑ _v ∈ hitIntervals n, (60 * aStar / θ ^ (kOf n)) :=
                  Finset.sum_le_sum fun _ _ => nuWeight_upper hb hk1
              _ = ((hitIntervals n).card : ℝ) * (60 * aStar / θ ^ (kOf n)) := by simp
              _ ≤ 2 * (60 * aStar / θ ^ (kOf n)) := by
                  have hcardR : ((hitIntervals n).card : ℝ) ≤ 2 := by exact_mod_cast hcard2
                  exact mul_le_mul_of_nonneg_right hcardR (by positivity)
          have hth_le : 1 / θ ^ (kOf n) ≤ 2 * θ * (δ n) ^ s := by
            have hpow : 1 / θ ^ (kOf n + 1) ≤ (2 * δ n) ^ s := by
              rw [← base_inv_rpow_suffixDimVal hb (kOf n + 1)]
              exact Real.rpow_le_rpow (by positivity) hlo_δ hs_pos.le
            have h2δ : (2 * δ n) ^ s ≤ 2 * (δ n) ^ s := by
              rw [Real.mul_rpow (by norm_num) (hδ_pos n).le]
              exact mul_le_mul_of_nonneg_right h2s_le (Real.rpow_nonneg (hδ_pos n).le s)
            have heq : 1 / θ ^ (kOf n) = θ * (1 / θ ^ (kOf n + 1)) := by
              rw [pow_succ]; field_simp [hθ_pos.ne']
            rw [heq]
            calc θ * (1 / θ ^ (kOf n + 1)) ≤ θ * (2 * δ n) ^ s :=
                  mul_le_mul_of_nonneg_left hpow hθ_pos.le
              _ ≤ θ * (2 * (δ n) ^ s) := mul_le_mul_of_nonneg_left h2δ hθ_pos.le
              _ = 2 * θ * (δ n) ^ s := by ring
          have hC0_ge : 240 * aStar * θ ≤ C0 := le_max_left _ _
          calc ∑ v ∈ hitIntervals n, nuWeight b (kOf n) v
              ≤ 2 * (60 * aStar / θ ^ (kOf n)) := hsum_le
            _ = 120 * aStar * (1 / θ ^ (kOf n)) := by ring
            _ ≤ 120 * aStar * (2 * θ * (δ n) ^ s) :=
                mul_le_mul_of_nonneg_left hth_le (by positivity)
            _ = (240 * aStar * θ) * (δ n) ^ s := by ring
            _ ≤ C0 * (δ n) ^ s :=
                mul_le_mul_of_nonneg_right hC0_ge (Real.rpow_nonneg (hδ_pos n).le s)
        · have hk_eq : kOf n = 1 := by dsimp only [kOf]; simp only [hsmall, ↓reduceIte]
          have hge_b : 1 / (b : ℝ) ≤ 2 * δ n := le_of_not_gt hsmall
          have hsum_le : ∑ v ∈ hitIntervals n, nuWeight b (kOf n) v ≤ totalMass b := by
            rw [hk_eq]
            dsimp only [hitIntervals]
            rw [hk_eq, pow_one]
            calc ∑ v ∈ (Finset.range b).filter _, nuWeight b 1 v
                ≤ ∑ v ∈ Finset.range b, nuWeight b 1 v :=
                  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                    (fun _ _ _ => nuWeight_nonneg hb 1 _)
              _ = totalMass b := rfl
          have h1_le : 1 ≤ 2 * θ * (δ n) ^ s := by
            have hpow : 1 / θ ≤ (2 * δ n) ^ s := by
              have hinv := base_inv_rpow_suffixDimVal hb 1
              simp only [pow_one] at hinv
              rw [← hinv]
              exact Real.rpow_le_rpow (by positivity) hge_b hs_pos.le
            have h2δ : (2 * δ n) ^ s ≤ 2 * (δ n) ^ s := by
              rw [Real.mul_rpow (by norm_num) (hδ_pos n).le]
              exact mul_le_mul_of_nonneg_right h2s_le (Real.rpow_nonneg (hδ_pos n).le s)
            calc (1 : ℝ) = θ * (1 / θ) := by field_simp [hθ_pos.ne']
              _ ≤ θ * (2 * δ n) ^ s := mul_le_mul_of_nonneg_left hpow hθ_pos.le
              _ ≤ θ * (2 * (δ n) ^ s) := mul_le_mul_of_nonneg_left h2δ hθ_pos.le
              _ = 2 * θ * (δ n) ^ s := by ring
          have hC0_ge : 2 * totalMass b * θ ≤ C0 := le_max_right _ _
          calc ∑ v ∈ hitIntervals n, nuWeight b (kOf n) v
              ≤ totalMass b := hsum_le
            _ = totalMass b * 1 := (mul_one _).symm
            _ ≤ totalMass b * (2 * θ * (δ n) ^ s) := mul_le_mul_of_nonneg_left h1_le hM0_pos.le
            _ = (2 * totalMass b * θ) * (δ n) ^ s := by ring
            _ ≤ C0 * (δ n) ^ s :=
                mul_le_mul_of_nonneg_right hC0_ge (Real.rpow_nonneg (hδ_pos n).le s)
      -- Split (δ n)^s ≤ (diam (t n))^s + η^s * r2^(n+1)
      have hsplit : ∑ n ∈ F', (δ n) ^ s ≤
          (∑ n ∈ F', (Metric.diam (t n)) ^ s) + η ^ s * ∑ n ∈ F', r2 ^ (n + 1) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun n _ => ?_
        have h1 := rpow_add_le_add_rpow (Metric.diam_nonneg (s := t n))
          (by positivity : 0 ≤ η * (1 / 2 : ℝ) ^ (n + 1)) hs_pos hs_le1
        have h2 : (η * (1 / 2 : ℝ) ^ (n + 1)) ^ s = η ^ s * r2 ^ (n + 1) := by
          rw [Real.mul_rpow hη.le (by positivity), ← Real.rpow_natCast (1 / 2 : ℝ),
              ← Real.rpow_mul (by norm_num), mul_comm ((n + 1 : ℕ) : ℝ) s,
              Real.rpow_mul (by norm_num), Real.rpow_natCast]
        linarith
      -- Bound ∑ n ∈ F', (Metric.diam (t n))^s ≤ S_rhs.toReal
      have hdiam_sum : ∑ n ∈ F', (Metric.diam (t n)) ^ s ≤ S_rhs.toReal := by
        rw [← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg, ← hrhs_eq]
        rw [ENNReal.ofReal_sum_of_nonneg fun n _ => Real.rpow_nonneg Metric.diam_nonneg s]
        have hterm_eq : ∀ n ∈ F',
            ENNReal.ofReal ((Metric.diam (t n)) ^ s) =
              ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ s := by
          intro n hn
          have hne : (t n).Nonempty := (Finset.mem_filter.mp hn).2
          have hnt : Metric.ediam (t n) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hdiam n)
          rw [ciSup_pos hne, ← ENNReal.ofReal_rpow_of_nonneg (Metric.diam_nonneg (s := t n)) hs_pos.le,
              Metric.diam, ENNReal.ofReal_toReal hnt]
        rw [Finset.sum_congr rfl hterm_eq]
        exact ENNReal.sum_le_tsum F'
      -- Bound ∑ n ∈ F', r2^(n+1) ≤ G
      have hgeom_sum : ∑ n ∈ F', r2 ^ (n + 1) ≤ G := by
        have hsum_able : Summable (fun n : ℕ => r2 ^ (n + 1)) := by
          have : (fun n : ℕ => r2 ^ (n + 1)) = fun n => r2 * r2 ^ n := by
            ext n; rw [pow_succ']
          rw [this]
          exact (summable_geometric_of_lt_one hr2_pos.le hr2_lt1).mul_left r2
        have htsum : ∑' n : ℕ, r2 ^ (n + 1) = G := by
          have : (fun n : ℕ => r2 ^ (n + 1)) = fun n => r2 * r2 ^ n := by
            ext n; rw [pow_succ']
          rw [this, tsum_mul_left, tsum_geometric_of_lt_one hr2_pos.le hr2_lt1]
          dsimp only [G]; ring
        rw [← htsum]
        exact hsum_able.sum_le_tsum F' (fun n _ => pow_nonneg hr2_pos.le _)
      have h1 : totalMass b ≤ C0 * ∑ n ∈ F', (δ n) ^ s := by
        calc totalMass b ≤ ∑ n ∈ F', ∑ v ∈ hitIntervals n, nuWeight b (kOf n) v := hmass_le
          _ ≤ ∑ n ∈ F', C0 * (δ n) ^ s := Finset.sum_le_sum hterm_n
          _ = C0 * ∑ n ∈ F', (δ n) ^ s := (Finset.mul_sum _ _ _).symm
      have h2 : ∑ n ∈ F', (δ n) ^ s ≤ S_rhs.toReal + G * η ^ s := by
        have hmul : η ^ s * ∑ n ∈ F', r2 ^ (n + 1) ≤ η ^ s * G :=
          mul_le_mul_of_nonneg_left hgeom_sum (Real.rpow_nonneg hη.le s)
        linarith
      nlinarith
    -- Send η = (1/2)^m → 0
    have htend0 : Tendsto (fun m : ℕ => C0 * S_rhs.toReal + C0 * G * ((1 / 2 : ℝ) ^ m) ^ s)
        atTop (nhds (C0 * S_rhs.toReal)) := by
      have hr : Tendsto (fun m : ℕ => r2 ^ m) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hr2_pos.le hr2_lt1
      have hpow_eq : ∀ m : ℕ, ((1 / 2 : ℝ) ^ m) ^ s = r2 ^ m := fun m => by
        rw [← Real.rpow_natCast (1 / 2 : ℝ), ← Real.rpow_mul (by norm_num),
            mul_comm (m : ℝ) s, Real.rpow_mul (by norm_num), Real.rpow_natCast]
      simp_rw [hpow_eq]
      simpa using (hr.const_mul (C0 * G)).const_add (C0 * S_rhs.toReal)
    exact ge_of_tendsto htend0 (Eventually.of_forall fun m => hfor_eta _ (by positivity))

lemma hausdorffMeasure_suffixClosure1_ne_zero {b : ℕ} (hb : 2 ≤ b) :
    μH[suffixDimVal b] (suffixClosure1 b) ≠ 0 :=
  ne_of_gt (hausdorffMeasure_suffixClosure1_pos hb)

/-- Exact Hausdorff dimension of `ℰ_b`: `dim_H(ℰ_b) = (log u + t * log λ) / log b`. -/
theorem suffixClosure1_dimH {b : ℕ} (hb : 2 ≤ b) :
    dimH (suffixClosure1 b) = ENNReal.ofReal (suffixDimVal b) := by
  set d : ℝ≥0 := ⟨suffixDimVal b, (suffixDimVal_pos hb).le⟩
  have h1 : μH[(d : ℝ)] (suffixClosure1 b) ≠ 0 := hausdorffMeasure_suffixClosure1_ne_zero hb
  have h2 : μH[(d : ℝ)] (suffixClosure1 b) ≠ ⊤ := hausdorffMeasure_suffixClosure1_ne_top hb
  rw [dimH_of_hausdorffMeasure_ne_zero_ne_top h1 h2, ENNReal.ofReal_eq_coe_nnreal (suffixDimVal_pos hb).le]
  rfl

/-! ## Section 6: Exact box-counting dimension `dim_B(ℰ_b)` -/

/-- Minimum number of sets of diameter `≤ δ` needed to cover `E ⊆ ℝ`. -/
noncomputable def boxCoverNumber (E : Set ℝ) (δ : ℝ) : ℕ :=
  sInf {m : ℕ | ∃ F : Finset (Set ℝ), F.card = m ∧
    (∀ U ∈ F, Metric.ediam U ≤ ENNReal.ofReal δ) ∧ E ⊆ ⋃ U ∈ F, U}

/-- Lower box-counting (Minkowski) dimension of `E ⊆ ℝ`. -/
noncomputable def lowerBoxDim (E : Set ℝ) : ℝ :=
  Filter.liminf (fun δ : ℝ => Real.log (boxCoverNumber E δ : ℝ) / Real.log (1 / δ))
    (nhdsWithin 0 (Set.Ioi 0))

/-- Upper box-counting (Minkowski) dimension of `E ⊆ ℝ`. -/
noncomputable def upperBoxDim (E : Set ℝ) : ℝ :=
  Filter.limsup (fun δ : ℝ => Real.log (boxCoverNumber E δ : ℝ) / Real.log (1 / δ))
    (nhdsWithin 0 (Set.Ioi 0))

/-- Two-sided scaling bound on `boxCoverNumber (ℰ_b) δ` for all `0 < δ < b⁻¹`. -/
lemma boxCoverNumber_suffixClosure1_bounds {b : ℕ} (hb : 2 ≤ b) {δ : ℝ}
    (hδ0 : 0 < δ) (hδb : δ < 1 / (b : ℝ)) :
    (totalMass b / (120 * aStar * suffixTheta b)) * δ ^ (-suffixDimVal b) ≤
      (boxCoverNumber (suffixClosure1 b) δ : ℝ) ∧
    (boxCoverNumber (suffixClosure1 b) δ : ℝ) ≤
      (totalMass b * suffixTheta b / (2 * aStar ^ 3)) * δ ^ (-suffixDimVal b) := by
  classical
  set s := suffixDimVal b
  set θ := suffixTheta b
  have hs_pos : 0 < s := suffixDimVal_pos hb
  have hθ_pos : 0 < θ := suffixTheta_pos hb
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
  have hex_k : ∃ k : ℕ, 1 / (b : ℝ) ^ (k + 1) ≤ δ := by
    have h0 : Tendsto (fun k : ℕ => 1 / (b : ℝ) ^ (k + 1)) atTop (nhds 0) := by
      simp_rw [one_div]
      exact (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hb1)).comp
        (tendsto_add_atTop_nat 1)
    obtain ⟨k, hk⟩ := (h0.eventually (gt_mem_nhds hδ0)).exists
    exact ⟨k, hk.le⟩
  set k := Nat.find hex_k
  have hk_ge1 : 1 ≤ k := by
    by_contra h0
    have hk0 : Nat.find hex_k = 0 := by omega
    have hspec := Nat.find_spec hex_k
    rw [hk0, zero_add, pow_one] at hspec
    linarith
  have hlo_δ : 1 / (b : ℝ) ^ (k + 1) ≤ δ := Nat.find_spec hex_k
  have hhi_δ : δ < 1 / (b : ℝ) ^ k := by
    have hnot := Nat.find_min hex_k (show k - 1 < k by omega)
    rw [show k - 1 + 1 = k by omega] at hnot
    exact lt_of_not_ge hnot
  -- Construct an explicit finite cover of size ≤ |Occ(k+1)|
  let Fcov : Finset (Set ℝ) := (occupiedFinset1 b (k + 1)).image (suffixInterval b (k + 1))
  have hFcov_diam : ∀ U ∈ Fcov, Metric.ediam U ≤ ENNReal.ofReal δ := by
    intro U hU
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hU
    exact (suffixInterval_ediam_le hb (k + 1) w).trans (ENNReal.ofReal_le_ofReal hlo_δ)
  have hFcov_sub : suffixClosure1 b ⊆ ⋃ U ∈ Fcov, U := by
    intro y hy
    obtain ⟨⟨w, hw⟩, hyw⟩ := Set.mem_iUnion.mp (suffixClosure1_subset_iUnion_occupied (k := k + 1) hb hy)
    exact Set.mem_iUnion₂.mpr ⟨suffixInterval b (k + 1) w, Finset.mem_image_of_mem _ hw, hyw⟩
  have hnonempty : {m : ℕ | ∃ F : Finset (Set ℝ), F.card = m ∧
      (∀ U ∈ F, Metric.ediam U ≤ ENNReal.ofReal δ) ∧ suffixClosure1 b ⊆ ⋃ U ∈ F, U}.Nonempty :=
    ⟨Fcov.card, Fcov, rfl, hFcov_diam, hFcov_sub⟩
  have hδ_neg_eq : δ ^ (-s) = (1 / δ) ^ s := by
    rw [one_div, Real.inv_rpow hδ0.le, Real.rpow_neg hδ0.le]
  constructor
  · -- Lower bound: any cover G of diameter ≤ δ satisfies |Occ(k)| ≤ 2 * G.card
    obtain ⟨G, hG_card, hG_diam, hG_cov⟩ := Nat.sInf_mem hnonempty
    -- For each w ∈ Occ(k), pick a witness revExp b (m w) in half-open interval [revNat b k w / b^k, ...)
    have hwit : ∀ w ∈ occupiedFinset1 b k, ∃ n : ℕ, 0 < n ∧ InBasin1 n ∧ n % b ^ k = w := by
      intro w hw
      unfold occupiedFinset1 at hw
      exact (Finset.mem_filter.mp hw).2
    let pt : ℕ → ℝ := fun w =>
      if h : w ∈ occupiedFinset1 b k then revExp b (hwit w h).choose else 0
    have hocc_sub : occupiedFinset1 b k ⊆
        G.biUnion (fun U => (occupiedFinset1 b k).filter (fun w => pt w ∈ U)) := by
      intro w hw
      have hspec := (hwit w hw).choose_spec
      have hpt_cl : pt w ∈ suffixClosure1 b := by
        dsimp only [pt]; simp only [hw, ↓reduceDIte]
        exact subset_closure ⟨_, ⟨hspec.1, hspec.2.1⟩, rfl⟩
      obtain ⟨U, hUG, hptU⟩ := Set.mem_iUnion₂.mp (hG_cov hpt_cl)
      exact Finset.mem_biUnion.mpr ⟨U, hUG, Finset.mem_filter.mpr ⟨hw, hptU⟩⟩
    have hcard_U : ∀ U ∈ G, ((occupiedFinset1 b k).filter (fun w => pt w ∈ U)).card ≤ 2 := by
      intro U hU
      set S := (occupiedFinset1 b k).filter (fun w => pt w ∈ U)
      have hS_sub : (S : Set ℕ) ⊆ (Finset.range (b ^ k) : Set ℕ) := fun w hw => by
        have hw' := (Finset.mem_filter.mp hw).1
        unfold occupiedFinset1 at hw'
        exact (Finset.mem_filter.mp hw').1
      have hcard_eq : S.card = (S.image (revNat b k)).card :=
        (Finset.card_image_of_injOn ((revNat_injOn (by omega) k).mono hS_sub)).symm
      rw [hcard_eq]
      by_cases hempty : (S.image (revNat b k)).Nonempty
      · set m0 := (S.image (revNat b k)).min' hempty
        have hsub : S.image (revNat b k) ⊆ {m0, m0 + 1} := by
          intro m hm
          have hm0_le : m0 ≤ m := Finset.min'_le _ m hm
          have hm0_mem := Finset.min'_mem _ hempty
          simp only [Finset.mem_image, S, Finset.mem_filter] at hm hm0_mem
          obtain ⟨w0, ⟨hw0_occ, hpt0_U⟩, hw0_rev⟩ := hm0_mem
          obtain ⟨w, ⟨hw_occ, hpt_U⟩, hw_rev⟩ := hm
          have hdist : dist (pt w) (pt w0) ≤ δ := by
            have hed : edist (pt w) (pt w0) ≤ ENNReal.ofReal δ :=
              (Metric.edist_le_ediam_of_mem hpt_U hpt0_U).trans (hG_diam U hU)
            rw [edist_dist] at hed
            exact (ENNReal.ofReal_le_ofReal_iff hδ0.le).mp hed
          have hspec0 := (hwit w0 hw0_occ).choose_spec
          have hspec := (hwit w hw_occ).choose_spec
          have hico0 := revExp_mem_Ico hb k (hwit w0 hw0_occ).choose
          have hico := revExp_mem_Ico hb k (hwit w hw_occ).choose
          have hpt0_eq : pt w0 = revExp b (hwit w0 hw0_occ).choose := by
            dsimp only [pt]; simp [hw0_occ]
          have hpt_eq : pt w = revExp b (hwit w hw_occ).choose := by
            dsimp only [pt]; simp [hw_occ]
          have hrev0 : revNat b k (hwit w0 hw0_occ).choose = m0 := by
            rw [← revNat_mod (by omega) k, hspec0.2.2, hw0_rev]
          have hrev : revNat b k (hwit w hw_occ).choose = m := by
            rw [← revNat_mod (by omega) k, hspec.2.2, hw_rev]
          rw [hrev0, ← hpt0_eq] at hico0
          rw [hrev, ← hpt_eq] at hico
          have hbk_pos : (0 : ℝ) < (b : ℝ) ^ k := by positivity
          have hy_diff : pt w - pt w0 ≤ δ := by
            rw [Real.dist_eq, abs_le] at hdist; exact hdist.2
          have hgap : (m : ℝ) - ((m0 : ℝ) + 1) < 1 := by
            have hdiv : ((m : ℝ) - ((m0 : ℝ) + 1)) / (b : ℝ) ^ k < 1 / (b : ℝ) ^ k := by
              rw [sub_div]
              linarith [hico0.2, hico.1, hy_diff, hhi_δ]
            exact (div_lt_div_iff_of_pos_right hbk_pos).mp hdiv
          have hm_le : m ≤ m0 + 1 := by
            have hcast : (m : ℝ) < (m0 + 2 : ℕ) := by push_cast; linarith
            have hnat : m < m0 + 2 := by exact_mod_cast hcast
            omega
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        exact (Finset.card_le_card hsub).trans Finset.card_le_two
      · simp [Finset.not_nonempty_iff_eq_empty.mp hempty]
    have hcard_le : (occupiedFinset1 b k).card ≤ 2 * boxCoverNumber (suffixClosure1 b) δ := by
      calc (occupiedFinset1 b k).card
          ≤ (G.biUnion (fun U => (occupiedFinset1 b k).filter (fun w => pt w ∈ U))).card :=
            Finset.card_le_card hocc_sub
        _ ≤ ∑ U ∈ G, ((occupiedFinset1 b k).filter (fun w => pt w ∈ U)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _U ∈ G, 2 := Finset.sum_le_sum hcard_U
        _ = 2 * G.card := by simp [mul_comm]
        _ = 2 * boxCoverNumber (suffixClosure1 b) δ := by rw [hG_card]; rfl
    have hcard_lo := (occupiedFinset1_card_bounds hb hk_ge1).1
    have hδ_le_th : δ ^ (-s) ≤ θ ^ (k + 1) := by
      rw [hδ_neg_eq]
      have h1 : 1 / δ ≤ (b : ℝ) ^ (k + 1) := by
        rw [div_le_iff₀ hδ0]
        have h1' := (div_le_iff₀ (by positivity : (0 : ℝ) < (b : ℝ) ^ (k + 1))).mp hlo_δ
        linarith
      calc (1 / δ) ^ s ≤ ((b : ℝ) ^ (k + 1)) ^ s :=
            Real.rpow_le_rpow (by positivity) h1 hs_pos.le
        _ = θ ^ (k + 1) := by
            rw [← Real.rpow_natCast (b : ℝ), ← Real.rpow_mul (by positivity),
                mul_comm ((k + 1 : ℕ) : ℝ) s, Real.rpow_mul (by positivity),
                base_rpow_suffixDimVal hb, Real.rpow_natCast]
    have hcardR : ((occupiedFinset1 b k).card : ℝ) ≤ 2 * (boxCoverNumber (suffixClosure1 b) δ : ℝ) := by
      exact_mod_cast hcard_le
    have hM0_nn : 0 ≤ totalMass b := (totalMass_pos hb).le
    have ha0 := aStar_spec.1
    have hstep : (totalMass b / (60 * aStar)) * (δ ^ (-s) / θ) ≤
        2 * (boxCoverNumber (suffixClosure1 b) δ : ℝ) := by
      have hdiv_le : δ ^ (-s) / θ ≤ θ ^ k := by
        rw [div_le_iff₀ hθ_pos, ← pow_succ]; exact hδ_le_th
      calc (totalMass b / (60 * aStar)) * (δ ^ (-s) / θ)
          ≤ (totalMass b / (60 * aStar)) * θ ^ k :=
            mul_le_mul_of_nonneg_left hdiv_le (by positivity)
        _ ≤ ((occupiedFinset1 b k).card : ℝ) := hcard_lo
        _ ≤ 2 * (boxCoverNumber (suffixClosure1 b) δ : ℝ) := hcardR
    have heq : (totalMass b / (120 * aStar * θ)) * δ ^ (-s) =
        ((totalMass b / (60 * aStar)) * (δ ^ (-s) / θ)) / 2 := by ring
    rw [heq]; linarith
  · -- Upper bound: boxCoverNumber ≤ Fcov.card ≤ |Occ(k+1)|
    have hle_nat : boxCoverNumber (suffixClosure1 b) δ ≤ (occupiedFinset1 b (k + 1)).card := by
      have h1 : boxCoverNumber (suffixClosure1 b) δ ≤ Fcov.card := by
        unfold boxCoverNumber
        exact Nat.sInf_le ⟨Fcov, rfl, hFcov_diam, hFcov_sub⟩
      exact h1.trans Finset.card_image_le
    have hcard_hi := (occupiedFinset1_card_bounds hb (by omega : 1 ≤ k + 1)).2
    have hth_le_δ : θ ^ k ≤ δ ^ (-s) := by
      rw [hδ_neg_eq]
      have h1 : (b : ℝ) ^ k ≤ 1 / δ := by
        rw [le_div_iff₀ hδ0]
        have h1' := (lt_div_iff₀ (by positivity : (0 : ℝ) < (b : ℝ) ^ k)).mp hhi_δ
        linarith
      calc θ ^ k = ((b : ℝ) ^ k) ^ s := by
            rw [← Real.rpow_natCast (b : ℝ), ← Real.rpow_mul (by positivity),
                mul_comm (k : ℝ) s, Real.rpow_mul (by positivity),
                base_rpow_suffixDimVal hb, Real.rpow_natCast]
        _ ≤ (1 / δ) ^ s := Real.rpow_le_rpow (by positivity) h1 hs_pos.le
    have hM0_nn : 0 ≤ totalMass b := (totalMass_pos hb).le
    have ha0 := aStar_spec.1
    calc (boxCoverNumber (suffixClosure1 b) δ : ℝ)
        ≤ ((occupiedFinset1 b (k + 1)).card : ℝ) := by exact_mod_cast hle_nat
      _ ≤ (totalMass b / (2 * aStar ^ 3)) * θ ^ (k + 1) := hcard_hi
      _ = (totalMass b * θ / (2 * aStar ^ 3)) * θ ^ k := by rw [pow_succ]; ring
      _ ≤ (totalMass b * θ / (2 * aStar ^ 3)) * δ ^ (-s) :=
          mul_le_mul_of_nonneg_left hth_le_δ (by positivity)

/-- Exact box-counting dimension limit for `ℰ_b`:
    `log(N_δ(ℰ_b)) / log(1/δ) → (log u + t * log λ) / log b` as `δ → 0⁺`. -/
theorem suffixClosure1_boxDim_tendsto {b : ℕ} (hb : 2 ≤ b) :
    Filter.Tendsto
      (fun δ : ℝ => Real.log (boxCoverNumber (suffixClosure1 b) δ : ℝ) / Real.log (1 / δ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (suffixDimVal b)) := by
  set s := suffixDimVal b
  set θ := suffixTheta b
  set c1 : ℝ := totalMass b / (120 * aStar * θ)
  set c2 : ℝ := totalMass b * θ / (2 * aStar ^ 3)
  have hc1_pos : 0 < c1 := div_pos (totalMass_pos hb) (by have := aStar_spec.1; have := suffixTheta_pos hb; positivity)
  have hc2_pos : 0 < c2 := div_pos (mul_pos (totalMass_pos hb) (suffixTheta_pos hb))
    (by have := aStar_spec.1; positivity)
  have hinv_top : Tendsto (fun δ : ℝ => 1 / δ) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero
  have hlog_top : Tendsto (fun δ : ℝ => Real.log (1 / δ)) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    Real.tendsto_log_atTop.comp hinv_top
  have hlo_tend : Tendsto (fun δ : ℝ => s + Real.log c1 / Real.log (1 / δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds s) := by
    simpa using (tendsto_const_nhds.div_atTop hlog_top).const_add s
  have hhi_tend : Tendsto (fun δ : ℝ => s + Real.log c2 / Real.log (1 / δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds s) := by
    simpa using (tendsto_const_nhds.div_atTop hlog_top).const_add s
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hmem : Set.Ioo (0 : ℝ) (1 / (b : ℝ)) ∈ nhdsWithin 0 (Set.Ioi 0) :=
    Ioo_mem_nhdsGT (div_pos one_pos hb_pos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo_tend hhi_tend ?_ ?_
  · filter_upwards [hmem] with δ ⟨hδ0, hδb⟩
    have hlog_pos : 0 < Real.log (1 / δ) := by
      apply Real.log_pos
      have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
      have h1 : (b : ℝ) < 1 / δ := by
        rw [lt_div_iff₀ hδ0]
        have := (lt_div_iff₀ (by positivity : (0 : ℝ) < (b : ℝ))).mp hδb
        linarith
      linarith
    have hbd := (boxCoverNumber_suffixClosure1_bounds hb hδ0 hδb).1
    have hpos1 : 0 < c1 * δ ^ (-s) := mul_pos hc1_pos (Real.rpow_pos_of_pos hδ0 _)
    have hlog_le := Real.log_le_log hpos1 hbd
    rw [Real.log_mul hc1_pos.ne' (Real.rpow_pos_of_pos hδ0 _).ne',
        Real.log_rpow hδ0] at hlog_le
    have hlog_inv : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
    have hdiv := div_le_div_of_nonneg_right hlog_le hlog_pos.le
    rw [add_div] at hdiv
    have hterm : (-s * Real.log δ) / Real.log (1 / δ) = s := by
      rw [hlog_inv]; field_simp [hlog_pos.ne', (show Real.log δ ≠ 0 by linarith)]
    linarith
  · filter_upwards [hmem] with δ ⟨hδ0, hδb⟩
    have hlog_pos : 0 < Real.log (1 / δ) := by
      apply Real.log_pos
      have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
      have h1 : (b : ℝ) < 1 / δ := by
        rw [lt_div_iff₀ hδ0]
        have := (lt_div_iff₀ (by positivity : (0 : ℝ) < (b : ℝ))).mp hδb
        linarith
      linarith
    obtain ⟨hbd1, hbd2⟩ := boxCoverNumber_suffixClosure1_bounds hb hδ0 hδb
    have hposN : 0 < (boxCoverNumber (suffixClosure1 b) δ : ℝ) :=
      lt_of_lt_of_le (mul_pos hc1_pos (Real.rpow_pos_of_pos hδ0 _)) hbd1
    have hlog_le := Real.log_le_log hposN hbd2
    rw [Real.log_mul hc2_pos.ne' (Real.rpow_pos_of_pos hδ0 _).ne',
        Real.log_rpow hδ0] at hlog_le
    have hlog_inv : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
    have hdiv := div_le_div_of_nonneg_right hlog_le hlog_pos.le
    rw [add_div] at hdiv
    have hterm : (-s * Real.log δ) / Real.log (1 / δ) = s := by
      rw [hlog_inv]; field_simp [hlog_pos.ne', (show Real.log δ ≠ 0 by linarith)]
    linarith

theorem suffixClosure1_lowerBoxDim {b : ℕ} (hb : 2 ≤ b) :
    lowerBoxDim (suffixClosure1 b) = suffixDimVal b :=
  (suffixClosure1_boxDim_tendsto hb).liminf_eq

theorem suffixClosure1_upperBoxDim {b : ℕ} (hb : 2 ≤ b) :
    upperBoxDim (suffixClosure1 b) = suffixDimVal b :=
  (suffixClosure1_boxDim_tendsto hb).limsup_eq

/-! ## Section 7: 8-decimal-place values and Corollary `cor:suffix-dimension` -/

lemma aStar_tight_bounds :
    (647798871 / 1000000000 : ℝ) < aStar ∧ aStar < (647798872 / 1000000000 : ℝ) := by
  have ha0 := aStar_spec.1
  have hq := aStar_quartic
  constructor
  · by_contra hle; push Not at hle
    have h4 : aStar ^ 4 ≤ (647798871 / 1000000000 : ℝ) ^ 4 := by gcongr
    linarith [show (647798871 / 1000000000 : ℝ) + 2 * (647798871 / 1000000000 : ℝ) ^ 4 < 1 by norm_num]
  · by_contra hge; push Not at hge
    have h4 : (647798872 / 1000000000 : ℝ) ^ 4 ≤ aStar ^ 4 := by gcongr
    linarith [show (1 : ℝ) < (647798872 / 1000000000 : ℝ) + 2 * (647798872 / 1000000000 : ℝ) ^ 4 by norm_num]

/-- Tight 9-digit rational bracket for `λ ≈ 1.5436890127`. -/
theorem suffixLambda_bounds :
    (1543689010 / 1000000000 : ℝ) < suffixLambda ∧ suffixLambda < (1543689014 / 1000000000 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := aStar_tight_bounds
  have ha0 := aStar_spec.1
  unfold suffixLambda
  constructor
  · rw [lt_div_iff₀ ha0]
    have : (1543689010 / 1000000000 : ℝ) * aStar <
        (1543689010 / 1000000000 : ℝ) * (647798872 / 1000000000 : ℝ) := by gcongr
    linarith [show (1543689010 / 1000000000 : ℝ) * (647798872 / 1000000000 : ℝ) < 1 by norm_num]
  · rw [div_lt_iff₀ ha0]
    have : (1543689014 / 1000000000 : ℝ) * (647798871 / 1000000000 : ℝ) <
        (1543689014 / 1000000000 : ℝ) * aStar := by gcongr
    linarith [show (1 : ℝ) < (1543689014 / 1000000000 : ℝ) * (647798871 / 1000000000 : ℝ) by norm_num]

private lemma log_suffixLambda_bounds :
    (4341750120 / 10000000000 : ℝ) < Real.log suffixLambda ∧
    Real.log suffixLambda < (43417501743 / 100000000000 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := suffixLambda_bounds
  have hlog2_lo : (6931471803 / 10000000000 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2_hi : Real.log 2 < (6931471808 / 10000000000 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hlam8_lo : (32 : ℝ) / (9923651 / 10000000 : ℝ) < suffixLambda ^ 8 := by
    have h8 : (1543689010 / 1000000000 : ℝ) ^ 8 < suffixLambda ^ 8 := by gcongr
    linarith [show (32 : ℝ) / (9923651 / 10000000 : ℝ) < (1543689010 / 1000000000 : ℝ) ^ 8 by norm_num]
  have hlam8_hi : suffixLambda ^ 8 < (32 : ℝ) / (49618253 / 50000000 : ℝ) := by
    have h8 : suffixLambda ^ 8 < (1543689014 / 1000000000 : ℝ) ^ 8 := by gcongr
    linarith [show (1543689014 / 1000000000 : ℝ) ^ 8 < (32 : ℝ) / (49618253 / 50000000 : ℝ) by norm_num]
  have hlog_r2 : (7664195 / 1000000000 : ℝ) < -(Real.log (9923651 / 10000000 : ℝ)) := by
    have hx : |(76349 / 10000000 : ℝ)| < 1 := by norm_num
    have hz := Real.abs_log_sub_add_sum_range_le hx 4
    have hsub : (1 : ℝ) - 76349 / 10000000 = 9923651 / 10000000 := by norm_num
    rw [hsub, abs_le] at hz
    norm_num [Finset.sum_range_succ] at hz
    linarith
  have hlog_r1 : -(Real.log (49618253 / 50000000 : ℝ)) < (76642354 / 10000000000 : ℝ) := by
    have hx : |(381747 / 50000000 : ℝ)| < 1 := by norm_num
    have hz := Real.abs_log_sub_add_sum_range_le hx 4
    have hsub : (1 : ℝ) - 381747 / 50000000 = 49618253 / 50000000 := by norm_num
    rw [hsub, abs_le] at hz
    norm_num [Finset.sum_range_succ] at hz
    linarith
  have hlog32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hlog8 : Real.log (suffixLambda ^ 8) = 8 * Real.log suffixLambda := by
    rw [Real.log_pow]; norm_num
  constructor
  · have h1 := Real.log_lt_log (by norm_num) hlam8_lo
    rw [Real.log_div (by norm_num) (by norm_num), hlog32, hlog8] at h1
    linarith
  · have h1 := Real.log_lt_log (pow_pos suffixLambda_pos 8) hlam8_hi
    rw [Real.log_div (by norm_num) (by norm_num), hlog32, hlog8] at h1
    linarith

private lemma log_five_bounds :
    (16094379118 / 10000000000 : ℝ) < Real.log 5 ∧
    Real.log 5 < (16094379130 / 10000000000 : ℝ) := by
  have hlog2_lo : (6931471803 / 10000000000 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2_hi : Real.log 2 < (6931471808 / 10000000000 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hx : |(3 / 128 : ℝ)| < 1 := by norm_num
  have hz := Real.abs_log_sub_add_sum_range_le hx 6
  have hsub : (1 : ℝ) - 3 / 128 = 125 / 128 := by norm_num
  rw [hsub, abs_le] at hz
  norm_num [Finset.sum_range_succ] at hz
  have hrel : 3 * Real.log 5 = 7 * Real.log 2 + Real.log (125 / 128 : ℝ) := by
    rw [Real.log_div (by norm_num) (by norm_num),
        show (125 : ℝ) = (5 : ℝ) ^ (3 : ℕ) by norm_num,
        show (128 : ℝ) = (2 : ℝ) ^ (7 : ℕ) by norm_num,
        Real.log_pow, Real.log_pow]
    norm_num
  constructor <;> linarith

/-- Exact identity `dim ℰ_2 = β` (recovering `beta` from `BasinOne.lean`). -/
theorem suffixDimVal_base2_eq_beta : suffixDimVal 2 = beta := by
  have hfac : suffixDimVal 2 = Real.log suffixLambda / Real.log 2 := by
    have := suffixDimVal_eq_of_fac (by norm_num) (by decide) (by norm_num : (2 : ℕ) = 2 ^ 1 * 1)
    simpa [Real.log_one] using this
  rw [hfac]
  rfl

/-- Base `2` dimension to 8 decimal places: `0.62638214` (and strictly exceeding `0.6245`). -/
theorem suffixDimVal_base2_bounds :
    (626382135 / 1000000000 : ℝ) < suffixDimVal 2 ∧
    suffixDimVal 2 < (626382145 / 1000000000 : ℝ) ∧
    (6245 / 10000 : ℝ) < suffixDimVal 2 := by
  have hfac : suffixDimVal 2 = Real.log suffixLambda / Real.log 2 := by
    have := suffixDimVal_eq_of_fac (by norm_num) (by decide) (by norm_num : (2 : ℕ) = 2 ^ 1 * 1)
    simpa [Real.log_one] using this
  rw [hfac]
  obtain ⟨hl_lo, hl_hi⟩ := log_suffixLambda_bounds
  have hlog2_lo : (6931471803 / 10000000000 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2_hi : Real.log 2 < (6931471808 / 10000000000 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hlog2_pos : 0 < Real.log 2 := by linarith
  have hlo : (626382135 / 1000000000 : ℝ) < Real.log suffixLambda / Real.log 2 := by
    rw [lt_div_iff₀ hlog2_pos]; nlinarith
  have hhi : Real.log suffixLambda / Real.log 2 < (626382145 / 1000000000 : ℝ) := by
    rw [div_lt_iff₀ hlog2_pos]; nlinarith
  exact ⟨hlo, hhi, by linarith⟩

/-- Base `10` dimension to 8 decimal places: `0.88752982`. -/
theorem suffixDimVal_base10_bounds :
    (887529815 / 1000000000 : ℝ) < suffixDimVal 10 ∧
    suffixDimVal 10 < (887529825 / 1000000000 : ℝ) := by
  have hfac : suffixDimVal 10 = (Real.log 5 + Real.log suffixLambda) / Real.log 10 := by
    have := suffixDimVal_eq_of_fac (by norm_num) (by decide) (by norm_num : (10 : ℕ) = 2 ^ 1 * 5)
    simpa using this
  rw [hfac]
  have hlog10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [hlog10]
  obtain ⟨hl_lo, hl_hi⟩ := log_suffixLambda_bounds
  obtain ⟨h5_lo, h5_hi⟩ := log_five_bounds
  have hlog2_lo : (6931471803 / 10000000000 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2_hi : Real.log 2 < (6931471808 / 10000000000 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hden_pos : 0 < Real.log 2 + Real.log 5 := by linarith
  constructor
  · rw [lt_div_iff₀ hden_pos]; nlinarith
  · rw [div_lt_iff₀ hden_pos]; nlinarith

/-- Base `7` dimension equals `1` exactly. -/
theorem suffixDimVal_base7 : suffixDimVal 7 = 1 := by
  have hfac := suffixDimVal_eq_of_fac (by norm_num) (by decide) (by norm_num : (7 : ℕ) = 2 ^ 0 * 7)
  rw [hfac]
  have hlog7 : Real.log (7 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simp [hlog7]

/-- **Corollary `cor:suffix-dimension` (Corollary 30)**:
    Exact Hausdorff and box-counting dimension of the reversed base-`b` suffix closure `ℰ_b ⊂ [0, 1]`
    of `ℬ_1`, together with the 8-decimal-place values in bases `2`, `10`, and `7`, the full-interval
    identity `ℰ_7 = [0, 1]`, and the full-interval identity `ℰ_{5,b} = [0, 1]` for `ℬ_5` in every
    base `b ≥ 2`. -/
theorem cor_suffix_dimension :
    (0 < suffixLambda ∧ suffixLambda ^ 4 = suffixLambda ^ 3 + 2 ∧
      (154368901 / 10 ^ 8 : ℝ) < suffixLambda ∧ suffixLambda < (1543689014 / 10 ^ 9 : ℝ) ∧
      (∃! lam : ℝ, 0 < lam ∧ lam ^ 4 = lam ^ 3 + 2)) ∧
    (∀ (b t u : ℕ), 2 ≤ b → u % 2 = 1 → b = 2 ^ t * u →
      let s := (Real.log (u : ℝ) + (t : ℝ) * Real.log suffixLambda) / Real.log (b : ℝ)
      suffixClosure1 b ⊆ Set.Icc (0 : ℝ) 1 ∧
      dimH (suffixClosure1 b) = ENNReal.ofReal s ∧
      lowerBoxDim (suffixClosure1 b) = s ∧
      upperBoxDim (suffixClosure1 b) = s ∧
      Filter.Tendsto
        (fun δ : ℝ => Real.log (boxCoverNumber (suffixClosure1 b) δ : ℝ) / Real.log (1 / δ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds s) ∧
      suffixClosure5 b = Set.Icc (0 : ℝ) 1) ∧
    (dimH (suffixClosure1 2) = ENNReal.ofReal beta ∧
      suffixDimVal 2 = beta ∧
      (626382135 / 1000000000 : ℝ) < suffixDimVal 2 ∧
      suffixDimVal 2 < (626382145 / 1000000000 : ℝ) ∧
      (6245 / 10000 : ℝ) < suffixDimVal 2) ∧
    (dimH (suffixClosure1 10) = ENNReal.ofReal (suffixDimVal 10) ∧
      (887529815 / 1000000000 : ℝ) < suffixDimVal 10 ∧
      suffixDimVal 10 < (887529825 / 1000000000 : ℝ)) ∧
    (dimH (suffixClosure1 7) = ENNReal.ofReal 1 ∧
      suffixDimVal 7 = 1 ∧ suffixClosure1 7 = Set.Icc (0 : ℝ) 1) := by
  refine ⟨⟨suffixLambda_spec.1, suffixLambda_spec.2,
      by linarith [suffixLambda_bounds.1], by linarith [suffixLambda_bounds.2],
      exists_unique_suffixLambda⟩,
    ?_, ?_,
    ⟨suffixClosure1_dimH (by norm_num), suffixDimVal_base10_bounds.1, suffixDimVal_base10_bounds.2⟩,
    ⟨by rw [suffixClosure1_dimH (by norm_num), suffixDimVal_base7],
      suffixDimVal_base7, suffixClosure1_base7_eq_Icc⟩⟩
  · intro b t u hb hu hfac
    dsimp only
    rw [← suffixDimVal_eq_of_fac hb hu hfac]
    exact ⟨suffixClosure1_subset_Icc hb, suffixClosure1_dimH hb,
      suffixClosure1_lowerBoxDim hb, suffixClosure1_upperBoxDim hb,
      suffixClosure1_boxDim_tendsto hb, suffixClosure5_eq_Icc hb⟩
  · exact ⟨by rw [suffixClosure1_dimH (by norm_num), suffixDimVal_base2_eq_beta],
      suffixDimVal_base2_eq_beta, suffixDimVal_base2_bounds.1,
      suffixDimVal_base2_bounds.2.1, suffixDimVal_base2_bounds.2.2⟩

end Ouroboros
