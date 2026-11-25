module
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic
public import Ouroboros.Defs
public import Ouroboros.BasinOne

@[expose] public section

/-!
# Section 3 (Theorem 18 / `thm:cantor`): Exact 2-adic Cantor closure and elementary quartic bounds

Formalizes every part of Theorem `thm:cantor` from `hughes-ouroboros-draft9.tex`:

1. **Exact `2`-adic closure**: for `r ∈ {1, 15, 17}`, `closure K_r = 𝒦_r` in `ℤ_[2]`, hence
   `closure B_1 = (30 𝒦_1 + 1) ∪ (30 𝒦_15 + 15) ∪ (30 𝒦_17 + 17)`. Every nonempty `2`-adic ball
   meeting `closure B_1` contains infinitely many positive integers reaching `1` and infinitely many
   exiting `{1, 15, 17} mod 30` at `19` or `23 mod 30`, and `closure B_1` is nowhere dense in `ℤ_[2]`.
2. **Self-similar isometry and Hausdorff/box dimension**: equipping `{0, 1}^ℕ` (`BitSeq`) with
   `d(x, y) = 2^{-inf{j : x_j ≠ y_j}}`, the halving-itinerary map `Ψ_r : 𝒦_r → BitSeq` is a
   surjective `2`-adic isometry onto `Σ = {0, 1000, 1001}^ω` for `r ∈ {1, 17}` and onto
   `000 Σ ⊔ 001 Σ` for `r = 15`. Consequently `1/2 ≤ μH[β](closure B_1) ≤ a^{-2} + a < 3.031`
   and `dimH(closure B_1) = dimB(closure B_1) = β = -log_2 a` (`0.626382135 < β < 0.626382145`).
3. **Elementary integer bounds**: for every real `X ≥ 1`,
   `a_1^9 * X^γ ≤ N_1(⌊X⌋) ≤ X^β` (`0.464958 < γ < 0.464959`), with natural density zero for the
   full basin of `1`.
-/

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace Ouroboros

noncomputable instance : MeasurableSpace ℤ_[2] := borel ℤ_[2]
instance : BorelSpace ℤ_[2] := ⟨rfl⟩

/-! ## Part 0: Exact quartic roots and high-precision numerical brackets -/

/-- `a* ∈ (0, 1)` is the unique positive root of `a + 2 * a^4 = 1`. -/
theorem exists_unique_aStar_quartic :
    ∃! a : ℝ, 0 < a ∧ a < 1 ∧ a + 2 * a ^ 4 = 1 := by
  refine ⟨aStar, ⟨aStar_spec.1, aStar_spec.2.1, aStar_quartic⟩, ?_⟩
  intro b ⟨hb0, _, hbeq⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h4 : b ^ 4 < aStar ^ 4 := by gcongr
    linarith [aStar_quartic]
  · have h0 := aStar_spec.1
    have h4 : aStar ^ 4 < b ^ 4 := by gcongr
    linarith [aStar_quartic]

/-- Tight 9-digit bracket on `a*`. -/
lemma aStar_bounds_tight :
    (647798871 / 1000000000 : ℝ) < aStar ∧ aStar < (647798872 / 1000000000 : ℝ) := by
  have h0 := aStar_spec.1
  have hq := aStar_quartic
  constructor
  · by_contra hle; push Not at hle
    have h4 : aStar ^ 4 ≤ (647798871 / 1000000000 : ℝ) ^ 4 := by gcongr
    have : (647798871 / 1000000000 : ℝ) + 2 * (647798871 / 1000000000 : ℝ) ^ 4 < 1 := by norm_num
    linarith
  · by_contra hge; push Not at hge
    have h4 : (647798872 / 1000000000 : ℝ) ^ 4 ≤ aStar ^ 4 := by gcongr
    have : (1 : ℝ) < (647798872 / 1000000000 : ℝ) + 2 * (647798872 / 1000000000 : ℝ) ^ 4 := by
      norm_num
    linarith

/-- Tight 9-digit bracket on `a_1`. -/
lemma a1_bounds_tight :
    (724491959 / 1000000000 : ℝ) < a1 ∧ a1 < (724491960 / 1000000000 : ℝ) := by
  have h0 := a1_spec.1
  have hq := a1_spec.2.2
  constructor
  · by_contra hle; push Not at hle
    have h4 : a1 ^ 4 ≤ (724491959 / 1000000000 : ℝ) ^ 4 := by gcongr
    have : (724491959 / 1000000000 : ℝ) + (724491959 / 1000000000 : ℝ) ^ 4 < 1 := by norm_num
    linarith
  · by_contra hge; push Not at hge
    have h4 : (724491960 / 1000000000 : ℝ) ^ 4 ≤ a1 ^ 4 := by gcongr
    have : (1 : ℝ) < (724491960 / 1000000000 : ℝ) + (724491960 / 1000000000 : ℝ) ^ 4 := by
      norm_num
    linarith

private lemma exp_le_cubic {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + (2 / 9 : ℝ) * x ^ 3 := by
  have h := Real.exp_bound' h0 h1 (n := 3) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at h
  linarith

private lemma cubic_le_exp {x : ℝ} (h0 : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg h0 4
  simp [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- Tight bracket on `Real.log (1 / a*)` using `125 / 81 = 5^3 / 3^4 ≈ 1 / a*`. -/
lemma log_inv_aStar_bounds :
    (4341750117 / 10000000000 : ℝ) < Real.log (1 / aStar) ∧
    Real.log (1 / aStar) < (4341750168 / 10000000000 : ℝ) := by
  obtain ⟨haL, haU⟩ := aStar_bounds_tight
  have ha0 := aStar_spec.1
  have hr_eq : (1 / aStar : ℝ) = (5 : ℝ) ^ (3 : ℕ) / (3 : ℝ) ^ (4 : ℕ) * (81 / (125 * aStar)) := by
    field_simp; ring
  have hr_pos : 0 < (81 / (125 * aStar) : ℝ) := by positivity
  have hlog_split : Real.log (1 / aStar) =
      3 * Real.log 5 - 4 * Real.log 3 + Real.log (81 / (125 * aStar)) := by
    rw [hr_eq, Real.log_mul (by positivity) hr_pos.ne', Real.log_div (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
    push_cast; ring
  have hratio_lo : (81 / (125 * (647798872 / 1000000000 : ℝ)) : ℝ) < 81 / (125 * aStar) := by
    gcongr
  have hratio_hi : 81 / (125 * aStar) < (81 / (125 * (647798871 / 1000000000 : ℝ)) : ℝ) := by
    gcongr
  have hlog_r_lo : (310430 / 1000000000 : ℝ) < Real.log (81 / (125 * aStar)) := by
    rw [Real.lt_log_iff_exp_lt hr_pos]
    have h1 := exp_le_cubic (x := (310430 / 1000000000 : ℝ)) (by norm_num) (by norm_num)
    have h2 : (1 + (310430 / 1000000000 : ℝ) + (310430 / 1000000000 : ℝ) ^ 2 / 2 +
        (2 / 9 : ℝ) * (310430 / 1000000000 : ℝ) ^ 3) <
        81 / (125 * (647798872 / 1000000000 : ℝ)) := by norm_num
    linarith
  have hlog_r_hi : Real.log (81 / (125 * aStar)) < (310433 / 1000000000 : ℝ) := by
    rw [Real.log_lt_iff_lt_exp hr_pos]
    have h1 := cubic_le_exp (x := (310433 / 1000000000 : ℝ)) (by norm_num)
    have h2 : (81 / (125 * (647798871 / 1000000000 : ℝ)) : ℝ) <
        1 + (310433 / 1000000000 : ℝ) + (310433 / 1000000000 : ℝ) ^ 2 / 2 +
        (310433 / 1000000000 : ℝ) ^ 3 / 6 := by norm_num
    linarith
  have h3lo := Real.log_three_gt_d9
  have h3hi := Real.log_three_lt_d9
  have h5lo := Real.log_five_gt_d9
  have h5hi := Real.log_five_lt_d9
  rw [hlog_split]
  constructor <;> linarith

lemma gamma_eq_neg_logb : gamma = -Real.logb 2 a1 := by
  unfold gamma Real.logb
  rw [one_div, Real.log_inv, neg_div]

lemma beta_eq_neg_logb : beta = -Real.logb 2 aStar := by
  unfold beta Real.logb
  rw [one_div, Real.log_inv, neg_div]

/-- Exact 8-decimal-place bracket `0.626382135 < β < 0.626382145` (so `β ≈ 0.62638214`). -/
theorem beta_bounds_8 :
    (626382135 / 1000000000 : ℝ) < beta ∧ beta < (626382145 / 1000000000 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := log_inv_aStar_bounds
  have h2lo : (6931471803 / 10000000000 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2hi : Real.log 2 < (6931471808 / 10000000000 : ℝ) := by linarith [Real.log_two_lt_d9]
  have h2pos : 0 < Real.log 2 := by linarith
  unfold beta Real.logb
  constructor
  · rw [lt_div_iff₀ h2pos]; nlinarith
  · rw [div_lt_iff₀ h2pos]; nlinarith

/-- Explicit 6-decimal-place bracket `0.626382 < β < 0.626383` from Theorem `thm:cantor`. -/
theorem beta_bounds_6 :
    (626382 / 1000000 : ℝ) < beta ∧ beta < (626383 / 1000000 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := beta_bounds_8
  exact ⟨by linarith, by linarith⟩

/-- Explicit 6-decimal-place bracket `0.464958 < γ < 0.464959` from Theorem `thm:cantor`. -/
theorem gamma_bounds_6 :
    (464958 / 1000000 : ℝ) < gamma ∧ gamma < (464959 / 1000000 : ℝ) := by
  obtain ⟨haL, haU⟩ := a1_bounds_tight
  have ha0 := a1_spec.1
  have hs_pos : 0 < (25 * a1 / 18 : ℝ) := by positivity
  have hs_eq : (1 / a1 : ℝ) = ((5 : ℝ) ^ (2 : ℕ) / (2 * (3 : ℝ) ^ (2 : ℕ))) / (25 * a1 / 18) := by
    field_simp; ring
  have hlog_split : Real.log (1 / a1) =
      2 * Real.log 5 - Real.log 2 - 2 * Real.log 3 - Real.log (25 * a1 / 18) := by
    rw [hs_eq, Real.log_div (by positivity) hs_pos.ne',
        Real.log_div (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have hs_lo : (25 * (724491959 / 1000000000 : ℝ) / 18 : ℝ) < 25 * a1 / 18 := by linarith
  have hs_hi : 25 * a1 / 18 < (25 * (724491960 / 1000000000 : ℝ) / 18 : ℝ) := by linarith
  have hy_lo : (62194 / 10000000 : ℝ) < Real.log (25 * a1 / 18) := by
    rw [Real.lt_log_iff_exp_lt hs_pos]
    have h1 := exp_le_cubic (x := (62194 / 10000000 : ℝ)) (by norm_num) (by norm_num)
    have h2 : (1 + (62194 / 10000000 : ℝ) + (62194 / 10000000 : ℝ) ^ 2 / 2 +
        (2 / 9 : ℝ) * (62194 / 10000000 : ℝ) ^ 3) <
        25 * (724491959 / 1000000000 : ℝ) / 18 := by norm_num
    linarith
  have hy_hi : Real.log (25 * a1 / 18) < (62195 / 10000000 : ℝ) := by
    rw [Real.log_lt_iff_lt_exp hs_pos]
    have h1 := cubic_le_exp (x := (62195 / 10000000 : ℝ)) (by norm_num)
    have h2 : (25 * (724491960 / 1000000000 : ℝ) / 18 : ℝ) <
        1 + (62195 / 10000000 : ℝ) + (62195 / 10000000 : ℝ) ^ 2 / 2 +
        (62195 / 10000000 : ℝ) ^ 3 / 6 := by norm_num
    linarith
  have h2lo : (6931471803 / 10000000000 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2hi : Real.log 2 < (6931471808 / 10000000000 : ℝ) := by linarith [Real.log_two_lt_d9]
  have h3lo := Real.log_three_gt_d9
  have h3hi := Real.log_three_lt_d9
  have h5lo := Real.log_five_gt_d9
  have h5hi := Real.log_five_lt_d9
  have h2pos : 0 < Real.log 2 := by linarith
  unfold gamma Real.logb
  rw [hlog_split]
  constructor
  · rw [lt_div_iff₀ h2pos]; nlinarith
  · rw [div_lt_iff₀ h2pos]; nlinarith

/-- Hausdorff upper constant `a^{-2} + a < 3.031`. -/
lemma aStar_hausdorff_ub_lt : aStar⁻¹ ^ 2 + aStar < (3031 / 1000 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := aStar_bounds_tight
  have ha0 := aStar_spec.1
  have hinv : aStar⁻¹ < (1000000000 / 647798871 : ℝ) := by
    rw [inv_lt_comm₀ ha0 (by norm_num)]; simpa using hlo
  have hsq : aStar⁻¹ ^ 2 < (1000000000 / 647798871 : ℝ) ^ 2 := by gcongr
  linarith [show (1000000000 / 647798871 : ℝ) ^ 2 + (647798872 / 1000000000 : ℝ) <
      3031 / 1000 by norm_num]

/-- Elementary upper prefactor `(1 + a) / ((1 - a) * 15^β) < 1`. -/
lemma aStar_N1_prefactor_lt_one :
    (1 + aStar) / ((1 - aStar) * (15 : ℝ) ^ beta) < 1 := by
  obtain ⟨_, hhi⟩ := aStar_bounds_tight
  have hd1 := aStar_denom_pos.1
  have hfrac : (1 + aStar) / (1 - aStar) < (468 / 100 : ℝ) := by
    rw [div_lt_iff₀ hd1]; linarith
  have hbeta58 : (5 / 8 : ℝ) < beta := by linarith [beta_bounds_6.1]
  have h15_58 : (468 / 100 : ℝ) < (15 : ℝ) ^ ((5 : ℝ) / 8) := by
    have h8 : (468 / 100 : ℝ) ^ (8 : ℕ) < ((15 : ℝ) ^ ((5 : ℝ) / 8)) ^ (8 : ℕ) := by
      rw [← Real.rpow_natCast ((15 : ℝ) ^ ((5 : ℝ) / 8)) 8, ← Real.rpow_mul (by norm_num)]
      have : ((5 : ℝ) / 8) * (8 : ℕ) = (5 : ℕ) := by norm_num
      rw [this, Real.rpow_natCast]; norm_num
    exact lt_of_pow_lt_pow_left₀ 8 (by positivity) h8
  have h15_beta : (15 : ℝ) ^ ((5 : ℝ) / 8) ≤ (15 : ℝ) ^ beta :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hbeta58.le
  rw [div_lt_one (mul_pos hd1 (by positivity))]
  have h1 : (1 + aStar) < (468 / 100 : ℝ) * (1 - aStar) := (div_lt_iff₀ hd1).mp hfrac
  nlinarith

/-! ## Part 1: Shortcut affine coding, modulo-30 survival, and the `+30` inverse commutator -/

/-- Odd step multiplier for `T`: `1` on even integers, `d(n) = n % 10` on odd integers. -/
def oddMult (n : ℕ) : ℕ := if n % 2 = 0 then 1 else d n

/-- Cumulative odd multiplier along the first `j` shortcut steps from `n`. -/
def prodOddMult (j n : ℕ) : ℕ := ∏ i ∈ Finset.range j, oddMult (T^[i] n)

lemma oddMult_odd (n : ℕ) : oddMult n % 2 = 1 := by
  unfold oddMult d
  split_ifs with h <;> omega

lemma prodOddMult_odd (j n : ℕ) : prodOddMult j n % 2 = 1 := by
  induction j with
  | zero => simp [prodOddMult]
  | succ j ih =>
    unfold prodOddMult at ih ⊢
    rw [Finset.prod_range_succ, Nat.mul_mod, ih, oddMult_odd]

private lemma T_step_affine (m D k' b : ℕ) (hm : 1 ≤ m) :
    T (30 * 2 ^ m * D * k' + b) = 30 * 2 ^ (m - 1) * (oddMult b * D) * k' + T b := by
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    have : m = (m - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ']
  have h60 : 30 * 2 ^ m * D * k' = 60 * (2 ^ (m - 1) * D * k') := by rw [hpow]; ring
  unfold T oddMult d
  by_cases hb : b % 2 = 0
  · have hsum_ev : (30 * 2 ^ m * D * k' + b) % 2 = 0 := by rw [h60]; omega
    simp only [hsum_ev, hb, ↓reduceIte, one_mul]
    have h2 : 30 * 2 ^ m * D * k' = 2 * (30 * 2 ^ (m - 1) * D * k') := by rw [hpow]; ring
    rw [h2, Nat.mul_add_div (by norm_num)]
  · have hsum_odd : (30 * 2 ^ m * D * k' + b) % 2 ≠ 0 := by rw [h60]; omega
    have hmod10 : (30 * 2 ^ m * D * k' + b) % 10 = b % 10 := by rw [h60]; omega
    have hdb_odd : (b % 10) % 2 = 1 := by omega
    have hbb_ev : ((b % 10) * b + 1) % 2 = 0 := by
      have : ((b % 10) * b) % 2 = 1 := by rw [Nat.mul_mod, hdb_odd]; omega
      omega
    simp only [hsum_odd, hb, ↓reduceIte, hmod10]
    have hmul : (b % 10) * (30 * 2 ^ m * D * k' + b) + 1 =
        2 * (30 * 2 ^ (m - 1) * (b % 10 * D) * k') + ((b % 10) * b + 1) := by
      rw [hpow]; ring
    rw [hmul]
    omega

/-- Exact affine formula for `j ≤ h` steps of `T` on a `2^h`-adic cylinder mod `30 * 2^h`. -/
theorem T_iter_affine (h j k₀ k' r : ℕ) (hj : j ≤ h) :
    T^[j] (30 * (2 ^ h * k' + k₀) + r) =
      30 * 2 ^ (h - j) * prodOddMult j (30 * k₀ + r) * k' + T^[j] (30 * k₀ + r) := by
  induction j with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.sub_zero, prodOddMult, Finset.range_zero,
      Finset.prod_empty, mul_one]
    ring
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [ih (by omega)]
    have hstep := T_step_affine (h - j) (prodOddMult j (30 * k₀ + r)) k' (T^[j] (30 * k₀ + r))
      (by omega)
    rw [hstep]
    have hsub : h - j - 1 = h - (j + 1) := by omega
    have hprod : prodOddMult (j + 1) (30 * k₀ + r) =
        oddMult (T^[j] (30 * k₀ + r)) * prodOddMult j (30 * k₀ + r) := by
      unfold prodOddMult
      rw [Finset.prod_range_succ, mul_comm]
    rw [hsub, hprod]

/-- General affine form `T^[j] (30 * 2^h * D * k' + b) = 30 * 2^(h-j) * (prodOddMult j b * D) * k' + T^[j] b`. -/
lemma T_iter_affine_gen (h j D k' b : ℕ) (hj : j ≤ h) :
    T^[j] (30 * 2 ^ h * D * k' + b) =
      30 * 2 ^ (h - j) * (prodOddMult j b * D) * k' + T^[j] b := by
  have hb : b = 30 * (b / 30) + b % 30 := (Nat.div_add_mod b 30).symm
  have h1 : 30 * 2 ^ h * D * k' + b = 30 * (2 ^ h * (D * k') + b / 30) + b % 30 := by
    conv_lhs => rw [hb]
    ring
  rw [h1, T_iter_affine h j (b / 30) (D * k') (b % 30) hj, ← hb]
  ring

/-- `T^[j] (30 * k + r) % 30` depends only on `k % 2^h` for all `j ≤ h`. -/
lemma T_iter_mod30_eq {h j k₁ k₂ r : ℕ} (hj : j ≤ h) (hmod : k₁ % 2 ^ h = k₂ % 2 ^ h) :
    T^[j] (30 * k₁ + r) % 30 = T^[j] (30 * k₂ + r) % 30 := by
  set k₀ := k₁ % 2 ^ h
  have hk1 : k₁ = 2 ^ h * (k₁ / 2 ^ h) + k₀ := by
    have := Nat.div_add_mod k₁ (2 ^ h); omega
  have hk2 : k₂ = 2 ^ h * (k₂ / 2 ^ h) + k₀ := by
    have := Nat.div_add_mod k₂ (2 ^ h); omega
  rw [hk1, hk2, T_iter_affine h j k₀ _ r hj, T_iter_affine h j k₀ _ r hj]
  have h1 : 30 * 2 ^ (h - j) * prodOddMult j (30 * k₀ + r) * (k₁ / 2 ^ h) =
      30 * (2 ^ (h - j) * prodOddMult j (30 * k₀ + r) * (k₁ / 2 ^ h)) := by ring
  have h2 : 30 * 2 ^ (h - j) * prodOddMult j (30 * k₀ + r) * (k₂ / 2 ^ h) =
      30 * (2 ^ (h - j) * prodOddMult j (30 * k₀ + r) * (k₂ / 2 ^ h)) := by ring
  rw [h1, h2, Nat.mul_add_mod, Nat.mul_add_mod]

/-- The `j`-th quotient parity `(T^[j](30*k + r) / 30) % 2` depends only on `k % 2^(j+1)`. -/
lemma T_iter_quot_mod2_eq {j k₁ k₂ r : ℕ} (hmod : k₁ % 2 ^ (j + 1) = k₂ % 2 ^ (j + 1)) :
    (T^[j] (30 * k₁ + r) / 30) % 2 = (T^[j] (30 * k₂ + r) / 30) % 2 := by
  set k₀ := k₁ % 2 ^ (j + 1)
  have hk1 : k₁ = 2 ^ (j + 1) * (k₁ / 2 ^ (j + 1)) + k₀ := by
    have := Nat.div_add_mod k₁ (2 ^ (j + 1)); omega
  have hk2 : k₂ = 2 ^ (j + 1) * (k₂ / 2 ^ (j + 1)) + k₀ := by
    have := Nat.div_add_mod k₂ (2 ^ (j + 1)); omega
  rw [hk1, hk2, T_iter_affine (j + 1) j k₀ _ r (Nat.le_succ j),
      T_iter_affine (j + 1) j k₀ _ r (Nat.le_succ j)]
  have hsub : j + 1 - j = 1 := by omega
  rw [hsub, pow_one]
  set D := prodOddMult j (30 * k₀ + r)
  set b := T^[j] (30 * k₀ + r)
  have h1 : (30 * 2 * D * (k₁ / 2 ^ (j + 1)) + b) / 30 =
      2 * D * (k₁ / 2 ^ (j + 1)) + b / 30 := by
    rw [show 30 * 2 * D * (k₁ / 2 ^ (j + 1)) = 30 * (2 * D * (k₁ / 2 ^ (j + 1))) by ring,
        Nat.mul_add_div (by norm_num)]
  have h2 : (30 * 2 * D * (k₂ / 2 ^ (j + 1)) + b) / 30 =
      2 * D * (k₂ / 2 ^ (j + 1)) + b / 30 := by
    rw [show 30 * 2 * D * (k₂ / 2 ^ (j + 1)) = 30 * (2 * D * (k₂ / 2 ^ (j + 1))) by ring,
        Nat.mul_add_div (by norm_num)]
  rw [h1, h2]
  have he1 : (2 * D * (k₁ / 2 ^ (j + 1)) + b / 30) % 2 = (b / 30) % 2 := by
    rw [show 2 * D * (k₁ / 2 ^ (j + 1)) = 2 * (D * (k₁ / 2 ^ (j + 1))) by ring, Nat.mul_add_mod]
  have he2 : (2 * D * (k₂ / 2 ^ (j + 1)) + b / 30) % 2 = (b / 30) % 2 := by
    rw [show 2 * D * (k₂ / 2 ^ (j + 1)) = 2 * (D * (k₂ / 2 ^ (j + 1))) by ring, Nat.mul_add_mod]
  rw [he1, he2]

/-- At the exact level `m` where `k₁, k₂` first diverge mod `2^(m+1)`, the `m`-th quotient
    parities `(T^[m](30*k + r) / 30) % 2` are opposite. -/
lemma T_iter_quot_mod2_ne {m k₁ k₂ r : ℕ}
    (hlo : k₁ % 2 ^ m = k₂ % 2 ^ m) (hhi : k₁ % 2 ^ (m + 1) ≠ k₂ % 2 ^ (m + 1)) :
    (T^[m] (30 * k₁ + r) / 30) % 2 ≠ (T^[m] (30 * k₂ + r) / 30) % 2 := by
  set k₀ := k₁ % 2 ^ m
  have hk1 : k₁ = 2 ^ m * (k₁ / 2 ^ m) + k₀ := by
    have := Nat.div_add_mod k₁ (2 ^ m); omega
  have hk2 : k₂ = 2 ^ m * (k₂ / 2 ^ m) + k₀ := by
    have := Nat.div_add_mod k₂ (2 ^ m); omega
  have hmod_expand : ∀ k : ℕ, k % 2 ^ m = k₀ →
      k % 2 ^ (m + 1) = 2 ^ m * ((k / 2 ^ m) % 2) + k₀ := by
    intro k hk0
    have hp : 2 ^ (m + 1) = 2 ^ m * 2 := by rw [pow_succ]
    have h1 : k = 2 ^ (m + 1) * ((k / 2 ^ m) / 2) + (2 ^ m * ((k / 2 ^ m) % 2) + k₀) := by
      have hdm := Nat.div_add_mod k (2 ^ m)
      have hd2 := Nat.div_add_mod (k / 2 ^ m) 2
      rw [hk0] at hdm
      rw [hp]
      calc k = 2 ^ m * (k / 2 ^ m) + k₀ := hdm.symm
        _ = 2 ^ m * (2 * ((k / 2 ^ m) / 2) + (k / 2 ^ m) % 2) + k₀ := by rw [hd2]
        _ = 2 ^ m * 2 * ((k / 2 ^ m) / 2) + (2 ^ m * ((k / 2 ^ m) % 2) + k₀) := by ring
    have hlt : 2 ^ m * ((k / 2 ^ m) % 2) + k₀ < 2 ^ (m + 1) := by
      have hk0_lt : k₀ < 2 ^ m := Nat.mod_lt k₁ (by positivity)
      have hm2 : (k / 2 ^ m) % 2 ≤ 1 := by omega
      rw [hp]; nlinarith
    conv_lhs => rw [h1]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  have hpar : (k₁ / 2 ^ m) % 2 ≠ (k₂ / 2 ^ m) % 2 := by
    intro heq
    apply hhi
    rw [hmod_expand k₁ rfl, hmod_expand k₂ hlo.symm, heq]
  rw [hk1, hk2, T_iter_affine m m k₀ _ r le_rfl, T_iter_affine m m k₀ _ r le_rfl]
  simp only [Nat.sub_self, pow_zero, mul_one]
  set D := prodOddMult m (30 * k₀ + r)
  set b := T^[m] (30 * k₀ + r)
  have hD : D % 2 = 1 := prodOddMult_odd m (30 * k₀ + r)
  have h1 : (30 * D * (k₁ / 2 ^ m) + b) / 30 = D * (k₁ / 2 ^ m) + b / 30 := by
    rw [show 30 * D * (k₁ / 2 ^ m) = 30 * (D * (k₁ / 2 ^ m)) by ring, Nat.mul_add_div (by norm_num)]
  have h2 : (30 * D * (k₂ / 2 ^ m) + b) / 30 = D * (k₂ / 2 ^ m) + b / 30 := by
    rw [show 30 * D * (k₂ / 2 ^ m) = 30 * (D * (k₂ / 2 ^ m)) by ring, Nat.mul_add_div (by norm_num)]
  rw [h1, h2]
  have hm1 : (D * (k₁ / 2 ^ m)) % 2 = (k₁ / 2 ^ m) % 2 := by rw [Nat.mul_mod, hD]; omega
  have hm2 : (D * (k₂ / 2 ^ m)) % 2 = (k₂ / 2 ^ m) % 2 := by rw [Nat.mul_mod, hD]; omega
  omega

/-- The 8 reachable residues modulo `30`: `S = {0, 1, 2, 4, 8, 15, 16, 17}`. -/
def InS30 (n : ℕ) : Prop :=
  n % 30 = 0 ∨ n % 30 = 1 ∨ n % 30 = 2 ∨ n % 30 = 4 ∨
  n % 30 = 8 ∨ n % 30 = 15 ∨ n % 30 = 16 ∨ n % 30 = 17

instance (n : ℕ) : Decidable (InS30 n) := by unfold InS30; infer_instance

/-- Allowed residues modulo `30`: even or in `{1, 15, 17} mod 30`. -/
def AllowedMod30 (n : ℕ) : Prop := n % 2 = 0 ∨ InABC n

instance (n : ℕ) : Decidable (AllowedMod30 n) := by
  unfold AllowedMod30 InABC InA InB InC; infer_instance

/-- `T(n) % 30` is determined solely by `n % 60`. -/
lemma T_mod30_eq_mod60 (n : ℕ) : T n % 30 = T (n % 60) % 30 := by
  have h : n = 30 * 2 ^ 1 * 1 * (n / 60) + n % 60 := by omega
  conv_lhs => rw [h]
  rw [T_step_affine 1 1 (n / 60) (n % 60) le_rfl]
  simp only [Nat.sub_self, pow_zero, mul_one]
  have : 30 * oddMult (n % 60) * (n / 60) = 30 * (oddMult (n % 60) * (n / 60)) := by ring
  rw [this, Nat.mul_add_mod]

private lemma InS30_backward_table :
    ∀ x : Fin 60, InS30 (T x.val) → InS30 x.val := by
  decide

/-- Backward closure of `S = {0, 1, 2, 4, 8, 15, 16, 17}` under `T`. -/
lemma InS30_of_T_mem {n : ℕ} (h : InS30 (T n)) : InS30 n := by
  have h1 : InS30 (T (n % 60)) := by
    unfold InS30 at h ⊢
    rwa [← T_mod30_eq_mod60]
  have h2 : InS30 (n % 60) := InS30_backward_table ⟨n % 60, Nat.mod_lt n (by omega)⟩ h1
  unfold InS30 at h2 ⊢
  omega

private lemma InS30_forward_table :
    ∀ x : Fin 60, InS30 x.val → AllowedMod30 (T x.val) → InS30 (T x.val) := by
  decide

lemma InS30_T_of_allowed {n : ℕ} (hS : InS30 n) (hA : AllowedMod30 (T n)) : InS30 (T n) := by
  have h1 : InS30 (n % 60) := by unfold InS30 at hS ⊢; omega
  have h2 : AllowedMod30 (T (n % 60)) := by
    have hm := T_mod30_eq_mod60 n
    unfold AllowedMod30 InABC InA InB InC at hA ⊢
    omega
  have h3 := InS30_forward_table ⟨n % 60, Nat.mod_lt n (by omega)⟩ h1 h2
  unfold InS30 at h3 ⊢
  rwa [T_mod30_eq_mod60]

lemma allowedMod30_of_InS30 {n : ℕ} (h : InS30 n) : AllowedMod30 n := by
  unfold InS30 at h
  unfold AllowedMod30 InABC InA InB InC
  omega

/-- Reachability of `1` under `f` is equivalent to reachability of `1` under shortcut `T`. -/
theorem reaches_f_one_iff_T {n : ℕ} : Reaches f n 1 ↔ Reaches T n 1 := by
  constructor
  · rintro ⟨k, hk⟩
    induction k using Nat.strong_induction_on generalizing n with
    | h k ih =>
      cases k with
      | zero => exact ⟨0, hk⟩
      | succ k =>
        by_cases hev : n % 2 = 0
        · rw [Function.iterate_succ_apply, f_even hev] at hk
          have hT : T n = n / 2 := by simp [T, hev]
          obtain ⟨j, hj⟩ := ih k (by omega) hk
          exact ⟨j + 1, by rw [Function.iterate_succ_apply, hT, hj]⟩
        · have hodd : n % 2 = 1 := by omega
          cases k with
          | zero =>
            change f n = 1 at hk
            have := f_odd_even hodd
            omega
          | succ k =>
            rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at hk
            have hT : T n = f (f n) := by
              have := T_eq_f_or_ff n
              simp only [hev, ↓reduceIte] at this
              exact this
            rw [← hT] at hk
            obtain ⟨j, hj⟩ := ih k (by omega) hk
            exact ⟨j + 1, by rw [Function.iterate_succ_apply, hj]⟩
  · rintro ⟨k, hk⟩
    obtain ⟨m, hm⟩ := T_iter_is_f_iter k n
    exact ⟨m, hm.symm.trans hk⟩

lemma T_one_eq : T 1 = 1 := by decide

lemma T_iter_one (k : ℕ) : T^[k] 1 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, T_one_eq]

/-- Every integer reaching `1` stays inside `S = {0, 1, 2, 4, 8, 15, 16, 17} mod 30` forever under `T`. -/
lemma InS30_T_iter_of_reaches_one {n : ℕ} (h : Reaches f n 1) (j : ℕ) :
    InS30 (T^[j] n) := by
  obtain ⟨L, hL⟩ := reaches_f_one_iff_T.mp h
  have hmax : InS30 (T^[max j L] n) := by
    have hsplit : max j L = (max j L - L) + L := by omega
    rw [hsplit, Function.iterate_add_apply, hL, T_iter_one]
    unfold InS30; omega
  have hdown : ∀ d : ℕ, InS30 (T^[max j L - d] n) := by
    intro d
    induction d with
    | zero => simpa using hmax
    | succ d ih =>
      by_cases hle : d + 1 ≤ max j L
      · have hstep : T (T^[max j L - (d + 1)] n) = T^[max j L - d] n := by
          rw [← Function.iterate_succ_apply' T]
          congr 1; omega
        exact InS30_of_T_mem (hstep.symm ▸ ih)
      · have : max j L - (d + 1) = max j L - d := by omega
        rwa [this]
  have := hdown (max j L - j)
  have heq : max j L - (max j L - j) = j := by omega
  rwa [heq] at this

/-- Survival of `30 * k + r` through the first `h` halvings without hitting a forbidden odd residue. -/
def Survives (r h k : ℕ) : Prop :=
  ∀ j ≤ h, AllowedMod30 (T^[j] (30 * k + r))

instance (r h k : ℕ) : Decidable (Survives r h k) := by
  unfold Survives
  exact Nat.decidableBallLE h _

lemma survives_iff_InS30 {r : ℕ} (hr : InS30 r) (h k : ℕ) :
    Survives r h k ↔ InS30 (T^[h] (30 * k + r)) := by
  constructor
  · intro hsurv
    induction h with
    | zero =>
      simp only [Function.iterate_zero, id_eq]
      unfold InS30 at hr ⊢; omega
    | succ h ih =>
      have hS := ih (fun j hj => hsurv j (by omega))
      have h1 := hsurv (h + 1) le_rfl
      rw [Function.iterate_succ_apply'] at h1 ⊢
      exact InS30_T_of_allowed hS h1
  · intro hSh j hj
    have hSj : InS30 (T^[j] (30 * k + r)) := by
      have hdown : ∀ d : ℕ, d ≤ h → InS30 (T^[h - d] (30 * k + r)) := by
        intro d hd
        induction d with
        | zero => simpa using hSh
        | succ d ih =>
          have hstep : T (T^[h - (d + 1)] (30 * k + r)) = T^[h - d] (30 * k + r) := by
            rw [← Function.iterate_succ_apply' T]
            congr 1; omega
          exact InS30_of_T_mem (hstep.symm ▸ ih (by omega))
      have := hdown (h - j) (by omega)
      have heq : h - (h - j) = j := by omega
      rwa [heq] at this
    exact allowedMod30_of_InS30 hSj

lemma survives_mod_pow {r h k₁ k₂ : ℕ} (hmod : k₁ % 2 ^ h = k₂ % 2 ^ h) :
    Survives r h k₁ ↔ Survives r h k₂ := by
  unfold Survives
  refine forall₂_congr fun j hj => ?_
  have hm := T_iter_mod30_eq (r := r) hj hmod
  unfold AllowedMod30 InABC InA InB InC
  omega

/-! ### The `+30` inverse commutator (`P(u) = 64u - 33`, `Q(u) = 64u - 3 = P(u) + 30`) -/

/-- Low backward digit-1 move `L(u) = 2u - 1`. -/
def commL (u : ℕ) : ℕ := 2 * u - 1

/-- High backward digit-1 move `H(u) = 32u - 1`. -/
def commH (u : ℕ) : ℕ := 32 * u - 1

/-- Commutator map `P(u) = H(L(u)) = 64u - 33`. -/
def commP (u : ℕ) : ℕ := 64 * u - 33

/-- Shifted commutator map `Q(u) = L(H(u)) = 64u - 3 = P(u) + 30`. -/
def commQ (u : ℕ) : ℕ := 64 * u - 3

private lemma commL_props {u : ℕ} (hu1 : 1 ≤ u) (hu10 : u % 10 = 1) :
    1 ≤ commL u ∧ commL u % 10 = 1 ∧ Reaches f (commL u) u := by
  refine ⟨by unfold commL; omega, by unfold commL; omega, ⟨2, ?_⟩⟩
  have hd : d (commL u) = 1 := by unfold d commL; omega
  calc f^[2] (commL u) = f (f (commL u)) := rfl
    _ = f (d (commL u) * commL u + 1) := by congr 1; exact f_odd (by unfold commL; omega)
    _ = f (2 * u) := by rw [hd, one_mul]; congr 1; unfold commL; omega
    _ = (2 * u) / 2 := f_even (by omega)
    _ = u := by omega

private lemma commH_props {u : ℕ} (hu1 : 1 ≤ u) (hu10 : u % 10 = 1) :
    1 ≤ commH u ∧ commH u % 10 = 1 ∧ Reaches f (commH u) u := by
  refine ⟨by unfold commH; omega, by unfold commH; omega, ⟨6, ?_⟩⟩
  rw [Function.iterate_succ_apply, f_odd (by unfold commH; omega)]
  have hd : d (commH u) = 1 := by unfold d commH; omega
  rw [hd, one_mul]
  have hsub : commH u + 1 = 2 ^ 5 * u := by unfold commH; omega
  rw [hsub, f_iter_two_pow]

lemma commP_props {u : ℕ} (hu1 : 1 ≤ u) (hu10 : u % 10 = 1) :
    u < commP u ∧ commP u % 30 = u % 30 ∧ Reaches f (commP u) u := by
  have heq : commP u = commH (commL u) := by unfold commP commH commL; omega
  obtain ⟨hL1, hL10, hLr⟩ := commL_props hu1 hu10
  obtain ⟨_, _, hHr⟩ := commH_props hL1 hL10
  refine ⟨by unfold commP; omega, by unfold commP; omega, ?_⟩
  rw [heq]
  exact reaches_trans hHr hLr

lemma commQ_props {u : ℕ} (hu1 : 1 ≤ u) (hu10 : u % 10 = 1) :
    commQ u = commP u + 30 ∧ commQ u % 30 = u % 30 ∧ Reaches f (commQ u) u := by
  have heq : commQ u = commL (commH u) := by unfold commQ commH commL; omega
  obtain ⟨hH1, hH10, hHr⟩ := commH_props hu1 hu10
  obtain ⟨_, _, hLr⟩ := commL_props hH1 hH10
  refine ⟨by unfold commQ commP; omega, by unfold commQ; omega, ?_⟩
  rw [heq]
  exact reaches_trans hLr hHr

private lemma commP_iter_props (k : ℕ) {u : ℕ} (_hu1 : 1 ≤ u) (hu10 : u % 10 = 1) :
    u + k ≤ commP^[k] u ∧ (commP^[k] u) % 30 = u % 30 ∧ Reaches f (commP^[k] u) u := by
  induction k with
  | zero => simp [reaches_refl]
  | succ k ih =>
    obtain ⟨hle, h30, hreach⟩ := ih
    have hv1 : 1 ≤ commP^[k] u := by omega
    have hv10 : (commP^[k] u) % 10 = 1 := by omega
    obtain ⟨hlt, h30', hr'⟩ := commP_props hv1 hv10
    rw [Function.iterate_succ_apply']
    exact ⟨by omega, by omega, reaches_trans hr' hreach⟩

private lemma commP_zmod {q : ℕ} (u : ℕ) (hu1 : 1 ≤ u) :
    ((commP u : ℕ) : ZMod q) = (64 : ZMod q) * (u : ZMod q) - (33 : ZMod q) := by
  have h : commP u + 33 = 64 * u := by unfold commP; omega
  have hz : ((commP u + 33 : ℕ) : ZMod q) = ((64 * u : ℕ) : ZMod q) := by rw [h]
  push_cast at hz
  exact eq_sub_of_add_eq hz

/-- The `+30` inverse commutator theorem: for any `u ≥ 1` with `u ≡ 1 (mod 10)`, any odd `D'`,
    any `b ≡ u (mod 30)`, and any lower bound `M`, there is `k''` such that
    `30 * D' * k'' + b ≥ M` and `Reaches f (30 * D' * k'' + b) u`. -/
theorem commutator_hit_prog {u D' b M : ℕ} (hu1 : 1 ≤ u) (hu10 : u % 10 = 1)
    (hD' : D' % 2 = 1) (hb : b % 30 = u % 30) :
    ∃ k'' : ℕ, M ≤ 30 * D' * k'' + b ∧ Reaches f (30 * D' * k'' + b) u := by
  set q := 15 * D'
  have : NeZero q := ⟨by omega⟩
  have hcop64 : Nat.Coprime 64 q := by
    have : Nat.Coprime 2 q := by rw [Nat.coprime_two_left]; exact Nat.odd_iff.mpr (by omega)
    simpa [show (64 : ℕ) = 2 ^ 6 by norm_num] using this.pow_left 6
  let u64 : (ZMod q)ˣ := ZMod.unitOfCoprime 64 hcop64
  let phi : Equiv.Perm (ZMod q) :=
    { toFun := fun x => (u64 : ZMod q) * x - 33
      invFun := fun y => (u64⁻¹ : (ZMod q)ˣ) * (y + 33)
      left_inv := fun x => by
        dsimp only
        rw [sub_add_cancel, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      right_inv := fun y => by
        dsimp only
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul, add_sub_cancel_right] }
  set s := orderOf phi
  have hs_pos : 0 < s := orderOf_pos phi
  have hphi_s : ∀ x : ZMod q, phi^[s] x = x := by
    intro x
    have hs_eq : phi ^ s = 1 := pow_orderOf_eq_one phi
    have := congr_arg (fun g : Equiv.Perm (ZMod q) => g x) hs_eq
    simpa [Equiv.Perm.coe_pow] using this
  have hcommP_phi : ∀ k v : ℕ, 1 ≤ v → v % 10 = 1 →
      ((commP^[k] v : ℕ) : ZMod q) = phi^[k] (v : ZMod q) := by
    intro k
    induction k with
    | zero => intro _ _ _; rfl
    | succ k ih =>
      intro v hv1 hv10
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      obtain ⟨hle, _, _⟩ := commP_iter_props k hv1 hv10
      rw [commP_zmod _ (by omega), ih v hv1 hv10]
      simp [phi, u64]
  let stepAdd30 : ℕ → ℕ := fun v => commQ (commP^[s - 1] v)
  have hstep_props : ∀ v : ℕ, 1 ≤ v → v % 10 = 1 →
      1 ≤ stepAdd30 v ∧ stepAdd30 v % 30 = v % 30 ∧ Reaches f (stepAdd30 v) v ∧
      ((stepAdd30 v : ℕ) : ZMod q) = (v : ZMod q) + 30 := by
    intro v hv1 hv10
    obtain ⟨hle, h30, hreach⟩ := commP_iter_props (s - 1) hv1 hv10
    have hw1 : 1 ≤ commP^[s - 1] v := by omega
    have hw10 : (commP^[s - 1] v) % 10 = 1 := by omega
    obtain ⟨hQeq, hQ30, hQreach⟩ := commQ_props hw1 hw10
    refine ⟨by dsimp [stepAdd30]; unfold commQ; omega,
            by dsimp [stepAdd30]; omega,
            reaches_trans hQreach hreach, ?_⟩
    dsimp [stepAdd30]
    rw [hQeq, Nat.cast_add, Nat.cast_ofNat]
    have hPs : commP (commP^[s - 1] v) = commP^[s] v := by
      rw [← Function.iterate_succ_apply' commP]; congr 1; omega
    rw [hPs, hcommP_phi s v hv1 hv10, hphi_s]
  have hstep_iter : ∀ t : ℕ,
      1 ≤ stepAdd30^[t] u ∧ (stepAdd30^[t] u) % 30 = u % 30 ∧
      Reaches f (stepAdd30^[t] u) u ∧
      ((stepAdd30^[t] u : ℕ) : ZMod q) = (u : ZMod q) + 30 * (t : ZMod q) := by
    intro t
    induction t with
    | zero => simp [reaches_refl, hu1]
    | succ t ih =>
      obtain ⟨h1, h30, hr, hz⟩ := ih
      obtain ⟨h1', h30', hr', hz'⟩ := hstep_props (stepAdd30^[t] u) h1 (by omega)
      rw [Function.iterate_succ_apply']
      refine ⟨h1', by omega, reaches_trans hr' hr, ?_⟩
      rw [hz', hz]; push_cast; ring
  have ht_exists : ∃ t : ℕ, ((u : ZMod q) + 30 * (t : ZMod q)) = (b : ZMod q) := by
    have hcop2 : Nat.Coprime 2 D' := by rw [Nat.coprime_two_left]; exact Nat.odd_iff.mpr hD'
    have h15 : (b : ZMod q) - (u : ZMod q) = 15 * (((b / 15 : ℕ) : ZMod q) - ((u / 15 : ℕ) : ZMod q)) := by
      have hbu : b % 15 = u % 15 := by omega
      have hb15 : b = 15 * (b / 15) + b % 15 := (Nat.div_add_mod b 15).symm
      have hu15 : u = 15 * (u / 15) + u % 15 := (Nat.div_add_mod u 15).symm
      have hbz : (b : ZMod q) = 15 * ((b / 15 : ℕ) : ZMod q) + ((b % 15 : ℕ) : ZMod q) := by
        conv_lhs => rw [hb15]
        push_cast; rfl
      have huz : (u : ZMod q) = 15 * ((u / 15 : ℕ) : ZMod q) + ((u % 15 : ℕ) : ZMod q) := by
        conv_lhs => rw [hu15]
        push_cast; rfl
      rw [hbz, huz, hbu]; ring
    have : NeZero D' := ⟨by omega⟩
    let u2 : (ZMod D')ˣ := ZMod.unitOfCoprime 2 hcop2
    let cD : ZMod D' := (u2⁻¹ : (ZMod D')ˣ) * (((b / 15 : ℕ) : ZMod D') - ((u / 15 : ℕ) : ZMod D'))
    have hpos_sub : u / 15 ≤ b / 15 + D' * u := by
      have h1 : u / 15 ≤ u := Nat.div_le_self u 15
      have h2 : u ≤ D' * u := Nat.le_mul_of_pos_left u (by omega)
      omega
    refine ⟨cD.val, ?_⟩
    have h2c : (2 * cD.val : ℕ) % D' = ((b / 15 + D' * u) - u / 15) % D' := by
      have hc : (2 : ZMod D') * (cD.val : ZMod D') = ((b / 15 : ℕ) : ZMod D') - ((u / 15 : ℕ) : ZMod D') := by
        rw [ZMod.natCast_zmod_val]
        have hcoe : (2 : ZMod D') = (u2 : ZMod D') := by simp [u2]
        rw [hcoe]; dsimp [cD]
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      have hcast : (((b / 15 + D' * u) - u / 15 : ℕ) : ZMod D') =
          ((b / 15 : ℕ) : ZMod D') - ((u / 15 : ℕ) : ZMod D') := by
        rw [Nat.cast_sub hpos_sub]; push_cast; simp
      rw [← hcast] at hc
      have hc' : ((2 * cD.val : ℕ) : ZMod D') = (((b / 15 + D' * u) - u / 15 : ℕ) : ZMod D') := by
        simpa using hc
      exact (ZMod.natCast_eq_natCast_iff' _ _ D').mp hc'
    have h15mul : (30 * cD.val : ℕ) % q = (15 * ((b / 15 + D' * u) - u / 15)) % q := by
      have h1 : 30 * cD.val = 15 * (2 * cD.val) := by ring
      rw [h1]; dsimp [q]
      rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, h2c]
    have h15z : (30 : ZMod q) * (cD.val : ZMod q) =
        15 * (((b / 15 : ℕ) : ZMod q) - ((u / 15 : ℕ) : ZMod q)) := by
      have hz := (ZMod.natCast_eq_natCast_iff' _ _ q).mpr h15mul
      push_cast at hz
      rw [hz, Nat.cast_sub hpos_sub]; push_cast
      have hDq : (15 : ZMod q) * (D' : ZMod q) = 0 := by
        rw [← Nat.cast_ofNat (n := 15), ← Nat.cast_mul]
        exact ZMod.natCast_self q
      calc (15 : ZMod q) * ((b / 15 : ℕ) + (D' : ZMod q) * (u : ZMod q) - (u / 15 : ℕ))
          = 15 * (((b / 15 : ℕ) : ZMod q) - ((u / 15 : ℕ) : ZMod q)) +
            ((15 : ZMod q) * (D' : ZMod q)) * (u : ZMod q) := by ring
        _ = 15 * (((b / 15 : ℕ) : ZMod q) - ((u / 15 : ℕ) : ZMod q)) := by rw [hDq, zero_mul, add_zero]
    rw [h15z, ← h15, add_sub_cancel]
  obtain ⟨t, ht⟩ := ht_exists
  set v₀ := stepAdd30^[t] u
  obtain ⟨hv1, hv30, hvr, hvz⟩ := hstep_iter t
  have hv1' : 1 ≤ v₀ := hv1
  have hv30' : v₀ % 30 = u % 30 := hv30
  have hvr' : Reaches f v₀ u := hvr
  have hvz' : (v₀ : ZMod q) = (b : ZMod q) := hvz.trans ht
  set N := max M b
  set o := commP^[s * N] v₀
  obtain ⟨ho_ge, ho30, hor⟩ := commP_iter_props (s * N) hv1' (by omega)
  have ho_ge_N : N ≤ o := by
    have h1 : N ≤ s * N := Nat.le_mul_of_pos_left N hs_pos
    change v₀ + s * N ≤ o at ho_ge
    omega
  have ho_zmod : (o : ZMod q) = (b : ZMod q) := by
    dsimp [o]
    rw [hcommP_phi (s * N) v₀ hv1' (by omega), ← hvz']
    clear ho_ge ho30 hor ho_ge_N o
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Nat.mul_succ, add_comm, Function.iterate_add_apply, hphi_s, ih]
  have ho_mod_q : o % q = b % q := (ZMod.natCast_eq_natCast_iff' o b q).mp ho_zmod
  have ho_mod_2 : o % 2 = b % 2 := by
    change o % 30 = v₀ % 30 at ho30
    omega
  have hcop2q : Nat.Coprime 2 q := by rw [Nat.coprime_two_left]; exact Nat.odd_iff.mpr (by omega)
  have ho_mod_2q : o % (2 * q) = b % (2 * q) :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop2q).mp ⟨ho_mod_2, ho_mod_q⟩
  have h2q : 2 * q = 30 * D' := by dsimp [q]; ring
  rw [h2q] at ho_mod_2q
  have hb_le_o : b ≤ o := le_trans (le_max_right M b) ho_ge_N
  have hdvd : 30 * D' ∣ o - b := (Nat.modEq_iff_dvd' hb_le_o).mp ho_mod_2q.symm
  obtain ⟨k'', hk''⟩ := hdvd
  have ho_form : 30 * D' * k'' + b = o := by omega
  refine ⟨k'', ?_, ?_⟩
  · rw [ho_form]; exact le_trans (le_max_left M b) ho_ge_N
  · rw [ho_form]; exact reaches_trans hor hvr'

/-! ### Mod-30 progression routing (to `1 mod 30` and to exit `{19, 23} mod 30`) -/

private lemma T_prog_one_step (D b : ℕ) (s : Fin 2) :
    ∀ j : ℕ, T (30 * D * (2 * j + s.val) + b) =
      30 * (oddMult (30 * D * s.val + b) * D) * j + T (30 * D * s.val + b) := by
  intro j
  have h : 30 * D * (2 * j + s.val) + b = 30 * 2 ^ 1 * D * j + (30 * D * s.val + b) := by ring
  rw [h, T_step_affine 1 D j (30 * D * s.val + b) le_rfl]
  simp only [Nat.sub_self, pow_zero, mul_one]

/-- From any progression `30*D*j + b` with `D` odd, splitting `j` by parity reaches EITHER
    mod-30 successor `T(30*t + b%30) % 30` (`t ∈ {0, 1}`). -/
lemma prog_step_choose (D b : ℕ) (hD : D % 2 = 1) (t : Fin 2) :
    ∃ s : Fin 2, ∃ D' b' : ℕ, D' % 2 = 1 ∧
      b' % 30 = T (30 * t.val + b % 30) % 30 ∧
      (∀ j : ℕ, T (30 * D * (2 * j + s.val) + b) = 30 * D' * j + b') := by
  let sv : ℕ := (t.val + b / 30) % 2
  refine ⟨⟨sv, by omega⟩, oddMult (30 * D * sv + b) * D, T (30 * D * sv + b), ?_, ?_, ?_⟩
  · rw [Nat.mul_mod, oddMult_odd, hD]
  · rw [T_mod30_eq_mod60 (30 * D * sv + b)]
    have h60 : (30 * D * sv + b) % 60 = 30 * t.val + b % 30 := by
      have hDs : (D * sv + b / 30) % 2 = t.val := by
        have h1 : (D * sv) % 2 = sv % 2 := by rw [Nat.mul_mod, hD]; omega
        have ht2 : t.val < 2 := t.isLt
        omega
      have hdiv : 30 * D * sv + b = 30 * (D * sv + b / 30) + b % 30 := by
        have hbm := Nat.div_add_mod b 30
        calc 30 * D * sv + b = 30 * (D * sv) + (30 * (b / 30) + b % 30) := by rw [hbm]; ring
          _ = 30 * (D * sv + b / 30) + b % 30 := by ring
      have ht2 : t.val < 2 := t.isLt
      have hb30 : b % 30 < 30 := Nat.mod_lt b (by omega)
      rw [hdiv]; omega
    rw [h60]
  · exact T_prog_one_step D b ⟨sv, by omega⟩

private lemma prog_step_path :
    ∀ (bits : List (Fin 2)) (D b : ℕ), D % 2 = 1 →
      ∃ c < 2 ^ bits.length, ∃ D' b' : ℕ, D' % 2 = 1 ∧
        b' % 30 = bits.foldl (fun r t => T (30 * t.val + r) % 30) (b % 30) ∧
        (∀ j : ℕ, T^[bits.length] (30 * D * (2 ^ bits.length * j + c) + b) = 30 * D' * j + b') := by
  intro bits
  induction bits with
  | nil =>
    intro D b hD
    exact ⟨0, by norm_num, D, b, hD, rfl, fun j => by simp⟩
  | cons t rest ih =>
    intro D b hD
    obtain ⟨s, D1, b1, hD1, hb1, hstep1⟩ := prog_step_choose D b hD t
    obtain ⟨c2, hc2, D2, b2, hD2, hb2, hstep2⟩ := ih D1 b1 hD1
    refine ⟨2 * c2 + s.val, ?_, D2, b2, hD2, ?_, ?_⟩
    · simp only [List.length_cons, pow_succ']; have := s.isLt; omega
    · simp only [List.foldl_cons, ← hb1, hb2]
    · intro j
      simp only [List.length_cons]
      rw [Function.iterate_succ_apply]
      have hrew : 30 * D * (2 ^ (rest.length + 1) * j + (2 * c2 + s.val)) + b =
          30 * D * (2 * (2 ^ rest.length * j + c2) + s.val) + b := by
        rw [pow_succ']; ring
      rw [hrew, hstep1, hstep2]

private def pathToOne : ℕ → List (Fin 2)
  | 1  => []
  | 2  => [0]
  | 4  => [0, 0]
  | 8  => [0, 0, 0]
  | 15 => [0, 0, 0, 0]
  | 16 => [0, 0, 0, 0]
  | 0  => [1, 0, 0, 0, 0]
  | 17 => [1, 0, 0, 0, 0]
  | _  => []

private lemma pathToOne_spec :
    ∀ r : Fin 30, InS30 r.val →
      (pathToOne r.val).length ≤ 5 ∧
      (pathToOne r.val).foldl (fun x t => T (30 * t.val + x) % 30) r.val = 1 := by
  decide

/-- From any progression in `S`, some sub-progression of depth `d ≤ 5` lands in `1 mod 30`. -/
theorem route_S30_to_one {D b : ℕ} (hD : D % 2 = 1) (hb : InS30 b) :
    ∃ d ≤ 5, ∃ c < 2 ^ d, ∃ D' b' : ℕ, D' % 2 = 1 ∧ b' % 30 = 1 ∧
      ∀ j : ℕ, T^[d] (30 * D * (2 ^ d * j + c) + b) = 30 * D' * j + b' := by
  have hbr : InS30 (b % 30) := by unfold InS30 at hb ⊢; simpa using hb
  have hspec := pathToOne_spec ⟨b % 30, Nat.mod_lt b (by omega)⟩ hbr
  obtain ⟨c, hc, D', b', hD', hb', hiter⟩ := prog_step_path (pathToOne (b % 30)) D b hD
  exact ⟨(pathToOne (b % 30)).length, hspec.1, c, hc, D', b', hD', hb'.trans hspec.2, hiter⟩

private def pathToExit : ℕ → List (Fin 2)
  | 15 => [1]
  | 16 => [1]
  | 8  => [1]
  | 0  => [1, 1]
  | 1  => [1, 1]
  | 2  => [1, 1]
  | 17 => [1, 1]
  | 4  => [0, 1, 1]
  | _  => []

private lemma pathToExit_spec :
    ∀ r : Fin 30, InS30 r.val →
      let p := pathToExit r.val
      p.length ≤ 3 ∧
      (∀ i < p.length, InS30 ((p.take i).foldl (fun x t => T (30 * t.val + x) % 30) r.val)) ∧
      (p.foldl (fun x t => T (30 * t.val + x) % 30) r.val = 19 ∨
       p.foldl (fun x t => T (30 * t.val + x) % 30) r.val = 23) := by
  decide

/-- Odd integer `n` starts in `{1, 15, 17} mod 30` (`InABC n`), stays in allowed residues,
    and exits `{1, 15, 17} mod 30` at `19` or `23 mod 30` at some positive halving step `j ≥ 1`. -/
def ExitsAt19Or23 (n : ℕ) : Prop :=
  InABC n ∧ ∃ j : ℕ, 1 ≤ j ∧ (∀ i < j, AllowedMod30 (T^[i] n)) ∧
    (T^[j] n % 30 = 19 ∨ T^[j] n % 30 = 23)

/-- From any progression in `S`, some sub-progression of depth `d ≤ 3` exits at `19` or `23 mod 30`. -/
theorem route_S30_to_exit {D b : ℕ} (hD : D % 2 = 1) (hb : InS30 b) :
    ∃ d ≤ 3, ∃ c < 2 ^ d, ∀ j : ℕ,
      (∀ i < d, AllowedMod30 (T^[i] (30 * D * (2 ^ d * j + c) + b))) ∧
      (T^[d] (30 * D * (2 ^ d * j + c) + b) % 30 = 19 ∨
       T^[d] (30 * D * (2 ^ d * j + c) + b) % 30 = 23) := by
  have hbr : InS30 (b % 30) := by unfold InS30 at hb ⊢; simpa using hb
  have hspec := pathToExit_spec ⟨b % 30, Nat.mod_lt b (by omega)⟩ hbr
  set p := pathToExit (b % 30)
  -- Stronger version of prog_step_path tracking intermediate residues mod 30!
  have hpath_all : ∀ (bits : List (Fin 2)) (D b : ℕ), D % 2 = 1 →
      ∃ c < 2 ^ bits.length, ∀ j : ℕ, ∀ i ≤ bits.length,
        T^[i] (30 * D * (2 ^ bits.length * j + c) + b) % 30 =
          (bits.take i).foldl (fun x t => T (30 * t.val + x) % 30) (b % 30) := by
    intro bits
    induction bits with
    | nil =>
      intro D b _
      refine ⟨0, by norm_num, fun j i hi => ?_⟩
      have hi0 : i = 0 := by simpa using hi
      subst hi0
      simp only [Function.iterate_zero, id_eq, List.take_zero, List.foldl_nil, List.length_nil]
      rw [show 30 * D * (2 ^ 0 * j + 0) = 30 * (D * j) by ring, Nat.mul_add_mod]
    | cons t rest ih =>
      intro D b hD
      obtain ⟨s, D1, b1, hD1, hb1, hstep1⟩ := prog_step_choose D b hD t
      obtain ⟨c2, hc2, hrec⟩ := ih D1 b1 hD1
      refine ⟨2 * c2 + s.val, ?_, fun j i hi => ?_⟩
      · simp only [List.length_cons, pow_succ']; have := s.isLt; omega
      · cases i with
        | zero =>
          simp only [Function.iterate_zero, id_eq, List.take_zero, List.foldl_nil, List.length_cons]
          rw [show 30 * D * (2 ^ (rest.length + 1) * j + (2 * c2 + s.val)) =
              30 * (D * (2 ^ (rest.length + 1) * j + (2 * c2 + s.val))) by ring, Nat.mul_add_mod]
        | succ i =>
          simp only [List.length_cons] at hi ⊢
          rw [Function.iterate_succ_apply]
          have hrew : 30 * D * (2 ^ (rest.length + 1) * j + (2 * c2 + s.val)) + b =
              30 * D * (2 * (2 ^ rest.length * j + c2) + s.val) + b := by
            rw [pow_succ']; ring
          rw [hrew, hstep1, hrec j i (by omega)]
          simp only [List.take_succ_cons, List.foldl_cons, hb1]
  obtain ⟨c, hc, hall⟩ := hpath_all p D b hD
  refine ⟨p.length, hspec.1, c, hc, fun j => ⟨fun i hi => ?_, ?_⟩⟩
  · have hm := hall j i (le_of_lt hi)
    have hS0 : InS30 ((p.take i).foldl (fun x t => T (30 * t.val + x) % 30) (b % 30)) :=
      hspec.2.1 i hi
    have hS : InS30 (T^[i] (30 * D * (2 ^ p.length * j + c) + b)) := by
      have hS' : InS30 (T^[i] (30 * D * (2 ^ p.length * j + c) + b) % 30) := by
        rw [hm]; exact hS0
      unfold InS30 at hS' ⊢
      rwa [Nat.mod_mod] at hS'
    exact allowedMod30_of_InS30 hS
  · have hm := hall j p.length le_rfl
    rw [List.take_length] at hm
    rw [hm]; exact hspec.2.2

/-! ## Part 2: Exact `2`-adic Cantor closure (`thm:cantor` Part 1) -/

/-- Odd basin of `1` in `ℕ`. -/
def B1Set : Set ℕ := {n : ℕ | n % 2 = 1 ∧ Reaches f n 1}

/-- Odd basin of `1` embedded in `ℤ_[2]`. -/
def B1Padic : Set ℤ_[2] := (fun n : ℕ => (n : ℤ_[2])) '' B1Set

/-- Coordinate set `K_r = {k ∈ ℕ : 30*k + r ∈ B_1}` for `r ∈ {1, 15, 17}`. -/
def KrSet (r : ℕ) : Set ℕ := {k : ℕ | 30 * k + r ∈ B1Set}

/-- Coordinate set `K_r` embedded in `ℤ_[2]`. -/
def KrPadic (r : ℕ) : Set ℤ_[2] := (fun k : ℕ => (k : ℤ_[2])) '' KrSet r

/-- The `2`-adic survival Cantor set `𝒦_r ⊂ ℤ_[2]`. -/
def KCal (r : ℕ) : Set ℤ_[2] := {x : ℤ_[2] | ∀ h : ℕ, Survives r h (x.appr h)}

/-- The affine embedding `k ↦ 30 * k + r` on `ℤ_[2]`. -/
noncomputable def affine30 (r : ℕ) (k : ℤ_[2]) : ℤ_[2] := (30 : ℤ_[2]) * k + (r : ℤ_[2])

private lemma padic2_norm_le_iff_appr_eq (x y : ℤ_[2]) (h : ℕ) :
    ‖x - y‖ ≤ (2 : ℝ) ^ (-(h : ℤ)) ↔ x.appr h = y.appr h := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcast2 : (2 : ℝ) ^ (-(h : ℤ)) = ((2 : ℕ) : ℝ) ^ (-(h : ℤ)) := by norm_num
  rw [hcast2, PadicInt.norm_le_pow_iff_mem_span_pow]
  have hx := PadicInt.appr_spec h x
  have hy := PadicInt.appr_spec h y
  constructor
  · intro hxy
    have hsub : ((x.appr h : ℤ) - (y.appr h : ℤ) : ℤ_[2]) ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ h} := by
      have heq : ((x.appr h : ℤ) - (y.appr h : ℤ) : ℤ_[2]) =
          (x - y) - (x - (x.appr h : ℤ_[2])) + (y - (y.appr h : ℤ_[2])) := by push_cast; ring
      rw [heq]
      exact Ideal.add_mem _ (Ideal.sub_mem _ hxy hx) hy
    rw [Ideal.mem_span_singleton] at hsub
    have hdvd : (((2 : ℕ) : ℤ) ^ h) ∣ ((x.appr h : ℤ) - (y.appr h : ℤ)) := by
      rw [← PadicInt.pow_p_dvd_int_iff (p := 2) h]
      simpa using hsub
    have hlt1 : (x.appr h : ℤ) < ((2 : ℕ) : ℤ) ^ h := by exact_mod_cast PadicInt.appr_lt x h
    have hlt2 : (y.appr h : ℤ) < ((2 : ℕ) : ℤ) ^ h := by exact_mod_cast PadicInt.appr_lt y h
    rcases hdvd with ⟨q, hq⟩
    have hq0 : q = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : q ≤ -1 := by omega
        nlinarith
      · have : 1 ≤ q := by omega
        nlinarith
    have heqz : (x.appr h : ℤ) = (y.appr h : ℤ) := by nlinarith
    exact_mod_cast heqz
  · intro heq
    have hdiff : x - y = (x - (x.appr h : ℤ_[2])) - (y - (y.appr h : ℤ_[2])) := by
      rw [heq]; ring
    rw [hdiff]
    exact Ideal.sub_mem _ hx hy

private lemma padic2_appr_natCast (k h : ℕ) : ((k : ℤ_[2]).appr h) = k % 2 ^ h := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set r := k % 2 ^ h
  have h1 := PadicInt.appr_spec h (k : ℤ_[2])
  have hdvd_k : (((2 : ℕ) : ℤ) ^ h) ∣ ((k : ℤ) - (r : ℤ)) := by
    refine ⟨(k / 2 ^ h : ℕ), ?_⟩
    have hdm : 2 ^ h * (k / 2 ^ h) + r = k := Nat.div_add_mod k (2 ^ h)
    have hdmz : ((2 : ℕ) : ℤ) ^ h * (k / 2 ^ h : ℕ) + (r : ℤ) = (k : ℤ) := by
      exact_mod_cast hdm
    linarith
  have h2 : ((k : ℤ_[2]) - (r : ℤ_[2])) ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ h} := by
    rw [Ideal.mem_span_singleton]
    have := (PadicInt.pow_p_dvd_int_iff (p := 2) h ((k : ℤ) - (r : ℤ))).mpr hdvd_k
    simpa using this
  have hsub : (((k : ℤ_[2]).appr h : ℤ) - (r : ℤ) : ℤ_[2]) ∈
      Ideal.span {((2 : ℕ) : ℤ_[2]) ^ h} := by
    have heq : (((k : ℤ_[2]).appr h : ℤ) - (r : ℤ) : ℤ_[2]) =
        ((k : ℤ_[2]) - (r : ℤ_[2])) - ((k : ℤ_[2]) - ((k : ℤ_[2]).appr h : ℤ_[2])) := by
      push_cast; ring
    rw [heq]; exact Ideal.sub_mem _ h2 h1
  rw [Ideal.mem_span_singleton] at hsub
  have hdvd : (((2 : ℕ) : ℤ) ^ h) ∣ (((k : ℤ_[2]).appr h : ℤ) - (r : ℤ)) := by
    rw [← PadicInt.pow_p_dvd_int_iff (p := 2) h]
    simpa using hsub
  have hlt1 : ((k : ℤ_[2]).appr h : ℤ) < ((2 : ℕ) : ℤ) ^ h := by exact_mod_cast PadicInt.appr_lt _ h
  have hlt2 : (r : ℤ) < ((2 : ℕ) : ℤ) ^ h := by
    exact_mod_cast Nat.mod_lt k (by positivity : 0 < 2 ^ h)
  rcases hdvd with ⟨q, hq⟩
  have hq0 : q = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : q ≤ -1 := by omega
      nlinarith
    · have : 1 ≤ q := by omega
      nlinarith
  have heqz : ((k : ℤ_[2]).appr h : ℤ) = (r : ℤ) := by nlinarith
  exact_mod_cast heqz

private lemma padic2_appr_mod_eq (x : ℤ_[2]) {m n : ℕ} (hmn : m ≤ n) :
    (x.appr n) % 2 ^ m = x.appr m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ^ m ∣ x.appr n - x.appr m := PadicInt.dvd_appr_sub_appr x m n hmn
  have hmono : x.appr m ≤ x.appr n := PadicInt.appr_mono x hmn
  have hlt : x.appr m < 2 ^ m := PadicInt.appr_lt x m
  rcases hdvd with ⟨q, hq⟩
  have heq : x.appr n = 2 ^ m * q + x.appr m := by omega
  rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

lemma KCal_isClosed (r : ℕ) : IsClosed (KCal r) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx h
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx ((2 : ℝ) ^ (-(h : ℤ))) (by positivity)
  rw [dist_eq_norm] at hxy
  have happr : x.appr h = y.appr h := (padic2_norm_le_iff_appr_eq x y h).mp hxy.le
  rw [happr]
  exact hy h

private lemma padic2_norm_30 : ‖(30 : ℤ_[2])‖ = (1 / 2 : ℝ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h30 : (30 : ℤ_[2]) = (2 : ℤ_[2]) * (15 : ℤ_[2]) := by norm_num
  have h2 : ‖((2 : ℕ) : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by simpa using (PadicInt.norm_p (p := 2))
  have h15 : ‖((15 : ℕ) : ℤ_[2])‖ = 1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr (by decide : Nat.Coprime 2 15)
  rw [h30, norm_mul]
  norm_num at h2 h15 ⊢
  rw [h2, h15]; norm_num

private lemma affine30_dist (r : ℕ) (x y : ℤ_[2]) :
    dist (affine30 r x) (affine30 r y) = (1 / 2 : ℝ) * dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  have hsub : affine30 r x - affine30 r y = (30 : ℤ_[2]) * (x - y) := by unfold affine30; ring
  rw [hsub, norm_mul, padic2_norm_30]

private lemma affine30_inj (r : ℕ) : Function.Injective (affine30 r) := by
  intro x y h
  have hd : dist (affine30 r x) (affine30 r y) = 0 := by rw [h, dist_self]
  rw [affine30_dist] at hd
  exact dist_eq_zero.mp (by linarith)

private lemma affine30_lipschitz (r : ℕ) : LipschitzWith (2⁻¹ : ℝ≥0) (affine30 r) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [affine30_dist]
  norm_num

private lemma affine30_antilipschitz (r : ℕ) : AntilipschitzWith (2 : ℝ≥0) (affine30 r) := by
  rw [antilipschitzWith_iff_le_mul_dist]
  intro x y
  rw [affine30_dist]
  norm_num
  linarith

private lemma InS30_of_mem_1_15_17 {r : ℕ} (hr : r = 1 ∨ r = 15 ∨ r = 17) : InS30 r := by
  unfold InS30; rcases hr with rfl | rfl | rfl <;> omega

/-- Every surviving `2`-adic cylinder `k₀ + 2^h ℤ_[2]` around `x ∈ 𝒦_r` contains arbitrarily
    large `k ∈ K_r` (reaching `1`) and an exit cylinder leaving `{1, 15, 17} mod 30` at `19` or `23`. -/
private lemma KCal_cylinder_witnesses {r : ℕ} (hr : r = 1 ∨ r = 15 ∨ r = 17)
    {x : ℤ_[2]} (hx : x ∈ KCal r) (h M : ℕ) :
    (∃ k : ℕ, M ≤ k ∧ k ∈ KrSet r ∧ ‖x - (k : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(h : ℤ))) ∧
    (∃ d ≤ 3, ∃ k_exit : ℕ,
      ‖x - (k_exit : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(h : ℤ)) ∧
      (∀ j : ℕ, ExitsAt19Or23 (30 * (2 ^ (h + d) * j + k_exit) + r) ∧
        ‖x - ((2 ^ (h + d) * j + k_exit : ℕ) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(h : ℤ))) ∧
      (k_exit : ℤ_[2]) ∉ KCal r) := by
  set k₀ := x.appr h
  have hk₀_lt : k₀ < 2 ^ h := PadicInt.appr_lt x h
  have hsurv : Survives r h k₀ := hx h
  have hS_b : InS30 (T^[h] (30 * k₀ + r)) :=
    (survives_iff_InS30 (InS30_of_mem_1_15_17 hr) h k₀).mp hsurv
  set D := prodOddMult h (30 * k₀ + r)
  set b := T^[h] (30 * k₀ + r)
  have hD_odd : D % 2 = 1 := prodOddMult_odd h (30 * k₀ + r)
  have haff : ∀ k' : ℕ, T^[h] (30 * (2 ^ h * k' + k₀) + r) = 30 * D * k' + b := by
    intro k'
    have := T_iter_affine h h k₀ k' r le_rfl
    simpa [Nat.sub_self, pow_zero, mul_one, D, b] using this
  constructor
  · -- Part A: arbitrarily large k ∈ KrSet r with k % 2^h = k₀
    obtain ⟨d, _, c, _, D', b', hD', hb', hroute⟩ := route_S30_to_one hD_odd hS_b
    obtain ⟨k'', hk''_ge, hk''_reach⟩ :=
      commutator_hit_prog (u := 1) (D' := D') (b := b') (M := 30 * D' * M + b')
        (by decide) (by decide) hD' (by omega)
    have hk''_M : M ≤ k'' := by
      have hD'pos : 1 ≤ 30 * D' := by omega
      nlinarith
    set k := 2 ^ h * (2 ^ d * k'' + c) + k₀
    refine ⟨k, ?_, ?_, ?_⟩
    · have h2hd : 1 ≤ 2 ^ h * 2 ^ d := Nat.mul_pos (by positivity) (by positivity)
      have : k = (2 ^ h * 2 ^ d) * k'' + (2 ^ h * c + k₀) := by dsimp [k]; ring
      nlinarith
    · refine ⟨by rcases hr with rfl | rfl | rfl <;> omega, ?_⟩
      have hTd : T^[d + h] (30 * k + r) = 30 * D' * k'' + b' := by
        rw [Function.iterate_add_apply, haff, hroute]
      obtain ⟨m, hm⟩ := T_iter_is_f_iter (d + h) (30 * k + r)
      exact reaches_trans ⟨m, hm.symm.trans hTd⟩ hk''_reach
    · rw [padic2_norm_le_iff_appr_eq, padic2_appr_natCast]
      dsimp [k]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hk₀_lt]
  · -- Part B: exit sub-ball of depth h + d (d ≤ 3)
    obtain ⟨d, hd3, c, _, hexit⟩ := route_S30_to_exit hD_odd hS_b
    set k_exit := 2 ^ h * c + k₀
    have hk_mod_h : ∀ j : ℕ, (2 ^ (h + d) * j + k_exit) % 2 ^ h = k₀ := by
      intro j
      have hrew : 2 ^ (h + d) * j + k_exit = 2 ^ h * (2 ^ d * j + c) + k₀ := by
        dsimp [k_exit]; rw [pow_add]; ring
      rw [hrew, Nat.mul_add_mod, Nat.mod_eq_of_lt hk₀_lt]
    refine ⟨d, hd3, k_exit, ?_, fun j => ⟨?_, ?_⟩, ?_⟩
    · rw [padic2_norm_le_iff_appr_eq, padic2_appr_natCast]
      have := hk_mod_h 0
      simpa using this.symm
    · have hInABC : InABC (30 * (2 ^ (h + d) * j + k_exit) + r) := by
        unfold InABC InA InB InC; rcases hr with rfl | rfl | rfl <;> omega
      have hbad : T^[h + d] (30 * (2 ^ (h + d) * j + k_exit) + r) % 30 = 19 ∨
          T^[h + d] (30 * (2 ^ (h + d) * j + k_exit) + r) % 30 = 23 := by
        have hrew : 2 ^ (h + d) * j + k_exit = 2 ^ h * (2 ^ d * j + c) + k₀ := by
          dsimp [k_exit]; rw [pow_add]; ring
        rw [hrew, add_comm h d, Function.iterate_add_apply, haff]
        exact (hexit j).2
      have hhd_pos : 1 ≤ h + d := by
        by_contra h0
        have hz : h + d = 0 := by omega
        rw [hz, Function.iterate_zero_apply] at hbad
        unfold InABC InA InB InC at hInABC; omega
      refine ⟨hInABC, h + d, hhd_pos, fun i hi => ?_, hbad⟩
      · by_cases hih : i ≤ h
        · have hm := T_iter_mod30_eq (h := h) (k₁ := 2 ^ (h + d) * j + k_exit) (k₂ := k₀) (r := r)
            hih (by rw [hk_mod_h j, Nat.mod_eq_of_lt hk₀_lt])
          have hA := hsurv i hih
          unfold AllowedMod30 InABC InA InB InC at hA ⊢
          omega
        · have hrew : 2 ^ (h + d) * j + k_exit = 2 ^ h * (2 ^ d * j + c) + k₀ := by
            dsimp [k_exit]; rw [pow_add]; ring
          have hisplit : i = (i - h) + h := by omega
          rw [hisplit, Function.iterate_add_apply, hrew, haff]
          exact (hexit j).1 (i - h) (by omega)
    · rw [padic2_norm_le_iff_appr_eq, padic2_appr_natCast, hk_mod_h j]
    · intro hmem
      have hsurv_ex := hmem (h + d)
      rw [padic2_appr_natCast] at hsurv_ex
      have hsurv_k : Survives r (h + d) k_exit :=
        (survives_mod_pow (Nat.mod_mod k_exit (2 ^ (h + d)))).mp hsurv_ex
      have hA := hsurv_k (h + d) le_rfl
      have hrew : k_exit = 2 ^ h * (2 ^ d * 0 + c) + k₀ := by dsimp [k_exit]; ring
      have hbad : T^[h + d] (30 * k_exit + r) % 30 = 19 ∨ T^[h + d] (30 * k_exit + r) % 30 = 23 := by
        rw [add_comm h d, Function.iterate_add_apply, hrew, haff]
        exact (hexit 0).2
      unfold AllowedMod30 InABC InA InB InC at hA
      omega

/-- Theorem `thm:cantor` (Part 1a): for `r ∈ {1, 15, 17}`, `closure K_r = 𝒦_r` in `ℤ_[2]`. -/
theorem closure_KrPadic_eq {r : ℕ} (hr : r = 1 ∨ r = 15 ∨ r = 17) :
    closure (KrPadic r) = KCal r := by
  apply Set.Subset.antisymm
  · refine closure_minimal ?_ (KCal_isClosed r)
    rintro _ ⟨k, hk, rfl⟩ h
    rw [padic2_appr_natCast]
    exact (survives_mod_pow (Nat.mod_mod k (2 ^ h))).mpr
      ((survives_iff_InS30 (InS30_of_mem_1_15_17 hr) h k).mpr
        (InS30_T_iter_of_reaches_one hk.2 h))
  · intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨h, hh⟩ := PadicInt.exists_pow_neg_lt 2 hε
    obtain ⟨k, _, hk, hdist⟩ := (KCal_cylinder_witnesses hr hx h 0).1
    refine ⟨(k : ℤ_[2]), ⟨k, hk, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hdist (by simpa using hh)

/-- Theorem `thm:cantor` (Part 1b): exact `2`-adic closure of the odd basin `B_1` in `ℤ_[2]`. -/
theorem closure_B1Padic_eq :
    closure B1Padic =
      affine30 1 '' KCal 1 ∪ affine30 15 '' KCal 15 ∪ affine30 17 '' KCal 17 := by
  have hB1_eq : B1Padic =
      affine30 1 '' KrPadic 1 ∪ affine30 15 '' KrPadic 15 ∪ affine30 17 '' KrPadic 17 := by
    ext x
    simp only [B1Padic, KrPadic, KrSet, Set.mem_union, Set.mem_image]
    constructor
    · rintro ⟨n, ⟨hn_odd, hn_r⟩, rfl⟩
      have hABC := thm_residue_law hn_odd hn_r
      rcases hABC with hA | hB | hC
      · left; left
        refine ⟨((n / 30 : ℕ) : ℤ_[2]), ⟨n / 30, ?_, rfl⟩, ?_⟩
        · have heq : 30 * (n / 30) + 1 = n := by unfold InA at hA; omega
          change 30 * (n / 30) + 1 ∈ B1Set; rw [heq]; exact ⟨hn_odd, hn_r⟩
        · unfold affine30
          have heq : 30 * (n / 30) + 1 = n := by unfold InA at hA; omega
          exact_mod_cast heq
      · left; right
        refine ⟨((n / 30 : ℕ) : ℤ_[2]), ⟨n / 30, ?_, rfl⟩, ?_⟩
        · have heq : 30 * (n / 30) + 15 = n := by unfold InB at hB; omega
          change 30 * (n / 30) + 15 ∈ B1Set; rw [heq]; exact ⟨hn_odd, hn_r⟩
        · unfold affine30
          have heq : 30 * (n / 30) + 15 = n := by unfold InB at hB; omega
          exact_mod_cast heq
      · right
        refine ⟨((n / 30 : ℕ) : ℤ_[2]), ⟨n / 30, ?_, rfl⟩, ?_⟩
        · have heq : 30 * (n / 30) + 17 = n := by unfold InC at hC; omega
          change 30 * (n / 30) + 17 ∈ B1Set; rw [heq]; exact ⟨hn_odd, hn_r⟩
        · unfold affine30
          have heq : 30 * (n / 30) + 17 = n := by unfold InC at hC; omega
          exact_mod_cast heq
    · rintro ((⟨_, ⟨k, hk, rfl⟩, rfl⟩ | ⟨_, ⟨k, hk, rfl⟩, rfl⟩) | ⟨_, ⟨k, hk, rfl⟩, rfl⟩)
      · exact ⟨30 * k + 1, hk, by unfold affine30; push_cast; rfl⟩
      · exact ⟨30 * k + 15, hk, by unfold affine30; push_cast; rfl⟩
      · exact ⟨30 * k + 17, hk, by unfold affine30; push_cast; rfl⟩
  have hcl_aff : ∀ r : ℕ, r = 1 ∨ r = 15 ∨ r = 17 →
      closure (affine30 r '' KrPadic r) = affine30 r '' KCal r := by
    intro r hr
    have hcont : Continuous (affine30 r) := (affine30_lipschitz r).continuous
    have hclosed : IsClosed (affine30 r '' KCal r) :=
      ((KCal_isClosed r).isCompact.image hcont).isClosed
    apply Set.Subset.antisymm
    · exact closure_minimal (Set.image_mono (by rw [← closure_KrPadic_eq hr]; exact subset_closure))
        hclosed
    · rw [← closure_KrPadic_eq hr]
      exact image_closure_subset_closure_image hcont
  rw [hB1_eq, closure_union, closure_union, hcl_aff 1 (Or.inl rfl),
      hcl_aff 15 (Or.inr (Or.inl rfl)), hcl_aff 17 (Or.inr (Or.inr rfl))]

/-- Theorem `thm:cantor` (Part 1c): every nonempty `2`-adic ball meeting `closure B_1` contains
    infinitely many positive integers reaching `1` and infinitely many starting in `{1, 15, 17} mod 30`
    and exiting `{1, 15, 17} mod 30` at `19` or `23 mod 30`. -/
theorem ball_meeting_closure_B1Padic {x : ℤ_[2]} {ρ : ℝ}
    (hmeet : (Metric.ball x ρ ∩ closure B1Padic).Nonempty) :
    {n : ℕ | 1 ≤ n ∧ Reaches f n 1 ∧ (n : ℤ_[2]) ∈ Metric.ball x ρ}.Infinite ∧
    {n : ℕ | 1 ≤ n ∧ InABC n ∧ ExitsAt19Or23 n ∧ (n : ℤ_[2]) ∈ Metric.ball x ρ}.Infinite := by
  obtain ⟨y, hy_ball, hy_cl⟩ := hmeet
  rw [Metric.mem_ball, dist_eq_norm] at hy_ball
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hy_ball
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hh⟩ := PadicInt.exists_pow_neg_lt 2 hρ
  have h2h : (2 : ℝ) ^ (-(h : ℤ)) < ρ := by simpa using hh
  rw [closure_B1Padic_eq] at hy_cl
  have hsheet : ∃ r : ℕ, (r = 1 ∨ r = 15 ∨ r = 17) ∧ ∃ k ∈ KCal r, y = affine30 r k := by
    rcases hy_cl with (⟨k, hk, hy⟩ | ⟨k, hk, hy⟩) | ⟨k, hk, hy⟩
    · exact ⟨1, Or.inl rfl, k, hk, hy.symm⟩
    · exact ⟨15, Or.inr (Or.inl rfl), k, hk, hy.symm⟩
    · exact ⟨17, Or.inr (Or.inr rfl), k, hk, hy.symm⟩
  obtain ⟨r, hr, k, hk_cal, hy_eq⟩ := hsheet
  have hball_of_k : ∀ k' : ℕ, ‖k - (k' : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(h : ℤ)) →
      ((30 * k' + r : ℕ) : ℤ_[2]) ∈ Metric.ball x ρ := by
    intro k' hk'
    rw [Metric.mem_ball, dist_eq_norm]
    have hcast : ((30 * k' + r : ℕ) : ℤ_[2]) = affine30 r (k' : ℤ_[2]) := by
      unfold affine30; push_cast; rfl
    rw [hcast]
    have hsub : affine30 r (k' : ℤ_[2]) - x = (affine30 r (k' : ℤ_[2]) - y) + (y - x) := by ring
    rw [hsub]
    have h1 : ‖affine30 r (k' : ℤ_[2]) - y‖ ≤ (2 : ℝ) ^ (-(h : ℤ)) := by
      rw [hy_eq, ← dist_eq_norm, affine30_dist, dist_eq_norm, norm_sub_rev]
      have : 0 ≤ ‖k - (k' : ℤ_[2])‖ := norm_nonneg _
      linarith
    calc ‖(affine30 r (k' : ℤ_[2]) - y) + (y - x)‖
        ≤ max ‖affine30 r (k' : ℤ_[2]) - y‖ ‖y - x‖ := PadicInt.nonarchimedean _ _
      _ < ρ := max_lt (lt_of_le_of_lt h1 h2h) hy_ball
  constructor
  · rw [Set.infinite_iff_exists_gt]
    intro M
    obtain ⟨k', hk'_ge, hk'_in, hk'_dist⟩ := (KCal_cylinder_witnesses hr hk_cal h (M + 1)).1
    refine ⟨30 * k' + r, ⟨?_, hk'_in.2, hball_of_k k' hk'_dist⟩, ?_⟩
    · rcases hr with rfl | rfl | rfl <;> omega
    · omega
  · obtain ⟨d, _, k_exit, _, hj_spec, _⟩ := (KCal_cylinder_witnesses hr hk_cal h 0).2
    rw [Set.infinite_iff_exists_gt]
    intro M
    set k' := 2 ^ (h + d) * (M + 1) + k_exit
    refine ⟨30 * k' + r, ⟨?_, (hj_spec (M + 1)).1.1, (hj_spec (M + 1)).1, hball_of_k k' (hj_spec (M + 1)).2⟩, ?_⟩
    · rcases hr with rfl | rfl | rfl <;> omega
    · have h2pos : 1 ≤ 2 ^ (h + d) := Nat.one_le_pow _ _ (by norm_num)
      dsimp [k']; nlinarith

/-- Theorem `thm:cantor` (Part 1d): `closure B_1` is nowhere dense in `ℤ_[2]`. -/
theorem isNowhereDense_closure_B1Padic : IsNowhereDense (closure B1Padic) := by
  have hsheet_nd : ∀ r : ℕ, (r = 1 ∨ r = 15 ∨ r = 17) → IsNowhereDense (affine30 r '' KCal r) := by
    intro r hr
    have hclosed : IsClosed (affine30 r '' KCal r) :=
      ((KCal_isClosed r).isCompact.image (affine30_lipschitz r).continuous).isClosed
    rw [IsNowhereDense, hclosed.closure_eq]
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx
    obtain ⟨ρ, hρ, hsub⟩ := hx
    have hx_mem : x ∈ affine30 r '' KCal r := hsub (Metric.mem_ball_self hρ)
    obtain ⟨k, hk_cal, rfl⟩ := hx_mem
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨h, hh⟩ := PadicInt.exists_pow_neg_lt 2 hρ
    obtain ⟨_, _, k_exit, hk_dist, _, hk_not⟩ := (KCal_cylinder_witnesses hr hk_cal h 0).2
    have hball : affine30 r (k_exit : ℤ_[2]) ∈ Metric.ball (affine30 r k) ρ := by
      rw [Metric.mem_ball, affine30_dist, dist_eq_norm, norm_sub_rev]
      have h2h : (2 : ℝ) ^ (-(h : ℤ)) < ρ := by simpa using hh
      have : 0 ≤ ‖k - (k_exit : ℤ_[2])‖ := norm_nonneg _
      linarith
    obtain ⟨k', hk'_cal, heq⟩ := hsub hball
    have hk_eq : k' = (k_exit : ℤ_[2]) := affine30_inj r heq
    exact hk_not (hk_eq ▸ hk'_cal)
  rw [closure_B1Padic_eq]
  exact ((hsheet_nd 1 (Or.inl rfl)).union (hsheet_nd 15 (Or.inr (Or.inl rfl)))).union
    (hsheet_nd 17 (Or.inr (Or.inr rfl)))

/-! ## Part 3: Ultrametric bit space `{0, 1}^ℕ`, isometry `Ψ_r`, Hausdorff measure, `dimH`, `dimB` -/

/-- Binary sequences `{0, 1}^ℕ` equipped with the ultrametric `d(x, y) = 2^{-inf{j : x_j ≠ y_j}}`. -/
@[ext]
structure BitSeq where
  bit : ℕ → Bool

lemma bitSeq_exists_ne {x y : BitSeq} (h : x ≠ y) : ∃ j : ℕ, x.bit j ≠ y.bit j := by
  by_contra hall
  push Not at hall
  exact h (BitSeq.ext (funext hall))

/-- Least index where two distinct `BitSeq` elements differ. -/
noncomputable def firstDiff {x y : BitSeq} (h : x ≠ y) : ℕ := by
  classical exact Nat.find (bitSeq_exists_ne h)

private lemma firstDiff_spec {x y : BitSeq} (h : x ≠ y) :
    x.bit (firstDiff h) ≠ y.bit (firstDiff h) := by
  classical exact Nat.find_spec (bitSeq_exists_ne h)

private lemma firstDiff_min {x y : BitSeq} (h : x ≠ y) {j : ℕ} (hj : j < firstDiff h) :
    x.bit j = y.bit j := by
  classical
  by_contra hne
  exact Nat.find_min (bitSeq_exists_ne h) hj hne

private lemma firstDiff_eq_of {x y : BitSeq} (h : x ≠ y) (m : ℕ)
    (hlt : ∀ j < m, x.bit j = y.bit j) (hne : x.bit m ≠ y.bit m) : firstDiff h = m := by
  apply le_antisymm
  · classical exact Nat.find_min' (bitSeq_exists_ne h) hne
  · by_contra hgt; push Not at hgt
    exact firstDiff_spec h (hlt _ hgt)

private lemma firstDiff_comm {x y : BitSeq} (h : x ≠ y) : firstDiff h = firstDiff h.symm :=
  firstDiff_eq_of h (firstDiff h.symm)
    (fun _ hj => (firstDiff_min h.symm hj).symm) (Ne.symm (firstDiff_spec h.symm))

/-- Ultrametric distance `d(x, y) = 2^{-inf{j : x_j ≠ y_j}}` on `{0, 1}^ℕ`. -/
noncomputable def bitSeqDist (x y : BitSeq) : ℝ := by
  classical exact if h : x = y then 0 else (2 : ℝ) ^ (-(firstDiff h : ℤ))

lemma bitSeqDist_self (x : BitSeq) : bitSeqDist x x = 0 := by
  classical simp [bitSeqDist]

private lemma bitSeqDist_of_ne {x y : BitSeq} (h : x ≠ y) :
    bitSeqDist x y = (2 : ℝ) ^ (-(firstDiff h : ℤ)) := by
  classical simp [bitSeqDist, h]

private lemma bitSeqDist_nonneg (x y : BitSeq) : 0 ≤ bitSeqDist x y := by
  by_cases h : x = y
  · subst h; rw [bitSeqDist_self]
  · rw [bitSeqDist_of_ne h]; positivity

noncomputable instance : MetricSpace BitSeq where
  dist := bitSeqDist
  dist_self := bitSeqDist_self
  dist_comm x y := by
    by_cases h : x = y
    · subst h; simp [bitSeqDist_self]
    · rw [bitSeqDist_of_ne h, bitSeqDist_of_ne (Ne.symm h), firstDiff_comm h]
  dist_triangle x y z := by
    by_cases hxz : x = z
    · subst hxz; rw [bitSeqDist_self]
      linarith [bitSeqDist_nonneg x y, bitSeqDist_nonneg y x]
    · by_cases hxy : x = y
      · subst hxy; rw [bitSeqDist_self, zero_add]
      · by_cases hyz : y = z
        · subst hyz; rw [bitSeqDist_self, add_zero]
        · rw [bitSeqDist_of_ne hxz, bitSeqDist_of_ne hxy, bitSeqDist_of_ne hyz]
          have hmin : min (firstDiff hxy) (firstDiff hyz) ≤ firstDiff hxz := by
            by_contra hlt; push Not at hlt
            have h1 := firstDiff_min hxy (lt_of_lt_of_le hlt (min_le_left _ _))
            have h2 := firstDiff_min hyz (lt_of_lt_of_le hlt (min_le_right _ _))
            exact firstDiff_spec hxz (h1.trans h2)
          have hle_max : (2 : ℝ) ^ (-(firstDiff hxz : ℤ)) ≤
              max ((2 : ℝ) ^ (-(firstDiff hxy : ℤ))) ((2 : ℝ) ^ (-(firstDiff hyz : ℤ))) := by
            rcases le_total (firstDiff hxy) (firstDiff hyz) with h12 | h21
            · rw [min_eq_left h12] at hmin
              exact le_trans (zpow_le_zpow_right₀ (by norm_num) (by omega)) (le_max_left _ _)
            · rw [min_eq_right h21] at hmin
              exact le_trans (zpow_le_zpow_right₀ (by norm_num) (by omega)) (le_max_right _ _)
          have hp1 : 0 ≤ (2 : ℝ) ^ (-(firstDiff hxy : ℤ)) := by positivity
          have hp2 : 0 ≤ (2 : ℝ) ^ (-(firstDiff hyz : ℤ)) := by positivity
          linarith [max_le_add_of_nonneg hp1 hp2]
  eq_of_dist_eq_zero := by
    intro x y h
    by_contra hne
    rw [bitSeqDist_of_ne hne] at h
    have : (0 : ℝ) < (2 : ℝ) ^ (-(firstDiff hne : ℤ)) := by positivity
    linarith

lemma bitSeq_dist_of_ne {x y : BitSeq} (h : x ≠ y) :
    dist x y = (2 : ℝ) ^ (-(firstDiff h : ℤ)) :=
  bitSeqDist_of_ne h

private lemma bitSeq_dist_le_of_eq {x y : BitSeq} (m : ℕ) (h : ∀ j < m, x.bit j = y.bit j) :
    dist x y ≤ (2 : ℝ) ^ (-(m : ℤ)) := by
  by_cases heq : x = y
  · subst heq; rw [dist_self]; positivity
  · rw [bitSeq_dist_of_ne heq]
    have hm : m ≤ firstDiff heq := by
      by_contra hlt; push Not at hlt
      exact firstDiff_spec heq (h _ hlt)
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)

private lemma bitSeq_eq_of_dist_lt {x y : BitSeq} {m : ℕ} (h : dist x y < (2 : ℝ) ^ (-(m : ℤ))) :
    ∀ j ≤ m, x.bit j = y.bit j := by
  intro j hj
  by_cases heq : x = y
  · rw [heq]
  · rw [bitSeq_dist_of_ne heq] at h
    have hlt : m < firstDiff heq := by
      by_contra hge; push Not at hge
      have : (2 : ℝ) ^ (-(m : ℤ)) ≤ (2 : ℝ) ^ (-(firstDiff heq : ℤ)) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      linarith
    exact firstDiff_min heq (lt_of_le_of_lt hj hlt)

instance : CompactSpace BitSeq := by
  let e : BitSeq ≃ (ℕ → Bool) :=
    { toFun := fun x => x.bit
      invFun := fun f => ⟨f⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcont1 : Continuous e := by
    rw [continuous_pi_iff]
    intro j
    rw [continuous_discrete_rng]
    intro b
    rw [Metric.isOpen_iff]
    intro x hx
    refine ⟨(2 : ℝ) ^ (-(j : ℤ)), by positivity, fun y hy => ?_⟩
    rw [Metric.mem_ball] at hy
    have heq := bitSeq_eq_of_dist_lt hy j le_rfl
    change y.bit j = b
    rw [heq]; exact hx
  have hcont2 : Continuous e.symm := by
    rw [continuous_iff_continuousAt]
    intro f
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (2 : ℝ) ^ (-(N : ℤ)) < ε := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt 2 hε
      exact ⟨N, by simpa using hN⟩
    have hopen : IsOpen {g : ℕ → Bool | ∀ i : Fin N, g i.val = f i.val} := by
      have : {g : ℕ → Bool | ∀ i : Fin N, g i.val = f i.val} =
          ⋂ i : Fin N, (fun g : ℕ → Bool => g i.val) ⁻¹' {f i.val} := by ext g; simp
      rw [this]
      exact isOpen_iInter_of_finite fun i =>
        (isOpen_discrete {f i.val}).preimage (continuous_apply i.val)
    rw [Filter.Eventually, mem_nhds_iff]
    refine ⟨{g : ℕ → Bool | ∀ i : Fin N, g i.val = f i.val}, ?_, hopen, fun _ => rfl⟩
    intro g hg
    exact lt_of_le_of_lt (bitSeq_dist_le_of_eq N fun j hj => hg ⟨j, hj⟩) hN
  let h : BitSeq ≃ₜ (ℕ → Bool) := ⟨e, hcont1, hcont2⟩
  exact h.symm.compactSpace

noncomputable instance : MeasurableSpace BitSeq := borel BitSeq
instance : BorelSpace BitSeq := ⟨rfl⟩

/-- Prefix cylinder `C_w = {x ∈ {0, 1}^ℕ : x|_len(w) = w}`. -/
def cylSet (w : List Bool) : Set BitSeq :=
  {x : BitSeq | ∀ i : Fin w.length, x.bit i.val = w[i.val]}

private lemma cylSet_isOpen (w : List Bool) : IsOpen (cylSet w) := by
  rw [Metric.isOpen_iff]
  intro x hx
  refine ⟨(2 : ℝ) ^ (-(w.length : ℤ)), by positivity, fun y hy i => ?_⟩
  rw [Metric.mem_ball] at hy
  rw [bitSeq_eq_of_dist_lt hy i.val (le_of_lt i.isLt)]
  exact hx i

private lemma cylSet_ediam_le (w : List Bool) :
    Metric.ediam (cylSet w) ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(w.length : ℤ))) := by
  rw [Metric.ediam_le_iff]
  intro x hx y hy
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (bitSeq_dist_le_of_eq w.length fun j hj => by
    rw [hx ⟨j, hj⟩, hy ⟨j, hj⟩])

/-- Every subset `U ⊆ BitSeq` of positive diameter has exact diameter `2^{-h}` and sits inside
    a single length-`h` cylinder `C_w`. -/
private lemma bitSeq_subset_cyl_of_ediam_pos {U : Set BitSeq} (hpos : 0 < Metric.ediam U) :
    ∃ (w : List Bool), U ⊆ cylSet w ∧ Metric.ediam U = ENNReal.ofReal ((2 : ℝ) ^ (-(w.length : ℤ))) := by
  classical
  have hex : ∃ j : ℕ, ∃ x ∈ U, ∃ y ∈ U, x.bit j ≠ y.bit j := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Metric.ediam_pos_iff.mp hpos
    have hne : x ≠ y := fun h => by subst h; simp at hxy
    exact ⟨firstDiff hne, x, hx, y, hy, firstDiff_spec hne⟩
  set h := Nat.find hex
  obtain ⟨x₀, hx₀, y₀, hy₀, hne0⟩ := Nat.find_spec hex
  have hagree : ∀ j < h, ∀ x ∈ U, ∀ y ∈ U, x.bit j = y.bit j := by
    intro j hj x hx y hy
    by_contra hne
    exact Nat.find_min hex hj ⟨x, hx, y, hy, hne⟩
  let w : List Bool := List.ofFn (fun i : Fin h => x₀.bit i.val)
  have hw_len : w.length = h := by simp [w]
  refine ⟨w, ?_, ?_⟩
  · intro x hx i
    have hi : i.val < h := by simpa [hw_len] using i.isLt
    have hget : w[i.val] = x₀.bit i.val := by simp [w]
    rw [hget]
    exact hagree i.val hi x hx x₀ hx₀
  · apply le_antisymm
    · exact (Metric.ediam_mono (s := U) (t := cylSet w) fun x hx i => by
        have hi : i.val < h := by simpa [hw_len] using i.isLt
        have hget : w[i.val] = x₀.bit i.val := by simp [w]
        rw [hget]; exact hagree i.val hi x hx x₀ hx₀).trans (cylSet_ediam_le w)
    · rw [hw_len]
      have hne_xy : x₀ ≠ y₀ := fun heq => hne0 (by rw [heq])
      have hfd : firstDiff hne_xy = h :=
        firstDiff_eq_of hne_xy h (fun j hj => hagree j hj x₀ hx₀ y₀ hy₀) hne0
      have hd : edist x₀ y₀ = ENNReal.ofReal ((2 : ℝ) ^ (-(h : ℤ))) := by
        rw [edist_dist, bitSeq_dist_of_ne hne_xy, hfd]
      rw [← hd]
      exact Metric.edist_le_ediam_of_mem hx₀ hy₀

/-- The prefix-code Cantor set `Σ = {0, 1000, 1001}^ω ⊂ {0, 1}^ℕ`. -/
def SigmaSet : Set BitSeq :=
  {x : BitSeq | ∃ pos : ℕ → ℕ, pos 0 = 0 ∧ ∀ i : ℕ,
    (pos (i + 1) = pos i + 1 ∧ x.bit (pos i) = false) ∨
    (pos (i + 1) = pos i + 4 ∧ x.bit (pos i) = true ∧
      x.bit (pos i + 1) = false ∧ x.bit (pos i + 2) = false)}

/-- Prepend a finite bit prefix to a `BitSeq`. -/
def prependBits (p : List Bool) (x : BitSeq) : BitSeq :=
  ⟨fun j => if h : j < p.length then p[j] else x.bit (j - p.length)⟩

/-- Target Cantor set `000 Σ ⊔ 001 Σ` for `r = 15`. -/
def Sigma15Set : Set BitSeq :=
  (prependBits [false, false, false] '' SigmaSet) ∪
  (prependBits [false, false, true] '' SigmaSet)

lemma sigma15_disjoint :
    Disjoint (prependBits [false, false, false] '' SigmaSet)
             (prependBits [false, false, true] '' SigmaSet) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, _, rfl⟩ ⟨y, _, heq⟩
  have h2 := congr_arg (fun z : BitSeq => z.bit 2) heq
  simp [prependBits] at h2

private lemma prependBits_dist (p : List Bool) (x y : BitSeq) :
    dist (prependBits p x) (prependBits p y) = (2 : ℝ) ^ (-(p.length : ℤ)) * dist x y := by
  by_cases hxy : x = y
  · subst hxy; simp
  · have hne : prependBits p x ≠ prependBits p y := by
      intro heq
      apply firstDiff_spec hxy
      have h := congr_arg (fun z : BitSeq => z.bit (p.length + firstDiff hxy)) heq
      simp only [prependBits, show ¬ (p.length + firstDiff hxy < p.length) by omega, ↓reduceDIte,
        Nat.add_sub_cancel_left] at h
      exact h
    have hfd : firstDiff hne = p.length + firstDiff hxy := by
      apply firstDiff_eq_of hne (p.length + firstDiff hxy)
      · intro j hj
        by_cases hjp : j < p.length
        · simp [prependBits, hjp]
        · simp only [prependBits, hjp, ↓reduceDIte]
          exact firstDiff_min hxy (by omega)
      · simp only [prependBits, show ¬ (p.length + firstDiff hxy < p.length) by omega, ↓reduceDIte,
          Nat.add_sub_cancel_left]
        exact firstDiff_spec hxy
    rw [bitSeq_dist_of_ne hne, bitSeq_dist_of_ne hxy, hfd]
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1; omega

/-! ### Four-state automaton and exact Bernoulli-eigenweight bounds on `Σ` -/

/-- The four collapsed survival states `S_0, S_1, S_2, S_3`. -/
inductive AutoState : Type
  | S0 | S1 | S2 | S3
  deriving DecidableEq

/-- One-bit transition of the 4-state automaton. -/
def autoStep : AutoState → Bool → Option AutoState
  | .S0, false => some .S0
  | .S0, true  => some .S1
  | .S1, false => some .S2
  | .S1, true  => none
  | .S2, false => some .S3
  | .S2, true  => none
  | .S3, _     => some .S0

/-- Run the 4-state automaton along a finite bit word. -/
def autoRun : AutoState → List Bool → Option AutoState
  | s, [] => some s
  | s, b :: bs => (autoStep s b).bind (fun s' => autoRun s' bs)

private lemma autoRun_append (s : AutoState) (w₁ w₂ : List Bool) :
    autoRun s (w₁ ++ w₂) = (autoRun s w₁).bind (fun s' => autoRun s' w₂) := by
  induction w₁ generalizing s with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.cons_append, autoRun]
    cases autoStep s b with
    | none => rfl
    | some s' => exact ih s'

/-- Map each residue modulo `30` to its collapsed state (`none` outside `S`). -/
def resToAutoState (r : ℕ) : Option AutoState :=
  match r % 30 with
  | 0 | 1 | 2 | 17 => some .S0
  | 15 | 16 => some .S1
  | 8 => some .S2
  | 4 => some .S3
  | _ => none

private lemma resToAutoState_isSome_iff (n : ℕ) :
    (resToAutoState n).isSome ↔ InS30 n := by
  unfold resToAutoState InS30
  have hlt : n % 30 < 30 := Nat.mod_lt n (by omega)
  interval_cases (n % 30) <;> decide

private lemma resToAutoState_step_fin :
    ∀ x : Fin 60,
      resToAutoState (T x.val) =
        (resToAutoState x.val).bind (fun s => autoStep s (decide ((x.val / 30) % 2 = 1))) := by
  decide

private lemma resToAutoState_step (n : ℕ) :
    resToAutoState (T n) =
      (resToAutoState n).bind (fun s => autoStep s (decide ((n / 30) % 2 = 1))) := by
  have hL : resToAutoState (T n) = resToAutoState (T (n % 60)) := by
    unfold resToAutoState; rw [T_mod30_eq_mod60]
  have hR1 : resToAutoState n = resToAutoState (n % 60) := by
    unfold resToAutoState; congr 1; omega
  have hR2 : (n / 30) % 2 = ((n % 60) / 30) % 2 := by omega
  rw [hL, hR1, hR2]
  exact resToAutoState_step_fin ⟨n % 60, Nat.mod_lt n (by omega)⟩

/-- Exact right Perron eigenvector of the 4-state automaton (`φ(S_0)=1, φ(S_1)=2a^3, φ(S_2)=2a^2, φ(S_3)=2a`). -/
noncomputable def autoWeight : AutoState → ℝ
  | .S0 => 1
  | .S1 => 2 * aStar ^ 3
  | .S2 => 2 * aStar ^ 2
  | .S3 => 2 * aStar

private lemma autoWeight_step (s : AutoState) :
    aStar * ((match autoStep s false with | some s' => autoWeight s' | none => 0) +
             (match autoStep s true  with | some s' => autoWeight s' | none => 0)) =
      autoWeight s := by
  cases s <;> simp only [autoStep, autoWeight]
  · linarith [aStar_quartic]
  · ring
  · ring
  · ring

private lemma autoWeight_bounds (s : AutoState) :
    2 * aStar ^ 3 ≤ autoWeight s ∧ autoWeight s ≤ 2 * aStar := by
  obtain ⟨hlo, hhi⟩ := aStar_bounds_tight
  have ha0 := aStar_spec.1
  have ha1 := aStar_spec.2.1
  have h3_le_2 : aStar ^ 3 ≤ aStar ^ 2 := by nlinarith
  have h2_le_1 : 2 * aStar ^ 2 ≤ 1 := by
    have : (647798872 / 1000000000 : ℝ) ^ 2 < 1 / 2 := by norm_num
    nlinarith
  have h1_le_2a : 1 ≤ 2 * aStar := by linarith
  cases s <;> simp only [autoWeight] <;> constructor <;> nlinarith

/-- Bernoulli cylinder weight `w(C_u)` of a finite bit word `u` on `Σ`. -/
noncomputable def sigmaCylWeight (w : List Bool) : ℝ :=
  match autoRun .S0 w with
  | some s => aStar ^ w.length * autoWeight s
  | none => 0

private lemma sigmaCylWeight_nonneg (w : List Bool) : 0 ≤ sigmaCylWeight w := by
  unfold sigmaCylWeight
  cases h : autoRun .S0 w with
  | none => exact le_rfl
  | some s =>
    have ha0 := aStar_spec.1
    have hw := (autoWeight_bounds s).1
    have : 0 ≤ autoWeight s := by linarith [show 0 < 2 * aStar ^ 3 by positivity]
    positivity

private lemma sigmaCylWeight_cons_split (w : List Bool) :
    sigmaCylWeight w = sigmaCylWeight (w ++ [false]) + sigmaCylWeight (w ++ [true]) := by
  unfold sigmaCylWeight
  rw [autoRun_append, autoRun_append]
  cases h : autoRun .S0 w with
  | none => simp
  | some s =>
    simp only [Option.bind_some, autoRun, List.length_append, List.length_singleton, pow_succ]
    have hstep := autoWeight_step s
    have heq0 : (Option.bind (autoStep s false) some) = autoStep s false := by
      cases autoStep s false <;> rfl
    have heq1 : (Option.bind (autoStep s true) some) = autoStep s true := by
      cases autoStep s true <;> rfl
    rw [heq0, heq1, ← hstep]
    cases autoStep s false <;> cases autoStep s true <;> ring

private lemma sigmaCylWeight_le (w : List Bool) :
    sigmaCylWeight w ≤ 2 * aStar * aStar ^ w.length := by
  unfold sigmaCylWeight
  cases h : autoRun .S0 w with
  | none => have := aStar_spec.1; positivity
  | some s =>
    have := (autoWeight_bounds s).2
    have ha0 : 0 ≤ aStar ^ w.length := by have := aStar_spec.1; positivity
    nlinarith

private lemma sigmaCylWeight_ge_of_valid {w : List Bool} (hv : (autoRun .S0 w).isSome) :
    2 * aStar ^ 3 * aStar ^ w.length ≤ sigmaCylWeight w := by
  unfold sigmaCylWeight
  cases h : autoRun .S0 w with
  | none => simp [h] at hv
  | some s =>
    have := (autoWeight_bounds s).1
    have ha0 : 0 ≤ aStar ^ w.length := by have := aStar_spec.1; positivity
    nlinarith

private lemma sum_sigmaCylWeight_ext (w : List Bool) (d : ℕ) :
    ∑ u : Fin d → Bool, sigmaCylWeight (w ++ List.ofFn u) = sigmaCylWeight w := by
  induction d generalizing w with
  | zero =>
    simp [Finset.univ_unique]
  | succ d ih =>
    have hsplit : ∑ u : Fin (d + 1) → Bool, sigmaCylWeight (w ++ List.ofFn u) =
        ∑ b : Bool, ∑ u' : Fin d → Bool, sigmaCylWeight ((w ++ [b]) ++ List.ofFn u') := by
      let e : (Fin (d + 1) → Bool) ≃ Bool × (Fin d → Bool) :=
        { toFun := fun u => (u 0, fun i => u i.succ)
          invFun := fun p => Fin.cons p.1 p.2
          left_inv := fun u => by ext i; refine Fin.cases ?_ ?_ i <;> simp
          right_inv := fun ⟨b, u'⟩ => by ext <;> simp }
      rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun u' _ => ?_
      congr 1
      simp [e, List.ofFn_succ, List.append_assoc]
    rw [hsplit]
    simp_rw [ih]
    rw [Fintype.sum_bool, add_comm, ← sigmaCylWeight_cons_split]

private lemma sum_sigmaCylWeight_level (h : ℕ) :
    ∑ u : Fin h → Bool, sigmaCylWeight (List.ofFn u) = 1 := by
  have := sum_sigmaCylWeight_ext [] h
  simpa [sigmaCylWeight, autoRun, autoWeight] using this

private lemma list_ofFn_add (f : ℕ → Bool) (p m : ℕ) :
    List.ofFn (fun j : Fin (p + m) => f j.val) =
      List.ofFn (fun j : Fin p => f j.val) ++ List.ofFn (fun j : Fin m => f (p + j.val)) := by
  apply List.ext_getElem
  · simp
  · intro k hk1 _
    simp only [List.getElem_ofFn]
    by_cases hk : k < p
    · have hkL : k < (List.ofFn (fun j : Fin p => f j.val)).length := by simpa using hk
      rw [List.getElem_append_left hkL, List.getElem_ofFn]
    · have hk' : p ≤ k := Nat.le_of_not_lt hk
      have hkL : (List.ofFn (fun j : Fin p => f j.val)).length ≤ k := by simpa using hk'
      rw [List.getElem_append_right hkL, List.getElem_ofFn]
      simp [Nat.add_sub_cancel' hk']

private lemma mem_SigmaSet_of_autoRun_all (x : BitSeq)
    (hall : ∀ n : ℕ, (autoRun .S0 (List.ofFn (fun i : Fin n => x.bit i.val))).isSome) :
    x ∈ SigmaSet := by
  let stepPos : ℕ → ℕ := fun p => if x.bit p = false then p + 1 else p + 4
  let pos : ℕ → ℕ := fun i => stepPos^[i] 0
  have hlist_eq : ∀ {a b : ℕ}, a = b →
      List.ofFn (fun j : Fin a => x.bit j.val) = List.ofFn (fun j : Fin b => x.bit j.val) := by
    rintro a _ rfl; rfl
  have hbits : ∀ p : ℕ, autoRun .S0 (List.ofFn (fun j : Fin p => x.bit j.val)) = some .S0 →
      x.bit p = true → x.bit (p + 1) = false ∧ x.bit (p + 2) = false := by
    intro p hp hb0
    have h2 := hall (p + 2)
    rw [list_ofFn_add x.bit p 2, autoRun_append, hp] at h2
    simp [List.ofFn_succ, List.ofFn_zero, autoRun, autoStep, hb0] at h2
    have hb1 : x.bit (p + 1) = false := by
      cases h1 : x.bit (p + 1) <;> simp [h1] at h2 ⊢
    have h3 := hall (p + 3)
    rw [list_ofFn_add x.bit p 3, autoRun_append, hp] at h3
    simp [List.ofFn_succ, List.ofFn_zero, autoRun, autoStep, hb0, hb1] at h3
    have hb2 : x.bit (p + 2) = false := by
      cases h2' : x.bit (p + 2) <;> simp [h2'] at h3 ⊢
    exact ⟨hb1, hb2⟩
  have hstate : ∀ i : ℕ,
      autoRun .S0 (List.ofFn (fun j : Fin (pos i) => x.bit j.val)) = some .S0 := by
    intro i
    induction i with
    | zero => simp [pos, autoRun]
    | succ i ih =>
      have hpi : pos (i + 1) = stepPos (pos i) := Function.iterate_succ_apply' stepPos i 0
      cases hb0 : x.bit (pos i) with
      | false =>
        have hstep1 : pos (i + 1) = pos i + 1 := by rw [hpi]; simp [stepPos, hb0]
        rw [hlist_eq hstep1, list_ofFn_add x.bit (pos i) 1, autoRun_append, ih]
        simp [List.ofFn_succ, List.ofFn_zero, autoRun, autoStep, hb0]
      | true =>
        have hstep4 : pos (i + 1) = pos i + 4 := by rw [hpi]; simp [stepPos, hb0]
        obtain ⟨hb1, hb2⟩ := hbits (pos i) ih hb0
        rw [hlist_eq hstep4, list_ofFn_add x.bit (pos i) 4, autoRun_append, ih]
        simp [List.ofFn_succ, List.ofFn_zero, autoRun, autoStep, hb0, hb1, hb2]
  refine ⟨pos, rfl, fun i => ?_⟩
  have hpi : pos (i + 1) = stepPos (pos i) := Function.iterate_succ_apply' stepPos i 0
  rw [hpi]; dsimp only [stepPos]
  cases hb0 : x.bit (pos i) with
  | false => left; simp
  | true =>
    right
    obtain ⟨hb1, hb2⟩ := hbits (pos i) (hstate i) hb0
    simp [hb1, hb2]

/-- Every finite prefix accepted by `autoRun .S0` extends to an infinite sequence in `Σ`. -/
private lemma exists_mem_SigmaSet_of_autoRun {w : List Bool} (hv : (autoRun .S0 w).isSome) :
    ∃ x ∈ SigmaSet, x ∈ cylSet w := by
  cases hrun : autoRun .S0 w with
  | none => simp [hrun] at hv
  | some s =>
    let x : BitSeq := ⟨fun j => if h : j < w.length then w[j] else false⟩
    have hx_cyl : x ∈ cylSet w := fun i => by simp [x, i.isLt]
    have hx_all : ∀ n : ℕ, (autoRun .S0 (List.ofFn (fun i : Fin n => x.bit i.val))).isSome := by
      intro n
      by_cases hn : n ≤ w.length
      · have htake : List.ofFn (fun i : Fin n => x.bit i.val) = w.take n := by
          apply List.ext_getElem
          · simp [hn]
          · intro i hi1 _
            simp only [List.getElem_ofFn, List.getElem_take, x]
            have hiw : i < w.length := by simp at hi1; omega
            simp [hiw]
        rw [htake]
        have hsp : w = w.take n ++ w.drop n := (List.take_append_drop n w).symm
        have hrun' := hrun
        rw [hsp, autoRun_append] at hrun'
        cases h1 : autoRun .S0 (w.take n) with
        | none => simp [h1] at hrun'
        | some _ => simp
      · have hle : w.length ≤ n := by omega
        have hsp : List.ofFn (fun i : Fin n => x.bit i.val) =
            w ++ List.replicate (n - w.length) false := by
          apply List.ext_getElem
          · simp; omega
          · intro i hi1 _
            simp only [List.getElem_ofFn, x]
            split_ifs with hiw
            · rw [List.getElem_append_left hiw]
            · have hiw' : w.length ≤ i := Nat.le_of_not_lt hiw
              rw [List.getElem_append_right hiw', List.getElem_replicate]
        rw [hsp, autoRun_append, hrun, Option.bind_some]
        have hzeros : ∀ (st : AutoState) (m : ℕ), (autoRun st (List.replicate m false)).isSome := by
          intro st m
          induction m generalizing st with
          | zero => simp [autoRun]
          | succ m ih =>
            simp only [List.replicate_succ, autoRun]
            cases st <;> simp only [autoStep, Option.bind_some] <;> exact ih _
        exact hzeros s (n - w.length)
    exact ⟨x, mem_SigmaSet_of_autoRun_all x hx_all, hx_cyl⟩

/-- Characterization of `Σ` by the 4-state automaton starting at `S_0`. -/
lemma mem_SigmaSet_iff_autoRun (x : BitSeq) :
    x ∈ SigmaSet ↔ ∀ h : ℕ, (autoRun .S0 (List.ofFn (fun i : Fin h => x.bit i.val))).isSome := by
  constructor
  · rintro ⟨pos, h0, hstep⟩ h
    have hpos_ge : ∀ i, i ≤ pos i := by
      intro i; induction i with
      | zero => omega
      | succ i ih => rcases hstep i with ⟨heq, _⟩ | ⟨heq, _⟩ <;> omega
    have hpos_state : ∀ i,
        autoRun .S0 (List.ofFn (fun j : Fin (pos i) => x.bit j.val)) = some .S0 := by
      intro i
      induction i with
      | zero => simp [h0, autoRun]
      | succ i ih =>
        rcases hstep i with ⟨heq, hb0⟩ | ⟨heq, hb0, hb1, hb2⟩
        · rw [heq, list_ofFn_add x.bit (pos i) 1, autoRun_append, ih]
          simp [List.ofFn_succ, List.ofFn_zero, autoRun, autoStep, hb0]
        · rw [heq, list_ofFn_add x.bit (pos i) 4, autoRun_append, ih]
          simp [List.ofFn_succ, List.ofFn_zero, autoRun, autoStep, hb0, hb1, hb2]
    have hle : h ≤ pos h := hpos_ge h
    have hsp : List.ofFn (fun j : Fin (pos h) => x.bit j.val) =
        List.ofFn (fun j : Fin h => x.bit j.val) ++
        List.ofFn (fun j : Fin (pos h - h) => x.bit (h + j.val)) := by
      have heq : pos h = h + (pos h - h) := by omega
      have h1 := list_ofFn_add x.bit h (pos h - h)
      simpa [← heq] using h1
    have hs := hpos_state h
    rw [hsp, autoRun_append] at hs
    cases hr : autoRun .S0 (List.ofFn (fun j : Fin h => x.bit j.val)) with
    | none => simp [hr] at hs
    | some _ => simp
  · exact mem_SigmaSet_of_autoRun_all x

lemma mem_Sigma15Set_iff_autoRun (x : BitSeq) :
    x ∈ Sigma15Set ↔ ∀ h : ℕ, (autoRun .S1 (List.ofFn (fun i : Fin h => x.bit i.val))).isSome := by
  have hshift : ∀ y : BitSeq, ∀ n : ℕ,
      List.ofFn (fun i : Fin (3 + n) => y.bit i.val) =
        [y.bit 0, y.bit 1, y.bit 2] ++ List.ofFn (fun i : Fin n => y.bit (3 + i.val)) := by
    intro y n
    rw [list_ofFn_add y.bit 3 n]
    simp [List.ofFn_succ, List.ofFn_zero]
  constructor
  · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩) h
    · have hz' := (mem_SigmaSet_iff_autoRun z).mp hz
      by_cases h3 : h < 3
      · interval_cases h <;> simp [prependBits, List.ofFn_succ, List.ofFn_zero, autoRun, autoStep]
      · have heq : h = 3 + (h - 3) := by omega
        rw [heq, hshift, autoRun_append]
        have htail : List.ofFn (fun i : Fin (h - 3) => (prependBits [false, false, false] z).bit (3 + i.val)) =
            List.ofFn (fun i : Fin (h - 3) => z.bit i.val) := by
          apply List.ext_getElem <;> simp [prependBits]
        rw [htail]
        simpa [prependBits, autoRun, autoStep] using hz' (h - 3)
    · have hz' := (mem_SigmaSet_iff_autoRun z).mp hz
      by_cases h3 : h < 3
      · interval_cases h <;> simp [prependBits, List.ofFn_succ, List.ofFn_zero, autoRun, autoStep]
      · have heq : h = 3 + (h - 3) := by omega
        rw [heq, hshift, autoRun_append]
        have htail : List.ofFn (fun i : Fin (h - 3) => (prependBits [false, false, true] z).bit (3 + i.val)) =
            List.ofFn (fun i : Fin (h - 3) => z.bit i.val) := by
          apply List.ext_getElem <;> simp [prependBits]
        rw [htail]
        simpa [prependBits, autoRun, autoStep] using hz' (h - 3)
  · intro hall
    have h1 := hall 1
    have h2 := hall 2
    simp only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, autoRun] at h1 h2
    have hb0 : x.bit 0 = false := by cases h : x.bit 0 <;> simp [h, autoStep] at h1 ⊢
    have hb1 : x.bit 1 = false := by cases h : x.bit 1 <;> simp [hb0, h, autoStep] at h2 ⊢
    let z : BitSeq := ⟨fun j => x.bit (3 + j)⟩
    have hz : z ∈ SigmaSet := by
      rw [mem_SigmaSet_iff_autoRun]
      intro n
      have h3n := hall (3 + n)
      rw [hshift, autoRun_append] at h3n
      simpa [hb0, hb1, autoRun, autoStep, z] using h3n
    cases hb2 : x.bit 2 with
    | false =>
      left
      refine ⟨z, hz, ?_⟩
      ext j
      by_cases hj : j < 3
      · interval_cases j <;> simp [prependBits, hb0, hb1, hb2]
      · simp [prependBits, hj, z, show 3 + (j - 3) = j by omega]
    | true =>
      right
      refine ⟨z, hz, ?_⟩
      ext j
      by_cases hj : j < 3
      · interval_cases j <;> simp [prependBits, hb0, hb1, hb2]
      · simp [prependBits, hj, z, show 3 + (j - 3) = j by omega]

lemma SigmaSet_isClosed : IsClosed SigmaSet := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  rw [mem_SigmaSet_iff_autoRun]
  intro h
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx ((2 : ℝ) ^ (-(h : ℤ))) (by positivity)
  have hagree : List.ofFn (fun i : Fin h => x.bit i.val) =
      List.ofFn (fun i : Fin h => y.bit i.val) := by
    apply List.ext_getElem
    · simp
    · intro i hi1 _
      simp only [List.getElem_ofFn]
      exact bitSeq_eq_of_dist_lt hxy i (by simp at hi1; omega)
  rw [hagree]
  exact (mem_SigmaSet_iff_autoRun y).mp hy h

/-- The halving-itinerary map `Ψ_r : ℤ_[2] → BitSeq`. -/
noncomputable def psiMap (r : ℕ) (x : ℤ_[2]) : BitSeq :=
  ⟨fun j => decide ((T^[j] (30 * x.appr (j + 1) + r) / 30) % 2 = 1)⟩

/-- Theorem `thm:cantor` (Part 2a): `Ψ_r : ℤ_[2] → {0, 1}^ℕ` is a `2`-adic isometry. -/
theorem psiMap_isometry (r : ℕ) : Isometry (psiMap r) := by
  rw [isometry_iff_dist_eq]
  intro x y
  by_cases hxy : x = y
  · subst hxy; simp
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set m := (x - y).valuation
    have hnorm : dist x y = (2 : ℝ) ^ (-(m : ℤ)) := by
      rw [dist_eq_norm, PadicInt.norm_eq_zpow_neg_valuation (sub_ne_zero.mpr hxy)]
      push_cast; rfl
    have hlo : x.appr m = y.appr m :=
      (padic2_norm_le_iff_appr_eq x y m).mp (by rw [← dist_eq_norm, hnorm])
    have hhi : x.appr (m + 1) ≠ y.appr (m + 1) := by
      intro heq
      have hle := (padic2_norm_le_iff_appr_eq x y (m + 1)).mpr heq
      rw [← dist_eq_norm, hnorm] at hle
      have hlt : (2 : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) < (2 : ℝ) ^ (-(m : ℤ)) :=
        zpow_lt_zpow_right₀ (by norm_num) (by omega)
      linarith
    have hbits_lt : ∀ j < m, (psiMap r x).bit j = (psiMap r y).bit j := by
      intro j hj
      have hj1 : x.appr (j + 1) = y.appr (j + 1) := by
        rw [← padic2_appr_mod_eq x (by omega : j + 1 ≤ m),
            ← padic2_appr_mod_eq y (by omega : j + 1 ≤ m), hlo]
      simp [psiMap, hj1]
    have hbit_m : (psiMap r x).bit m ≠ (psiMap r y).bit m := by
      have hmod_m : x.appr (m + 1) % 2 ^ m = y.appr (m + 1) % 2 ^ m := by
        rw [padic2_appr_mod_eq x (Nat.le_succ m), padic2_appr_mod_eq y (Nat.le_succ m), hlo]
      have hmod_m1 : x.appr (m + 1) % 2 ^ (m + 1) ≠ y.appr (m + 1) % 2 ^ (m + 1) := by
        rw [Nat.mod_eq_of_lt (PadicInt.appr_lt x (m + 1)),
            Nat.mod_eq_of_lt (PadicInt.appr_lt y (m + 1))]
        exact hhi
      have hne := T_iter_quot_mod2_ne (r := r) hmod_m hmod_m1
      simp only [psiMap, ne_eq, decide_eq_decide]
      omega
    have hpsi_ne : psiMap r x ≠ psiMap r y := fun h => hbit_m (by rw [h])
    have hfd : firstDiff hpsi_ne = m := firstDiff_eq_of hpsi_ne m hbits_lt hbit_m
    rw [bitSeq_dist_of_ne hpsi_ne, hfd, hnorm]

private def liftMod (r : ℕ) (y : BitSeq) : ℕ → ℕ
  | 0 => 0
  | h + 1 =>
    let k := liftMod r y h
    if decide ((T^[h] (30 * k + r) / 30) % 2 = 1) = y.bit h then k else k + 2 ^ h

private lemma liftMod_lt (r : ℕ) (y : BitSeq) (h : ℕ) : liftMod r y h < 2 ^ h := by
  induction h with
  | zero => simp [liftMod]
  | succ h ih =>
    simp only [liftMod]
    split_ifs <;> rw [pow_succ'] <;> omega

private lemma liftMod_dvd_sub (r : ℕ) (y : BitSeq) (h : ℕ) :
    ((2 : ℕ) : ℤ) ^ h ∣ ((liftMod r y (h + 1) : ℤ) - (liftMod r y h : ℤ)) := by
  simp only [liftMod]
  split_ifs
  · simp
  · refine ⟨1, ?_⟩; push_cast; ring

private lemma liftMod_bit (r : ℕ) (y : BitSeq) (h : ℕ) :
    decide ((T^[h] (30 * liftMod r y (h + 1) + r) / 30) % 2 = 1) = y.bit h := by
  set k := liftMod r y h
  have hdef : liftMod r y (h + 1) =
      if decide ((T^[h] (30 * k + r) / 30) % 2 = 1) = y.bit h then k else k + 2 ^ h := rfl
  rw [hdef]
  split_ifs with hmatch
  · exact hmatch
  · have hlt := liftMod_lt r y h
    have hlo : (k + 2 ^ h) % 2 ^ h = k % 2 ^ h := Nat.add_mod_right k (2 ^ h)
    have hhi : (k + 2 ^ h) % 2 ^ (h + 1) ≠ k % 2 ^ (h + 1) := by
      have hlt1 : k < 2 ^ (h + 1) := lt_trans hlt (by rw [pow_succ']; omega)
      have hlt2 : k + 2 ^ h < 2 ^ (h + 1) := by rw [pow_succ']; omega
      rw [Nat.mod_eq_of_lt hlt2, Nat.mod_eq_of_lt hlt1]
      have : 0 < 2 ^ h := by positivity
      omega
    have hne := T_iter_quot_mod2_ne (r := r) hlo hhi
    cases hb : y.bit h <;> simp only [hb] at hmatch ⊢ <;>
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hmatch ⊢ <;> omega

/-- `Ψ_r : ℤ_[2] → {0, 1}^ℕ` is surjective onto all of `{0, 1}^ℕ`. -/
theorem psiMap_surjective (r : ℕ) : Function.Surjective (psiMap r) := by
  intro y
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let fseq : ℕ → ℤ := fun h => (liftMod r y h : ℤ)
  have hdvd : ∀ i : ℕ, ((2 : ℕ) : ℤ) ^ i ∣ fseq (i + 1) - fseq i := liftMod_dvd_sub r y
  let x : ℤ_[2] := PadicInt.ofIntSeq fseq (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub fseq 2 hdvd)
  have hx_appr : ∀ h : ℕ, x.appr h = liftMod r y h := by
    intro h
    have hz1 := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub fseq 2 hdvd h
    have hz2 : PadicInt.toZModPow h x = ((x.appr h : ℕ) : ZMod (2 ^ h)) := by
      have hmem := PadicInt.appr_spec h x
      rw [← PadicInt.ker_toZModPow h, RingHom.mem_ker, map_sub, map_natCast] at hmem
      exact sub_eq_zero.mp hmem
    have hzeq : ((x.appr h : ℕ) : ZMod (2 ^ h)) = ((liftMod r y h : ℕ) : ZMod (2 ^ h)) := by
      have : ((fseq h : ℤ) : ZMod (2 ^ h)) = ((liftMod r y h : ℕ) : ZMod (2 ^ h)) := by
        simp [fseq]
      rw [← hz2, ← this]; exact hz1
    have hmod := (ZMod.natCast_eq_natCast_iff' (x.appr h) (liftMod r y h) (2 ^ h)).mp hzeq
    rwa [Nat.mod_eq_of_lt (PadicInt.appr_lt x h), Nat.mod_eq_of_lt (liftMod_lt r y h)] at hmod
  refine ⟨x, ?_⟩
  ext j
  simp only [psiMap, hx_appr (j + 1)]
  exact liftMod_bit r y j

private lemma resToAutoState_T_iter (r h : ℕ) (x : ℤ_[2]) :
    resToAutoState (T^[h] (30 * x.appr h + r)) =
      (resToAutoState r).bind (fun s => autoRun s (List.ofFn (fun i : Fin h => (psiMap r x).bit i.val))) := by
  induction h with
  | zero =>
    simp only [Function.iterate_zero, id_eq, List.ofFn_zero, autoRun]
    have : resToAutoState (30 * x.appr 0 + r) = resToAutoState r := by
      unfold resToAutoState; congr 1; omega
    rw [this]
    cases resToAutoState r <;> rfl
  | succ h ih =>
    have hmod_h : x.appr (h + 1) % 2 ^ h = x.appr h := padic2_appr_mod_eq x (Nat.le_succ h)
    have hstep_mod : resToAutoState (T^[h] (30 * x.appr (h + 1) + r)) =
        resToAutoState (T^[h] (30 * x.appr h + r)) := by
      unfold resToAutoState
      have hmt := T_iter_mod30_eq (h := h) (j := h) (k₁ := x.appr (h + 1)) (k₂ := x.appr h)
        (r := r) le_rfl (by rw [hmod_h, Nat.mod_eq_of_lt (PadicInt.appr_lt x h)])
      rw [hmt]
    rw [Function.iterate_succ_apply', resToAutoState_step, hstep_mod, ih]
    have hlist : List.ofFn (fun i : Fin (h + 1) => (psiMap r x).bit i.val) =
        List.ofFn (fun i : Fin h => (psiMap r x).bit i.val) ++ [(psiMap r x).bit h] := by
      rw [list_ofFn_add (psiMap r x).bit h 1]
      simp [List.ofFn_succ, List.ofFn_zero]
    rw [hlist]
    cases h0 : resToAutoState r with
    | none => simp
    | some s0 =>
      simp only [Option.bind_some, autoRun_append]
      cases hrun : autoRun s0 (List.ofFn (fun i : Fin h => (psiMap r x).bit i.val)) with
      | none => simp
      | some s1 =>
        simp only [Option.bind_some, autoRun, psiMap]
        cases autoStep s1 _ <;> rfl

/-- Theorem `thm:cantor` (Part 2b): `Ψ_r` maps `𝒦_r` bijectively onto `Σ` for `r ∈ {1, 17}`. -/
theorem psiMap_image_KCal_1_17 {r : ℕ} (hr : r = 1 ∨ r = 17) :
    psiMap r '' KCal r = SigmaSet := by
  have hres : resToAutoState r = some .S0 := by rcases hr with rfl | rfl <;> decide
  have hS : InS30 r := by unfold InS30; rcases hr with rfl | rfl <;> omega
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_SigmaSet_iff_autoRun]
    intro h
    have h1 := resToAutoState_T_iter r h x
    rw [hres, Option.bind_some] at h1
    rw [← h1, resToAutoState_isSome_iff]
    exact (survives_iff_InS30 hS h (x.appr h)).mp (hx h)
  · intro hy
    obtain ⟨x, rfl⟩ := psiMap_surjective r y
    refine ⟨x, fun h => ?_, rfl⟩
    rw [survives_iff_InS30 hS h (x.appr h), ← resToAutoState_isSome_iff,
        resToAutoState_T_iter r h x, hres, Option.bind_some]
    exact (mem_SigmaSet_iff_autoRun _).mp hy h

/-- Theorem `thm:cantor` (Part 2c): `Ψ_15` maps `𝒦_15` bijectively onto `000 Σ ⊔ 001 Σ`. -/
theorem psiMap_image_KCal_15 : psiMap 15 '' KCal 15 = Sigma15Set := by
  have hres : resToAutoState 15 = some .S1 := by decide
  have hS : InS30 15 := by unfold InS30; omega
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_Sigma15Set_iff_autoRun]
    intro h
    have h1 := resToAutoState_T_iter 15 h x
    rw [hres, Option.bind_some] at h1
    rw [← h1, resToAutoState_isSome_iff]
    exact (survives_iff_InS30 hS h (x.appr h)).mp (hx h)
  · intro hy
    obtain ⟨x, rfl⟩ := psiMap_surjective 15 y
    refine ⟨x, fun h => ?_, rfl⟩
    rw [survives_iff_InS30 hS h (x.appr h), ← resToAutoState_isSome_iff,
        resToAutoState_T_iter 15 h x, hres, Option.bind_some]
    exact (mem_Sigma15Set_iff_autoRun _).mp hy h

/-! ### Exact cylinder counts `N_h(r)` and Hausdorff measure of `Σ` and `closure B_1` -/

/-- Number `N_h(r)` of surviving classes `k < 2^h` for residue `r`. -/
def countSurvives (r h : ℕ) : ℕ :=
  ((Finset.range (2 ^ h)).filter (fun k => Survives r h k)).card

private def validWords (s : AutoState) (h : ℕ) : Finset (Fin h → Bool) :=
  Finset.univ.filter (fun u : Fin h → Bool => (autoRun s (List.ofFn u)).isSome)

private lemma countSurvives_eq_validWords {r : ℕ} {s : AutoState}
    (hres : resToAutoState r = some s) (h : ℕ) :
    countSurvives r h = (validWords s h).card := by
  have hS : InS30 r := (resToAutoState_isSome_iff r).mp (by simp [hres])
  let g : ℕ → (Fin h → Bool) := fun k i => (psiMap r (k : ℤ_[2])).bit i.val
  unfold countSurvives
  refine Finset.card_bij (fun k _ => g k) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [validWords, Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 := resToAutoState_T_iter r h (k : ℤ_[2])
    rw [hres, Option.bind_some, padic2_appr_natCast, Nat.mod_eq_of_lt hk.1] at h1
    rw [← h1, resToAutoState_isSome_iff]
    exact (survives_iff_InS30 hS h k).mp hk.2
  · intro k₁ hk₁ k₂ hk₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hk₁ hk₂
    by_contra hne
    have hlt : dist (psiMap r (k₁ : ℤ_[2])) (psiMap r (k₂ : ℤ_[2])) ≤ (2 : ℝ) ^ (-(h : ℤ)) :=
      bitSeq_dist_le_of_eq h fun j hj => congr_fun heq ⟨j, hj⟩
    rw [isometry_iff_dist_eq.mp (psiMap_isometry r), dist_eq_norm] at hlt
    have happr := (padic2_norm_le_iff_appr_eq _ _ h).mp hlt
    rw [padic2_appr_natCast, padic2_appr_natCast, Nat.mod_eq_of_lt hk₁.1,
        Nat.mod_eq_of_lt hk₂.1] at happr
    exact hne happr
  · intro u hu
    simp only [validWords, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    let y : BitSeq := ⟨fun j => if hj : j < h then u ⟨j, hj⟩ else false⟩
    obtain ⟨x, hx⟩ := psiMap_surjective r y
    set k := x.appr h
    have hk_lt : k < 2 ^ h := PadicInt.appr_lt x h
    have hgk : g k = u := by
      ext i
      simp only [g, psiMap]
      have hmod : (k : ℤ_[2]).appr (i.val + 1) = x.appr (i.val + 1) := by
        rw [padic2_appr_natCast, padic2_appr_mod_eq x (by omega : i.val + 1 ≤ h)]
      rw [hmod]
      have hbit : (psiMap r x).bit i.val = y.bit i.val := by rw [hx]
      simpa [psiMap, y, i.isLt] using hbit
    have hsurv : Survives r h k := by
      rw [survives_iff_InS30 hS h k, ← resToAutoState_isSome_iff]
      have h1 := resToAutoState_T_iter r h (k : ℤ_[2])
      rw [hres, Option.bind_some, padic2_appr_natCast, Nat.mod_eq_of_lt hk_lt] at h1
      rw [h1]
      have hlist : List.ofFn (fun i : Fin h => (psiMap r (k : ℤ_[2])).bit i.val) = List.ofFn u :=
        congr_arg List.ofFn hgk
      rw [hlist]; exact hu
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk_lt, hsurv⟩, hgk⟩

/-- Uniform upper and lower cylinder-count bounds for `N_h(1), N_h(17), N_h(15)`. -/
lemma countSurvives_bounds (h : ℕ) :
    (2 * aStar)⁻¹ * (aStar ^ h)⁻¹ ≤ (countSurvives 1 h : ℝ) ∧
    (countSurvives 1 h : ℝ) ≤ (2 * aStar ^ 3)⁻¹ * (aStar ^ h)⁻¹ ∧
    countSurvives 17 h = countSurvives 1 h ∧
    (countSurvives 15 h : ℝ) ≤ (aStar ^ h)⁻¹ := by
  have ha0 := aStar_spec.1
  have h1_eq : countSurvives 1 h = (validWords .S0 h).card :=
    countSurvives_eq_validWords (r := 1) (s := .S0) (by decide) h
  have h17_eq : countSurvives 17 h = (validWords .S0 h).card :=
    countSurvives_eq_validWords (r := 17) (s := .S0) (by decide) h
  have h15_eq : countSurvives 15 h = (validWords .S1 h).card :=
    countSurvives_eq_validWords (r := 15) (s := .S1) (by decide) h
  have hsum_valid : ∀ m : ℕ, ∑ u ∈ validWords .S0 m, sigmaCylWeight (List.ofFn u) = 1 := by
    intro m
    rw [← sum_sigmaCylWeight_level m]
    refine Finset.sum_subset (Finset.filter_subset _ _) fun u _ hu => ?_
    simp only [validWords, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    unfold sigmaCylWeight
    cases hrun : autoRun .S0 (List.ofFn u) with
    | none => rfl
    | some _ => simp [hrun] at hu
  have hlo : 2 * aStar ^ 3 * aStar ^ h * ((validWords .S0 h).card : ℝ) ≤ 1 := by
    calc 2 * aStar ^ 3 * aStar ^ h * ((validWords .S0 h).card : ℝ)
        = ∑ _u ∈ validWords .S0 h, 2 * aStar ^ 3 * aStar ^ h := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ u ∈ validWords .S0 h, sigmaCylWeight (List.ofFn u) :=
            Finset.sum_le_sum fun u hu => by
              have hv : (autoRun .S0 (List.ofFn u)).isSome := (Finset.mem_filter.mp hu).2
              simpa using sigmaCylWeight_ge_of_valid hv
      _ = 1 := hsum_valid h
  have hhi : 1 ≤ 2 * aStar * aStar ^ h * ((validWords .S0 h).card : ℝ) := by
    calc (1 : ℝ) = ∑ u ∈ validWords .S0 h, sigmaCylWeight (List.ofFn u) := (hsum_valid h).symm
      _ ≤ ∑ _u ∈ validWords .S0 h, 2 * aStar * aStar ^ h :=
            Finset.sum_le_sum fun u _ => by simpa using sigmaCylWeight_le (List.ofFn u)
      _ = 2 * aStar * aStar ^ h * ((validWords .S0 h).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hN1_lo : (2 * aStar)⁻¹ * (aStar ^ h)⁻¹ ≤ ((validWords .S0 h).card : ℝ) := by
    rw [← mul_inv, ← one_div, div_le_iff₀ (by positivity)]
    linarith
  have hN1_hi : ((validWords .S0 h).card : ℝ) ≤ (2 * aStar ^ 3)⁻¹ * (aStar ^ h)⁻¹ := by
    rw [← mul_inv, ← one_div, le_div_iff₀ (by positivity)]
    linarith
  have hN15_hi : ((validWords .S1 h).card : ℝ) ≤ (aStar ^ h)⁻¹ := by
    by_cases h3 : h < 3
    · have hcard : (validWords .S1 h).card = 1 := by
        interval_cases h <;> decide
      rw [hcard, Nat.cast_one]
      have ha1 := aStar_spec.2.1
      have : aStar ^ h ≤ 1 := pow_le_one₀ ha0.le ha1.le
      exact (one_le_inv₀ (by positivity)).mpr this
    · have hge3 : 3 ≤ h := by omega
      have hsplit3 : ∀ u : Fin h → Bool, List.ofFn u =
          [u ⟨0, by omega⟩, u ⟨1, by omega⟩, u ⟨2, by omega⟩] ++
          List.ofFn (fun i : Fin (h - 3) => u ⟨3 + i.val, by omega⟩) := by
        intro u
        let g : ℕ → Bool := fun j => if hj : j < h then u ⟨j, hj⟩ else false
        have h1 : List.ofFn u = List.ofFn (fun j : Fin (3 + (h - 3)) => g j.val) := by
          apply List.ext_getElem
          · simp; omega
          · intro k hk1 _
            have hk : k < h := by simp at hk1; exact hk1
            simp [g, hk]
        rw [h1, list_ofFn_add g 3 (h - 3)]
        have hL : List.ofFn (fun j : Fin 3 => g j.val) =
            [u ⟨0, by omega⟩, u ⟨1, by omega⟩, u ⟨2, by omega⟩] := by
          simp [List.ofFn_succ, List.ofFn_zero, g, show (0 : ℕ) < h by omega,
            show (1 : ℕ) < h by omega, show (2 : ℕ) < h by omega]
        have hR : List.ofFn (fun i : Fin (h - 3) => g (3 + i.val)) =
            List.ofFn (fun i : Fin (h - 3) => u ⟨3 + i.val, by omega⟩) := by
          congr 1; ext i; simp [g, show 3 + i.val < h by omega]
        rw [hL, hR]
      let f : (Fin h → Bool) → Bool × (Fin (h - 3) → Bool) :=
        fun u => (u ⟨2, by omega⟩, fun i => u ⟨3 + i.val, by omega⟩)
      have hbit01 : ∀ u : Fin h → Bool, (autoRun .S1 (List.ofFn u)).isSome →
          u ⟨0, by omega⟩ = false ∧ u ⟨1, by omega⟩ = false := by
        intro u hu
        rw [hsplit3 u, autoRun_append] at hu
        have hb0 : u ⟨0, by omega⟩ = false := by
          cases hb : u ⟨0, by omega⟩ <;> simp [hb, autoRun, autoStep] at hu ⊢
        have hb1 : u ⟨1, by omega⟩ = false := by
          cases hb : u ⟨1, by omega⟩ <;> simp [hb0, hb, autoRun, autoStep] at hu ⊢
        exact ⟨hb0, hb1⟩
      have hcard_le : (validWords .S1 h).card ≤ 2 * (validWords .S0 (h - 3)).card := by
        have h1 : (validWords .S1 h).card ≤
            ((Finset.univ : Finset Bool) ×ˢ validWords .S0 (h - 3)).card := by
          refine Finset.card_le_card_of_injOn f ?_ ?_
          · intro u hu
            simp only [Finset.mem_coe, validWords, Finset.mem_filter, Finset.mem_univ, true_and] at hu
            obtain ⟨hb0, hb1⟩ := hbit01 u hu
            rw [hsplit3 u, autoRun_append] at hu
            simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, true_and,
              validWords, Finset.mem_filter]
            simpa [f, hb0, hb1, autoRun, autoStep] using hu
          · intro u₁ hu₁ u₂ hu₂ heq
            simp only [Finset.mem_coe, validWords, Finset.mem_filter, Finset.mem_univ, true_and] at hu₁ hu₂
            have h1 := hbit01 u₁ hu₁
            have h2 := hbit01 u₂ hu₂
            ext i
            by_cases hi0 : i.val = 0
            · have : i = ⟨0, by omega⟩ := Fin.ext hi0; rw [this, h1.1, h2.1]
            · by_cases hi1 : i.val = 1
              · have : i = ⟨1, by omega⟩ := Fin.ext hi1; rw [this, h1.2, h2.2]
              · by_cases hi2 : i.val = 2
                · have : i = ⟨2, by omega⟩ := Fin.ext hi2; rw [this]; exact congr_arg Prod.fst heq
                · have h3i : 3 + (i.val - 3) = i.val := by omega
                  have := congr_fun (congr_arg Prod.snd heq) ⟨i.val - 3, by omega⟩
                  simpa [f, h3i] using this
        simpa [Finset.card_product] using h1
      have hcast : ((validWords .S1 h).card : ℝ) ≤ 2 * ((validWords .S0 (h - 3)).card : ℝ) := by
        exact_mod_cast hcard_le
      have hlo_sub : 2 * aStar ^ 3 * aStar ^ (h - 3) * ((validWords .S0 (h - 3)).card : ℝ) ≤ 1 := by
        calc 2 * aStar ^ 3 * aStar ^ (h - 3) * ((validWords .S0 (h - 3)).card : ℝ)
            = ∑ _u ∈ validWords .S0 (h - 3), 2 * aStar ^ 3 * aStar ^ (h - 3) := by
                rw [Finset.sum_const, nsmul_eq_mul]; ring
          _ ≤ ∑ u ∈ validWords .S0 (h - 3), sigmaCylWeight (List.ofFn u) :=
                Finset.sum_le_sum fun u hu => by
                  simpa using sigmaCylWeight_ge_of_valid (Finset.mem_filter.mp hu).2
          _ = 1 := hsum_valid (h - 3)
      have hpow : aStar ^ 3 * aStar ^ (h - 3) = aStar ^ h := by
        rw [← pow_add, show 3 + (h - 3) = h by omega]
      have hsub : 2 * aStar ^ h * ((validWords .S0 (h - 3)).card : ℝ) ≤ 1 := by
        calc 2 * aStar ^ h * ((validWords .S0 (h - 3)).card : ℝ)
            = 2 * (aStar ^ 3 * aStar ^ (h - 3)) * ((validWords .S0 (h - 3)).card : ℝ) := by rw [hpow]
          _ = 2 * aStar ^ 3 * aStar ^ (h - 3) * ((validWords .S0 (h - 3)).card : ℝ) := by ring
          _ ≤ 1 := hlo_sub
      rw [← one_div, le_div_iff₀ (by positivity)]
      have hmul : ((validWords .S1 h).card : ℝ) * aStar ^ h ≤
          2 * aStar ^ h * ((validWords .S0 (h - 3)).card : ℝ) := by
        calc ((validWords .S1 h).card : ℝ) * aStar ^ h
            ≤ (2 * ((validWords .S0 (h - 3)).card : ℝ)) * aStar ^ h :=
              mul_le_mul_of_nonneg_right hcast (by positivity)
          _ = 2 * aStar ^ h * ((validWords .S0 (h - 3)).card : ℝ) := by ring
      linarith
  exact ⟨h1_eq ▸ hN1_lo, h1_eq ▸ hN1_hi, by rw [h17_eq, h1_eq], h15_eq ▸ hN15_hi⟩

private lemma two_zpow_neg_rpow_beta (h : ℕ) :
    ((2 : ℝ) ^ (-(h : ℤ))) ^ beta = aStar ^ h := by
  rw [zpow_neg, zpow_natCast, Real.inv_rpow (by positivity),
      ← Real.rpow_natCast (2 : ℝ) h, ← Real.rpow_mul (by norm_num),
      mul_comm (h : ℝ) beta, Real.rpow_mul (by norm_num), two_rpow_beta,
      Real.rpow_natCast, one_div, inv_pow, inv_inv]

private lemma finset_sum_biUnion_le {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h1 : ∑ b ∈ t a ∪ s.biUnion t, f b ≤ (∑ b ∈ t a, f b) + ∑ b ∈ s.biUnion t, f b := by
      have := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
      have hnn : 0 ≤ ∑ b ∈ t a ∩ s.biUnion t, f b := Finset.sum_nonneg fun b _ => hf b
      linarith
    linarith

/-- Exact Hausdorff measure bracket on `Σ`: `(2a)^{-1} ≤ μH[β](Σ) ≤ (2a^3)^{-1}`. -/
theorem hausdorffMeasure_SigmaSet_bounds :
    ENNReal.ofReal ((2 * aStar)⁻¹) ≤ μH[beta] SigmaSet ∧
    μH[beta] SigmaSet ≤ ENNReal.ofReal ((2 * aStar ^ 3)⁻¹) := by
  have ha0 := aStar_spec.1
  have ha1 := aStar_spec.2.1
  have hbeta_pos : 0 < beta := by linarith [beta_bounds_6.1]
  constructor
  · -- Lower bound via compact finite subcover and exact consistency of `sigmaCylWeight`.
    rw [Measure.hausdorffMeasure_apply]
    refine le_iSup₂_of_le 1 zero_lt_one ?_
    refine le_iInf₂ fun t hcov => le_iInf fun _ => ?_
    set S : ℝ≥0∞ := ∑' n : ℕ, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ beta
    by_cases hStop : S = ⊤
    · rw [hStop]; exact le_top
    have hS_real : S = ENNReal.ofReal S.toReal := (ENNReal.ofReal_toReal hStop).symm
    suffices hR : (2 * aStar)⁻¹ ≤ S.toReal by
      rw [hS_real]; exact ENNReal.ofReal_le_ofReal hR
    suffices hε_all : ∀ ε : ℝ, 0 < ε → 1 ≤ 2 * aStar * S.toReal + ε by
      have h1 : 1 ≤ 2 * aStar * S.toReal := le_of_forall_pos_le_add hε_all
      rw [← one_div, div_le_iff₀ (by positivity)]
      linarith
    intro ε hε
    have hex_w : ∀ n : ℕ, ∃ w : List Bool,
        ((t n).Nonempty → t n ⊆ cylSet w) ∧
        sigmaCylWeight w ≤ 2 * aStar * (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ beta).toReal +
          ε / 2 ^ (n + 1) := by
      intro n
      by_cases hne : (t n).Nonempty
      · by_cases hd : 0 < Metric.ediam (t n)
        · obtain ⟨w, hsub, hdiam⟩ := bitSeq_subset_cyl_of_ediam_pos hd
          refine ⟨w, fun _ => hsub, ?_⟩
          have hterm : (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ beta).toReal = aStar ^ w.length := by
            rw [ciSup_pos hne, hdiam, ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (-(w.length : ℤ))),
                two_zpow_neg_rpow_beta, ENNReal.toReal_ofReal (by positivity)]
          rw [hterm]
          have hle := sigmaCylWeight_le w
          have hpos_e : 0 ≤ ε / 2 ^ (n + 1) := by positivity
          linarith
        · have hd0 : Metric.ediam (t n) = 0 := le_antisymm (not_lt.mp hd) bot_le
          obtain ⟨x₀, hx₀⟩ := hne
          have hsub_sing : t n ⊆ {x₀} := fun y hy => by
            rw [Set.mem_singleton_iff]
            have := Metric.edist_le_ediam_of_mem hy hx₀
            rw [hd0, nonpos_iff_eq_zero] at this
            exact edist_eq_zero.mp this
          have htend : Filter.Tendsto (fun k : ℕ => 2 * aStar * aStar ^ k) Filter.atTop (nhds 0) := by
            simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).const_mul (2 * aStar)
          obtain ⟨k, hk⟩ := (htend.eventually (gt_mem_nhds (by positivity : 0 < ε / 2 ^ (n + 1)))).exists
          let w : List Bool := List.ofFn (fun i : Fin k => x₀.bit i.val)
          refine ⟨w, fun _ y hy => ?_, ?_⟩
          · have hyx : y = x₀ := hsub_sing hy
            subst hyx; intro i; simp [w]
          · have hwle : sigmaCylWeight w ≤ 2 * aStar * aStar ^ k := by
              simpa [w] using sigmaCylWeight_le w
            have hnn : 0 ≤ 2 * aStar * (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ beta).toReal := by
              positivity
            linarith
      · have htend : Filter.Tendsto (fun k : ℕ => 2 * aStar * aStar ^ k) Filter.atTop (nhds 0) := by
          simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).const_mul (2 * aStar)
        obtain ⟨k, hk⟩ := (htend.eventually (gt_mem_nhds (by positivity : 0 < ε / 2 ^ (n + 1)))).exists
        refine ⟨List.replicate k false, fun h => absurd h hne, ?_⟩
        have hwle : sigmaCylWeight (List.replicate k false) ≤ 2 * aStar * aStar ^ k := by
          simpa using sigmaCylWeight_le (List.replicate k false)
        have hnn : 0 ≤ 2 * aStar * (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ beta).toReal := by
          positivity
        linarith
    choose w hw_sub hw_wt using hex_w
    have hcov_cyl : SigmaSet ⊆ ⋃ n : ℕ, cylSet (w n) := fun x hx => by
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcov hx)
      exact Set.mem_iUnion.mpr ⟨n, hw_sub n ⟨x, hn⟩ hn⟩
    obtain ⟨F, hF⟩ := SigmaSet_isClosed.isCompact.elim_finite_subcover
      (fun n => cylSet (w n)) (fun n => cylSet_isOpen (w n)) hcov_cyl
    set H := F.sup (fun n => (w n).length)
    let extSet : List Bool → Finset (Fin H → Bool) := fun p =>
      Finset.univ.filter (fun u : Fin H → Bool =>
        ∀ i : Fin H, (hi : i.val < p.length) → u i = p[i.val])
    have hext_sum : ∀ p : List Bool, p.length ≤ H →
        ∑ u ∈ extSet p, sigmaCylWeight (List.ofFn u) = sigmaCylWeight p := by
      intro p hp
      let φ : (Fin (H - p.length) → Bool) → (Fin H → Bool) :=
        fun u' i => if hi : i.val < p.length then p[i.val] else u' ⟨i.val - p.length, by omega⟩
      have hsum_eq : ∑ u' : Fin (H - p.length) → Bool, sigmaCylWeight (p ++ List.ofFn u') =
          ∑ u ∈ extSet p, sigmaCylWeight (List.ofFn u) := by
        refine Finset.sum_bij (fun u' _ => φ u') ?_ ?_ ?_ ?_
        · intro u' _
          simp only [extSet, Finset.mem_filter, Finset.mem_univ, true_and]
          intro i hi; simp [φ, hi]
        · intro u₁ _ u₂ _ heq
          ext j
          have h := congr_fun heq ⟨p.length + j.val, by omega⟩
          simpa [φ, show ¬ (p.length + j.val < p.length) by omega] using h
        · intro u hu
          simp only [extSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
          refine ⟨fun j => u ⟨p.length + j.val, by omega⟩, Finset.mem_univ _, ?_⟩
          ext i
          dsimp only [φ]
          split_ifs with hi
          · exact (hu i hi).symm
          · congr 1; apply Fin.ext; dsimp; omega
        · intro u' _
          congr 1
          apply List.ext_getElem
          · simp; omega
          · intro k hk1 _
            simp only [List.getElem_ofFn, φ]
            split_ifs with hk
            · rw [List.getElem_append_left hk]
            · have hk' : p.length ≤ k := Nat.le_of_not_lt hk
              rw [List.getElem_append_right hk', List.getElem_ofFn]
      rw [← hsum_eq, sum_sigmaCylWeight_ext p (H - p.length)]
    have hsub_cov : validWords .S0 H ⊆ F.biUnion (fun n => extSet (w n)) := by
      intro u hu
      have hv : (autoRun .S0 (List.ofFn u)).isSome := (Finset.mem_filter.mp hu).2
      obtain ⟨x, hx_sig, hx_cyl⟩ := exists_mem_SigmaSet_of_autoRun hv
      have hx_cov := hF hx_sig
      simp only [Set.mem_iUnion] at hx_cov
      obtain ⟨n, hnF, hxn⟩ := hx_cov
      rw [Finset.mem_biUnion]
      refine ⟨n, hnF, ?_⟩
      simp only [extSet, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i hi
      have h1 : x.bit i.val = u i := by
        have := hx_cyl ⟨i.val, by simp⟩
        simpa using this
      have h2 : x.bit i.val = (w n)[i.val] := hxn ⟨i.val, hi⟩
      rw [← h1, h2]
    have hsum1 : ∑ u ∈ validWords .S0 H, sigmaCylWeight (List.ofFn u) = 1 := by
      rw [← sum_sigmaCylWeight_level H]
      refine Finset.sum_subset (Finset.filter_subset _ _) fun u _ hu => ?_
      simp only [validWords, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      unfold sigmaCylWeight
      cases hrun : autoRun .S0 (List.ofFn u) with
      | none => rfl
      | some _ => simp [hrun] at hu
    have h1_le_F : (1 : ℝ) ≤ ∑ n ∈ F, sigmaCylWeight (w n) := by
      calc (1 : ℝ) = ∑ u ∈ validWords .S0 H, sigmaCylWeight (List.ofFn u) := hsum1.symm
        _ ≤ ∑ u ∈ F.biUnion (fun n => extSet (w n)), sigmaCylWeight (List.ofFn u) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_cov fun _ _ _ => sigmaCylWeight_nonneg _
        _ ≤ ∑ n ∈ F, ∑ u ∈ extSet (w n), sigmaCylWeight (List.ofFn u) :=
              finset_sum_biUnion_le F (fun n => extSet (w n)) (fun u => sigmaCylWeight (List.ofFn u))
                (fun u => sigmaCylWeight_nonneg _)
        _ = ∑ n ∈ F, sigmaCylWeight (w n) :=
              Finset.sum_congr rfl fun n hn => hext_sum (w n) (Finset.le_sup (f := fun m => (w m).length) hn)
    have hF_sum_term : ∑ n ∈ F, (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ beta).toReal ≤ S.toReal := by
      have hle_enn : ∑ n ∈ F, (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ beta) ≤ S :=
        ENNReal.sum_le_tsum F
      have hfin : ∀ n ∈ F, (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ beta) ≠ ⊤ := fun n hn =>
        ne_top_of_le_ne_top hStop
          (le_trans (Finset.single_le_sum
            (f := fun m => ⨆ _ : (t m).Nonempty, Metric.ediam (t m) ^ beta)
            (fun _ _ => bot_le) hn) hle_enn)
      rw [← ENNReal.toReal_sum hfin]
      exact ENNReal.toReal_mono hStop hle_enn
    have hF_sum_eps : ∑ n ∈ F, ε / (2 : ℝ) ^ (n + 1) ≤ ε := by
      set M := F.sup id + 1
      have hsubM : F ⊆ Finset.range M := fun n hn =>
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
      have h1 : ∑ n ∈ F, ε / (2 : ℝ) ^ (n + 1) ≤ ∑ n ∈ Finset.range M, ε / (2 : ℝ) ^ (n + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubM fun _ _ _ => by positivity
      have h2 : ∑ n ∈ Finset.range M, ε / (2 : ℝ) ^ (n + 1) =
          (ε / 2) * ∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ n := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [pow_succ', one_div, inv_pow]; ring
      have hgeom : ∑ n ∈ Finset.range M, (1 / 2 : ℝ) ^ n ≤ 2 := by
        rw [geom_sum_eq (by norm_num)]
        have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ M := by positivity
        have heq : ((1 / 2 : ℝ) ^ M - 1) / (1 / 2 - 1) = 2 * (1 - (1 / 2 : ℝ) ^ M) := by ring
        rw [heq]; linarith
      nlinarith
    calc (1 : ℝ) ≤ ∑ n ∈ F, sigmaCylWeight (w n) := h1_le_F
      _ ≤ ∑ n ∈ F, (2 * aStar * (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ beta).toReal +
            ε / 2 ^ (n + 1)) := Finset.sum_le_sum fun n _ => hw_wt n
      _ = 2 * aStar * (∑ n ∈ F, (⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ beta).toReal) +
            ∑ n ∈ F, ε / (2 : ℝ) ^ (n + 1) := by rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 2 * aStar * S.toReal + ε := by nlinarith
  · -- Upper bound via `hausdorffMeasure_le_liminf_sum` on level-`h` valid cylinders.
    have hr_tend : Filter.Tendsto (fun h : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (-(h : ℤ))))
        Filter.atTop (nhds 0) := by
      have hR : Filter.Tendsto (fun h : ℕ => ((1 / 2 : ℝ) ^ h)) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have heq : (fun h : ℕ => ENNReal.ofReal ((2 : ℝ) ^ (-(h : ℤ)))) =
          (fun h : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ h)) := by
        ext h; rw [zpow_neg, zpow_natCast, one_div, inv_pow]
      rw [heq]
      have h0 : ENNReal.ofReal (0 : ℝ) = 0 := ENNReal.ofReal_zero
      rw [← h0]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp hR
    have hlim := Measure.hausdorffMeasure_le_liminf_sum (d := beta) (s := SigmaSet)
      (ι := fun h => {u : Fin h → Bool // u ∈ validWords .S0 h})
      (r := fun h => ENNReal.ofReal ((2 : ℝ) ^ (-(h : ℤ)))) hr_tend
      (t := fun h u => cylSet (List.ofFn u.1))
      (Filter.Eventually.of_forall fun h u => by simpa using cylSet_ediam_le (List.ofFn u.1))
      (Filter.Eventually.of_forall fun h x hx => by
        rw [Set.mem_iUnion]
        let u : Fin h → Bool := fun i => x.bit i.val
        have hu : u ∈ validWords .S0 h := by
          simp only [validWords, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (mem_SigmaSet_iff_autoRun x).mp hx h
        refine ⟨⟨u, hu⟩, fun i => ?_⟩
        simp [u])
    refine hlim.trans ?_
    refine Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun h => ?_)
    have hsum_le : (∑ u : {u : Fin h → Bool // u ∈ validWords .S0 h},
        Metric.ediam (cylSet (List.ofFn u.1)) ^ beta) ≤
        ((validWords .S0 h).card : ℝ≥0∞) * ENNReal.ofReal (aStar ^ h) := by
      calc (∑ u : {u : Fin h → Bool // u ∈ validWords .S0 h},
            Metric.ediam (cylSet (List.ofFn u.1)) ^ beta)
          ≤ ∑ _u : {u : Fin h → Bool // u ∈ validWords .S0 h},
              ENNReal.ofReal ((2 : ℝ) ^ (-(h : ℤ))) ^ beta := by
              refine Finset.sum_le_sum fun u _ =>
                ENNReal.rpow_le_rpow (by simpa using cylSet_ediam_le (List.ofFn u.1)) hbeta_pos.le
        _ = ((validWords .S0 h).card : ℝ≥0∞) * ENNReal.ofReal (aStar ^ h) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
                  ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (-(h : ℤ))),
                  two_zpow_neg_rpow_beta]
    refine hsum_le.trans ?_
    have hcnt := (countSurvives_bounds h).2.1
    rw [countSurvives_eq_validWords (r := 1) (s := .S0) (by decide) h] at hcnt
    have hprod : ((validWords .S0 h).card : ℝ) * aStar ^ h ≤ (2 * aStar ^ 3)⁻¹ := by
      calc ((validWords .S0 h).card : ℝ) * aStar ^ h
          ≤ ((2 * aStar ^ 3)⁻¹ * (aStar ^ h)⁻¹) * aStar ^ h :=
            mul_le_mul_of_nonneg_right hcnt (by positivity)
        _ = (2 * aStar ^ 3)⁻¹ := by field_simp
    have hcast : ((validWords .S0 h).card : ℝ≥0∞) * ENNReal.ofReal (aStar ^ h) =
        ENNReal.ofReal (((validWords .S0 h).card : ℝ) * aStar ^ h) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    rw [hcast]
    exact ENNReal.ofReal_le_ofReal hprod

private lemma hausdorffMeasure_affine30 (r : ℕ) (s : Set ℤ_[2]) :
    μH[beta] (affine30 r '' s) = ENNReal.ofReal aStar * μH[beta] s := by
  have hbeta_pos : 0 < beta := by linarith [beta_bounds_6.1]
  have ha0 := aStar_spec.1
  have hhalf : (((2⁻¹ : ℝ≥0) : ℝ≥0∞) ^ beta) = ENNReal.ofReal aStar := by
    have h1 : ((2⁻¹ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (2⁻¹ : ℝ) := by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num
    rw [h1, ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹),
        Real.inv_rpow (by norm_num), two_rpow_beta, one_div, inv_inv]
  have htwo : (((2 : ℝ≥0) : ℝ≥0∞) ^ beta) = ENNReal.ofReal (1 / aStar) := by
    have h1 : ((2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
    rw [h1, ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)), two_rpow_beta]
  apply le_antisymm
  · have h := (affine30_lipschitz r).hausdorffMeasure_image_le hbeta_pos.le s
    rwa [hhalf] at h
  · have h := (affine30_antilipschitz r).le_hausdorffMeasure_image hbeta_pos.le s
    rw [htwo] at h
    calc ENNReal.ofReal aStar * μH[beta] s
        ≤ ENNReal.ofReal aStar * (ENNReal.ofReal (1 / aStar) * μH[beta] (affine30 r '' s)) := by
          gcongr
      _ = (ENNReal.ofReal aStar * ENNReal.ofReal (1 / aStar)) * μH[beta] (affine30 r '' s) := by
          rw [mul_assoc]
      _ = μH[beta] (affine30 r '' s) := by
          rw [← ENNReal.ofReal_mul ha0.le, mul_one_div_cancel ha0.ne', ENNReal.ofReal_one, one_mul]

private lemma hausdorffMeasure_prepend3 (p : List Bool) (hp : p.length = 3) (s : Set BitSeq) :
    μH[beta] (prependBits p '' s) ≤ ENNReal.ofReal (aStar ^ 3) * μH[beta] s := by
  have hbeta_pos : 0 < beta := by linarith [beta_bounds_6.1]
  have hlip : LipschitzWith (8⁻¹ : ℝ≥0) (prependBits p) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [prependBits_dist, hp]
    norm_num
  have h8 : (((8⁻¹ : ℝ≥0) : ℝ≥0∞) ^ beta) = ENNReal.ofReal (aStar ^ 3) := by
    have h1 : ((8⁻¹ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ (-((3 : ℕ) : ℤ))) := by
      have : (2 : ℝ) ^ (-((3 : ℕ) : ℤ)) = (8 : ℝ)⁻¹ := by norm_num
      rw [this, ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num
    rw [h1, ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (-((3 : ℕ) : ℤ))),
        two_zpow_neg_rpow_beta 3]
  have h := hlip.hausdorffMeasure_image_le hbeta_pos.le s
  rwa [h8] at h

/-- Theorem `thm:cantor` (Part 2d): `1/2 ≤ μH[β](closure B_1) ≤ a^{-2} + a < 3.031`. -/
theorem hausdorffMeasure_closure_B1Padic_bounds :
    ENNReal.ofReal (1 / 2) ≤ μH[beta] (closure B1Padic) ∧
    μH[beta] (closure B1Padic) ≤ ENNReal.ofReal (aStar⁻¹ ^ 2 + aStar) ∧
    μH[beta] (closure B1Padic) < ENNReal.ofReal (3031 / 1000) := by
  have ha0 := aStar_spec.1
  have hbeta_pos : 0 < beta := by linarith [beta_bounds_6.1]
  obtain ⟨hSig_lo, hSig_hi⟩ := hausdorffMeasure_SigmaSet_bounds
  have hK1 : μH[beta] (KCal 1) = μH[beta] SigmaSet := by
    rw [← psiMap_image_KCal_1_17 (Or.inl rfl),
        (psiMap_isometry 1).hausdorffMeasure_image (Or.inl hbeta_pos.le)]
  have hK17 : μH[beta] (KCal 17) = μH[beta] SigmaSet := by
    rw [← psiMap_image_KCal_1_17 (Or.inr rfl),
        (psiMap_isometry 17).hausdorffMeasure_image (Or.inl hbeta_pos.le)]
  have hK15 : μH[beta] (KCal 15) ≤ ENNReal.ofReal (2 * aStar ^ 3) * μH[beta] SigmaSet := by
    rw [← (psiMap_isometry 15).hausdorffMeasure_image (Or.inl hbeta_pos.le),
        psiMap_image_KCal_15, Sigma15Set]
    refine (measure_union_le _ _).trans ?_
    have h0 := hausdorffMeasure_prepend3 [false, false, false] rfl SigmaSet
    have h1 := hausdorffMeasure_prepend3 [false, false, true] rfl SigmaSet
    calc μH[beta] (prependBits [false, false, false] '' SigmaSet) +
            μH[beta] (prependBits [false, false, true] '' SigmaSet)
        ≤ ENNReal.ofReal (aStar ^ 3) * μH[beta] SigmaSet +
            ENNReal.ofReal (aStar ^ 3) * μH[beta] SigmaSet := add_le_add h0 h1
      _ = (ENNReal.ofReal (aStar ^ 3) + ENNReal.ofReal (aStar ^ 3)) * μH[beta] SigmaSet := by
            rw [add_mul]
      _ = ENNReal.ofReal (2 * aStar ^ 3) * μH[beta] SigmaSet := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity), two_mul]
  have hlo : ENNReal.ofReal (1 / 2) ≤ μH[beta] (closure B1Padic) := by
    have hsub : affine30 1 '' KCal 1 ⊆ closure B1Padic := by
      rw [closure_B1Padic_eq]
      exact Set.subset_union_of_subset_left Set.subset_union_left _
    calc ENNReal.ofReal (1 / 2)
        = ENNReal.ofReal aStar * ENNReal.ofReal ((2 * aStar)⁻¹) := by
            rw [← ENNReal.ofReal_mul ha0.le]
            congr 1; field_simp
      _ ≤ ENNReal.ofReal aStar * μH[beta] SigmaSet := by gcongr
      _ = μH[beta] (affine30 1 '' KCal 1) := by rw [hausdorffMeasure_affine30, hK1]
      _ ≤ μH[beta] (closure B1Padic) := measure_mono hsub
  have hhi : μH[beta] (closure B1Padic) ≤ ENNReal.ofReal (aStar⁻¹ ^ 2 + aStar) := by
    rw [closure_B1Padic_eq]
    have hsub1 := measure_union_le (μ := μH[beta])
      (affine30 1 '' KCal 1 ∪ affine30 15 '' KCal 15) (affine30 17 '' KCal 17)
    have hsub2 := measure_union_le (μ := μH[beta])
      (affine30 1 '' KCal 1) (affine30 15 '' KCal 15)
    have hu : μH[beta] (affine30 1 '' KCal 1 ∪ affine30 15 '' KCal 15 ∪ affine30 17 '' KCal 17) ≤
        μH[beta] (affine30 1 '' KCal 1) + μH[beta] (affine30 15 '' KCal 15) +
          μH[beta] (affine30 17 '' KCal 17) :=
      hsub1.trans (add_le_add hsub2 le_rfl)
    refine hu.trans ?_
    rw [hausdorffMeasure_affine30, hausdorffMeasure_affine30, hausdorffMeasure_affine30, hK1, hK17]
    have h15_bound : ENNReal.ofReal aStar * μH[beta] (KCal 15) ≤
        ENNReal.ofReal aStar * (ENNReal.ofReal (2 * aStar ^ 3) * μH[beta] SigmaSet) := by gcongr
    have hsum_le : ENNReal.ofReal aStar * μH[beta] SigmaSet +
          ENNReal.ofReal aStar * μH[beta] (KCal 15) +
          ENNReal.ofReal aStar * μH[beta] SigmaSet ≤
        ENNReal.ofReal (2 * aStar + 2 * aStar ^ 4) * μH[beta] SigmaSet := by
      have hrew : ENNReal.ofReal aStar * (ENNReal.ofReal (2 * aStar ^ 3) * μH[beta] SigmaSet) =
          ENNReal.ofReal (2 * aStar ^ 4) * μH[beta] SigmaSet := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul ha0.le]
        congr 2; ring
      calc ENNReal.ofReal aStar * μH[beta] SigmaSet +
            ENNReal.ofReal aStar * μH[beta] (KCal 15) +
            ENNReal.ofReal aStar * μH[beta] SigmaSet
          ≤ ENNReal.ofReal aStar * μH[beta] SigmaSet +
            ENNReal.ofReal (2 * aStar ^ 4) * μH[beta] SigmaSet +
            ENNReal.ofReal aStar * μH[beta] SigmaSet :=
              add_le_add (add_le_add le_rfl (h15_bound.trans_eq hrew)) le_rfl
        _ = (ENNReal.ofReal aStar + ENNReal.ofReal (2 * aStar ^ 4) + ENNReal.ofReal aStar) *
              μH[beta] SigmaSet := by ring
        _ = ENNReal.ofReal (2 * aStar + 2 * aStar ^ 4) * μH[beta] SigmaSet := by
              rw [← ENNReal.ofReal_add ha0.le (by positivity),
                  ← ENNReal.ofReal_add (by positivity) ha0.le]
              congr 2; ring
    refine hsum_le.trans ?_
    calc ENNReal.ofReal (2 * aStar + 2 * aStar ^ 4) * μH[beta] SigmaSet
        ≤ ENNReal.ofReal (2 * aStar + 2 * aStar ^ 4) * ENNReal.ofReal ((2 * aStar ^ 3)⁻¹) := by
          gcongr
      _ = ENNReal.ofReal (aStar⁻¹ ^ 2 + aStar) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp
  have hlt : μH[beta] (closure B1Padic) < ENNReal.ofReal (3031 / 1000) :=
    lt_of_le_of_lt hhi ((ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr aStar_hausdorff_ub_lt)
  exact ⟨hlo, hhi, hlt⟩

/-- Theorem `thm:cantor` (Part 2e): exact `2`-adic Hausdorff dimension `dimH (closure B_1) = β`. -/
theorem dimH_closure_B1Padic : dimH (closure B1Padic) = ENNReal.ofReal beta := by
  have hbeta_pos : 0 < beta := by linarith [beta_bounds_6.1]
  obtain ⟨hlo, _, hlt⟩ := hausdorffMeasure_closure_B1Padic_bounds
  let d : ℝ≥0 := ⟨beta, hbeta_pos.le⟩
  have hd_coe : (d : ℝ) = beta := rfl
  have hne0 : μH[(d : ℝ)] (closure B1Padic) ≠ 0 := by
    rw [hd_coe]
    intro h0
    rw [h0] at hlo
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 2) := ENNReal.ofReal_pos.mpr (by norm_num)
    exact not_lt_of_ge hlo hpos
  have hnetop : μH[(d : ℝ)] (closure B1Padic) ≠ ⊤ := by
    rw [hd_coe]
    exact ne_top_of_lt (lt_trans hlt ENNReal.ofReal_lt_top)
  have hdim := dimH_of_hausdorffMeasure_ne_zero_ne_top hne0 hnetop
  rw [hdim]
  exact (ENNReal.ofReal_eq_coe_nnreal hbeta_pos.le).symm

/-! ### Textbook box-counting dimension (`dim_B`) -/

/-- Minimum number of subsets of diameter `≤ ε` required to cover `s` (Falconer Def. 3.1(i)). -/
noncomputable def boxCoverNum {X : Type*} [PseudoEMetricSpace X] (s : Set X) (ε : ℝ) : ℕ :=
  sInf {N : ℕ | ∃ F : Finset (Set X), F.card = N ∧ s ⊆ ⋃ U ∈ F, U ∧
    ∀ U ∈ F, Metric.ediam U ≤ ENNReal.ofReal ε}

/-- Exact box-counting (Minkowski) dimension: `lim_{ε → 0^+} log N(s, ε) / log(1 / ε) = d`. -/
def HasBoxDim {X : Type*} [PseudoEMetricSpace X] (s : Set X) (d : ℝ) : Prop :=
  Filter.Tendsto (fun ε : ℝ => Real.log (boxCoverNum s ε : ℝ) / Real.log (1 / ε))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds d)

/-- General scale-count criterion for box-counting dimension (reusable in any metric space). -/
lemma hasBoxDim_of_scale_bounds {X : Type*} [PseudoEMetricSpace X] {s : Set X}
    {b θ C₁ C₂ : ℝ} (hb : 1 < b) (hθ : 1 ≤ θ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hbounds : ∀ ε : ℝ, 0 < ε → ε < 1 / b →
      let k : ℕ := Nat.floor (Real.log (1 / ε) / Real.log b)
      C₁ * θ ^ k ≤ (boxCoverNum s ε : ℝ) ∧ (boxCoverNum s ε : ℝ) ≤ C₂ * θ ^ k) :
    HasBoxDim s (Real.log θ / Real.log b) := by
  unfold HasBoxDim
  have hlogb_pos : 0 < Real.log b := Real.log_pos hb
  have hlogθ_nn : 0 ≤ Real.log θ := Real.log_nonneg hθ
  have hlog_inv_top : Filter.Tendsto (fun ε : ℝ => Real.log (1 / ε))
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    have hinv : Filter.Tendsto (fun ε : ℝ => (1 / ε : ℝ)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
      simpa only [one_div] using tendsto_inv_nhdsGT_zero
    exact Real.tendsto_log_atTop.comp hinv
  have hdiv_zero : ∀ C : ℝ, Filter.Tendsto (fun ε : ℝ => C / Real.log (1 / ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := fun C =>
    tendsto_const_nhds.div_atTop hlog_inv_top
  let loFn : ℝ → ℝ := fun ε =>
    Real.log θ / Real.log b + (Real.log C₁ - Real.log θ) / Real.log (1 / ε)
  let hiFn : ℝ → ℝ := fun ε =>
    Real.log θ / Real.log b + Real.log C₂ / Real.log (1 / ε)
  have hlo_tend : Filter.Tendsto loFn (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log θ / Real.log b)) := by
    simpa [loFn] using tendsto_const_nhds.add (hdiv_zero (Real.log C₁ - Real.log θ))
  have hhi_tend : Filter.Tendsto hiFn (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log θ / Real.log b)) := by
    simpa [hiFn] using tendsto_const_nhds.add (hdiv_zero (Real.log C₂))
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      loFn ε ≤ Real.log (boxCoverNum s ε : ℝ) / Real.log (1 / ε) ∧
      Real.log (boxCoverNum s ε : ℝ) / Real.log (1 / ε) ≤ hiFn ε := by
    have hmem : Set.Ioo (0 : ℝ) (1 / b) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      Ioo_mem_nhdsGT (by positivity)
    filter_upwards [hmem] with ε ⟨hε0, hεb⟩
    have h1ε_gt_b : b < 1 / ε := by rw [lt_div_iff₀ hε0]; nlinarith [div_mul_cancel₀ (1 : ℝ) (by linarith : b ≠ 0)]
    have hlog_gt : Real.log b < Real.log (1 / ε) := Real.log_lt_log (by linarith) h1ε_gt_b
    have hlog_pos : 0 < Real.log (1 / ε) := lt_trans hlogb_pos hlog_gt
    set k : ℕ := Nat.floor (Real.log (1 / ε) / Real.log b)
    have hk_le : (k : ℝ) ≤ Real.log (1 / ε) / Real.log b :=
      Nat.floor_le (div_nonneg hlog_pos.le hlogb_pos.le)
    have hlt_k1 : Real.log (1 / ε) / Real.log b < (k : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    obtain ⟨hblo, hbhi⟩ := hbounds ε hε0 hεb
    have hθk_pos : 0 < θ ^ k := by positivity
    have hN_pos : 0 < (boxCoverNum s ε : ℝ) := lt_of_lt_of_le (mul_pos hC₁ hθk_pos) hblo
    have hlog_lo : Real.log C₁ + (k : ℝ) * Real.log θ ≤ Real.log (boxCoverNum s ε : ℝ) := by
      have h := Real.log_le_log (mul_pos hC₁ hθk_pos) hblo
      rwa [Real.log_mul hC₁.ne' hθk_pos.ne', Real.log_pow] at h
    have hlog_hi : Real.log (boxCoverNum s ε : ℝ) ≤ Real.log C₂ + (k : ℝ) * Real.log θ := by
      have h := Real.log_le_log hN_pos hbhi
      rwa [Real.log_mul hC₂.ne' hθk_pos.ne', Real.log_pow] at h
    constructor
    · dsimp only [loFn]
      have hk_lo : (Real.log (1 / ε) / Real.log b - 1) * Real.log θ ≤ (k : ℝ) * Real.log θ :=
        mul_le_mul_of_nonneg_right (by linarith) hlogθ_nn
      have hnum : (Real.log θ / Real.log b) * Real.log (1 / ε) + (Real.log C₁ - Real.log θ) ≤
          Real.log (boxCoverNum s ε : ℝ) := by
        have hrew : (Real.log (1 / ε) / Real.log b - 1) * Real.log θ =
            (Real.log θ / Real.log b) * Real.log (1 / ε) - Real.log θ := by ring
        linarith
      rw [← mul_div_cancel_right₀ (Real.log θ / Real.log b) hlog_pos.ne', ← add_div]
      exact div_le_div_of_nonneg_right hnum hlog_pos.le
    · dsimp only [hiFn]
      have hk_hi : (k : ℝ) * Real.log θ ≤ (Real.log (1 / ε) / Real.log b) * Real.log θ :=
        mul_le_mul_of_nonneg_right hk_le hlogθ_nn
      have hnum : Real.log (boxCoverNum s ε : ℝ) ≤
          (Real.log θ / Real.log b) * Real.log (1 / ε) + Real.log C₂ := by
        have hrew : (Real.log (1 / ε) / Real.log b) * Real.log θ =
            (Real.log θ / Real.log b) * Real.log (1 / ε) := by ring
        linarith
      rw [← mul_div_cancel_right₀ (Real.log θ / Real.log b) hlog_pos.ne', ← add_div]
      exact div_le_div_of_nonneg_right hnum hlog_pos.le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo_tend hhi_tend
    (hev.mono fun _ h => h.1) (hev.mono fun _ h => h.2)

/-- Theorem `thm:cantor` (Part 2f): exact `2`-adic box-counting dimension `dim_B (closure B_1) = β`. -/
theorem hasBoxDim_closure_B1Padic : HasBoxDim (closure B1Padic) beta := by
  classical
  have ha0 := aStar_spec.1
  have ha1 := aStar_spec.2.1
  have h1a : 0 < 1 - aStar := aStar_denom_pos.1
  have hbeta_eq : beta = Real.log (1 / aStar) / Real.log 2 := rfl
  rw [hbeta_eq]
  refine hasBoxDim_of_scale_bounds (b := 2) (θ := 1 / aStar) (C₁ := 1 / 2)
    (C₂ := (1 + aStar) / (1 - aStar)) (by norm_num) (by rw [one_le_div ha0]; exact ha1.le)
    (by norm_num) (by positivity) fun ε hε0 hεhalf => ?_
  set k : ℕ := Nat.floor (Real.log (1 / ε) / Real.log 2)
  have h1ε_gt2 : (2 : ℝ) < 1 / ε := by rw [lt_div_iff₀ hε0]; linarith
  have hk_ge1 : 1 ≤ k := by
    rw [Nat.one_le_floor_iff, one_le_div (Real.log_pos (by norm_num))]
    exact (Real.log_lt_log (by norm_num) h1ε_gt2).le
  have hk_le : (k : ℝ) ≤ Real.log (1 / ε) / Real.log 2 :=
    Nat.floor_le (div_nonneg (Real.log_nonneg (by linarith)) (Real.log_pos (by norm_num)).le)
  have hlt_k1 : Real.log (1 / ε) / Real.log 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hε_hi : ε ≤ (2 : ℝ) ^ (-(k : ℤ)) := by
    have hlog : (k : ℝ) * Real.log 2 ≤ Real.log (1 / ε) :=
      (le_div_iff₀ (Real.log_pos (by norm_num))).mp hk_le
    have hexp : (2 : ℝ) ^ k ≤ 1 / ε := by
      have := Real.exp_le_exp.mpr hlog
      rw [Real.exp_log (by positivity), mul_comm, Real.exp_mul, Real.exp_log (by norm_num),
          Real.rpow_natCast] at this
      exact this
    rw [zpow_neg, zpow_natCast, ← one_div, le_div_iff₀ (by positivity)]
    have h1 : (2 : ℝ) ^ k * ε ≤ 1 := (le_div_iff₀ hε0).mp hexp
    linarith
  have hε_lo : (2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) < ε := by
    have hlog : Real.log (1 / ε) < ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
      have := (div_lt_iff₀ (Real.log_pos (by norm_num))).mp hlt_k1
      push_cast; linarith
    have hexp : 1 / ε < (2 : ℝ) ^ (k + 1) := by
      have := Real.exp_lt_exp.mpr hlog
      rw [Real.exp_log (by positivity), mul_comm, Real.exp_mul, Real.exp_log (by norm_num),
          Real.rpow_natCast] at this
      exact this
    rw [zpow_neg, zpow_natCast, ← one_div, div_lt_iff₀ (by positivity)]
    have h1 : 1 < (2 : ℝ) ^ (k + 1) * ε := by
      have := (div_lt_iff₀ hε0).mp hexp; linarith
    linarith
  -- Construct an explicit finite cover of `closure B1Padic` of size ≤ N_k(1) + N_k(15) + N_k(17).
  let ballOf (r k₀ : ℕ) : Set ℤ_[2] :=
    affine30 r '' {y : ℤ_[2] | y.appr k = k₀}
  have hdiam_ball : ∀ r k₀ : ℕ, Metric.ediam (ballOf r k₀) ≤ ENNReal.ofReal ε := by
    intro r k₀
    rw [Metric.ediam_le_iff]
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
    rw [edist_dist, affine30_dist, dist_eq_norm]
    have hy12 : ‖y₁ - y₂‖ ≤ (2 : ℝ) ^ (-(k : ℤ)) :=
      (padic2_norm_le_iff_appr_eq y₁ y₂ k).mpr (hy₁.trans hy₂.symm)
    have hhalf : (1 / 2 : ℝ) * ‖y₁ - y₂‖ ≤ (2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
      have heq : (2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) = (1 / 2 : ℝ) * (2 : ℝ) ^ (-(k : ℤ)) := by
        rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ', mul_inv]; ring
      rw [heq]; linarith
    exact ENNReal.ofReal_le_ofReal (le_trans hhalf hε_lo.le)
  let S (r : ℕ) : Finset (Set ℤ_[2]) :=
    ((Finset.range (2 ^ k)).filter (fun k₀ => Survives r k k₀)).image (ballOf r)
  let Fcov : Finset (Set ℤ_[2]) := S 1 ∪ S 15 ∪ S 17
  have hcov_spec : closure B1Padic ⊆ ⋃ U ∈ Fcov, U := by
    intro x hx
    rw [closure_B1Padic_eq] at hx
    have hmem : ∀ r : ℕ, x ∈ affine30 r '' KCal r → x ∈ ⋃ U ∈ S r, U := by
      rintro r ⟨y, hy, rfl⟩
      rw [Set.mem_iUnion₂]
      refine ⟨ballOf r (y.appr k), ?_, ⟨y, rfl, rfl⟩⟩
      exact Finset.mem_image.mpr ⟨y.appr k,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (PadicInt.appr_lt y k), hy k⟩, rfl⟩
    rcases hx with (h1 | h15) | h17
    · exact Set.biUnion_subset_biUnion_left
        (Finset.subset_union_left.trans Finset.subset_union_left) (hmem 1 h1)
    · exact Set.biUnion_subset_biUnion_left
        (Finset.subset_union_right.trans Finset.subset_union_left) (hmem 15 h15)
    · exact Set.biUnion_subset_biUnion_left Finset.subset_union_right (hmem 17 h17)
  have hdiam_Fcov : ∀ U ∈ Fcov, Metric.ediam U ≤ ENNReal.ofReal ε := by
    intro U hU
    simp only [Fcov, S, Finset.mem_union, Finset.mem_image] at hU
    rcases hU with (⟨k₀, _, rfl⟩ | ⟨k₀, _, rfl⟩) | ⟨k₀, _, rfl⟩ <;> exact hdiam_ball _ k₀
  have hnonempty : {N : ℕ | ∃ F : Finset (Set ℤ_[2]), F.card = N ∧ closure B1Padic ⊆ ⋃ U ∈ F, U ∧
      ∀ U ∈ F, Metric.ediam U ≤ ENNReal.ofReal ε}.Nonempty :=
    ⟨Fcov.card, Fcov, rfl, hcov_spec, hdiam_Fcov⟩
  constructor
  · -- Lower bound: `N_{k - 1}(1) ≤ boxCoverNum (closure B1Padic) ε`.
    have hnat_lo : countSurvives 1 (k - 1) ≤ boxCoverNum (closure B1Padic) ε := by
      unfold boxCoverNum
      refine le_csInf hnonempty ?_
      rintro N ⟨F, rfl, hFcov, hFdiam⟩
      -- For every surviving k₀ < 2^(k-1), choose a point y(k₀) ∈ KCal 1 with y.appr (k-1) = k₀.
      let survFin : Finset ℕ := (Finset.range (2 ^ (k - 1))).filter (fun k₀ => Survives 1 (k - 1) k₀)
      have hex_pt : ∀ k₀ ∈ survFin, ∃ y ∈ KCal 1, y.appr (k - 1) = k₀ := by
        intro k₀ hk₀
        simp only [survFin, Finset.mem_filter, Finset.mem_range] at hk₀
        let w : List Bool := List.ofFn (fun i : Fin (k - 1) => (psiMap 1 (k₀ : ℤ_[2])).bit i.val)
        have hrun : (autoRun .S0 w).isSome := by
          have h1 := resToAutoState_T_iter 1 (k - 1) (k₀ : ℤ_[2])
          have hres1 : resToAutoState 1 = some .S0 := by decide
          rw [hres1, Option.bind_some, padic2_appr_natCast, Nat.mod_eq_of_lt hk₀.1] at h1
          rw [← h1, resToAutoState_isSome_iff]
          exact (survives_iff_InS30 (by unfold InS30; omega) (k - 1) k₀).mp hk₀.2
        obtain ⟨z, hz_sig, hz_cyl⟩ := exists_mem_SigmaSet_of_autoRun hrun
        obtain ⟨y, hy_psi⟩ := psiMap_surjective 1 z
        have hy_cal : y ∈ KCal 1 := by
          have hmem : psiMap 1 y ∈ psiMap 1 '' KCal 1 := by
            rw [psiMap_image_KCal_1_17 (Or.inl rfl), hy_psi]; exact hz_sig
          obtain ⟨y', hy', heq⟩ := hmem
          have : y = y' := (psiMap_isometry 1).injective heq.symm
          rwa [this]
        have hy_appr : y.appr (k - 1) = k₀ := by
          have hd : dist (psiMap 1 y) (psiMap 1 (k₀ : ℤ_[2])) ≤ (2 : ℝ) ^ (-((k - 1 : ℕ) : ℤ)) :=
            bitSeq_dist_le_of_eq (k - 1) fun j hj => by
              rw [hy_psi]
              have := hz_cyl ⟨j, by simp [w]; exact hj⟩
              simpa [w] using this
          rw [isometry_iff_dist_eq.mp (psiMap_isometry 1), dist_eq_norm] at hd
          have hap := (padic2_norm_le_iff_appr_eq y (k₀ : ℤ_[2]) (k - 1)).mp hd
          rwa [padic2_appr_natCast, Nat.mod_eq_of_lt hk₀.1] at hap
        exact ⟨y, hy_cal, hy_appr⟩
      choose pt hpt_cal hpt_appr using hex_pt
      -- Map each k₀ ∈ survFin to some U ∈ F containing affine30 1 (pt k₀ ...).
      have hmap_ex : ∀ k₀ (hk₀ : k₀ ∈ survFin), ∃ U ∈ F, affine30 1 (pt k₀ hk₀) ∈ U := by
        intro k₀ hk₀
        have hmem : affine30 1 (pt k₀ hk₀) ∈ closure B1Padic := by
          rw [closure_B1Padic_eq]
          exact Set.mem_union_left _ (Set.mem_union_left _ ⟨pt k₀ hk₀, hpt_cal k₀ hk₀, rfl⟩)
        obtain ⟨U, hUF, hUmem⟩ := Set.mem_iUnion₂.mp (hFcov hmem)
        exact ⟨U, hUF, hUmem⟩
      let assign : ℕ → Set ℤ_[2] := fun k₀ =>
        if h : k₀ ∈ survFin then (hmap_ex k₀ h).choose else ∅
      have hinj : Set.InjOn assign survFin := by
        intro a ha b hb heq
        have ha' : a ∈ survFin := Finset.mem_coe.mp ha
        have hb' : b ∈ survFin := Finset.mem_coe.mp hb
        by_contra hne
        set U := assign a
        have hUa : U ∈ F ∧ affine30 1 (pt a ha') ∈ U := by
          simp only [U, assign, ha', ↓reduceDIte]; exact (hmap_ex a ha').choose_spec
        have hUb : affine30 1 (pt b hb') ∈ U := by
          have : U = assign b := heq
          rw [this]; simp only [assign, hb', ↓reduceDIte]; exact (hmap_ex b hb').choose_spec.2
        have hdist_le : dist (affine30 1 (pt a ha')) (affine30 1 (pt b hb')) ≤ ε := by
          have hed := (Metric.edist_le_ediam_of_mem hUa.2 hUb).trans (hFdiam U hUa.1)
          rw [edist_dist] at hed
          exact (ENNReal.ofReal_le_ofReal_iff hε0.le).mp hed
        have hnorm_gt : (2 : ℝ) ^ (-((k - 1 : ℕ) : ℤ)) < ‖pt a ha' - pt b hb'‖ := by
          by_contra hle; push Not at hle
          have hap := (padic2_norm_le_iff_appr_eq (pt a ha') (pt b hb') (k - 1)).mp hle
          rw [hpt_appr a ha', hpt_appr b hb'] at hap
          exact hne hap
        have hdist_gt : (2 : ℝ) ^ (-(k : ℤ)) < dist (affine30 1 (pt a ha')) (affine30 1 (pt b hb')) := by
          rw [affine30_dist, dist_eq_norm]
          have hpow : (2 : ℝ) ^ (-(k : ℤ)) = (1 / 2 : ℝ) * (2 : ℝ) ^ (-((k - 1 : ℕ) : ℤ)) := by
            have hk1 : (k : ℤ) = ((k - 1 : ℕ) : ℤ) + 1 := by omega
            rw [hk1, neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; norm_num; ring
          rw [hpow]; linarith
        linarith
      have hmaps : Set.MapsTo assign survFin F := fun a ha => by
        have ha' : a ∈ survFin := Finset.mem_coe.mp ha
        simp only [assign, ha', ↓reduceDIte]
        exact Finset.mem_coe.mpr (hmap_ex a ha').choose_spec.1
      exact Finset.card_le_card_of_injOn assign hmaps hinj
    have hcnt := (countSurvives_bounds (k - 1)).1
    have hpow : (1 / 2 : ℝ) * (1 / aStar) ^ k = (2 * aStar)⁻¹ * (aStar ^ (k - 1))⁻¹ := by
      have hk1 : k = (k - 1) + 1 := by omega
      conv_lhs => rw [hk1, pow_succ]
      simp only [one_div, inv_pow, mul_inv]
      ring
    calc (1 / 2 : ℝ) * (1 / aStar) ^ k
        = (2 * aStar)⁻¹ * (aStar ^ (k - 1))⁻¹ := hpow
      _ ≤ (countSurvives 1 (k - 1) : ℝ) := hcnt
      _ ≤ (boxCoverNum (closure B1Padic) ε : ℝ) := by exact_mod_cast hnat_lo
  · -- Upper bound: `boxCoverNum (closure B1Padic) ε ≤ Fcov.card ≤ ((1 + a)/(1 - a)) * (1/a)^k`.
    have hnat_hi : boxCoverNum (closure B1Padic) ε ≤ Fcov.card :=
      Nat.sInf_le ⟨Fcov, rfl, hcov_spec, hdiam_Fcov⟩
    have hFcard : Fcov.card ≤ countSurvives 1 k + countSurvives 15 k + countSurvives 17 k := by
      have h1 : Fcov.card ≤ (S 1).card + (S 15).card + (S 17).card :=
        (Finset.card_union_le _ _).trans (add_le_add (Finset.card_union_le _ _) le_rfl)
      have hs : ∀ r, (S r).card ≤ countSurvives r k := fun r => Finset.card_image_le
      linarith [hs 1, hs 15, hs 17]
    obtain ⟨_, hN1, hN17, hN15⟩ := countSurvives_bounds k
    have halg : (2 * aStar ^ 3)⁻¹ + 1 + (2 * aStar ^ 3)⁻¹ = (1 + aStar) / (1 - aStar) := by
      have hq := aStar_quartic
      have h1a_ne : 1 - aStar ≠ 0 := h1a.ne'
      have ha3_ne : aStar ^ 3 ≠ 0 := by positivity
      field_simp
      nlinarith
    calc (boxCoverNum (closure B1Padic) ε : ℝ)
        ≤ (Fcov.card : ℝ) := by exact_mod_cast hnat_hi
      _ ≤ (countSurvives 1 k : ℝ) + (countSurvives 15 k : ℝ) + (countSurvives 17 k : ℝ) := by
            exact_mod_cast hFcard
      _ ≤ (2 * aStar ^ 3)⁻¹ * (aStar ^ k)⁻¹ + (aStar ^ k)⁻¹ + (2 * aStar ^ 3)⁻¹ * (aStar ^ k)⁻¹ := by
            rw [hN17]; linarith
      _ = ((2 * aStar ^ 3)⁻¹ + 1 + (2 * aStar ^ 3)⁻¹) * (1 / aStar) ^ k := by
            rw [one_div, inv_pow]; ring
      _ = (1 + aStar) / (1 - aStar) * (1 / aStar) ^ k := by rw [halg]

/-! ## Part 4: Elementary integer bounds `a_1^9 * X^γ ≤ N_1(⌊X⌋) ≤ X^β` (`thm:cantor` Part 3) -/

/-- Theorem `thm:cantor` (Part 3, lower bound for all real `X ≥ 1`): `a_1^9 * X^γ ≤ N_1(⌊X⌋)`. -/
theorem thm_cantor_lower_real (X : ℝ) (hX : 1 ≤ X) :
    a1 ^ 9 * X ^ gamma ≤ (N1 ⌊X⌋₊ : ℝ) := by
  classical
  have ha0 := a1_spec.1
  have ha1 := a1_spec.2.1
  by_cases hX32 : X < 32
  · have hfl1 : 1 ≤ ⌊X⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hX)
    have hN1 : (1 : ℝ) ≤ (N1 ⌊X⌋₊ : ℝ) := by
      have : 1 ≤ N1 ⌊X⌋₊ := by
        unfold N1
        refine Finset.card_pos.mpr ⟨1, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨le_rfl, hfl1⟩, by decide, reaches_refl f 1⟩
      exact_mod_cast this
    have hXlt : X ^ gamma ≤ (32 : ℝ) ^ gamma :=
      Real.rpow_le_rpow (by linarith) hX32.le gamma_pos.le
    have h32 : (32 : ℝ) ^ gamma = (a1 ^ 5)⁻¹ := by
      have h25 : (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) := by norm_num
      rw [h25, ← Real.rpow_natCast 2 5, ← Real.rpow_mul (by norm_num),
          mul_comm, Real.rpow_mul (by norm_num), two_rpow_gamma, Real.rpow_natCast,
          one_div, inv_pow]
    have hbound : a1 ^ 9 * (32 : ℝ) ^ gamma = a1 ^ 4 := by rw [h32]; field_simp
    have ha4 : a1 ^ 4 ≤ 1 := by
      have : a1 ^ 4 ≤ 1 ^ 4 := by gcongr
      simpa using this
    nlinarith [mul_le_mul_of_nonneg_left hXlt (show 0 ≤ a1 ^ 9 by positivity)]
  · push Not at hX32
    set N := ⌊X⌋₊
    have hN32 : 32 ≤ N := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hX32)
    set M := Nat.log 2 N
    have hM5 : 5 ≤ M := (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by omega)
    have h2M_le : 2 ^ M ≤ N := Nat.pow_log_le_self 2 (by omega)
    have hN_lt : N < 2 ^ (M + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
    have hX_lt : X < (2 : ℝ) ^ (M + 1 : ℕ) := by
      have h1 : X < (N : ℝ) + 1 := Nat.lt_floor_add_one X
      have h2 : (N : ℝ) + 1 ≤ (2 : ℝ) ^ (M + 1 : ℕ) := by exact_mod_cast hN_lt
      linarith
    have hcard_le : (UList (M - 4)).card ≤ N1 N := by
      unfold N1
      refine Finset.card_le_card_of_injOn (fun l => chainVal (add4Last l)) ?_ ?_
      · intro l hl
        obtain ⟨hmod, hsum, hne⟩ := UList_props (M - 4) l hl
        obtain ⟨hvt, hsum'⟩ := add4Last_valid (hne (by omega)) hmod
        obtain ⟨h30, hgt1, hreach, hlt2⟩ := chainVal_props hvt
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
        have hsumM : (add4Last l).sum = M := by omega
        rw [hsumM] at hlt2
        exact ⟨⟨by omega, by omega⟩, by omega, hreach⟩
      · intro a ha b hb h
        obtain ⟨hmoda, _, hnea⟩ := UList_props (M - 4) a ha
        obtain ⟨hmodb, _, hneb⟩ := UList_props (M - 4) b hb
        have hvta := (add4Last_valid (hnea (by omega)) hmoda).1
        have hvtb := (add4Last_valid (hneb (by omega)) hmodb).1
        exact add4Last_inj (chainVal_inj hvta hvtb h)
    have hU : a1 ^ (4 : ℤ) * (a1 ^ (M - 4))⁻¹ ≤ (N1 N : ℝ) := by
      calc a1 ^ (4 : ℤ) * (a1 ^ (M - 4))⁻¹
          ≤ (URec (M - 4) : ℝ) := URec_lower (M - 4)
        _ = ((UList (M - 4)).card : ℝ) := by rw [UList_card]
        _ ≤ (N1 N : ℝ) := by exact_mod_cast hcard_le
    have hXpow : X ^ gamma ≤ ((2 : ℝ) ^ ((M + 1 : ℕ) : ℝ)) ^ gamma := by
      calc X ^ gamma ≤ ((2 : ℝ) ^ (M + 1 : ℕ)) ^ gamma :=
            Real.rpow_le_rpow (by linarith) hX_lt.le gamma_pos.le
        _ = ((2 : ℝ) ^ ((M + 1 : ℕ) : ℝ)) ^ gamma := by rw [Real.rpow_natCast]
    have h2pow : ((2 : ℝ) ^ ((M + 1 : ℕ) : ℝ)) ^ gamma = (a1 ^ (M + 1))⁻¹ := by
      rw [← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
          two_rpow_gamma, Real.rpow_natCast, one_div, inv_pow]
    have hEq : a1 ^ 9 * (a1 ^ (M + 1))⁻¹ = a1 ^ (4 : ℤ) * (a1 ^ (M - 4))⁻¹ := by
      have hMsplit : M + 1 = (M - 4) + 5 := by omega
      rw [hMsplit, pow_add, zpow_ofNat]; field_simp
    calc a1 ^ 9 * X ^ gamma
        ≤ a1 ^ 9 * ((2 : ℝ) ^ ((M + 1 : ℕ) : ℝ)) ^ gamma :=
          mul_le_mul_of_nonneg_left hXpow (by positivity)
      _ = a1 ^ 9 * (a1 ^ (M + 1))⁻¹ := by rw [h2pow]
      _ = a1 ^ (4 : ℤ) * (a1 ^ (M - 4))⁻¹ := hEq
      _ ≤ (N1 N : ℝ) := hU

/-- Theorem `thm:cantor` (Part 3, elementary upper bound for integers `N ≥ 1`): `N_1(N) ≤ N^β`. -/
theorem thm_cantor_upper_nat (N : ℕ) (hN : 1 ≤ N) :
    (N1 N : ℝ) ≤ (N : ℝ) ^ beta := by
  classical
  have ha0 := aStar_spec.1
  have h1a := aStar_denom_pos.1
  have hbeta_pos : 0 < beta := by linarith [beta_bounds_6.1]
  by_cases hN31 : N < 31
  · -- For 1 ≤ N < 31, 15 exits at T^[2] 15 = 19 and 17 exits at T^[5] 17 = 19, leaving N1(N) = 1.
    have hnot15 : ¬ Reaches f 15 1 := fun h => by
      have hS := InS30_T_iter_of_reaches_one h 2
      have hT : T^[2] 15 = 19 := by decide
      rw [hT] at hS; unfold InS30 at hS; omega
    have hnot17 : ¬ Reaches f 17 1 := fun h => by
      have hS := InS30_T_iter_of_reaches_one h 5
      have hT : T^[5] 17 = 19 := by decide
      rw [hT] at hS; unfold InS30 at hS; omega
    have hcard : N1 N ≤ 1 := by
      unfold N1
      have hsub : (Finset.Icc 1 N).filter (fun n => n % 2 = 1 ∧ Reaches f n 1) ⊆ {1} := by
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc] at hn
        simp only [Finset.mem_singleton]
        have hABC := thm_residue_law hn.2.1 hn.2.2
        simp only [InABC, InA, InB, InC] at hABC
        have hcases : n = 1 ∨ n = 15 ∨ n = 17 := by omega
        rcases hcases with rfl | rfl | rfl
        · rfl
        · exact absurd hn.2.2 hnot15
        · exact absurd hn.2.2 hnot17
      exact (Finset.card_le_card hsub).trans (by simp)
    have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ beta :=
      Real.one_le_rpow (by exact_mod_cast hN) hbeta_pos.le
    have hcast : (N1 N : ℝ) ≤ 1 := by exact_mod_cast hcard
    linarith
  · have hge31 : 31 ≤ N := by omega
    set h := Nat.log 2 ((N - 1) / 30) + 1
    have h1 : 1 ≤ (N - 1) / 30 := by omega
    have h2lo : 2 ^ (h - 1) ≤ (N - 1) / 30 := by
      have : h - 1 = Nat.log 2 ((N - 1) / 30) := by omega
      rw [this]
      exact Nat.pow_log_le_self 2 (by omega)
    have h2hi : (N - 1) / 30 < 2 ^ h := Nat.lt_pow_succ_log_self (by norm_num) ((N - 1) / 30)
    have hN_gt : 30 * 2 ^ (h - 1) < N := by omega
    have hN_le : N ≤ 30 * 2 ^ h := by omega
    -- Inject odd basin-of-1 members ≤ N into the disjoint union of surviving classes mod 2^h.
    let target : Finset (Fin 3 × ℕ) :=
      (((Finset.range (2 ^ h)).filter (fun k => Survives 1 h k)).image (fun k => ((0 : Fin 3), k))) ∪
      (((Finset.range (2 ^ h)).filter (fun k => Survives 15 h k)).image (fun k => ((1 : Fin 3), k))) ∪
      (((Finset.range (2 ^ h)).filter (fun k => Survives 17 h k)).image (fun k => ((2 : Fin 3), k)))
    have hN1_le_t : N1 N ≤ target.card := by
      unfold N1
      refine Finset.card_le_card_of_injOn (fun n => (clsIdx n, n / 30)) ?_ ?_
      · intro n hn
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
        obtain ⟨⟨_, hnN⟩, hn_odd, hn_r⟩ := hn
        have hABC := thm_residue_law hn_odd hn_r
        have hS := InS30_T_iter_of_reaches_one hn_r h
        simp only [Finset.mem_coe, target, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
          Finset.mem_range]
        rcases hABC with hA | hB | hC
        · left; left
          have hcls : clsIdx n = 0 := by unfold InA at hA; unfold clsIdx; simp [hA]
          have hdiv : 30 * (n / 30) + 1 = n := by unfold InA at hA; omega
          refine ⟨n / 30, ⟨by omega, (survives_iff_InS30 (by unfold InS30; omega) h (n / 30)).mpr
            (by rw [hdiv]; exact hS)⟩, by rw [hcls]⟩
        · left; right
          have hcls : clsIdx n = 1 := by unfold InB at hB; unfold clsIdx; simp [hB]
          have hdiv : 30 * (n / 30) + 15 = n := by unfold InB at hB; omega
          refine ⟨n / 30, ⟨by omega, (survives_iff_InS30 (by unfold InS30; omega) h (n / 30)).mpr
            (by rw [hdiv]; exact hS)⟩, by rw [hcls]⟩
        · right
          have hcls : clsIdx n = 2 := by unfold InC at hC; unfold clsIdx; simp [hC]
          have hdiv : 30 * (n / 30) + 17 = n := by unfold InC at hC; omega
          refine ⟨n / 30, ⟨by omega, (survives_iff_InS30 (by unfold InS30; omega) h (n / 30)).mpr
            (by rw [hdiv]; exact hS)⟩, by rw [hcls]⟩
      · intro a ha b hb heq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
        have hcls : clsIdx a = clsIdx b := congr_arg Prod.fst heq
        have hq : a / 30 = b / 30 := congr_arg Prod.snd heq
        have hAa := thm_residue_law ha.2.1 ha.2.2
        have hAb := thm_residue_law hb.2.1 hb.2.2
        have hmod30 : a % 30 = b % 30 := by
          simp only [InABC, InA, InB, InC] at hAa hAb
          rcases hAa with haA | haB | haC <;> rcases hAb with hbA | hbB | hbC <;>
            (unfold clsIdx at hcls; simp_all)
        omega
    have ht_le : target.card ≤ countSurvives 1 h + countSurvives 15 h + countSurvives 17 h := by
      let A1 := ((Finset.range (2 ^ h)).filter (fun k => Survives 1 h k)).image (fun k => ((0 : Fin 3), k))
      let A15 := ((Finset.range (2 ^ h)).filter (fun k => Survives 15 h k)).image (fun k => ((1 : Fin 3), k))
      let A17 := ((Finset.range (2 ^ h)).filter (fun k => Survives 17 h k)).image (fun k => ((2 : Fin 3), k))
      have htarget : target = A1 ∪ A15 ∪ A17 := rfl
      rw [htarget]
      unfold countSurvives
      have h1 : (A1 ∪ A15 ∪ A17).card ≤ A1.card + A15.card + A17.card :=
        (Finset.card_union_le (A1 ∪ A15) A17).trans (add_le_add (Finset.card_union_le A1 A15) le_rfl)
      have hi1 : A1.card ≤ ((Finset.range (2 ^ h)).filter (fun k => Survives 1 h k)).card :=
        Finset.card_image_le
      have hi15 : A15.card ≤ ((Finset.range (2 ^ h)).filter (fun k => Survives 15 h k)).card :=
        Finset.card_image_le
      have hi17 : A17.card ≤ ((Finset.range (2 ^ h)).filter (fun k => Survives 17 h k)).card :=
        Finset.card_image_le
      omega
    obtain ⟨_, hN1, hN17, hN15⟩ := countSurvives_bounds h
    have halg : (2 * aStar ^ 3)⁻¹ + 1 + (2 * aStar ^ 3)⁻¹ = (1 + aStar) / (1 - aStar) := by
      have hq := aStar_quartic
      have h1a_ne : 1 - aStar ≠ 0 := h1a.ne'
      have ha3_ne : aStar ^ 3 ≠ 0 := by positivity
      field_simp; nlinarith
    have h2h_lt : (2 : ℝ) ^ h < (N : ℝ) / 15 := by
      have hnat : 15 * 2 ^ h < N := by
        have hpow : 2 ^ h = 2 * 2 ^ (h - 1) := by
          have : h = (h - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ']
        rw [hpow]; omega
      have hreal : (15 : ℝ) * (2 : ℝ) ^ h < (N : ℝ) := by exact_mod_cast hnat
      linarith
    have ha_inv : (aStar ^ h)⁻¹ < ((N : ℝ) / 15) ^ beta := by
      have heq : (aStar ^ h)⁻¹ = ((2 : ℝ) ^ h) ^ beta := by
        rw [← Real.rpow_natCast (2 : ℝ) h, ← Real.rpow_mul (by norm_num),
            mul_comm (h : ℝ) beta, Real.rpow_mul (by norm_num), two_rpow_beta,
            Real.rpow_natCast, one_div, inv_pow]
      rw [heq]
      exact Real.rpow_lt_rpow (by positivity) h2h_lt hbeta_pos
    have hpref := aStar_N1_prefactor_lt_one
    calc (N1 N : ℝ)
        ≤ (target.card : ℝ) := by exact_mod_cast hN1_le_t
      _ ≤ (countSurvives 1 h : ℝ) + (countSurvives 15 h : ℝ) + (countSurvives 17 h : ℝ) := by
            exact_mod_cast ht_le
      _ ≤ (2 * aStar ^ 3)⁻¹ * (aStar ^ h)⁻¹ + (aStar ^ h)⁻¹ + (2 * aStar ^ 3)⁻¹ * (aStar ^ h)⁻¹ := by
            rw [hN17]; linarith
      _ = ((1 + aStar) / (1 - aStar)) * (aStar ^ h)⁻¹ := by rw [← halg]; ring
      _ ≤ ((1 + aStar) / (1 - aStar)) * ((N : ℝ) / 15) ^ beta :=
            mul_le_mul_of_nonneg_left ha_inv.le (by positivity)
      _ = ((1 + aStar) / ((1 - aStar) * (15 : ℝ) ^ beta)) * (N : ℝ) ^ beta := by
            rw [Real.div_rpow (by positivity) (by norm_num)]
            have h15 : (15 : ℝ) ^ beta ≠ 0 := by positivity
            have h1a_ne : 1 - aStar ≠ 0 := h1a.ne'
            field_simp
      _ ≤ 1 * (N : ℝ) ^ beta := mul_le_mul_of_nonneg_right hpref.le (by positivity)
      _ = (N : ℝ) ^ beta := one_mul _

/-- Theorem `thm:cantor` (Part 3, elementary upper bound for all real `X ≥ 1`): `N_1(⌊X⌋) ≤ X^β`. -/
theorem thm_cantor_upper_real (X : ℝ) (hX : 1 ≤ X) :
    (N1 ⌊X⌋₊ : ℝ) ≤ X ^ beta := by
  have hbeta_pos : 0 < beta := by linarith [beta_bounds_6.1]
  have hfl1 : 1 ≤ ⌊X⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hX)
  have hfl_le : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
  exact (thm_cantor_upper_nat ⌊X⌋₊ hfl1).trans
    (Real.rpow_le_rpow (by positivity) hfl_le hbeta_pos.le)

/-- **Theorem 18 (`thm:cantor`)** — Exact `2`-adic Cantor closure, self-similar isometry,
    Hausdorff and box-counting dimension `β = -log_2 a`, and elementary quartic bounds
    `a_1^9 * X^γ ≤ N_1(⌊X⌋) ≤ X^β` for all real `X ≥ 1`. -/
theorem thm_cantor :
    -- Roots & exponents (explicitly tying `a1` and `aStar` to their unique positive quartic roots)
    (0 < a1 ∧ a1 < 1 ∧ a1 + a1 ^ 4 = 1) ∧
    (∃! a : ℝ, 0 < a ∧ a < 1 ∧ a + a ^ 4 = 1) ∧
    (0 < aStar ∧ aStar < 1 ∧ aStar + 2 * aStar ^ 4 = 1) ∧
    (∃! a : ℝ, 0 < a ∧ a < 1 ∧ a + 2 * a ^ 4 = 1) ∧
    (gamma = -Real.logb 2 a1 ∧ beta = -Real.logb 2 aStar) ∧
    ((464958 / 1000000 : ℝ) < gamma ∧ gamma < (464959 / 1000000 : ℝ)) ∧
    ((626382135 / 1000000000 : ℝ) < beta ∧ beta < (626382145 / 1000000000 : ℝ)) ∧
    ((626382 / 1000000 : ℝ) < beta ∧ beta < (626383 / 1000000 : ℝ)) ∧
    -- Part (1): Exact 2-adic closure, ball dichotomy, nowhere-denseness
    ((∀ r : ℕ, (r = 1 ∨ r = 15 ∨ r = 17) → closure (KrPadic r) = KCal r) ∧
      closure B1Padic =
        affine30 1 '' KCal 1 ∪ affine30 15 '' KCal 15 ∪ affine30 17 '' KCal 17 ∧
      (∀ (x : ℤ_[2]) (ρ : ℝ), (Metric.ball x ρ ∩ closure B1Padic).Nonempty →
        {n : ℕ | 1 ≤ n ∧ Reaches f n 1 ∧ (n : ℤ_[2]) ∈ Metric.ball x ρ}.Infinite ∧
        {n : ℕ | 1 ≤ n ∧ InABC n ∧ ExitsAt19Or23 n ∧ (n : ℤ_[2]) ∈ Metric.ball x ρ}.Infinite) ∧
      IsNowhereDense (closure B1Padic)) ∧
    -- Part (2): Self-similar isometry, Hausdorff measure, dimH = dimB = β
    ((∀ r : ℕ, Isometry (psiMap r)) ∧
      (∀ r : ℕ, (r = 1 ∨ r = 17) → psiMap r '' KCal r = SigmaSet) ∧
      psiMap 15 '' KCal 15 = Sigma15Set ∧
      Disjoint (prependBits [false, false, false] '' SigmaSet)
        (prependBits [false, false, true] '' SigmaSet) ∧
      ENNReal.ofReal (1 / 2) ≤ μH[beta] (closure B1Padic) ∧
      μH[beta] (closure B1Padic) ≤ ENNReal.ofReal (aStar⁻¹ ^ 2 + aStar) ∧
      μH[beta] (closure B1Padic) < ENNReal.ofReal (3031 / 1000) ∧
      dimH (closure B1Padic) = ENNReal.ofReal beta ∧
      HasBoxDim (closure B1Padic) beta) ∧
    -- Part (3): Elementary integer bounds & density zero
    ((∀ X : ℝ, 1 ≤ X → a1 ^ 9 * X ^ gamma ≤ (N1 ⌊X⌋₊ : ℝ) ∧ (N1 ⌊X⌋₊ : ℝ) ≤ X ^ beta) ∧
      (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → (N1All X : ℝ) / (X : ℝ) ≤ ε)) :=
  ⟨a1_spec, exists_unique_a1, ⟨aStar_spec.1, aStar_spec.2.1, aStar_quartic⟩,
   exists_unique_aStar_quartic,
   ⟨gamma_eq_neg_logb, beta_eq_neg_logb⟩, gamma_bounds_6, beta_bounds_8, beta_bounds_6,
   ⟨fun _ hr => closure_KrPadic_eq hr, closure_B1Padic_eq,
    fun _ _ h => ball_meeting_closure_B1Padic h, isNowhereDense_closure_B1Padic⟩,
   ⟨psiMap_isometry, fun _ hr => psiMap_image_KCal_1_17 hr, psiMap_image_KCal_15, sigma15_disjoint,
    hausdorffMeasure_closure_B1Padic_bounds.1, hausdorffMeasure_closure_B1Padic_bounds.2.1,
    hausdorffMeasure_closure_B1Padic_bounds.2.2, dimH_closure_B1Padic, hasBoxDim_closure_B1Padic⟩,
   ⟨fun X hX => ⟨thm_cantor_lower_real X hX, thm_cantor_upper_real X hX⟩, thm_basin1_density_zero⟩⟩

end Ouroboros
