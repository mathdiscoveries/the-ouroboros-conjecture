module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Tactic
public import Ouroboros.Defs
public import Ouroboros.BasinOne
public import Ouroboros.BasinOneMoves
public import Ouroboros.BasinFive
public import Ouroboros.BasinFiveUncond
public import Ouroboros.BasinOneUpperCert

@[expose] public section

/-!
# Sharpened Archimedean upper bound for the basin of 1 (`thm:basin-sharp` Part 1b)

Formalizes in Lean 4's pure kernel (ZERO `native_decide`, ZERO `sorry`, ZERO custom axioms):
- **Forward 3-state weighted word bound** (`admWords_weighted_bound`):
  at `(a_F, s_F) = (6331/10000, 7/100)`, `a_F^L ∑_{w ∈ admWords c L} D(c, w)^{s_F} ≤ h_F(c)`.
- **Unified backward path bound** (`backPaths_weighted_bound`):
  for any positive weight vector obeying `∑_{(d,v)} d^s a^v w(m) ≤ w(o)`,
  `a^L ∑_{l ∈ backPaths o L} D(o, l)^s ≤ w(o)`.
- **3-state depth bound** (`depth_backPaths_bound`, Case 1):
  at `a_H = 2/3, s_H = 0` with `(w_A, w_B, w_C) = (10, 4, 4)` using exact spacing
  `(4, 20, 3)` for digits `(1, 5, 7)`, proving `θ_H = log_2(3/2) < 3/5 < 0.6245`.
- **Certified `Q1 = 643,125` pair bound** (`pair_backPaths_bound`, Case 3):
  bridges the 21 pure-kernel `rfl` shards in `Ouroboros.BasinOneUpperCert` (`128,625` rows,
  `a_P = 7116/10000`, `s_P = 9/25`, `Vmax = 36` plus per-class geometric tails) to
  `∑_{l ∈ backPaths o L} D(o, l)^{9/25} ≤ 226,730 * (10000/7116)^L`.
- **Theorem (`thm:basin-sharp` Part 1b)** (`thm_basin1_upper_sharp`, `thm_basin1_upper_sharp_real`):
  `∃ C > 0, ∀ X ≥ 1, N_1(X) ≤ C * X^{0.6245}`.
- **2-adic/Archimedean separation & sharpened ratio** (`cor_basin1_archimedean_lt_2adic`,
  `cor_basin_separation_sharp`):
  `limsup (log N_1(X) / log X) ≤ 0.6245 < β = dim_H(B_1_bar)` and
  `N_1(X) / N_5(X) = O(X^{-0.0255})`.
-/

namespace Ouroboros

open BasinOneUpperCert

/-! ## Section 1: Parameters and exact rational exponent inequalities -/

/-- Target Archimedean exponent `β' = 0.6245`. -/
noncomputable def betaPrime : ℝ := 6245 / 10000

/-- Cutoff parameter `δ = 0.505`. -/
noncomputable def deltaParam : ℝ := 505 / 1000

/-- Forward parameters `(a_F, s_F) = (0.6331, 7/100)`. -/
noncomputable def aFVal : ℝ := 6331 / 10000
noncomputable def sFVal : ℝ := 7 / 100

/-- Pair parameters `(a_P, s_P) = (0.7116, 9/25)`. -/
noncomputable def aPVal : ℝ := 7116 / 10000
noncomputable def sPVal : ℝ := 9 / 25

/-- Depth parameter `a_H = 2/3`. -/
noncomputable def aHVal : ℝ := 2 / 3

private lemma rpow_le_of_pow_le {x r : ℝ} {p q : ℕ} (hx : 0 ≤ x) (hr : 0 ≤ r) (hq : 0 < q)
    (h : x ^ p ≤ r ^ q) : x ^ ((p : ℝ) / (q : ℝ)) ≤ r := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hpow : (x ^ ((p : ℝ) / (q : ℝ))) ^ q ≤ r ^ q := by
    rw [← Real.rpow_natCast (x ^ _), ← Real.rpow_mul hx, div_mul_cancel₀ _ hq', Real.rpow_natCast]
    exact h
  exact le_of_pow_le_pow_left₀ hq.ne' hr hpow

private lemma inv_le_two_rpow_of_pow {a : ℝ} {p q : ℕ} (ha : 0 < a) (hq : 0 < q)
    (h : (1 : ℝ) ≤ a ^ q * (2 : ℝ) ^ p) :
    (1 / a) ≤ (2 : ℝ) ^ ((p : ℝ) / (q : ℝ)) := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hpow : (1 / a) ^ q ≤ ((2 : ℝ) ^ ((p : ℝ) / (q : ℝ))) ^ q := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num),
        div_mul_cancel₀ _ hq', Real.rpow_natCast, one_div, inv_pow,
        inv_le_iff_one_le_mul₀ (pow_pos ha q), mul_comm]
    exact h
  exact le_of_pow_le_pow_left₀ hq.ne' (by positivity) hpow

/-- Case 1 exponent bound: `3/2 ≤ 2^(3/5)` (since `3^5 = 243 ≤ 256 = 2^8`). -/
lemma inv_aH_le_two_rpow : (1 / aHVal) ≤ (2 : ℝ) ^ ((3 : ℝ) / 5) := by
  unfold aHVal
  exact inv_le_two_rpow_of_pow (p := 3) (q := 5) (by norm_num) (by norm_num) (by norm_num)

/-- Case 2 exponent bound: `1 / a_F ≤ 2^(64/97)`. -/
lemma inv_aF_le_two_rpow : (1 / aFVal) ≤ (2 : ℝ) ^ ((64 : ℝ) / 97) := by
  unfold aFVal
  exact inv_le_two_rpow_of_pow (p := 64) (q := 97) (by norm_num) (by norm_num) (by norm_num)

/-- Case 3 exponent bound: `1 / a_P ≤ 2^(27/55)`. -/
lemma inv_aP_le_two_rpow : (1 / aPVal) ≤ (2 : ℝ) ^ ((27 : ℝ) / 55) := by
  unfold aPVal
  exact inv_le_two_rpow_of_pow (p := 27) (q := 55) (by norm_num) (by norm_num) (by norm_num)

private lemma five_rpow_sF_le : (5 : ℝ) ^ sFVal ≤ 11193 / 10000 := by
  unfold sFVal
  exact rpow_le_of_pow_le (p := 7) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private lemma seven_rpow_sF_le : (7 : ℝ) ^ sFVal ≤ 11460 / 10000 := by
  unfold sFVal
  exact rpow_le_of_pow_le (p := 7) (q := 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private lemma five_rpow_sP_le : (5 : ℝ) ^ sPVal ≤ (c5Val : ℝ) / 1000000 := by
  unfold sPVal c5Val
  exact rpow_le_of_pow_le (p := 9) (q := 25) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private lemma seven_rpow_sP_le : (7 : ℝ) ^ sPVal ≤ (c7Val : ℝ) / 1000000 := by
  unfold sPVal c7Val
  exact rpow_le_of_pow_le (p := 9) (q := 25) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## Section 2: General finite geometric-series and elementary analytic helpers -/

/-- Generic finite geometric sum along a residue class modulo `step ≥ 1` above floor `lo`. -/
lemma finite_geom_step_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {step r lo L : ℕ} (hstep : 1 ≤ step) :
    ∑ v ∈ (Finset.Icc lo L).filter (fun v => v % step = r % step), a ^ v ≤
      a ^ lo / (1 - a ^ step) := by
  have hastep : a ^ step < 1 := by
    calc a ^ step < 1 ^ step := pow_lt_pow_left₀ ha1 ha0.le (by omega)
      _ = 1 := one_pow step
  have h1a : 0 < 1 - a ^ step := by linarith
  let v0 : ℕ := lo + (r % step + step - lo % step) % step
  have hv0_ge : lo ≤ v0 := Nat.le_add_right _ _
  have hv0_mod : v0 % step = r % step := by
    have hlo_lt : lo % step < step := Nat.mod_lt lo (by omega)
    have hr_lt : r % step < step := Nat.mod_lt r (by omega)
    have h1 : (lo + (r % step + step - lo % step) % step) % step =
        (lo % step + (r % step + step - lo % step)) % step := by
      simp only [Nat.add_mod, Nat.mod_mod]
    rw [show v0 = lo + (r % step + step - lo % step) % step from rfl, h1]
    have h2 : lo % step + (r % step + step - lo % step) = r % step + step := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hr_lt]
  have hsub : (Finset.Icc lo L).filter (fun v => v % step = r % step) ⊆
      (Finset.range (L + 1)).image (fun j => v0 + step * j) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_Icc] at hv
    simp only [Finset.mem_image, Finset.mem_range]
    have hv_ge : v0 ≤ v := by
      have hlo_lt : lo % step < step := Nat.mod_lt lo (by omega)
      have hr_lt : r % step < step := Nat.mod_lt r (by omega)
      have hdiv_lo := Nat.div_add_mod lo step
      have hdiv_v := Nat.div_add_mod v step
      by_cases hcmp : lo % step ≤ r % step
      · have hmod : (r % step + step - lo % step) % step = r % step - lo % step := by
          have : r % step + step - lo % step = (r % step - lo % step) + step := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have hv0_eq : v0 = lo + (r % step - lo % step) := by simp [v0, hmod]
        have hq : lo / step ≤ v / step := Nat.div_le_div_right hv.1.1
        have hmul : step * (lo / step) ≤ step * (v / step) := Nat.mul_le_mul_left step hq
        omega
      · have hmod : (r % step + step - lo % step) % step = r % step + step - lo % step :=
          Nat.mod_eq_of_lt (by omega)
        have hv0_eq : v0 = lo + (r % step + step - lo % step) := by simp [v0, hmod]
        have hq : lo / step + 1 ≤ v / step := by
          by_contra hlt
          have hqle : v / step ≤ lo / step := by omega
          have hmul : step * (v / step) ≤ step * (lo / step) := Nat.mul_le_mul_left step hqle
          omega
        have hmul : step * (lo / step + 1) ≤ step * (v / step) := Nat.mul_le_mul_left step hq
        rw [mul_add, mul_one] at hmul
        omega
    have hdvd : step ∣ (v - v0) := by
      have h1 : (v - v0) % step = 0 := by
        have hdv := Nat.div_add_mod v step
        have hdv0 := Nat.div_add_mod v0 step
        have hq : v0 / step ≤ v / step := Nat.div_le_div_right hv_ge
        have : v - v0 = step * (v / step - v0 / step) := by
          rw [Nat.mul_sub]; omega
        rw [this, Nat.mul_mod_right]
      exact Nat.dvd_of_mod_eq_zero h1
    obtain ⟨j, hj⟩ := hdvd
    refine ⟨j, ?_, by omega⟩
    have : 1 * j ≤ step * j := Nat.mul_le_mul_right j hstep
    omega
  have hsum_le : ∑ v ∈ (Finset.Icc lo L).filter (fun v => v % step = r % step), a ^ v ≤
      ∑ v ∈ (Finset.range (L + 1)).image (fun j => v0 + step * j), a ^ v :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have himg : ∑ v ∈ (Finset.range (L + 1)).image (fun j => v0 + step * j), a ^ v =
      a ^ v0 * ∑ j ∈ Finset.range (L + 1), (a ^ step) ^ j := by
    rw [Finset.sum_image (fun x _ y _ h => by
      have : step * x = step * y := by omega
      exact Nat.eq_of_mul_eq_mul_left (by omega) this), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add, pow_mul]
  have hgeom : ∑ j ∈ Finset.range (L + 1), (a ^ step) ^ j ≤ 1 / (1 - a ^ step) := by
    rw [geom_sum_eq (ne_of_lt hastep)]
    have hnn : 0 ≤ (a ^ step) ^ (L + 1) := by positivity
    have hneg : (a ^ step) ^ (L + 1) - 1 = -(1 - (a ^ step) ^ (L + 1)) := by ring
    have hneg2 : a ^ step - 1 = -(1 - a ^ step) := by ring
    rw [hneg, hneg2, neg_div_neg_eq]
    exact div_le_div_of_nonneg_right (by linarith) h1a.le
  have hv0_pow : a ^ v0 ≤ a ^ lo := pow_le_pow_of_le_one ha0.le ha1.le hv0_ge
  calc ∑ v ∈ (Finset.Icc lo L).filter (fun v => v % step = r % step), a ^ v
      ≤ a ^ v0 * ∑ j ∈ Finset.range (L + 1), (a ^ step) ^ j := hsum_le.trans_eq himg
    _ ≤ a ^ v0 * (1 / (1 - a ^ step)) := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ ≤ a ^ lo * (1 / (1 - a ^ step)) := mul_le_mul_of_nonneg_right hv0_pow (by positivity)
    _ = a ^ lo / (1 - a ^ step) := by ring

/-- Distinct odd integers `≥ 15` satisfy `∏_{x ∈ S} (1 + 1/x) ≤ √(K + 1)` when `|S| ≤ K`. -/
lemma prod_one_add_inv_le_sqrt {S : Finset ℕ} {K : ℕ} (hcard : S.card ≤ K)
    (hodd : ∀ x ∈ S, x % 2 = 1 ∧ 15 ≤ x) :
    ∏ x ∈ S, (1 + 1 / (x : ℝ)) ≤ Real.sqrt ((K : ℝ) + 1) := by
  have hsq : ∀ (n : ℕ) (a : ℕ) (T : Finset ℕ), T.card = n →
      (∀ x ∈ T, x % 2 = 1 ∧ 2 * a + 15 ≤ x) →
      (∏ x ∈ T, (1 + 1 / (x : ℝ))) ^ 2 ≤ ((a : ℝ) + (n : ℝ) + 7) / ((a : ℝ) + 7) := by
    intro n
    induction n with
    | zero =>
      intro a T hT _
      rw [Finset.card_eq_zero.mp hT]
      simp only [Finset.prod_empty, one_pow, Nat.cast_zero, add_zero]
      rw [div_self (by positivity)]
    | succ n ih =>
      intro a T hT hmem
      have hne : T.Nonempty := Finset.card_pos.mp (by omega)
      let x0 := T.min' hne
      have hx0_mem : x0 ∈ T := Finset.min'_mem T hne
      obtain ⟨hx0_odd, hx0_ge⟩ := hmem x0 hx0_mem
      let T' := T.erase x0
      have hT'_card : T'.card = n := by rw [Finset.card_erase_of_mem hx0_mem, hT]; omega
      have hT'_mem : ∀ x ∈ T', x % 2 = 1 ∧ 2 * (a + 1) + 15 ≤ x := by
        intro x hx
        have hne_x : x ≠ x0 := (Finset.mem_erase.mp hx).1
        have hxT : x ∈ T := (Finset.mem_erase.mp hx).2
        have hle_x : x0 ≤ x := Finset.min'_le T x hxT
        obtain ⟨hx_odd, _⟩ := hmem x hxT
        exact ⟨hx_odd, by omega⟩
      have hih := ih (a + 1) T' hT'_card hT'_mem
      have hprod : ∏ x ∈ T, (1 + 1 / (x : ℝ)) =
          (1 + 1 / (x0 : ℝ)) * ∏ x ∈ T', (1 + 1 / (x : ℝ)) :=
        (Finset.mul_prod_erase T (fun x => 1 + 1 / (x : ℝ)) hx0_mem).symm
      rw [hprod, mul_pow]
      have hx0_pos : (0 : ℝ) < (x0 : ℝ) := by exact_mod_cast (by omega : 0 < x0)
      have ha15 : (2 * (a : ℝ) + 15) ≤ (x0 : ℝ) := by exact_mod_cast hx0_ge
      have hstep1 : 1 + 1 / (x0 : ℝ) ≤ 1 + 1 / (2 * (a : ℝ) + 15) := by
        have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by positivity) ha15
        linarith
      have hstep2 : (1 + 1 / (2 * (a : ℝ) + 15)) ^ 2 ≤ ((a : ℝ) + 8) / ((a : ℝ) + 7) := by
        have hden1 : (0 : ℝ) < 2 * (a : ℝ) + 15 := by positivity
        have hden2 : (0 : ℝ) < (a : ℝ) + 7 := by positivity
        have hrew : 1 + 1 / (2 * (a : ℝ) + 15) = (2 * (a : ℝ) + 16) / (2 * (a : ℝ) + 15) := by
          field_simp; ring
        rw [hrew, div_pow, div_le_div_iff₀ (pow_pos hden1 2) hden2]
        nlinarith [show (0 : ℝ) ≤ (a : ℝ) by positivity]
      have hstep0 : (1 + 1 / (x0 : ℝ)) ^ 2 ≤ ((a : ℝ) + 8) / ((a : ℝ) + 7) :=
        (pow_le_pow_left₀ (by positivity) hstep1 2).trans hstep2
      have hprod_nn : 0 ≤ (∏ x ∈ T', (1 + 1 / (x : ℝ))) ^ 2 := sq_nonneg _
      have hmul := mul_le_mul hstep0 hih hprod_nn (by positivity)
      have hsimp : ((a : ℝ) + 8) / ((a : ℝ) + 7) *
          ((((a + 1 : ℕ) : ℝ) + (n : ℝ) + 7) / (((a + 1 : ℕ) : ℝ) + 7)) =
          ((a : ℝ) + ((n + 1 : ℕ) : ℝ) + 7) / ((a : ℝ) + 7) := by
        push_cast
        have hne8 : (a : ℝ) + 1 + 7 ≠ 0 := by positivity
        have hne7 : (a : ℝ) + 7 ≠ 0 := by positivity
        field_simp
        ring
      linarith
  have h0 := hsq S.card 0 S rfl (fun x hx => by simpa using hodd x hx)
  have hleK : ((0 : ℕ) : ℝ) + (S.card : ℝ) + 7 ≤ 7 * ((K : ℝ) + 1) := by
    have hK : (S.card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hcard
    push_cast; linarith
  have hsqK : (∏ x ∈ S, (1 + 1 / (x : ℝ))) ^ 2 ≤ (K : ℝ) + 1 := by
    have h1 : (((0 : ℕ) : ℝ) + (S.card : ℝ) + 7) / (((0 : ℕ) : ℝ) + 7) ≤ (K : ℝ) + 1 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < ((0 : ℕ) : ℝ) + 7)]
      push_cast at hleK ⊢; linarith
    exact h0.trans h1
  have hnn : 0 ≤ ∏ x ∈ S, (1 + 1 / (x : ℝ)) := Finset.prod_nonneg fun _ _ => by positivity
  rw [← Real.sqrt_sq hnn]
  exact Real.sqrt_le_sqrt hsqK

open Classical in
/-- Discrete summation by parts for `∑_{o ≤ M, o ∈ B_1 odd} o^(-s)` when `N1(t) ≤ C * t^b`
    for all `1 ≤ t ≤ M` and `0 < s < b < 1`. -/
lemma sum_inv_rpow_le_of_count_le {s b C : ℝ} (hs : 0 < s) (hsb : s < b) (hb1 : b < 1)
    (hC : 0 ≤ C) {M : ℕ} (hM : 1 ≤ M)
    (hcount : ∀ t : ℕ, 1 ≤ t → t ≤ M → (N1 t : ℝ) ≤ C * (t : ℝ) ^ b) :
    ∑ o ∈ (Finset.Icc 1 M).filter (fun o => o % 2 = 1 ∧ Reaches f o 1), (o : ℝ) ^ (-s) ≤
      (b / (b - s)) * C * (M : ℝ) ^ (b - s) := by
  let ind (k : ℕ) : ℝ := if k % 2 = 1 ∧ Reaches f k 1 then 1 else 0
  have hN1_sum : ∀ m : ℕ, (N1 m : ℝ) = ∑ k ∈ Finset.Icc 1 m, ind k := by
    intro m
    unfold N1 ind
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hN1_diff : ∀ k : ℕ, 1 ≤ k → ind k = (N1 k : ℝ) - (N1 (k - 1) : ℝ) := by
    intro k hk
    rw [hN1_sum k, hN1_sum (k - 1)]
    have hsplit : Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotmem : k ∉ Finset.Icc 1 (k - 1) := by simp only [Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert hnotmem]
    ring
  have hlhs_eq : ∑ o ∈ (Finset.Icc 1 M).filter (fun o => o % 2 = 1 ∧ Reaches f o 1), (o : ℝ) ^ (-s) =
      ∑ k ∈ Finset.Icc 1 M, ind k * (k : ℝ) ^ (-s) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold ind; split_ifs <;> ring
  rw [hlhs_eq]
  -- Abel summation identity
  have habel : ∀ m : ℕ, 1 ≤ m →
      ∑ k ∈ Finset.Icc 1 m, ind k * (k : ℝ) ^ (-s) =
        (N1 m : ℝ) * (m : ℝ) ^ (-s) +
          ∑ k ∈ Finset.Icc 1 (m - 1), (N1 k : ℝ) * ((k : ℝ) ^ (-s) - ((k + 1 : ℕ) : ℝ) ^ (-s)) := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      cases m with
      | zero =>
        have hN0 : N1 0 = 0 := by unfold N1; simp
        simp [hN1_diff 1 le_rfl, hN0]
      | succ m =>
        have hIcc1 : Finset.Icc 1 (m + 2) = insert (m + 2) (Finset.Icc 1 (m + 1)) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnm1 : m + 2 ∉ Finset.Icc 1 (m + 1) := by simp only [Finset.mem_Icc]; omega
        have hIcc2 : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnm2 : m + 1 ∉ Finset.Icc 1 m := by simp only [Finset.mem_Icc]; omega
        rw [hIcc1, Finset.sum_insert hnm1, ih (by omega)]
        rw [show m + 2 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega]
        rw [hIcc2, Finset.sum_insert hnm2, hN1_diff (m + 2) (by omega), show m + 2 - 1 = m + 1 by omega]
        ring
  rw [habel M hM]
  -- Elementary concavity inequality: u^r ≤ 1 + r * (u - 1) for u ≥ 0, 0 < r < 1 (no calculus needed!)
  have hrpow_conc : ∀ {u r : ℝ}, 0 ≤ u → 0 < r → r < 1 → u ^ r ≤ 1 + r * (u - 1) := by
    intro u r hu hr0 hr1
    rcases eq_or_lt_of_le hu with rfl | hu_pos
    · rw [Real.zero_rpow hr0.ne']; linarith
    · set t : ℝ := 1 + r * (u - 1)
      have ht_eq : t = r * u + (1 - r) := by unfold t; ring
      have ht_pos : 0 < t := by rw [ht_eq]; nlinarith
      have h1 := Real.log_le_sub_one_of_pos (div_pos hu_pos ht_pos)
      have h2 := Real.log_le_sub_one_of_pos (div_pos zero_lt_one ht_pos)
      have hcomb : r * Real.log (u / t) + (1 - r) * Real.log (1 / t) ≤
          r * (u / t - 1) + (1 - r) * (1 / t - 1) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hr0.le)
          (mul_le_mul_of_nonneg_left h2 (by linarith))
      have hrhs0 : r * (u / t - 1) + (1 - r) * (1 / t - 1) = 0 := by
        have htne : t ≠ 0 := ht_pos.ne'
        field_simp
        linarith [ht_eq]
      rw [hrhs0, Real.log_div hu_pos.ne' ht_pos.ne', Real.log_div one_ne_zero ht_pos.ne',
          Real.log_one] at hcomb
      have hlog : Real.log u * r ≤ Real.log t := by linarith
      calc u ^ r = Real.exp (Real.log u * r) := Real.rpow_def_of_pos hu_pos r
        _ ≤ Real.exp (Real.log t) := Real.exp_le_exp.mpr hlog
        _ = t := Real.exp_log ht_pos
  -- Bound 1: k^(-s) - (k+1)^(-s) ≤ s * k^(-s - 1)
  have hdiff_le : ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ^ (-s) - ((k + 1 : ℕ) : ℝ) ^ (-s) ≤ s * (k : ℝ) ^ (-s - 1) := by
    intro k hk
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hconc := hrpow_conc (u := ((k + 1 : ℕ) : ℝ) / (k : ℝ)) (r := s) (by positivity) hs (by linarith)
    have hu_sub : ((k + 1 : ℕ) : ℝ) / (k : ℝ) - 1 = 1 / (k : ℝ) := by
      push_cast; field_simp; ring
    rw [hu_sub] at hconc
    have hmul := mul_le_mul_of_nonneg_right hconc (Real.rpow_nonneg hk1_pos.le (-s))
    have hlhs_simp : (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ^ s * ((k + 1 : ℕ) : ℝ) ^ (-s) = (k : ℝ) ^ (-s) := by
      rw [Real.div_rpow hk1_pos.le hk_pos.le, Real.rpow_neg hk1_pos.le, Real.rpow_neg hk_pos.le]
      have hne : ((k + 1 : ℕ) : ℝ) ^ s ≠ 0 := (Real.rpow_pos_of_pos hk1_pos s).ne'
      field_simp
    have hmono : ((k + 1 : ℕ) : ℝ) ^ (-s) ≤ (k : ℝ) ^ (-s) := by
      rw [Real.rpow_neg hk1_pos.le, Real.rpow_neg hk_pos.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hk_pos s)
        (Real.rpow_le_rpow hk_pos.le (by push_cast; linarith) hs.le)
    have hk_pow : (k : ℝ) ^ (-s - 1) = (1 / (k : ℝ)) * (k : ℝ) ^ (-s) := by
      rw [show -s - 1 = -1 + (-s) by ring, Real.rpow_add hk_pos, Real.rpow_neg_one, one_div]
    rw [hlhs_simp] at hmul
    have hbound : s * (1 / (k : ℝ)) * ((k + 1 : ℕ) : ℝ) ^ (-s) ≤ s * (k : ℝ) ^ (-s - 1) := by
      rw [hk_pow]
      have := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ s * (1 / (k : ℝ)))
      linarith
    linarith
  -- Bound 2: k^(α - 1) ≤ (k^α - (k-1)^α) / α for α = b - s ∈ (0, 1)
  set α : ℝ := b - s
  have hα0 : 0 < α := by linarith
  have hα1 : α < 1 := by linarith
  have hteles_step : ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ^ (α - 1) ≤ ((k : ℝ) ^ α - ((k - 1 : ℕ) : ℝ) ^ α) / α := by
    intro k hk
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hconc := hrpow_conc (u := ((k - 1 : ℕ) : ℝ) / (k : ℝ)) (r := α) (by positivity) hα0 hα1
    have hsub1 : (k : ℝ) - ((k - 1 : ℕ) : ℝ) = 1 := by
      have : (k : ℕ) = (k - 1) + 1 := by omega
      conv_lhs => rw [this]
      push_cast; ring
    have hu_sub : ((k - 1 : ℕ) : ℝ) / (k : ℝ) - 1 = -(1 / (k : ℝ)) := by
      have hne : (k : ℝ) ≠ 0 := hk_pos.ne'
      field_simp; linarith
    rw [hu_sub] at hconc
    have hmul := mul_le_mul_of_nonneg_right hconc (Real.rpow_nonneg hk_pos.le α)
    have hlhs_simp : (((k - 1 : ℕ) : ℝ) / (k : ℝ)) ^ α * (k : ℝ) ^ α = ((k - 1 : ℕ) : ℝ) ^ α := by
      rw [Real.div_rpow (Nat.cast_nonneg _) hk_pos.le,
          div_mul_cancel₀ _ (Real.rpow_pos_of_pos hk_pos α).ne']
    have hk_pow : (k : ℝ) ^ (α - 1) = (1 / (k : ℝ)) * (k : ℝ) ^ α := by
      rw [show α - 1 = -1 + α by ring, Real.rpow_add hk_pos, Real.rpow_neg_one, one_div]
    rw [hlhs_simp] at hmul
    rw [le_div_iff₀ hα0, hk_pow]
    linarith
  -- Bound the tail sum
  have hsum_tail : ∑ k ∈ Finset.Icc 1 (M - 1),
        (N1 k : ℝ) * ((k : ℝ) ^ (-s) - ((k + 1 : ℕ) : ℝ) ^ (-s)) ≤
      (s / α) * C * (M : ℝ) ^ α := by
    have h1 : ∑ k ∈ Finset.Icc 1 (M - 1),
          (N1 k : ℝ) * ((k : ℝ) ^ (-s) - ((k + 1 : ℕ) : ℝ) ^ (-s)) ≤
        ∑ k ∈ Finset.Icc 1 (M - 1), (C * s) * (k : ℝ) ^ (α - 1) := by
      refine Finset.sum_le_sum fun k hk => ?_
      simp only [Finset.mem_Icc] at hk
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      have hN1_nn : (0 : ℝ) ≤ (N1 k : ℝ) := Nat.cast_nonneg _
      have hcnt := hcount k hk.1 (by omega)
      have hd := hdiff_le k hk.1
      have hpow : (k : ℝ) ^ b * (k : ℝ) ^ (-s - 1) = (k : ℝ) ^ (α - 1) := by
        rw [← Real.rpow_add hk_pos]; congr 1; unfold α; ring
      calc (N1 k : ℝ) * ((k : ℝ) ^ (-s) - ((k + 1 : ℕ) : ℝ) ^ (-s))
          ≤ (N1 k : ℝ) * (s * (k : ℝ) ^ (-s - 1)) := mul_le_mul_of_nonneg_left hd hN1_nn
        _ ≤ (C * (k : ℝ) ^ b) * (s * (k : ℝ) ^ (-s - 1)) :=
              mul_le_mul_of_nonneg_right hcnt (by positivity)
        _ = (C * s) * ((k : ℝ) ^ b * (k : ℝ) ^ (-s - 1)) := by ring
        _ = (C * s) * (k : ℝ) ^ (α - 1) := by rw [hpow]
    have hteles : ∀ m : ℕ, ∑ k ∈ Finset.Icc 1 m, (k : ℝ) ^ (α - 1) ≤ (m : ℝ) ^ α / α := by
      intro m
      induction m with
      | zero => simp [Real.zero_rpow hα0.ne']
      | succ m ihm =>
        have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnm : m + 1 ∉ Finset.Icc 1 m := by simp only [Finset.mem_Icc]; omega
        rw [hIcc, Finset.sum_insert hnm]
        have hstep := hteles_step (m + 1) (by omega)
        simp only [Nat.add_sub_cancel] at hstep
        linarith [show ((m + 1 : ℕ) : ℝ) ^ α / α =
          (((m + 1 : ℕ) : ℝ) ^ α - (m : ℝ) ^ α) / α + (m : ℝ) ^ α / α by ring]
    have h2 : ∑ k ∈ Finset.Icc 1 (M - 1), (C * s) * (k : ℝ) ^ (α - 1) ≤
        (C * s) * (((M - 1 : ℕ) : ℝ) ^ α / α) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hteles (M - 1)) (by positivity)
    have hM1 : ((M - 1 : ℕ) : ℝ) ^ α ≤ (M : ℝ) ^ α :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le M 1) hα0.le
    calc ∑ k ∈ Finset.Icc 1 (M - 1),
          (N1 k : ℝ) * ((k : ℝ) ^ (-s) - ((k + 1 : ℕ) : ℝ) ^ (-s))
        ≤ (C * s) * (((M - 1 : ℕ) : ℝ) ^ α / α) := h1.trans h2
      _ ≤ (C * s) * ((M : ℝ) ^ α / α) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hM1 hα0.le) (by positivity)
      _ = (s / α) * C * (M : ℝ) ^ α := by ring
  -- Bound the leading term
  have hlead : (N1 M : ℝ) * (M : ℝ) ^ (-s) ≤ C * (M : ℝ) ^ α := by
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
    have hcnt := hcount M hM le_rfl
    calc (N1 M : ℝ) * (M : ℝ) ^ (-s)
        ≤ (C * (M : ℝ) ^ b) * (M : ℝ) ^ (-s) := mul_le_mul_of_nonneg_right hcnt (by positivity)
      _ = C * ((M : ℝ) ^ b * (M : ℝ) ^ (-s)) := by ring
      _ = C * (M : ℝ) ^ α := by rw [← Real.rpow_add hMpos, ← sub_eq_add_neg]
  have hcombine : C * (M : ℝ) ^ α + (s / α) * C * (M : ℝ) ^ α = (b / α) * C * (M : ℝ) ^ α := by
    have hαne : α ≠ 0 := hα0.ne'
    unfold α at hαne ⊢
    field_simp
    ring
  linarith

/-- `(K + 1) * r^K → 0` for `0 ≤ r < 1`. -/
lemma tendsto_add_one_mul_pow_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Filter.Tendsto (fun K : ℕ => ((K : ℝ) + 1) * r ^ K) Filter.atTop (nhds 0) := by
  rcases eq_or_lt_of_le hr0 with rfl | hrpos
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with K hK
    have : (0 : ℝ) ^ K = 0 := zero_pow (by omega)
    simp [this]
  · set s : ℝ := (1 + r) / 2
    have hs0 : 0 ≤ s := by unfold s; linarith
    have hs1 : s < 1 := by unfold s; linarith
    set δ : ℝ := (1 - r) / (2 * r)
    have hδ : 0 < δ := div_pos (by linarith) (by linarith)
    have hsr : s = r * (1 + δ) := by unfold s δ; field_simp; ring
    have hbern : ∀ K : ℕ, 1 + (K : ℝ) * δ ≤ (1 + δ) ^ K := by
      intro K
      induction K with
      | zero => simp
      | succ K ih =>
        rw [pow_succ]
        push_cast
        have h1 : (1 + (K : ℝ) * δ) * (1 + δ) ≤ (1 + δ) ^ K * (1 + δ) :=
          mul_le_mul_of_nonneg_right ih (by linarith)
        have h2 : 0 ≤ (K : ℝ) * δ * δ := by positivity
        nlinarith
    have hdom : ∀ K : ℕ, ((K : ℝ) + 1) * r ^ K ≤ (1 + 1 / δ) * s ^ K := by
      intro K
      have hpos : 0 < (1 + δ) ^ K := by positivity
      have h1 : ((K : ℝ) + 1) ≤ (1 + 1 / δ) * (1 + (K : ℝ) * δ) := by
        have hrew : (1 + 1 / δ) * (1 + (K : ℝ) * δ) = 1 + (K : ℝ) + 1 / δ + (K : ℝ) * δ := by
          field_simp; ring
        have : 0 ≤ 1 / δ + (K : ℝ) * δ := by positivity
        linarith
      have h2 : ((K : ℝ) + 1) ≤ (1 + 1 / δ) * (1 + δ) ^ K :=
        h1.trans (mul_le_mul_of_nonneg_left (hbern K) (by positivity))
      have h3 := mul_le_mul_of_nonneg_right h2 (pow_nonneg hrpos.le K)
      rw [hsr, mul_pow]
      linarith
    have htend_dom : Filter.Tendsto (fun K : ℕ => (1 + 1 / δ) * s ^ K) Filter.atTop (nhds 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hs0 hs1).const_mul (1 + 1 / δ)
      simpa using h
    exact squeeze_zero (fun K => by positivity) hdom htend_dom

/-! ## Section 3: Forward 3-state weighted word bound (Case 2) -/

/-- Odd digit `d(x) ∈ {1, 5, 7}` associated with class `c ∈ {A, B, C}`. -/
def clsDigit (c : Fin 3) : ℕ :=
  match c.val with
  | 0 => 1
  | 1 => 5
  | _ => 7

/-- Next class determined by `(c, v)` along an admissible forward edge. -/
def nextCls (c : Fin 3) (v : ℕ) : Fin 3 :=
  match c.val with
  | 0 => if v % 4 = 1 then 0 else 2
  | 1 => if v % 4 = 0 then 0 else 2
  | _ => 1

lemma admEdge_iff_nextCls (c c' : Fin 3) (v : ℕ) (h : admEdge c c' v = true) :
    c' = nextCls c v := by
  fin_cases c <;> fin_cases c' <;> simp [admEdge, nextCls] at h ⊢ <;> omega

/-- Digit product along an admissible forward word `w` starting at class `c`. -/
def wordDigitProd : Fin 3 → List ℕ → ℕ
  | _, [] => 1
  | c, v :: vs => clsDigit c * wordDigitProd (nextCls c v) vs

/-- Certified 3-state forward super-eigenvector `h_F` at `(a_F, s_F) = (0.6331, 7/100)`. -/
noncomputable def hFVec (c : Fin 3) : ℝ :=
  match c.val with
  | 0 => 3853879722 / 1000000
  | 1 => 2499010185 / 1000000
  | _ => 4942394081 / 1000000

private lemma hFVec_ge_one (c : Fin 3) : 1 ≤ hFVec c := by
  fin_cases c <;> norm_num [hFVec]

private lemma hFVec_sub_eig :
    (aFVal / (1 - aFVal ^ 4)) * hFVec 0 + (aFVal ^ 4 / (1 - aFVal ^ 4)) * hFVec 2 ≤ hFVec 0 ∧
    (5 : ℝ) ^ sFVal * ((aFVal ^ 4 / (1 - aFVal ^ 4)) * hFVec 0 +
      (aFVal ^ 3 / (1 - aFVal ^ 4)) * hFVec 2) ≤ hFVec 1 ∧
    (7 : ℝ) ^ sFVal * ((aFVal / (1 - aFVal)) * hFVec 1) ≤ hFVec 2 := by
  have h5 := five_rpow_sF_le
  have h7 := seven_rpow_sF_le
  refine ⟨by norm_num [aFVal, hFVec], ?_, ?_⟩
  · have hpos : (0 : ℝ) ≤ (aFVal ^ 4 / (1 - aFVal ^ 4)) * hFVec 0 +
        (aFVal ^ 3 / (1 - aFVal ^ 4)) * hFVec 2 := by norm_num [aFVal, hFVec]
    have hmul := mul_le_mul_of_nonneg_right h5 hpos
    have hnum : (11193 / 10000 : ℝ) * ((aFVal ^ 4 / (1 - aFVal ^ 4)) * hFVec 0 +
        (aFVal ^ 3 / (1 - aFVal ^ 4)) * hFVec 2) ≤ hFVec 1 := by norm_num [aFVal, hFVec]
    linarith
  · have hpos : (0 : ℝ) ≤ (aFVal / (1 - aFVal)) * hFVec 1 := by norm_num [aFVal, hFVec]
    have hmul := mul_le_mul_of_nonneg_right h7 hpos
    have hnum : (11460 / 10000 : ℝ) * ((aFVal / (1 - aFVal)) * hFVec 1) ≤ hFVec 2 := by
      norm_num [aFVal, hFVec]
    linarith

private lemma finset_sum_biUnion_le {ι α : Type*} [DecidableEq ι] [DecidableEq α] {s : Finset ι}
    {t : ι → Finset α} {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    have hnn : 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, f x := Finset.sum_nonneg fun x _ => hf x
    linarith

/-- Forward weighted word bound:
    `a_F^L * ∑_{w ∈ admWords c L} D(c, w)^{s_F} ≤ h_F(c)` for all `L ≥ 0` and `c ∈ Fin 3`. -/
theorem admWords_weighted_bound (L : ℕ) :
    ∀ c : Fin 3, aFVal ^ L * ∑ w ∈ admWords c L, (wordDigitProd c w : ℝ) ^ sFVal ≤ hFVec c := by
  have ha0 : 0 < aFVal := by norm_num [aFVal]
  have ha1 : aFVal < 1 := by norm_num [aFVal]
  have hs0 : 0 ≤ sFVal := by norm_num [sFVal]
  obtain ⟨heq0, heq1, heq2⟩ := hFVec_sub_eig
  induction L using Nat.strong_induction_on with
  | h L ih =>
    intro c
    match L with
    | 0 =>
      simp only [admWords, Finset.sum_singleton, wordDigitProd, Nat.cast_one, Real.one_rpow,
        pow_zero, one_mul]
      exact hFVec_ge_one c
    | L + 1 =>
      have hsum_le : ∑ w ∈ admWords c (L + 1), (wordDigitProd c w : ℝ) ^ sFVal ≤
          ∑ v ∈ Finset.Icc 1 (L + 1), ∑ c' : Fin 3,
            if admEdge c c' v then
              (clsDigit c : ℝ) ^ sFVal *
                ∑ w' ∈ admWords c' (L + 1 - v), (wordDigitProd c' w' : ℝ) ^ sFVal
            else 0 := by
        conv_lhs => unfold admWords
        have h1 : ∑ w ∈ ((Finset.Icc 1 (L + 1)).attach.biUnion fun ⟨v, _⟩ =>
              Finset.univ.biUnion fun c' : Fin 3 =>
                if admEdge c c' v then (admWords c' (L + 1 - v)).image (v :: ·) else ∅),
              (wordDigitProd c w : ℝ) ^ sFVal ≤
            ∑ v ∈ (Finset.Icc 1 (L + 1)).attach, ∑ c' : Fin 3,
              if admEdge c c' v.val then
                (clsDigit c : ℝ) ^ sFVal *
                  ∑ w' ∈ admWords c' (L + 1 - v.val), (wordDigitProd c' w' : ℝ) ^ sFVal
              else 0 := by
          refine (finset_sum_biUnion_le fun _ => by positivity).trans
            (Finset.sum_le_sum fun v _ => ?_)
          rcases v with ⟨v, hv⟩
          dsimp only
          refine (finset_sum_biUnion_le fun _ => by positivity).trans
            (Finset.sum_le_sum fun c' _ => ?_)
          split_ifs with he
          · have hc' : c' = nextCls c v := admEdge_iff_nextCls c c' v he
            apply le_of_eq
            calc ∑ w ∈ (admWords c' (L + 1 - v)).image (v :: ·),
                    (wordDigitProd c w : ℝ) ^ sFVal
                = ∑ w' ∈ admWords c' (L + 1 - v),
                    (wordDigitProd c (v :: w') : ℝ) ^ sFVal :=
                  Finset.sum_image fun _ _ _ _ h => (List.cons.inj h).2
              _ = (clsDigit c : ℝ) ^ sFVal *
                    ∑ w' ∈ admWords c' (L + 1 - v), (wordDigitProd c' w' : ℝ) ^ sFVal := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun w' _ => ?_
                  simp only [wordDigitProd, ← hc', Nat.cast_mul]
                  rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
          · simp
        exact h1.trans_eq (Finset.sum_attach (Finset.Icc 1 (L + 1)) fun v =>
          ∑ c' : Fin 3, if admEdge c c' v then
            (clsDigit c : ℝ) ^ sFVal *
              ∑ w' ∈ admWords c' (L + 1 - v), (wordDigitProd c' w' : ℝ) ^ sFVal
          else 0)
      have hstep : aFVal ^ (L + 1) * ∑ w ∈ admWords c (L + 1), (wordDigitProd c w : ℝ) ^ sFVal ≤
          (clsDigit c : ℝ) ^ sFVal *
            ∑ c' : Fin 3,
              (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge c c' v = true), aFVal ^ v) *
                hFVec c' := by
        have hmul := mul_le_mul_of_nonneg_left hsum_le (by positivity : 0 ≤ aFVal ^ (L + 1))
        refine hmul.trans ?_
        rw [Finset.mul_sum]
        have hpush : ∑ v ∈ Finset.Icc 1 (L + 1),
              aFVal ^ (L + 1) * ∑ c' : Fin 3,
                (if admEdge c c' v then
                  (clsDigit c : ℝ) ^ sFVal *
                    ∑ w' ∈ admWords c' (L + 1 - v), (wordDigitProd c' w' : ℝ) ^ sFVal
                else 0) ≤
            ∑ v ∈ Finset.Icc 1 (L + 1), ∑ c' : Fin 3,
              if admEdge c c' v then (clsDigit c : ℝ) ^ sFVal * (aFVal ^ v * hFVec c') else 0 := by
          refine Finset.sum_le_sum fun v hv => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun c' _ => ?_
          split_ifs with he
          · simp only [Finset.mem_Icc] at hv
            have hpow : aFVal ^ (L + 1) = aFVal ^ v * aFVal ^ (L + 1 - v) := by
              rw [← pow_add, Nat.add_sub_of_le hv.2]
            have hih := ih (L + 1 - v) (by omega) c'
            calc aFVal ^ (L + 1) * ((clsDigit c : ℝ) ^ sFVal *
                    ∑ w' ∈ admWords c' (L + 1 - v), (wordDigitProd c' w' : ℝ) ^ sFVal)
                = (clsDigit c : ℝ) ^ sFVal * (aFVal ^ v *
                    (aFVal ^ (L + 1 - v) *
                      ∑ w' ∈ admWords c' (L + 1 - v), (wordDigitProd c' w' : ℝ) ^ sFVal)) := by
                  rw [hpow]; ring
              _ ≤ (clsDigit c : ℝ) ^ sFVal * (aFVal ^ v * hFVec c') :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hih (by positivity))
                    (by positivity)
          · simp
        refine hpush.trans_eq ?_
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs <;> ring
      refine hstep.trans ?_
      rw [Fin.sum_univ_three]
      have hp0 : 0 ≤ hFVec 0 := by linarith [hFVec_ge_one 0]
      have hp1 : 0 ≤ hFVec 1 := by linarith [hFVec_ge_one 1]
      have hp2 : 0 ≤ hFVec 2 := by linarith [hFVec_ge_one 2]
      fin_cases c
      · dsimp only [clsDigit]
        simp only [Nat.cast_one, Real.one_rpow, one_mul]
        have hf0 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 0 0 v = true) =
            (Finset.Icc 1 (L + 1)).filter (fun v => v % 4 = 1 % 4) :=
          Finset.filter_congr fun v hv => by simp [admEdge, (Finset.mem_Icc.mp hv).1]
        have hf1 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 0 1 v = true) = ∅ :=
          Finset.filter_eq_empty_iff.mpr fun v _ => by simp [admEdge]
        have hf2 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 0 2 v = true) =
            (Finset.Icc 1 (L + 1)).filter (fun v => v % 4 = 4 % 4) :=
          Finset.filter_congr fun v hv => by simp [admEdge, (Finset.mem_Icc.mp hv).1]
        change (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 0 0 v = true), aFVal ^ v) * hFVec 0 +
            (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 0 1 v = true), aFVal ^ v) * hFVec 1 +
            (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 0 2 v = true), aFVal ^ v) * hFVec 2 ≤ hFVec 0
        rw [hf0, hf1, hf2, Finset.sum_empty, zero_mul, add_zero]
        have hg0 := finite_geom_step4_le ha0 ha1 1 (L + 1) (by omega) (by omega)
        have hg2 := finite_geom_step4_le ha0 ha1 4 (L + 1) (by omega) (by omega)
        rw [pow_one] at hg0
        exact (add_le_add (mul_le_mul_of_nonneg_right hg0 hp0)
          (mul_le_mul_of_nonneg_right hg2 hp2)).trans heq0
      · dsimp only [clsDigit]
        have hf0 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 1 0 v = true) =
            (Finset.Icc 1 (L + 1)).filter (fun v => v % 4 = 4 % 4) :=
          Finset.filter_congr fun v hv => by simp [admEdge, (Finset.mem_Icc.mp hv).1]
        have hf1 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 1 1 v = true) = ∅ :=
          Finset.filter_eq_empty_iff.mpr fun v _ => by simp [admEdge]
        have hf2 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 1 2 v = true) =
            (Finset.Icc 1 (L + 1)).filter (fun v => v % 4 = 3 % 4) :=
          Finset.filter_congr fun v hv => by simp [admEdge, (Finset.mem_Icc.mp hv).1]
        change ((5 : ℕ) : ℝ) ^ sFVal *
            ((∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 1 0 v = true), aFVal ^ v) * hFVec 0 +
             (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 1 1 v = true), aFVal ^ v) * hFVec 1 +
             (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 1 2 v = true), aFVal ^ v) * hFVec 2) ≤ hFVec 1
        rw [hf0, hf1, hf2, Finset.sum_empty, zero_mul, add_zero]
        have hg0 := finite_geom_step4_le ha0 ha1 4 (L + 1) (by omega) (by omega)
        have hg2 := finite_geom_step4_le ha0 ha1 3 (L + 1) (by omega) (by omega)
        push_cast
        exact (mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_right hg0 hp0) (mul_le_mul_of_nonneg_right hg2 hp2))
          (by positivity)).trans heq1
      · dsimp only [clsDigit]
        have hf0 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 2 0 v = true) = ∅ :=
          Finset.filter_eq_empty_iff.mpr fun v _ => by simp [admEdge]
        have hf1 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 2 1 v = true) = Finset.Icc 1 (L + 1) :=
          Finset.filter_true_of_mem fun v hv => by simp [admEdge, (Finset.mem_Icc.mp hv).1]
        have hf2 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 2 2 v = true) = ∅ :=
          Finset.filter_eq_empty_iff.mpr fun v _ => by simp [admEdge]
        change ((7 : ℕ) : ℝ) ^ sFVal *
            ((∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 2 0 v = true), aFVal ^ v) * hFVec 0 +
             (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 2 1 v = true), aFVal ^ v) * hFVec 1 +
             (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 2 2 v = true), aFVal ^ v) * hFVec 2) ≤ hFVec 2
        rw [hf0, hf1, hf2, Finset.sum_empty, zero_mul, zero_add, zero_mul, add_zero]
        have hg1 := finite_geom_step1_le ha0 ha1 (L + 1)
        push_cast
        exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg1 hp1) (by positivity)).trans heq2

/-! ## Section 4: Backward move tree and master weighted path bound -/

/-- Unique backward move `(d_mv, m)` from `o ∈ A ∪ B ∪ C` at halving count `v ≥ 1`. -/
def backPred (o v : ℕ) : Option (ℕ × ℕ) :=
  if o % 15 = 1 then
    if v % 4 = 1 then some (1, 2 ^ v * o - 1)
    else if (2 ^ v * o) % 25 = 1 then some (5, (2 ^ v * o - 1) / 5)
    else none
  else if o % 15 = 2 then
    if v % 4 = 0 then some (1, 2 ^ v * o - 1)
    else if (2 ^ v * o) % 25 = 1 then some (5, (2 ^ v * o - 1) / 5)
    else none
  else if o % 15 = 0 then
    if (2 ^ v * o) % 7 = 1 then some (7, (2 ^ v * o - 1) / 7)
    else none
  else none

lemma backPred_of_move {o v m : ℕ} (ho : InABC15 o) (hv : 1 ≤ v) (hm_odd : m % 2 = 1)
    (heq : d m * m + 1 = 2 ^ v * o) :
    backPred o v = some (d m, m) := by
  have hcl := lem_basin1_moves_classify ho hv hm_odd heq
  rcases hcl.2.2.2 with ⟨h15, hd, hv4, _⟩ | ⟨h15, hd, hv4, _⟩ | ⟨h15, hd, h25, _⟩ | ⟨h15, hd, h7, _⟩
  · unfold backPred; rw [hd] at heq ⊢; simp [h15, hv4]; omega
  · unfold backPred; rw [hd] at heq ⊢; simp [h15, hv4]; omega
  · rcases h15 with h15 | h15
    · have hv4 : v % 4 ≠ 1 := by
        intro hv1
        have h2v : 2 ^ v % 5 = 2 := by
          have : v = 4 * (v / 4) + 1 := by omega
          rw [this, pow_add, pow_one, Nat.mul_mod]
          have h4 := two_pow_mod_15_of_four_dvd (dvd_mul_right 4 (v / 4))
          have : 2 ^ (4 * (v / 4)) % 5 = 1 := by omega
          rw [this]
        have : (2 ^ v * o) % 5 = 2 := by rw [Nat.mul_mod, h2v, show o % 5 = 1 by omega]
        omega
      unfold backPred; rw [hd] at heq ⊢; simp [h15, hv4, h25]; omega
    · have hv4 : v % 4 ≠ 0 := by
        intro hv0
        have h4 := two_pow_mod_15_of_four_dvd (Nat.dvd_of_mod_eq_zero hv0)
        have : (2 ^ v * o) % 5 = 2 := by rw [Nat.mul_mod, show 2 ^ v % 5 = 1 by omega, show o % 5 = 2 by omega]
        omega
      unfold backPred; rw [hd] at heq ⊢; simp [h15, hv4, h25]; omega
  · unfold backPred; rw [hd] at heq ⊢; simp [h15, h7]; omega

lemma backPred_mem_InABC15 {o v d_mv m : ℕ} (ho : InABC15 o) (hv : 1 ≤ v)
    (h : backPred o v = some (d_mv, m)) :
    InABC15 m ∧ d m = d_mv ∧ d_mv * m + 1 = 2 ^ v * o := by
  have ho_pos : 0 < o := ho.1
  have ho_odd : o % 2 = 1 := ho.2.1
  have h2v_ge : 2 ≤ 2 ^ v := calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv
  have h2vo_ge : 2 ≤ 2 ^ v * o := by nlinarith
  have h2vo_ev : (2 ^ v * o) % 2 = 0 := by
    have : v = (v - 1) + 1 := by omega
    rw [this, pow_succ', mul_assoc]; omega
  rcases ho.2.2 with h15 | h15 | h15
  · unfold backPred at h
    simp only [h15, ↓reduceIte] at h
    by_cases hv1 : v % 4 = 1
    · simp only [hv1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h2v5 : (2 ^ v * o) % 5 = 2 := by
        have : v = 4 * (v / 4) + 1 := by omega
        rw [this, pow_add, pow_one, mul_assoc, Nat.mul_mod]
        have h4 := two_pow_mod_15_of_four_dvd (dvd_mul_right 4 (v / 4))
        have : 2 ^ (4 * (v / 4)) % 5 = 1 := by omega
        rw [this]; omega
      have h2v3 : (2 ^ v * o) % 3 = 2 := by
        have hodd : v % 2 = 1 := by omega
        have h2_3 : 2 ^ v % 3 = 2 := by
          have : v = 2 * (v / 2) + 1 := by omega
          rw [this, pow_add, pow_one, Nat.mul_mod]
          have hsq : 2 ^ (2 * (v / 2)) % 3 = 1 := by
            rw [pow_mul]
            induction (v / 2) with
            | zero => decide
            | succ k ih => rw [pow_succ, Nat.mul_mod, ih]; decide
          rw [hsq]
        rw [Nat.mul_mod, h2_3, show o % 3 = 1 by omega]
      exact ⟨⟨by omega, by omega, Or.inl (by omega)⟩, by unfold d; omega, by omega⟩
    · simp only [hv1, ↓reduceIte] at h
      by_cases h25 : (2 ^ v * o) % 25 = 1
      · simp only [h25, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hm_pos, hm_odd, hdm, heq, _⟩ :=
          lemma_odd_predecessors_unique ho_pos ho_odd hv 2 (by simpa [predCond] using h25)
        have hd2 : digitVal 2 = 5 := rfl
        rw [hd2] at hm_pos hm_odd hdm heq
        have hcl := lem_basin1_moves_classify ho hv hm_odd heq
        exact ⟨hcl.2.2.1, hdm, by rwa [hdm] at heq⟩
      · simp [h25] at h
  · unfold backPred at h
    simp only [h15, show ¬(0 = 1) by decide, show ¬(0 = 2) by decide, ↓reduceIte] at h
    by_cases h7 : (2 ^ v * o) % 7 = 1
    · simp only [h7, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hcond : predCond 3 (2 ^ v * o) := by
        simp only [predCond]; exact ⟨by rw [Nat.mul_mod, show o % 5 = 0 by omega]; simp, h7⟩
      obtain ⟨hm_pos, hm_odd, hdm, heq, _⟩ :=
        lemma_odd_predecessors_unique ho_pos ho_odd hv 3 hcond
      have hd3 : digitVal 3 = 7 := rfl
      rw [hd3] at hm_pos hm_odd hdm heq
      have hcl := lem_basin1_moves_classify ho hv hm_odd heq
      exact ⟨hcl.2.2.1, hdm, by rwa [hdm] at heq⟩
    · simp [h7] at h
  · unfold backPred at h
    simp only [h15, show ¬(2 = 1) by decide, ↓reduceIte] at h
    by_cases hv0 : v % 4 = 0
    · simp only [hv0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h4 := two_pow_mod_15_of_four_dvd (Nat.dvd_of_mod_eq_zero hv0)
      have h2v15 : (2 ^ v * o) % 15 = 2 := by rw [Nat.mul_mod, h4, h15]
      exact ⟨⟨by omega, by omega, Or.inl (by omega)⟩, by unfold d; omega, by omega⟩
    · simp only [hv0, ↓reduceIte] at h
      by_cases h25 : (2 ^ v * o) % 25 = 1
      · simp only [h25, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hm_pos, hm_odd, hdm, heq, _⟩ :=
          lemma_odd_predecessors_unique ho_pos ho_odd hv 2 (by simpa [predCond] using h25)
        have hd2 : digitVal 2 = 5 := rfl
        rw [hd2] at hm_pos hm_odd hdm heq
        have hcl := lem_basin1_moves_classify ho hv hm_odd heq
        exact ⟨hcl.2.2.1, hdm, by rwa [hdm] at heq⟩
      · simp [h25] at h

/-- Finite set of reverse valuation lists of exact sum `L` starting from `o`. -/
def backPaths (o : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | L + 1 =>
    (Finset.Icc 1 (L + 1)).attach.biUnion fun ⟨v, _⟩ =>
      match backPred o v with
      | some (_, m) => (backPaths m (L + 1 - v)).image (v :: ·)
      | none => ∅
termination_by L => L
decreasing_by
  simp_wf
  have := (Finset.mem_Icc.mp ‹_›).1
  omega

/-- Endpoint and digit product obtained by following reverse valuation list `l` from `o`. -/
def backEnd (o : ℕ) : List ℕ → ℕ × ℕ
  | [] => (o, 1)
  | v :: vs =>
    match backPred o v with
    | some (d_mv, m) =>
      let p := backEnd m vs
      (p.1, d_mv * p.2)
    | none => (o, 1)

/-- Master backward weighted path bound: if `w ≥ 1` on `A ∪ B ∪ C` satisfies
    `∑_{v=1}^L d^s a^v w(m) ≤ w(o)` for every `o ∈ A ∪ B ∪ C` and `L ≥ 0`, then
    `a^L ∑_{l ∈ backPaths o L} D(o, l)^s ≤ w(o)`. -/
theorem backPaths_weighted_bound {a s : ℝ} (ha0 : 0 < a)
    (w : ℕ → ℝ) (hw1 : ∀ o, InABC15 o → 1 ≤ w o)
    (hrow : ∀ o L, InABC15 o →
      ∑ v ∈ Finset.Icc 1 L,
        (match backPred o v with
         | some (d_mv, m) => (d_mv : ℝ) ^ s * a ^ v * w m
         | none => 0) ≤ w o) :
    ∀ L o, InABC15 o →
      a ^ L * ∑ l ∈ backPaths o L, ((backEnd o l).2 : ℝ) ^ s ≤ w o := by
  intro L
  induction L using Nat.strong_induction_on with
  | h L ih =>
    intro o ho
    match L with
    | 0 =>
      simp only [backPaths, Finset.sum_singleton, backEnd, Nat.cast_one, Real.one_rpow,
        pow_zero, one_mul]
      exact hw1 o ho
    | L + 1 =>
      have hsum_le : ∑ l ∈ backPaths o (L + 1), ((backEnd o l).2 : ℝ) ^ s ≤
          ∑ v ∈ Finset.Icc 1 (L + 1),
            match backPred o v with
            | some (d_mv, m) =>
              (d_mv : ℝ) ^ s * ∑ l' ∈ backPaths m (L + 1 - v), ((backEnd m l').2 : ℝ) ^ s
            | none => 0 := by
        conv_lhs => unfold backPaths
        have h1 : ∑ l ∈ ((Finset.Icc 1 (L + 1)).attach.biUnion fun ⟨v, _⟩ =>
              match backPred o v with
              | some (_, m) => (backPaths m (L + 1 - v)).image (v :: ·)
              | none => ∅), ((backEnd o l).2 : ℝ) ^ s ≤
            ∑ v ∈ (Finset.Icc 1 (L + 1)).attach,
              match backPred o v.val with
              | some (d_mv, m) =>
                (d_mv : ℝ) ^ s * ∑ l' ∈ backPaths m (L + 1 - v.val), ((backEnd m l').2 : ℝ) ^ s
              | none => 0 := by
          refine (finset_sum_biUnion_le fun _ => by positivity).trans
            (Finset.sum_le_sum fun v _ => ?_)
          rcases v with ⟨v, hv⟩
          dsimp only
          cases hbp : backPred o v with
          | none => simp
          | some p =>
            rcases p with ⟨d_mv, m⟩
            apply le_of_eq
            calc ∑ l ∈ (backPaths m (L + 1 - v)).image (v :: ·),
                    ((backEnd o l).2 : ℝ) ^ s
                = ∑ l' ∈ backPaths m (L + 1 - v),
                    ((backEnd o (v :: l')).2 : ℝ) ^ s :=
                  Finset.sum_image fun _ _ _ _ h => (List.cons.inj h).2
              _ = (d_mv : ℝ) ^ s *
                    ∑ l' ∈ backPaths m (L + 1 - v), ((backEnd m l').2 : ℝ) ^ s := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun l' _ => ?_
                  simp only [backEnd, hbp, Nat.cast_mul]
                  rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
        exact h1.trans_eq (Finset.sum_attach (Finset.Icc 1 (L + 1)) fun v =>
          match backPred o v with
          | some (d_mv, m) =>
            (d_mv : ℝ) ^ s * ∑ l' ∈ backPaths m (L + 1 - v), ((backEnd m l').2 : ℝ) ^ s
          | none => 0)
      have hmul := mul_le_mul_of_nonneg_left hsum_le (by positivity : 0 ≤ a ^ (L + 1))
      refine hmul.trans ?_
      rw [Finset.mul_sum]
      refine (Finset.sum_le_sum fun v hv => ?_).trans (hrow o (L + 1) ho)
      simp only [Finset.mem_Icc] at hv
      cases hbp : backPred o v with
      | none => simp
      | some p =>
        rcases p with ⟨d_mv, m⟩
        have hm_abc : InABC15 m := (backPred_mem_InABC15 ho hv.1 hbp).1
        have hih := ih (L + 1 - v) (by omega) m hm_abc
        have hpow : a ^ (L + 1) = a ^ v * a ^ (L + 1 - v) := by
          rw [← pow_add, Nat.add_sub_of_le hv.2]
        calc a ^ (L + 1) * ((d_mv : ℝ) ^ s *
                ∑ l' ∈ backPaths m (L + 1 - v), ((backEnd m l').2 : ℝ) ^ s)
            = (d_mv : ℝ) ^ s * a ^ v *
                (a ^ (L + 1 - v) * ∑ l' ∈ backPaths m (L + 1 - v), ((backEnd m l').2 : ℝ) ^ s) := by
              rw [hpow]; ring
          _ ≤ (d_mv : ℝ) ^ s * a ^ v * w m :=
              mul_le_mul_of_nonneg_left hih (by positivity)

/-! ## Section 5: Case 1 (3-state depth bound at `a_H = 2/3`) -/

private lemma two_pow_mod_25_period (v : ℕ) : 2 ^ v % 25 = 2 ^ (v % 20) % 25 := by
  have hdiv : v = 20 * (v / 20) + v % 20 := (Nat.div_add_mod v 20).symm
  conv_lhs => rw [hdiv, pow_add, Nat.mul_mod]
  have h20 : 2 ^ (20 * (v / 20)) % 25 = 1 := by
    rw [pow_mul]
    have : 2 ^ 20 % 25 = 1 := by decide
    induction (v / 20) with
    | zero => decide
    | succ k ih => rw [pow_succ, Nat.mul_mod, ih, this]
  rw [h20, one_mul, Nat.mod_mod]

private lemma two_pow_mod_25_eq_one_iff (o v : ℕ) :
    (2 ^ v * o) % 25 = 1 ↔ (2 ^ (v % 20) * (o % 25)) % 25 = 1 := by
  rw [Nat.mul_mod, two_pow_mod_25_period v, Nat.mul_mod (2 ^ (v % 20)) (o % 25), Nat.mod_mod]

/-- Unique residue class mod `20` solving `2^v * o ≡ 1 (mod 25)` when `o % 5 ∈ {1, 2}`. -/
def v5Class (r25 : ℕ) : ℕ :=
  match r25 with
  | 1 => 20 | 6 => 12 | 11 => 4 | 16 => 16 | 21 => 8
  | 2 => 19 | 7 => 15 | 12 => 11 | 17 => 7 | 22 => 3
  | _ => 0

private lemma v5Class_spec (o v : ℕ) (h5 : o % 5 = 1 ∨ o % 5 = 2) :
    (2 ^ v * o) % 25 = 1 ↔ v % 20 = v5Class (o % 25) % 20 := by
  rw [two_pow_mod_25_eq_one_iff]
  have h25 : o % 25 = 1 ∨ o % 25 = 6 ∨ o % 25 = 11 ∨ o % 25 = 16 ∨ o % 25 = 21 ∨
      o % 25 = 2 ∨ o % 25 = 7 ∨ o % 25 = 12 ∨ o % 25 = 17 ∨ o % 25 = 22 := by omega
  have hv20 : v % 20 < 20 := Nat.mod_lt v (by omega)
  rcases h25 with h | h | h | h | h | h | h | h | h | h <;>
    (rw [h]; interval_cases (v % 20) <;> decide)

private lemma two_pow_mod_7_period (v : ℕ) : 2 ^ v % 7 = 2 ^ (v % 3) % 7 := by
  have hdiv : v = 3 * (v / 3) + v % 3 := (Nat.div_add_mod v 3).symm
  conv_lhs => rw [hdiv, pow_add, Nat.mul_mod]
  have h3 : 2 ^ (3 * (v / 3)) % 7 = 1 := by
    rw [pow_mul]
    have : 2 ^ 3 % 7 = 1 := by decide
    induction (v / 3) with
    | zero => decide
    | succ k ih => rw [pow_succ, Nat.mul_mod, ih, this]
  rw [h3, one_mul, Nat.mod_mod]

private lemma two_pow_mod_7_eq_one_cases (o : ℕ) :
    ((o % 7 = 4 → ∀ v, (2 ^ v * o) % 7 = 1 ↔ v % 3 = 1) ∧
     (o % 7 = 2 → ∀ v, (2 ^ v * o) % 7 = 1 ↔ v % 3 = 2) ∧
     (o % 7 = 1 → ∀ v, (2 ^ v * o) % 7 = 1 ↔ v % 3 = 0) ∧
     (o % 7 ≠ 1 → o % 7 ≠ 2 → o % 7 ≠ 4 → ∀ v, (2 ^ v * o) % 7 ≠ 1)) := by
  have hmod : ∀ v, (2 ^ v * o) % 7 = (2 ^ (v % 3) % 7 * (o % 7)) % 7 := fun v => by
    rw [Nat.mul_mod, two_pow_mod_7_period v]
  have ho7 : o % 7 < 7 := Nat.mod_lt o (by omega)
  refine ⟨fun h v => ?_, fun h v => ?_, fun h v => ?_, fun h1 h2 h4 v => ?_⟩
  · have hv3 : v % 3 < 3 := Nat.mod_lt v (by omega)
    rw [hmod v, h]; interval_cases (v % 3) <;> decide
  · have hv3 : v % 3 < 3 := Nat.mod_lt v (by omega)
    rw [hmod v, h]; interval_cases (v % 3) <;> decide
  · have hv3 : v % 3 < 3 := Nat.mod_lt v (by omega)
    rw [hmod v, h]; interval_cases (v % 3) <;> decide
  · have hv3 : v % 3 < 3 := Nat.mod_lt v (by omega)
    rw [hmod v]; interval_cases (o % 7) <;> interval_cases (v % 3) <;> simp_all

/-- 3-state depth weight vector `w_H`: `10` on `A`, `4` on `B ∪ C`. -/
noncomputable def wHVec (o : ℕ) : ℝ :=
  if o % 15 = 1 then 10 else 4

/-- Case 1 (3-state depth bound): for every `L ≥ 0` and `o ∈ A ∪ B ∪ C`,
    `(2/3)^L * |backPaths o L| ≤ wHVec o`. -/
theorem depth_backPaths_bound (L o : ℕ) (ho : InABC15 o) :
    aHVal ^ L * ((backPaths o L).card : ℝ) ≤ wHVec o := by
  have ha0 : 0 < aHVal := by norm_num [aHVal]
  have ha1 : aHVal < 1 := by norm_num [aHVal]
  have hmain := backPaths_weighted_bound (a := aHVal) (s := 0) ha0 wHVec
    (fun x _ => by unfold wHVec; split_ifs <;> norm_num) ?_ L o ho
  · simpa only [Real.rpow_zero, Finset.sum_const, nsmul_eq_mul, mul_one] using hmain
  · intro x M hx
    simp only [Real.rpow_zero, one_mul]
    rcases hx.2.2 with h15 | h15 | h15
    · -- x ∈ A (x % 15 = 1): d=1 at v%4=1 (to A, weight 10), d=5 at v≡v5 (mod 20), v≥4 (to B, weight 4)
      have h5 : x % 5 = 1 := by omega
      have hsplit : ∑ v ∈ Finset.Icc 1 M,
            (match backPred x v with | some (_, m) => aHVal ^ v * wHVec m | none => 0) ≤
          (∑ v ∈ (Finset.Icc 1 M).filter (fun v => v % 4 = 1 % 4), aHVal ^ v) * 10 +
          (∑ v ∈ (Finset.Icc 4 M).filter (fun v => v % 20 = v5Class (x % 25) % 20), aHVal ^ v) * 4 := by
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_filter, Finset.sum_filter]
        have hsub4 : ∑ v ∈ Finset.Icc 4 M,
              (if v % 20 = v5Class (x % 25) % 20 then aHVal ^ v * 4 else 0) =
            ∑ v ∈ Finset.Icc 1 M,
              (if 4 ≤ v ∧ v % 20 = v5Class (x % 25) % 20 then aHVal ^ v * 4 else 0) := by
          rw [← Finset.sum_filter, ← Finset.sum_filter]
          congr 1; ext v; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
        rw [hsub4, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun v hv => ?_
        have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1
        unfold backPred
        simp only [h15, ↓reduceIte]
        by_cases hv4 : v % 4 = 1
        · simp only [hv4, ↓reduceIte]
          have hm15 : (2 ^ v * x - 1) % 15 = 1 := by
            have hbp : backPred x v = some (1, 2 ^ v * x - 1) := by unfold backPred; simp [h15, hv4]
            have hm := backPred_mem_InABC15 hx hv1 hbp
            have hcl := lem_basin1_moves_classify hx hv1 hm.1.2.1 (by rw [hm.2.1]; exact hm.2.2)
            rcases hcl.2.2.2 with ⟨_, _, _, hm1⟩ | ⟨h2, _, _, _⟩ | ⟨_, hd, _, _⟩ | ⟨h0, _, _, _⟩
            · exact hm1
            · omega
            · rw [hm.2.1] at hd; omega
            · omega
          have hw : wHVec (2 ^ v * x - 1) = 10 := by simp [wHVec, hm15]
          rw [hw]
          have hnn : (0 : ℝ) ≤ if 4 ≤ v ∧ v % 20 = v5Class (x % 25) % 20 then aHVal ^ v * 4 else 0 := by
            split_ifs <;> positivity
          linarith
        · simp only [hv4, ↓reduceIte]
          by_cases h25 : (2 ^ v * x) % 25 = 1
          · simp only [h25, ↓reduceIte]
            have hv20 : v % 20 = v5Class (x % 25) % 20 := (v5Class_spec x v (Or.inl h5)).mp h25
            have hv_ge4 : 4 ≤ v := by
              have hx25 : x % 25 = 1 ∨ x % 25 = 6 ∨ x % 25 = 11 ∨ x % 25 = 16 ∨ x % 25 = 21 := by omega
              rcases hx25 with h | h | h | h | h <;> (rw [h] at hv20; simp [v5Class] at hv20; omega)
            have hw : wHVec ((2 ^ v * x - 1) / 5) = 4 := by
              have hbp : backPred x v = some (5, (2 ^ v * x - 1) / 5) := by
                unfold backPred; simp [h15, hv4, h25]
              have hm := backPred_mem_InABC15 hx hv1 hbp
              have hcl := lem_basin1_moves_classify hx hv1 hm.1.2.1 (by rw [hm.2.1]; exact hm.2.2)
              rcases hcl.2.2.2 with ⟨_, hd, _, _⟩ | ⟨_, hd, _, _⟩ | ⟨_, _, _, hm0⟩ | ⟨h0, _, _, _⟩
              · rw [hm.2.1] at hd; omega
              · rw [hm.2.1] at hd; omega
              · simp [wHVec, hm0]
              · omega
            rw [hw]
            simp only [hv_ge4, hv20, and_self, ↓reduceIte, zero_add]
            exact le_rfl
          · simp only [h25, ↓reduceIte, zero_add]
            split_ifs <;> positivity
      have hg1 := finite_geom_step_le (step := 4) (r := 1) (lo := 1) (L := M) ha0 ha1 (by omega)
      have hg5 := finite_geom_step_le (step := 20) (r := v5Class (x % 25)) (lo := 4) (L := M)
        ha0 ha1 (by omega)
      have hw : wHVec x = 10 := by simp [wHVec, h15]
      rw [hw]
      have hnum : (aHVal ^ 1 / (1 - aHVal ^ 4)) * 10 + (aHVal ^ 4 / (1 - aHVal ^ 20)) * 4 ≤ 10 := by
        norm_num [aHVal]
      linarith [mul_le_mul_of_nonneg_right hg1 (by norm_num : (0 : ℝ) ≤ 10),
                mul_le_mul_of_nonneg_right hg5 (by norm_num : (0 : ℝ) ≤ 4)]
    · -- x ∈ B (x % 15 = 0): d=7 at v≡v0 (mod 3), v≥1 (to C, weight 4)
      have hw : wHVec x = 4 := by simp [wHVec, h15]
      rw [hw]
      obtain ⟨hc4, hc2, hc1, hcnone⟩ := two_pow_mod_7_eq_one_cases x
      by_cases hact : x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 4
      · let r3 : ℕ := if x % 7 = 4 then 1 else if x % 7 = 2 then 2 else 0
        have hiff : ∀ v, (2 ^ v * x) % 7 = 1 ↔ v % 3 = r3 % 3 := by
          intro v
          rcases hact with h | h | h
          · simp [r3, h]; exact hc1 h v
          · simp [r3, h]; exact hc2 h v
          · simp [r3, h]; exact hc4 h v
        have hle : ∑ v ∈ Finset.Icc 1 M,
              (match backPred x v with | some (_, m) => aHVal ^ v * wHVec m | none => 0) ≤
            (∑ v ∈ (Finset.Icc 1 M).filter (fun v => v % 3 = r3 % 3), aHVal ^ v) * 4 := by
          rw [Finset.sum_mul, Finset.sum_filter]
          refine Finset.sum_le_sum fun v hv => ?_
          have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1
          unfold backPred
          simp only [h15, show ¬(0 = 1) by omega, show ¬(0 = 2) by omega, ↓reduceIte]
          by_cases h7 : (2 ^ v * x) % 7 = 1
          · have hmod : v % 3 = r3 % 3 := (hiff v).mp h7
            simp only [h7, hmod, ↓reduceIte]
            have hbp : backPred x v = some (7, (2 ^ v * x - 1) / 7) := by
              unfold backPred; simp [h15, h7]
            have hm := backPred_mem_InABC15 hx hv1 hbp
            have hcl := lem_basin1_moves_classify hx hv1 hm.1.2.1 (by rw [hm.2.1]; exact hm.2.2)
            have hwm : wHVec ((2 ^ v * x - 1) / 7) = 4 := by
              rcases hcl.2.2.2 with ⟨h1, _, _, _⟩ | ⟨h2, _, _, _⟩ | ⟨h12, _, _, _⟩ | ⟨_, _, _, hm2⟩
              · omega
              · omega
              · omega
              · simp [wHVec, hm2]
            rw [hwm]
          · have hmod : v % 3 ≠ r3 % 3 := mt (hiff v).mpr h7
            simp [h7, hmod]
        have hg7 := finite_geom_step_le (step := 3) (r := r3) (lo := 1) (L := M) ha0 ha1 (by omega)
        have hnum : (aHVal ^ 1 / (1 - aHVal ^ 3)) * 4 ≤ 4 := by norm_num [aHVal]
        linarith [mul_le_mul_of_nonneg_right hg7 (by norm_num : (0 : ℝ) ≤ 4)]
      · push Not at hact
        have hzero : ∑ v ∈ Finset.Icc 1 M,
              (match backPred x v with | some (_, m) => aHVal ^ v * wHVec m | none => 0) = 0 := by
          refine Finset.sum_eq_zero fun v _ => ?_
          unfold backPred
          simp [h15, hcnone hact.1 hact.2.1 hact.2.2 v]
        linarith
    · -- x ∈ C (x % 15 = 2): d=1 at v%4=0, v≥4 (to A, weight 10), d=5 at v≡v5 (mod 20), v≥3 (to B, weight 4)
      have h5 : x % 5 = 2 := by omega
      have hsplit : ∑ v ∈ Finset.Icc 1 M,
            (match backPred x v with | some (_, m) => aHVal ^ v * wHVec m | none => 0) ≤
          (∑ v ∈ (Finset.Icc 4 M).filter (fun v => v % 4 = 0 % 4), aHVal ^ v) * 10 +
          (∑ v ∈ (Finset.Icc 3 M).filter (fun v => v % 20 = v5Class (x % 25) % 20), aHVal ^ v) * 4 := by
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_filter, Finset.sum_filter]
        have hsub1 : ∑ v ∈ Finset.Icc 4 M, (if v % 4 = 0 % 4 then aHVal ^ v * 10 else 0) =
            ∑ v ∈ Finset.Icc 1 M, (if 4 ≤ v ∧ v % 4 = 0 then aHVal ^ v * 10 else 0) := by
          rw [← Finset.sum_filter, ← Finset.sum_filter]
          congr 1; ext v; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
        have hsub3 : ∑ v ∈ Finset.Icc 3 M,
              (if v % 20 = v5Class (x % 25) % 20 then aHVal ^ v * 4 else 0) =
            ∑ v ∈ Finset.Icc 1 M,
              (if 3 ≤ v ∧ v % 20 = v5Class (x % 25) % 20 then aHVal ^ v * 4 else 0) := by
          rw [← Finset.sum_filter, ← Finset.sum_filter]
          congr 1; ext v; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
        rw [hsub1, hsub3, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun v hv => ?_
        have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1
        unfold backPred
        simp only [h15, show ¬(2 = 1) by omega, ↓reduceIte]
        by_cases hv4 : v % 4 = 0
        · have hv_ge4 : 4 ≤ v := by omega
          simp only [hv4, hv_ge4, and_self, ↓reduceIte]
          have hm15 : (2 ^ v * x - 1) % 15 = 1 := by
            have hbp : backPred x v = some (1, 2 ^ v * x - 1) := by unfold backPred; simp [h15, hv4]
            have hm := backPred_mem_InABC15 hx hv1 hbp
            have hcl := lem_basin1_moves_classify hx hv1 hm.1.2.1 (by rw [hm.2.1]; exact hm.2.2)
            rcases hcl.2.2.2 with ⟨h1, _, _, _⟩ | ⟨_, _, _, hm1⟩ | ⟨_, hd, _, _⟩ | ⟨h0, _, _, _⟩
            · omega
            · exact hm1
            · rw [hm.2.1] at hd; omega
            · omega
          have hw : wHVec (2 ^ v * x - 1) = 10 := by simp [wHVec, hm15]
          rw [hw]
          have hnn : (0 : ℝ) ≤ if 3 ≤ v ∧ v % 20 = v5Class (x % 25) % 20 then aHVal ^ v * 4 else 0 := by
            split_ifs <;> positivity
          linarith
        · simp only [hv4, and_false, ↓reduceIte, zero_add]
          by_cases h25 : (2 ^ v * x) % 25 = 1
          · simp only [h25, ↓reduceIte]
            have hv20 : v % 20 = v5Class (x % 25) % 20 := (v5Class_spec x v (Or.inr h5)).mp h25
            have hv_ge3 : 3 ≤ v := by
              have hx25 : x % 25 = 2 ∨ x % 25 = 7 ∨ x % 25 = 12 ∨ x % 25 = 17 ∨ x % 25 = 22 := by omega
              rcases hx25 with h | h | h | h | h <;> (rw [h] at hv20; simp [v5Class] at hv20; omega)
            have hw : wHVec ((2 ^ v * x - 1) / 5) = 4 := by
              have hbp : backPred x v = some (5, (2 ^ v * x - 1) / 5) := by
                unfold backPred; simp [h15, hv4, h25]
              have hm := backPred_mem_InABC15 hx hv1 hbp
              have hcl := lem_basin1_moves_classify hx hv1 hm.1.2.1 (by rw [hm.2.1]; exact hm.2.2)
              rcases hcl.2.2.2 with ⟨_, hd, _, _⟩ | ⟨_, hd, _, _⟩ | ⟨_, _, _, hm0⟩ | ⟨h0, _, _, _⟩
              · rw [hm.2.1] at hd; omega
              · rw [hm.2.1] at hd; omega
              · simp [wHVec, hm0]
              · omega
            rw [hw]
            simp only [hv_ge3, hv20, and_self, ↓reduceIte]
            exact le_rfl
          · simp only [h25, ↓reduceIte]
            split_ifs <;> positivity
      have hg1 := finite_geom_step_le (step := 4) (r := 0) (lo := 4) (L := M) ha0 ha1 (by omega)
      have hg5 := finite_geom_step_le (step := 20) (r := v5Class (x % 25)) (lo := 3) (L := M)
        ha0 ha1 (by omega)
      have hw : wHVec x = 4 := by simp [wHVec, h15]
      rw [hw]
      have hnum : (aHVal ^ 4 / (1 - aHVal ^ 4)) * 10 + (aHVal ^ 3 / (1 - aHVal ^ 20)) * 4 ≤ 4 := by
        norm_num [aHVal]
      linarith [mul_le_mul_of_nonneg_right hg1 (by norm_num : (0 : ℝ) ≤ 10),
                mul_le_mul_of_nonneg_right hg5 (by norm_num : (0 : ℝ) ≤ 4)]

/-! ## Section 6: Certified `Q1 = 643,125` pair bound (Case 3) -/

/-- Certified pair weight vector on `A ∪ B ∪ C` backed by `Ouroboros.BasinOneUpperCert`. -/
noncomputable def certPairW (o : ℕ) : ℝ :=
  if o % 15 = 1 then (getWA ((o % 643125) / 15) : ℝ)
  else if o % 15 = 0 then (getWB (((o % 643125) / 15) % 8575) : ℝ)
  else (getWC (((o % 643125) / 15) % 6125) : ℝ)

private lemma certPairW_ge_one (o : ℕ) (ho : InABC15 o) : 1 ≤ certPairW o := by
  have hq : (o % 643125) / 15 < 42875 := by have := Nat.mod_lt o (by omega : 0 < 643125); omega
  have hchk := checkQ_all ((o % 643125) / 15) hq
  simp only [checkQ, Bool.and_eq_true, Nat.ble_eq] at hchk
  unfold certPairW
  rcases ho.2.2 with h1 | h0 | h2
  · simp only [h1, ↓reduceIte]; exact_mod_cast hchk.1.1.1.1.1
  · simp only [h0, show ¬(0 = 1) by omega, ↓reduceIte]; exact_mod_cast hchk.1.1.1.1.2
  · simp only [h2, show ¬(2 = 1) by omega, show ¬(2 = 0) by omega, ↓reduceIte]
    exact_mod_cast hchk.1.1.1.2

private lemma certPairW_le_max (o : ℕ) : certPairW o ≤ 226730 := by
  unfold certPairW
  split_ifs
  · have := getWA_le ((o % 643125) / 15); exact_mod_cast (by omega : getWA _ ≤ 226730)
  · exact_mod_cast getWB_le (((o % 643125) / 15) % 8575)
  · have := getWC_le (((o % 643125) / 15) % 6125); exact_mod_cast (by omega : getWC _ ≤ 226730)

-- Pure-kernel check of all 36 rational upper-bound coefficients `getF1`, `getF5`, `getF7`.
def checkPairCoeffsAux : Nat → Bool
  | 0 => true
  | v + 1 =>
    let k := v + 1
    Nat.ble (1000000 * 7116 ^ k) (getF1 k * 10000 ^ k) &&
    Nat.ble (c5Val * getF1 k) (getF5 k * 1000000) &&
    Nat.ble (c7Val * getF1 k) (getF7 k * 1000000) &&
    checkPairCoeffsAux v

private theorem checkPairCoeffs_true : checkPairCoeffsAux 36 = true := rfl

private lemma checkPairCoeffs_sound :
    ∀ n v, checkPairCoeffsAux n = true → 1 ≤ v → v ≤ n →
      1000000 * 7116 ^ v ≤ getF1 v * 10000 ^ v ∧
      c5Val * getF1 v ≤ getF5 v * 1000000 ∧
      c7Val * getF1 v ≤ getF7 v * 1000000 := by
  intro n
  induction n with
  | zero => intro v _ h1 h2; omega
  | succ n ih =>
    intro v h h1 h2
    simp only [checkPairCoeffsAux, Bool.and_eq_true, Nat.ble_eq] at h
    by_cases hv : v = n + 1
    · subst hv; exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩
    · exact ih v h.2 h1 (by omega)

private lemma aP_pow_le_getF1 {v : ℕ} (hv1 : 1 ≤ v) (hv36 : v ≤ 36) :
    aPVal ^ v ≤ (getF1 v : ℝ) / 1000000 := by
  have h := (checkPairCoeffs_sound 36 v checkPairCoeffs_true hv1 hv36).1
  have hR : (1000000 : ℝ) * (7116 : ℝ) ^ v ≤ (getF1 v : ℝ) * (10000 : ℝ) ^ v := by exact_mod_cast h
  unfold aPVal
  rw [div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

private lemma five_aP_pow_le_getF5 {v : ℕ} (hv1 : 1 ≤ v) (hv36 : v ≤ 36) :
    (5 : ℝ) ^ sPVal * aPVal ^ v ≤ (getF5 v : ℝ) / 1000000 := by
  have ha0 : 0 ≤ aPVal := by norm_num [aPVal]
  have h5 := five_rpow_sP_le
  have hf1 := aP_pow_le_getF1 hv1 hv36
  have hnat := (checkPairCoeffs_sound 36 v checkPairCoeffs_true hv1 hv36).2.1
  have hR : (c5Val : ℝ) * (getF1 v : ℝ) ≤ (getF5 v : ℝ) * 1000000 := by exact_mod_cast hnat
  calc (5 : ℝ) ^ sPVal * aPVal ^ v
      ≤ ((c5Val : ℝ) / 1000000) * ((getF1 v : ℝ) / 1000000) :=
        mul_le_mul h5 hf1 (pow_nonneg ha0 v) (by positivity)
    _ ≤ (getF5 v : ℝ) / 1000000 := by
        rw [div_mul_div_comm, div_le_div_iff₀ (by norm_num) (by norm_num)]
        linarith

private lemma seven_aP_pow_le_getF7 {v : ℕ} (hv1 : 1 ≤ v) (hv36 : v ≤ 36) :
    (7 : ℝ) ^ sPVal * aPVal ^ v ≤ (getF7 v : ℝ) / 1000000 := by
  have ha0 : 0 ≤ aPVal := by norm_num [aPVal]
  have h7 := seven_rpow_sP_le
  have hf1 := aP_pow_le_getF1 hv1 hv36
  have hnat := (checkPairCoeffs_sound 36 v checkPairCoeffs_true hv1 hv36).2.2
  have hR : (c7Val : ℝ) * (getF1 v : ℝ) ≤ (getF7 v : ℝ) * 1000000 := by exact_mod_cast hnat
  calc (7 : ℝ) ^ sPVal * aPVal ^ v
      ≤ ((c7Val : ℝ) / 1000000) * ((getF1 v : ℝ) / 1000000) :=
        mul_le_mul h7 hf1 (pow_nonneg ha0 v) (by positivity)
    _ ≤ (getF7 v : ℝ) / 1000000 := by
        rw [div_mul_div_comm, div_le_div_iff₀ (by norm_num) (by norm_num)]
        linarith

private lemma tailA_bound :
    (aPVal ^ 37 / (1 - aPVal ^ 4)) * (123192 : ℝ) +
    (5 : ℝ) ^ sPVal * (aPVal ^ 37 / (1 - aPVal ^ 20)) * (226730 : ℝ) ≤
      (tailAVal : ℝ) / 1000000 := by
  have h5 := five_rpow_sP_le
  have hpos : (0 : ℝ) ≤ (aPVal ^ 37 / (1 - aPVal ^ 20)) * 226730 := by norm_num [aPVal]
  have hmul := mul_le_mul_of_nonneg_right h5 hpos
  have hnum : (aPVal ^ 37 / (1 - aPVal ^ 4)) * (123192 : ℝ) +
      ((c5Val : ℝ) / 1000000) * ((aPVal ^ 37 / (1 - aPVal ^ 20)) * 226730) ≤
      (tailAVal : ℝ) / 1000000 := by
    norm_num [aPVal, c5Val, tailAVal]
  linarith

private lemma tailB_bound :
    (7 : ℝ) ^ sPVal * (aPVal ^ 37 / (1 - aPVal ^ 3)) * (153363 : ℝ) ≤
      (tailBVal : ℝ) / 1000000 := by
  have h7 := seven_rpow_sP_le
  have hpos : (0 : ℝ) ≤ (aPVal ^ 37 / (1 - aPVal ^ 3)) * 153363 := by norm_num [aPVal]
  have hmul := mul_le_mul_of_nonneg_right h7 hpos
  have hnum : ((c7Val : ℝ) / 1000000) * ((aPVal ^ 37 / (1 - aPVal ^ 3)) * 153363) ≤
      (tailBVal : ℝ) / 1000000 := by
    norm_num [aPVal, c7Val, tailBVal]
  linarith

-- Helper: child index equations mod 643125 for d = 1, 5, 7
private lemma certPairW_child_d1 {o v : ℕ} (ho : InABC15 o) (hv : 1 ≤ v)
    (hbp : backPred o v = some (1, 2 ^ v * o - 1)) :
    certPairW (2 ^ v * o - 1) = (getWA (((2 ^ v * (o % 643125)) % 643125 - 1) / 15) : ℝ) := by
  have hm := backPred_mem_InABC15 ho hv hbp
  have hcl := lem_basin1_moves_classify ho hv hm.1.2.1 (by rw [hm.2.1]; exact hm.2.2)
  have hm15 : (2 ^ v * o - 1) % 15 = 1 := by
    rcases hcl.2.2.2 with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, hd, _, _⟩ | ⟨_, hd, _, _⟩
    · exact h
    · exact h
    · rw [hm.2.1] at hd; omega
    · rw [hm.2.1] at hd; omega
  have hxmod : (2 ^ v * o) % 643125 = (2 ^ v * (o % 643125)) % 643125 := by
    simp [Nat.mul_mod]
  have hx15 : ((2 ^ v * o) % 643125) % 15 = 2 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 15 ∣ 643125)]
    have h2vo : 2 ≤ 2 ^ v * o := by
      have : 2 ≤ 2 ^ v := calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv
      nlinarith [ho.1]
    omega
  have hx_ge1 : 1 ≤ (2 ^ v * o) % 643125 := by omega
  have hsub : (2 ^ v * o - 1) % 643125 = (2 ^ v * o) % 643125 - 1 := by
    have hdiv := Nat.div_add_mod (2 ^ v * o) 643125
    have hlt := Nat.mod_lt (2 ^ v * o) (by omega : 0 < 643125)
    have : 2 ^ v * o - 1 = 643125 * ((2 ^ v * o) / 643125) + ((2 ^ v * o) % 643125 - 1) := by omega
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  unfold certPairW
  simp only [hm15, ↓reduceIte, hsub, hxmod]

private lemma certPairW_child_d5 {o v : ℕ} (ho : InABC15 o) (hv : 1 ≤ v)
    (hbp : backPred o v = some (5, (2 ^ v * o - 1) / 5)) :
    certPairW ((2 ^ v * o - 1) / 5) = (getWB (((2 ^ v * (o % 643125)) % 643125 - 1) / 75) : ℝ) := by
  have hm := backPred_mem_InABC15 ho hv hbp
  have hcl := lem_basin1_moves_classify ho hv hm.1.2.1 (by rw [hm.2.1]; exact hm.2.2)
  have hm15 : ((2 ^ v * o - 1) / 5) % 15 = 0 := by
    rcases hcl.2.2.2 with ⟨_, hd, _, _⟩ | ⟨_, hd, _, _⟩ | ⟨_, _, _, h⟩ | ⟨_, hd, _, _⟩
    · rw [hm.2.1] at hd; omega
    · rw [hm.2.1] at hd; omega
    · exact h
    · rw [hm.2.1] at hd; omega
  have h5dvd : 5 ∣ (2 ^ v * o - 1) := ⟨(2 ^ v * o - 1) / 5, by omega⟩
  have hxmod : (2 ^ v * o) % 643125 = (2 ^ v * (o % 643125)) % 643125 := by simp [Nat.mul_mod]
  have hx_ge1 : 1 ≤ (2 ^ v * o) % 643125 := by
    have : ((2 ^ v * o) % 643125) % 5 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by decide : 5 ∣ 643125)]
      have h2vo : 2 ≤ 2 ^ v * o := by
        have : 2 ≤ 2 ^ v := calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv
        nlinarith [ho.1]
      omega
    omega
  have hsub : (2 ^ v * o - 1) % 643125 = (2 ^ v * o) % 643125 - 1 := by
    have hdiv := Nat.div_add_mod (2 ^ v * o) 643125
    have hlt := Nat.mod_lt (2 ^ v * o) (by omega : 0 < 643125)
    have : 2 ^ v * o - 1 = 643125 * ((2 ^ v * o) / 643125) + ((2 ^ v * o) % 643125 - 1) := by omega
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  set m := (2 ^ v * o - 1) / 5
  have hm_mod : m % 128625 = ((2 ^ v * o) % 643125 - 1) / 5 := by
    have hd := div_mod_div_eq (y := 2 ^ v * o - 1) (d := 5) (Q := 643125)
      (by omega) (by decide) h5dvd
    rw [hsub] at hd
    simpa [m] using hd
  have hidx : ((m % 643125) / 15) % 8575 = ((2 ^ v * o) % 643125 - 1) / 75 := by
    have h1 : ((m % 643125) / 15) % 8575 = (m % 128625) / 15 := by
      have h128 : (m % 643125) % 128625 = m % 128625 :=
        Nat.mod_mod_of_dvd m (by decide : 128625 ∣ 643125)
      omega
    rw [h1, hm_mod, Nat.div_div_eq_div_mul]
  unfold certPairW
  simp only [hm15, show ¬(0 = 1) by omega, ↓reduceIte, hidx, hxmod]

private lemma certPairW_child_d7 {o v : ℕ} (ho : InABC15 o) (hv : 1 ≤ v)
    (hbp : backPred o v = some (7, (2 ^ v * o - 1) / 7)) :
    certPairW ((2 ^ v * o - 1) / 7) = (getWC (((2 ^ v * (o % 643125)) % 643125 - 1) / 105) : ℝ) := by
  have hm := backPred_mem_InABC15 ho hv hbp
  have hcl := lem_basin1_moves_classify ho hv hm.1.2.1 (by rw [hm.2.1]; exact hm.2.2)
  have hm15 : ((2 ^ v * o - 1) / 7) % 15 = 2 := by
    rcases hcl.2.2.2 with ⟨_, hd, _, _⟩ | ⟨_, hd, _, _⟩ | ⟨_, hd, _, _⟩ | ⟨_, _, _, h⟩
    · rw [hm.2.1] at hd; omega
    · rw [hm.2.1] at hd; omega
    · rw [hm.2.1] at hd; omega
    · exact h
  have h7dvd : 7 ∣ (2 ^ v * o - 1) := ⟨(2 ^ v * o - 1) / 7, by omega⟩
  have hxmod : (2 ^ v * o) % 643125 = (2 ^ v * (o % 643125)) % 643125 := by simp [Nat.mul_mod]
  have hx_ge1 : 1 ≤ (2 ^ v * o) % 643125 := by
    have : ((2 ^ v * o) % 643125) % 7 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by decide : 7 ∣ 643125)]
      have h2vo : 2 ≤ 2 ^ v * o := by
        have : 2 ≤ 2 ^ v := calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv
        nlinarith [ho.1]
      omega
    omega
  have hsub : (2 ^ v * o - 1) % 643125 = (2 ^ v * o) % 643125 - 1 := by
    have hdiv := Nat.div_add_mod (2 ^ v * o) 643125
    have hlt := Nat.mod_lt (2 ^ v * o) (by omega : 0 < 643125)
    have : 2 ^ v * o - 1 = 643125 * ((2 ^ v * o) / 643125) + ((2 ^ v * o) % 643125 - 1) := by omega
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  set m := (2 ^ v * o - 1) / 7
  have hm_mod : m % 91875 = ((2 ^ v * o) % 643125 - 1) / 7 := by
    have hd := div_mod_div_eq (y := 2 ^ v * o - 1) (d := 7) (Q := 643125)
      (by omega) (by decide) h7dvd
    rw [hsub] at hd
    simpa [m] using hd
  have hidx : ((m % 643125) / 15) % 6125 = ((2 ^ v * o) % 643125 - 1) / 105 := by
    have h1 : ((m % 643125) / 15) % 6125 = (m % 91875) / 15 := by
      have h91 : (m % 643125) % 91875 = m % 91875 :=
        Nat.mod_mod_of_dvd m (by decide : 91875 ∣ 643125)
      omega
    rw [h1, hm_mod, Nat.div_div_eq_div_mul]
  unfold certPairW
  simp only [hm15, show ¬(2 = 1) by omega, show ¬(2 = 0) by omega, ↓reduceIte, hidx, hxmod]

private lemma mod_step (m k s k' r : ℕ) (hm : m % 643125 = 2 ^ s % 643125) (hk : k + s = k') :
    (m * ((2 ^ k * r) % 643125)) % 643125 = (2 ^ k' * r) % 643125 := by
  subst hk
  rw [Nat.mul_mod, hm, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, ← pow_add, add_comm s k]

private lemma pow2_20_step_mod {k r : ℕ} :
    (405451 * ((2 ^ k * r) % 643125)) % 643125 = (2 ^ (k + 20) * r) % 643125 :=
  mod_step 405451 k 20 (k + 20) r (by decide) rfl

private lemma sumD1A_eq (r : ℕ) :
    sumD1A r =
      getF1 1 * getWA (((2 ^ 1 * r) % 643125 - 1) / 15) +
      getF1 5 * getWA (((2 ^ 5 * r) % 643125 - 1) / 15) +
      getF1 9 * getWA (((2 ^ 9 * r) % 643125 - 1) / 15) +
      getF1 13 * getWA (((2 ^ 13 * r) % 643125 - 1) / 15) +
      getF1 17 * getWA (((2 ^ 17 * r) % 643125 - 1) / 15) +
      getF1 21 * getWA (((2 ^ 21 * r) % 643125 - 1) / 15) +
      getF1 25 * getWA (((2 ^ 25 * r) % 643125 - 1) / 15) +
      getF1 29 * getWA (((2 ^ 29 * r) % 643125 - 1) / 15) +
      getF1 33 * getWA (((2 ^ 33 * r) % 643125 - 1) / 15) := by
  unfold sumD1A; dsimp only
  rw [show 2 * r = 2 ^ 1 * r by simp,
      mod_step 16 1 4 5 r rfl rfl, mod_step 16 5 4 9 r rfl rfl,
      mod_step 16 9 4 13 r rfl rfl, mod_step 16 13 4 17 r rfl rfl,
      mod_step 16 17 4 21 r rfl rfl, mod_step 16 21 4 25 r rfl rfl,
      mod_step 16 25 4 29 r rfl rfl, mod_step 16 29 4 33 r rfl rfl]
  rfl

private lemma sumD1C_eq (r : ℕ) :
    sumD1C r =
      getF1 4 * getWA (((2 ^ 4 * r) % 643125 - 1) / 15) +
      getF1 8 * getWA (((2 ^ 8 * r) % 643125 - 1) / 15) +
      getF1 12 * getWA (((2 ^ 12 * r) % 643125 - 1) / 15) +
      getF1 16 * getWA (((2 ^ 16 * r) % 643125 - 1) / 15) +
      getF1 20 * getWA (((2 ^ 20 * r) % 643125 - 1) / 15) +
      getF1 24 * getWA (((2 ^ 24 * r) % 643125 - 1) / 15) +
      getF1 28 * getWA (((2 ^ 28 * r) % 643125 - 1) / 15) +
      getF1 32 * getWA (((2 ^ 32 * r) % 643125 - 1) / 15) +
      getF1 36 * getWA (((2 ^ 36 * r) % 643125 - 1) / 15) := by
  unfold sumD1C; dsimp only
  rw [show 16 * r = 2 ^ 4 * r by rfl,
      mod_step 16 4 4 8 r rfl rfl, mod_step 16 8 4 12 r rfl rfl,
      mod_step 16 12 4 16 r rfl rfl, mod_step 16 16 4 20 r rfl rfl,
      mod_step 16 20 4 24 r rfl rfl, mod_step 16 24 4 28 r rfl rfl,
      mod_step 16 28 4 32 r rfl rfl, mod_step 16 32 4 36 r rfl rfl]
  rfl

private lemma sumD7B_eq_4 (r : ℕ) (hr : r % 7 = 4) :
    sumD7B r =
      getF7 1 * getWC (((2 ^ 1 * r) % 643125 - 1) / 105) +
      getF7 4 * getWC (((2 ^ 4 * r) % 643125 - 1) / 105) +
      getF7 7 * getWC (((2 ^ 7 * r) % 643125 - 1) / 105) +
      getF7 10 * getWC (((2 ^ 10 * r) % 643125 - 1) / 105) +
      getF7 13 * getWC (((2 ^ 13 * r) % 643125 - 1) / 105) +
      getF7 16 * getWC (((2 ^ 16 * r) % 643125 - 1) / 105) +
      getF7 19 * getWC (((2 ^ 19 * r) % 643125 - 1) / 105) +
      getF7 22 * getWC (((2 ^ 22 * r) % 643125 - 1) / 105) +
      getF7 25 * getWC (((2 ^ 25 * r) % 643125 - 1) / 105) +
      getF7 28 * getWC (((2 ^ 28 * r) % 643125 - 1) / 105) +
      getF7 31 * getWC (((2 ^ 31 * r) % 643125 - 1) / 105) +
      getF7 34 * getWC (((2 ^ 34 * r) % 643125 - 1) / 105) := by
  unfold sumD7B; simp only [hr, show Nat.beq 4 4 = true by decide]
  rw [show 2 * r = 2 ^ 1 * r by simp,
      mod_step 8 1 3 4 r rfl rfl, mod_step 8 4 3 7 r rfl rfl,
      mod_step 8 7 3 10 r rfl rfl, mod_step 8 10 3 13 r rfl rfl,
      mod_step 8 13 3 16 r rfl rfl, mod_step 8 16 3 19 r rfl rfl,
      mod_step 8 19 3 22 r rfl rfl, mod_step 8 22 3 25 r rfl rfl,
      mod_step 8 25 3 28 r rfl rfl, mod_step 8 28 3 31 r rfl rfl,
      mod_step 8 31 3 34 r rfl rfl]
  rfl

private lemma sumD7B_eq_2 (r : ℕ) (hr : r % 7 = 2) :
    sumD7B r =
      getF7 2 * getWC (((2 ^ 2 * r) % 643125 - 1) / 105) +
      getF7 5 * getWC (((2 ^ 5 * r) % 643125 - 1) / 105) +
      getF7 8 * getWC (((2 ^ 8 * r) % 643125 - 1) / 105) +
      getF7 11 * getWC (((2 ^ 11 * r) % 643125 - 1) / 105) +
      getF7 14 * getWC (((2 ^ 14 * r) % 643125 - 1) / 105) +
      getF7 17 * getWC (((2 ^ 17 * r) % 643125 - 1) / 105) +
      getF7 20 * getWC (((2 ^ 20 * r) % 643125 - 1) / 105) +
      getF7 23 * getWC (((2 ^ 23 * r) % 643125 - 1) / 105) +
      getF7 26 * getWC (((2 ^ 26 * r) % 643125 - 1) / 105) +
      getF7 29 * getWC (((2 ^ 29 * r) % 643125 - 1) / 105) +
      getF7 32 * getWC (((2 ^ 32 * r) % 643125 - 1) / 105) +
      getF7 35 * getWC (((2 ^ 35 * r) % 643125 - 1) / 105) := by
  unfold sumD7B; simp only [hr, show Nat.beq 2 4 = false by decide, show Nat.beq 2 2 = true by decide]
  rw [show 4 * r = 2 ^ 2 * r by rfl,
      mod_step 8 2 3 5 r rfl rfl, mod_step 8 5 3 8 r rfl rfl,
      mod_step 8 8 3 11 r rfl rfl, mod_step 8 11 3 14 r rfl rfl,
      mod_step 8 14 3 17 r rfl rfl, mod_step 8 17 3 20 r rfl rfl,
      mod_step 8 20 3 23 r rfl rfl, mod_step 8 23 3 26 r rfl rfl,
      mod_step 8 26 3 29 r rfl rfl, mod_step 8 29 3 32 r rfl rfl,
      mod_step 8 32 3 35 r rfl rfl]
  rfl

private lemma sumD7B_eq_1 (r : ℕ) (hr : r % 7 = 1) :
    sumD7B r =
      getF7 3 * getWC (((2 ^ 3 * r) % 643125 - 1) / 105) +
      getF7 6 * getWC (((2 ^ 6 * r) % 643125 - 1) / 105) +
      getF7 9 * getWC (((2 ^ 9 * r) % 643125 - 1) / 105) +
      getF7 12 * getWC (((2 ^ 12 * r) % 643125 - 1) / 105) +
      getF7 15 * getWC (((2 ^ 15 * r) % 643125 - 1) / 105) +
      getF7 18 * getWC (((2 ^ 18 * r) % 643125 - 1) / 105) +
      getF7 21 * getWC (((2 ^ 21 * r) % 643125 - 1) / 105) +
      getF7 24 * getWC (((2 ^ 24 * r) % 643125 - 1) / 105) +
      getF7 27 * getWC (((2 ^ 27 * r) % 643125 - 1) / 105) +
      getF7 30 * getWC (((2 ^ 30 * r) % 643125 - 1) / 105) +
      getF7 33 * getWC (((2 ^ 33 * r) % 643125 - 1) / 105) +
      getF7 36 * getWC (((2 ^ 36 * r) % 643125 - 1) / 105) := by
  unfold sumD7B
  simp only [hr, show Nat.beq 1 4 = false by decide, show Nat.beq 1 2 = false by decide,
    show Nat.beq 1 1 = true by decide]
  rw [show 8 * r = 2 ^ 3 * r by rfl,
      mod_step 8 3 3 6 r rfl rfl, mod_step 8 6 3 9 r rfl rfl,
      mod_step 8 9 3 12 r rfl rfl, mod_step 8 12 3 15 r rfl rfl,
      mod_step 8 15 3 18 r rfl rfl, mod_step 8 18 3 21 r rfl rfl,
      mod_step 8 21 3 24 r rfl rfl, mod_step 8 24 3 27 r rfl rfl,
      mod_step 8 27 3 30 r rfl rfl, mod_step 8 30 3 33 r rfl rfl,
      mod_step 8 33 3 36 r rfl rfl]
  rfl

private lemma sumD5A_eq_1 (r : ℕ) (h : r % 25 = 1) :
    sumD5A r = getF5 20 * getWB (((2 ^ 20 * r) % 643125 - 1) / 75) := by
  unfold sumD5A; rw [h, show 1 / 5 = 0 by decide]; dsimp only [getF5]
  have h20 : (405451 * r) % 643125 = (2 ^ 20 * r) % 643125 := by
    rw [show (405451 : ℕ) = 2 ^ 20 % 643125 by decide, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  rw [h20]; rfl

private lemma sumD5A_eq_6 (r : ℕ) (h : r % 25 = 6) :
    sumD5A r = getF5 12 * getWB (((2 ^ 12 * r) % 643125 - 1) / 75) +
      getF5 32 * getWB (((2 ^ 32 * r) % 643125 - 1) / 75) := by
  unfold sumD5A; rw [h, show 6 / 5 = 1 by decide]; dsimp only [getF5]
  rw [show 4096 * r = 2 ^ 12 * r from rfl, mod_step 405451 12 20 32 r (by decide) rfl]; rfl

private lemma sumD5A_eq_11 (r : ℕ) (h : r % 25 = 11) :
    sumD5A r = getF5 4 * getWB (((2 ^ 4 * r) % 643125 - 1) / 75) +
      getF5 24 * getWB (((2 ^ 24 * r) % 643125 - 1) / 75) := by
  unfold sumD5A; rw [h, show 11 / 5 = 2 by decide]; dsimp only [getF5]
  rw [show 16 * r = 2 ^ 4 * r from rfl, mod_step 405451 4 20 24 r (by decide) rfl]; rfl

private lemma sumD5A_eq_16 (r : ℕ) (h : r % 25 = 16) :
    sumD5A r = getF5 16 * getWB (((2 ^ 16 * r) % 643125 - 1) / 75) +
      getF5 36 * getWB (((2 ^ 36 * r) % 643125 - 1) / 75) := by
  unfold sumD5A; rw [h, show 16 / 5 = 3 by decide]; dsimp only [getF5]
  rw [show 65536 * r = 2 ^ 16 * r from rfl, mod_step 405451 16 20 36 r (by decide) rfl]; rfl

private lemma sumD5A_eq_21 (r : ℕ) (h : r % 25 = 21) :
    sumD5A r = getF5 8 * getWB (((2 ^ 8 * r) % 643125 - 1) / 75) +
      getF5 28 * getWB (((2 ^ 28 * r) % 643125 - 1) / 75) := by
  unfold sumD5A; rw [h, show 21 / 5 = 4 by decide]; dsimp only [getF5]
  rw [show 256 * r = 2 ^ 8 * r from rfl, mod_step 405451 8 20 28 r (by decide) rfl]; rfl

private lemma sumD5C_eq_2 (r : ℕ) (h : r % 25 = 2) :
    sumD5C r = getF5 19 * getWB (((2 ^ 19 * r) % 643125 - 1) / 75) := by
  unfold sumD5C; rw [h, show 2 / 5 = 0 by decide]; dsimp only [getF5]
  rw [show 524288 * r = 2 ^ 19 * r from rfl]; rfl

private lemma sumD5C_eq_7 (r : ℕ) (h : r % 25 = 7) :
    sumD5C r = getF5 15 * getWB (((2 ^ 15 * r) % 643125 - 1) / 75) +
      getF5 35 * getWB (((2 ^ 35 * r) % 643125 - 1) / 75) := by
  unfold sumD5C; rw [h, show 7 / 5 = 1 by decide]; dsimp only [getF5]
  rw [show 32768 * r = 2 ^ 15 * r from rfl, mod_step 405451 15 20 35 r (by decide) rfl]; rfl

private lemma sumD5C_eq_12 (r : ℕ) (h : r % 25 = 12) :
    sumD5C r = getF5 11 * getWB (((2 ^ 11 * r) % 643125 - 1) / 75) +
      getF5 31 * getWB (((2 ^ 31 * r) % 643125 - 1) / 75) := by
  unfold sumD5C; rw [h, show 12 / 5 = 2 by decide]; dsimp only [getF5]
  rw [show 2048 * r = 2 ^ 11 * r from rfl, mod_step 405451 11 20 31 r (by decide) rfl]; rfl

private lemma sumD5C_eq_17 (r : ℕ) (h : r % 25 = 17) :
    sumD5C r = getF5 7 * getWB (((2 ^ 7 * r) % 643125 - 1) / 75) +
      getF5 27 * getWB (((2 ^ 27 * r) % 643125 - 1) / 75) := by
  unfold sumD5C; rw [h, show 17 / 5 = 3 by decide]; dsimp only [getF5]
  rw [show 128 * r = 2 ^ 7 * r from rfl, mod_step 405451 7 20 27 r (by decide) rfl]; rfl

private lemma sumD5C_eq_22 (r : ℕ) (h : r % 25 = 22) :
    sumD5C r = getF5 3 * getWB (((2 ^ 3 * r) % 643125 - 1) / 75) +
      getF5 23 * getWB (((2 ^ 23 * r) % 643125 - 1) / 75) := by
  unfold sumD5C; rw [h, show 22 / 5 = 4 by decide]; dsimp only [getF5]
  rw [show 8 * r = 2 ^ 3 * r from rfl, mod_step 405451 3 20 23 r (by decide) rfl]; rfl

private lemma certPairW_row_A (o M : ℕ) (ho : InABC15 o) (h15 : o % 15 = 1) :
    (∑ v ∈ Finset.Icc 1 36,
      (match backPred o v with
       | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
       | none => 0)) +
    (∑ v ∈ Finset.Icc 37 M,
      (match backPred o v with
       | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
       | none => 0)) ≤ certPairW o := by
  have ha0 : 0 < aPVal := by norm_num [aPVal]
  have ha1 : aPVal < 1 := by norm_num [aPVal]
  set r := o % 643125
  set q := r / 15
  have hq_lt : q < 42875 := by have := Nat.mod_lt o (by omega : 0 < 643125); omega
  have hr15 : r % 15 = o % 15 := Nat.mod_mod_of_dvd o (by decide : 15 ∣ 643125)
  have hr25 : r % 25 = o % 25 := Nat.mod_mod_of_dvd o (by decide : 25 ∣ 643125)
  have hr_eq : r = 15 * q + 1 := by omega
  have hchk := checkQ_all q hq_lt
  simp only [checkQ, Bool.and_eq_true, Nat.ble_eq] at hchk
  have hcertA : tailAVal + sumD1A r + sumD5A r ≤ 1000000 * getWA q := by
    have := hchk.1.1.2; rwa [← hr_eq] at this
  have hhead : ∑ v ∈ Finset.Icc 1 36,
        (match backPred o v with
         | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
         | none => 0) ≤
      ((sumD1A r : ℝ) + (sumD5A r : ℝ)) / 1000000 := by
    have hd1_set : (Finset.Icc 1 36).filter (fun v => v % 4 = 1) =
        {1, 5, 9, 13, 17, 21, 25, 29, 33} := by decide
    have hterm : ∀ v ∈ Finset.Icc 1 36,
        (match backPred o v with
         | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
         | none => 0) ≤
        (if v % 4 = 1 then
          ((getF1 v : ℝ) * (getWA (((2 ^ v * r) % 643125 - 1) / 15) : ℝ)) / 1000000 else 0) +
        (if (2 ^ v * r) % 25 = 1 then
          ((getF5 v : ℝ) * (getWB (((2 ^ v * r) % 643125 - 1) / 75) : ℝ)) / 1000000 else 0) := by
      intro v hv
      simp only [Finset.mem_Icc] at hv
      unfold backPred
      simp only [h15, ↓reduceIte]
      have hmod25 : (2 ^ v * o) % 25 = (2 ^ v * r) % 25 := by
        rw [Nat.mul_mod, ← hr25, ← Nat.mul_mod]
      by_cases hv4 : v % 4 = 1
      · simp only [hv4, ↓reduceIte, Nat.cast_one, Real.one_rpow, one_mul]
        have hbp : backPred o v = some (1, 2 ^ v * o - 1) := by unfold backPred; simp [h15, hv4]
        rw [certPairW_child_d1 ho hv.1 hbp]
        have hf1 := aP_pow_le_getF1 hv.1 hv.2
        have h1 := mul_le_mul_of_nonneg_right hf1
          (Nat.cast_nonneg (α := ℝ) (getWA (((2 ^ v * r) % 643125 - 1) / 15)))
        have hnn : (0 : ℝ) ≤ if (2 ^ v * r) % 25 = 1 then
            ((getF5 v : ℝ) * (getWB (((2 ^ v * r) % 643125 - 1) / 75) : ℝ)) / 1000000 else 0 := by
          split_ifs <;> positivity
        linarith [show (getF1 v : ℝ) / 1000000 * (getWA (((2 ^ v * r) % 643125 - 1) / 15) : ℝ) =
          ((getF1 v : ℝ) * (getWA (((2 ^ v * r) % 643125 - 1) / 15) : ℝ)) / 1000000 by ring]
      · simp only [hv4, ↓reduceIte, zero_add, hmod25]
        by_cases h25 : (2 ^ v * r) % 25 = 1
        · simp only [h25, ↓reduceIte]
          have hbp : backPred o v = some (5, (2 ^ v * o - 1) / 5) := by
            unfold backPred; simp [h15, hv4, hmod25, h25]
          rw [certPairW_child_d5 ho hv.1 hbp]
          have hf5 := five_aP_pow_le_getF5 hv.1 hv.2
          have h1 := mul_le_mul_of_nonneg_right hf5
            (Nat.cast_nonneg (α := ℝ) (getWB (((2 ^ v * r) % 643125 - 1) / 75)))
          push_cast at h1 ⊢
          linarith [show (getF5 v : ℝ) / 1000000 * (getWB (((2 ^ v * r) % 643125 - 1) / 75) : ℝ) =
            ((getF5 v : ℝ) * (getWB (((2 ^ v * r) % 643125 - 1) / 75) : ℝ)) / 1000000 by ring]
        · simp [h25]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, hd1_set]
    have hd1_eq : ∑ v ∈ ({1, 5, 9, 13, 17, 21, 25, 29, 33} : Finset ℕ),
          ((getF1 v : ℝ) * (getWA (((2 ^ v * r) % 643125 - 1) / 15) : ℝ)) / 1000000 =
        (sumD1A r : ℝ) / 1000000 := by
      rw [sumD1A_eq,
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
      push_cast; ring
    have hd5_eq : ∑ v ∈ (Finset.Icc 1 36).filter (fun v => (2 ^ v * r) % 25 = 1),
          ((getF5 v : ℝ) * (getWB (((2 ^ v * r) % 643125 - 1) / 75) : ℝ)) / 1000000 =
        (sumD5A r : ℝ) / 1000000 := by
      have hflt : ∀ v, (2 ^ v * r) % 25 = 1 ↔ (2 ^ v * (r % 25)) % 25 = 1 := fun v => by
        rw [Nat.mul_mod, Nat.mul_mod (2 ^ v) (r % 25), Nat.mod_mod]
      simp_rw [hflt]
      have hr25_cases : r % 25 = 1 ∨ r % 25 = 6 ∨ r % 25 = 11 ∨ r % 25 = 16 ∨ r % 25 = 21 := by omega
      rcases hr25_cases with h | h | h | h | h
      · have hs : (Finset.Icc 1 36).filter (fun v => (2 ^ v * 1) % 25 = 1) = {20} := by decide
        rw [h, hs, sumD5A_eq_1 r h, Finset.sum_singleton]; push_cast; ring
      · have hs : (Finset.Icc 1 36).filter (fun v => (2 ^ v * 6) % 25 = 1) = {12, 32} := by decide
        rw [h, hs, sumD5A_eq_6 r h, Finset.sum_pair (by decide)]; push_cast; ring
      · have hs : (Finset.Icc 1 36).filter (fun v => (2 ^ v * 11) % 25 = 1) = {4, 24} := by decide
        rw [h, hs, sumD5A_eq_11 r h, Finset.sum_pair (by decide)]; push_cast; ring
      · have hs : (Finset.Icc 1 36).filter (fun v => (2 ^ v * 16) % 25 = 1) = {16, 36} := by decide
        rw [h, hs, sumD5A_eq_16 r h, Finset.sum_pair (by decide)]; push_cast; ring
      · have hs : (Finset.Icc 1 36).filter (fun v => (2 ^ v * 21) % 25 = 1) = {8, 28} := by decide
        rw [h, hs, sumD5A_eq_21 r h, Finset.sum_pair (by decide)]; push_cast; ring
    rw [hd1_eq, hd5_eq, add_div]
  have htail : ∑ v ∈ Finset.Icc 37 M,
        (match backPred o v with
         | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
         | none => 0) ≤ (tailAVal : ℝ) / 1000000 := by
    have h5 : o % 5 = 1 := by omega
    have hle : ∑ v ∈ Finset.Icc 37 M,
          (match backPred o v with
           | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
           | none => 0) ≤
        (∑ v ∈ (Finset.Icc 37 M).filter (fun v => v % 4 = 1 % 4), aPVal ^ v) * (123192 : ℝ) +
        (5 : ℝ) ^ sPVal *
          (∑ v ∈ (Finset.Icc 37 M).filter (fun v => v % 20 = v5Class (o % 25) % 20), aPVal ^ v) *
            (226730 : ℝ) := by
      rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_filter, Finset.sum_filter,
          ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun v hv => ?_
      have hv1 : 1 ≤ v := by simp only [Finset.mem_Icc] at hv; omega
      unfold backPred
      simp only [h15, ↓reduceIte]
      by_cases hv4 : v % 4 = 1
      · simp only [hv4, ↓reduceIte, Nat.cast_one, Real.one_rpow, one_mul]
        have hbp : backPred o v = some (1, 2 ^ v * o - 1) := by unfold backPred; simp [h15, hv4]
        rw [certPairW_child_d1 ho hv1 hbp]
        have hw := getWA_le (((2 ^ v * r) % 643125 - 1) / 15)
        have hnn : (0 : ℝ) ≤ if v % 20 = v5Class (o % 25) % 20 then
            (5 : ℝ) ^ sPVal * aPVal ^ v * 226730 else 0 := by split_ifs <;> positivity
        have h1 : aPVal ^ v * (getWA (((2 ^ v * r) % 643125 - 1) / 15) : ℝ) ≤ aPVal ^ v * 123192 :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hw) (by positivity)
        linarith
      · simp only [hv4, ↓reduceIte, zero_add]
        by_cases h25 : (2 ^ v * o) % 25 = 1
        · have hv20 : v % 20 = v5Class (o % 25) % 20 := (v5Class_spec o v (Or.inl h5)).mp h25
          simp only [h25, hv20, ↓reduceIte]
          have hbp : backPred o v = some (5, (2 ^ v * o - 1) / 5) := by
            unfold backPred; simp [h15, hv4, h25]
          rw [certPairW_child_d5 ho hv1 hbp]
          have hw := getWB_le (((2 ^ v * r) % 643125 - 1) / 75)
          push_cast
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hw) (by positivity)
        · simp only [h25, ↓reduceIte]; split_ifs <;> positivity
    have hg1 := finite_geom_step_le (step := 4) (r := 1) (lo := 37) (L := M) ha0 ha1 (by omega)
    have hg5 := finite_geom_step_le (step := 20) (r := v5Class (o % 25)) (lo := 37) (L := M)
      ha0 ha1 (by omega)
    have h1 := mul_le_mul_of_nonneg_right hg1 (by norm_num : (0 : ℝ) ≤ 123192)
    have h2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hg5 (by positivity : (0 : ℝ) ≤ (5 : ℝ) ^ sPVal))
      (by norm_num : (0 : ℝ) ≤ 226730)
    linarith [tailA_bound]
  have hcertR : ((tailAVal : ℝ) + (sumD1A r : ℝ) + (sumD5A r : ℝ)) / 1000000 ≤ (getWA q : ℝ) := by
    have hR : (tailAVal : ℝ) + (sumD1A r : ℝ) + (sumD5A r : ℝ) ≤ 1000000 * (getWA q : ℝ) := by
      exact_mod_cast hcertA
    linarith
  have hw_eq : certPairW o = (getWA q : ℝ) := by unfold certPairW; simp [h15, q, r]
  rw [hw_eq]; linarith

private lemma certPairW_row_B (o M : ℕ) (ho : InABC15 o) (h15 : o % 15 = 0) :
    (∑ v ∈ Finset.Icc 1 36,
      (match backPred o v with
       | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
       | none => 0)) +
    (∑ v ∈ Finset.Icc 37 M,
      (match backPred o v with
       | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
       | none => 0)) ≤ certPairW o := by
  have ha0 : 0 < aPVal := by norm_num [aPVal]
  have ha1 : aPVal < 1 := by norm_num [aPVal]
  set r := o % 643125
  set q := r / 15
  have hq_lt : q < 42875 := by have := Nat.mod_lt o (by omega : 0 < 643125); omega
  have hr15 : r % 15 = o % 15 := Nat.mod_mod_of_dvd o (by decide : 15 ∣ 643125)
  have hr7 : r % 7 = o % 7 := Nat.mod_mod_of_dvd o (by decide : 7 ∣ 643125)
  have hr_eq : r = 15 * q := by omega
  have hchk := checkQ_all q hq_lt
  simp only [checkQ, Bool.and_eq_true, Nat.ble_eq] at hchk
  have hw_eq : certPairW o = (getWB (q % 8575) : ℝ) := by
    unfold certPairW; simp [h15, q, r]
  rw [hw_eq]
  obtain ⟨hc4, hc2, hc1, hcnone⟩ := two_pow_mod_7_eq_one_cases o
  by_cases hact : r % 7 = 1 ∨ r % 7 = 2 ∨ r % 7 = 4
  · have hcondB : (Nat.beq (15 * q % 7) 1 || Nat.beq (15 * q % 7) 2 || Nat.beq (15 * q % 7) 4) = true := by
      rw [← hr_eq]
      rcases hact with h | h | h <;> simp [h]
    have hcertB : tailBVal + sumD7B r ≤ 1000000 * getWB (q % 8575) := by
      have hB := hchk.2
      rw [hcondB] at hB
      dsimp only at hB
      have hB' := Nat.ble_eq.mp hB
      rwa [← hr_eq] at hB'
    have hhead : ∑ v ∈ Finset.Icc 1 36,
          (match backPred o v with
           | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
           | none => 0) ≤ (sumD7B r : ℝ) / 1000000 := by
      have hterm : ∀ v ∈ Finset.Icc 1 36,
          (match backPred o v with
           | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
           | none => 0) ≤
          if (2 ^ v * r) % 7 = 1 then
            ((getF7 v : ℝ) * (getWC (((2 ^ v * r) % 643125 - 1) / 105) : ℝ)) / 1000000 else 0 := by
        intro v hv
        simp only [Finset.mem_Icc] at hv
        unfold backPred
        simp only [h15, show ¬(0 = 1) by omega, show ¬(0 = 2) by omega, ↓reduceIte]
        have hmod7 : (2 ^ v * o) % 7 = (2 ^ v * r) % 7 := by
          rw [Nat.mul_mod, ← hr7, ← Nat.mul_mod]
        rw [hmod7]
        by_cases h7 : (2 ^ v * r) % 7 = 1
        · simp only [h7, ↓reduceIte]
          have hbp : backPred o v = some (7, (2 ^ v * o - 1) / 7) := by
            unfold backPred; simp [h15, hmod7, h7]
          rw [certPairW_child_d7 ho hv.1 hbp]
          have hf7 := seven_aP_pow_le_getF7 hv.1 hv.2
          have h1 := mul_le_mul_of_nonneg_right hf7
            (Nat.cast_nonneg (α := ℝ) (getWC (((2 ^ v * r) % 643125 - 1) / 105)))
          push_cast at h1 ⊢
          linarith [show (getF7 v : ℝ) / 1000000 * (getWC (((2 ^ v * r) % 643125 - 1) / 105) : ℝ) =
            ((getF7 v : ℝ) * (getWC (((2 ^ v * r) % 643125 - 1) / 105) : ℝ)) / 1000000 by ring]
        · simp [h7]
      refine (Finset.sum_le_sum hterm).trans_eq ?_
      rw [← Finset.sum_filter]
      have hflt : ∀ v, (2 ^ v * r) % 7 = 1 ↔ (2 ^ v * (r % 7)) % 7 = 1 := fun v => by
        rw [Nat.mul_mod, Nat.mul_mod (2 ^ v) (r % 7), Nat.mod_mod]
      simp_rw [hflt]
      rcases hact with h | h | h
      · have hs : (Finset.Icc 1 36).filter (fun v => (2 ^ v * 1) % 7 = 1) =
            {3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36} := by decide
        rw [h, hs, sumD7B_eq_1 r h,
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_pair (by decide)]
        push_cast; ring
      · have hs : (Finset.Icc 1 36).filter (fun v => (2 ^ v * 2) % 7 = 1) =
            {2, 5, 8, 11, 14, 17, 20, 23, 26, 29, 32, 35} := by decide
        rw [h, hs, sumD7B_eq_2 r h,
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_pair (by decide)]
        push_cast; ring
      · have hs : (Finset.Icc 1 36).filter (fun v => (2 ^ v * 4) % 7 = 1) =
            {1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34} := by decide
        rw [h, hs, sumD7B_eq_4 r h,
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_pair (by decide)]
        push_cast; ring
    have htail : ∑ v ∈ Finset.Icc 37 M,
          (match backPred o v with
           | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
           | none => 0) ≤ (tailBVal : ℝ) / 1000000 := by
      let r3 : ℕ := if o % 7 = 4 then 1 else if o % 7 = 2 then 2 else 0
      have hoact : o % 7 = 1 ∨ o % 7 = 2 ∨ o % 7 = 4 := by rwa [← hr7]
      have hiff : ∀ v, (2 ^ v * o) % 7 = 1 ↔ v % 3 = r3 % 3 := by
        intro v
        rcases hoact with h | h | h
        · simp [r3, h]; exact hc1 h v
        · simp [r3, h]; exact hc2 h v
        · simp [r3, h]; exact hc4 h v
      have hle : ∑ v ∈ Finset.Icc 37 M,
            (match backPred o v with
             | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
             | none => 0) ≤
          (7 : ℝ) ^ sPVal *
            (∑ v ∈ (Finset.Icc 37 M).filter (fun v => v % 3 = r3 % 3), aPVal ^ v) *
              (153363 : ℝ) := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_filter]
        refine Finset.sum_le_sum fun v hv => ?_
        have hv1 : 1 ≤ v := by simp only [Finset.mem_Icc] at hv; omega
        unfold backPred
        simp only [h15, show ¬(0 = 1) by omega, show ¬(0 = 2) by omega, ↓reduceIte]
        by_cases h7 : (2 ^ v * o) % 7 = 1
        · have hmod : v % 3 = r3 % 3 := (hiff v).mp h7
          simp only [h7, hmod, ↓reduceIte]
          have hbp : backPred o v = some (7, (2 ^ v * o - 1) / 7) := by
            unfold backPred; simp [h15, h7]
          rw [certPairW_child_d7 ho hv1 hbp]
          have hw := getWC_le (((2 ^ v * r) % 643125 - 1) / 105)
          push_cast
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hw) (by positivity)
        · have hmod : v % 3 ≠ r3 % 3 := mt (hiff v).mpr h7
          simp [h7, hmod]
      have hg7 := finite_geom_step_le (step := 3) (r := r3) (lo := 37) (L := M) ha0 ha1 (by omega)
      have h2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hg7 (by positivity : (0 : ℝ) ≤ (7 : ℝ) ^ sPVal))
        (by norm_num : (0 : ℝ) ≤ 153363)
      linarith [tailB_bound]
    have hcertR : ((tailBVal : ℝ) + (sumD7B r : ℝ)) / 1000000 ≤ (getWB (q % 8575) : ℝ) := by
      have hR : (tailBVal : ℝ) + (sumD7B r : ℝ) ≤ 1000000 * (getWB (q % 8575) : ℝ) := by
        exact_mod_cast hcertB
      linarith
    linarith
  · push Not at hact
    have hzero1 : ∑ v ∈ Finset.Icc 1 36,
          (match backPred o v with
           | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
           | none => 0) = 0 := by
      refine Finset.sum_eq_zero fun v _ => ?_
      unfold backPred
      simp [h15, hcnone (by omega) (by omega) (by omega) v]
    have hzero2 : ∑ v ∈ Finset.Icc 37 M,
          (match backPred o v with
           | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
           | none => 0) = 0 := by
      refine Finset.sum_eq_zero fun v _ => ?_
      unfold backPred
      simp [h15, hcnone (by omega) (by omega) (by omega) v]
    rw [hzero1, hzero2, add_zero]
    exact Nat.cast_nonneg _

private lemma certPairW_row_C (o M : ℕ) (ho : InABC15 o) (h15 : o % 15 = 2) :
    (∑ v ∈ Finset.Icc 1 36,
      (match backPred o v with
       | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
       | none => 0)) +
    (∑ v ∈ Finset.Icc 37 M,
      (match backPred o v with
       | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
       | none => 0)) ≤ certPairW o := by
  have ha0 : 0 < aPVal := by norm_num [aPVal]
  have ha1 : aPVal < 1 := by norm_num [aPVal]
  set r := o % 643125
  set q := r / 15
  have hq_lt : q < 42875 := by have := Nat.mod_lt o (by omega : 0 < 643125); omega
  have hr15 : r % 15 = o % 15 := Nat.mod_mod_of_dvd o (by decide : 15 ∣ 643125)
  have hr25 : r % 25 = o % 25 := Nat.mod_mod_of_dvd o (by decide : 25 ∣ 643125)
  have hr_eq : r = 15 * q + 2 := by omega
  have hchk := checkQ_all q hq_lt
  simp only [checkQ, Bool.and_eq_true, Nat.ble_eq] at hchk
  have hcertC : tailAVal + sumD1C r + sumD5C r ≤ 1000000 * getWC (q % 6125) := by
    have := hchk.1.2; rwa [← hr_eq] at this
  have hhead : ∑ v ∈ Finset.Icc 1 36,
        (match backPred o v with
         | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
         | none => 0) ≤
      ((sumD1C r : ℝ) + (sumD5C r : ℝ)) / 1000000 := by
    have hd1_set : (Finset.Icc 1 36).filter (fun v => v % 4 = 0) =
        {4, 8, 12, 16, 20, 24, 28, 32, 36} := by decide
    have hterm : ∀ v ∈ Finset.Icc 1 36,
        (match backPred o v with
         | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
         | none => 0) ≤
        (if v % 4 = 0 then
          ((getF1 v : ℝ) * (getWA (((2 ^ v * r) % 643125 - 1) / 15) : ℝ)) / 1000000 else 0) +
        (if (2 ^ v * r) % 25 = 1 then
          ((getF5 v : ℝ) * (getWB (((2 ^ v * r) % 643125 - 1) / 75) : ℝ)) / 1000000 else 0) := by
      intro v hv
      simp only [Finset.mem_Icc] at hv
      unfold backPred
      simp only [h15, show ¬(2 = 1) by omega, ↓reduceIte]
      have hmod25 : (2 ^ v * o) % 25 = (2 ^ v * r) % 25 := by
        rw [Nat.mul_mod, ← hr25, ← Nat.mul_mod]
      by_cases hv4 : v % 4 = 0
      · simp only [hv4, ↓reduceIte, Nat.cast_one, Real.one_rpow, one_mul]
        have hbp : backPred o v = some (1, 2 ^ v * o - 1) := by unfold backPred; simp [h15, hv4]
        rw [certPairW_child_d1 ho hv.1 hbp]
        have hf1 := aP_pow_le_getF1 hv.1 hv.2
        have h1 := mul_le_mul_of_nonneg_right hf1
          (Nat.cast_nonneg (α := ℝ) (getWA (((2 ^ v * r) % 643125 - 1) / 15)))
        have hnn : (0 : ℝ) ≤ if (2 ^ v * r) % 25 = 1 then
            ((getF5 v : ℝ) * (getWB (((2 ^ v * r) % 643125 - 1) / 75) : ℝ)) / 1000000 else 0 := by
          split_ifs <;> positivity
        linarith [show (getF1 v : ℝ) / 1000000 * (getWA (((2 ^ v * r) % 643125 - 1) / 15) : ℝ) =
          ((getF1 v : ℝ) * (getWA (((2 ^ v * r) % 643125 - 1) / 15) : ℝ)) / 1000000 by ring]
      · simp only [hv4, ↓reduceIte, zero_add, hmod25]
        by_cases h25 : (2 ^ v * r) % 25 = 1
        · simp only [h25, ↓reduceIte]
          have hbp : backPred o v = some (5, (2 ^ v * o - 1) / 5) := by
            unfold backPred; simp [h15, hv4, hmod25, h25]
          rw [certPairW_child_d5 ho hv.1 hbp]
          have hf5 := five_aP_pow_le_getF5 hv.1 hv.2
          have h1 := mul_le_mul_of_nonneg_right hf5
            (Nat.cast_nonneg (α := ℝ) (getWB (((2 ^ v * r) % 643125 - 1) / 75)))
          push_cast at h1 ⊢
          linarith [show (getF5 v : ℝ) / 1000000 * (getWB (((2 ^ v * r) % 643125 - 1) / 75) : ℝ) =
            ((getF5 v : ℝ) * (getWB (((2 ^ v * r) % 643125 - 1) / 75) : ℝ)) / 1000000 by ring]
        · simp [h25]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, hd1_set]
    have hd1_eq : ∑ v ∈ ({4, 8, 12, 16, 20, 24, 28, 32, 36} : Finset ℕ),
          ((getF1 v : ℝ) * (getWA (((2 ^ v * r) % 643125 - 1) / 15) : ℝ)) / 1000000 =
        (sumD1C r : ℝ) / 1000000 := by
      rw [sumD1C_eq,
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_insert (by decide),
          Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
      push_cast; ring
    have hd5_eq : ∑ v ∈ (Finset.Icc 1 36).filter (fun v => (2 ^ v * r) % 25 = 1),
          ((getF5 v : ℝ) * (getWB (((2 ^ v * r) % 643125 - 1) / 75) : ℝ)) / 1000000 =
        (sumD5C r : ℝ) / 1000000 := by
      have hflt : ∀ v, (2 ^ v * r) % 25 = 1 ↔ (2 ^ v * (r % 25)) % 25 = 1 := fun v => by
        rw [Nat.mul_mod, Nat.mul_mod (2 ^ v) (r % 25), Nat.mod_mod]
      simp_rw [hflt]
      have hr25_cases : r % 25 = 2 ∨ r % 25 = 7 ∨ r % 25 = 12 ∨ r % 25 = 17 ∨ r % 25 = 22 := by omega
      rcases hr25_cases with h | h | h | h | h
      · have hs : (Finset.Icc 1 36).filter (fun v => (2 ^ v * 2) % 25 = 1) = {19} := by decide
        rw [h, hs, sumD5C_eq_2 r h, Finset.sum_singleton]; push_cast; ring
      · have hs : (Finset.Icc 1 36).filter (fun v => (2 ^ v * 7) % 25 = 1) = {15, 35} := by decide
        rw [h, hs, sumD5C_eq_7 r h, Finset.sum_pair (by decide)]; push_cast; ring
      · have hs : (Finset.Icc 1 36).filter (fun v => (2 ^ v * 12) % 25 = 1) = {11, 31} := by decide
        rw [h, hs, sumD5C_eq_12 r h, Finset.sum_pair (by decide)]; push_cast; ring
      · have hs : (Finset.Icc 1 36).filter (fun v => (2 ^ v * 17) % 25 = 1) = {7, 27} := by decide
        rw [h, hs, sumD5C_eq_17 r h, Finset.sum_pair (by decide)]; push_cast; ring
      · have hs : (Finset.Icc 1 36).filter (fun v => (2 ^ v * 22) % 25 = 1) = {3, 23} := by decide
        rw [h, hs, sumD5C_eq_22 r h, Finset.sum_pair (by decide)]; push_cast; ring
    rw [hd1_eq, hd5_eq, add_div]
  have htail : ∑ v ∈ Finset.Icc 37 M,
        (match backPred o v with
         | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
         | none => 0) ≤ (tailAVal : ℝ) / 1000000 := by
    have h5 : o % 5 = 2 := by omega
    have hle : ∑ v ∈ Finset.Icc 37 M,
          (match backPred o v with
           | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
           | none => 0) ≤
        (∑ v ∈ (Finset.Icc 37 M).filter (fun v => v % 4 = 0 % 4), aPVal ^ v) * (123192 : ℝ) +
        (5 : ℝ) ^ sPVal *
          (∑ v ∈ (Finset.Icc 37 M).filter (fun v => v % 20 = v5Class (o % 25) % 20), aPVal ^ v) *
            (226730 : ℝ) := by
      rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_filter, Finset.sum_filter,
          ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun v hv => ?_
      have hv1 : 1 ≤ v := by simp only [Finset.mem_Icc] at hv; omega
      unfold backPred
      simp only [h15, show ¬(2 = 1) by omega, ↓reduceIte]
      by_cases hv4 : v % 4 = 0
      · simp only [hv4, ↓reduceIte, Nat.cast_one, Real.one_rpow, one_mul]
        have hbp : backPred o v = some (1, 2 ^ v * o - 1) := by unfold backPred; simp [h15, hv4]
        rw [certPairW_child_d1 ho hv1 hbp]
        have hw := getWA_le (((2 ^ v * r) % 643125 - 1) / 15)
        have hnn : (0 : ℝ) ≤ if v % 20 = v5Class (o % 25) % 20 then
            (5 : ℝ) ^ sPVal * aPVal ^ v * 226730 else 0 := by split_ifs <;> positivity
        have h1 : aPVal ^ v * (getWA (((2 ^ v * r) % 643125 - 1) / 15) : ℝ) ≤ aPVal ^ v * 123192 :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hw) (by positivity)
        linarith
      · simp only [hv4, ↓reduceIte, zero_add]
        by_cases h25 : (2 ^ v * o) % 25 = 1
        · have hv20 : v % 20 = v5Class (o % 25) % 20 := (v5Class_spec o v (Or.inr h5)).mp h25
          simp only [h25, hv20, ↓reduceIte]
          have hbp : backPred o v = some (5, (2 ^ v * o - 1) / 5) := by
            unfold backPred; simp [h15, hv4, h25]
          rw [certPairW_child_d5 ho hv1 hbp]
          have hw := getWB_le (((2 ^ v * r) % 643125 - 1) / 75)
          push_cast
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hw) (by positivity)
        · simp only [h25, ↓reduceIte]; split_ifs <;> positivity
    have hg1 := finite_geom_step_le (step := 4) (r := 0) (lo := 37) (L := M) ha0 ha1 (by omega)
    have hg5 := finite_geom_step_le (step := 20) (r := v5Class (o % 25)) (lo := 37) (L := M)
      ha0 ha1 (by omega)
    have h1 := mul_le_mul_of_nonneg_right hg1 (by norm_num : (0 : ℝ) ≤ 123192)
    have h2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hg5 (by positivity : (0 : ℝ) ≤ (5 : ℝ) ^ sPVal))
      (by norm_num : (0 : ℝ) ≤ 226730)
    linarith [tailA_bound]
  have hcertR : ((tailAVal : ℝ) + (sumD1C r : ℝ) + (sumD5C r : ℝ)) / 1000000 ≤
      (getWC (q % 6125) : ℝ) := by
    have hR : (tailAVal : ℝ) + (sumD1C r : ℝ) + (sumD5C r : ℝ) ≤
        1000000 * (getWC (q % 6125) : ℝ) := by exact_mod_cast hcertC
    linarith
  have hw_eq : certPairW o = (getWC (q % 6125) : ℝ) := by
    unfold certPairW; simp [h15, show ¬(2 = 1) by omega, show ¬(2 = 0) by omega, q, r]
  rw [hw_eq]; linarith

-- Exact row inequality for `certPairW` at `(a_P, s_P) = (7116/10000, 9/25)`.
private lemma certPairW_row_le (o M : ℕ) (ho : InABC15 o) :
    ∑ v ∈ Finset.Icc 1 M,
      (match backPred o v with
       | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
       | none => 0) ≤ certPairW o := by
  have ha0 : 0 < aPVal := by norm_num [aPVal]
  have hsplit36 : ∑ v ∈ Finset.Icc 1 M,
        (match backPred o v with
         | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
         | none => 0) ≤
      (∑ v ∈ Finset.Icc 1 36,
        (match backPred o v with
         | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
         | none => 0)) +
      (∑ v ∈ Finset.Icc 37 M,
        (match backPred o v with
         | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
         | none => 0)) := by
    have hnn : ∀ v, (0 : ℝ) ≤ match backPred o v with
        | some (d_mv, m) => (d_mv : ℝ) ^ sPVal * aPVal ^ v * certPairW m
        | none => 0 := fun v => by
      cases hbp : backPred o v with
      | none => exact le_rfl
      | some p =>
        have hw : 0 ≤ certPairW p.2 := by unfold certPairW; split_ifs <;> positivity
        positivity
    have hdisj : Disjoint (Finset.Icc 1 36) (Finset.Icc 37 M) := by
      rw [Finset.disjoint_left]; intro v h1 h2
      simp only [Finset.mem_Icc] at h1 h2; omega
    rw [← Finset.sum_union hdisj]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun v hv => ?_) (fun v _ _ => hnn v)
    simp only [Finset.mem_Icc, Finset.mem_union] at hv ⊢; omega
  refine hsplit36.trans ?_
  rcases ho.2.2 with h15 | h15 | h15
  · exact certPairW_row_A o M ho h15
  · exact certPairW_row_B o M ho h15
  · exact certPairW_row_C o M ho h15

/-- Case 3 (Certified `Q1 = 643,125` pair bound): for every `L ≥ 0` and `o ∈ A ∪ B ∪ C`,
    `∑_{l ∈ backPaths o L} D(o, l)^{9/25} ≤ 226,730 * (10000 / 7116)^L`. -/
theorem pair_backPaths_bound (L o : ℕ) (ho : InABC15 o) :
    ∑ l ∈ backPaths o L, ((backEnd o l).2 : ℝ) ^ sPVal ≤ 226730 * (1 / aPVal) ^ L := by
  have ha0 : 0 < aPVal := by norm_num [aPVal]
  have h := backPaths_weighted_bound ha0 certPairW certPairW_ge_one certPairW_row_le L o ho
  have hle : aPVal ^ L * ∑ l ∈ backPaths o L, ((backEnd o l).2 : ℝ) ^ sPVal ≤ 226730 :=
    h.trans (certPairW_le_max o)
  rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos ha0 L)]
  linarith

/-! ## Section 7: Trajectory analysis and 3-case inductive proof of `thm:basin-sharp` Part 1b -/

/-- `k`-th odd iterate along the odd-to-odd trajectory starting from `n`. -/
def oddIter (k n : ℕ) : ℕ := (fun x => (oddStep x).2)^[k] n

/-- Cumulative halvings along the first `k` odd steps from `n`. -/
def cumHalv : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => (oddStep n).1 + cumHalv k (oddStep n).2

/-- Cumulative digit product along the first `k` odd steps from `n`. -/
def cumDigitProd : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k + 1, n => d n * cumDigitProd k (oddStep n).2

/-- Reverse valuation list of the first `k` odd steps from `n` (ordered from `oddIter k n` back to `n`). -/
def revValList : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, n => revValList k (oddStep n).2 ++ [(oddStep n).1]

private lemma oddStep_one_snd : (oddStep 1).2 = 1 := by
  obtain ⟨hv1, ho_odd, hfac⟩ := oddStep_spec (by decide : 1 % 2 = 1)
  have hd1 : d 1 = 1 := by decide
  rw [hd1] at hfac
  have h2v : 2 ≤ 2 ^ (oddStep 1).1 := calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (oddStep 1).1 := Nat.pow_le_pow_right (by norm_num) hv1
  have ho1 : 1 ≤ (oddStep 1).2 := by omega
  nlinarith

private lemma oddStep_reaches_one {n : ℕ} (hn : n % 2 = 1) (hr : Reaches f n 1) :
    Reaches f (oddStep n).2 1 := by
  obtain ⟨hv1, ho_odd, hfac⟩ := oddStep_spec hn
  rcases hr with ⟨k, hk⟩
  cases k with
  | zero =>
    simp only [Function.iterate_zero, id_eq] at hk
    subst hk
    rw [oddStep_one_snd]; exact reaches_refl f 1
  | succ k =>
    rw [Function.iterate_succ_apply, f_odd hn, hfac] at hk
    exact ⟨k - (oddStep n).1, (f_iter_two_pow_eq_odd (by decide) hk).2⟩

private lemma oddIter_props (k n : ℕ) (hn : n % 2 = 1) (hr : Reaches f n 1) :
    oddIter k n % 2 = 1 ∧ Reaches f (oddIter k n) 1 ∧ InABC15 (oddIter k n) := by
  induction k generalizing n with
  | zero =>
    have hABC := thm_residue_law hn hr
    have hn_pos : 0 < n := by omega
    have h15 : n % 15 = 1 ∨ n % 15 = 0 ∨ n % 15 = 2 := by
      simp only [InABC, InA, InB, InC] at hABC; omega
    exact ⟨hn, hr, ⟨hn_pos, hn, h15⟩⟩
  | succ k ih =>
    unfold oddIter at *
    rw [Function.iterate_succ_apply]
    exact ih (oddStep n).2 (oddStep_spec hn).2.1 (oddStep_reaches_one hn hr)

private lemma exists_oddIter_eq_one {n : ℕ} (hn : n % 2 = 1) (hr : Reaches f n 1) :
    ∃ m : ℕ, oddIter m n = 1 := by
  rcases hr with ⟨k, hk⟩
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    cases k with
    | zero => exact ⟨0, by simpa [oddIter] using hk⟩
    | succ k =>
      obtain ⟨hv1, ho_odd, hfac⟩ := oddStep_spec hn
      rw [Function.iterate_succ_apply, f_odd hn, hfac] at hk
      obtain ⟨hle, hko⟩ := f_iter_two_pow_eq_odd (by decide) hk
      obtain ⟨m, hm⟩ := ih (k - (oddStep n).1) (by omega) ho_odd hko
      refine ⟨m + 1, ?_⟩
      unfold oddIter at hm ⊢
      rw [Function.iterate_succ_apply]
      exact hm

private lemma oddIter_inj_before_stop {n m : ℕ} (hm : oddIter m n = 1)
    (hmin : ∀ j < m, oddIter j n ≠ 1) :
    ∀ i j, i < m → j < m → oddIter i n = oddIter j n → i = j := by
  intro i j hi hj heq
  wlog hle : i ≤ j generalizing i j
  · exact (this j i hj hi heq.symm (by omega)).symm
  by_contra hne
  have hper : ∀ t : ℕ, oddIter (i + t * (j - i)) n = oddIter i n := by
    intro t
    induction t with
    | zero => simp
    | succ t iht =>
      have h1 : i + (t + 1) * (j - i) = (j - i) + (i + t * (j - i)) := by ring
      rw [h1]
      unfold oddIter at iht heq ⊢
      rw [Function.iterate_add_apply, iht]
      have h2 : (j - i) + i = j := by omega
      rw [← Function.iterate_add_apply, h2, heq]
  -- Now express m = i + q*(j - i) + r with r < j - i, giving oddIter (i + r) n = 1!
  have hpos : 0 < j - i := by omega
  let q := (m - i) / (j - i)
  let r := (m - i) % (j - i)
  have hm_eq : m = r + (i + q * (j - i)) := by
    have hdm : q * (j - i) + r = m - i := by
      have := Nat.div_add_mod (m - i) (j - i)
      rwa [mul_comm] at this
    omega
  have h1 : oddIter (i + r) n = 1 := by
    unfold oddIter at hm hper ⊢
    rw [hm_eq, Function.iterate_add_apply, hper q] at hm
    rwa [add_comm i r, Function.iterate_add_apply]
  exact hmin (i + r) (by have := Nat.mod_lt (m - i) hpos; omega) h1

/-- Exact step product identity along `k` odd steps:
    `2^(cumHalv k n) * oddIter k n = cumDigitProd k n * n * ∏_{j < k} (1 + 1 / (d(x_j) * x_j))`. -/
private lemma traj_prod_identity (k n : ℕ) (hn : n % 2 = 1) (hr : Reaches f n 1) :
    (2 : ℝ) ^ cumHalv k n * (oddIter k n : ℝ) =
      (cumDigitProd k n : ℝ) * (n : ℝ) *
        ∏ j ∈ Finset.range k, (1 + 1 / ((d (oddIter j n) : ℝ) * (oddIter j n : ℝ))) := by
  induction k generalizing n with
  | zero => simp [cumHalv, oddIter, cumDigitProd]
  | succ k ih =>
    obtain ⟨hv1, ho_odd, hfac⟩ := oddStep_spec hn
    have hro := oddStep_reaches_one hn hr
    have hih := ih (oddStep n).2 ho_odd hro
    have hstep_R : (2 : ℝ) ^ (oddStep n).1 * ((oddStep n).2 : ℝ) =
        (d n : ℝ) * (n : ℝ) * (1 + 1 / ((d n : ℝ) * (n : ℝ))) := by
      have hdn : 0 < d n := by
        have hABC := thm_residue_law hn hr
        simp only [InABC, InA, InB, InC] at hABC; unfold d; omega
      have hn_pos : 0 < n := by omega
      have hne : (d n : ℝ) * (n : ℝ) ≠ 0 := by positivity
      have hfR : (d n : ℝ) * (n : ℝ) + 1 = (2 : ℝ) ^ (oddStep n).1 * ((oddStep n).2 : ℝ) := by
        exact_mod_cast hfac
      field_simp; linarith
    have hiter_succ : oddIter (k + 1) n = oddIter k (oddStep n).2 := by
      unfold oddIter; rw [Function.iterate_succ_apply]
    have hprod_split : ∏ j ∈ Finset.range (k + 1),
          (1 + 1 / ((d (oddIter j n) : ℝ) * (oddIter j n : ℝ))) =
        (1 + 1 / ((d n : ℝ) * (n : ℝ))) *
          ∏ j ∈ Finset.range k,
            (1 + 1 / ((d (oddIter j (oddStep n).2) : ℝ) * (oddIter j (oddStep n).2 : ℝ))) := by
      rw [Finset.prod_range_succ']
      simp only [oddIter, Function.iterate_zero, id_eq, Function.iterate_succ_apply]
      ring
    simp only [cumHalv, cumDigitProd, hiter_succ, hprod_split, pow_add, Nat.cast_mul]
    have hstep_mul : ((2 : ℝ) ^ (oddStep n).1 * (2 : ℝ) ^ cumHalv k (oddStep n).2) *
          (oddIter k (oddStep n).2 : ℝ) =
        (2 : ℝ) ^ (oddStep n).1 * ((2 : ℝ) ^ cumHalv k (oddStep n).2 * (oddIter k (oddStep n).2 : ℝ)) := by
      ring
    rw [hstep_mul, hih]
    calc (2 : ℝ) ^ (oddStep n).1 * ((cumDigitProd k (oddStep n).2 : ℝ) * ((oddStep n).2 : ℝ) *
            ∏ j ∈ Finset.range k,
              (1 + 1 / ((d (oddIter j (oddStep n).2) : ℝ) * (oddIter j (oddStep n).2 : ℝ))))
        = (cumDigitProd k (oddStep n).2 : ℝ) * ((2 : ℝ) ^ (oddStep n).1 * ((oddStep n).2 : ℝ)) *
            ∏ j ∈ Finset.range k,
              (1 + 1 / ((d (oddIter j (oddStep n).2) : ℝ) * (oddIter j (oddStep n).2 : ℝ))) := by ring
      _ = (cumDigitProd k (oddStep n).2 : ℝ) *
            ((d n : ℝ) * (n : ℝ) * (1 + 1 / ((d n : ℝ) * (n : ℝ)))) *
            ∏ j ∈ Finset.range k,
              (1 + 1 / ((d (oddIter j (oddStep n).2) : ℝ) * (oddIter j (oddStep n).2 : ℝ))) := by
            rw [hstep_R]
      _ = (d n : ℝ) * (cumDigitProd k (oddStep n).2 : ℝ) * (n : ℝ) *
            ((1 + 1 / ((d n : ℝ) * (n : ℝ))) *
              ∏ j ∈ Finset.range k,
                (1 + 1 / ((d (oddIter j (oddStep n).2) : ℝ) * (oddIter j (oddStep n).2 : ℝ)))) := by
            ring

/-- Completeness of `backPaths` and `backEnd` along any `k`-step trajectory from `n`. -/
private lemma backPaths_mem_revValList (k n : ℕ) (hn : n % 2 = 1) (hr : Reaches f n 1) :
    revValList k n ∈ backPaths (oddIter k n) (cumHalv k n) ∧
    backEnd (oddIter k n) (revValList k n) = (n, cumDigitProd k n) := by
  -- Helper: appending one final backward move `[v]` to a valid path in `backPaths o L`
  have happend : ∀ (L o v d_mv m : ℕ) (l : List ℕ),
      l ∈ backPaths o L →
      backPred (backEnd o l).1 v = some (d_mv, m) →
      1 ≤ v →
      l ++ [v] ∈ backPaths o (L + v) ∧
      backEnd o (l ++ [v]) = (m, (backEnd o l).2 * d_mv) := by
    intro L
    induction L using Nat.strong_induction_on with
    | h L ih =>
      intro o v d_mv m l hl hbp hv1
      match L with
      | 0 =>
        simp only [backPaths, Finset.mem_singleton] at hl
        subst hl
        simp only [backEnd, List.nil_append] at hbp ⊢
        have hpos : 0 + v = (v - 1) + 1 := by omega
        rw [hpos]
        constructor
        · unfold backPaths
          simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists, Finset.mem_Icc]
          refine ⟨v, ⟨hv1, by omega⟩, ?_⟩
          rw [hbp]
          simp only [show v - 1 + 1 - v = 0 by omega, backPaths, Finset.image_singleton,
            Finset.mem_singleton]
        · simp [hbp]
      | L + 1 =>
        unfold backPaths at hl
        simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists,
          Finset.mem_Icc] at hl
        obtain ⟨v0, hv0, hl'⟩ := hl
        cases hbp0 : backPred o v0 with
        | none => simp [hbp0] at hl'
        | some p0 =>
          rcases p0 with ⟨d0, m0⟩
          rw [hbp0] at hl'
          simp only [Finset.mem_image] at hl'
          obtain ⟨l0, hl0, rfl⟩ := hl'
          simp only [backEnd, hbp0] at hbp
          obtain ⟨hmem_rec, hend_rec⟩ := ih (L + 1 - v0) (by omega) m0 v d_mv m l0 hl0 hbp hv1
          have hsum_eq : L + 1 + v = (L + v) + 1 := by omega
          constructor
          · rw [hsum_eq]; unfold backPaths
            simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists,
              Finset.mem_Icc]
            refine ⟨v0, ⟨hv0.1, by omega⟩, ?_⟩
            rw [hbp0]
            simp only [Finset.mem_image]
            refine ⟨l0 ++ [v], ?_, rfl⟩
            have : L + v + 1 - v0 = (L + 1 - v0) + v := by omega
            rwa [this]
          · simp only [List.cons_append, backEnd, hbp0, hend_rec]
            exact Prod.ext rfl (by ring)
  induction k generalizing n with
  | zero => simp [revValList, backPaths, oddIter, cumHalv, backEnd, cumDigitProd]
  | succ k ih =>
    obtain ⟨hv1, ho_odd, hfac⟩ := oddStep_spec hn
    have hro := oddStep_reaches_one hn hr
    obtain ⟨hmem, hend⟩ := ih (oddStep n).2 ho_odd hro
    have hiter : oddIter (k + 1) n = oddIter k (oddStep n).2 := by
      unfold oddIter; rw [Function.iterate_succ_apply]
    have ho_abc : InABC15 (oddStep n).2 := (oddIter_props 0 (oddStep n).2 ho_odd hro).2.2
    have hbp : backPred (oddStep n).2 (oddStep n).1 = some (d n, n) :=
      backPred_of_move ho_abc hv1 hn hfac
    have hbp' : backPred (backEnd (oddIter k (oddStep n).2) (revValList k (oddStep n).2)).1
        (oddStep n).1 = some (d n, n) := by rw [hend]; exact hbp
    obtain ⟨hmem', hend'⟩ := happend (cumHalv k (oddStep n).2) (oddIter k (oddStep n).2)
      (oddStep n).1 (d n) n (revValList k (oddStep n).2) hmem hbp' hv1
    rw [hiter]
    simp only [revValList, cumHalv, cumDigitProd]
    rw [add_comm (oddStep n).1 (cumHalv k (oddStep n).2)]
    refine ⟨hmem', ?_⟩
    rw [hend', hend]
    exact Prod.ext rfl (mul_comm _ _)

/-- Exact relation between `phiWord K n` and `(cumHalv, cumDigitProd, oddIter)`:
    letting `r = (phiWord K n).length`, we have `cumHalv r n < K ≤ cumHalv (r + 1) n`
    and `wordDigitProd (clsIdx n) (phiWord K n) = cumDigitProd r n`. -/
private lemma phiWord_crossing_spec (K : ℕ) (hK : 1 ≤ K) :
    ∀ n : ℕ, n % 2 = 1 → Reaches f n 1 →
      let r := (phiWord K n).length
      cumHalv r n < K ∧ K ≤ cumHalv (r + 1) n ∧
      wordDigitProd (clsIdx n) (phiWord K n) = cumDigitProd r n := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    match K with
    | 0 => omega
    | 1 =>
      intro n hn _
      have hv1 := (oddStep_spec hn).1
      simp [phiWord, cumHalv, wordDigitProd, cumDigitProd, hv1]
    | K + 2 =>
      intro n hn hr
      obtain ⟨hv1, ho_odd, _⟩ := oddStep_spec hn
      have hro := oddStep_reaches_one hn hr
      have hABC_n := thm_residue_law hn hr
      have hABC_o := thm_residue_law ho_odd hro
      have hdig : clsDigit (clsIdx n) = d n := by
        simp only [InABC, InA, InB, InC] at hABC_n
        rcases hABC_n with h | h | h <;> (unfold clsDigit clsIdx d; simp [h]; omega)
      unfold phiWord
      split_ifs with hv
      · obtain ⟨hrec1, hrec2, hrec3⟩ := ih (K + 2 - (oddStep n).1) (by omega) (by omega) (oddStep n).2 ho_odd hro
        have hedge := oddStep_admEdge hABC_n hABC_o
        have hnxt : clsIdx (oddStep n).2 = nextCls (clsIdx n) (oddStep n).1 :=
          admEdge_iff_nextCls _ _ _ hedge
        simp only [List.length_cons]
        change (oddStep n).1 + cumHalv _ (oddStep n).2 < K + 2 ∧
          K + 2 ≤ (oddStep n).1 + cumHalv (_ + 1) (oddStep n).2 ∧
          clsDigit (clsIdx n) * wordDigitProd (nextCls (clsIdx n) (oddStep n).1) _ =
            d n * cumDigitProd _ (oddStep n).2
        rw [← hnxt, hdig, hrec3]
        exact ⟨by omega, by omega, rfl⟩
      · simp only [List.length_nil, cumHalv, wordDigitProd, cumDigitProd]
        exact ⟨by omega, by omega, trivial⟩

private lemma finset_prod_le_prod_nonneg {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hga : f a ≤ g a := hfg a (Finset.mem_insert_self a s)
    have hps : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hih := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    exact mul_le_mul hga hih hps (hfa.trans hga)

def inCase1 (K n : ℕ) : Prop :=
  ∃ m : ℕ, oddIter m n = 1 ∧ cumHalv m n < K

def inCase2 (K n : ℕ) : Prop :=
  ¬ inCase1 K n ∧ (2 : ℝ) ^ (deltaParam * (K : ℝ)) ≤
    (wordDigitProd (clsIdx n) (phiWord K n) : ℝ)

def inCase3 (K n : ℕ) : Prop :=
  ¬ inCase1 K n ∧ (wordDigitProd (clsIdx n) (phiWord K n) : ℝ) <
    (2 : ℝ) ^ (deltaParam * (K : ℝ))

open Classical in
private lemma case1_card_bound (X K : ℕ) :
    ((((Finset.Icc 1 X).filter (fun n => n % 2 = 1 ∧ Reaches f n 1)).filter
        (inCase1 K)).card : ℝ) ≤
      30 * (2 : ℝ) ^ (betaPrime * (K : ℝ)) := by
  let S1 := ((Finset.Icc 1 X).filter (fun n => n % 2 = 1 ∧ Reaches f n 1)).filter (inCase1 K)
  let T1 : Finset (ℕ × List ℕ) :=
    (Finset.range K).biUnion fun L => (backPaths 1 L).image (fun l => (L, l))
  have hcard1 : S1.card ≤ T1.card := by
    refine Finset.card_le_card_of_injOn (fun n =>
        if h : ∃ m, oddIter m n = 1 ∧ cumHalv m n < K then
          (cumHalv (Nat.find h) n, revValList (Nat.find h) n)
        else (0, [])) ?_ ?_
    · intro n hn
      simp only [Finset.mem_coe, S1, Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨_, hn_odd, hr⟩, h1⟩ := hn
      dsimp only
      split_ifs with h1'
      · set m := Nat.find h1'
        obtain ⟨hm1, hmK⟩ := Nat.find_spec h1'
        obtain ⟨hmem, _⟩ := backPaths_mem_revValList m n hn_odd hr
        rw [hm1] at hmem
        simp only [Finset.mem_coe, T1, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
        exact ⟨cumHalv m n, hmK, revValList m n, hmem, rfl⟩
      · exact False.elim (h1' h1)
    · intro a ha b hb hEq
      simp only [Finset.mem_coe, S1, Finset.mem_filter, Finset.mem_Icc] at ha hb
      obtain ⟨⟨_, ha_odd, hra⟩, h1a⟩ := ha
      obtain ⟨⟨_, hb_odd, hrb⟩, h1b⟩ := hb
      dsimp only at hEq
      split_ifs at hEq with h1a' h1b'
      · simp only [Prod.mk.injEq] at hEq
        set ma := Nat.find h1a'
        set mb := Nat.find h1b'
        obtain ⟨hma1, _⟩ := Nat.find_spec h1a'
        obtain ⟨hmb1, _⟩ := Nat.find_spec h1b'
        have hea := (backPaths_mem_revValList ma a ha_odd hra).2
        have heb := (backPaths_mem_revValList mb b hb_odd hrb).2
        rw [hma1] at hea; rw [hmb1] at heb
        have h1 := congr_arg (fun l => (backEnd 1 l).1) hEq.2
        rw [hea, heb] at h1
        exact h1
      · exact False.elim (h1b' h1b)
      · exact False.elim (h1a' h1a)
      · exact False.elim (h1a' h1a)
  have hT1_card : T1.card ≤ ∑ L ∈ Finset.range K, (backPaths 1 L).card := by
    unfold T1
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun L _ => Finset.card_image_le)
  have h1_abc : InABC15 1 := ⟨by omega, by decide, Or.inl (by decide)⟩
  have hS1_real : (S1.card : ℝ) ≤ 10 * ∑ L ∈ Finset.range K, (1 / aHVal) ^ L := by
    have hcast : (S1.card : ℝ) ≤ ∑ L ∈ Finset.range K, ((backPaths 1 L).card : ℝ) := by
      exact_mod_cast hcard1.trans hT1_card
    refine hcast.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun L _ => ?_
    have hb := depth_backPaths_bound L 1 h1_abc
    simp only [wHVec, show (1 : ℕ) % 15 = 1 by decide, ↓reduceIte] at hb
    rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by norm_num [aHVal] : (0 : ℝ) < aHVal ^ L)]
    linarith
  have hgeom : ∑ L ∈ Finset.range K, (1 / aHVal) ^ L ≤ 3 * (1 / aHVal) ^ K := by
    rw [geom_sum_eq (by norm_num [aHVal] : (1 / aHVal : ℝ) ≠ 1)]
    have h1 : (1 / aHVal : ℝ) - 1 = 1 / 2 := by norm_num [aHVal]
    rw [h1]
    linarith [show (0 : ℝ) ≤ (1 / aHVal) ^ K by norm_num [aHVal]]
  have hpow_le : (1 / aHVal) ^ K ≤ (2 : ℝ) ^ (betaPrime * (K : ℝ)) := by
    calc (1 / aHVal) ^ K ≤ ((2 : ℝ) ^ ((3 : ℝ) / 5)) ^ K :=
          pow_le_pow_left₀ (by norm_num [aHVal]) inv_aH_le_two_rpow K
      _ = (2 : ℝ) ^ (((3 : ℝ) / 5) * (K : ℝ)) := by
          rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num)]
      _ ≤ (2 : ℝ) ^ (betaPrime * (K : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (mul_le_mul_of_nonneg_right (by norm_num [betaPrime]) (Nat.cast_nonneg K))
  calc (S1.card : ℝ) ≤ 10 * (3 * (1 / aHVal) ^ K) :=
        hS1_real.trans (mul_le_mul_of_nonneg_left hgeom (by norm_num))
    _ = 30 * (1 / aHVal) ^ K := by ring
    _ ≤ 30 * (2 : ℝ) ^ (betaPrime * (K : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow_le (by norm_num)

open Classical in
private lemma case2_card_bound (X K : ℕ) (hK1 : 1 ≤ K) (hX2K : X < 2 ^ K) :
    ((((Finset.Icc 1 X).filter (fun n => n % 2 = 1 ∧ Reaches f n 1)).filter
        (inCase2 K)).card : ℝ) ≤
      ((hFVec 0 + hFVec 1 + hFVec 2) / (1 - aFVal)) * (2 : ℝ) ^ (betaPrime * (K : ℝ)) := by
  let S2 := ((Finset.Icc 1 X).filter (fun n => n % 2 = 1 ∧ Reaches f n 1)).filter (inCase2 K)
  let T2 : Finset (Fin 3 × List ℕ) :=
    Finset.univ.biUnion fun c : Fin 3 =>
      (Finset.range K).biUnion fun L =>
        ((admWords c L).filter fun w =>
          (2 : ℝ) ^ (deltaParam * (K : ℝ)) ≤ (wordDigitProd c w : ℝ)).image (fun w => (c, w))
  have hcard2 : S2.card ≤ T2.card := by
    refine Finset.card_le_card_of_injOn (fun n => (clsIdx n, phiWord K n)) ?_ ?_
    · intro n hn
      simp only [Finset.mem_coe, S2, Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨_, hn_odd, hr⟩, _, hD⟩ := hn
      simp only [Finset.mem_coe, T2, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_range, Finset.mem_image, Finset.mem_filter]
      exact ⟨clsIdx n, (phiWord K n).sum, phiWord_sum_lt K n hK1, phiWord K n,
        ⟨phiWord_mem_admWords K hK1 n hn_odd hr, hD⟩, rfl⟩
    · intro a ha b hb hEq
      simp only [Finset.mem_coe, S2, Finset.mem_filter, Finset.mem_Icc] at ha hb
      obtain ⟨⟨⟨_, ha_le⟩, ha_odd, hra⟩, _⟩ := ha
      obtain ⟨⟨⟨_, hb_le⟩, hb_odd, hrb⟩, _⟩ := hb
      have hcls : clsIdx a = clsIdx b := congr_arg Prod.fst hEq
      have hphi : phiWord K a = phiWord K b := congr_arg Prod.snd hEq
      have hABC_a := thm_residue_law ha_odd hra
      have hABC_b := thm_residue_law hb_odd hrb
      have h30 : a % 30 = b % 30 := by
        simp only [InABC, InA, InB, InC] at hABC_a hABC_b
        rcases hABC_a with haA | haB | haC <;> rcases hABC_b with hbA | hbB | hbC <;>
          (unfold clsIdx at hcls; simp_all)
      have hmod := phiWord_inj_mod K hK1 a b ha_odd hb_odd (by omega) hphi
      have ha_lt : a < 15 * 2 ^ K := by omega
      have hb_lt : b < 15 * 2 ^ K := by omega
      rwa [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] at hmod
  have hT2_card : (T2.card : ℝ) ≤
      (2 : ℝ) ^ (-(sFVal * deltaParam * (K : ℝ))) *
        ∑ L ∈ Finset.range K, ∑ c : Fin 3,
          ∑ w ∈ admWords c L, (wordDigitProd c w : ℝ) ^ sFVal := by
    have h1 : T2.card ≤ ∑ L ∈ Finset.range K, ∑ c : Fin 3,
        ((admWords c L).filter fun w =>
          (2 : ℝ) ^ (deltaParam * (K : ℝ)) ≤ (wordDigitProd c w : ℝ)).card := by
      rw [Finset.sum_comm]
      unfold T2
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun c _ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun L _ => Finset.card_image_le)
    have hcast : (T2.card : ℝ) ≤ ∑ L ∈ Finset.range K, ∑ c : Fin 3,
        (((admWords c L).filter fun w =>
          (2 : ℝ) ^ (deltaParam * (K : ℝ)) ≤ (wordDigitProd c w : ℝ)).card : ℝ) := by
      exact_mod_cast h1
    refine hcast.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun L _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have hmarkov : (((admWords c L).filter fun w =>
          (2 : ℝ) ^ (deltaParam * (K : ℝ)) ≤ (wordDigitProd c w : ℝ)).card : ℝ) *
          (2 : ℝ) ^ (sFVal * deltaParam * (K : ℝ)) ≤
        ∑ w ∈ admWords c L, (wordDigitProd c w : ℝ) ^ sFVal := by
      have hfilt : (((admWords c L).filter fun w =>
            (2 : ℝ) ^ (deltaParam * (K : ℝ)) ≤ (wordDigitProd c w : ℝ)).card : ℝ) *
            (2 : ℝ) ^ (sFVal * deltaParam * (K : ℝ)) =
          ∑ _w ∈ (admWords c L).filter (fun w =>
            (2 : ℝ) ^ (deltaParam * (K : ℝ)) ≤ (wordDigitProd c w : ℝ)),
            (2 : ℝ) ^ (sFVal * deltaParam * (K : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [hfilt]
      refine (Finset.sum_le_sum fun w hw => ?_).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity)
      have hD := (Finset.mem_filter.mp hw).2
      have hpow : (2 : ℝ) ^ (sFVal * deltaParam * (K : ℝ)) =
          ((2 : ℝ) ^ (deltaParam * (K : ℝ))) ^ sFVal := by
        rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
      rw [hpow]
      exact Real.rpow_le_rpow (by positivity) hD (by norm_num [sFVal])
    rw [Real.rpow_neg (by norm_num), ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    exact hmarkov
  have hS2_sum : ∑ L ∈ Finset.range K, ∑ c : Fin 3,
        ∑ w ∈ admWords c L, (wordDigitProd c w : ℝ) ^ sFVal ≤
      (hFVec 0 + hFVec 1 + hFVec 2) * ∑ L ∈ Finset.range K, (1 / aFVal) ^ L := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun L _ => ?_
    rw [Fin.sum_univ_three]
    have hb := fun c => admWords_weighted_bound L c
    have hdiv : ∀ c : Fin 3, ∑ w ∈ admWords c L, (wordDigitProd c w : ℝ) ^ sFVal ≤
        hFVec c * (1 / aFVal) ^ L := fun c => by
      rw [one_div, inv_pow, ← div_eq_mul_inv,
          le_div_iff₀ (by norm_num [aFVal] : (0 : ℝ) < aFVal ^ L)]
      linarith [hb c]
    linarith [hdiv 0, hdiv 1, hdiv 2]
  have hgeomF : ∑ L ∈ Finset.range K, (1 / aFVal) ^ L ≤
      (1 / (1 - aFVal)) * (1 / aFVal) ^ K := by
    have haF_pos : 0 < aFVal := by norm_num [aFVal]
    rw [geom_sum_eq (by norm_num [aFVal] : (1 / aFVal : ℝ) ≠ 1)]
    have h1 : (1 / aFVal : ℝ) - 1 = (1 - aFVal) / aFVal := by norm_num [aFVal]
    rw [h1, div_div_eq_mul_div]
    have haF_le1 : aFVal ≤ 1 := by norm_num [aFVal]
    have hnum : ((1 / aFVal) ^ K - 1) * aFVal ≤ (1 / aFVal) ^ K := by
      have : (1 / aFVal) ^ K - 1 ≤ (1 / aFVal) ^ K := by linarith
      have : ((1 / aFVal) ^ K - 1) * aFVal ≤ (1 / aFVal) ^ K * 1 :=
        mul_le_mul this haF_le1 (by positivity) (by positivity)
      linarith
    have hden : 0 < 1 - aFVal := by norm_num [aFVal]
    calc ((1 / aFVal) ^ K - 1) * aFVal / (1 - aFVal)
        ≤ (1 / aFVal) ^ K / (1 - aFVal) := div_le_div_of_nonneg_right hnum hden.le
      _ = (1 / (1 - aFVal)) * (1 / aFVal) ^ K := by ring
  have hpowF : (2 : ℝ) ^ (-(sFVal * deltaParam * (K : ℝ))) * (1 / aFVal) ^ K ≤
      (2 : ℝ) ^ (betaPrime * (K : ℝ)) := by
    have h1 : (1 / aFVal) ^ K ≤ (2 : ℝ) ^ (((64 : ℝ) / 97) * (K : ℝ)) := by
      calc (1 / aFVal) ^ K ≤ ((2 : ℝ) ^ ((64 : ℝ) / 97)) ^ K :=
            pow_le_pow_left₀ (by norm_num [aFVal]) inv_aF_le_two_rpow K
        _ = (2 : ℝ) ^ (((64 : ℝ) / 97) * (K : ℝ)) := by
            rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num)]
    calc (2 : ℝ) ^ (-(sFVal * deltaParam * (K : ℝ))) * (1 / aFVal) ^ K
        ≤ (2 : ℝ) ^ (-(sFVal * deltaParam * (K : ℝ))) *
            (2 : ℝ) ^ (((64 : ℝ) / 97) * (K : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (2 : ℝ) ^ ((((64 : ℝ) / 97) - sFVal * deltaParam) * (K : ℝ)) := by
          rw [← Real.rpow_add (by norm_num)]; congr 1; ring
      _ ≤ (2 : ℝ) ^ (betaPrime * (K : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (mul_le_mul_of_nonneg_right
              (by norm_num [betaPrime, sFVal, deltaParam]) (Nat.cast_nonneg K))
  have hsum_nn : 0 ≤ hFVec 0 + hFVec 1 + hFVec 2 := by
    linarith [hFVec_ge_one 0, hFVec_ge_one 1, hFVec_ge_one 2]
  have hK2_nn : 0 ≤ (hFVec 0 + hFVec 1 + hFVec 2) / (1 - aFVal) :=
    div_nonneg hsum_nn (by norm_num [aFVal])
  calc (S2.card : ℝ) ≤ (T2.card : ℝ) := by exact_mod_cast hcard2
    _ ≤ (2 : ℝ) ^ (-(sFVal * deltaParam * (K : ℝ))) *
          ((hFVec 0 + hFVec 1 + hFVec 2) * ((1 / (1 - aFVal)) * (1 / aFVal) ^ K)) :=
        hT2_card.trans (mul_le_mul_of_nonneg_left
          (hS2_sum.trans (mul_le_mul_of_nonneg_left hgeomF hsum_nn)) (by positivity))
    _ = ((hFVec 0 + hFVec 1 + hFVec 2) / (1 - aFVal)) *
          ((2 : ℝ) ^ (-(sFVal * deltaParam * (K : ℝ))) * (1 / aFVal) ^ K) := by ring
    _ ≤ ((hFVec 0 + hFVec 1 + hFVec 2) / (1 - aFVal)) * (2 : ℝ) ^ (betaPrime * (K : ℝ)) :=
        mul_le_mul_of_nonneg_left hpowF hK2_nn

noncomputable def crossingYL (X K L : ℕ) : ℝ :=
  7 * Real.sqrt ((K : ℝ) + 1) * (X : ℝ) * (2 : ℝ) ^ (deltaParam * (K : ℝ)) / (2 : ℝ) ^ L

open Classical in
private lemma case3_inj_bound (X K Lmax : ℕ) (hK1 : 1 ≤ K)
    (hYL_lt1 : ∀ L, Lmax < L → crossingYL X K L < 1) :
    (((Finset.Icc 1 X).filter (fun n => n % 2 = 1 ∧ Reaches f n 1)).filter (inCase3 K)).card ≤
    ((Finset.Icc K Lmax).biUnion fun L =>
      ((Finset.Icc 1 (Nat.floor (crossingYL X K L))).filter
        (fun o => o % 2 = 1 ∧ Reaches f o 1)).biUnion fun o =>
        ((backPaths o L).filter fun l =>
          (2 : ℝ) ^ L * (o : ℝ) ≤
            Real.sqrt ((K : ℝ) + 1) * (X : ℝ) * ((backEnd o l).2 : ℝ)).image
          (fun l => (L, o, l))).card := by
  have hcum_step : ∀ k x, cumHalv k x ≤ cumHalv (k + 1) x := by
    intro k
    induction k with
    | zero => intro x; simp [cumHalv]
    | succ k ihk =>
      intro x
      change (oddStep x).1 + cumHalv k (oddStep x).2 ≤
        (oddStep x).1 + cumHalv (k + 1) (oddStep x).2
      have := ihk (oddStep x).2; omega
  have hr_le_Vr : ∀ k x, x % 2 = 1 → k ≤ cumHalv k x := by
    intro k
    induction k with
    | zero => intro _ _; simp [cumHalv]
    | succ k ihk =>
      intro x hx
      obtain ⟨hv1, ho_odd, _⟩ := oddStep_spec hx
      simp only [cumHalv]
      have := ihk (oddStep x).2 ho_odd; omega
  have hsplit_D : ∀ k x, cumDigitProd (k + 1) x = cumDigitProd k x * d (oddIter k x) := by
    intro k
    induction k with
    | zero => intro x; simp [cumDigitProd, oddIter]
    | succ k ihk =>
      intro x
      change d x * cumDigitProd (k + 1) (oddStep x).2 =
        (d x * cumDigitProd k (oddStep x).2) * d (oddIter (k + 1) x)
      rw [ihk (oddStep x).2]
      have hiter : oddIter (k + 1) x = oddIter k (oddStep x).2 := by
        unfold oddIter; rw [Function.iterate_succ_apply]
      rw [hiter]; ring
  refine Finset.card_le_card_of_injOn (fun n =>
      let r := (phiWord K n).length
      (cumHalv (r + 1) n, oddIter (r + 1) n, revValList (r + 1) n)) ?_ ?_
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨hn1, hnX⟩, hn_odd, hr⟩, hnot1, hDlt⟩ := hn
    set r := (phiWord K n).length
    obtain ⟨hVr_lt, hVr1_ge, hD_eq⟩ := phiWord_crossing_spec K hK1 n hn_odd hr
    change cumHalv r n < K at hVr_lt
    change K ≤ cumHalv (r + 1) n at hVr1_ge
    change wordDigitProd (clsIdx n) (phiWord K n) = cumDigitProd r n at hD_eq
    have hex1 := exists_oddIter_eq_one hn_odd hr
    set m := Nat.find hex1
    have hm1 : oddIter m n = 1 := Nat.find_spec hex1
    have hmin : ∀ j < m, oddIter j n ≠ 1 := fun j hj => Nat.find_min hex1 hj
    have hVm_ge : K ≤ cumHalv m n := by
      by_contra hlt; exact hnot1 ⟨m, hm1, by omega⟩
    have hcum_mono : ∀ a b, a ≤ b → cumHalv a n ≤ cumHalv b n := by
      intro a b hab
      induction b with
      | zero =>
        have : a = 0 := by omega
        subst this; exact le_rfl
      | succ b ihb =>
        by_cases h : a = b + 1
        · subst h; exact le_rfl
        · have hle := ihb (by omega)
          have hst := hcum_step b n
          omega
    have hr_lt_m : r < m := by
      by_contra hge
      have := hcum_mono m r (by omega); omega
    have hr1_le_K : r + 1 ≤ K := by have := hr_le_Vr r n hn_odd; omega
    have hprod_le : ∏ j ∈ Finset.range (r + 1),
          (1 + 1 / ((d (oddIter j n) : ℝ) * (oddIter j n : ℝ))) ≤
        Real.sqrt ((K : ℝ) + 1) := by
      let img : Finset ℕ := (Finset.range (r + 1)).image (fun j => oddIter j n)
      have hinj : Set.InjOn (fun j => oddIter j n) (Finset.range (r + 1) : Set ℕ) := by
        intro i hi j hj heq
        simp only [Finset.mem_coe, Finset.mem_range] at hi hj
        exact oddIter_inj_before_stop hm1 hmin i j (by omega) (by omega) heq
      have hle1 : ∏ j ∈ Finset.range (r + 1),
            (1 + 1 / ((d (oddIter j n) : ℝ) * (oddIter j n : ℝ))) ≤
          ∏ x ∈ img, (1 + 1 / (x : ℝ)) := by
        dsimp only [img]
        rw [Finset.prod_image (fun a ha b hb h => hinj ha hb h)]
        refine finset_prod_le_prod_nonneg (fun _ _ => by positivity) fun j hj => ?_
        simp only [Finset.mem_range] at hj
        obtain ⟨_, _, habc_j⟩ := oddIter_props j n hn_odd hr
        have hdj : 1 ≤ d (oddIter j n) := by
          rcases habc_j.2.2 with h | h | h <;> (unfold d; omega)
        have hxj : 0 < oddIter j n := habc_j.1
        have hmul : (oddIter j n : ℝ) ≤ (d (oddIter j n) : ℝ) * (oddIter j n : ℝ) := by
          have : oddIter j n ≤ d (oddIter j n) * oddIter j n := Nat.le_mul_of_pos_left _ hdj
          exact_mod_cast this
        have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
          (by exact_mod_cast hxj) hmul
        linarith
      have himg_card : img.card ≤ K := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_range]; exact hr1_le_K
      have himg_odd : ∀ x ∈ img, x % 2 = 1 ∧ 15 ≤ x := by
        intro x hx
        simp only [img, Finset.mem_image, Finset.mem_range] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        obtain ⟨hodd_j, _, habc_j⟩ := oddIter_props j n hn_odd hr
        have hne1 : oddIter j n ≠ 1 := hmin j (by omega)
        refine ⟨hodd_j, ?_⟩
        rcases habc_j.2.2 with h | h | h <;> omega
      exact hle1.trans (prod_one_add_inv_le_sqrt himg_card himg_odd)
    set L := cumHalv (r + 1) n
    set o := oddIter (r + 1) n
    set l := revValList (r + 1) n
    obtain ⟨hmem_bp, hend_bp⟩ := backPaths_mem_revValList (r + 1) n hn_odd hr
    obtain ⟨ho_odd, ho_reach, ho_abc⟩ := oddIter_props (r + 1) n hn_odd hr
    have hcross : (2 : ℝ) ^ L * (o : ℝ) ≤
        Real.sqrt ((K : ℝ) + 1) * (X : ℝ) * ((backEnd o l).2 : ℝ) := by
      rw [hend_bp, traj_prod_identity (r + 1) n hn_odd hr]
      have hnX_R : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast hnX
      calc (cumDigitProd (r + 1) n : ℝ) * (n : ℝ) *
            ∏ j ∈ Finset.range (r + 1),
              (1 + 1 / ((d (oddIter j n) : ℝ) * (oddIter j n : ℝ)))
          ≤ (cumDigitProd (r + 1) n : ℝ) * (X : ℝ) * Real.sqrt ((K : ℝ) + 1) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hnX_R (Nat.cast_nonneg _))
              hprod_le (Finset.prod_nonneg fun _ _ => by positivity) (by positivity)
        _ = Real.sqrt ((K : ℝ) + 1) * (X : ℝ) * (cumDigitProd (r + 1) n : ℝ) := by ring
    have hDfull_le : (cumDigitProd (r + 1) n : ℝ) ≤ 7 * (2 : ℝ) ^ (deltaParam * (K : ℝ)) := by
      rw [hsplit_D r n, Nat.cast_mul]
      have hdp_r : (d (oddIter r n) : ℝ) ≤ 7 := by
        obtain ⟨_, _, habc_r⟩ := oddIter_props r n hn_odd hr
        have : d (oddIter r n) ≤ 7 := by
          rcases habc_r.2.2 with h | h | h <;> (unfold d; omega)
        exact_mod_cast this
      rw [hD_eq] at hDlt
      have h1 := mul_le_mul hDlt.le hdp_r (Nat.cast_nonneg _) (by positivity)
      linarith
    have ho_le_YL : (o : ℝ) ≤ crossingYL X K L := by
      unfold crossingYL
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ L)]
      rw [hend_bp] at hcross
      have h1 : Real.sqrt ((K : ℝ) + 1) * (X : ℝ) * (cumDigitProd (r + 1) n : ℝ) ≤
          Real.sqrt ((K : ℝ) + 1) * (X : ℝ) * (7 * (2 : ℝ) ^ (deltaParam * (K : ℝ))) :=
        mul_le_mul_of_nonneg_left hDfull_le (by positivity)
      linarith
    have hL_le_Lmax : L ≤ Lmax := by
      by_contra hgt
      have hlt1 := hYL_lt1 L (by omega)
      have ho1 : (1 : ℝ) ≤ (o : ℝ) := by exact_mod_cast ho_abc.1
      linarith
    have ho_floor : o ≤ Nat.floor (crossingYL X K L) := Nat.le_floor ho_le_YL
    simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter,
      Finset.mem_image]
    exact ⟨L, ⟨hVr1_ge, hL_le_Lmax⟩, o, ⟨⟨ho_abc.1, ho_floor⟩, ho_odd, ho_reach⟩,
      l, ⟨hmem_bp, hcross⟩, rfl⟩
  · intro a ha b hb hEq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
    obtain ⟨⟨_, ha_odd, hra⟩, _⟩ := ha
    obtain ⟨⟨_, hb_odd, hrb⟩, _⟩ := hb
    simp only [Prod.mk.injEq] at hEq
    obtain ⟨_, ho_eq, hl_eq⟩ := hEq
    have hea := (backPaths_mem_revValList ((phiWord K a).length + 1) a ha_odd hra).2
    have heb := (backPaths_mem_revValList ((phiWord K b).length + 1) b hb_odd hrb).2
    have h1 : (backEnd (oddIter ((phiWord K a).length + 1) a)
        (revValList ((phiWord K a).length + 1) a)).1 =
        (backEnd (oddIter ((phiWord K b).length + 1) b)
        (revValList ((phiWord K b).length + 1) b)).1 := by rw [ho_eq, hl_eq]
    rw [hea, heb] at h1
    exact h1

open Classical in
private lemma case3_card_bound (X K : ℕ) (C : ℝ) (hX : 1 ≤ X) (hK1 : 1 ≤ K)
    (h2Km1 : 2 ^ (K - 1) ≤ X) (hX2K : X < 2 ^ K) (hC : 0 < C)
    (ih : ∀ t < X, 1 ≤ t → (N1 t : ℝ) ≤ C * (t : ℝ) ^ betaPrime)
    (hYstep : 14 * (((K : ℝ) + 1) * ((2 : ℝ) ^ (-(495 : ℝ) / 1000)) ^ K) < 1)
    (hK3_small : (226730 * (betaPrime / (betaPrime - sPVal)) *
        (7 : ℝ) ^ (betaPrime - sPVal) * (2 : ℝ) ^ betaPrime /
        (1 - (aPVal * (2 : ℝ) ^ betaPrime)⁻¹)) *
      (((K : ℝ) + 1) *
        ((2 : ℝ) ^ (-(betaPrime - ((27 : ℝ) / 55 + deltaParam * (betaPrime - sPVal))))) ^ K) <
      1 / 2) :
    ((((Finset.Icc 1 X).filter (fun n => n % 2 = 1 ∧ Reaches f n 1)).filter
        (inCase3 K)).card : ℝ) ≤
      (1 / 2 : ℝ) * C * (X : ℝ) ^ betaPrime := by
  have haP_pos : 0 < aPVal := by norm_num [aPVal]
  have h2bp : (1 : ℝ) < aPVal * (2 : ℝ) ^ betaPrime := by
    have h1 := inv_aP_le_two_rpow
    have hpow : (2 : ℝ) ^ ((27 : ℝ) / 55) < (2 : ℝ) ^ betaPrime :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num [betaPrime])
    have h2 : 1 / aPVal < (2 : ℝ) ^ betaPrime := lt_of_le_of_lt h1 hpow
    rwa [div_lt_iff₀ haP_pos, mul_comm] at h2
  set qL : ℝ := (aPVal * (2 : ℝ) ^ betaPrime)⁻¹
  have hqL_pos : 0 < qL := inv_pos.mpr (by linarith)
  have hqL_lt1 : qL < 1 := inv_lt_one_of_one_lt₀ h2bp
  have h1qL : 0 < 1 - qL := by linarith
  set gap3 : ℝ := betaPrime - ((27 : ℝ) / 55 + deltaParam * (betaPrime - sPVal))
  set K3 : ℝ := 226730 * (betaPrime / (betaPrime - sPVal)) *
    (7 : ℝ) ^ (betaPrime - sPVal) * (2 : ℝ) ^ betaPrime / (1 - qL)
  have hK3_pos : 0 < K3 := by
    have : 0 < betaPrime - sPVal := by norm_num [betaPrime, sPVal]
    have : 0 < betaPrime := by norm_num [betaPrime]
    positivity
  have hYK_lt : crossingYL X K K < (X : ℝ) := by
    have hsqrt_le : Real.sqrt ((K : ℝ) + 1) ≤ (K : ℝ) + 1 := by
      calc Real.sqrt ((K : ℝ) + 1) ≤ Real.sqrt (((K : ℝ) + 1) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [Nat.cast_nonneg (α := ℝ) K])
        _ = (K : ℝ) + 1 := Real.sqrt_sq (by positivity)
    have h2Km1_R : (2 : ℝ) ^ (K - 1) ≤ (X : ℝ) := by exact_mod_cast h2Km1
    have hX_lt_R : (X : ℝ) < (2 : ℝ) ^ K := by exact_mod_cast hX2K
    have hYL_bound : crossingYL X K K ≤ 7 * ((K : ℝ) + 1) * (2 : ℝ) ^ (deltaParam * (K : ℝ)) := by
      unfold crossingYL
      have hXdiv : (X : ℝ) / (2 : ℝ) ^ K ≤ 1 := (div_le_one (by positivity)).mpr hX_lt_R.le
      calc 7 * Real.sqrt ((K : ℝ) + 1) * (X : ℝ) * (2 : ℝ) ^ (deltaParam * (K : ℝ)) / (2 : ℝ) ^ K
          = 7 * Real.sqrt ((K : ℝ) + 1) * (2 : ℝ) ^ (deltaParam * (K : ℝ)) * ((X : ℝ) / (2 : ℝ) ^ K) := by ring
        _ ≤ 7 * ((K : ℝ) + 1) * (2 : ℝ) ^ (deltaParam * (K : ℝ)) * 1 := by
            refine mul_le_mul ?_ hXdiv (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsqrt_le (by norm_num)) (by positivity)
        _ = 7 * ((K : ℝ) + 1) * (2 : ℝ) ^ (deltaParam * (K : ℝ)) := by ring
    have hpow_split : (2 : ℝ) ^ (deltaParam * (K : ℝ)) =
        ((2 : ℝ) ^ (-(495 : ℝ) / 1000)) ^ K * (2 : ℝ) ^ K := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num),
          ← Real.rpow_natCast 2 K, ← Real.rpow_add (by norm_num)]
      congr 1; unfold deltaParam; ring
    have h2K_eq : (2 : ℝ) ^ K = 2 * (2 : ℝ) ^ (K - 1) := by
      have : K = (K - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    have hlt2Km1 : 7 * ((K : ℝ) + 1) * (2 : ℝ) ^ (deltaParam * (K : ℝ)) < (2 : ℝ) ^ (K - 1) := by
      rw [hpow_split, h2K_eq]
      have hmul : (14 * (((K : ℝ) + 1) * ((2 : ℝ) ^ (-(495 : ℝ) / 1000)) ^ K)) * (2 : ℝ) ^ (K - 1) <
          1 * (2 : ℝ) ^ (K - 1) :=
        mul_lt_mul_of_pos_right hYstep (by positivity)
      linarith
    linarith
  let Lmax : ℕ := K + Nat.log 2 X + 2
  have hYL_lt1 : ∀ L : ℕ, Lmax < L → crossingYL X K L < 1 := by
    intro L hL
    have h1 : crossingYL X K L ≤ crossingYL X K K / (2 : ℝ) ^ (L - K) := by
      unfold crossingYL
      rw [div_div, ← pow_add, Nat.add_sub_of_le (by omega)]
    have h2 : (X : ℝ) ≤ (2 : ℝ) ^ (L - K) := by
      have hnat : X < 2 ^ (L - K) := by
        calc X < 2 ^ (Nat.log 2 X + 1) := Nat.lt_pow_succ_log_self (by norm_num) X
          _ ≤ 2 ^ (L - K) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast hnat.le
    have h3 : crossingYL X K K / (2 : ℝ) ^ (L - K) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    linarith
  let T3 : Finset (ℕ × ℕ × List ℕ) :=
    (Finset.Icc K Lmax).biUnion fun L =>
      ((Finset.Icc 1 (Nat.floor (crossingYL X K L))).filter
        (fun o => o % 2 = 1 ∧ Reaches f o 1)).biUnion fun o =>
        ((backPaths o L).filter fun l =>
          (2 : ℝ) ^ L * (o : ℝ) ≤
            Real.sqrt ((K : ℝ) + 1) * (X : ℝ) * ((backEnd o l).2 : ℝ)).image
          (fun l => (L, o, l))
  have hcard3 := case3_inj_bound X K Lmax hK1 hYL_lt1
  have hT3_le : (T3.card : ℝ) ≤
      ∑ L ∈ Finset.Icc K Lmax,
        (226730 * (betaPrime / (betaPrime - sPVal)) * C *
          (7 : ℝ) ^ (betaPrime - sPVal) *
          ((K : ℝ) + 1) ^ (betaPrime / 2) *
          (X : ℝ) ^ betaPrime *
          (2 : ℝ) ^ ((betaPrime - sPVal) * deltaParam * (K : ℝ))) *
          (1 / (aPVal * (2 : ℝ) ^ betaPrime)) ^ L := by
    have hcard_sum : T3.card ≤ ∑ L ∈ Finset.Icc K Lmax,
        ∑ o ∈ (Finset.Icc 1 (Nat.floor (crossingYL X K L))).filter
          (fun o => o % 2 = 1 ∧ Reaches f o 1),
          ((backPaths o L).filter fun l =>
            (2 : ℝ) ^ L * (o : ℝ) ≤
              Real.sqrt ((K : ℝ) + 1) * (X : ℝ) * ((backEnd o l).2 : ℝ)).card := by
      unfold T3
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun L _ => ?_)
      refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun o _ => Finset.card_image_le)
    have hcast : (T3.card : ℝ) ≤ ∑ L ∈ Finset.Icc K Lmax,
        ∑ o ∈ (Finset.Icc 1 (Nat.floor (crossingYL X K L))).filter
          (fun o => o % 2 = 1 ∧ Reaches f o 1),
          (((backPaths o L).filter fun l =>
            (2 : ℝ) ^ L * (o : ℝ) ≤
              Real.sqrt ((K : ℝ) + 1) * (X : ℝ) * ((backEnd o l).2 : ℝ)).card : ℝ) := by
      exact_mod_cast hcard_sum
    refine hcast.trans (Finset.sum_le_sum fun L hL => ?_)
    simp only [Finset.mem_Icc] at hL
    by_cases hM0 : Nat.floor (crossingYL X K L) = 0
    · have hemp : Finset.Icc 1 (Nat.floor (crossingYL X K L)) = ∅ := by rw [hM0]; simp
      rw [hemp, Finset.filter_empty, Finset.sum_empty]
      have : 0 < betaPrime - sPVal := by norm_num [betaPrime, sPVal]
      have : 0 < betaPrime := by norm_num [betaPrime]
      positivity
    · have hM1 : 1 ≤ Nat.floor (crossingYL X K L) := Nat.pos_of_ne_zero hM0
      have hYL_le_YK : crossingYL X K L ≤ crossingYL X K K := by
        unfold crossingYL
        exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_right₀ (by norm_num) hL.1)
      have hM_lt_X : Nat.floor (crossingYL X K L) < X := by
        have h1 : (Nat.floor (crossingYL X K L) : ℝ) ≤ crossingYL X K L :=
          Nat.floor_le (by unfold crossingYL; positivity)
        have h2 : (Nat.floor (crossingYL X K L) : ℝ) < (X : ℝ) :=
          lt_of_le_of_lt (h1.trans hYL_le_YK) hYK_lt
        exact_mod_cast h2
      have ho_bound : ∀ o ∈ (Finset.Icc 1 (Nat.floor (crossingYL X K L))).filter
            (fun o => o % 2 = 1 ∧ Reaches f o 1),
          (((backPaths o L).filter fun l =>
            (2 : ℝ) ^ L * (o : ℝ) ≤
              Real.sqrt ((K : ℝ) + 1) * (X : ℝ) * ((backEnd o l).2 : ℝ)).card : ℝ) ≤
          (226730 * (Real.sqrt ((K : ℝ) + 1) * (X : ℝ)) ^ sPVal *
            (1 / (aPVal * (2 : ℝ) ^ sPVal)) ^ L) * (o : ℝ) ^ (-sPVal) := by
        intro o ho
        simp only [Finset.mem_filter, Finset.mem_Icc] at ho
        obtain ⟨⟨ho1, _⟩, ho_odd, ho_reach⟩ := ho
        have ho_pos : (0 : ℝ) < (o : ℝ) := by exact_mod_cast (by omega : 0 < o)
        have ho_abc : InABC15 o := (oddIter_props 0 o ho_odd ho_reach).2.2
        have hmarkov : (((backPaths o L).filter fun l =>
              (2 : ℝ) ^ L * (o : ℝ) ≤
                Real.sqrt ((K : ℝ) + 1) * (X : ℝ) * ((backEnd o l).2 : ℝ)).card : ℝ) ≤
            ((Real.sqrt ((K : ℝ) + 1) * (X : ℝ)) / ((2 : ℝ) ^ L * (o : ℝ))) ^ sPVal *
              ∑ l ∈ backPaths o L, ((backEnd o l).2 : ℝ) ^ sPVal := by
          have hconst : (((backPaths o L).filter fun l =>
                (2 : ℝ) ^ L * (o : ℝ) ≤
                  Real.sqrt ((K : ℝ) + 1) * (X : ℝ) * ((backEnd o l).2 : ℝ)).card : ℝ) =
              ∑ _l ∈ (backPaths o L).filter (fun l =>
                (2 : ℝ) ^ L * (o : ℝ) ≤
                  Real.sqrt ((K : ℝ) + 1) * (X : ℝ) * ((backEnd o l).2 : ℝ)), (1 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          rw [hconst, Finset.mul_sum]
          refine (Finset.sum_le_sum fun l hl => ?_).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity)
          have hle := (Finset.mem_filter.mp hl).2
          have hdiv1 : (1 : ℝ) ≤
              (Real.sqrt ((K : ℝ) + 1) * (X : ℝ) / ((2 : ℝ) ^ L * (o : ℝ))) *
                ((backEnd o l).2 : ℝ) := by
            rw [div_mul_eq_mul_div, one_le_div (by positivity)]; exact hle
          have hpow1 : (1 : ℝ) ≤
              ((Real.sqrt ((K : ℝ) + 1) * (X : ℝ) / ((2 : ℝ) ^ L * (o : ℝ))) *
                ((backEnd o l).2 : ℝ)) ^ sPVal :=
            Real.one_le_rpow hdiv1 (by norm_num [sPVal])
          rwa [Real.mul_rpow (by positivity) (Nat.cast_nonneg _)] at hpow1
        have hpair := pair_backPaths_bound L o ho_abc
        have hmul := hmarkov.trans (mul_le_mul_of_nonneg_left hpair (by positivity))
        refine hmul.trans_eq ?_
        rw [Real.div_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) ho_pos.le,
            ← Real.rpow_natCast 2 L, ← Real.rpow_mul (by norm_num),
            mul_comm (L : ℝ) sPVal, Real.rpow_mul (by norm_num), Real.rpow_natCast,
            Real.rpow_neg ho_pos.le, one_div, one_div, mul_inv, mul_pow, inv_pow, inv_pow]
        ring
      have hsum_o := Finset.sum_le_sum ho_bound
      rw [← Finset.mul_sum] at hsum_o
      have hsbp := sum_inv_rpow_le_of_count_le (s := sPVal) (b := betaPrime) (C := C)
        (by norm_num [sPVal]) (by norm_num [sPVal, betaPrime]) (by norm_num [betaPrime])
        hC.le hM1 (fun t ht1 htM => ih t (lt_of_le_of_lt htM hM_lt_X) ht1)
      have hM_le_YL : ((Nat.floor (crossingYL X K L) : ℕ) : ℝ) ^ (betaPrime - sPVal) ≤
          (crossingYL X K L) ^ (betaPrime - sPVal) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by unfold crossingYL; positivity))
          (by norm_num [betaPrime, sPVal])
      have hstep1 := hsum_o.trans (mul_le_mul_of_nonneg_left
        (hsbp.trans (mul_le_mul_of_nonneg_left hM_le_YL
          (by
            have : 0 < betaPrime - sPVal := by norm_num [betaPrime, sPVal]
            have : 0 < betaPrime := by norm_num [betaPrime]
            positivity)))
        (by positivity))
      refine hstep1.trans_eq ?_
      have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
      have hK1pos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
      have hsqrt_pow : ∀ r : ℝ, (Real.sqrt ((K : ℝ) + 1)) ^ r =
          ((K : ℝ) + 1) ^ (r / 2) := fun r => by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hK1pos.le]; congr 1; ring
      have hYL_rpow : (crossingYL X K L) ^ (betaPrime - sPVal) =
          (7 : ℝ) ^ (betaPrime - sPVal) * ((K : ℝ) + 1) ^ ((betaPrime - sPVal) / 2) *
          (X : ℝ) ^ (betaPrime - sPVal) *
          (2 : ℝ) ^ ((betaPrime - sPVal) * deltaParam * (K : ℝ)) *
          (((2 : ℝ) ^ (betaPrime - sPVal)) ^ L)⁻¹ := by
        unfold crossingYL
        have hpowK : ((2 : ℝ) ^ (deltaParam * (K : ℝ))) ^ (betaPrime - sPVal) =
            (2 : ℝ) ^ ((betaPrime - sPVal) * deltaParam * (K : ℝ)) := by
          rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
        have hdenL : ((2 : ℝ) ^ L) ^ (betaPrime - sPVal) =
            ((2 : ℝ) ^ (betaPrime - sPVal)) ^ L := by
          rw [← Real.rpow_natCast 2 L, ← Real.rpow_mul (by norm_num),
              mul_comm (L : ℝ) (betaPrime - sPVal), Real.rpow_mul (by norm_num),
              Real.rpow_natCast]
        rw [Real.div_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by norm_num) (by positivity),
            hsqrt_pow, hpowK, hdenL, div_eq_mul_inv]
      have h1_rpow : (Real.sqrt ((K : ℝ) + 1) * (X : ℝ)) ^ sPVal =
          ((K : ℝ) + 1) ^ (sPVal / 2) * (X : ℝ) ^ sPVal := by
        rw [Real.mul_rpow (by positivity) hXpos.le, hsqrt_pow]
      rw [h1_rpow, hYL_rpow]
      have hK_comb : ((K : ℝ) + 1) ^ (sPVal / 2) * ((K : ℝ) + 1) ^ ((betaPrime - sPVal) / 2) =
          ((K : ℝ) + 1) ^ (betaPrime / 2) := by
        rw [← Real.rpow_add hK1pos]; congr 1; ring
      have hX_comb : (X : ℝ) ^ sPVal * (X : ℝ) ^ (betaPrime - sPVal) = (X : ℝ) ^ betaPrime := by
        rw [← Real.rpow_add hXpos]; congr 1; ring
      have hL_comb : (1 / (aPVal * (2 : ℝ) ^ sPVal)) ^ L *
          (((2 : ℝ) ^ (betaPrime - sPVal)) ^ L)⁻¹ =
          (1 / (aPVal * (2 : ℝ) ^ betaPrime)) ^ L := by
        rw [one_div, one_div, ← inv_pow, ← mul_pow, ← mul_inv, mul_assoc,
            ← Real.rpow_add (by norm_num), add_sub_cancel]
      calc 226730 * (((K : ℝ) + 1) ^ (sPVal / 2) * (X : ℝ) ^ sPVal) *
            (1 / (aPVal * (2 : ℝ) ^ sPVal)) ^ L *
            (betaPrime / (betaPrime - sPVal) * C *
              ((7 : ℝ) ^ (betaPrime - sPVal) * ((K : ℝ) + 1) ^ ((betaPrime - sPVal) / 2) *
                (X : ℝ) ^ (betaPrime - sPVal) *
                (2 : ℝ) ^ ((betaPrime - sPVal) * deltaParam * (K : ℝ)) *
                (((2 : ℝ) ^ (betaPrime - sPVal)) ^ L)⁻¹))
          = 226730 * (betaPrime / (betaPrime - sPVal)) * C * (7 : ℝ) ^ (betaPrime - sPVal) *
              (((K : ℝ) + 1) ^ (sPVal / 2) * ((K : ℝ) + 1) ^ ((betaPrime - sPVal) / 2)) *
              ((X : ℝ) ^ sPVal * (X : ℝ) ^ (betaPrime - sPVal)) *
              (2 : ℝ) ^ ((betaPrime - sPVal) * deltaParam * (K : ℝ)) *
              ((1 / (aPVal * (2 : ℝ) ^ sPVal)) ^ L *
                (((2 : ℝ) ^ (betaPrime - sPVal)) ^ L)⁻¹) := by ring
        _ = _ := by rw [hK_comb, hX_comb, hL_comb]
  have hgeomL : ∑ L ∈ Finset.Icc K Lmax, qL ^ L ≤ qL ^ K / (1 - qL) := by
    have hsub : Finset.Icc K Lmax ⊆ (Finset.range (Lmax + 1)).image (fun j => K + j) := by
      intro L hL; simp only [Finset.mem_Icc] at hL
      simp only [Finset.mem_image, Finset.mem_range]
      exact ⟨L - K, by omega, by omega⟩
    have h1 : ∑ L ∈ Finset.Icc K Lmax, qL ^ L ≤
        ∑ L ∈ (Finset.range (Lmax + 1)).image (fun j => K + j), qL ^ L :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    have himg : ∑ L ∈ (Finset.range (Lmax + 1)).image (fun j => K + j), qL ^ L =
        qL ^ K * ∑ j ∈ Finset.range (Lmax + 1), qL ^ j := by
      rw [Finset.sum_image (fun x _ y _ h => by omega), Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => pow_add qL K j
    have hgs : ∑ j ∈ Finset.range (Lmax + 1), qL ^ j ≤ 1 / (1 - qL) := by
      rw [geom_sum_eq (ne_of_lt hqL_lt1)]
      have h1' : qL ^ (Lmax + 1) - 1 = -(1 - qL ^ (Lmax + 1)) := by ring
      have h2' : qL - 1 = -(1 - qL) := by ring
      rw [h1', h2', neg_div_neg_eq]
      exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hqL_pos.le (Lmax + 1)]) h1qL.le
    calc ∑ L ∈ Finset.Icc K Lmax, qL ^ L ≤ qL ^ K * (1 / (1 - qL)) :=
          (h1.trans_eq himg).trans (mul_le_mul_of_nonneg_left hgs (by positivity))
      _ = qL ^ K / (1 - qL) := by ring
  rw [← Finset.mul_sum] at hT3_le
  have hqL_eq : (1 / (aPVal * (2 : ℝ) ^ betaPrime)) = qL := one_div _
  simp_rw [hqL_eq] at hT3_le
  have h3_1 : ((((Finset.Icc 1 X).filter (fun n => n % 2 = 1 ∧ Reaches f n 1)).filter
        (inCase3 K)).card : ℝ) ≤
      (226730 * (betaPrime / (betaPrime - sPVal)) * C * (7 : ℝ) ^ (betaPrime - sPVal) *
        ((K : ℝ) + 1) ^ (betaPrime / 2) * (X : ℝ) ^ betaPrime *
        (2 : ℝ) ^ ((betaPrime - sPVal) * deltaParam * (K : ℝ))) * (qL ^ K / (1 - qL)) := by
    have hpre_nn : 0 ≤ 226730 * (betaPrime / (betaPrime - sPVal)) * C *
        (7 : ℝ) ^ (betaPrime - sPVal) * ((K : ℝ) + 1) ^ (betaPrime / 2) *
        (X : ℝ) ^ betaPrime * (2 : ℝ) ^ ((betaPrime - sPVal) * deltaParam * (K : ℝ)) := by
      have : 0 < betaPrime - sPVal := by norm_num [betaPrime, sPVal]
      have : 0 < betaPrime := by norm_num [betaPrime]
      positivity
    exact (Nat.cast_le.mpr hcard3).trans
      (hT3_le.trans (mul_le_mul_of_nonneg_left hgeomL hpre_nn))
  have hqL_pow : (2 : ℝ) ^ ((betaPrime - sPVal) * deltaParam * (K : ℝ)) * qL ^ K ≤
      ((2 : ℝ) ^ (-gap3)) ^ K := by
    have hqL_le : qL ≤ (2 : ℝ) ^ ((27 : ℝ) / 55 - betaPrime) := by
      unfold qL
      rw [mul_inv, Real.rpow_sub (by norm_num), div_eq_mul_inv, ← one_div]
      exact mul_le_mul_of_nonneg_right inv_aP_le_two_rpow (by positivity)
    have hpow1 : qL ^ K ≤ (2 : ℝ) ^ (((27 : ℝ) / 55 - betaPrime) * (K : ℝ)) := by
      calc qL ^ K ≤ ((2 : ℝ) ^ ((27 : ℝ) / 55 - betaPrime)) ^ K :=
            pow_le_pow_left₀ hqL_pos.le hqL_le K
        _ = (2 : ℝ) ^ (((27 : ℝ) / 55 - betaPrime) * (K : ℝ)) := by
            rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num)]
    calc (2 : ℝ) ^ ((betaPrime - sPVal) * deltaParam * (K : ℝ)) * qL ^ K
        ≤ (2 : ℝ) ^ ((betaPrime - sPVal) * deltaParam * (K : ℝ)) *
            (2 : ℝ) ^ (((27 : ℝ) / 55 - betaPrime) * (K : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow1 (by positivity)
      _ = (2 : ℝ) ^ ((-gap3) * (K : ℝ)) := by
          rw [← Real.rpow_add (by norm_num)]; congr 1; unfold gap3; ring
      _ = ((2 : ℝ) ^ (-gap3)) ^ K := by
          rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have hKpow_le : ((K : ℝ) + 1) ^ (betaPrime / 2) ≤ (K : ℝ) + 1 := by
    calc ((K : ℝ) + 1) ^ (betaPrime / 2) ≤ ((K : ℝ) + 1) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) K])
            (by norm_num [betaPrime])
      _ = (K : ℝ) + 1 := Real.rpow_one _
  have h2bp_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ betaPrime :=
    Real.one_le_rpow (by norm_num) (by norm_num [betaPrime])
  have h3_2 : ((((Finset.Icc 1 X).filter (fun n => n % 2 = 1 ∧ Reaches f n 1)).filter
        (inCase3 K)).card : ℝ) ≤
      (K3 * (((K : ℝ) + 1) * ((2 : ℝ) ^ (-gap3)) ^ K)) * (C * (X : ℝ) ^ betaPrime) := by
    have hfactor : (226730 * (betaPrime / (betaPrime - sPVal)) * C *
          (7 : ℝ) ^ (betaPrime - sPVal) * ((K : ℝ) + 1) ^ (betaPrime / 2) *
          (X : ℝ) ^ betaPrime * (2 : ℝ) ^ ((betaPrime - sPVal) * deltaParam * (K : ℝ))) *
          (qL ^ K / (1 - qL)) =
        (226730 * (betaPrime / (betaPrime - sPVal)) * (7 : ℝ) ^ (betaPrime - sPVal) / (1 - qL)) *
          (((K : ℝ) + 1) ^ (betaPrime / 2) *
            ((2 : ℝ) ^ ((betaPrime - sPVal) * deltaParam * (K : ℝ)) * qL ^ K)) *
          (C * (X : ℝ) ^ betaPrime) := by ring
    rw [hfactor] at h3_1
    have hcoef_le : 226730 * (betaPrime / (betaPrime - sPVal)) *
          (7 : ℝ) ^ (betaPrime - sPVal) / (1 - qL) ≤ K3 := by
      unfold K3
      have hnum_nn : 0 ≤ 226730 * (betaPrime / (betaPrime - sPVal)) *
          (7 : ℝ) ^ (betaPrime - sPVal) := by
        have : 0 < betaPrime - sPVal := by norm_num [betaPrime, sPVal]
        have : 0 < betaPrime := by norm_num [betaPrime]
        positivity
      apply div_le_div_of_nonneg_right _ h1qL.le
      nlinarith
    have hmid_le : ((K : ℝ) + 1) ^ (betaPrime / 2) *
          ((2 : ℝ) ^ ((betaPrime - sPVal) * deltaParam * (K : ℝ)) * qL ^ K) ≤
        ((K : ℝ) + 1) * ((2 : ℝ) ^ (-gap3)) ^ K :=
      mul_le_mul hKpow_le hqL_pow (by positivity) (by positivity)
    have hprod_le := mul_le_mul hcoef_le hmid_le (by positivity) hK3_pos.le
    exact h3_1.trans (mul_le_mul_of_nonneg_right hprod_le (by positivity))
  calc ((((Finset.Icc 1 X).filter (fun n => n % 2 = 1 ∧ Reaches f n 1)).filter
        (inCase3 K)).card : ℝ)
      ≤ (K3 * (((K : ℝ) + 1) * ((2 : ℝ) ^ (-gap3)) ^ K)) * (C * (X : ℝ) ^ betaPrime) := h3_2
    _ ≤ (1 / 2 : ℝ) * (C * (X : ℝ) ^ betaPrime) :=
        mul_le_mul_of_nonneg_right hK3_small.le (by positivity)
    _ = (1 / 2 : ℝ) * C * (X : ℝ) ^ betaPrime := by ring

/-- Main Theorem (`thm:basin-sharp`, Part 1b): there exists `C > 0` such that for every integer
    `X ≥ 1`, `N_1(X) ≤ C * X^{0.6245}`. -/
theorem thm_basin1_upper_sharp :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X → (N1 X : ℝ) ≤ C * (X : ℝ) ^ betaPrime := by
  classical
  let K1 : ℝ := 30
  let K2 : ℝ := (hFVec 0 + hFVec 1 + hFVec 2) / (1 - aFVal)
  have hK2_pos : 0 < K2 := by
    have : 0 < hFVec 0 + hFVec 1 + hFVec 2 := by
      linarith [hFVec_ge_one 0, hFVec_ge_one 1, hFVec_ge_one 2]
    have : 0 < 1 - aFVal := by norm_num [aFVal]
    positivity
  let qL : ℝ := (aPVal * (2 : ℝ) ^ betaPrime)⁻¹
  let K3 : ℝ := 226730 * (betaPrime / (betaPrime - sPVal)) *
    (7 : ℝ) ^ (betaPrime - sPVal) * (2 : ℝ) ^ betaPrime / (1 - qL)
  let gap3 : ℝ := betaPrime - ((27 : ℝ) / 55 + deltaParam * (betaPrime - sPVal))
  have hgap3_pos : 0 < gap3 := by norm_num [gap3, betaPrime, deltaParam, sPVal]
  have hrY_lt1 : (2 : ℝ) ^ (-(495 : ℝ) / 1000) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have htendY := (tendsto_add_one_mul_pow_zero (r := (2 : ℝ) ^ (-(495 : ℝ) / 1000))
    (by positivity) hrY_lt1).const_mul (14 : ℝ)
  simp only [mul_zero] at htendY
  obtain ⟨KY, hKY⟩ := (htendY.eventually (gt_mem_nhds zero_lt_one)).exists_forall_of_atTop
  have hr3_lt1 : (2 : ℝ) ^ (-gap3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have htend3 := (tendsto_add_one_mul_pow_zero (r := (2 : ℝ) ^ (-gap3))
    (by positivity) hr3_lt1).const_mul K3
  simp only [mul_zero] at htend3
  obtain ⟨K3cut, hK3cut⟩ :=
    (htend3.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists_forall_of_atTop
  let K0 : ℕ := max 2 (max KY K3cut)
  let X0 : ℕ := 2 ^ K0
  let C : ℝ := max (2 * (K1 + K2) * (2 : ℝ) ^ betaPrime) (max 1 (X0 : ℝ))
  have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left 1 _) (le_max_right _ _))
  refine ⟨C, hC_pos, fun X hX => ?_⟩
  induction X using Nat.strong_induction_on with
  | h X ih =>
    by_cases hsmall : X < X0
    · have hN1_le_X : N1 X ≤ X := by
        unfold N1
        calc ((Finset.Icc 1 X).filter _).card ≤ (Finset.Icc 1 X).card := Finset.card_filter_le _ _
          _ = X := by simp
      have hX_le_C : (X : ℝ) ≤ C := by
        have h1 : (X : ℝ) ≤ (X0 : ℝ) := by exact_mod_cast hsmall.le
        exact h1.trans (le_trans (le_max_right 1 _) (le_max_right _ _))
      have hXpow : (1 : ℝ) ≤ (X : ℝ) ^ betaPrime :=
        Real.one_le_rpow (by exact_mod_cast hX) (by norm_num [betaPrime])
      calc (N1 X : ℝ) ≤ (X : ℝ) := by exact_mod_cast hN1_le_X
        _ ≤ C := hX_le_C
        _ = C * 1 := by ring
        _ ≤ C * (X : ℝ) ^ betaPrime := mul_le_mul_of_nonneg_left hXpow hC_pos.le
    · have hX_ge : X0 ≤ X := by omega
      let K : ℕ := Nat.log 2 X + 1
      have hK_ge : K0 ≤ K := by
        have hlog : K0 ≤ Nat.log 2 X := (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr hX_ge
        omega
      have hK1_le : 1 ≤ K := by omega
      have h2Km1_le : 2 ^ (K - 1) ≤ X := by
        have : K - 1 = Nat.log 2 X := by omega
        rw [this]; exact Nat.pow_log_le_self 2 (by omega)
      have hX_lt_2K : X < 2 ^ K := Nat.lt_pow_succ_log_self (by norm_num) X
      have h2K_le_2X : (2 : ℝ) ^ K ≤ 2 * (X : ℝ) := by
        have hnat : 2 ^ K ≤ 2 * X := by
          have : K = (K - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ']
          omega
        exact_mod_cast hnat
      have h2K_rpow_le : (2 : ℝ) ^ (betaPrime * (K : ℝ)) ≤
          (2 : ℝ) ^ betaPrime * (X : ℝ) ^ betaPrime := by
        rw [mul_comm betaPrime (K : ℝ), Real.rpow_mul (by norm_num), Real.rpow_natCast,
            ← Real.mul_rpow (by norm_num) (Nat.cast_nonneg X)]
        exact Real.rpow_le_rpow (by positivity) h2K_le_2X (by norm_num [betaPrime])
      let S_all := (Finset.Icc 1 X).filter (fun n => n % 2 = 1 ∧ Reaches f n 1)
      let S1 := S_all.filter (inCase1 K)
      let S2 := S_all.filter (inCase2 K)
      let S3 := S_all.filter (inCase3 K)
      have hS_split : S_all.card ≤ S1.card + S2.card + S3.card := by
        have hsub : S_all ⊆ (S1 ∪ S2) ∪ S3 := by
          intro n hn
          simp only [S1, S2, S3, Finset.mem_union, Finset.mem_filter, inCase2, inCase3]
          by_cases h1 : inCase1 K n
          · left; left; exact ⟨hn, h1⟩
          · by_cases h2 : (2 : ℝ) ^ (deltaParam * (K : ℝ)) ≤
                (wordDigitProd (clsIdx n) (phiWord K n) : ℝ)
            · left; right; exact ⟨hn, h1, h2⟩
            · right; exact ⟨hn, h1, lt_of_not_ge h2⟩
        calc S_all.card ≤ ((S1 ∪ S2) ∪ S3).card := Finset.card_le_card hsub
          _ ≤ (S1 ∪ S2).card + S3.card := Finset.card_union_le _ _
          _ ≤ S1.card + S2.card + S3.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
      have hCase1 : (S1.card : ℝ) ≤ K1 * (2 : ℝ) ^ (betaPrime * (K : ℝ)) :=
        case1_card_bound X K
      have hCase2 : (S2.card : ℝ) ≤ K2 * (2 : ℝ) ^ (betaPrime * (K : ℝ)) :=
        case2_card_bound X K hK1_le hX_lt_2K
      have hYstep := hKY K (le_trans (le_max_left _ _) (le_trans (le_max_right 2 _) hK_ge))
      have hK3step := hK3cut K (le_trans (le_max_right _ _) (le_trans (le_max_right 2 _) hK_ge))
      have hCase3 : (S3.card : ℝ) ≤ (1 / 2 : ℝ) * C * (X : ℝ) ^ betaPrime :=
        case3_card_bound X K C hX hK1_le h2Km1_le hX_lt_2K hC_pos ih hYstep hK3step
      have hC_half : (K1 + K2) * (2 : ℝ) ^ betaPrime ≤ (1 / 2 : ℝ) * C := by
        have : 2 * (K1 + K2) * (2 : ℝ) ^ betaPrime ≤ C := le_max_left _ _
        linarith
      have h12 : (S1.card : ℝ) + (S2.card : ℝ) ≤ (1 / 2 : ℝ) * C * (X : ℝ) ^ betaPrime := by
        calc (S1.card : ℝ) + (S2.card : ℝ)
            ≤ (K1 + K2) * (2 : ℝ) ^ (betaPrime * (K : ℝ)) := by linarith only [hCase1, hCase2]
          _ ≤ (K1 + K2) * ((2 : ℝ) ^ betaPrime * (X : ℝ) ^ betaPrime) :=
              mul_le_mul_of_nonneg_left h2K_rpow_le (by positivity)
          _ = ((K1 + K2) * (2 : ℝ) ^ betaPrime) * (X : ℝ) ^ betaPrime := by ring
          _ ≤ ((1 / 2 : ℝ) * C) * (X : ℝ) ^ betaPrime :=
              mul_le_mul_of_nonneg_right hC_half (by positivity)
          _ = (1 / 2 : ℝ) * C * (X : ℝ) ^ betaPrime := by ring
      have hN1_eq : N1 X = S_all.card := rfl
      have hcast_split : (N1 X : ℝ) ≤ (S1.card : ℝ) + (S2.card : ℝ) + (S3.card : ℝ) := by
        rw [hN1_eq]; exact_mod_cast hS_split
      linarith only [hcast_split, h12, hCase3]

/-- Real-argument form of `thm:basin-sharp` Part 1b:
    `∃ C > 0, ∀ X : ℝ, 1 ≤ X → N_1(⌊X⌋) ≤ C * X^{0.6245}`. -/
theorem thm_basin1_upper_sharp_real :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → (N1 (Nat.floor X) : ℝ) ≤ C * X ^ betaPrime := by
  obtain ⟨C, hC, hnat⟩ := thm_basin1_upper_sharp
  refine ⟨C, hC, fun X hX => ?_⟩
  have hf1 : 1 ≤ Nat.floor X := Nat.le_floor (by exact_mod_cast hX)
  have h1 := hnat (Nat.floor X) hf1
  have hpow : ((Nat.floor X : ℕ) : ℝ) ^ betaPrime ≤ X ^ betaPrime :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) (by norm_num [betaPrime])
  exact h1.trans (mul_le_mul_of_nonneg_left hpow hC.le)

/-- Strict 2-adic/Archimedean separation against `beta = dim_H(B_1_bar)` (`thm:basin-sharp` Part 1b):
    `limsup_{X → ∞} (log N_1(X) / log X) ≤ 0.6245 < beta`. -/
theorem cor_basin1_archimedean_lt_2adic :
    Filter.limsup (fun X : ℕ => Real.log (N1 X : ℝ) / Real.log (X : ℝ)) Filter.atTop ≤ betaPrime ∧
    betaPrime < beta := by
  classical
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC, hbound⟩ := thm_basin1_upper_sharp
    have hev_le : ∀ᶠ X : ℕ in Filter.atTop,
        Real.log (N1 X : ℝ) / Real.log (X : ℝ) ≤ Real.log C / Real.log (X : ℝ) + betaPrime := by
      filter_upwards [Filter.eventually_ge_atTop 2] with X hX
      have hX_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
      have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
      have h1_mem : 1 ∈ (Finset.Icc 1 X).filter (fun n => n % 2 = 1 ∧ Reaches f n 1) := by
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨le_rfl, by omega⟩, by decide, reaches_refl f 1⟩
      have hN1_pos : (0 : ℝ) < (N1 X : ℝ) := by
        have : 1 ≤ N1 X := Finset.card_pos.mpr ⟨1, h1_mem⟩
        exact_mod_cast this
      have hup := hbound X (by omega)
      have hlog_le : Real.log (N1 X : ℝ) ≤ Real.log (C * (X : ℝ) ^ betaPrime) :=
        Real.log_le_log hN1_pos hup
      rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hX_pos _).ne',
          Real.log_rpow hX_pos] at hlog_le
      rw [div_le_iff₀ hlogX_pos]
      have hrew : (Real.log C / Real.log (X : ℝ) + betaPrime) * Real.log (X : ℝ) =
          Real.log C + betaPrime * Real.log (X : ℝ) := by
        have hne : Real.log (X : ℝ) ≠ 0 := hlogX_pos.ne'
        field_simp
      linarith
    have hev_ge0 : ∀ᶠ X : ℕ in Filter.atTop,
        (0 : ℝ) ≤ Real.log (N1 X : ℝ) / Real.log (X : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop 2] with X hX
      have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
      have h1_mem : 1 ∈ (Finset.Icc 1 X).filter (fun n => n % 2 = 1 ∧ Reaches f n 1) := by
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨le_rfl, by omega⟩, by decide, reaches_refl f 1⟩
      have hN1_ge1 : (1 : ℝ) ≤ (N1 X : ℝ) := by
        have : 1 ≤ N1 X := Finset.card_pos.mpr ⟨1, h1_mem⟩
        exact_mod_cast this
      exact div_nonneg (Real.log_nonneg hN1_ge1) hlogX_pos.le
    have htend_rhs : Filter.Tendsto
        (fun X : ℕ => Real.log C / Real.log (X : ℝ) + betaPrime)
        Filter.atTop (nhds betaPrime) := by
      have hlog_atTop : Filter.Tendsto (fun X : ℕ => Real.log (X : ℝ)) Filter.atTop Filter.atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      have hdiv0 : Filter.Tendsto (fun X : ℕ => Real.log C / Real.log (X : ℝ))
          Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hlog_atTop
      simpa using hdiv0.add tendsto_const_nhds
    have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
        (fun X : ℕ => Real.log (N1 X : ℝ) / Real.log (X : ℝ)) :=
      Filter.isCoboundedUnder_le_of_eventually_le Filter.atTop hev_ge0
    have hbdd_rhs : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun X : ℕ => Real.log C / Real.log (X : ℝ) + betaPrime) :=
      htend_rhs.isBoundedUnder_le
    calc Filter.limsup (fun X : ℕ => Real.log (N1 X : ℝ) / Real.log (X : ℝ)) Filter.atTop
        ≤ Filter.limsup (fun X : ℕ => Real.log C / Real.log (X : ℝ) + betaPrime) Filter.atTop :=
          Filter.limsup_le_limsup hev_le hcobdd hbdd_rhs
      _ = betaPrime := htend_rhs.limsup_eq
  · have hbeta_lo := beta_bounds.1
    unfold betaPrime
    linarith

/-- Sharpened unconditional basin separation `N_1(X) / N_5(X) = O(X^{-0.0255})`:
    combining `thm_basin1_upper_sharp` (`0.6245`) with unconditional `thm_basin5_tight` (`0.65`)
    yields `∃ C > 0, ∀ X ≥ 3, N_1(X) / N_5(X) ≤ C * X^{-0.0255}`. -/
theorem cor_basin_separation_sharp :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 3 ≤ X →
      (N1 X : ℝ) / (N5 X : ℝ) ≤ C * (X : ℝ) ^ (-(255 : ℝ) / 10000) := by
  obtain ⟨C1, hC1, hup⟩ := thm_basin1_upper_sharp
  refine ⟨C1 / (605 / 1000000 : ℝ), by positivity, fun X hX => ?_⟩
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hN1 := hup X (by omega)
  have hN5 := thm_basin5_tight X hX
  have hlow_pos : (0 : ℝ) < (605 / 1000000 : ℝ) * (X : ℝ) ^ ((65 : ℝ) / 100) := by positivity
  have hN5_pos : (0 : ℝ) < (N5 X : ℝ) := lt_of_lt_of_le hlow_pos hN5
  have hdiv : (N1 X : ℝ) / (N5 X : ℝ) ≤
      (C1 * (X : ℝ) ^ betaPrime) / ((605 / 1000000 : ℝ) * (X : ℝ) ^ ((65 : ℝ) / 100)) := by
    rw [div_le_div_iff₀ hN5_pos hlow_pos]
    exact mul_le_mul hN1 hN5 hlow_pos.le (by positivity)
  have hpow : (X : ℝ) ^ betaPrime / (X : ℝ) ^ ((65 : ℝ) / 100) =
      (X : ℝ) ^ (-(255 : ℝ) / 10000) := by
    rw [← Real.rpow_sub hXpos]
    congr 1; unfold betaPrime; norm_num
  have hrew : (C1 * (X : ℝ) ^ betaPrime) / ((605 / 1000000 : ℝ) * (X : ℝ) ^ ((65 : ℝ) / 100)) =
      (C1 / (605 / 1000000 : ℝ)) * (X : ℝ) ^ (-(255 : ℝ) / 10000) := by
    rw [← hpow]; ring
  linarith

end Ouroboros
