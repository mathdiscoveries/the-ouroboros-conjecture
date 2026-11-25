module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
public import Ouroboros.Defs
@[expose] public section

/-! # Section 2: Why bases 4 and 10 stand out (Propositions 2 and 3) -/

namespace Ouroboros

/-! ## Proposition 2: Base 4 is the Collatz problem -/
lemma f4_odd_even (y : ℕ) : f_b 4 (2 * y + 1) % 2 = 0 := by
  unfold f_b; have h : (2 * y + 1) % 2 ≠ 0 := by omega
  simp only [h, ↓reduceIte]; have hm : (2 * y + 1) % 4 = 1 ∨ (2 * y + 1) % 4 = 3 := by omega
  rcases hm with h1 | h3
  · rw [h1]; omega
  · rw [h3]; omega
/-- One odd-to-odd step of `f_4` conjugates to `T_C` via `n = 2*y + 1`. -/
theorem prop_base4_step (y : ℕ) : f_b 4 (f_b 4 (2 * y + 1)) = 2 * T_C y + 1 := by
  have hev := f4_odd_even y; have h1 : (2 * y + 1) % 2 ≠ 0 := by omega
  have hf1 : f_b 4 (2 * y + 1) = (2 * y + 1) % 4 * (2 * y + 1) + 1 := by unfold f_b; simp only [h1, ↓reduceIte]
  have hf2 : f_b 4 (f_b 4 (2 * y + 1)) = f_b 4 (2 * y + 1) / 2 := by
    generalize hx : f_b 4 (2 * y + 1) = x at hev ⊢
    unfold f_b; simp only [hev, ↓reduceIte]
  rw [hf2, hf1]; unfold T_C
  by_cases hy : y % 2 = 0
  · have hmod : (2 * y + 1) % 4 = 1 := by omega
    simp only [hy, ↓reduceIte, hmod]; omega
  · have hmod : (2 * y + 1) % 4 = 3 := by omega
    simp only [hy, ↓reduceIte, hmod]; omega
/-- Orbit-level conjugacy: `2*k` steps of `f_4` from `2*y + 1` equal `2 * T_C^[k] y + 1`. -/
theorem prop_base4_iter (k y : ℕ) : (f_b 4)^[2 * k] (2 * y + 1) = 2 * T_C^[k] y + 1 := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    have hmul : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [hmul, Function.iterate_add_apply]; have h2 : (f_b 4)^[2] (2 * y + 1) = f_b 4 (f_b 4 (2 * y + 1)) := rfl
    rw [h2, prop_base4_step, ih, ← Function.iterate_succ_apply]
lemma T_C_pos {y : ℕ} (hy : 0 < y) : 0 < T_C y := by
  unfold T_C
  split_ifs <;> omega
lemma T_C_iter_pos (k : ℕ) {y : ℕ} (hy : 0 < y) : 0 < T_C^[k] y := by
  induction k generalizing y with
  | zero => exact hy
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (T_C_pos hy)
/-- Under `f_4`, an odd integer `2*y + 1` with `y > 0` never reaches `1`. -/
theorem prop_base4_odd_gt1_ne_one {y : ℕ} (hy : 0 < y) : ¬ Reaches (f_b 4) (2 * y + 1) 1 := by
  rintro ⟨m, hm⟩
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h2 : k + k = 2 * k := by omega
    rw [h2, prop_base4_iter] at hm; have hp := T_C_iter_pos k hy; omega
  · have h2 : 2 * k + 1 = 1 + 2 * k := by omega
    rw [h2, Function.iterate_add_apply, prop_base4_iter] at hm; simp only [Function.iterate_one] at hm
    have hev := f4_odd_even (T_C^[k] y); rw [hm] at hev; omega
/-- For odd `2*y + 1`, reaching `3` under `f_4` is equivalent to `y` reaching `1` under `T_C`. -/
theorem prop_base4_reaches_three_iff (y : ℕ) : Reaches (f_b 4) (2 * y + 1) 3 ↔ Reaches T_C y 1 := by
  constructor
  · rintro ⟨m, hm⟩
    rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have h2 : k + k = 2 * k := by omega
      rw [h2, prop_base4_iter] at hm; exact ⟨k, by omega⟩
    · have h2 : 2 * k + 1 = 1 + 2 * k := by omega
      rw [h2, Function.iterate_add_apply, prop_base4_iter] at hm; simp only [Function.iterate_one] at hm
      have hev := f4_odd_even (T_C^[k] y); rw [hm] at hev; omega
  · rintro ⟨k, hk⟩
    refine ⟨2 * k, ?_⟩
    rw [prop_base4_iter, hk]
/-- Proposition 2 (full equivalence): every positive integer reaches `1` or `3` under `f_4` if and only if every -/
theorem prop_base4_iff_collatz :
    (∀ n : ℕ, 0 < n → Reaches (f_b 4) n 1 ∨ Reaches (f_b 4) n 3) ↔
    (∀ y : ℕ, 0 < y → Reaches T_C y 1) := by
  constructor
  · intro h y hy
    rcases h (2 * y + 1) (by omega) with h1 | h3
    · exact absurd h1 (prop_base4_odd_gt1_ne_one hy)
    · exact (prop_base4_reaches_three_iff y).mp h3
  · intro h n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hev : n % 2 = 0
      · have hpos : 0 < n / 2 := by omega
        have hlt : n / 2 < n := by omega
        have hf : f_b 4 n = n / 2 := by simp [f_b, hev]
        rcases ih (n / 2) hlt hpos with h1 | h3
        · left; exact reaches_step (by rw [hf]; exact h1)
        · right; exact reaches_step (by rw [hf]; exact h3)
      · have hodd : n = 2 * (n / 2) + 1 := by omega
        by_cases h0 : n / 2 = 0
        · left; rw [show n = 1 by omega]
          exact reaches_refl _ 1
        · right; rw [hodd, prop_base4_reaches_three_iff]; exact h (n / 2) (by omega)

/-! ## Proposition 3(1): Trivial bases `b = 2` and `b = 5` -/
/-- Proposition 3(1a): Under `f_2`, every positive integer reaches `1`. -/
theorem prop_base2_reaches_one (n : ℕ) (hn : 0 < n) : Reaches (f_b 2) n 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst h1; exact reaches_refl _ 1
    · by_cases hev : n % 2 = 0
      · have hf : f_b 2 n = n / 2 := by simp [f_b, hev]
        exact reaches_step (by rw [hf]; exact ih (n / 2) (by omega) (by omega))
      · have hmod : n % 2 = 1 := by omega
        have hf1 : f_b 2 n = n + 1 := by unfold f_b; simp [hmod]
        have hf2 : f_b 2 (f_b 2 n) = (n + 1) / 2 := by
          rw [hf1]; unfold f_b
          have : (n + 1) % 2 = 0 := by omega
          simp [this]
        have hlt : (n + 1) / 2 < n := by omega
        have hpos : 0 < (n + 1) / 2 := by omega
        exact reaches_step (reaches_step (by rw [hf2]; exact ih _ hlt hpos))
/-- Helper for `b = 5`: any positive multiple of `5` reaches `1` under `f_5`. -/
lemma base5_mult5_reaches_one (n : ℕ) (hn : 0 < n) (h5 : n % 5 = 0) : Reaches (f_b 5) n 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hev : n % 2 = 0
    · have hf : f_b 5 n = n / 2 := by simp [f_b, hev]
      exact reaches_step (by rw [hf]; exact ih (n / 2) (by omega) (by omega) (by omega))
    · have hf : f_b 5 n = 1 := by unfold f_b; simp [hev, h5]
      exact ⟨1, by simpa using hf⟩
/-- Proposition 3(1b): Under `f_5`, every positive integer reaches `1`. -/
theorem prop_base5_reaches_one (n : ℕ) (hn : 0 < n) : Reaches (f_b 5) n 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · subst h1; exact reaches_refl _ 1
    · by_cases hev : n % 2 = 0
      · have hf : f_b 5 n = n / 2 := by simp [f_b, hev]
        exact reaches_step (by rw [hf]; exact ih (n / 2) (by omega) (by omega))
      · have hmod : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
        rcases hmod with h0 | h1m | h2 | h3 | h4
        · exact base5_mult5_reaches_one n hn h0
        · have hf1 : f_b 5 n = n + 1 := by unfold f_b; simp [hev, h1m]
          have hf2 : f_b 5 (f_b 5 n) = (n + 1) / 2 := by
            rw [hf1]; unfold f_b
            have : (n + 1) % 2 = 0 := by omega
            simp [this]
          exact reaches_step (reaches_step (by rw [hf2]; exact ih _ (by omega) (by omega)))
        · have hf1 : f_b 5 n = 2 * n + 1 := by unfold f_b; simp [hev, h2]
          exact reaches_step (by rw [hf1]; exact base5_mult5_reaches_one _ (by omega) (by omega))
        · have hf1 : f_b 5 n = 3 * n + 1 := by unfold f_b; simp [hev, h3]
          exact reaches_step (by rw [hf1]; exact base5_mult5_reaches_one _ (by omega) (by omega))
        · have hf1 : f_b 5 n = 4 * n + 1 := by unfold f_b; simp [hev, h4]
          have hodd1 : (4 * n + 1) % 2 ≠ 0 := by omega
          have hm1 : (4 * n + 1) % 5 = 2 := by omega
          have hf2 : f_b 5 (f_b 5 n) = 2 * (4 * n + 1) + 1 := by rw [hf1]; unfold f_b; simp [hodd1, hm1]
          exact reaches_step (reaches_step
            (by rw [hf2]; exact base5_mult5_reaches_one _ (by omega) (by omega)))

/-! ## Proposition 3(2): Multiples of 4 (`b = 4k`, `k ≥ 1`) -/
/-- Under `f_{4k}`, every odd step lands at `2 (mod 4)`, so exactly one halving follows. -/
theorem prop_mult4_single_halving {k n : ℕ} (_hk : 1 ≤ k) (hn : n % 2 = 1) : f_b (4 * k) n % 4 = 2 := by
  have hne : n % 2 ≠ 0 := by omega
  have hf : f_b (4 * k) n = (n % (4 * k)) * n + 1 := by unfold f_b; simp [hne]
  rw [hf]; have hd4 : (n % (4 * k)) % 4 = n % 4 := Nat.mod_mod_of_dvd n ⟨k, rfl⟩
  have hmul : ((n % (4 * k)) * n + 1) % 4 = ((n % 4) * (n % 4) + 1) % 4 := by simp [Nat.add_mod, Nat.mul_mod, hd4]
  rw [hmul]; have hcases : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases hcases with h1 | h3
  · simp [h1]
  · simp [h3]

/-! ## Proposition 3(4): Odd bases with even-digit runaway cycles -/
/-- Proposition 3(4): If `b` is odd and `S` is a set of nonzero even residues `< b` closed under -/
theorem prop_odd_runaway {b : ℕ} (_hb : b % 2 = 1) (S : Set ℕ)
    (hS_even : ∀ d ∈ S, d % 2 = 0 ∧ 2 ≤ d)
    (hS_closed : ∀ d ∈ S, (d * d + 1) % b ∈ S)
    {n : ℕ} (hn_odd : n % 2 = 1) (hn_S : n % b ∈ S) :
    ∀ k : ℕ, ((f_b b)^[k] n) % 2 = 1 ∧
             ((f_b b)^[k] n) % b ∈ S ∧
             2 ^ k * n ≤ (f_b b)^[k] n := by
  intro k
  induction k with
  | zero => exact ⟨hn_odd, hn_S, by simp⟩
  | succ k ih =>
    obtain ⟨hodd, hmem, hgrow⟩ := ih; rw [Function.iterate_succ_apply']; set x := (f_b b)^[k] n
    have hne : x % 2 ≠ 0 := by omega
    have hstep : f_b b x = (x % b) * x + 1 := by unfold f_b; simp [hne]
    obtain ⟨hdeven, hd2⟩ := hS_even (x % b) hmem
    refine ⟨?_, ?_, ?_⟩
    · rw [hstep]; have hmul : ((x % b) * x) % 2 = 0 := by rw [Nat.mul_mod, hdeven]; norm_num
      omega
    · rw [hstep]
      have hmod : ((x % b) * x + 1) % b = ((x % b) * (x % b) + 1) % b := by simp [Nat.add_mod, Nat.mul_mod]
      rw [hmod]; exact hS_closed (x % b) hmem
    · rw [hstep, pow_succ]; have hmul : 2 * x ≤ (x % b) * x := Nat.mul_le_mul_right x hd2
      have h2 : 2 ^ k * 2 * n = 2 * (2 ^ k * n) := by ring
      omega
/-- Corollary of Proposition 3(4) for `b = 3`: every odd `n ≡ 2 (mod 3)` diverges strictly. -/
theorem prop_base3_runaway {n : ℕ} (hn_odd : n % 2 = 1) (hn_mod : n % 3 = 2) :
    ∀ k : ℕ, 2 ^ k * n ≤ (f_b 3)^[k] n := fun k =>
  (prop_odd_runaway (b := 3) (by decide) {2}
    (by intro d hd; simp only [Set.mem_singleton_iff] at hd; subst hd; omega)
    (by intro d hd; simp only [Set.mem_singleton_iff] at hd; subst hd; decide)
    hn_odd (by simpa using hn_mod) k).2.2

end Ouroboros
