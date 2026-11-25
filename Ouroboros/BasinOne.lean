module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic
public import Ouroboros.Defs
@[expose] public section

/-! # Section 5 (Part 1): The basin of 1 (Theorem 8, Proposition 9, Theorem 10) -/

namespace Ouroboros

/-! ## Shared 2-adic / halving helpers -/
lemma f_iter_two_pow (v o : ℕ) : f^[v] (2 ^ v * o) = o := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [Function.iterate_succ_apply]; have hmul : 2 ^ (v + 1) * o = 2 * (2 ^ v * o) := by rw [pow_succ', mul_assoc]
    have hev : (2 ^ (v + 1) * o) % 2 = 0 := by rw [hmul]; omega
    rw [f_even hev]; have hdiv : 2 ^ (v + 1) * o / 2 = 2 ^ v * o := by rw [hmul]; omega
    rw [hdiv, ih]
/-- Split a positive natural number into `(v, o)` with `m = 2^v * o` and `o` odd. -/
def splitTwo : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | m + 1 =>
    if (m + 1) % 2 = 0 then
      let p := splitTwo ((m + 1) / 2)
      (p.1 + 1, p.2)
    else (0, m + 1)
lemma splitTwo_spec {m : ℕ} (hm : 0 < m) : (splitTwo m).2 % 2 = 1 ∧ m = 2 ^ (splitTwo m).1 * (splitTwo m).2 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => omega
    | succ m =>
      unfold splitTwo
      by_cases hev : (m + 1) % 2 = 0
      · simp only [hev, ↓reduceIte]; have hpos : 0 < (m + 1) / 2 := by omega
        have hlt : (m + 1) / 2 < m + 1 := by omega
        obtain ⟨hodd, heq⟩ := ih ((m + 1) / 2) hlt hpos
        refine ⟨hodd, ?_⟩
        rw [pow_succ']; have h2 : m + 1 = 2 * ((m + 1) / 2) := by omega
        linarith
      · simp only [hev, ↓reduceIte]; exact ⟨by omega, by simp⟩
lemma splitTwo_pos_of_even {m : ℕ} (hm : 0 < m) (hev : m % 2 = 0) : 1 ≤ (splitTwo m).1 := by
  cases m with
  | zero => omega
  | succ m => unfold splitTwo; simp only [hev, ↓reduceIte]; omega
lemma two_pow_mul_odd_inj {a b x y : ℕ} (hx : x % 2 = 1) (hy : y % 2 = 1)
    (h : 2 ^ a * x = 2 ^ b * y) : a = b ∧ x = y := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simpa using h
    | succ b =>
      have hmul : 2 ^ (b + 1) * y = 2 * (2 ^ b * y) := by rw [pow_succ', mul_assoc]
      rw [pow_zero, one_mul, hmul] at h; omega
  | succ a ih =>
    cases b with
    | zero =>
      have hmul : 2 ^ (a + 1) * x = 2 * (2 ^ a * x) := by rw [pow_succ', mul_assoc]
      rw [pow_zero, one_mul, hmul] at h; omega
    | succ b =>
      have h' : 2 ^ a * x = 2 ^ b * y := by
        have h1 : 2 ^ (a + 1) * x = 2 * (2 ^ a * x) := by rw [pow_succ', mul_assoc]
        have h2 : 2 ^ (b + 1) * y = 2 * (2 ^ b * y) := by rw [pow_succ', mul_assoc]
        omega
      obtain ⟨hab, hxy⟩ := ih h'; exact ⟨by omega, hxy⟩
lemma f_iter_two_pow_eq_odd {k v o z : ℕ} (hz : z % 2 = 1)
    (h : f^[k] (2 ^ v * o) = z) : v ≤ k ∧ f^[k - v] o = z := by
  by_cases hlt : k < v
  · exfalso
    have hsplit : 2 ^ v * o = 2 ^ k * (2 ^ (v - k) * o) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (le_of_lt hlt)]
    rw [hsplit, f_iter_two_pow] at h
    have hev : (2 ^ (v - k) * o) % 2 = 0 := by
      have : v - k = (v - k - 1) + 1 := by omega
      have hmul : 2 ^ (v - k) * o = 2 * (2 ^ (v - k - 1) * o) := by conv_lhs => rw [this, pow_succ', mul_assoc]
      rw [hmul]; omega
    rw [h] at hev; omega
  · have hle : v ≤ k := by omega
    refine ⟨hle, ?_⟩
    have hadd : k = (k - v) + v := by omega
    rw [hadd, Function.iterate_add_apply, f_iter_two_pow] at h; exact h

/-! ## Theorem 8: Residue law modulo 30 -/
/-- The three odd residue classes modulo `30` forming the basin of `1`. -/
def InA (n : ℕ) : Prop := n % 30 = 1
def InB (n : ℕ) : Prop := n % 30 = 15
def InC (n : ℕ) : Prop := n % 30 = 17
def InABC (n : ℕ) : Prop := InA n ∨ InB n ∨ InC n
lemma two_pow_mod_30 {v : ℕ} (hv : 1 ≤ v) : 2 ^ v % 30 = 2 ∨ 2 ^ v % 30 = 4 ∨ 2 ^ v % 30 = 8 ∨ 2 ^ v % 30 = 16 := by
  induction v with
  | zero => omega
  | succ v ih =>
    cases v with
    | zero => left; decide
    | succ v =>
      have h := ih (by omega)
      have hstep : 2 ^ (v + 2) % 30 = (2 * (2 ^ (v + 1) % 30)) % 30 := by rw [pow_succ', Nat.mul_mod]
      rw [hstep]
      rcases h with h | h | h | h <;> rw [h] <;> decide
private lemma residue_step_table :
    ∀ r : Fin 30, r.val % 2 = 1 →
      ∀ p : Fin 4, ∀ q : Fin 3,
        ((r.val % 10) * r.val + 1) % 30 =
          (([2, 4, 8, 16].get p) * ([1, 15, 17].get q)) % 30 →
        r.val = 1 ∨ r.val = 15 ∨ r.val = 17 := by
  decide
/-- One backward odd step preserves `A ∪ B ∪ C`. -/
lemma nextOdd_step_in_ABC {n v o : ℕ} (hn : n % 2 = 1) (hv : 1 ≤ v)
    (heq : d n * n + 1 = 2 ^ v * o) (hABC : InABC o) : InABC n := by
  have hr : n % 30 < 30 := Nat.mod_lt n (by omega)
  have hrodd : (n % 30) % 2 = 1 := by omega
  have hdn : d n = (n % 30) % 10 := by unfold d; omega
  have hlhs : (d n * n + 1) % 30 = (((n % 30) % 10) * (n % 30) + 1) % 30 := by
    rw [hdn]; simp [Nat.add_mod, Nat.mul_mod]
  have hrhs : (2 ^ v * o) % 30 = ((2 ^ v % 30) * (o % 30)) % 30 := by simp [Nat.mul_mod]
  have hmod : (((n % 30) % 10) * (n % 30) + 1) % 30 = ((2 ^ v % 30) * (o % 30)) % 30 := by rw [← hlhs, ← hrhs, heq]
  have hp : ∃ p : Fin 4, [2, 4, 8, 16].get p = 2 ^ v % 30 := by
    rcases two_pow_mod_30 hv with h | h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
    · exact ⟨3, h.symm⟩
  have hq : ∃ q : Fin 3, [1, 15, 17].get q = o % 30 := by
    rcases hABC with h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
  obtain ⟨p, hp⟩ := hp; obtain ⟨q, hq⟩ := hq; rw [← hp, ← hq] at hmod
  exact residue_step_table ⟨n % 30, hr⟩ hrodd p q hmod
/-- Theorem 8 (Residue law): every odd integer whose orbit reaches `1` lies in `A ∪ B ∪ C` (congruent to `1`, -/
theorem thm_residue_law {n : ℕ} (hn : n % 2 = 1) (h : Reaches f n 1) : InABC n := by
  rcases h with ⟨k, hk⟩
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    cases k with
    | zero =>
      simp only [Function.iterate_zero, id_eq] at hk
      left; unfold InA; omega
    | succ k =>
      rw [Function.iterate_succ_apply] at hk; rw [f_odd hn] at hk; have hpos : 0 < d n * n + 1 := by omega
      have hev : (d n * n + 1) % 2 = 0 := by
        have := f_odd_even hn
        rwa [f_odd hn] at this
      obtain ⟨ho_odd, hfac⟩ := splitTwo_spec hpos
      have hv1 : 1 ≤ (splitTwo (d n * n + 1)).1 := splitTwo_pos_of_even hpos hev; set v := (splitTwo (d n * n + 1)).1
      set o := (splitTwo (d n * n + 1)).2; rw [hfac] at hk; obtain ⟨hle, hko⟩ := f_iter_two_pow_eq_odd (by decide) hk
      have hABC_o : InABC o := ih (k - v) (by omega) ho_odd hko
      exact nextOdd_step_in_ABC hn hv1 hfac hABC_o
/-- Corollary of Theorem 8: no integer ending in decimal digit `3` or `9` reaches `1`. -/
theorem thm_residue_no_3_or_9 {n : ℕ} (h : Reaches f n 1) : n % 10 ≠ 3 ∧ n % 10 ≠ 9 := by
  by_cases hn : n % 2 = 1
  · rcases thm_residue_law hn h with hA | hB | hC
    · unfold InA at hA; omega
    · unfold InB at hB; omega
    · unfold InC at hC; omega
  · omega

/-! ## Proposition 9: Binary run-of-ones test -/
/-- `n` is odd and reaches `1` with every odd iterate along the path ending in digit `1`. -/
def ReachesOneDigitOne (n : ℕ) : Prop :=
  n % 2 = 1 ∧ ∃ k : ℕ, f^[k] n = 1 ∧ ∀ j ≤ k, (f^[j] n) % 2 = 1 → d (f^[j] n) = 1
/-- Count of trailing `1`-bits in the binary expansion of `b` (`0` if `b` is even). -/
def trailingOnes : ℕ → ℕ
  | 0 => 0
  | b + 1 => if (b + 1) % 2 = 1 then 1 + trailingOnes ((b + 1) / 2) else 0
lemma trailingOnes_spec (b : ℕ) : b + 1 = 2 ^ trailingOnes b * (2 * (b / 2 ^ (trailingOnes b + 1)) + 1) := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    cases b with
    | zero => simp [trailingOnes]
    | succ b =>
      unfold trailingOnes
      by_cases hodd : (b + 1) % 2 = 1
      · simp only [hodd, ↓reduceIte]; have hlt : (b + 1) / 2 < b + 1 := by omega
        have hih := ih ((b + 1) / 2) hlt; set r' := trailingOnes ((b + 1) / 2)
        have hdiv : ((b + 1) / 2) / 2 ^ (r' + 1) = (b + 1) / 2 ^ (1 + r' + 1) := by
          rw [Nat.div_div_eq_div_mul]; congr 1; ring
        rw [hdiv] at hih; have h2 : (b + 1) + 1 = 2 * ((b + 1) / 2 + 1) := by omega
        rw [h2, hih]; have hpow : 2 ^ (1 + r') = 2 * 2 ^ r' := by rw [add_comm, pow_succ']
        rw [hpow]; ring
      · simp only [hodd, ↓reduceIte, pow_zero, one_mul, zero_add, pow_one]; omega
/-- Every maximal run of consecutive `1`-bits in the binary expansion of `b` has length divisible by `4`. -/
inductive AllRunsDiv4 : ℕ → Prop
  | zero : AllRunsDiv4 0
  | step {b : ℕ} (hb : 0 < b) (h4 : 4 ∣ trailingOnes b)
      (hnext : AllRunsDiv4 (b / 2 ^ (trailingOnes b + 1))) : AllRunsDiv4 b
lemma two_pow_mod_15_of_four_dvd {r : ℕ} (h4 : 4 ∣ r) : 2 ^ r % 15 = 1 := by
  rcases h4 with ⟨m, rfl⟩
  induction m with
  | zero => decide
  | succ m ih =>
    have h : 2 ^ (4 * (m + 1)) = 16 * 2 ^ (4 * m) := by ring
    rw [h, Nat.mul_mod, ih]
lemma AllRunsDiv4_dvd_15 {b : ℕ} (h : AllRunsDiv4 b) : 15 ∣ b := by
  induction h with
  | zero => exact dvd_zero 15
  | @step b hb h4 _ ih =>
    have hspec := trailingOnes_spec b; set r := trailingOnes b; set c := b / 2 ^ (r + 1)
    have h2r : 2 ^ r % 15 = 1 := two_pow_mod_15_of_four_dvd h4
    rcases ih with ⟨q, hq⟩
    have hmod : (b + 1) % 15 = 1 := by
      rw [hspec, hq]; have hmul : 2 ^ r * (2 * (15 * q) + 1) = 15 * (2 ^ r * 2 * q) + 2 ^ r := by ring
      rw [hmul, Nat.mul_add_mod, h2r]
    omega
lemma four_dvd_of_two_pow_succ_mod_5 {r : ℕ} (h : 2 ^ (r + 1) % 5 = 2) : 4 ∣ r := by
  have h4 : 2 ^ r % 5 = 2 ^ (r % 4) % 5 := by
    have hdiv : r = 4 * (r / 4) + r % 4 := (Nat.div_add_mod r 4).symm
    conv_lhs => rw [hdiv, pow_add, Nat.mul_mod]
    have hpow4 : 2 ^ (4 * (r / 4)) % 5 = 1 := by
      have := two_pow_mod_15_of_four_dvd (dvd_mul_right 4 (r / 4))
      omega
    rw [hpow4, one_mul, Nat.mod_mod]
  have hs : 2 ^ (r + 1) % 5 = (2 * (2 ^ (r % 4) % 5)) % 5 := by rw [pow_succ', Nat.mul_mod, h4]
  rw [hs] at h; have hr4 : r % 4 < 4 := Nat.mod_lt r (by omega)
  interval_cases hm : r % 4
  · omega
  · norm_num at h
  · norm_num at h
  · norm_num at h
/-- Proposition 9 (Binary run-of-ones test): an odd integer `2*b + 1` reaches `1` with every odd iterate ending -/
theorem prop_binary_test (b : ℕ) : ReachesOneDigitOne (2 * b + 1) ↔ AllRunsDiv4 b := by
  constructor
  · intro h
    induction b using Nat.strong_induction_on with
    | h b ih =>
      by_cases hb0 : b = 0
      · subst hb0; exact AllRunsDiv4.zero
      · have hb : 0 < b := by omega
        obtain ⟨_, k, hk, hall⟩ := h; have hd0 : d (2 * b + 1) = 1 := hall 0 (Nat.zero_le k) (by simp)
        cases k with
        | zero =>
          simp only [Function.iterate_zero, id_eq] at hk; omega
        | succ k =>
          rw [Function.iterate_succ_apply, f_odd (by omega), hd0, one_mul] at hk
          set r := trailingOnes b; set c := b / 2 ^ (r + 1); have hspec := trailingOnes_spec b
          have hstep : 2 * b + 1 + 1 = 2 ^ (r + 1) * (2 * c + 1) := by rw [pow_succ', mul_assoc, ← hspec]; omega
          rw [hstep] at hk; obtain ⟨hle, hkc⟩ := f_iter_two_pow_eq_odd (by decide) hk
          have hrec_c : ReachesOneDigitOne (2 * c + 1) := by
            refine ⟨by omega, k - (r + 1), hkc, fun j hj hodd => ?_⟩
            have hidx : j + (r + 2) ≤ k + 1 := by omega
            have heq_it : f^[j + (r + 2)] (2 * b + 1) = f^[j] (2 * c + 1) := by
              have h1 : f^[r + 2] (2 * b + 1) = 2 * c + 1 := by
                have : r + 2 = (r + 1) + 1 := by omega
                rw [this, Function.iterate_add_apply, Function.iterate_one, f_odd (by omega),
                    hd0, one_mul, hstep, f_iter_two_pow]
              rw [Function.iterate_add_apply, h1]
            rw [← heq_it]; exact hall (j + (r + 2)) hidx (by rwa [heq_it])
          have hclt : c < b := by
            have h2p : 2 ≤ 2 ^ (r + 1) := by
              calc 2 = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            exact Nat.div_lt_self hb h2p
          have hall_c : AllRunsDiv4 c := ih c hclt hrec_c; have hc15 : 15 ∣ c := AllRunsDiv4_dvd_15 hall_c
          have hc5 : (2 * c + 1) % 5 = 1 := by omega
          have hn5 : (2 * b + 1 + 1) % 5 = 2 := by unfold d at hd0; omega
          have h2r5 : 2 ^ (r + 1) % 5 = 2 := by
            have := congr_arg (· % 5) hstep
            rw [hn5, Nat.mul_mod, hc5, mul_one, Nat.mod_mod] at this; exact this.symm
          exact AllRunsDiv4.step hb (four_dvd_of_two_pow_succ_mod_5 h2r5) hall_c
  · intro hall
    induction hall with
    | zero =>
      exact ⟨by decide, 0, rfl, fun j hj _ => by
        have : j = 0 := by omega
        subst this; decide⟩
    | @step b hb h4 hnext ih =>
      have hb15 : 15 ∣ b := AllRunsDiv4_dvd_15 (AllRunsDiv4.step hb h4 hnext)
      have hd : d (2 * b + 1) = 1 := by unfold d; omega
      set r := trailingOnes b; set c := b / 2 ^ (r + 1); have hspec := trailingOnes_spec b
      have hstep : 2 * b + 1 + 1 = 2 ^ (r + 1) * (2 * c + 1) := by rw [pow_succ', mul_assoc, ← hspec]; omega
      obtain ⟨_, k, hk, hall_c⟩ := ih
      refine ⟨by omega, k + (r + 2), ?_, ?_⟩
      · rw [Function.iterate_add_apply]
        have h1 : f^[r + 2] (2 * b + 1) = 2 * c + 1 := by
          have : r + 2 = (r + 1) + 1 := by omega
          rw [this, Function.iterate_add_apply, Function.iterate_one, f_odd (by omega),
              hd, one_mul, hstep, f_iter_two_pow]
        rw [h1, hk]
      · intro j hj hodd
        by_cases hj0 : j = 0
        · subst hj0; simpa using hd
        · by_cases hjsm : j < r + 2
          · exfalso; have hj1 : j = (j - 1) + 1 := by omega
            have hle : j - 1 ≤ r := by omega
            have hit : f^[j] (2 * b + 1) = 2 ^ (r + 1 - (j - 1)) * (2 * c + 1) := by
              conv_lhs => rw [hj1]
              rw [Function.iterate_add_apply, Function.iterate_one, f_odd (by omega),
                  hd, one_mul, hstep]
              have hsp : 2 ^ (r + 1) * (2 * c + 1) =
                  2 ^ (j - 1) * (2 ^ (r + 1 - (j - 1)) * (2 * c + 1)) := by
                rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (by omega)]
              rw [hsp, f_iter_two_pow]
            rw [hit] at hodd
            have hev : (2 ^ (r + 1 - (j - 1)) * (2 * c + 1)) % 2 = 0 := by
              have : r + 1 - (j - 1) = (r - (j - 1)) + 1 := by omega
              have hmul : 2 ^ (r + 1 - (j - 1)) * (2 * c + 1) =
                  2 * (2 ^ (r - (j - 1)) * (2 * c + 1)) := by
                rw [this, pow_succ', mul_assoc]
              rw [hmul]; omega
            omega
          · have hge : r + 2 ≤ j := by omega
            have hj_eq : j = (j - (r + 2)) + (r + 2) := by omega
            have h1 : f^[r + 2] (2 * b + 1) = 2 * c + 1 := by
              have : r + 2 = (r + 1) + 1 := by omega
              rw [this, Function.iterate_add_apply, Function.iterate_one, f_odd (by omega),
                  hd, one_mul, hstep, f_iter_two_pow]
            rw [hj_eq, Function.iterate_add_apply, h1] at hodd ⊢; exact hall_c (j - (r + 2)) (by omega) hodd

/-! ## Theorem 10: Power bounds and density zero for the basin of 1 -/

/-! ### Part 10.1: Exact roots `a_1` and `a*` and numerical exponent bounds -/
/-- Polynomial `a + a^4 - 1` defining `a_1`. -/
def polyA1 (a : ℝ) : ℝ := a + a ^ 4 - 1
/-- Polynomial `(1 - a - a^4)((1 - a)(1 - a^4) - a^4) - a^9` defining `a*`. -/
def polyAStar (a : ℝ) : ℝ := (1 - a - a ^ 4) * ((1 - a) * (1 - a ^ 4) - a ^ 4) - a ^ 9
lemma exists_unique_a1 : ∃! a : ℝ, 0 < a ∧ a < 1 ∧ a + a ^ 4 = 1 := by
  have hcont : ContinuousOn polyA1 (Set.Icc (724491 / 1000000 : ℝ) (724492 / 1000000 : ℝ)) :=
    (by unfold polyA1; fun_prop : Continuous polyA1).continuousOn
  have hlo : polyA1 (724491 / 1000000) < 0 := by unfold polyA1; norm_num
  have hhi : 0 < polyA1 (724492 / 1000000) := by unfold polyA1; norm_num
  have hmem : (0 : ℝ) ∈ Set.Icc (polyA1 (724491 / 1000000)) (polyA1 (724492 / 1000000)) := ⟨hlo.le, hhi.le⟩
  obtain ⟨a, ha_mem, ha_eq⟩ := intermediate_value_Icc (by norm_num) hcont hmem
  have ha0 : 0 < a := by linarith [ha_mem.1]
  refine ⟨a, ⟨ha0, by linarith [ha_mem.2], by unfold polyA1 at ha_eq; linarith⟩, ?_⟩
  intro b ⟨hb0, _, hbeq⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h4 : b ^ 4 < a ^ 4 := by gcongr
    have : a + a ^ 4 = 1 := by unfold polyA1 at ha_eq; linarith
    linarith
  · have h4 : a ^ 4 < b ^ 4 := by gcongr
    have : a + a ^ 4 = 1 := by unfold polyA1 at ha_eq; linarith
    linarith
/-- The unique root `a_1 ∈ (0, 1)` of `a + a^4 = 1`. -/
noncomputable def a1 : ℝ := Classical.choose exists_unique_a1
lemma a1_spec : 0 < a1 ∧ a1 < 1 ∧ a1 + a1 ^ 4 = 1 := (Classical.choose_spec exists_unique_a1).1
lemma a1_bounds : (724491 / 1000000 : ℝ) < a1 ∧ a1 < (724492 / 1000000 : ℝ) := by
  obtain ⟨h0, _, heq⟩ := a1_spec; constructor
  · by_contra hle
    push Not at hle
    have h4 : a1 ^ 4 ≤ (724491 / 1000000 : ℝ) ^ 4 := by gcongr
    have : (724491 / 1000000 : ℝ) + (724491 / 1000000 : ℝ) ^ 4 < 1 := by norm_num
    linarith
  · by_contra hge
    push Not at hge
    have h4 : (724492 / 1000000 : ℝ) ^ 4 ≤ a1 ^ 4 := by gcongr
    have : (1 : ℝ) < (724492 / 1000000 : ℝ) + (724492 / 1000000 : ℝ) ^ 4 := by norm_num
    linarith
/-- Lower-bound exponent `γ = log_2(1 / a_1)`. -/
noncomputable def gamma : ℝ := Real.logb 2 (1 / a1)
lemma two_rpow_gamma : (2 : ℝ) ^ gamma = 1 / a1 := by
  unfold gamma
  have hpos : (0 : ℝ) < 1 / a1 := div_pos one_pos a1_spec.1
  exact Real.rpow_logb (by norm_num) (by norm_num) hpos
lemma two_rpow_neg_gamma : (2 : ℝ) ^ (-gamma) = a1 := by
  rw [Real.rpow_neg (by norm_num), two_rpow_gamma, one_div, inv_inv]
lemma gamma_pos : 0 < gamma := by
  unfold gamma
  have hgt : (1 : ℝ) < 1 / a1 := by rw [one_lt_div a1_spec.1]; exact a1_spec.2.1
  exact Real.logb_pos (by norm_num) hgt
lemma exists_unique_aStar :
    ∃! a : ℝ, 0 < a ∧ a < 1 ∧
      (1 - a - a ^ 4) * ((1 - a) * (1 - a ^ 4) - a ^ 4) = a ^ 9 := by
  have hcont : ContinuousOn polyAStar (Set.Icc (64779885 / 100000000 : ℝ) (6477989 / 10000000 : ℝ)) :=
    (by unfold polyAStar; fun_prop : Continuous polyAStar).continuousOn
  have hlo : 0 < polyAStar (64779885 / 100000000) := by unfold polyAStar; norm_num
  have hhi : polyAStar (6477989 / 10000000) < 0 := by unfold polyAStar; norm_num
  have hmem : (0 : ℝ) ∈ Set.Icc (polyAStar (6477989 / 10000000)) (polyAStar (64779885 / 100000000)) :=
    ⟨hhi.le, hlo.le⟩
  obtain ⟨a, ha_mem, ha_eq⟩ := intermediate_value_Icc' (by norm_num) hcont hmem
  have ha0 : 0 < a := by linarith [ha_mem.1]
  have ha1 : a < 1 := by linarith [ha_mem.2]
  have ha_root : (1 - a - a ^ 4) * ((1 - a) * (1 - a ^ 4) - a ^ 4) = a ^ 9 := by unfold polyAStar at ha_eq; linarith
  have ha_f1 : 0 < 1 - a - a ^ 4 := by
    have h4 : a ^ 4 ≤ (6477989 / 10000000 : ℝ) ^ 4 := by gcongr; exact ha_mem.2
    linarith [ha_mem.2, show (6477989 / 10000000 : ℝ) + (6477989 / 10000000 : ℝ) ^ 4 < 1 by norm_num]
  have ha_f2 : 0 < (1 - a) * (1 - a ^ 4) - a ^ 4 := by
    have : 0 < a ^ 9 := by positivity
    nlinarith
  refine ⟨a, ⟨ha0, ha1, ha_root⟩, ?_⟩
  intro b ⟨hb0, hb1, hb_root⟩
  have hb_f1 : 0 < 1 - b - b ^ 4 := by
    by_contra hle
    push Not at hle
    have h1 : 0 ≤ b ^ 4 + b - 1 := by linarith
    have h2 : b ^ 4 + b - 1 < b ^ 5 := by
      have : b ^ 5 - (b ^ 4 + b - 1) = (1 - b) * (1 - b ^ 4) := by ring
      have hb4 : b ^ 4 < 1 := by
        calc b ^ 4 < 1 ^ 4 := by gcongr
          _ = 1 := by norm_num
      have hprod : 0 < (1 - b) * (1 - b ^ 4) := mul_pos (by linarith) (by linarith)
      linarith
    have h3 : (1 - b) * (1 - b ^ 4) > 0 := by
      have hb4 : b ^ 4 < 1 := by
        calc b ^ 4 < 1 ^ 4 := by gcongr
          _ = 1 := by norm_num
      exact mul_pos (by linarith) (by linarith)
    have h4 : b ^ 4 - (1 - b) * (1 - b ^ 4) < b ^ 4 := by linarith
    have h5 : 0 ≤ b ^ 4 - (1 - b) * (1 - b ^ 4) := by
      have : b ^ 4 - (1 - b) * (1 - b ^ 4) = (b ^ 4 + b - 1) + b ^ 4 * (1 - b) := by ring
      have : 0 ≤ b ^ 4 * (1 - b) := mul_nonneg (by positivity) (by linarith)
      linarith
    have hprod : (b ^ 4 + b - 1) * (b ^ 4 - (1 - b) * (1 - b ^ 4)) < b ^ 5 * b ^ 4 := by
      calc (b ^ 4 + b - 1) * (b ^ 4 - (1 - b) * (1 - b ^ 4))
          ≤ (b ^ 4 + b - 1) * b ^ 4 := mul_le_mul_of_nonneg_left h4.le h1
        _ < b ^ 5 * b ^ 4 := mul_lt_mul_of_pos_right h2 (by positivity)
    have heq' : (1 - b - b ^ 4) * ((1 - b) * (1 - b ^ 4) - b ^ 4) =
        (b ^ 4 + b - 1) * (b ^ 4 - (1 - b) * (1 - b ^ 4)) := by ring
    have hb9 : b ^ 5 * b ^ 4 = b ^ 9 := by ring
    linarith
  have hb_f2 : 0 < (1 - b) * (1 - b ^ 4) - b ^ 4 := by
    have : 0 < b ^ 9 := by positivity
    nlinarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h4 : b ^ 4 < a ^ 4 := by gcongr
    have h9 : b ^ 9 < a ^ 9 := by gcongr
    have hf1 : 1 - a - a ^ 4 < 1 - b - b ^ 4 := by linarith
    have hf2 : (1 - a) * (1 - a ^ 4) - a ^ 4 < (1 - b) * (1 - b ^ 4) - b ^ 4 := by
      have ha4 : a ^ 4 < 1 := by
        calc a ^ 4 < 1 ^ 4 := by gcongr
          _ = 1 := by norm_num
      have hprod : (1 - a) * (1 - a ^ 4) < (1 - b) * (1 - b ^ 4) :=
        mul_lt_mul' (by linarith) (by linarith) (by linarith) (by linarith)
      linarith
    have : (1 - a - a ^ 4) * ((1 - a) * (1 - a ^ 4) - a ^ 4) <
        (1 - b - b ^ 4) * ((1 - b) * (1 - b ^ 4) - b ^ 4) :=
      mul_lt_mul' hf1.le hf2 ha_f2.le hb_f1
    linarith
  · have h4 : a ^ 4 < b ^ 4 := by gcongr
    have h9 : a ^ 9 < b ^ 9 := by gcongr
    have hf1 : 1 - b - b ^ 4 < 1 - a - a ^ 4 := by linarith
    have hf2 : (1 - b) * (1 - b ^ 4) - b ^ 4 < (1 - a) * (1 - a ^ 4) - a ^ 4 := by
      have hb4 : b ^ 4 < 1 := by
        calc b ^ 4 < 1 ^ 4 := by gcongr
          _ = 1 := by norm_num
      have hprod : (1 - b) * (1 - b ^ 4) < (1 - a) * (1 - a ^ 4) :=
        mul_lt_mul' (by linarith) (by linarith) (by linarith) (by linarith)
      linarith
    have : (1 - b - b ^ 4) * ((1 - b) * (1 - b ^ 4) - b ^ 4) <
        (1 - a - a ^ 4) * ((1 - a) * (1 - a ^ 4) - a ^ 4) :=
      mul_lt_mul' hf1.le hf2 hb_f2.le ha_f1
    linarith
/-- The unique root `a* ∈ (0, 1)` of `(1 - a - a^4)((1 - a)(1 - a^4) - a^4) = a^9`. -/
noncomputable def aStar : ℝ := Classical.choose exists_unique_aStar
lemma aStar_spec :
    0 < aStar ∧ aStar < 1 ∧
    (1 - aStar - aStar ^ 4) * ((1 - aStar) * (1 - aStar ^ 4) - aStar ^ 4) = aStar ^ 9 :=
  (Classical.choose_spec exists_unique_aStar).1
lemma aStar_bounds : (64779885 / 100000000 : ℝ) < aStar ∧ aStar < (6477989 / 10000000 : ℝ) := by
  have hcont : ContinuousOn polyAStar (Set.Icc (64779885 / 100000000 : ℝ) (6477989 / 10000000 : ℝ)) :=
    (by unfold polyAStar; fun_prop : Continuous polyAStar).continuousOn
  have hlo : 0 < polyAStar (64779885 / 100000000) := by unfold polyAStar; norm_num
  have hhi : polyAStar (6477989 / 10000000) < 0 := by unfold polyAStar; norm_num
  obtain ⟨a, ha_mem, ha_eq⟩ := intermediate_value_Icc' (by norm_num) hcont ⟨hhi.le, hlo.le⟩
  have ha_uniq : a = aStar := (Classical.choose_spec exists_unique_aStar).2 a
    ⟨by linarith [ha_mem.1], by linarith [ha_mem.2], by unfold polyAStar at ha_eq; linarith⟩
  subst ha_uniq
  refine ⟨lt_of_le_of_ne ha_mem.1 ?_, lt_of_le_of_ne ha_mem.2 ?_⟩
  · intro heq; rw [← heq] at ha_eq; linarith
  · intro heq; rw [heq] at ha_eq; linarith
/-- Upper-bound exponent `β = log_2(1 / a*)`. -/
noncomputable def beta : ℝ := Real.logb 2 (1 / aStar)
lemma two_rpow_beta : (2 : ℝ) ^ beta = 1 / aStar := by
  unfold beta; exact Real.rpow_logb (by norm_num) (by norm_num) (div_pos one_pos aStar_spec.1)
lemma two_rpow_neg_beta : (2 : ℝ) ^ (-beta) = aStar := by
  rw [Real.rpow_neg (by norm_num), two_rpow_beta, one_div, inv_inv]
/-- Explicit rigorous bracket `0.62625 < β < 0.626383`. -/
lemma beta_bounds : (501 / 800 : ℝ) < beta ∧ beta < (626383 / 1000000 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := aStar_bounds; have ha_pos := aStar_spec.1
  have h2_58_lo : (1542210825 / 1000000000 : ℝ) < (2 : ℝ) ^ ((5 : ℝ) / 8) := by
    have h8 : (1542210825 / 1000000000 : ℝ) ^ (8 : ℕ) < ((2 : ℝ) ^ ((5 : ℝ) / 8)) ^ (8 : ℕ) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((5 : ℝ) / 8)) 8, ← Real.rpow_mul (by norm_num)]
      have hexp : ((5 : ℝ) / 8) * (8 : ℕ) = (5 : ℕ) := by norm_num
      rw [hexp, Real.rpow_natCast]; norm_num
    exact lt_of_pow_lt_pow_left₀ 8 (by positivity) h8
  have h2_58_hi : (2 : ℝ) ^ ((5 : ℝ) / 8) < (1542210826 / 1000000000 : ℝ) := by
    have h8 : ((2 : ℝ) ^ ((5 : ℝ) / 8)) ^ (8 : ℕ) < (1542210826 / 1000000000 : ℝ) ^ (8 : ℕ) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((5 : ℝ) / 8)) 8, ← Real.rpow_mul (by norm_num)]
      have hexp : ((5 : ℝ) / 8) * (8 : ℕ) = (5 : ℕ) := by norm_num
      rw [hexp, Real.rpow_natCast]; norm_num
    exact lt_of_pow_lt_pow_left₀ 8 (by norm_num) h8
  have hlog2_lo : (6931471803 / 10000000000 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2_hi : Real.log 2 < (6931471808 / 10000000000 : ℝ) := by linarith [Real.log_two_lt_d9]
  constructor
  ·
    have hexp_hi : (2 : ℝ) ^ ((1 : ℝ) / 800) < (10009 / 10000 : ℝ) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      have harg : Real.log 2 * (1 / 800 : ℝ) < (867 / 1000000 : ℝ) := by linarith
      have h1 : Real.exp (Real.log 2 * (1 / 800 : ℝ)) < Real.exp (867 / 1000000 : ℝ) := Real.exp_lt_exp.mpr harg
      have h2 : Real.exp (867 / 1000000 : ℝ) ≤ (1 - 867 / 1000000 : ℝ)⁻¹ := by
        have := Real.add_one_le_exp (-(867 / 1000000 : ℝ))
        rw [Real.exp_neg] at this
        have hpos : (0 : ℝ) < 1 - 867 / 1000000 := by norm_num
        rw [le_inv_comm₀ (Real.exp_pos _) hpos]; linarith
      linarith [show (1 - 867 / 1000000 : ℝ)⁻¹ < 10009 / 10000 by norm_num]
    have hprod : (2 : ℝ) ^ ((501 : ℝ) / 800) < 1 / aStar := by
      have hsplit : (501 : ℝ) / 800 = (5 : ℝ) / 8 + (1 : ℝ) / 800 := by norm_num
      rw [hsplit, Real.rpow_add (by norm_num)]
      have hmul : (2 : ℝ) ^ ((5 : ℝ) / 8) * (2 : ℝ) ^ ((1 : ℝ) / 800) <
          (1542210826 / 1000000000 : ℝ) * (10009 / 10000 : ℝ) :=
        mul_lt_mul'' h2_58_hi hexp_hi (by positivity) (by positivity)
      have hinv : (1542210826 / 1000000000 : ℝ) * (10009 / 10000 : ℝ) < 1 / aStar := by
        rw [lt_div_iff₀ ha_pos]
        have : (1542210826 / 1000000000 : ℝ) * (10009 / 10000 : ℝ) * aStar <
            (1542210826 / 1000000000 : ℝ) * (10009 / 10000 : ℝ) * (6477989 / 10000000 : ℝ) := by
          gcongr
        linarith [show (1542210826 / 1000000000 : ℝ) * (10009 / 10000 : ℝ) *
            (6477989 / 10000000 : ℝ) < 1 by norm_num]
      linarith
    have hlt : (2 : ℝ) ^ ((501 : ℝ) / 800) < (2 : ℝ) ^ beta := by rwa [two_rpow_beta]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num)).mp hlt
  ·
    have hexp_lo : (1 + (10 / 7231 : ℝ) * (6931471803 / 10000000000 : ℝ)) <
        (2 : ℝ) ^ ((10 : ℝ) / 7231) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      have harg : (10 / 7231 : ℝ) * (6931471803 / 10000000000 : ℝ) <
          Real.log 2 * (10 / 7231 : ℝ) := by linarith
      have h1 := Real.add_one_le_exp (Real.log 2 * (10 / 7231 : ℝ)); linarith
    have hprod : 1 / aStar < (2 : ℝ) ^ ((5 : ℝ) / 8 + (10 : ℝ) / 7231) := by
      rw [Real.rpow_add (by norm_num)]
      have hmul : (1542210825 / 1000000000 : ℝ) *
          (1 + (10 / 7231 : ℝ) * (6931471803 / 10000000000 : ℝ)) <
          (2 : ℝ) ^ ((5 : ℝ) / 8) * (2 : ℝ) ^ ((10 : ℝ) / 7231) :=
        mul_lt_mul'' h2_58_lo hexp_lo (by norm_num) (by norm_num)
      have hinv : 1 / aStar < (1542210825 / 1000000000 : ℝ) *
          (1 + (10 / 7231 : ℝ) * (6931471803 / 10000000000 : ℝ)) := by
        rw [div_lt_iff₀ ha_pos]
        have : (1542210825 / 1000000000 : ℝ) *
            (1 + (10 / 7231 : ℝ) * (6931471803 / 10000000000 : ℝ)) * (64779885 / 100000000 : ℝ) <
            (1542210825 / 1000000000 : ℝ) *
            (1 + (10 / 7231 : ℝ) * (6931471803 / 10000000000 : ℝ)) * aStar := by
          gcongr
        linarith [show (1 : ℝ) < (1542210825 / 1000000000 : ℝ) *
            (1 + (10 / 7231 : ℝ) * (6931471803 / 10000000000 : ℝ)) *
            (64779885 / 100000000 : ℝ) by norm_num]
      linarith
    have hlt : (2 : ℝ) ^ beta < (2 : ℝ) ^ ((5 : ℝ) / 8 + (10 : ℝ) / 7231) := by rwa [two_rpow_beta]
    have hlt' := (Real.rpow_lt_rpow_left_iff (by norm_num)).mp hlt
    linarith [show (5 : ℝ) / 8 + (10 : ℝ) / 7231 < 626383 / 1000000 by norm_num]

/-! ### Part 10.2: Lower bound `c * X^γ ≤ N1(X)` -/
/-- Value of a backward `d = 1` chain: `chainVal [] = 1`, `chainVal (v :: vs) = 2^v * chainVal vs - 1`. -/
def chainVal : List ℕ → ℕ
  | [] => 1
  | v :: vs => 2 ^ v * chainVal vs - 1
/-- Valid non-empty backward chain with all exponents `≡ 1 (mod 4)` and innermost `v_1 ≥ 5`. -/
inductive ValidTail : List ℕ → Prop
  | base {v : ℕ} (hv5 : 5 ≤ v) (hv4 : v % 4 = 1) : ValidTail [v]
  | cons {v : ℕ} {vs : List ℕ} (hv4 : v % 4 = 1) (hvs : ValidTail vs) : ValidTail (v :: vs)
lemma two_pow_mod_30_of_mod4_1 {v : ℕ} (hv : v % 4 = 1) : 2 ^ v % 30 = 2 := by
  have h : v = 4 * (v / 4) + 1 := by omega
  rw [h, pow_add, pow_one, Nat.mul_mod]
  have h15 : 2 ^ (4 * (v / 4)) % 15 = 1 := two_pow_mod_15_of_four_dvd (dvd_mul_right 4 (v / 4))
  have h2 : 2 ^ (4 * (v / 4)) % 30 = 1 ∨ 2 ^ (4 * (v / 4)) % 30 = 16 := by omega
  rcases h2 with h2 | h2 <;> rw [h2]
lemma chainVal_props {vs : List ℕ} (h : ValidTail vs) :
    chainVal vs % 30 = 1 ∧ 1 < chainVal vs ∧ Reaches f (chainVal vs) 1 ∧
    chainVal vs < 2 ^ vs.sum := by
  induction h with
  | @base v hv5 hv4 =>
    have h2v : 2 ^ v % 30 = 2 := two_pow_mod_30_of_mod4_1 hv4
    have hge : 32 ≤ 2 ^ v := by
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv5
    simp only [chainVal, mul_one, List.sum_cons, List.sum_nil, add_zero]
    refine ⟨by omega, by omega, ?_, by omega⟩
    have hd : d (2 ^ v - 1) = 1 := by unfold d; omega
    refine ⟨v + 1, ?_⟩
    rw [Function.iterate_succ_apply, f_odd (by omega), hd, one_mul]
    have hsub : 2 ^ v - 1 + 1 = 2 ^ v * 1 := by omega
    rw [hsub, f_iter_two_pow]
  | @cons v vs hv4 _ ih =>
    obtain ⟨hmod, hgt1, hreach, hlt⟩ := ih; have h2v : 2 ^ v % 30 = 2 := two_pow_mod_30_of_mod4_1 hv4
    have hv1 : 1 ≤ v := by omega
    have h2ge : 2 ≤ 2 ^ v := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv1
    have hmul_mod : (2 ^ v * chainVal vs) % 30 = 2 := by rw [Nat.mul_mod, h2v, hmod]
    have hmul_ge : 4 ≤ 2 ^ v * chainVal vs := by nlinarith
    simp only [chainVal, List.sum_cons]
    refine ⟨by omega, by omega, ?_, ?_⟩
    · have hd : d (2 ^ v * chainVal vs - 1) = 1 := by unfold d; omega
      have hstep : f^[v + 1] (2 ^ v * chainVal vs - 1) = chainVal vs := by
        rw [Function.iterate_succ_apply, f_odd (by omega), hd, one_mul]
        have hsub : 2 ^ v * chainVal vs - 1 + 1 = 2 ^ v * chainVal vs := by omega
        rw [hsub, f_iter_two_pow]
      exact reaches_trans ⟨v + 1, hstep⟩ hreach
    · rw [pow_add]
      have : 2 ^ v * chainVal vs < 2 ^ v * 2 ^ vs.sum := Nat.mul_lt_mul_of_pos_left hlt (by positivity)
      omega
lemma chainVal_inj {vs1 vs2 : List ℕ} (h1 : ValidTail vs1) (h2 : ValidTail vs2)
    (heq : chainVal vs1 = chainVal vs2) : vs1 = vs2 := by
  induction h1 generalizing vs2 with
  | @base v1 hv5_1 hv4_1 =>
    cases h2 with
    | @base v2 hv5_2 hv4_2 =>
      have h2v1 : 32 ≤ 2 ^ v1 := by
        calc 32 = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ v1 := Nat.pow_le_pow_right (by norm_num) hv5_1
      have h2v2 : 32 ≤ 2 ^ v2 := by
        calc 32 = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ v2 := Nat.pow_le_pow_right (by norm_num) hv5_2
      simp only [chainVal, mul_one] at heq; have hpow : 2 ^ v1 * 1 = 2 ^ v2 * 1 := by omega
      have hv := (two_pow_mul_odd_inj (by decide) (by decide) hpow).1
      rw [hv]
    | @cons v2 t2 hv4_2 ht2 =>
      exfalso; obtain ⟨hmod2, hgt2, _, _⟩ := chainVal_props ht2
      have h2v1 : 32 ≤ 2 ^ v1 := by
        calc 32 = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ v1 := Nat.pow_le_pow_right (by norm_num) hv5_1
      have h2v2 : 2 ≤ 2 ^ v2 := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ v2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [chainVal, mul_one] at heq; have hpow : 2 ^ v1 * 1 = 2 ^ v2 * chainVal t2 := by omega
      have hodd2 : chainVal t2 % 2 = 1 := by omega
      have h1eq := (two_pow_mul_odd_inj (by decide) hodd2 hpow).2
      omega
  | @cons v1 t1 hv4_1 ht1 ih =>
    cases h2 with
    | @base v2 hv5_2 hv4_2 =>
      exfalso; obtain ⟨hmod1, hgt1, _, _⟩ := chainVal_props ht1
      have h2v1 : 2 ≤ 2 ^ v1 := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ v1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2v2 : 32 ≤ 2 ^ v2 := by
        calc 32 = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ v2 := Nat.pow_le_pow_right (by norm_num) hv5_2
      simp only [chainVal, mul_one] at heq; have hpow : 2 ^ v1 * chainVal t1 = 2 ^ v2 * 1 := by omega
      have hodd1 : chainVal t1 % 2 = 1 := by omega
      have h1eq := (two_pow_mul_odd_inj hodd1 (by decide) hpow).2
      omega
    | @cons v2 t2 hv4_2 ht2 =>
      obtain ⟨hmod1, hgt1, _, _⟩ := chainVal_props ht1; obtain ⟨hmod2, hgt2, _, _⟩ := chainVal_props ht2
      have h2v1 : 2 ≤ 2 ^ v1 := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ v1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2v2 : 2 ≤ 2 ^ v2 := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ v2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp only [chainVal] at heq; have hp1 : 1 ≤ 2 ^ v1 * chainVal t1 := by nlinarith
      have hp2 : 1 ≤ 2 ^ v2 * chainVal t2 := by nlinarith
      have hpow : 2 ^ v1 * chainVal t1 = 2 ^ v2 * chainVal t2 := by omega
      have hodd1 : chainVal t1 % 2 = 1 := by omega
      have hodd2 : chainVal t2 % 2 = 1 := by omega
      obtain ⟨hv, hct⟩ := two_pow_mul_odd_inj hodd1 hodd2 hpow; rw [hv, ih ht2 hct]
/-- Explicit finite set of compositions of `m` into parts `≡ 1 (mod 4)`. -/
def UList : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | 1 => {[1]}
  | 2 => {[1, 1]}
  | 3 => {[1, 1, 1]}
  | 4 => {[1, 1, 1, 1]}
  | m + 5 =>
    (UList (m + 4)).image (fun l => 1 :: l) ∪
    (UList (m + 1)).image (fun l => match l with | [] => [] | w :: rest => (w + 4) :: rest)
lemma UList_props (m : ℕ) : ∀ l ∈ UList m, (∀ w ∈ l, w % 4 = 1) ∧ l.sum = m ∧ (1 ≤ m → l ≠ []) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 => intro l hl; simp [UList] at hl; subst hl; simp
    | 1 => intro l hl; simp [UList] at hl; subst hl; simp
    | 2 => intro l hl; simp [UList] at hl; subst hl; simp
    | 3 => intro l hl; simp [UList] at hl; subst hl; simp
    | 4 => intro l hl; simp [UList] at hl; subst hl; simp
    | m + 5 =>
      intro l hl; simp only [UList, Finset.mem_union, Finset.mem_image] at hl
      rcases hl with ⟨l', hl', rfl⟩ | ⟨l', hl', rfl⟩
      · obtain ⟨hmod, hsum, _⟩ := ih (m + 4) (by omega) l' hl'
        refine ⟨fun w hw => ?_, by simp [hsum]; omega, fun _ => by simp⟩
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · decide
        · exact hmod w hw
      · obtain ⟨hmod, hsum, hne⟩ := ih (m + 1) (by omega) l' hl'
        cases l' with
        | nil => exact absurd rfl (hne (by omega))
        | cons w rest =>
          simp only
          refine ⟨fun u hu => ?_, ?_, fun _ => by simp⟩
          · simp only [List.mem_cons] at hu
            rcases hu with rfl | hu
            · have := hmod w (by simp); omega
            · exact hmod u (by simp [hu])
          · simp only [List.sum_cons] at hsum ⊢; omega
/-- Recurrence `U(0)=...=U(4)=1`, `U(m+5) = U(m+4) + U(m+1)`. -/
def URec : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | m + 5 => URec (m + 4) + URec (m + 1)
lemma UList_card (m : ℕ) : (UList m).card = URec m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 => simp [UList, URec]
    | 1 => simp [UList, URec]
    | 2 => simp [UList, URec]
    | 3 => simp [UList, URec]
    | 4 => simp [UList, URec]
    | m + 5 =>
      unfold UList URec
      have hdisj : Disjoint
          ((UList (m + 4)).image (fun l => 1 :: l))
          ((UList (m + 1)).image (fun l => match l with | [] => [] | w :: rest => (w + 4) :: rest)) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        simp only [Finset.mem_image] at hx1 hx2; obtain ⟨l1, _, rfl⟩ := hx1; obtain ⟨l2, hl2, h2⟩ := hx2
        have hne := (UList_props (m + 1) l2 hl2).2.2 (by omega)
        cases l2 with
        | nil => exact hne rfl
        | cons w rest =>
          simp only [List.cons.injEq] at h2; omega
      rw [Finset.card_union_of_disjoint hdisj]
      have hc1 : ((UList (m + 4)).image (fun l => 1 :: l)).card = (UList (m + 4)).card :=
        Finset.card_image_of_injective _ (fun a b h => by simpa using h)
      have hc2 : ((UList (m + 1)).image (fun l => match l with | [] => [] | w :: rest => (w + 4) :: rest)).card =
          (UList (m + 1)).card := by
        refine Finset.card_image_of_injOn fun a ha b hb h => ?_
        have hna := (UList_props (m + 1) a ha).2.2 (by omega)
        have hnb := (UList_props (m + 1) b hb).2.2 (by omega)
        cases a with
        | nil => exact absurd rfl hna
        | cons wa ra =>
          cases b with
          | nil => exact absurd rfl hnb
          | cons wb rb =>
            simp only [List.cons.injEq] at h; rw [show wa = wb by omega, h.2]
      rw [hc1, hc2, ih (m + 4) (by omega), ih (m + 1) (by omega)]
lemma URec_lower (m : ℕ) : a1 ^ (4 : ℤ) * (a1 ^ (m : ℕ))⁻¹ ≤ (URec m : ℝ) := by
  have ha0 := a1_spec.1; have ha1 := a1_spec.2.1; have ha_eq := a1_spec.2.2
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 =>
      simp only [URec, Nat.cast_one, pow_zero, inv_one, mul_one, zpow_ofNat]
      have : a1 ^ 4 ≤ 1 ^ 4 := by gcongr
      simpa using this
    | 1 =>
      simp only [URec, Nat.cast_one, pow_one, zpow_ofNat]; have h3 : a1 ^ 4 * a1⁻¹ = a1 ^ 3 := by field_simp
      rw [h3]
      have : a1 ^ 3 ≤ 1 ^ 3 := by gcongr
      simpa using this
    | 2 =>
      simp only [URec, Nat.cast_one, zpow_ofNat]; have h2 : a1 ^ 4 * (a1 ^ 2)⁻¹ = a1 ^ 2 := by field_simp
      rw [h2]
      have : a1 ^ 2 ≤ 1 ^ 2 := by gcongr
      simpa using this
    | 3 =>
      simp only [URec, Nat.cast_one, zpow_ofNat]; have h1 : a1 ^ 4 * (a1 ^ 3)⁻¹ = a1 := by field_simp
      rw [h1]; exact ha1.le
    | 4 =>
      simp only [URec, Nat.cast_one, zpow_ofNat]
      have : a1 ^ 4 * (a1 ^ 4)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
      rw [this]
    | m + 5 =>
      have h1 := ih (m + 4) (by omega)
      have h4 := ih (m + 1) (by omega)
      unfold URec; push_cast
      have hid : a1 ^ (4 : ℤ) * (a1 ^ (m + 5))⁻¹ =
          a1 ^ (4 : ℤ) * (a1 ^ (m + 4))⁻¹ + a1 ^ (4 : ℤ) * (a1 ^ (m + 1))⁻¹ := by
        have hsum : (a1 ^ (m + 4))⁻¹ + (a1 ^ (m + 1))⁻¹ =
            (a1 + a1 ^ 4) * (a1 ^ (m + 5))⁻¹ := by
          field_simp; ring
        calc a1 ^ (4 : ℤ) * (a1 ^ (m + 5))⁻¹
            = a1 ^ (4 : ℤ) * (1 * (a1 ^ (m + 5))⁻¹) := by ring
          _ = a1 ^ (4 : ℤ) * ((a1 + a1 ^ 4) * (a1 ^ (m + 5))⁻¹) := by rw [ha_eq]
          _ = a1 ^ (4 : ℤ) * ((a1 ^ (m + 4))⁻¹ + (a1 ^ (m + 1))⁻¹) := by rw [← hsum]
          _ = a1 ^ (4 : ℤ) * (a1 ^ (m + 4))⁻¹ + a1 ^ (4 : ℤ) * (a1 ^ (m + 1))⁻¹ := by ring
      linarith
/-- Add `4` to the last element of a non-empty list, turning a `UList (m - 4)` element into a `ValidTail` of -/
def add4Last : List ℕ → List ℕ
  | [] => []
  | [w] => [w + 4]
  | w :: ws => w :: add4Last ws
lemma add4Last_ne_nil {l : List ℕ} (h : l ≠ []) : add4Last l ≠ [] := by
  cases l with
  | nil => exact absurd rfl h
  | cons w ws => cases ws <;> simp [add4Last]
lemma add4Last_inj : Function.Injective add4Last := by
  intro a b h
  induction a generalizing b with
  | nil => cases b with | nil => rfl | cons w ws => cases ws <;> simp [add4Last] at h
  | cons wa ra ih =>
    cases ra with
    | nil =>
      cases b with
      | nil => simp [add4Last] at h
      | cons wb rb =>
        cases rb with
        | nil =>
          simp only [add4Last, List.cons.injEq, and_true] at h; rw [show wa = wb by omega]
        | cons wb2 rb2 =>
          simp only [add4Last, List.cons.injEq] at h; exact absurd h.2.symm (add4Last_ne_nil (by simp))
    | cons wa2 ra2 =>
      cases b with
      | nil => simp [add4Last] at h
      | cons wb rb =>
        cases rb with
        | nil =>
          simp only [add4Last, List.cons.injEq] at h; exact absurd h.2 (add4Last_ne_nil (by simp))
        | cons wb2 rb2 =>
          simp only [add4Last, List.cons.injEq] at h; rw [h.1, ih h.2]
lemma add4Last_valid {l : List ℕ} (hne : l ≠ []) (hmod : ∀ w ∈ l, w % 4 = 1) :
    ValidTail (add4Last l) ∧ (add4Last l).sum = l.sum + 4 := by
  induction l with
  | nil => exact absurd rfl hne
  | cons w rest ih =>
    cases rest with
    | nil =>
      have hw : w % 4 = 1 := hmod w (by simp)
      refine ⟨ValidTail.base (by omega) (by omega), by simp [add4Last]⟩
    | cons w2 rest2 =>
      have hw : w % 4 = 1 := hmod w (by simp)
      obtain ⟨hvt, hsum⟩ := ih (by simp) (fun u hu => hmod u (by simp [hu]))
      refine ⟨ValidTail.cons hw hvt, ?_⟩
      simp only [add4Last, List.sum_cons, hsum]; omega
/-- Theorem 10 (Lower bound): there is `c > 0` (explicitly `c = a_1^9`) such that `c * X^γ ≤ N1(X)` for every -/
theorem thm_basin1_lower : ∃ c : ℝ, 0 < c ∧ ∀ X : ℕ, 1 ≤ X → c * (X : ℝ) ^ gamma ≤ (N1 X : ℝ) := by
  classical
  have ha0 := a1_spec.1; have ha1 := a1_spec.2.1
  refine ⟨a1 ^ 9, by positivity, fun X hX => ?_⟩
  by_cases hX32 : X < 32
  · have hN1 : (1 : ℝ) ≤ (N1 X : ℝ) := by
      have : 1 ≤ N1 X := by
        unfold N1
        refine Finset.card_pos.mpr ⟨1, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨le_rfl, hX⟩, by decide, reaches_refl f 1⟩
      exact_mod_cast this
    have hXlt : (X : ℝ) ^ gamma ≤ (32 : ℝ) ^ gamma :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hX32.le) gamma_pos.le
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
  · have hge32 : 32 ≤ X := by omega
    set M := Nat.log 2 X
    have hM5 : 5 ≤ M := by
      have h5 : 2 ^ 5 ≤ X := by omega
      exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr h5
    have h2M_le : 2 ^ M ≤ X := Nat.pow_log_le_self 2 (by omega)
    have hX_lt : X < 2 ^ (M + 1) := Nat.lt_pow_succ_log_self (by norm_num) X
    have hcard_le : (UList (M - 4)).card ≤ N1 X := by
      unfold N1
      refine Finset.card_le_card_of_injOn (fun l => chainVal (add4Last l)) ?_ ?_
      · intro l hl; obtain ⟨hmod, hsum, hne⟩ := UList_props (M - 4) l hl
        obtain ⟨hvt, hsum'⟩ := add4Last_valid (hne (by omega)) hmod
        obtain ⟨h30, hgt1, hreach, hlt2⟩ := chainVal_props hvt
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]; have hsumM : (add4Last l).sum = M := by omega
        rw [hsumM] at hlt2; exact ⟨⟨by omega, by omega⟩, by omega, hreach⟩
      · intro a ha b hb h; obtain ⟨hmoda, _, hnea⟩ := UList_props (M - 4) a ha
        obtain ⟨hmodb, _, hneb⟩ := UList_props (M - 4) b hb; have hvta := (add4Last_valid (hnea (by omega)) hmoda).1
        have hvtb := (add4Last_valid (hneb (by omega)) hmodb).1
        exact add4Last_inj (chainVal_inj hvta hvtb h)
    have hU : a1 ^ (4 : ℤ) * (a1 ^ (M - 4))⁻¹ ≤ (N1 X : ℝ) := by
      calc a1 ^ (4 : ℤ) * (a1 ^ (M - 4))⁻¹
          ≤ (URec (M - 4) : ℝ) := URec_lower (M - 4)
        _ = ((UList (M - 4)).card : ℝ) := by rw [UList_card]
        _ ≤ (N1 X : ℝ) := by exact_mod_cast hcard_le
    have hXpow : (X : ℝ) ^ gamma ≤ ((2 : ℝ) ^ ((M + 1 : ℕ) : ℝ)) ^ gamma := by
      have : (X : ℝ) ≤ (2 : ℝ) ^ (M + 1 : ℕ) := by exact_mod_cast hX_lt.le
      calc (X : ℝ) ^ gamma ≤ ((2 : ℝ) ^ (M + 1 : ℕ)) ^ gamma := Real.rpow_le_rpow (by positivity) this gamma_pos.le
        _ = ((2 : ℝ) ^ ((M + 1 : ℕ) : ℝ)) ^ gamma := by rw [Real.rpow_natCast]
    have h2pow : ((2 : ℝ) ^ ((M + 1 : ℕ) : ℝ)) ^ gamma = (a1 ^ (M + 1))⁻¹ := by
      rw [← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
          two_rpow_gamma, Real.rpow_natCast, one_div, inv_pow]
    have hEq : a1 ^ 9 * (a1 ^ (M + 1))⁻¹ = a1 ^ (4 : ℤ) * (a1 ^ (M - 4))⁻¹ := by
      have hMsplit : M + 1 = (M - 4) + 5 := by omega
      rw [hMsplit, pow_add, zpow_ofNat]; field_simp
    calc a1 ^ 9 * (X : ℝ) ^ gamma
        ≤ a1 ^ 9 * ((2 : ℝ) ^ ((M + 1 : ℕ) : ℝ)) ^ gamma := mul_le_mul_of_nonneg_left hXpow (by positivity)
      _ = a1 ^ 9 * (a1 ^ (M + 1))⁻¹ := by rw [h2pow]
      _ = a1 ^ (4 : ℤ) * (a1 ^ (M - 4))⁻¹ := hEq
      _ ≤ (N1 X : ℝ) := hU

/-! ### Part 10.3: Upper bound `N1(X) ≤ 2.44 * X^β` and density zero -/
/-- One odd-to-odd step `(v, o)` with `d(n) * n + 1 = 2^v * o` and `o` odd. -/
def oddStep (n : ℕ) : ℕ × ℕ := splitTwo (d n * n + 1)
lemma oddStep_spec {n : ℕ} (hn : n % 2 = 1) :
    1 ≤ (oddStep n).1 ∧ (oddStep n).2 % 2 = 1 ∧
    d n * n + 1 = 2 ^ (oddStep n).1 * (oddStep n).2 := by
  unfold oddStep; have hpos : 0 < d n * n + 1 := by omega
  have hev : (d n * n + 1) % 2 = 0 := by have := f_odd_even hn; rwa [f_odd hn] at this
  obtain ⟨hodd, heq⟩ := splitTwo_spec hpos; exact ⟨splitTwo_pos_of_even hpos hev, hodd, heq⟩
/-- Terras-type valuation word `phiWord K n = [v_1, ..., v_j]` with sum `< K`. -/
def phiWord : ℕ → ℕ → List ℕ
  | 0, _ => []
  | 1, _ => []
  | K + 2, n =>
    if hv : 1 ≤ (oddStep n).1 ∧ (oddStep n).1 < K + 2 then
      (oddStep n).1 :: phiWord (K + 2 - (oddStep n).1) (oddStep n).2
    else []
termination_by K _ => K
decreasing_by
  simp_wf
  have := hv.1
  omega
lemma phiWord_sum_lt (K n : ℕ) (hK : 1 ≤ K) : (phiWord K n).sum < K := by
  induction K using Nat.strong_induction_on generalizing n with
  | h K ih =>
    match K with
    | 0 => omega
    | 1 => simp [phiWord]
    | K + 2 =>
      unfold phiWord
      split_ifs with hv
      · simp only [List.sum_cons]; have hrec := ih (K + 2 - (oddStep n).1) (by omega) (oddStep n).2 (by omega)
        omega
      · simp
/-- Key Terras injectivity lemma modulo `15 * 2^K`: two odd integers with the same residue mod `15` and the same -/
lemma phiWord_inj_mod (K : ℕ) (hK : 1 ≤ K) :
    ∀ n m : ℕ, n % 2 = 1 → m % 2 = 1 → n % 15 = m % 15 →
      phiWord K n = phiWord K m → n % (15 * 2 ^ K) = m % (15 * 2 ^ K) := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    match K with
    | 0 => omega
    | 1 =>
      intro n m hn hm h15 _
      have : 15 * 2 ^ 1 = 30 := by norm_num
      rw [this]; omega
    | K + 2 =>
      intro n m hn hm h15 hphi; have hd : d n = d m := by unfold d; omega
      have hd_odd : d n % 2 = 1 := by unfold d; omega
      obtain ⟨hvn1, hon_odd, hfac_n⟩ := oddStep_spec hn; obtain ⟨hvm1, hom_odd, hfac_m⟩ := oddStep_spec hm
      set vn := (oddStep n).1; set on := (oddStep n).2; set vm := (oddStep m).1; set om := (oddStep m).2
      have hcop_d : Nat.Coprime (d n) (2 ^ (K + 2)) := by
        have : Nat.Coprime (d n) 2 := by rw [Nat.coprime_two_right]; exact Nat.odd_iff.mpr hd_odd
        exact this.pow_right (K + 2)
      have hcop_15 : Nat.Coprime 15 (2 ^ (K + 2)) := (show Nat.Coprime 15 2 by decide).pow_right (K + 2)
      have hmod2K : n % (2 ^ (K + 2)) = m % (2 ^ (K + 2)) := by
        have hdn_mod : (d n * n + 1) % (2 ^ (K + 2)) = (d n * m + 1) % (2 ^ (K + 2)) := by
          unfold phiWord at hphi
          by_cases hcn : 1 ≤ (oddStep n).1 ∧ (oddStep n).1 < K + 2
          · by_cases hcm : 1 ≤ (oddStep m).1 ∧ (oddStep m).1 < K + 2
            · simp [hcn, hcm] at hphi; obtain ⟨hv_eq, hrest⟩ := hphi
              have hon15 : on % 15 = om % 15 := by
                have h2v_mod : (2 ^ vn * on) % 15 = (2 ^ vn * om) % 15 := by
                  have hv' : vn = vm := hv_eq; rw [← hfac_n, hv', ← hfac_m, ← hd]
                  simp [Nat.add_mod, Nat.mul_mod, h15]
                have hcop2 : Nat.Coprime (2 ^ vn) 15 := (show Nat.Coprime 2 15 by decide).pow_left vn
                exact Nat.ModEq.cancel_left_of_coprime hcop2.symm h2v_mod
              rw [hv_eq] at hrest
              have hrec := ih (K + 2 - vm) (by omega) (by omega) on om hon_odd hom_odd hon15 hrest
              have hom_2 : on % (2 ^ (K + 2 - vm)) = om % (2 ^ (K + 2 - vm)) := Nat.ModEq.of_mul_left 15 hrec
              have hv' : vn = vm := hv_eq; rw [hfac_n, hd, hfac_m, hv']
              have hsplit : 2 ^ (K + 2) = 2 ^ vm * 2 ^ (K + 2 - vm) := by rw [← pow_add, Nat.add_sub_of_le (by omega)]
              rw [hsplit, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hom_2]
            · simp [hcn, hcm] at hphi
          · by_cases hcm : 1 ≤ (oddStep m).1 ∧ (oddStep m).1 < K + 2
            · simp [hcn, hcm] at hphi
            · have hge_n : K + 2 ≤ vn := by omega
              have hge_m : K + 2 ≤ vm := by omega
              rw [hfac_n, hd, hfac_m]
              have hdn0 : (2 ^ vn * on) % (2 ^ (K + 2)) = 0 := by
                have : 2 ^ (K + 2) ∣ 2 ^ vn * on := dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hge_n) on
                exact Nat.mod_eq_zero_of_dvd this
              have hdm0 : (2 ^ vm * om) % (2 ^ (K + 2)) = 0 := by
                have : 2 ^ (K + 2) ∣ 2 ^ vm * om := dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hge_m) om
                exact Nat.mod_eq_zero_of_dvd this
              rw [hdn0, hdm0]
        have hmul_eq : (d n * n) % (2 ^ (K + 2)) = (d n * m) % (2 ^ (K + 2)) := by
          exact Nat.ModEq.add_right_cancel' 1 hdn_mod
        exact Nat.ModEq.cancel_left_of_coprime hcop_d.symm hmul_eq
      exact (Nat.modEq_and_modEq_iff_modEq_mul hcop_15).mp ⟨h15, hmod2K⟩
/-- Class index `0 = A (1 mod 30)`, `1 = B (15 mod 30)`, `2 = C (17 mod 30)`. -/
def clsIdx (n : ℕ) : Fin 3 := if n % 30 = 1 then 0 else if n % 30 = 15 then 1 else 2
/-- Admissible transition predicate `(c → c', v)` on `{A, B, C}`. -/
def admEdge (c c' : Fin 3) (v : ℕ) : Bool :=
  1 ≤ v &&
  match c.val, c'.val with
  | 0, 0 => v % 4 == 1
  | 0, 2 => v % 4 == 0
  | 1, 0 => v % 4 == 0
  | 1, 2 => v % 4 == 3
  | 2, 1 => true
  | _, _ => false
private lemma admEdge_table :
    ∀ r : Fin 30, (r.val = 1 ∨ r.val = 15 ∨ r.val = 17) →
      ∀ v4 : Fin 4, ∀ q : Fin 3,
        let v := if v4.val = 0 then 4 else v4.val; let o := [1, 15, 17].get q
        ((r.val % 10) * r.val + 1) % 30 = (2 ^ v * o) % 30 →
        admEdge (clsIdx r.val) q v = true := by
  decide
lemma oddStep_admEdge {n : ℕ} (hn : InABC n) (ho : InABC (oddStep n).2) :
    admEdge (clsIdx n) (clsIdx (oddStep n).2) (oddStep n).1 = true := by
  have hn_odd : n % 2 = 1 := by simp only [InABC, InA, InB, InC] at hn; omega
  obtain ⟨hv1, _, hfac⟩ := oddStep_spec hn_odd; set v := (oddStep n).1; set o := (oddStep n).2
  have h2v_mod : 2 ^ v % 30 = 2 ^ (if v % 4 = 0 then 4 else v % 4) % 30 := by
    have h4 : v = 4 * ((v - 1) / 4) + (if v % 4 = 0 then 4 else v % 4) := by
      split_ifs <;> omega
    conv_lhs => rw [h4, pow_add, Nat.mul_mod]
    have h15 := two_pow_mod_15_of_four_dvd (dvd_mul_right 4 ((v - 1) / 4))
    have h30 : 2 ^ (4 * ((v - 1) / 4)) % 30 = 1 ∨ 2 ^ (4 * ((v - 1) / 4)) % 30 = 16 := by omega
    have hv4_lt : v % 4 < 4 := Nat.mod_lt v (by omega)
    rcases h30 with h30 | h30 <;> (rw [h30]; interval_cases (v % 4) <;> decide)
  have hr : n % 30 = 1 ∨ n % 30 = 15 ∨ n % 30 = 17 := hn
  have hcls_n : clsIdx n = clsIdx (n % 30) := by unfold clsIdx; simp
  have hq : ∃ q : Fin 3, [1, 15, 17].get q = o % 30 ∧ clsIdx o = q := by
    simp only [InABC, InA, InB, InC] at ho
    rcases ho with h | h | h
    · exact ⟨0, h.symm, by unfold clsIdx; simp [h]⟩
    · exact ⟨1, h.symm, by unfold clsIdx; simp [h]⟩
    · exact ⟨2, h.symm, by unfold clsIdx; simp [h]⟩
  obtain ⟨q, hq_val, hq_cls⟩ := hq
  have hmod : (((n % 30) % 10) * (n % 30) + 1) % 30 =
      (2 ^ (if v % 4 = 0 then 4 else v % 4) * [1, 15, 17].get q) % 30 := by
    have h1 : (d n * n + 1) % 30 = (((n % 30) % 10) * (n % 30) + 1) % 30 := by
      have : d n = (n % 30) % 10 := by unfold d; omega
      rw [this]; simp [Nat.add_mod, Nat.mul_mod]
    have hq_lt : [1, 15, 17].get q < 30 := by fin_cases q <;> decide
    rw [← h1, hfac, Nat.mul_mod, h2v_mod, ← hq_val, ← Nat.mod_eq_of_lt hq_lt, ← Nat.mul_mod,
        Nat.mod_eq_of_lt hq_lt]
  have htab := admEdge_table ⟨n % 30, Nat.mod_lt n (by omega)⟩ hr ⟨v % 4, Nat.mod_lt v (by omega)⟩ q hmod
  rw [hcls_n, hq_cls]
  have hv_mod : (if v % 4 = 0 then 4 else v % 4) % 4 = v % 4 := by
    split_ifs with h <;> simp [h]
  unfold admEdge at htab ⊢; have hv1' : decide (1 ≤ v) = true := by simp [hv1]
  have hv1'' : decide (1 ≤ if v % 4 = 0 then 4 else v % 4) = true := by
    split_ifs with h
    · simp
    · simp; omega
  simp only [hv1', hv1'', Bool.true_and, hv_mod] at htab ⊢; exact htab
/-- Finite set of admissible words of exact sum `L` starting from class `c ∈ {A, B, C}`. -/
def admWords : Fin 3 → ℕ → Finset (List ℕ)
  | _, 0 => {[]}
  | c, L + 1 =>
    (Finset.Icc 1 (L + 1)).attach.biUnion fun ⟨v, hv⟩ =>
      Finset.univ.biUnion fun c' : Fin 3 => if admEdge c c' v then (admWords c' (L + 1 - v)).image (v :: ·) else ∅
termination_by _ L => L
decreasing_by
  simp_wf
  have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1; omega
lemma phiWord_mem_admWords (K : ℕ) (hK : 1 ≤ K) :
    ∀ n : ℕ, n % 2 = 1 → Reaches f n 1 →
      phiWord K n ∈ admWords (clsIdx n) (phiWord K n).sum := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    match K with
    | 0 => omega
    | 1 => intro n _ _; simp [phiWord, admWords]
    | K + 2 =>
      intro n hn hreach; unfold phiWord
      split_ifs with hv
      · have hABC_n : InABC n := thm_residue_law hn hreach; obtain ⟨hv1, ho_odd, hfac⟩ := oddStep_spec hn
        set v := (oddStep n).1; set o := (oddStep n).2
        have hreach_o : Reaches f o 1 := by
          rcases hreach with ⟨k, hk⟩
          cases k with
          | zero =>
            simp only [Function.iterate_zero, id_eq] at hk; subst hk
            have : o = 1 := by simp [o, oddStep, d, splitTwo]
            rw [this]; exact reaches_refl f 1
          | succ k =>
            rw [Function.iterate_succ_apply, f_odd hn, hfac] at hk
            exact ⟨k - v, (f_iter_two_pow_eq_odd (by decide) hk).2⟩
        have hABC_o : InABC o := thm_residue_law ho_odd hreach_o
        have hedge : admEdge (clsIdx n) (clsIdx o) v = true := oddStep_admEdge hABC_n hABC_o
        have hrec := ih (K + 2 - v) (by omega) (by omega) o ho_odd hreach_o
        set rest := phiWord (K + 2 - v) o
        have hsum : (v :: rest).sum = (v + rest.sum - 1) + 1 := by simp; omega
        rw [hsum]; unfold admWords
        simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists,
          Finset.mem_Icc, Finset.mem_univ]
        refine ⟨v, ⟨hv.1, by omega⟩, clsIdx o, ?_⟩
        simp only [hedge, ↓reduceIte, Finset.mem_image]
        refine ⟨rest, ?_, rfl⟩
        have hsub : v + rest.sum - 1 + 1 - v = rest.sum := by omega
        rw [hsub]; exact hrec
      · simp [admWords]
/-- True Perron right eigenvector `h = (h_A, h_B, h_C)` of `M_0(a*)` scaled so `h_B = 1`. -/
noncomputable def perronH (c : Fin 3) : ℝ :=
  match c.val with
  | 0 => aStar ^ 5 / ((1 - aStar) * (1 - aStar - aStar ^ 4))
  | 1 => 1
  | _ => aStar / (1 - aStar)
lemma perronH_0 : perronH 0 = aStar ^ 5 / ((1 - aStar) * (1 - aStar - aStar ^ 4)) := rfl
lemma perronH_1 : perronH 1 = 1 := rfl
lemma perronH_2 : perronH 2 = aStar / (1 - aStar) := rfl
lemma aStar_denom_pos : 0 < 1 - aStar ∧ 0 < 1 - aStar ^ 4 ∧ 0 < 1 - aStar - aStar ^ 4 := by
  obtain ⟨_, hhi⟩ := aStar_bounds; have ha0 := aStar_spec.1
  have h4 : aStar ^ 4 < (6477989 / 10000000 : ℝ) ^ 4 := by gcongr
  refine ⟨by linarith, by linarith [show (6477989 / 10000000 : ℝ) ^ 4 < 1 by norm_num], ?_⟩
  linarith [show (6477989 / 10000000 : ℝ) + (6477989 / 10000000 : ℝ) ^ 4 < 1 by norm_num]
/-- Exact quartic factorization of the characteristic equation: -/
theorem aStar_quartic : aStar + 2 * aStar ^ 4 = 1 := by
  obtain ⟨hd1, hd2, _⟩ := aStar_denom_pos; have hroot := aStar_spec.2.2
  have hfac : (1 - aStar - 2 * aStar ^ 4) * ((1 - aStar) * (1 - aStar ^ 4)) = 0 := by
    linarith [show (1 - aStar - aStar ^ 4) * ((1 - aStar) * (1 - aStar ^ 4) - aStar ^ 4) - aStar ^ 9 =
      (1 - aStar - 2 * aStar ^ 4) * ((1 - aStar) * (1 - aStar ^ 4)) by ring]
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · exact absurd h (ne_of_gt (mul_pos hd1 hd2))
/-- Because `a* + 2*(a*)^4 = 1`, we have `1 - a* - (a*)^4 = (a*)^4` identically, so `h_A = h_C = a* / (1 - a*)` -/
theorem perronH_A_eq_C : perronH 0 = perronH 2 := by
  obtain ⟨hd1, _, hd3⟩ := aStar_denom_pos; have hq := aStar_quartic
  have hsub : 1 - aStar - aStar ^ 4 = aStar ^ 4 := by linarith
  have hne1 : 1 - aStar ≠ 0 := ne_of_gt hd1; have ha4 : aStar ^ 4 ≠ 0 := by linarith
  rw [perronH_0, perronH_2, hsub]; field_simp
lemma perronH_ge_one (c : Fin 3) : 1 ≤ perronH c := by
  obtain ⟨hlo, hhi⟩ := aStar_bounds; obtain ⟨hd1, _, hd3⟩ := aStar_denom_pos; have ha0 := aStar_spec.1
  fin_cases c
  · simp only [perronH]; rw [one_le_div (mul_pos hd1 hd3)]
    have h5 : (64779885 / 100000000 : ℝ) ^ 5 < aStar ^ 5 := by gcongr
    have hprod : (1 - aStar) * (1 - aStar - aStar ^ 4) ≤
        (1 - 64779885 / 100000000 : ℝ) * (1 - 64779885 / 100000000 - (64779885 / 100000000) ^ 4) := by
      have h4lo : (64779885 / 100000000 : ℝ) ^ 4 < aStar ^ 4 := by gcongr
      exact mul_le_mul (by linarith) (by linarith) hd3.le (by norm_num)
    linarith [show (1 - 64779885 / 100000000 : ℝ) *
        (1 - 64779885 / 100000000 - (64779885 / 100000000) ^ 4) <
        (64779885 / 100000000 : ℝ) ^ 5 by norm_num]
  · simp [perronH]
  · simp only [perronH]; rw [one_le_div hd1]; linarith
lemma finite_geom_step4_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (r L : ℕ)
    (hr1 : 1 ≤ r) (hr4 : r ≤ 4) :
    ∑ v ∈ (Finset.Icc 1 L).filter (fun v => v % 4 = r % 4), a ^ v ≤ a ^ r / (1 - a ^ 4) := by
  have ha4 : a ^ 4 < 1 := by
    calc a ^ 4 < 1 ^ 4 := by gcongr
      _ = 1 := by norm_num
  have h1a4 : 0 < 1 - a ^ 4 := by linarith
  have hsub : (Finset.Icc 1 L).filter (fun v => v % 4 = r % 4) ⊆
      (Finset.range (L + 1)).image (fun j => r + 4 * j) := by
    intro v hv; simp only [Finset.mem_filter, Finset.mem_Icc] at hv
    simp only [Finset.mem_image, Finset.mem_range]; refine ⟨(v - r) / 4, by omega, by omega⟩
  have hsum_le : ∑ v ∈ (Finset.Icc 1 L).filter (fun v => v % 4 = r % 4), a ^ v ≤
      ∑ v ∈ (Finset.range (L + 1)).image (fun j => r + 4 * j), a ^ v :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have himg : ∑ v ∈ (Finset.range (L + 1)).image (fun j => r + 4 * j), a ^ v =
      a ^ r * ∑ j ∈ Finset.range (L + 1), (a ^ 4) ^ j := by
    rw [Finset.sum_image (fun x _ y _ h => by omega), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add, pow_mul]
  have hgeom : ∑ j ∈ Finset.range (L + 1), (a ^ 4) ^ j ≤ 1 / (1 - a ^ 4) := by
    rw [geom_sum_eq (ne_of_lt ha4)]; have hnn : 0 ≤ (a ^ 4) ^ (L + 1) := by positivity
    have hneg : (a ^ 4) ^ (L + 1) - 1 = -(1 - (a ^ 4) ^ (L + 1)) := by ring
    have hneg2 : a ^ 4 - 1 = -(1 - a ^ 4) := by ring
    rw [hneg, hneg2, neg_div_neg_eq]; exact div_le_div_of_nonneg_right (by linarith) h1a4.le
  calc ∑ v ∈ (Finset.Icc 1 L).filter (fun v => v % 4 = r % 4), a ^ v
      ≤ a ^ r * ∑ j ∈ Finset.range (L + 1), (a ^ 4) ^ j := hsum_le.trans_eq himg
    _ ≤ a ^ r * (1 / (1 - a ^ 4)) := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = a ^ r / (1 - a ^ 4) := by ring
lemma finite_geom_step1_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (L : ℕ) :
    ∑ v ∈ Finset.Icc 1 L, a ^ v ≤ a / (1 - a) := by
  have h1a : 0 < 1 - a := by linarith
  have hsub : Finset.Icc 1 L ⊆ (Finset.range (L + 1)).image (fun j => 1 + j) := by
    intro v hv; simp only [Finset.mem_Icc] at hv
    simp only [Finset.mem_image, Finset.mem_range]; exact ⟨v - 1, by omega, by omega⟩
  have hsum_le : ∑ v ∈ Finset.Icc 1 L, a ^ v ≤
      ∑ v ∈ (Finset.range (L + 1)).image (fun j => 1 + j), a ^ v :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have himg : ∑ v ∈ (Finset.range (L + 1)).image (fun j => 1 + j), a ^ v =
      a * ∑ j ∈ Finset.range (L + 1), a ^ j := by
    rw [Finset.sum_image (fun x _ y _ h => by omega), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add, pow_one]
  have hgeom : ∑ j ∈ Finset.range (L + 1), a ^ j ≤ 1 / (1 - a) := by
    rw [geom_sum_eq (ne_of_lt ha1)]; have hnn : 0 ≤ a ^ (L + 1) := by positivity
    have hneg : a ^ (L + 1) - 1 = -(1 - a ^ (L + 1)) := by ring
    have hneg2 : a - 1 = -(1 - a) := by ring
    rw [hneg, hneg2, neg_div_neg_eq]; exact div_le_div_of_nonneg_right (by linarith) h1a.le
  calc ∑ v ∈ Finset.Icc 1 L, a ^ v
      ≤ a * ∑ j ∈ Finset.range (L + 1), a ^ j := hsum_le.trans_eq himg
    _ ≤ a * (1 / (1 - a)) := mul_le_mul_of_nonneg_left hgeom ha0.le
    _ = a / (1 - a) := by ring
lemma perron_eigenvector_eq :
    (aStar / (1 - aStar ^ 4)) * perronH 0 + (aStar ^ 4 / (1 - aStar ^ 4)) * perronH 2 = perronH 0 ∧
    (aStar ^ 4 / (1 - aStar ^ 4)) * perronH 0 + (aStar ^ 3 / (1 - aStar ^ 4)) * perronH 2 = perronH 1 ∧
    (aStar / (1 - aStar)) * perronH 1 = perronH 2 := by
  obtain ⟨hd1, hd2, hd3⟩ := aStar_denom_pos; have hroot := aStar_spec.2.2; have hne1 : 1 - aStar ≠ 0 := ne_of_gt hd1
  have hne2 : 1 - aStar ^ 4 ≠ 0 := ne_of_gt hd2; have hne3 : 1 - aStar - aStar ^ 4 ≠ 0 := ne_of_gt hd3
  refine ⟨?_, ?_, ?_⟩
  · rw [perronH_0, perronH_2]; field_simp; ring
  · rw [perronH_0, perronH_1, perronH_2]; field_simp; linarith
  · rw [perronH_1, perronH_2]; ring
/-- Strong induction: `(a*)^L * |admWords c L| ≤ h_c` for all `L ≥ 0` and `c ∈ {A, B, C}`. -/
lemma admWords_card_bound (L : ℕ) : ∀ c : Fin 3, aStar ^ L * ((admWords c L).card : ℝ) ≤ perronH c := by
  have ha0 := aStar_spec.1; have ha1 := aStar_spec.2.1; obtain ⟨heq0, heq1, heq2⟩ := perron_eigenvector_eq
  induction L using Nat.strong_induction_on with
  | h L ih =>
    intro c
    match L with
    | 0 =>
      have h0 : (admWords c 0).card = 1 := by unfold admWords; simp
      rw [h0, Nat.cast_one, pow_zero, one_mul]; exact perronH_ge_one c
    | L + 1 =>
      have hcard_nat : (admWords c (L + 1)).card ≤
          ∑ v ∈ Finset.Icc 1 (L + 1), ∑ c' : Fin 3,
            if admEdge c c' v then (admWords c' (L + 1 - v)).card else 0 := by
        conv_lhs => unfold admWords
        have h1 : ((Finset.Icc 1 (L + 1)).attach.biUnion fun ⟨v, _⟩ =>
            Finset.univ.biUnion fun c' : Fin 3 =>
              if admEdge c c' v then (admWords c' (L + 1 - v)).image (v :: ·) else ∅).card ≤
            ∑ v ∈ (Finset.Icc 1 (L + 1)).attach, ∑ c' : Fin 3,
              if admEdge c c' v.val then (admWords c' (L + 1 - v.val)).card else 0 := by
          refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun v _ => ?_)
          refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun c' _ => ?_)
          split_ifs
          · exact Finset.card_image_le
          · simp
        refine h1.trans_eq ?_
        exact Finset.sum_attach (Finset.Icc 1 (L + 1)) (fun v =>
          ∑ c' : Fin 3, if admEdge c c' v then (admWords c' (L + 1 - v)).card else 0)
      have hstep : aStar ^ (L + 1) * ((admWords c (L + 1)).card : ℝ) ≤
          ∑ c' : Fin 3,
            (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge c c' v = true), aStar ^ v) *
              perronH c' := by
        have h1 : aStar ^ (L + 1) * ((admWords c (L + 1)).card : ℝ) ≤
            ∑ v ∈ Finset.Icc 1 (L + 1), ∑ c' : Fin 3,
              if admEdge c c' v then aStar ^ (L + 1) * ((admWords c' (L + 1 - v)).card : ℝ)
              else 0 := by
          have hcast : ((admWords c (L + 1)).card : ℝ) ≤
              ∑ v ∈ Finset.Icc 1 (L + 1), ∑ c' : Fin 3,
                if admEdge c c' v then ((admWords c' (L + 1 - v)).card : ℝ) else 0 := by
            have := Nat.cast_le (α := ℝ).mpr hcard_nat
            push_cast at this; simpa using this
          calc aStar ^ (L + 1) * ((admWords c (L + 1)).card : ℝ)
              ≤ aStar ^ (L + 1) * ∑ v ∈ Finset.Icc 1 (L + 1), ∑ c' : Fin 3,
                  if admEdge c c' v then ((admWords c' (L + 1 - v)).card : ℝ) else 0 :=
                mul_le_mul_of_nonneg_left hcast (by positivity)
            _ = ∑ v ∈ Finset.Icc 1 (L + 1), ∑ c' : Fin 3,
                  if admEdge c c' v then aStar ^ (L + 1) * ((admWords c' (L + 1 - v)).card : ℝ)
                  else 0 := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun v _ => ?_
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun c' _ => ?_
                split_ifs <;> ring
        have h2 : ∑ v ∈ Finset.Icc 1 (L + 1), ∑ c' : Fin 3,
              (if admEdge c c' v then aStar ^ (L + 1) * ((admWords c' (L + 1 - v)).card : ℝ) else 0) ≤
            ∑ v ∈ Finset.Icc 1 (L + 1), ∑ c' : Fin 3,
              (if admEdge c c' v then aStar ^ v * perronH c' else 0) := by
          refine Finset.sum_le_sum fun v hv => Finset.sum_le_sum fun c' _ => ?_
          split_ifs with he
          · simp only [Finset.mem_Icc] at hv
            have hpow : aStar ^ (L + 1) = aStar ^ v * aStar ^ (L + 1 - v) := by rw [← pow_add, Nat.add_sub_of_le hv.2]
            rw [hpow, mul_assoc]; exact mul_le_mul_of_nonneg_left (ih (L + 1 - v) (by omega) c') (by positivity)
          · exact le_rfl
        have h3 : ∑ v ∈ Finset.Icc 1 (L + 1), ∑ c' : Fin 3,
              (if admEdge c c' v then aStar ^ v * perronH c' else 0) =
            ∑ c' : Fin 3,
              (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge c c' v = true), aStar ^ v) *
                perronH c' := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c' _ => ?_
          rw [Finset.sum_mul, Finset.sum_filter]
        exact (h1.trans h2).trans_eq h3
      refine hstep.trans ?_
      rw [Fin.sum_univ_three]; have hp0 : 0 ≤ perronH 0 := by linarith [perronH_ge_one 0]
      have hp1 : 0 ≤ perronH 1 := by linarith [perronH_ge_one 1]
      have hp2 : 0 ≤ perronH 2 := by linarith [perronH_ge_one 2]
      fin_cases c
      ·
        dsimp only
        change (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 0 0 v = true), aStar ^ v) *
              perronH 0 +
            (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 0 1 v = true), aStar ^ v) *
              perronH 1 +
            (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 0 2 v = true), aStar ^ v) *
              perronH 2 ≤ perronH 0
        have hf0 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 0 0 v = true) =
            (Finset.Icc 1 (L + 1)).filter (fun v => v % 4 = 1 % 4) := by
          refine Finset.filter_congr fun v hv => ?_
          have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1; simp [admEdge, hv1]
        have hf1 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 0 1 v = true) = ∅ :=
          Finset.filter_eq_empty_iff.mpr fun v _ => by simp [admEdge]
        have hf2 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 0 2 v = true) =
            (Finset.Icc 1 (L + 1)).filter (fun v => v % 4 = 4 % 4) := by
          refine Finset.filter_congr fun v hv => ?_
          have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1; simp [admEdge, hv1]
        rw [hf0, hf1, hf2, Finset.sum_empty, zero_mul, add_zero]
        have hg0 := finite_geom_step4_le ha0 ha1 1 (L + 1) (by omega) (by omega)
        have hg2 := finite_geom_step4_le ha0 ha1 4 (L + 1) (by omega) (by omega)
        rw [pow_one] at hg0
        calc (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => v % 4 = 1 % 4), aStar ^ v) * perronH 0 +
              (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => v % 4 = 4 % 4), aStar ^ v) * perronH 2
            ≤ (aStar / (1 - aStar ^ 4)) * perronH 0 + (aStar ^ 4 / (1 - aStar ^ 4)) * perronH 2 :=
              add_le_add (mul_le_mul_of_nonneg_right hg0 hp0) (mul_le_mul_of_nonneg_right hg2 hp2)
          _ = perronH 0 := heq0
      ·
        dsimp only
        change (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 1 0 v = true), aStar ^ v) *
              perronH 0 +
            (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 1 1 v = true), aStar ^ v) *
              perronH 1 +
            (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 1 2 v = true), aStar ^ v) *
              perronH 2 ≤ perronH 1
        have hf0 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 1 0 v = true) =
            (Finset.Icc 1 (L + 1)).filter (fun v => v % 4 = 4 % 4) := by
          refine Finset.filter_congr fun v hv => ?_
          have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1; simp [admEdge, hv1]
        have hf1 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 1 1 v = true) = ∅ :=
          Finset.filter_eq_empty_iff.mpr fun v _ => by simp [admEdge]
        have hf2 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 1 2 v = true) =
            (Finset.Icc 1 (L + 1)).filter (fun v => v % 4 = 3 % 4) := by
          refine Finset.filter_congr fun v hv => ?_
          have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1; simp [admEdge, hv1]
        rw [hf0, hf1, hf2, Finset.sum_empty, zero_mul, add_zero]
        have hg0 := finite_geom_step4_le ha0 ha1 4 (L + 1) (by omega) (by omega)
        have hg2 := finite_geom_step4_le ha0 ha1 3 (L + 1) (by omega) (by omega)
        calc (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => v % 4 = 4 % 4), aStar ^ v) * perronH 0 +
              (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => v % 4 = 3 % 4), aStar ^ v) * perronH 2
            ≤ (aStar ^ 4 / (1 - aStar ^ 4)) * perronH 0 + (aStar ^ 3 / (1 - aStar ^ 4)) * perronH 2 :=
              add_le_add (mul_le_mul_of_nonneg_right hg0 hp0) (mul_le_mul_of_nonneg_right hg2 hp2)
          _ = perronH 1 := heq1
      ·
        dsimp only
        change (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 2 0 v = true), aStar ^ v) *
              perronH 0 +
            (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 2 1 v = true), aStar ^ v) *
              perronH 1 +
            (∑ v ∈ (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 2 2 v = true), aStar ^ v) *
              perronH 2 ≤ perronH 2
        have hf0 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 2 0 v = true) = ∅ :=
          Finset.filter_eq_empty_iff.mpr fun v _ => by simp [admEdge]
        have hf1 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 2 1 v = true) =
            Finset.Icc 1 (L + 1) :=
          Finset.filter_true_of_mem fun v hv => by
            have hv1 : 1 ≤ v := (Finset.mem_Icc.mp hv).1; simp [admEdge, hv1]
        have hf2 : (Finset.Icc 1 (L + 1)).filter (fun v => admEdge 2 2 v = true) = ∅ :=
          Finset.filter_eq_empty_iff.mpr fun v _ => by simp [admEdge]
        rw [hf0, hf1, hf2, Finset.sum_empty, zero_mul, zero_add, zero_mul, add_zero]
        have hg1 := finite_geom_step1_le ha0 ha1 (L + 1)
        calc (∑ v ∈ Finset.Icc 1 (L + 1), aStar ^ v) * perronH 1
            ≤ (aStar / (1 - aStar)) * perronH 1 := mul_le_mul_of_nonneg_right hg1 hp1
          _ = perronH 2 := heq2
/-- Leading constant `C_W = (h_A + h_B + h_C) * a* / (1 - a*) ≈ 8.6052`. -/
noncomputable def constCW : ℝ := (perronH 0 + perronH 1 + perronH 2) * aStar / (1 - aStar)
lemma constCW_lt : constCW < 86053 / 10000 := by
  obtain ⟨hlo, hhi⟩ := aStar_bounds; obtain ⟨hd1, _, hd3⟩ := aStar_denom_pos; have ha0 := aStar_spec.1
  have h0_lt : perronH 0 < 18393 / 10000 := by
    rw [perronH_0, div_lt_iff₀ (mul_pos hd1 hd3)]
    have h5 : aStar ^ 5 < (6477989 / 10000000 : ℝ) ^ 5 := by gcongr
    have h4 : aStar ^ 4 < (6477989 / 10000000 : ℝ) ^ 4 := by gcongr
    have hd_lo : (1 - 6477989 / 10000000 : ℝ) *
        (1 - 6477989 / 10000000 - (6477989 / 10000000) ^ 4) <
        (1 - aStar) * (1 - aStar - aStar ^ 4) :=
      mul_lt_mul'' (by linarith) (by linarith) (by norm_num) (by norm_num)
    linarith [show (6477989 / 10000000 : ℝ) ^ 5 < (18393 / 10000 : ℝ) *
        ((1 - 6477989 / 10000000 : ℝ) *
          (1 - 6477989 / 10000000 - (6477989 / 10000000) ^ 4)) by norm_num]
  have h2_lt : perronH 2 < 18393 / 10000 := by rw [perronH_2, div_lt_iff₀ hd1]; linarith
  have h1_eq : perronH 1 = 1 := rfl; unfold constCW; rw [div_lt_iff₀ hd1]
  have hsum : perronH 0 + perronH 1 + perronH 2 < 46786 / 10000 := by linarith
  have hnn : 0 ≤ perronH 0 + perronH 1 + perronH 2 := by
    linarith [perronH_ge_one 0, perronH_ge_one 1, perronH_ge_one 2]
  have hmul : (perronH 0 + perronH 1 + perronH 2) * aStar <
      (46786 / 10000 : ℝ) * (6477989 / 10000000 : ℝ) :=
    mul_lt_mul'' hsum hhi hnn ha0.le
  linarith [show (46786 / 10000 : ℝ) * (6477989 / 10000000 : ℝ) <
      (86053 / 10000 : ℝ) * (1 - 6477989 / 10000000 : ℝ) by norm_num]
/-- Block upper bound: `N1(15 * 2^K) ≤ C_W * 2^(β * K)` for every `K ≥ 1`. -/
lemma N1_block_bound (K : ℕ) (hK : 1 ≤ K) : (N1 (15 * 2 ^ K) : ℝ) ≤ constCW * (2 : ℝ) ^ (beta * (K : ℝ)) := by
  classical
  have ha0 := aStar_spec.1; have ha1 := aStar_spec.2.1; obtain ⟨hd1, _, _⟩ := aStar_denom_pos
  let WSet : Finset (Fin 3 × List ℕ) :=
    Finset.univ.biUnion fun c : Fin 3 => (Finset.range K).biUnion fun L => (admWords c L).image (fun w => (c, w))
  have hN1_le_W : N1 (15 * 2 ^ K) ≤ WSet.card := by
    unfold N1
    refine Finset.card_le_card_of_injOn (fun n => (clsIdx n, phiWord K n)) ?_ ?_
    · intro n hn; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨_, hn_odd, hreach⟩ := hn
      simp only [Finset.mem_coe, WSet, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_range, Finset.mem_image]
      refine ⟨clsIdx n, (phiWord K n).sum, phiWord_sum_lt K n hK, phiWord K n,
        phiWord_mem_admWords K hK n hn_odd hreach, rfl⟩
    · intro a ha b hb h; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
      obtain ⟨⟨_, ha_le⟩, ha_odd, ha_r⟩ := ha
      obtain ⟨⟨_, hb_le⟩, hb_odd, hb_r⟩ := hb
      have hcls : clsIdx a = clsIdx b := congr_arg Prod.fst h
      have hphi : phiWord K a = phiWord K b := congr_arg Prod.snd h; have hABC_a := thm_residue_law ha_odd ha_r
      have hABC_b := thm_residue_law hb_odd hb_r
      have h30 : a % 30 = b % 30 := by
        simp only [InABC, InA, InB, InC] at hABC_a hABC_b
        rcases hABC_a with haA | haB | haC <;> rcases hABC_b with hbA | hbB | hbC <;>
          (unfold clsIdx at hcls; simp_all)
      have h15 : a % 15 = b % 15 := by omega
      have hmod := phiWord_inj_mod K hK a b ha_odd hb_odd h15 hphi
      have hev_top : (15 * 2 ^ K) % 2 = 0 := by
        have : K = (K - 1) + 1 := by omega
        rw [this, pow_succ]; omega
      have ha_lt : a < 15 * 2 ^ K := by omega
      have hb_lt : b < 15 * 2 ^ K := by omega
      rw [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] at hmod; exact hmod
  have hW_card : WSet.card ≤ ∑ L ∈ Finset.range K, ∑ c : Fin 3, (admWords c L).card := by
    rw [Finset.sum_comm]; unfold WSet
    refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun c _ => ?_)
    refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun L _ => ?_)
    exact Finset.card_image_le
  have hW_real : (WSet.card : ℝ) ≤
      (perronH 0 + perronH 1 + perronH 2) * ∑ L ∈ Finset.range K, (1 / aStar) ^ L := by
    have hcast : (WSet.card : ℝ) ≤
        ∑ L ∈ Finset.range K, ∑ c : Fin 3, ((admWords c L).card : ℝ) := by
      exact_mod_cast hW_card
    refine hcast.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun L _ => ?_
    rw [Fin.sum_univ_three]
    have hb0 : ((admWords 0 L).card : ℝ) ≤ perronH 0 * (1 / aStar) ^ L := by
      have := admWords_card_bound L 0
      rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith
    have hb1 : ((admWords 1 L).card : ℝ) ≤ perronH 1 * (1 / aStar) ^ L := by
      have := admWords_card_bound L 1
      rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith
    have hb2 : ((admWords 2 L).card : ℝ) ≤ perronH 2 * (1 / aStar) ^ L := by
      have := admWords_card_bound L 2
      rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith
    linarith
  have hgeom : ∑ L ∈ Finset.range K, (1 / aStar) ^ L ≤ (aStar / (1 - aStar)) * (1 / aStar) ^ K := by
    have hne : (1 / aStar : ℝ) ≠ 1 := by
      intro h; have : aStar = 1 := by field_simp at h; linarith
      linarith
    rw [geom_sum_eq hne]; have hden : 1 / aStar - 1 = (1 - aStar) / aStar := by field_simp
    rw [hden, div_div_eq_mul_div]; have hsub : (1 / aStar) ^ K - 1 ≤ (1 / aStar) ^ K := by linarith
    have hmul := mul_le_mul_of_nonneg_right hsub ha0.le
    calc ((1 / aStar) ^ K - 1) * aStar / (1 - aStar)
        ≤ (1 / aStar) ^ K * aStar / (1 - aStar) := div_le_div_of_nonneg_right hmul hd1.le
      _ = (aStar / (1 - aStar)) * (1 / aStar) ^ K := by ring
  have hpow : (1 / aStar) ^ K = (2 : ℝ) ^ (beta * (K : ℝ)) := by
    rw [← two_rpow_beta, ← Real.rpow_natCast ((2 : ℝ) ^ beta) K, ← Real.rpow_mul (by norm_num)]
  have hsum_nn : 0 ≤ perronH 0 + perronH 1 + perronH 2 := by
    linarith [perronH_ge_one 0, perronH_ge_one 1, perronH_ge_one 2]
  calc (N1 (15 * 2 ^ K) : ℝ)
      ≤ (WSet.card : ℝ) := by exact_mod_cast hN1_le_W
    _ ≤ (perronH 0 + perronH 1 + perronH 2) * ∑ L ∈ Finset.range K, (1 / aStar) ^ L := hW_real
    _ ≤ (perronH 0 + perronH 1 + perronH 2) * ((aStar / (1 - aStar)) * (1 / aStar) ^ K) :=
          mul_le_mul_of_nonneg_left hgeom hsum_nn
    _ = constCW * (2 : ℝ) ^ (beta * (K : ℝ)) := by unfold constCW; rw [hpow]; ring
lemma constCW_mul_rpow_lt : constCW * (2 / 15 : ℝ) ^ beta < 244 / 100 := by
  have hCW := constCW_lt; have hbeta_lo := beta_bounds.1
  have h215_le : (2 / 15 : ℝ) ^ beta ≤ (2 / 15 : ℝ) ^ ((501 : ℝ) / 800) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hbeta_lo.le
  have h58 : (2 / 15 : ℝ) ^ ((5 : ℝ) / 8) < 284224 / 1000000 := by
    have h8 : ((2 / 15 : ℝ) ^ ((5 : ℝ) / 8)) ^ (8 : ℕ) < (284224 / 1000000 : ℝ) ^ (8 : ℕ) := by
      rw [← Real.rpow_natCast ((2 / 15 : ℝ) ^ ((5 : ℝ) / 8)) 8, ← Real.rpow_mul (by norm_num)]
      have hexp : ((5 : ℝ) / 8) * (8 : ℕ) = (5 : ℕ) := by norm_num
      rw [hexp, Real.rpow_natCast]; norm_num
    exact lt_of_pow_lt_pow_left₀ 8 (by norm_num) h8
  have h1800 : (2 / 15 : ℝ) ^ ((1 : ℝ) / 800) < 400 / 401 := by
    have hexp2 : Real.exp 2 < 15 / 2 := by
      have he1 : Real.exp 1 < 272 / 100 := by linarith [Real.exp_one_lt_d9]
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [he2]; nlinarith [Real.exp_pos 1]
    have hlog : (2 : ℝ) < Real.log (15 / 2) := by
      conv_lhs => rw [← Real.log_exp 2]
      exact Real.log_lt_log (Real.exp_pos 2) hexp2
    have hgt : (401 / 400 : ℝ) < (15 / 2 : ℝ) ^ ((1 : ℝ) / 800) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      have harg : (1 / 400 : ℝ) < Real.log (15 / 2) * (1 / 800 : ℝ) := by linarith
      have := Real.add_one_le_exp (Real.log (15 / 2) * (1 / 800 : ℝ))
      linarith
    have hinv : (2 / 15 : ℝ) ^ ((1 : ℝ) / 800) = ((15 / 2 : ℝ) ^ ((1 : ℝ) / 800))⁻¹ := by
      rw [← Real.inv_rpow (by norm_num)]; norm_num
    rw [hinv]
    have : (400 / 401 : ℝ) = (401 / 400 : ℝ)⁻¹ := by norm_num
    rw [this]; exact inv_strictAnti₀ (by norm_num) hgt
  have h501 : (2 / 15 : ℝ) ^ ((501 : ℝ) / 800) < (284224 / 1000000 : ℝ) * (400 / 401 : ℝ) := by
    have hsp : (501 : ℝ) / 800 = (5 : ℝ) / 8 + (1 : ℝ) / 800 := by norm_num
    rw [hsp, Real.rpow_add (by norm_num)]
    exact mul_lt_mul'' h58 h1800 (by positivity) (by positivity)
  have hCW_nn : 0 ≤ constCW := by
    unfold constCW
    have := aStar_spec.1
    have := aStar_denom_pos.1
    have : 0 ≤ perronH 0 + perronH 1 + perronH 2 := by linarith [perronH_ge_one 0, perronH_ge_one 1, perronH_ge_one 2]
    positivity
  have hprod : constCW * (2 / 15 : ℝ) ^ beta <
      (86053 / 10000 : ℝ) * ((284224 / 1000000 : ℝ) * (400 / 401 : ℝ)) :=
    mul_lt_mul'' hCW (lt_of_le_of_lt h215_le h501) hCW_nn (by positivity)
  linarith [show (86053 / 10000 : ℝ) * ((284224 / 1000000 : ℝ) * (400 / 401 : ℝ)) <
      244 / 100 by norm_num]
/-- Theorem 10 (Upper bound for odd starts): `N1(X) ≤ 2.44 * X^β` for every `X ≥ 1`. -/
theorem thm_basin1_upper (X : ℕ) (hX : 1 ≤ X) : (N1 X : ℝ) ≤ (244 / 100 : ℝ) * (X : ℝ) ^ beta := by
  classical
  have hbeta_pos : 0 < beta := by linarith [beta_bounds.1]
  by_cases hX15 : X < 15
  ·
    have hcard : N1 X ≤ 1 := by
      unfold N1
      have hsub : (Finset.Icc 1 X).filter (fun n => n % 2 = 1 ∧ Reaches f n 1) ⊆ {1} := by
        intro n hn; simp only [Finset.mem_filter, Finset.mem_Icc] at hn
        simp only [Finset.mem_singleton]; have hABC := thm_residue_law hn.2.1 hn.2.2
        simp only [InABC, InA, InB, InC] at hABC; omega
      exact (Finset.card_le_card hsub).trans (by simp)
    have hX1 : (1 : ℝ) ≤ (X : ℝ) ^ beta := Real.one_le_rpow (by exact_mod_cast hX) hbeta_pos.le
    have hcast : (N1 X : ℝ) ≤ 1 := by exact_mod_cast hcard
    linarith
  · have hge15 : 15 ≤ X := by omega
    set K := Nat.log 2 (X / 15) + 1; have hK1 : 1 ≤ K := by omega
    have hq_pos : 1 ≤ X / 15 := by omega
    have h2K_lo : 2 ^ (K - 1) ≤ X / 15 := by
      have : K - 1 = Nat.log 2 (X / 15) := by omega
      rw [this]; exact Nat.pow_log_le_self 2 (by omega)
    have h2K_hi : X / 15 < 2 ^ K := Nat.lt_pow_succ_log_self (by norm_num) (X / 15)
    have hX_le : X ≤ 15 * 2 ^ K := by omega
    have h2K_le : (2 : ℝ) ^ (K : ℝ) ≤ (2 / 15 : ℝ) * (X : ℝ) := by
      have hnat : 15 * 2 ^ K ≤ 2 * X := by
        have hKeq : 2 ^ K = 2 * 2 ^ (K - 1) := by
          have : K = (K - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ']
        rw [hKeq]; omega
      have hreal : (15 : ℝ) * (2 : ℝ) ^ K ≤ 2 * (X : ℝ) := by exact_mod_cast hnat
      rw [Real.rpow_natCast]; linarith
    have hmono : N1 X ≤ N1 (15 * 2 ^ K) := by
      classical
      unfold N1
      refine Finset.card_le_card fun n hn => ?_
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢; exact ⟨⟨hn.1.1, hn.1.2.trans hX_le⟩, hn.2⟩
    have hblk := N1_block_bound K hK1
    have hCW_nn : 0 ≤ constCW := by
      unfold constCW
      have := aStar_spec.1; have := aStar_denom_pos.1
      have : 0 ≤ perronH 0 + perronH 1 + perronH 2 := by
        linarith [perronH_ge_one 0, perronH_ge_one 1, perronH_ge_one 2]
      positivity
    have hpow_le : (2 : ℝ) ^ (beta * (K : ℝ)) ≤ (2 / 15 : ℝ) ^ beta * (X : ℝ) ^ beta := by
      rw [mul_comm beta (K : ℝ), Real.rpow_mul (by norm_num),
          ← Real.mul_rpow (by norm_num) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) h2K_le hbeta_pos.le
    calc (N1 X : ℝ)
        ≤ (N1 (15 * 2 ^ K) : ℝ) := by exact_mod_cast hmono
      _ ≤ constCW * (2 : ℝ) ^ (beta * (K : ℝ)) := hblk
      _ ≤ constCW * ((2 / 15 : ℝ) ^ beta * (X : ℝ) ^ beta) := mul_le_mul_of_nonneg_left hpow_le hCW_nn
      _ = (constCW * (2 / 15 : ℝ) ^ beta) * (X : ℝ) ^ beta := by ring
      _ ≤ (244 / 100 : ℝ) * (X : ℝ) ^ beta := mul_le_mul_of_nonneg_right constCW_mul_rpow_lt.le (by positivity)
/-- Theorem 10 (Explicit safe exponent): `N1(X) ≤ 2.44 * X^0.626383` for all `X ≥ 1`. -/
theorem thm_basin1_upper_explicit (X : ℕ) (hX : 1 ≤ X) :
    (N1 X : ℝ) ≤ (244 / 100 : ℝ) * (X : ℝ) ^ ((626383 : ℝ) / 1000000) := by
  have h1 := thm_basin1_upper X hX
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hpow : (X : ℝ) ^ beta ≤ (X : ℝ) ^ ((626383 : ℝ) / 1000000) :=
    Real.rpow_le_rpow_of_exponent_le hX1 beta_bounds.2.le
  nlinarith
/-- Theorem 10 (Upper bound for all positive starts, even and odd): `N1All(X) ≤ 6.93 * X^β`. -/
theorem thm_basin1_all_upper (X : ℕ) (hX : 1 ≤ X) : (N1All X : ℝ) ≤ (693 / 100 : ℝ) * (X : ℝ) ^ beta := by
  classical
  have ha0 := aStar_spec.1; have ha1 := aStar_spec.2.1; have hbeta_pos : 0 < beta := by linarith [beta_bounds.1]
  let L := Nat.log 2 X + 1
  have hcard_le : N1All X ≤ ∑ j ∈ Finset.range L, N1 (X / 2 ^ j) := by
    unfold N1All N1
    let target : Finset (ℕ × ℕ) :=
      (Finset.range L).biUnion fun j =>
        ((Finset.Icc 1 (X / 2 ^ j)).filter (fun m => m % 2 = 1 ∧ Reaches f m 1)).image
          (fun m => (j, m))
    have h1 : ((Finset.Icc 1 X).filter (fun n => Reaches f n 1)).card ≤ target.card := by
      refine Finset.card_le_card_of_injOn (fun n => splitTwo n) ?_ ?_
      · intro n hn; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
        obtain ⟨⟨hn1, hnX⟩, hreach⟩ := hn
        obtain ⟨hm_odd, hfac⟩ := splitTwo_spec (m := n) (by omega)
        set j := (splitTwo n).1; set m := (splitTwo n).2
        have h2j_le : 2 ^ j ≤ X := by
          have hm1 : 1 ≤ m := by omega
          calc 2 ^ j = 2 ^ j * 1 := by ring
            _ ≤ 2 ^ j * m := Nat.mul_le_mul_left _ hm1
            _ = n := hfac.symm
            _ ≤ X := hnX
        have hj_lt : j < L := by
          have : j ≤ Nat.log 2 X := (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr h2j_le
          omega
        have hm_le : m ≤ X / 2 ^ j := by
          rw [Nat.le_div_iff_mul_le (by positivity)]
          linarith
        have hreach_m : Reaches f m 1 := by
          rcases hreach with ⟨k, hk⟩
          rw [hfac] at hk; exact ⟨k - j, (f_iter_two_pow_eq_odd (by decide) hk).2⟩
        simp only [Finset.mem_coe, target, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
          Finset.mem_filter, Finset.mem_Icc]
        exact ⟨j, hj_lt, m, ⟨⟨by omega, hm_le⟩, hm_odd, hreach_m⟩, rfl⟩
      · intro a ha b hb h; simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb; dsimp only at h
        have hfa := (splitTwo_spec (m := a) (by omega)).2
        have hfb := (splitTwo_spec (m := b) (by omega)).2
        rw [hfa, hfb, h]
    have h2 : target.card ≤ ∑ j ∈ Finset.range L,
        ((Finset.Icc 1 (X / 2 ^ j)).filter (fun m => m % 2 = 1 ∧ Reaches f m 1)).card := by
      unfold target; refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun j _ => Finset.card_image_le)
    exact h1.trans h2
  have hsum_real : (N1All X : ℝ) ≤
      (244 / 100 : ℝ) * (X : ℝ) ^ beta * ∑ j ∈ Finset.range L, aStar ^ j := by
    have hcast : (N1All X : ℝ) ≤ ∑ j ∈ Finset.range L, (N1 (X / 2 ^ j) : ℝ) := by exact_mod_cast hcard_le
    refine hcast.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases h0 : X / 2 ^ j = 0
    · have hN0 : N1 0 = 0 := by unfold N1; simp
      rw [h0, hN0, Nat.cast_zero]; positivity
    · have hge1 : 1 ≤ X / 2 ^ j := Nat.pos_of_ne_zero h0; have hup := thm_basin1_upper (X / 2 ^ j) hge1
      have hdiv : ((X / 2 ^ j : ℕ) : ℝ) ≤ (X : ℝ) / (2 : ℝ) ^ j := by
        have h := Nat.cast_div_le (m := X) (n := 2 ^ j) (α := ℝ)
        push_cast at h; exact h
      have hpow : ((X / 2 ^ j : ℕ) : ℝ) ^ beta ≤ (X : ℝ) ^ beta * aStar ^ j := by
        calc ((X / 2 ^ j : ℕ) : ℝ) ^ beta
            ≤ ((X : ℝ) / (2 : ℝ) ^ j) ^ beta := Real.rpow_le_rpow (by positivity) hdiv hbeta_pos.le
          _ = (X : ℝ) ^ beta / ((2 : ℝ) ^ j) ^ beta := Real.div_rpow (by positivity) (by positivity) beta
          _ = (X : ℝ) ^ beta * aStar ^ j := by
              rw [← Real.rpow_natCast 2 j, ← Real.rpow_mul (by norm_num),
                  mul_comm (j : ℝ) beta, Real.rpow_mul (by norm_num), two_rpow_beta,
                  Real.rpow_natCast, one_div, inv_pow, div_inv_eq_mul]
      calc (N1 (X / 2 ^ j) : ℝ)
          ≤ (244 / 100 : ℝ) * ((X / 2 ^ j : ℕ) : ℝ) ^ beta := hup
        _ ≤ (244 / 100 : ℝ) * ((X : ℝ) ^ beta * aStar ^ j) := mul_le_mul_of_nonneg_left hpow (by norm_num)
        _ = (244 / 100 : ℝ) * (X : ℝ) ^ beta * aStar ^ j := by ring
  have hgeom : ∑ j ∈ Finset.range L, aStar ^ j ≤ 1 / (1 - aStar) := by
    rw [geom_sum_eq (ne_of_lt ha1)]; have hnn : 0 ≤ aStar ^ L := by positivity
    have hneg : aStar ^ L - 1 = -(1 - aStar ^ L) := by ring
    have hneg2 : aStar - 1 = -(1 - aStar) := by ring
    rw [hneg, hneg2, neg_div_neg_eq]; exact div_le_div_of_nonneg_right (by linarith) aStar_denom_pos.1.le
  have hconst : (244 / 100 : ℝ) * (1 / (1 - aStar)) ≤ 693 / 100 := by
    rw [mul_one_div, div_le_iff₀ aStar_denom_pos.1]; linarith [aStar_bounds.2]
  calc (N1All X : ℝ)
      ≤ (244 / 100 : ℝ) * (X : ℝ) ^ beta * ∑ j ∈ Finset.range L, aStar ^ j := hsum_real
    _ ≤ (244 / 100 : ℝ) * (X : ℝ) ^ beta * (1 / (1 - aStar)) := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = ((244 / 100 : ℝ) * (1 / (1 - aStar))) * (X : ℝ) ^ beta := by ring
    _ ≤ (693 / 100 : ℝ) * (X : ℝ) ^ beta := mul_le_mul_of_nonneg_right hconst (by positivity)
/-- Theorem 10 (Natural density zero): `N1All(X) / X → 0` as `X → ∞`. -/
theorem thm_basin1_density_zero (ε : ℝ) (hε : 0 < ε) : ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → (N1All X : ℝ) / (X : ℝ) ≤ ε := by
  have hdiff : beta - 1 < -(1 / 4 : ℝ) := by linarith [beta_bounds.2]
  obtain ⟨X₀, hX₀⟩ := exists_nat_gt (((693 / 100 : ℝ) / ε) ^ (4 : ℕ))
  refine ⟨max 1 X₀, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_of_max_le_left hX
  have hXpos : (0 : ℝ) < (X : ℝ) := by positivity
  have hup := thm_basin1_all_upper X hX1
  have hdiv : (N1All X : ℝ) / (X : ℝ) ≤ (693 / 100 : ℝ) * (X : ℝ) ^ (beta - 1) := by
    rw [div_le_iff₀ hXpos]
    calc (N1All X : ℝ)
        ≤ (693 / 100 : ℝ) * (X : ℝ) ^ beta := hup
      _ = (693 / 100 : ℝ) * (X : ℝ) ^ (beta - 1) * (X : ℝ) := by
            have : (X : ℝ) ^ (beta - 1) * (X : ℝ) = (X : ℝ) ^ beta := by
              conv_rhs => rw [show beta = (beta - 1) + 1 by ring]
              rw [Real.rpow_add hXpos, Real.rpow_one]
            linarith
  have hpow : (X : ℝ) ^ (beta - 1) ≤ (X : ℝ) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX1) hdiff.le
  have hX4 : ((693 / 100 : ℝ) / ε) ^ (4 : ℕ) ≤ (X : ℝ) := le_trans hX₀.le (by exact_mod_cast le_of_max_le_right hX)
  have hq : (693 / 100 : ℝ) / ε ≤ (X : ℝ) ^ ((1 / 4 : ℝ)) := by
    have h4 : ((693 / 100 : ℝ) / ε) ^ (4 : ℕ) ≤ ((X : ℝ) ^ ((1 / 4 : ℝ))) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast ((X : ℝ) ^ ((1 / 4 : ℝ))) 4, ← Real.rpow_mul hXpos.le]
      have : ((1 / 4 : ℝ) * (4 : ℕ)) = 1 := by norm_num
      rw [this, Real.rpow_one]; exact hX4
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h4
  have hfinal : (693 / 100 : ℝ) * (X : ℝ) ^ (-(1 / 4 : ℝ)) ≤ ε := by
    rw [Real.rpow_neg hXpos.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have := (div_le_iff₀ hε).mp hq
    linarith
  calc (N1All X : ℝ) / (X : ℝ)
      ≤ (693 / 100 : ℝ) * (X : ℝ) ^ (beta - 1) := hdiv
    _ ≤ (693 / 100 : ℝ) * (X : ℝ) ^ (-(1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ ε := hfinal

end Ouroboros
