module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import Ouroboros.Defs
public import Ouroboros.BasinOne
public import Ouroboros.BasinOneMoves
public import Ouroboros.BasinFive
public import Ouroboros.BasinOneLowerCert

@[expose] public section

/-!
# Sharpened lower bound for the basin of 1 (`thm:basin-sharp`, Part 1a)

Proves the sharpened lower bounds of Theorem 8 (`thm:basin-sharp`, Part 1) completely inside
Lean 4's pure kernel using the `Q₁ = 643,125` (`128,625`-row, `57,575`-weight) integer
certificate verified by `rfl` in `Ouroboros.BasinOneLowerCert`:

- `nonperiodic_31`: `31` is non-periodic under `f = f_10`.
- `thm_basin1_sharp_lower_real`: for every real `X ≥ 1`,
  `0.0806 * (X / 31)^(399/800) ≤ N1 ⌊X⌋₊` and `0.0145 * X^(399/800) ≤ N1 ⌊X⌋₊`.
- `thm_basin1_sharp_lower`: natural-number specialization for every integer `X ≥ 1`,
  `0.0806 * (X / 31)^(399/800) ≤ N1 X` and `0.0145 * X^(399/800) ≤ N1 X`.

ZERO `sorry`, ZERO `admit`, ZERO `native_decide`, ZERO custom axioms.
-/

namespace Ouroboros

open BasinOneLowerCert

/-! ## Section 1: Pure-kernel `800`-th power coefficient soundness (`γ' = 399 / 800`) -/

private lemma pow800_eq_pow (x : ℕ) : (pow800 x : ℝ) = (x : ℝ) ^ (800 : ℕ) := by
  unfold pow800
  push_cast
  ring

private lemma pow399_eq_pow (x : ℕ) : (pow399 x : ℝ) = (x : ℝ) ^ (399 : ℕ) := by
  unfold pow399
  push_cast
  ring

private lemma halfSC_le :
    (759908250 : ℝ) / 1073741824 ≤ (2 : ℝ) ^ (-((399 : ℝ) / 800)) := by
  have hnat : pow800 759908250 * pow399 2 ≤ pow800 1073741824 :=
    Nat.ble_eq.mp check_halfSC
  have hR : (759908250 : ℝ) ^ (800 : ℕ) * (2 : ℝ) ^ (399 : ℕ) ≤
      (1073741824 : ℝ) ^ (800 : ℕ) := by
    have h1 : (pow800 759908250 : ℝ) * (pow399 2 : ℝ) ≤ (pow800 1073741824 : ℝ) := by
      exact_mod_cast hnat
    rwa [pow800_eq_pow, pow399_eq_pow, pow800_eq_pow] at h1
  have hpow : ((759908250 : ℝ) / 1073741824) ^ (800 : ℕ) ≤
      ((2 : ℝ) ^ (-((399 : ℝ) / 800))) ^ (800 : ℕ) := by
    rw [div_pow, ← Real.rpow_natCast ((2 : ℝ) ^ _) 800, ← Real.rpow_mul (by norm_num)]
    have hexp : -((399 : ℝ) / 800) * (800 : ℕ) = -((399 : ℕ) : ℝ) := by norm_num
    rw [hexp, Real.rpow_neg (by norm_num), Real.rpow_natCast, ← one_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simpa [one_mul] using hR
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hpow

private lemma d5SC_le :
    (2396134319 : ℝ) / 1073741824 ≤ (5 : ℝ) ^ ((399 : ℝ) / 800) := by
  have hnat : pow800 2396134319 ≤ pow800 1073741824 * pow399 5 :=
    Nat.ble_eq.mp check_d5SC
  have hR : (2396134319 : ℝ) ^ (800 : ℕ) ≤
      (1073741824 : ℝ) ^ (800 : ℕ) * (5 : ℝ) ^ (399 : ℕ) := by
    have h1 : (pow800 2396134319 : ℝ) ≤ (pow800 1073741824 : ℝ) * (pow399 5 : ℝ) := by
      exact_mod_cast hnat
    rwa [pow800_eq_pow, pow800_eq_pow, pow399_eq_pow] at h1
  have hpow : ((2396134319 : ℝ) / 1073741824) ^ (800 : ℕ) ≤
      ((5 : ℝ) ^ ((399 : ℝ) / 800)) ^ (800 : ℕ) := by
    rw [div_pow, ← Real.rpow_natCast ((5 : ℝ) ^ _) 800, ← Real.rpow_mul (by norm_num)]
    have hexp : ((399 : ℝ) / 800) * (800 : ℕ) = (399 : ℕ) := by norm_num
    rw [hexp, Real.rpow_natCast, div_le_iff₀ (by positivity)]
    simpa [mul_comm] using hR
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hpow

private lemma d7SC_le :
    (2833952177 : ℝ) / 1073741824 ≤ (7 : ℝ) ^ ((399 : ℝ) / 800) := by
  have hnat : pow800 2833952177 ≤ pow800 1073741824 * pow399 7 :=
    Nat.ble_eq.mp check_d7SC
  have hR : (2833952177 : ℝ) ^ (800 : ℕ) ≤
      (1073741824 : ℝ) ^ (800 : ℕ) * (7 : ℝ) ^ (399 : ℕ) := by
    have h1 : (pow800 2833952177 : ℝ) ≤ (pow800 1073741824 : ℝ) * (pow399 7 : ℝ) := by
      exact_mod_cast hnat
    rwa [pow800_eq_pow, pow800_eq_pow, pow399_eq_pow] at h1
  have hpow : ((2833952177 : ℝ) / 1073741824) ^ (800 : ℕ) ≤
      ((7 : ℝ) ^ ((399 : ℝ) / 800)) ^ (800 : ℕ) := by
    rw [div_pow, ← Real.rpow_natCast ((7 : ℝ) ^ _) 800, ← Real.rpow_mul (by norm_num)]
    have hexp : ((399 : ℝ) / 800) * (800 : ℕ) = (399 : ℕ) := by norm_num
    rw [hexp, Real.rpow_natCast, div_le_iff₀ (by positivity)]
    simpa [mul_comm] using hR
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hpow

private lemma termSC_le {d t0 : ℕ} (hd : 0 < d)
    (ht0 : (t0 : ℝ) / 1073741824 ≤ (d : ℝ) ^ ((399 : ℝ) / 800)) (v : ℕ) :
    (termSC t0 v : ℝ) / 1073741824 ≤ ((d : ℝ) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) := by
  induction v with
  | zero =>
    simpa [termSC] using ht0
  | succ v ih =>
    have hdiv : (termSC t0 (v + 1) : ℝ) ≤
        ((termSC t0 v : ℝ) * 759908250) / 1073741824 := by
      change (((termSC t0 v * 759908250) / 1073741824 : ℕ) : ℝ) ≤ _
      have h := Nat.cast_div_le (m := termSC t0 v * 759908250) (n := 1073741824) (α := ℝ)
      push_cast at h
      exact h
    have hstep1 : (termSC t0 (v + 1) : ℝ) / 1073741824 ≤
        ((termSC t0 v : ℝ) / 1073741824) * ((759908250 : ℝ) / 1073741824) := by
      have h1 := div_le_div_of_nonneg_right hdiv (by norm_num : (0 : ℝ) ≤ 1073741824)
      linarith
    have hstep2 : ((termSC t0 v : ℝ) / 1073741824) * ((759908250 : ℝ) / 1073741824) ≤
        ((d : ℝ) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) * (2 : ℝ) ^ (-((399 : ℝ) / 800)) :=
      mul_le_mul ih halfSC_le (by norm_num) (by positivity)
    have hcomb : ((d : ℝ) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) * (2 : ℝ) ^ (-((399 : ℝ) / 800)) =
        ((d : ℝ) / (2 : ℝ) ^ (v + 1)) ^ ((399 : ℝ) / 800) := by
      have hinv : (2 : ℝ) ^ (-((399 : ℝ) / 800)) = ((2 : ℝ)⁻¹) ^ ((399 : ℝ) / 800) := by
        rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
      rw [hinv, ← Real.mul_rpow (by positivity) (by norm_num)]
      congr 1
      rw [pow_succ]
      ring
    exact hstep1.trans (hstep2.trans_eq hcomb)

private lemma coeffOf_le {d t0 : ℕ} (hd : 0 < d)
    (ht0 : (t0 : ℝ) / 1073741824 ≤ (d : ℝ) ^ ((399 : ℝ) / 800)) (v : ℕ) :
    (coeffOf t0 v : ℝ) / 1048576 ≤ ((d : ℝ) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) := by
  have hdiv : (coeffOf t0 v : ℝ) ≤ (termSC t0 v : ℝ) / 1024 := by
    unfold coeffOf
    have h := Nat.cast_div_le (m := termSC t0 v) (n := 1024) (α := ℝ)
    push_cast at h
    exact h
  have h1 : (coeffOf t0 v : ℝ) / 1048576 ≤ (termSC t0 v : ℝ) / 1073741824 := by
    have h2 := div_le_div_of_nonneg_right hdiv (by norm_num : (0 : ℝ) ≤ 1048576)
    linarith
  exact h1.trans (termSC_le hd ht0 v)

private lemma coeff1_le {c v : ℕ} (h : c = coeffOf 1073741824 v) :
    (c : ℝ) / 1048576 ≤ ((1 : ℝ) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) := by
  rw [h]
  have h0 : ((1073741824 : ℕ) : ℝ) / 1073741824 ≤ ((1 : ℕ) : ℝ) ^ ((399 : ℝ) / 800) := by
    rw [Nat.cast_one, Real.one_rpow]; norm_num
  simpa using coeffOf_le (d := 1) (t0 := 1073741824) (by omega) h0 v

private lemma coeff5_le {c v : ℕ} (h : c = coeffOf 2396134319 v) :
    (c : ℝ) / 1048576 ≤ ((5 : ℝ) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) := by
  rw [h]
  simpa using coeffOf_le (d := 5) (t0 := 2396134319) (by omega) d5SC_le v

private lemma coeff7_le {c v : ℕ} (h : c = coeffOf 2833952177 v) :
    (c : ℝ) / 1048576 ≤ ((7 : ℝ) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) := by
  rw [h]
  simpa using coeffOf_le (d := 7) (t0 := 2833952177) (by omega) d7SC_le v

private lemma term1_le {c v : ℕ} (h : c = coeffOf 1073741824 v) (w : ℕ) :
    (c : ℝ) * (w : ℝ) ≤
      1048576 * (((1 : ℝ) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) * (w : ℝ)) := by
  have hle := coeff1_le h
  have h1 : (c : ℝ) ≤ 1048576 * ((1 : ℝ) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) := by
    have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1048576)).mp hle; linarith
  have h2 := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℝ) w)
  linarith

private lemma term5_le {c v : ℕ} (h : c = coeffOf 2396134319 v) (w : ℕ) :
    (c : ℝ) * (w : ℝ) ≤
      1048576 * (((5 : ℝ) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) * (w : ℝ)) := by
  have hle := coeff5_le h
  have h1 : (c : ℝ) ≤ 1048576 * ((5 : ℝ) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) := by
    have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1048576)).mp hle; linarith
  have h2 := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℝ) w)
  linarith

private lemma term7_le {c v : ℕ} (h : c = coeffOf 2833952177 v) (w : ℕ) :
    (c : ℝ) * (w : ℝ) ≤
      1048576 * (((7 : ℝ) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) * (w : ℝ)) := by
  have hle := coeff7_le h
  have h1 : (c : ℝ) ≤ 1048576 * ((7 : ℝ) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) := by
    have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1048576)).mp hle; linarith
  have h2 := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℝ) w)
  linarith

/-! ## Section 2: Certified weight function and move sets on `A ∪ B ∪ C` -/

private lemma predCond_0 (x : ℕ) : predCond 0 x = (x % 5 = 2) := rfl
private lemma predCond_2 (x : ℕ) : predCond 2 x = (x % 25 = 1) := rfl
private lemma predCond_3 (x : ℕ) : predCond 3 x = (x % 5 = 0 ∧ x % 7 = 1) := rfl
private lemma digitVal_0 : digitVal 0 = 1 := rfl
private lemma digitVal_2 : digitVal 2 = 5 := rfl
private lemma digitVal_3 : digitVal 3 = 7 := rfl

/-- Certified integer weight `w(o) ∈ [0, 65535]` on `A ∪ B ∪ C` modulo `Q₁ = 643,125`. -/
def wCertNat (o : ℕ) : ℕ :=
  let k := (o % 643125) / 15
  if o % 15 = 1 then getWA k
  else if o % 15 = 0 then getWB (k % 8575)
  else if o % 15 = 2 then getWC (k % 6125)
  else 0

private lemma wCertNat_le (o : ℕ) : wCertNat o ≤ 65535 := by
  unfold wCertNat
  split_ifs
  · exact getWA_le _
  · exact getWB_le _
  · exact getWC_le _
  · exact Nat.zero_le _

private lemma wCertNat_31 : wCertNat 31 = 13484 := by
  unfold wCertNat
  simpa using getWA_root

/-- Explicit finite move set `(digitIdx, v)` used in the `Vmax = 25` certificate at `o`. -/
def certMoves (o : ℕ) : Finset (Fin 5 × ℕ) :=
  let k := (o % 643125) / 15
  if o % 15 = 1 then
    ({1, 5, 9, 13, 17, 21, 25} : Finset ℕ).image (fun v => ((0 : Fin 5), v)) ∪
    (match k % 5 with
      | 0 => {20}
      | 1 => {16}
      | 2 => {12}
      | 3 => {8}
      | _ => {4, 24} : Finset ℕ).image (fun v => ((2 : Fin 5), v))
  else if o % 15 = 2 then
    ({4, 8, 12, 16, 20, 24} : Finset ℕ).image (fun v => ((0 : Fin 5), v)) ∪
    (match k % 5 with
      | 0 => {19}
      | 1 => {7}
      | 2 => {15}
      | 3 => {3, 23}
      | _ => {11} : Finset ℕ).image (fun v => ((2 : Fin 5), v))
  else if o % 15 = 0 then
    (match k % 7 with
      | 4 => {1, 4, 7, 10, 13, 16, 19, 22, 25}
      | 2 => {2, 5, 8, 11, 14, 17, 20, 23}
      | 1 => {3, 6, 9, 12, 15, 18, 21, 24}
      | _ => ∅ : Finset ℕ).image (fun v => ((3 : Fin 5), v))
  else ∅

/-- Child vertex `m = (2^v * o - 1) / digitVal di`. -/
def predOf (o : ℕ) (mv : Fin 5 × ℕ) : ℕ :=
  (2 ^ mv.2 * o - 1) / digitVal mv.1

private lemma predCond_of_mem_certMoves {o : ℕ} (ho : InABC15 o)
    {mv : Fin 5 × ℕ} (hmv : mv ∈ certMoves o) :
    1 ≤ mv.2 ∧ predCond mv.1 (2 ^ mv.2 * o) := by
  have ho15 := ho.2.2
  set k := (o % 643125) / 15 with hk_def
  have ho_mod_eq : o % 643125 = 15 * k + o % 15 := by
    have h15 : (o % 643125) % 15 = o % 15 := Nat.mod_mod_of_dvd o (by decide)
    omega
  have h25 : o % 25 = (15 * (k % 5) + o % 15) % 25 := by
    have h1 : o % 25 = (o % 643125) % 25 := (Nat.mod_mod_of_dvd o (by decide)).symm
    rw [h1, ho_mod_eq]; omega
  have h7 : o % 7 = (15 * (k % 7) + o % 15) % 7 := by
    have h1 : o % 7 = (o % 643125) % 7 := (Nat.mod_mod_of_dvd o (by decide)).symm
    rw [h1, ho_mod_eq]; omega
  have h5 : o % 5 = o % 15 % 5 := by omega
  rcases ho15 with h15 | h15 | h15
  · -- Class A: o % 15 = 1
    simp only [certMoves, ← hk_def, h15, ↓reduceIte, Finset.mem_union, Finset.mem_image] at hmv
    rcases hmv with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by omega, by rw [predCond_0, Nat.mul_mod, h5, h15]; decide⟩
    · have hk5 : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
      rcases hk5 with hr | hr | hr | hr | hr
      · rw [hr] at hv; simp only [Finset.mem_singleton] at hv; subst hv
        exact ⟨by omega, by rw [predCond_2, Nat.mul_mod, h25, hr, h15]; decide⟩
      · rw [hr] at hv; simp only [Finset.mem_singleton] at hv; subst hv
        exact ⟨by omega, by rw [predCond_2, Nat.mul_mod, h25, hr, h15]; decide⟩
      · rw [hr] at hv; simp only [Finset.mem_singleton] at hv; subst hv
        exact ⟨by omega, by rw [predCond_2, Nat.mul_mod, h25, hr, h15]; decide⟩
      · rw [hr] at hv; simp only [Finset.mem_singleton] at hv; subst hv
        exact ⟨by omega, by rw [predCond_2, Nat.mul_mod, h25, hr, h15]; decide⟩
      · rw [hr] at hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;>
          exact ⟨by omega, by rw [predCond_2, Nat.mul_mod, h25, hr, h15]; decide⟩
  · -- Class B: o % 15 = 0
    simp only [certMoves, ← hk_def, h15, show (0 : ℕ) ≠ 1 by decide,
      show (0 : ℕ) ≠ 2 by decide, ↓reduceIte, Finset.mem_image] at hmv
    obtain ⟨v, hv, rfl⟩ := hmv
    have hk7 : k % 7 = 0 ∨ k % 7 = 1 ∨ k % 7 = 2 ∨ k % 7 = 3 ∨
        k % 7 = 4 ∨ k % 7 = 5 ∨ k % 7 = 6 := by omega
    rcases hk7 with hr | hr | hr | hr | hr | hr | hr
    · rw [hr] at hv; simp at hv
    · rw [hr] at hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by omega, by
          rw [predCond_3]
          exact ⟨by rw [Nat.mul_mod, h5, h15]; decide,
                 by rw [Nat.mul_mod, h7, hr, h15]; decide⟩⟩
    · rw [hr] at hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by omega, by
          rw [predCond_3]
          exact ⟨by rw [Nat.mul_mod, h5, h15]; decide,
                 by rw [Nat.mul_mod, h7, hr, h15]; decide⟩⟩
    · rw [hr] at hv; simp at hv
    · rw [hr] at hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by omega, by
          rw [predCond_3]
          exact ⟨by rw [Nat.mul_mod, h5, h15]; decide,
                 by rw [Nat.mul_mod, h7, hr, h15]; decide⟩⟩
    · rw [hr] at hv; simp at hv
    · rw [hr] at hv; simp at hv
  · -- Class C: o % 15 = 2
    simp only [certMoves, ← hk_def, h15, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte,
      Finset.mem_union, Finset.mem_image] at hmv
    rcases hmv with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by omega, by rw [predCond_0, Nat.mul_mod, h5, h15]; decide⟩
    · have hk5 : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
      rcases hk5 with hr | hr | hr | hr | hr
      · rw [hr] at hv; simp only [Finset.mem_singleton] at hv; subst hv
        exact ⟨by omega, by rw [predCond_2, Nat.mul_mod, h25, hr, h15]; decide⟩
      · rw [hr] at hv; simp only [Finset.mem_singleton] at hv; subst hv
        exact ⟨by omega, by rw [predCond_2, Nat.mul_mod, h25, hr, h15]; decide⟩
      · rw [hr] at hv; simp only [Finset.mem_singleton] at hv; subst hv
        exact ⟨by omega, by rw [predCond_2, Nat.mul_mod, h25, hr, h15]; decide⟩
      · rw [hr] at hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;>
          exact ⟨by omega, by rw [predCond_2, Nat.mul_mod, h25, hr, h15]; decide⟩
      · rw [hr] at hv; simp only [Finset.mem_singleton] at hv; subst hv
        exact ⟨by omega, by rw [predCond_2, Nat.mul_mod, h25, hr, h15]; decide⟩

/-- Every move in `certMoves o` yields a valid odd predecessor `m ∈ A ∪ B ∪ C` of `o`. -/
private lemma predOf_props {o : ℕ} (ho : InABC15 o) {mv : Fin 5 × ℕ} (hmv : mv ∈ certMoves o) :
    let m := predOf o mv
    InABC15 m ∧ 1 ≤ mv.2 ∧ d m = digitVal mv.1 ∧
    d m * m + 1 = 2 ^ mv.2 * o ∧ f^[mv.2 + 1] m = o := by
  obtain ⟨hv1, hcond⟩ := predCond_of_mem_certMoves ho hmv
  obtain ⟨hm_pos, hm_odd, hdm, heq, hstep⟩ :=
    lemma_odd_predecessors_unique ho.1 ho.2.1 hv1 mv.1 hcond
  have hm_abc : InABC15 (predOf o mv) :=
    (lem_basin1_moves_classify ho hv1 hm_odd heq).2.2.1
  exact ⟨hm_abc, hv1, hdm, heq, hstep⟩

/-! ## Section 3: Exact child-index bridges from `sumA`, `sumC`, `sumB` to `wCertNat ∘ predOf` -/

private lemma wCertNat_pred_d1 {o v c : ℕ} (ho : InABC15 o) (hv : 1 ≤ v)
    (hcond : predCond 0 (2 ^ v * o))
    (hc_lt : c < 42875)
    (hmod : (2 ^ v * o) % 643125 = 15 * c + 2) :
    wCertNat (predOf o (0, v)) = getWA c := by
  have hm_eq : predOf o (0, v) = 2 ^ v * o - 1 := by simp [predOf, digitVal]
  have hm_mod : predOf o (0, v) % 643125 = 15 * c + 1 := by
    rw [hm_eq]
    have hq := Nat.div_add_mod (2 ^ v * o) 643125
    have hsub : 2 ^ v * o - 1 = 643125 * (2 ^ v * o / 643125) + (15 * c + 1) := by omega
    rw [hsub, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hm15 : predOf o (0, v) % 15 = 1 := by
    have : predOf o (0, v) % 15 = (predOf o (0, v) % 643125) % 15 :=
      (Nat.mod_mod_of_dvd _ (by decide)).symm
    rw [this, hm_mod]; omega
  have _ := (lemma_odd_predecessors_unique ho.1 ho.2.1 hv 0 hcond).1
  unfold wCertNat
  simp only [hm15, ↓reduceIte, hm_mod]
  congr 1; omega

private lemma step_d1_mod {o v c : ℕ} (h : (2 ^ v * o) % 643125 = 15 * c + 2) :
    (2 ^ (v + 4) * o) % 643125 = 15 * ((16 * c + 2) % 42875) + 2 := by
  have hpow : 2 ^ (v + 4) * o = 16 * (2 ^ v * o) := by rw [pow_add]; ring
  rw [hpow, Nat.mul_mod, h, show 16 % 643125 = 16 by decide]
  have hq := Nat.div_add_mod (16 * c + 2) 42875
  have hlt := Nat.mod_lt (16 * c + 2) (by omega : 0 < 42875)
  have h2 : 16 * (15 * c + 2) =
      643125 * ((16 * c + 2) / 42875) + (15 * ((16 * c + 2) % 42875) + 2) := by omega
  rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

private lemma wCertNat_pred_d5 {o v p2v : ℕ} (ho : InABC15 o) (hv : 1 ≤ v)
    (hcond : predCond 2 (2 ^ v * o))
    (hp2v : 2 ^ v % 643125 = p2v) :
    wCertNat (predOf o (2, v)) = getWB (((p2v * (o % 643125)) % 643125 - 1) / 75) := by
  obtain ⟨_, hm_odd, hdm, heq, _⟩ :=
    lemma_odd_predecessors_unique ho.1 ho.2.1 hv 2 hcond
  have hm15 : predOf o (2, v) % 15 = 0 := by
    have hcl := (lem_basin1_moves_classify ho hv hm_odd heq).2.2.2
    rw [hdm, digitVal_2] at hcl
    rcases hcl with h | h | h | h
    · omega
    · omega
    · exact h.2.2.2
    · omega
  have h5dvd : 5 ∣ 2 ^ v * o - 1 := by
    rw [hdm, digitVal_2] at heq
    exact ⟨(2 ^ v * o - 1) / 5, by omega⟩
  have hm_mod128 : predOf o (2, v) % 128625 = ((2 ^ v * o - 1) % 643125) / 5 := by
    change ((2 ^ v * o - 1) / 5) % (643125 / 5) = ((2 ^ v * o - 1) % 643125) / 5
    exact div_mod_div_eq (by omega) (by decide) h5dvd
  have hidx_eq : ((predOf o (2, v) % 643125) / 15) % 8575 = (predOf o (2, v) % 128625) / 15 := by
    have h1 := Nat.div_add_mod (predOf o (2, v) % 643125) 128625
    have h2 : (predOf o (2, v) % 643125) % 128625 = predOf o (2, v) % 128625 :=
      Nat.mod_mod_of_dvd _ (by decide)
    rw [h2] at h1
    have hlt := Nat.mod_lt (predOf o (2, v)) (by omega : 0 < 128625)
    omega
  have hmod2v : (2 ^ v * o) % 643125 = (p2v * (o % 643125)) % 643125 := by
    have hp_lt : p2v < 643125 := by rw [← hp2v]; exact Nat.mod_lt _ (by omega)
    rw [Nat.mul_mod, hp2v, Nat.mul_mod p2v (o % 643125), Nat.mod_mod, Nat.mod_eq_of_lt hp_lt]
  have hpos_mod : 1 ≤ (2 ^ v * o) % 643125 := by
    have h25 : ((2 ^ v * o) % 643125) % 25 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by decide)]; exact hcond
    omega
  have hsub_mod : (2 ^ v * o - 1) % 643125 = (2 ^ v * o) % 643125 - 1 := by
    have hq := Nat.div_add_mod (2 ^ v * o) 643125
    have hlt := Nat.mod_lt (2 ^ v * o) (by omega : 0 < 643125)
    have hsub : 2 ^ v * o - 1 = 643125 * (2 ^ v * o / 643125) + ((2 ^ v * o) % 643125 - 1) := by
      omega
    rw [hsub, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  unfold wCertNat
  simp only [hm15, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, hidx_eq, hm_mod128, hsub_mod, hmod2v]
  congr 1
  rw [Nat.div_div_eq_div_mul]

private lemma wCertNat_pred_d7 {o v c : ℕ} (ho : InABC15 o) (hv : 1 ≤ v)
    (hcond : predCond 3 (2 ^ v * o))
    (_hc_lt : c < 6125)
    (hmod : (2 ^ v * o) % 643125 = 105 * c + 15) :
    wCertNat (predOf o (3, v)) = getWC c := by
  obtain ⟨_, hm_odd, hdm, heq, _⟩ :=
    lemma_odd_predecessors_unique ho.1 ho.2.1 hv 3 hcond
  have hm15 : predOf o (3, v) % 15 = 2 := by
    have hcl := (lem_basin1_moves_classify ho hv hm_odd heq).2.2.2
    rw [hdm, digitVal_3] at hcl
    rcases hcl with h | h | h | h
    · omega
    · omega
    · omega
    · exact h.2.2.2
  have h7dvd : 7 ∣ 2 ^ v * o - 1 := by
    rw [hdm, digitVal_3] at heq
    exact ⟨(2 ^ v * o - 1) / 7, by omega⟩
  have hm_mod91 : predOf o (3, v) % 91875 = ((2 ^ v * o - 1) % 643125) / 7 := by
    change ((2 ^ v * o - 1) / 7) % (643125 / 7) = ((2 ^ v * o - 1) % 643125) / 7
    exact div_mod_div_eq (by omega) (by decide) h7dvd
  have hidx_eq : ((predOf o (3, v) % 643125) / 15) % 6125 = (predOf o (3, v) % 91875) / 15 := by
    have h1 := Nat.div_add_mod (predOf o (3, v) % 643125) 91875
    have h2 : (predOf o (3, v) % 643125) % 91875 = predOf o (3, v) % 91875 :=
      Nat.mod_mod_of_dvd _ (by decide)
    rw [h2] at h1
    have hlt := Nat.mod_lt (predOf o (3, v)) (by omega : 0 < 91875)
    omega
  have hsub_mod : (2 ^ v * o - 1) % 643125 = 105 * c + 14 := by
    have hq := Nat.div_add_mod (2 ^ v * o) 643125
    have hsub : 2 ^ v * o - 1 = 643125 * (2 ^ v * o / 643125) + (105 * c + 14) := by omega
    rw [hsub, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  unfold wCertNat
  simp only [hm15, show (2 : ℕ) ≠ 1 by decide, show (2 : ℕ) ≠ 0 by decide, ↓reduceIte,
    hidx_eq, hm_mod91, hsub_mod]
  congr 1; omega

private lemma step_d7_mod {o v c : ℕ} (h : (2 ^ v * o) % 643125 = 105 * c + 15) :
    (2 ^ (v + 3) * o) % 643125 = 105 * ((8 * c + 1) % 6125) + 15 := by
  have hpow : 2 ^ (v + 3) * o = 8 * (2 ^ v * o) := by rw [pow_add]; ring
  rw [hpow, Nat.mul_mod, h, show 8 % 643125 = 8 by decide]
  have hq := Nat.div_add_mod (8 * c + 1) 6125
  have hlt := Nat.mod_lt (8 * c + 1) (by omega : 0 < 6125)
  have h2 : 8 * (105 * c + 15) =
      643125 * ((8 * c + 1) / 6125) + (105 * ((8 * c + 1) % 6125) + 15) := by omega
  rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

private lemma base_d7_mod {o v p2v : ℕ} (ho15 : o % 15 = 0)
    (h7 : (p2v * ((o % 643125) / 15)) % 7 = 1) (hp2v : 2 ^ v = p2v) (hp_lt : p2v < 643125) :
    (2 ^ v * o) % 643125 = 105 * (((p2v * ((o % 643125) / 15)) % 42875 - 1) / 7) + 15 ∧
    ((p2v * ((o % 643125) / 15)) % 42875 - 1) / 7 < 6125 := by
  set k := (o % 643125) / 15
  have ho_eq : o % 643125 = 15 * k := by
    have h1 : (o % 643125) % 15 = 0 := by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact ho15
    omega
  have hmul : (2 ^ v * o) % 643125 = 15 * ((p2v * k) % 42875) := by
    rw [hp2v, Nat.mul_mod, ho_eq, Nat.mod_eq_of_lt hp_lt]
    have hcomm : p2v * (15 * k) = 15 * (p2v * k) := by ring
    have hq := Nat.div_add_mod (p2v * k) 42875
    have hlt := Nat.mod_lt (p2v * k) (by omega : 0 < 42875)
    have h1 : p2v * (15 * k) = 643125 * ((p2v * k) / 42875) + 15 * ((p2v * k) % 42875) := by
      rw [hcomm]; omega
    rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hmod7 : ((p2v * k) % 42875) % 7 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (by decide)]; exact h7
  have hlt := Nat.mod_lt (p2v * k) (by omega : 0 < 42875)
  exact ⟨by rw [hmul]; omega, by omega⟩

private lemma certW_sub_eig_A {o : ℕ} (ho : InABC15 o) (h15 : o % 15 = 1) :
    (wCertNat o : ℝ) ≤
      ∑ mv ∈ certMoves o,
        ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
          (wCertNat (predOf o mv) : ℝ) := by
  set k := (o % 643125) / 15 with hk_def
  have hk_lt : k < 42875 := by have := Nat.mod_lt o (by omega : 0 < 643125); omega
  have hcert := checkA_all k hk_lt
  have hw_eq : wCertNat o = getWA k := by
    unfold wCertNat; simp only [← hk_def, h15, ↓reduceIte]
  have ho_mod : o % 643125 = 15 * k + 1 := by
    have h1 : (o % 643125) % 15 = 1 := by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact h15
    omega
  have ho5 : o % 5 = 1 := by omega
  set c0 := (2 * k) % 42875
  set c1 := (16 * c0 + 2) % 42875
  set c2 := (16 * c1 + 2) % 42875
  set c3 := (16 * c2 + 2) % 42875
  set c4 := (16 * c3 + 2) % 42875
  set c5 := (16 * c4 + 2) % 42875
  set c6 := (16 * c5 + 2) % 42875
  have hm1 : (2 ^ 1 * o) % 643125 = 15 * c0 + 2 := by
    rw [Nat.mul_mod, ho_mod, show 2 ^ 1 % 643125 = 2 by decide]
    have hq := Nat.div_add_mod (2 * k) 42875
    have hlt := Nat.mod_lt (2 * k) (by omega : 0 < 42875)
    have h1 : 2 * (15 * k + 1) = 643125 * (2 * k / 42875) + (15 * c0 + 2) := by omega
    rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hm5 : (2 ^ 5 * o) % 643125 = 15 * c1 + 2 := step_d1_mod hm1
  have hm9 : (2 ^ 9 * o) % 643125 = 15 * c2 + 2 := step_d1_mod hm5
  have hm13 : (2 ^ 13 * o) % 643125 = 15 * c3 + 2 := step_d1_mod hm9
  have hm17 : (2 ^ 17 * o) % 643125 = 15 * c4 + 2 := step_d1_mod hm13
  have hm21 : (2 ^ 21 * o) % 643125 = 15 * c5 + 2 := step_d1_mod hm17
  have hm25 : (2 ^ 25 * o) % 643125 = 15 * c6 + 2 := step_d1_mod hm21
  have hpc1 : ∀ v, v % 4 = 1 → predCond 0 (2 ^ v * o) := fun v hv4 => by
    rw [predCond_0]
    have h24 : 2 ^ v % 5 = 2 := by
      have : v = 4 * (v / 4) + 1 := by omega
      rw [this, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
    rw [Nat.mul_mod, h24, ho5]
  have hw_c0 := wCertNat_pred_d1 ho (by omega) (hpc1 1 rfl) (Nat.mod_lt _ (by omega)) hm1
  have hw_c1 := wCertNat_pred_d1 ho (by omega) (hpc1 5 rfl) (Nat.mod_lt _ (by omega)) hm5
  have hw_c2 := wCertNat_pred_d1 ho (by omega) (hpc1 9 rfl) (Nat.mod_lt _ (by omega)) hm9
  have hw_c3 := wCertNat_pred_d1 ho (by omega) (hpc1 13 rfl) (Nat.mod_lt _ (by omega)) hm13
  have hw_c4 := wCertNat_pred_d1 ho (by omega) (hpc1 17 rfl) (Nat.mod_lt _ (by omega)) hm17
  have hw_c5 := wCertNat_pred_d1 ho (by omega) (hpc1 21 rfl) (Nat.mod_lt _ (by omega)) hm21
  have hw_c6 := wCertNat_pred_d1 ho (by omega) (hpc1 25 rfl) (Nat.mod_lt _ (by omega)) hm25
  have hs1_le :
      ((742097 * getWA c0 + 186168 * getWA c1 + 46703 * getWA c2 +
        11716 * getWA c3 + 2939 * getWA c4 + 737 * getWA c5 + 184 * getWA c6 : ℕ) : ℝ) ≤
      1048576 * ∑ mv ∈ ({1, 5, 9, 13, 17, 21, 25} : Finset ℕ).image (fun v => ((0 : Fin 5), v)),
        ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
          (wCertNat (predOf o mv) : ℝ) := by
    rw [Finset.sum_image (fun a _ b _ h => congr_arg Prod.snd h)]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      show (1 : ℕ) ≠ 5 by decide, show (1 : ℕ) ≠ 9 by decide, show (1 : ℕ) ≠ 13 by decide,
      show (1 : ℕ) ≠ 17 by decide, show (1 : ℕ) ≠ 21 by decide, show (1 : ℕ) ≠ 25 by decide,
      show (5 : ℕ) ≠ 9 by decide, show (5 : ℕ) ≠ 13 by decide, show (5 : ℕ) ≠ 17 by decide,
      show (5 : ℕ) ≠ 21 by decide, show (5 : ℕ) ≠ 25 by decide,
      show (9 : ℕ) ≠ 13 by decide, show (9 : ℕ) ≠ 17 by decide, show (9 : ℕ) ≠ 21 by decide,
      show (9 : ℕ) ≠ 25 by decide, show (13 : ℕ) ≠ 17 by decide, show (13 : ℕ) ≠ 21 by decide,
      show (13 : ℕ) ≠ 25 by decide, show (17 : ℕ) ≠ 21 by decide, show (17 : ℕ) ≠ 25 by decide,
      show (21 : ℕ) ≠ 25 by decide, or_self, not_false_eq_true, Finset.sum_singleton,
      digitVal_0, Nat.cast_one, hw_c0, hw_c1, hw_c2, hw_c3, hw_c4, hw_c5, hw_c6]
    push_cast
    have t0 := term1_le (c := 742097) (v := 1) rfl (getWA c0)
    have t1 := term1_le (c := 186168) (v := 5) rfl (getWA c1)
    have t2 := term1_le (c := 46703) (v := 9) rfl (getWA c2)
    have t3 := term1_le (c := 11716) (v := 13) rfl (getWA c3)
    have t4 := term1_le (c := 2939) (v := 17) rfl (getWA c4)
    have t5 := term1_le (c := 737) (v := 21) rfl (getWA c5)
    have t6 := term1_le (c := 184) (v := 25) rfl (getWA c6)
    linarith
  have hdisj : ∀ S5 : Finset ℕ, Disjoint
      (({1, 5, 9, 13, 17, 21, 25} : Finset ℕ).image (fun v => ((0 : Fin 5), v)))
      (S5.image (fun v => ((2 : Fin 5), v))) := by
    intro S5
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_image] at hx1 hx2
    obtain ⟨_, _, rfl⟩ := hx1; obtain ⟨_, _, h2⟩ := hx2
    exact (by decide : (2 : Fin 5) ≠ 0) (congr_arg Prod.fst h2)
  have h25_mod : o % 25 = (15 * (k % 5) + 1) % 25 := by
    have h1 : o % 25 = (o % 643125) % 25 := (Nat.mod_mod_of_dvd o (by decide)).symm
    rw [h1, ho_mod]; omega
  suffices hR : (wCertNat o : ℝ) * 1048576 ≤
      1048576 * ∑ mv ∈ certMoves o,
        ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
          (wCertNat (predOf o mv) : ℝ) by linarith
  have hcertR : (wCertNat o : ℝ) * 1048576 ≤ (sumA k : ℝ) := by
    rw [hw_eq]; exact_mod_cast hcert
  refine hcertR.trans ?_
  unfold certMoves
  simp only [← hk_def, h15, ↓reduceIte]
  rw [Finset.sum_union (hdisj _), mul_add]
  have hk5 : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  rcases hk5 with hr | hr | hr | hr | hr
  · have hsumA : sumA k =
        (742097 * getWA c0 + 186168 * getWA c1 + 46703 * getWA c2 +
         11716 * getWA c3 + 2939 * getWA c4 + 737 * getWA c5 + 184 * getWA c6) +
        2325 * getWB (((405451 * (o % 643125)) % 643125 - 1) / 75) := by
      unfold sumA; dsimp only; rw [hr, ← ho_mod]
    have hw5 := wCertNat_pred_d5 (v := 20) (p2v := 405451) ho (by omega)
      (by rw [predCond_2, Nat.mul_mod, h25_mod, hr]; decide) (by decide)
    have t5 := term5_le (c := 2325) (v := 20) rfl (getWB (((405451 * (o % 643125)) % 643125 - 1) / 75))
    rw [hsumA, Nat.cast_add, hr]
    simp only [Finset.image_singleton, Finset.sum_singleton, digitVal_2, hw5]
    refine add_le_add hs1_le ?_
    push_cast at t5 ⊢
    exact t5
  · have hsumA : sumA k =
        (742097 * getWA c0 + 186168 * getWA c1 + 46703 * getWA c2 +
         11716 * getWA c3 + 2939 * getWA c4 + 737 * getWA c5 + 184 * getWA c6) +
        9268 * getWB (((65536 * (o % 643125)) % 643125 - 1) / 75) := by
      unfold sumA; dsimp only; rw [hr, ← ho_mod]
    have hw5 := wCertNat_pred_d5 (v := 16) (p2v := 65536) ho (by omega)
      (by rw [predCond_2, Nat.mul_mod, h25_mod, hr]; decide) (by decide)
    have t5 := term5_le (c := 9268) (v := 16) rfl (getWB (((65536 * (o % 643125)) % 643125 - 1) / 75))
    rw [hsumA, Nat.cast_add, hr]
    simp only [Finset.image_singleton, Finset.sum_singleton, digitVal_2, hw5]
    refine add_le_add hs1_le ?_
    push_cast at t5 ⊢
    exact t5
  · have hsumA : sumA k =
        (742097 * getWA c0 + 186168 * getWA c1 + 46703 * getWA c2 +
         11716 * getWA c3 + 2939 * getWA c4 + 737 * getWA c5 + 184 * getWA c6) +
        36944 * getWB (((4096 * (o % 643125)) % 643125 - 1) / 75) := by
      unfold sumA; dsimp only; rw [hr, ← ho_mod]
    have hw5 := wCertNat_pred_d5 (v := 12) (p2v := 4096) ho (by omega)
      (by rw [predCond_2, Nat.mul_mod, h25_mod, hr]; decide) (by decide)
    have t5 := term5_le (c := 36944) (v := 12) rfl (getWB (((4096 * (o % 643125)) % 643125 - 1) / 75))
    rw [hsumA, Nat.cast_add, hr]
    simp only [Finset.image_singleton, Finset.sum_singleton, digitVal_2, hw5]
    refine add_le_add hs1_le ?_
    push_cast at t5 ⊢
    exact t5
  · have hsumA : sumA k =
        (742097 * getWA c0 + 186168 * getWA c1 + 46703 * getWA c2 +
         11716 * getWA c3 + 2939 * getWA c4 + 737 * getWA c5 + 184 * getWA c6) +
        147265 * getWB (((256 * (o % 643125)) % 643125 - 1) / 75) := by
      unfold sumA; dsimp only; rw [hr, ← ho_mod]
    have hw5 := wCertNat_pred_d5 (v := 8) (p2v := 256) ho (by omega)
      (by rw [predCond_2, Nat.mul_mod, h25_mod, hr]; decide) (by decide)
    have t5 := term5_le (c := 147265) (v := 8) rfl (getWB (((256 * (o % 643125)) % 643125 - 1) / 75))
    rw [hsumA, Nat.cast_add, hr]
    simp only [Finset.image_singleton, Finset.sum_singleton, digitVal_2, hw5]
    refine add_le_add hs1_le ?_
    push_cast at t5 ⊢
    exact t5
  · have hsumA : sumA k =
        (742097 * getWA c0 + 186168 * getWA c1 + 46703 * getWA c2 +
         11716 * getWA c3 + 2939 * getWA c4 + 737 * getWA c5 + 184 * getWA c6) +
        (587024 * getWB (((16 * (o % 643125)) % 643125 - 1) / 75) +
         583 * getWB (((55966 * (o % 643125)) % 643125 - 1) / 75)) := by
      unfold sumA; dsimp only; rw [hr, ← ho_mod]
    have hw5a := wCertNat_pred_d5 (v := 4) (p2v := 16) ho (by omega)
      (by rw [predCond_2, Nat.mul_mod, h25_mod, hr]; decide) (by decide)
    have hw5b := wCertNat_pred_d5 (v := 24) (p2v := 55966) ho (by omega)
      (by rw [predCond_2, Nat.mul_mod, h25_mod, hr]; decide) (by decide)
    have t5a := term5_le (c := 587024) (v := 4) rfl (getWB (((16 * (o % 643125)) % 643125 - 1) / 75))
    have t5b := term5_le (c := 583) (v := 24) rfl (getWB (((55966 * (o % 643125)) % 643125 - 1) / 75))
    have hs5 : ∑ mv ∈ ({4, 24} : Finset ℕ).image (fun v => ((2 : Fin 5), v)),
        ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
          (wCertNat (predOf o mv) : ℝ) =
        ((5 : ℝ) / (2 : ℝ) ^ 4) ^ ((399 : ℝ) / 800) *
          (getWB (((16 * (o % 643125)) % 643125 - 1) / 75) : ℝ) +
        ((5 : ℝ) / (2 : ℝ) ^ 24) ^ ((399 : ℝ) / 800) *
          (getWB (((55966 * (o % 643125)) % 643125 - 1) / 75) : ℝ) := by
      rw [Finset.sum_image (fun a _ b _ h => congr_arg Prod.snd h)]
      simp only [Finset.sum_insert, Finset.mem_singleton, show (4 : ℕ) ≠ 24 by decide,
        not_false_eq_true, Finset.sum_singleton, digitVal_2, hw5a, hw5b]
      push_cast; rfl
    rw [hsumA, Nat.cast_add, hr]
    refine add_le_add hs1_le ?_
    change _ ≤ 1048576 * ∑ mv ∈ ({4, 24} : Finset ℕ).image (fun v => ((2 : Fin 5), v)), _
    rw [hs5]
    push_cast at t5a t5b ⊢
    linarith

private lemma certW_sub_eig_B {o : ℕ} (ho : InABC15 o) (h15 : o % 15 = 0) :
    (wCertNat o : ℝ) ≤
      ∑ mv ∈ certMoves o,
        ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
          (wCertNat (predOf o mv) : ℝ) := by
  set k := (o % 643125) / 15 with hk_def
  have hk_lt : k < 42875 := by have := Nat.mod_lt o (by omega : 0 < 643125); omega
  have hcert := checkB_all k hk_lt
  have hw_eq : wCertNat o = getWB (k % 8575) := by
    unfold wCertNat; simp only [← hk_def, h15, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
  suffices hR : (wCertNat o : ℝ) * 1048576 ≤
      1048576 * ∑ mv ∈ certMoves o,
        ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
          (wCertNat (predOf o mv) : ℝ) by linarith
  have hcertR : (wCertNat o : ℝ) * 1048576 ≤ (sumB k : ℝ) := by
    rw [hw_eq]; exact_mod_cast hcert
  refine hcertR.trans ?_
  unfold certMoves
  simp only [← hk_def, h15, show (0 : ℕ) ≠ 1 by decide, show (0 : ℕ) ≠ 2 by decide, ↓reduceIte]
  have h5 : o % 5 = 0 := by omega
  have ho_mod : o % 643125 = 15 * k := by
    have h1 : (o % 643125) % 15 = 0 := by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact h15
    omega
  have h7 : o % 7 = (15 * (k % 7)) % 7 := by
    have h1 : o % 7 = (o % 643125) % 7 := (Nat.mod_mod_of_dvd o (by decide)).symm
    rw [h1, ho_mod]; omega
  have hk7 : k % 7 = 0 ∨ k % 7 = 1 ∨ k % 7 = 2 ∨ k % 7 = 3 ∨
      k % 7 = 4 ∨ k % 7 = 5 ∨ k % 7 = 6 := by omega
  rcases hk7 with hr | hr | hr | hr | hr | hr | hr
  · have hsumB : sumB k = 0 := by unfold sumB; dsimp only; rw [hr]
    rw [hsumB, hr]; simp
  · -- r7 = 1: v = 3, 6, 9, 12, 15, 18, 21, 24
    set c0 := ((8 * k) % 42875 - 1) / 7
    set c1 := (8 * c0 + 1) % 6125
    set c2 := (8 * c1 + 1) % 6125
    set c3 := (8 * c2 + 1) % 6125
    set c4 := (8 * c3 + 1) % 6125
    set c5 := (8 * c4 + 1) % 6125
    set c6 := (8 * c5 + 1) % 6125
    set c7 := (8 * c6 + 1) % 6125
    obtain ⟨hm3, hc0_lt⟩ := base_d7_mod (v := 3) (p2v := 8) h15 (by omega) rfl (by decide)
    have hm6 : (2 ^ 6 * o) % 643125 = 105 * c1 + 15 := step_d7_mod hm3
    have hm9 : (2 ^ 9 * o) % 643125 = 105 * c2 + 15 := step_d7_mod hm6
    have hm12 : (2 ^ 12 * o) % 643125 = 105 * c3 + 15 := step_d7_mod hm9
    have hm15 : (2 ^ 15 * o) % 643125 = 105 * c4 + 15 := step_d7_mod hm12
    have hm18 : (2 ^ 18 * o) % 643125 = 105 * c5 + 15 := step_d7_mod hm15
    have hm21 : (2 ^ 21 * o) % 643125 = 105 * c6 + 15 := step_d7_mod hm18
    have hm24 : (2 ^ 24 * o) % 643125 = 105 * c7 + 15 := step_d7_mod hm21
    have hpc : ∀ v, v % 3 = 0 → predCond 3 (2 ^ v * o) := fun v hv3 => by
      rw [predCond_3]
      refine ⟨by rw [Nat.mul_mod, h5]; simp, ?_⟩
      have h23 : 2 ^ v % 7 = 1 := by
        have : v = 3 * (v / 3) := by omega
        rw [this, pow_mul, Nat.pow_mod]; norm_num
      rw [Nat.mul_mod, h23, h7, hr]
    have hw0 := wCertNat_pred_d7 ho (by omega) (hpc 3 rfl) hc0_lt hm3
    have hw1 := wCertNat_pred_d7 ho (by omega) (hpc 6 rfl) (Nat.mod_lt _ (by omega)) hm6
    have hw2 := wCertNat_pred_d7 ho (by omega) (hpc 9 rfl) (Nat.mod_lt _ (by omega)) hm9
    have hw3 := wCertNat_pred_d7 ho (by omega) (hpc 12 rfl) (Nat.mod_lt _ (by omega)) hm12
    have hw4 := wCertNat_pred_d7 ho (by omega) (hpc 15 rfl) (Nat.mod_lt _ (by omega)) hm15
    have hw5 := wCertNat_pred_d7 ho (by omega) (hpc 18 rfl) (Nat.mod_lt _ (by omega)) hm18
    have hw6 := wCertNat_pred_d7 ho (by omega) (hpc 21 rfl) (Nat.mod_lt _ (by omega)) hm21
    have hw7 := wCertNat_pred_d7 ho (by omega) (hpc 24 rfl) (Nat.mod_lt _ (by omega)) hm24
    have hsumB : sumB k =
        981016 * getWC c0 + 347744 * getWC c1 + 123266 * getWC c2 +
        43694 * getWC c3 + 15488 * getWC c4 + 5490 * getWC c5 +
        1946 * getWC c6 + 689 * getWC c7 := by
      unfold sumB; dsimp only; rw [hr]
    rw [hsumB, hr, Finset.sum_image (fun a _ b _ h => congr_arg Prod.snd h)]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      show (3 : ℕ) ≠ 6 by decide, show (3 : ℕ) ≠ 9 by decide, show (3 : ℕ) ≠ 12 by decide,
      show (3 : ℕ) ≠ 15 by decide, show (3 : ℕ) ≠ 18 by decide, show (3 : ℕ) ≠ 21 by decide,
      show (3 : ℕ) ≠ 24 by decide, show (6 : ℕ) ≠ 9 by decide, show (6 : ℕ) ≠ 12 by decide,
      show (6 : ℕ) ≠ 15 by decide, show (6 : ℕ) ≠ 18 by decide, show (6 : ℕ) ≠ 21 by decide,
      show (6 : ℕ) ≠ 24 by decide, show (9 : ℕ) ≠ 12 by decide, show (9 : ℕ) ≠ 15 by decide,
      show (9 : ℕ) ≠ 18 by decide, show (9 : ℕ) ≠ 21 by decide, show (9 : ℕ) ≠ 24 by decide,
      show (12 : ℕ) ≠ 15 by decide, show (12 : ℕ) ≠ 18 by decide, show (12 : ℕ) ≠ 21 by decide,
      show (12 : ℕ) ≠ 24 by decide, show (15 : ℕ) ≠ 18 by decide, show (15 : ℕ) ≠ 21 by decide,
      show (15 : ℕ) ≠ 24 by decide, show (18 : ℕ) ≠ 21 by decide, show (18 : ℕ) ≠ 24 by decide,
      show (21 : ℕ) ≠ 24 by decide, or_self, not_false_eq_true, Finset.sum_singleton,
      digitVal_3, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7]
    have t0 := term7_le (c := 981016) (v := 3) rfl (getWC c0)
    have t1 := term7_le (c := 347744) (v := 6) rfl (getWC c1)
    have t2 := term7_le (c := 123266) (v := 9) rfl (getWC c2)
    have t3 := term7_le (c := 43694) (v := 12) rfl (getWC c3)
    have t4 := term7_le (c := 15488) (v := 15) rfl (getWC c4)
    have t5 := term7_le (c := 5490) (v := 18) rfl (getWC c5)
    have t6 := term7_le (c := 1946) (v := 21) rfl (getWC c6)
    have t7 := term7_le (c := 689) (v := 24) rfl (getWC c7)
    push_cast at t0 t1 t2 t3 t4 t5 t6 t7 ⊢
    linarith
  · -- r7 = 2: v = 2, 5, 8, 11, 14, 17, 20, 23
    set c0 := ((4 * k) % 42875 - 1) / 7
    set c1 := (8 * c0 + 1) % 6125
    set c2 := (8 * c1 + 1) % 6125
    set c3 := (8 * c2 + 1) % 6125
    set c4 := (8 * c3 + 1) % 6125
    set c5 := (8 * c4 + 1) % 6125
    set c6 := (8 * c5 + 1) % 6125
    set c7 := (8 * c6 + 1) % 6125
    obtain ⟨hm2, hc0_lt⟩ := base_d7_mod (v := 2) (p2v := 4) h15 (by omega) rfl (by decide)
    have hm5 : (2 ^ 5 * o) % 643125 = 105 * c1 + 15 := step_d7_mod hm2
    have hm8 : (2 ^ 8 * o) % 643125 = 105 * c2 + 15 := step_d7_mod hm5
    have hm11 : (2 ^ 11 * o) % 643125 = 105 * c3 + 15 := step_d7_mod hm8
    have hm14 : (2 ^ 14 * o) % 643125 = 105 * c4 + 15 := step_d7_mod hm11
    have hm17 : (2 ^ 17 * o) % 643125 = 105 * c5 + 15 := step_d7_mod hm14
    have hm20 : (2 ^ 20 * o) % 643125 = 105 * c6 + 15 := step_d7_mod hm17
    have hm23 : (2 ^ 23 * o) % 643125 = 105 * c7 + 15 := step_d7_mod hm20
    have hpc : ∀ v, v % 3 = 2 → predCond 3 (2 ^ v * o) := fun v hv3 => by
      rw [predCond_3]
      refine ⟨by rw [Nat.mul_mod, h5]; simp, ?_⟩
      have h23 : 2 ^ v % 7 = 4 := by
        have : v = 3 * (v / 3) + 2 := by omega
        rw [this, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
      rw [Nat.mul_mod, h23, h7, hr]
    have hw0 := wCertNat_pred_d7 ho (by omega) (hpc 2 rfl) hc0_lt hm2
    have hw1 := wCertNat_pred_d7 ho (by omega) (hpc 5 rfl) (Nat.mod_lt _ (by omega)) hm5
    have hw2 := wCertNat_pred_d7 ho (by omega) (hpc 8 rfl) (Nat.mod_lt _ (by omega)) hm8
    have hw3 := wCertNat_pred_d7 ho (by omega) (hpc 11 rfl) (Nat.mod_lt _ (by omega)) hm11
    have hw4 := wCertNat_pred_d7 ho (by omega) (hpc 14 rfl) (Nat.mod_lt _ (by omega)) hm14
    have hw5 := wCertNat_pred_d7 ho (by omega) (hpc 17 rfl) (Nat.mod_lt _ (by omega)) hm17
    have hw6 := wCertNat_pred_d7 ho (by omega) (hpc 20 rfl) (Nat.mod_lt _ (by omega)) hm20
    have hw7 := wCertNat_pred_d7 ho (by omega) (hpc 23 rfl) (Nat.mod_lt _ (by omega)) hm23
    have hsumB : sumB k =
        1386165 * getWC c0 + 491359 * getWC c1 + 174173 * getWC c2 +
        61740 * getWC c3 + 21885 * getWC c4 + 7757 * getWC c5 +
        2749 * getWC c6 + 974 * getWC c7 := by
      unfold sumB; dsimp only; rw [hr]
    rw [hsumB, hr, Finset.sum_image (fun a _ b _ h => congr_arg Prod.snd h)]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      show (2 : ℕ) ≠ 5 by decide, show (2 : ℕ) ≠ 8 by decide, show (2 : ℕ) ≠ 11 by decide,
      show (2 : ℕ) ≠ 14 by decide, show (2 : ℕ) ≠ 17 by decide, show (2 : ℕ) ≠ 20 by decide,
      show (2 : ℕ) ≠ 23 by decide, show (5 : ℕ) ≠ 8 by decide, show (5 : ℕ) ≠ 11 by decide,
      show (5 : ℕ) ≠ 14 by decide, show (5 : ℕ) ≠ 17 by decide, show (5 : ℕ) ≠ 20 by decide,
      show (5 : ℕ) ≠ 23 by decide, show (8 : ℕ) ≠ 11 by decide, show (8 : ℕ) ≠ 14 by decide,
      show (8 : ℕ) ≠ 17 by decide, show (8 : ℕ) ≠ 20 by decide, show (8 : ℕ) ≠ 23 by decide,
      show (11 : ℕ) ≠ 14 by decide, show (11 : ℕ) ≠ 17 by decide, show (11 : ℕ) ≠ 20 by decide,
      show (11 : ℕ) ≠ 23 by decide, show (14 : ℕ) ≠ 17 by decide, show (14 : ℕ) ≠ 20 by decide,
      show (14 : ℕ) ≠ 23 by decide, show (17 : ℕ) ≠ 20 by decide, show (17 : ℕ) ≠ 23 by decide,
      show (20 : ℕ) ≠ 23 by decide, or_self, not_false_eq_true, Finset.sum_singleton,
      digitVal_3, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7]
    have t0 := term7_le (c := 1386165) (v := 2) rfl (getWC c0)
    have t1 := term7_le (c := 491359) (v := 5) rfl (getWC c1)
    have t2 := term7_le (c := 174173) (v := 8) rfl (getWC c2)
    have t3 := term7_le (c := 61740) (v := 11) rfl (getWC c3)
    have t4 := term7_le (c := 21885) (v := 14) rfl (getWC c4)
    have t5 := term7_le (c := 7757) (v := 17) rfl (getWC c5)
    have t6 := term7_le (c := 2749) (v := 20) rfl (getWC c6)
    have t7 := term7_le (c := 974) (v := 23) rfl (getWC c7)
    push_cast at t0 t1 t2 t3 t4 t5 t6 t7 ⊢
    linarith
  · have hsumB : sumB k = 0 := by unfold sumB; dsimp only; rw [hr]
    rw [hsumB, hr]; simp
  · -- r7 = 4: v = 1, 4, 7, 10, 13, 16, 19, 22, 25
    set c0 := ((2 * k) % 42875 - 1) / 7
    set c1 := (8 * c0 + 1) % 6125
    set c2 := (8 * c1 + 1) % 6125
    set c3 := (8 * c2 + 1) % 6125
    set c4 := (8 * c3 + 1) % 6125
    set c5 := (8 * c4 + 1) % 6125
    set c6 := (8 * c5 + 1) % 6125
    set c7 := (8 * c6 + 1) % 6125
    set c8 := (8 * c7 + 1) % 6125
    obtain ⟨hm1, hc0_lt⟩ := base_d7_mod (v := 1) (p2v := 2) h15 (by omega) rfl (by decide)
    have hm4 : (2 ^ 4 * o) % 643125 = 105 * c1 + 15 := step_d7_mod hm1
    have hm7 : (2 ^ 7 * o) % 643125 = 105 * c2 + 15 := step_d7_mod hm4
    have hm10 : (2 ^ 10 * o) % 643125 = 105 * c3 + 15 := step_d7_mod hm7
    have hm13 : (2 ^ 13 * o) % 643125 = 105 * c4 + 15 := step_d7_mod hm10
    have hm16 : (2 ^ 16 * o) % 643125 = 105 * c5 + 15 := step_d7_mod hm13
    have hm19 : (2 ^ 19 * o) % 643125 = 105 * c6 + 15 := step_d7_mod hm16
    have hm22 : (2 ^ 22 * o) % 643125 = 105 * c7 + 15 := step_d7_mod hm19
    have hm25 : (2 ^ 25 * o) % 643125 = 105 * c8 + 15 := step_d7_mod hm22
    have hpc : ∀ v, v % 3 = 1 → predCond 3 (2 ^ v * o) := fun v hv3 => by
      rw [predCond_3]
      refine ⟨by rw [Nat.mul_mod, h5]; simp, ?_⟩
      have h23 : 2 ^ v % 7 = 2 := by
        have : v = 3 * (v / 3) + 1 := by omega
        rw [this, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
      rw [Nat.mul_mod, h23, h7, hr]
    have hw0 := wCertNat_pred_d7 ho (by omega) (hpc 1 rfl) hc0_lt hm1
    have hw1 := wCertNat_pred_d7 ho (by omega) (hpc 4 rfl) (Nat.mod_lt _ (by omega)) hm4
    have hw2 := wCertNat_pred_d7 ho (by omega) (hpc 7 rfl) (Nat.mod_lt _ (by omega)) hm7
    have hw3 := wCertNat_pred_d7 ho (by omega) (hpc 10 rfl) (Nat.mod_lt _ (by omega)) hm10
    have hw4 := wCertNat_pred_d7 ho (by omega) (hpc 13 rfl) (Nat.mod_lt _ (by omega)) hm13
    have hw5 := wCertNat_pred_d7 ho (by omega) (hpc 16 rfl) (Nat.mod_lt _ (by omega)) hm16
    have hw6 := wCertNat_pred_d7 ho (by omega) (hpc 19 rfl) (Nat.mod_lt _ (by omega)) hm19
    have hw7 := wCertNat_pred_d7 ho (by omega) (hpc 22 rfl) (Nat.mod_lt _ (by omega)) hm22
    have hw8 := wCertNat_pred_d7 ho (by omega) (hpc 25 rfl) (Nat.mod_lt _ (by omega)) hm25
    have hsumB : sumB k =
        1958636 * getWC c0 + 694284 * getWC c1 + 246105 * getWC c2 +
        87237 * getWC c3 + 30923 * getWC c4 + 10961 * getWC c5 +
        3885 * getWC c6 + 1377 * getWC c7 + 488 * getWC c8 := by
      unfold sumB; dsimp only; rw [hr]
    rw [hsumB, hr, Finset.sum_image (fun a _ b _ h => congr_arg Prod.snd h)]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      show (1 : ℕ) ≠ 4 by decide, show (1 : ℕ) ≠ 7 by decide, show (1 : ℕ) ≠ 10 by decide,
      show (1 : ℕ) ≠ 13 by decide, show (1 : ℕ) ≠ 16 by decide, show (1 : ℕ) ≠ 19 by decide,
      show (1 : ℕ) ≠ 22 by decide, show (1 : ℕ) ≠ 25 by decide, show (4 : ℕ) ≠ 7 by decide,
      show (4 : ℕ) ≠ 10 by decide, show (4 : ℕ) ≠ 13 by decide, show (4 : ℕ) ≠ 16 by decide,
      show (4 : ℕ) ≠ 19 by decide, show (4 : ℕ) ≠ 22 by decide, show (4 : ℕ) ≠ 25 by decide,
      show (7 : ℕ) ≠ 10 by decide, show (7 : ℕ) ≠ 13 by decide, show (7 : ℕ) ≠ 16 by decide,
      show (7 : ℕ) ≠ 19 by decide, show (7 : ℕ) ≠ 22 by decide, show (7 : ℕ) ≠ 25 by decide,
      show (10 : ℕ) ≠ 13 by decide, show (10 : ℕ) ≠ 16 by decide, show (10 : ℕ) ≠ 19 by decide,
      show (10 : ℕ) ≠ 22 by decide, show (10 : ℕ) ≠ 25 by decide, show (13 : ℕ) ≠ 16 by decide,
      show (13 : ℕ) ≠ 19 by decide, show (13 : ℕ) ≠ 22 by decide, show (13 : ℕ) ≠ 25 by decide,
      show (16 : ℕ) ≠ 19 by decide, show (16 : ℕ) ≠ 22 by decide, show (16 : ℕ) ≠ 25 by decide,
      show (19 : ℕ) ≠ 22 by decide, show (19 : ℕ) ≠ 25 by decide, show (22 : ℕ) ≠ 25 by decide,
      or_self, not_false_eq_true, Finset.sum_singleton,
      digitVal_3, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8]
    have t0 := term7_le (c := 1958636) (v := 1) rfl (getWC c0)
    have t1 := term7_le (c := 694284) (v := 4) rfl (getWC c1)
    have t2 := term7_le (c := 246105) (v := 7) rfl (getWC c2)
    have t3 := term7_le (c := 87237) (v := 10) rfl (getWC c3)
    have t4 := term7_le (c := 30923) (v := 13) rfl (getWC c4)
    have t5 := term7_le (c := 10961) (v := 16) rfl (getWC c5)
    have t6 := term7_le (c := 3885) (v := 19) rfl (getWC c6)
    have t7 := term7_le (c := 1377) (v := 22) rfl (getWC c7)
    have t8 := term7_le (c := 488) (v := 25) rfl (getWC c8)
    push_cast at t0 t1 t2 t3 t4 t5 t6 t7 t8 ⊢
    linarith
  · have hsumB : sumB k = 0 := by unfold sumB; dsimp only; rw [hr]
    rw [hsumB, hr]; simp
  · have hsumB : sumB k = 0 := by unfold sumB; dsimp only; rw [hr]
    rw [hsumB, hr]; simp

private lemma certW_sub_eig_C {o : ℕ} (ho : InABC15 o) (h15 : o % 15 = 2) :
    (wCertNat o : ℝ) ≤
      ∑ mv ∈ certMoves o,
        ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
          (wCertNat (predOf o mv) : ℝ) := by
  set k := (o % 643125) / 15 with hk_def
  have hk_lt : k < 42875 := by have := Nat.mod_lt o (by omega : 0 < 643125); omega
  have hcert := checkC_all k hk_lt
  have hw_eq : wCertNat o = getWC (k % 6125) := by
    unfold wCertNat
    simp only [← hk_def, h15, show (2 : ℕ) ≠ 1 by decide, show (2 : ℕ) ≠ 0 by decide, ↓reduceIte]
  have ho_mod : o % 643125 = 15 * k + 2 := by
    have h1 : (o % 643125) % 15 = 2 := by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact h15
    omega
  have ho5 : o % 5 = 2 := by omega
  set c0 := (16 * k + 2) % 42875
  set c1 := (16 * c0 + 2) % 42875
  set c2 := (16 * c1 + 2) % 42875
  set c3 := (16 * c2 + 2) % 42875
  set c4 := (16 * c3 + 2) % 42875
  set c5 := (16 * c4 + 2) % 42875
  have hm4 : (2 ^ 4 * o) % 643125 = 15 * c0 + 2 := by
    rw [Nat.mul_mod, ho_mod, show 2 ^ 4 % 643125 = 16 by decide]
    have hq := Nat.div_add_mod (16 * k + 2) 42875
    have hlt := Nat.mod_lt (16 * k + 2) (by omega : 0 < 42875)
    have h1 : 16 * (15 * k + 2) = 643125 * ((16 * k + 2) / 42875) + (15 * c0 + 2) := by omega
    rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hm8 : (2 ^ 8 * o) % 643125 = 15 * c1 + 2 := step_d1_mod hm4
  have hm12 : (2 ^ 12 * o) % 643125 = 15 * c2 + 2 := step_d1_mod hm8
  have hm16 : (2 ^ 16 * o) % 643125 = 15 * c3 + 2 := step_d1_mod hm12
  have hm20 : (2 ^ 20 * o) % 643125 = 15 * c4 + 2 := step_d1_mod hm16
  have hm24 : (2 ^ 24 * o) % 643125 = 15 * c5 + 2 := step_d1_mod hm20
  have hpc1 : ∀ v, v % 4 = 0 → predCond 0 (2 ^ v * o) := fun v hv4 => by
    rw [predCond_0]
    have h24 : 2 ^ v % 5 = 1 := by
      have : v = 4 * (v / 4) := by omega
      rw [this, pow_mul, Nat.pow_mod]; norm_num
    rw [Nat.mul_mod, h24, ho5]
  have hw_c0 := wCertNat_pred_d1 ho (by omega) (hpc1 4 rfl) (Nat.mod_lt _ (by omega)) hm4
  have hw_c1 := wCertNat_pred_d1 ho (by omega) (hpc1 8 rfl) (Nat.mod_lt _ (by omega)) hm8
  have hw_c2 := wCertNat_pred_d1 ho (by omega) (hpc1 12 rfl) (Nat.mod_lt _ (by omega)) hm12
  have hw_c3 := wCertNat_pred_d1 ho (by omega) (hpc1 16 rfl) (Nat.mod_lt _ (by omega)) hm16
  have hw_c4 := wCertNat_pred_d1 ho (by omega) (hpc1 20 rfl) (Nat.mod_lt _ (by omega)) hm20
  have hw_c5 := wCertNat_pred_d1 ho (by omega) (hpc1 24 rfl) (Nat.mod_lt _ (by omega)) hm24
  have hs1_le :
      ((263054 * getWA c0 + 65991 * getWA c1 + 16555 * getWA c2 +
        4153 * getWA c3 + 1041 * getWA c4 + 261 * getWA c5 : ℕ) : ℝ) ≤
      1048576 * ∑ mv ∈ ({4, 8, 12, 16, 20, 24} : Finset ℕ).image (fun v => ((0 : Fin 5), v)),
        ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
          (wCertNat (predOf o mv) : ℝ) := by
    rw [Finset.sum_image (fun a _ b _ h => congr_arg Prod.snd h)]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      show (4 : ℕ) ≠ 8 by decide, show (4 : ℕ) ≠ 12 by decide, show (4 : ℕ) ≠ 16 by decide,
      show (4 : ℕ) ≠ 20 by decide, show (4 : ℕ) ≠ 24 by decide, show (8 : ℕ) ≠ 12 by decide,
      show (8 : ℕ) ≠ 16 by decide, show (8 : ℕ) ≠ 20 by decide, show (8 : ℕ) ≠ 24 by decide,
      show (12 : ℕ) ≠ 16 by decide, show (12 : ℕ) ≠ 20 by decide, show (12 : ℕ) ≠ 24 by decide,
      show (16 : ℕ) ≠ 20 by decide, show (16 : ℕ) ≠ 24 by decide, show (20 : ℕ) ≠ 24 by decide,
      or_self, not_false_eq_true, Finset.sum_singleton,
      digitVal_0, Nat.cast_one, hw_c0, hw_c1, hw_c2, hw_c3, hw_c4, hw_c5]
    push_cast
    have t0 := term1_le (c := 263054) (v := 4) rfl (getWA c0)
    have t1 := term1_le (c := 65991) (v := 8) rfl (getWA c1)
    have t2 := term1_le (c := 16555) (v := 12) rfl (getWA c2)
    have t3 := term1_le (c := 4153) (v := 16) rfl (getWA c3)
    have t4 := term1_le (c := 1041) (v := 20) rfl (getWA c4)
    have t5 := term1_le (c := 261) (v := 24) rfl (getWA c5)
    linarith
  have hdisj : ∀ S5 : Finset ℕ, Disjoint
      (({4, 8, 12, 16, 20, 24} : Finset ℕ).image (fun v => ((0 : Fin 5), v)))
      (S5.image (fun v => ((2 : Fin 5), v))) := by
    intro S5
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_image] at hx1 hx2
    obtain ⟨_, _, rfl⟩ := hx1; obtain ⟨_, _, h2⟩ := hx2
    exact (by decide : (2 : Fin 5) ≠ 0) (congr_arg Prod.fst h2)
  have h25_mod : o % 25 = (15 * (k % 5) + 2) % 25 := by
    have h1 : o % 25 = (o % 643125) % 25 := (Nat.mod_mod_of_dvd o (by decide)).symm
    rw [h1, ho_mod]; omega
  suffices hR : (wCertNat o : ℝ) * 1048576 ≤
      1048576 * ∑ mv ∈ certMoves o,
        ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
          (wCertNat (predOf o mv) : ℝ) by linarith
  have hcertR : (wCertNat o : ℝ) * 1048576 ≤ (sumC k : ℝ) := by
    rw [hw_eq]; exact_mod_cast hcert
  refine hcertR.trans ?_
  unfold certMoves
  simp only [← hk_def, h15, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]
  rw [Finset.sum_union (hdisj _), mul_add]
  have hk5 : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  rcases hk5 with hr | hr | hr | hr | hr
  · have hsumC : sumC k =
        (263054 * getWA c0 + 65991 * getWA c1 + 16555 * getWA c2 +
         4153 * getWA c3 + 1041 * getWA c4 + 261 * getWA c5) +
        3285 * getWB (((524288 * (o % 643125)) % 643125 - 1) / 75) := by
      unfold sumC; dsimp only; rw [hr, ← ho_mod]
    have hw5 := wCertNat_pred_d5 (v := 19) (p2v := 524288) ho (by omega)
      (by rw [predCond_2, Nat.mul_mod, h25_mod, hr]; decide) (by decide)
    have t5 := term5_le (c := 3285) (v := 19) rfl (getWB (((524288 * (o % 643125)) % 643125 - 1) / 75))
    rw [hsumC, Nat.cast_add, hr]
    simp only [Finset.image_singleton, Finset.sum_singleton, digitVal_2, hw5]
    refine add_le_add hs1_le ?_
    push_cast at t5 ⊢
    exact t5
  · have hsumC : sumC k =
        (263054 * getWA c0 + 65991 * getWA c1 + 16555 * getWA c2 +
         4153 * getWA c3 + 1041 * getWA c4 + 261 * getWA c5) +
        208084 * getWB (((128 * (o % 643125)) % 643125 - 1) / 75) := by
      unfold sumC; dsimp only; rw [hr, ← ho_mod]
    have hw5 := wCertNat_pred_d5 (v := 7) (p2v := 128) ho (by omega)
      (by rw [predCond_2, Nat.mul_mod, h25_mod, hr]; decide) (by decide)
    have t5 := term5_le (c := 208084) (v := 7) rfl (getWB (((128 * (o % 643125)) % 643125 - 1) / 75))
    rw [hsumC, Nat.cast_add, hr]
    simp only [Finset.image_singleton, Finset.sum_singleton, digitVal_2, hw5]
    refine add_le_add hs1_le ?_
    push_cast at t5 ⊢
    exact t5
  · have hsumC : sumC k =
        (263054 * getWA c0 + 65991 * getWA c1 + 16555 * getWA c2 +
         4153 * getWA c3 + 1041 * getWA c4 + 261 * getWA c5) +
        13095 * getWB (((32768 * (o % 643125)) % 643125 - 1) / 75) := by
      unfold sumC; dsimp only; rw [hr, ← ho_mod]
    have hw5 := wCertNat_pred_d5 (v := 15) (p2v := 32768) ho (by omega)
      (by rw [predCond_2, Nat.mul_mod, h25_mod, hr]; decide) (by decide)
    have t5 := term5_le (c := 13095) (v := 15) rfl (getWB (((32768 * (o % 643125)) % 643125 - 1) / 75))
    rw [hsumC, Nat.cast_add, hr]
    simp only [Finset.image_singleton, Finset.sum_singleton, digitVal_2, hw5]
    refine add_le_add hs1_le ?_
    push_cast at t5 ⊢
    exact t5
  · have hsumC : sumC k =
        (263054 * getWA c0 + 65991 * getWA c1 + 16555 * getWA c2 +
         4153 * getWA c3 + 1041 * getWA c4 + 261 * getWA c5) +
        (829459 * getWB (((8 * (o % 643125)) % 643125 - 1) / 75) +
         824 * getWB (((27983 * (o % 643125)) % 643125 - 1) / 75)) := by
      unfold sumC; dsimp only; rw [hr, ← ho_mod]
    have hw5a := wCertNat_pred_d5 (v := 3) (p2v := 8) ho (by omega)
      (by rw [predCond_2, Nat.mul_mod, h25_mod, hr]; decide) (by decide)
    have hw5b := wCertNat_pred_d5 (v := 23) (p2v := 27983) ho (by omega)
      (by rw [predCond_2, Nat.mul_mod, h25_mod, hr]; decide) (by decide)
    have t5a := term5_le (c := 829459) (v := 3) rfl (getWB (((8 * (o % 643125)) % 643125 - 1) / 75))
    have t5b := term5_le (c := 824) (v := 23) rfl (getWB (((27983 * (o % 643125)) % 643125 - 1) / 75))
    have hs5 : ∑ mv ∈ ({3, 23} : Finset ℕ).image (fun v => ((2 : Fin 5), v)),
        ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
          (wCertNat (predOf o mv) : ℝ) =
        ((5 : ℝ) / (2 : ℝ) ^ 3) ^ ((399 : ℝ) / 800) *
          (getWB (((8 * (o % 643125)) % 643125 - 1) / 75) : ℝ) +
        ((5 : ℝ) / (2 : ℝ) ^ 23) ^ ((399 : ℝ) / 800) *
          (getWB (((27983 * (o % 643125)) % 643125 - 1) / 75) : ℝ) := by
      rw [Finset.sum_image (fun a _ b _ h => congr_arg Prod.snd h)]
      simp only [Finset.sum_insert, Finset.mem_singleton, show (3 : ℕ) ≠ 23 by decide,
        not_false_eq_true, Finset.sum_singleton, digitVal_2, hw5a, hw5b]
      push_cast; rfl
    rw [hsumC, Nat.cast_add, hr]
    refine add_le_add hs1_le ?_
    change _ ≤ 1048576 * ∑ mv ∈ ({3, 23} : Finset ℕ).image (fun v => ((2 : Fin 5), v)), _
    rw [hs5]
    push_cast at t5a t5b ⊢
    linarith
  · have hsumC : sumC k =
        (263054 * getWA c0 + 65991 * getWA c1 + 16555 * getWA c2 +
         4153 * getWA c3 + 1041 * getWA c4 + 261 * getWA c5) +
        52201 * getWB (((2048 * (o % 643125)) % 643125 - 1) / 75) := by
      unfold sumC; dsimp only; rw [hr, ← ho_mod]
    have hw5 := wCertNat_pred_d5 (v := 11) (p2v := 2048) ho (by omega)
      (by rw [predCond_2, Nat.mul_mod, h25_mod, hr]; decide) (by decide)
    have t5 := term5_le (c := 52201) (v := 11) rfl (getWB (((2048 * (o % 643125)) % 643125 - 1) / 75))
    rw [hsumC, Nat.cast_add, hr]
    simp only [Finset.image_singleton, Finset.sum_singleton, digitVal_2, hw5]
    refine add_le_add hs1_le ?_
    push_cast at t5 ⊢
    exact t5

/-- Master bridge: the pure-kernel certificate implies the real super-eigenvector inequality
    at every `o ∈ A ∪ B ∪ C`. -/
private lemma certW_sub_eig {o : ℕ} (ho : InABC15 o) :
    (wCertNat o : ℝ) ≤
      ∑ mv ∈ certMoves o,
        ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
          (wCertNat (predOf o mv) : ℝ) := by
  rcases ho.2.2 with h15 | h15 | h15
  · exact certW_sub_eig_A ho h15
  · exact certW_sub_eig_B ho h15
  · exact certW_sub_eig_C ho h15

/-! ## Section 4: Geometric discarded-move bound (`< 5 / 2`) and strong tree induction -/

private lemma discarded_spaced_sum_le {p : ℕ} (hp : 1 ≤ p) {γ A : ℝ}
    (hγ : 0 < γ) (hA : 0 < A) (S : Finset ℕ)
    (hmod : ∀ u ∈ S, ∀ v ∈ S, u % p = v % p)
    (hlt1 : ∀ v ∈ S, A / (2 : ℝ) ^ v < 1) :
    ∑ v ∈ S, (A / (2 : ℝ) ^ v) ^ γ ≤ 1 / (1 - (2 : ℝ) ^ (-(γ * (p : ℝ)))) := by
  set r : ℝ := (2 : ℝ) ^ (-(γ * (p : ℝ)))
  have hr_pos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr_lt1 : r < 1 := by
    have hneg : -(γ * (p : ℝ)) < 0 := by
      have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
      nlinarith
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
  have h1r_pos : 0 < 1 - r := by linarith
  by_cases hne : S.Nonempty
  · set v0 := S.min' hne
    have hv0_mem : v0 ∈ S := Finset.min'_mem S hne
    have hv_decomp : ∀ v ∈ S, v = v0 + p * ((v - v0) / p) := by
      intro v hv
      have hv_ge : v0 ≤ v := Finset.min'_le S v hv
      have hmv : v % p = v0 % p := hmod v hv v0 hv0_mem
      have hdvd : p ∣ v - v0 := (Nat.modEq_iff_dvd' hv_ge).mp hmv.symm
      have hmul := Nat.mul_div_cancel' hdvd
      omega
    have hterm_le : ∀ v ∈ S, (A / (2 : ℝ) ^ v) ^ γ ≤ r ^ ((v - v0) / p) := by
      intro v hv
      set j := (v - v0) / p
      have hv_eq : v = v0 + p * j := hv_decomp v hv
      have hdiv_le : A / (2 : ℝ) ^ v ≤ ((2 : ℝ) ^ p)⁻¹ ^ j := by
        have hv0_lt : A / (2 : ℝ) ^ v0 ≤ 1 := (hlt1 v0 hv0_mem).le
        calc A / (2 : ℝ) ^ v
            = (A / (2 : ℝ) ^ v0) * ((2 : ℝ) ^ p)⁻¹ ^ j := by
              rw [hv_eq, pow_add, pow_mul, inv_pow]; field_simp
          _ ≤ 1 * ((2 : ℝ) ^ p)⁻¹ ^ j :=
              mul_le_mul_of_nonneg_right hv0_lt (by positivity)
          _ = ((2 : ℝ) ^ p)⁻¹ ^ j := one_mul _
      have hrj : (((2 : ℝ) ^ p)⁻¹ ^ j) ^ γ = r ^ j := by
        rw [← Real.rpow_natCast (((2 : ℝ) ^ p)⁻¹) j, ← Real.rpow_mul (by positivity),
            mul_comm (j : ℝ) γ, Real.rpow_mul (by positivity), Real.rpow_natCast]
        congr 1
        rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast 2 p,
            ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
        congr 1; ring
      calc (A / (2 : ℝ) ^ v) ^ γ
          ≤ (((2 : ℝ) ^ p)⁻¹ ^ j) ^ γ := Real.rpow_le_rpow (by positivity) hdiv_le hγ.le
        _ = r ^ j := hrj
    have h1 : ∑ v ∈ S, (A / (2 : ℝ) ^ v) ^ γ ≤ ∑ v ∈ S, r ^ ((v - v0) / p) :=
      Finset.sum_le_sum hterm_le
    set N := (S.max' hne - v0) / p + 1
    have hinj : Set.InjOn (fun v => (v - v0) / p) (S : Set ℕ) := by
      intro a ha b hb hab
      dsimp only at hab
      rw [hv_decomp a ha, hv_decomp b hb, hab]
    have himg_sub : S.image (fun v => (v - v0) / p) ⊆ Finset.range N := by
      intro j hj
      simp only [Finset.mem_image] at hj
      obtain ⟨v, hv, rfl⟩ := hj
      have hv_le : v ≤ S.max' hne := Finset.le_max' S v hv
      simp only [Finset.mem_range, N]
      have : (v - v0) / p ≤ (S.max' hne - v0) / p := Nat.div_le_div_right (by omega)
      omega
    have h2 : ∑ v ∈ S, r ^ ((v - v0) / p) ≤ ∑ j ∈ Finset.range N, r ^ j := by
      rw [← Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
      exact Finset.sum_le_sum_of_subset_of_nonneg himg_sub fun _ _ _ => by positivity
    have hgeom : ∑ j ∈ Finset.range N, r ^ j ≤ 1 / (1 - r) := by
      rw [geom_sum_eq (ne_of_lt hr_lt1)]
      have hnn : 0 ≤ r ^ N := by positivity
      have hnum : r ^ N - 1 = -(1 - r ^ N) := by ring
      have hden : r - 1 = -(1 - r) := by ring
      rw [hnum, hden, neg_div_neg_eq]
      exact div_le_div_of_nonneg_right (by linarith) h1r_pos.le
    exact h1.trans (h2.trans hgeom)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    positivity

private lemma geom_bound_AC :
    1 / (1 - (2 : ℝ) ^ (-(((399 : ℝ) / 800) * (4 : ℕ)))) +
    1 / (1 - (2 : ℝ) ^ (-(((399 : ℝ) / 800) * (20 : ℕ)))) ≤ (5 / 2 : ℝ) := by
  have h1 : (2 : ℝ) ^ (-(((399 : ℝ) / 800) * (4 : ℕ))) ≤ 3 / 10 := by
    have hle : (2 : ℝ) ^ (-(((399 : ℝ) / 800) * (4 : ℕ))) ≤ (2 : ℝ) ^ (-(7 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h74 : (2 : ℝ) ^ (-(7 / 4 : ℝ)) ≤ 3 / 10 := by
      have hpow : ((2 : ℝ) ^ (-(7 / 4 : ℝ))) ^ (4 : ℕ) ≤ (3 / 10 : ℝ) ^ (4 : ℕ) := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ _) 4, ← Real.rpow_mul (by norm_num)]
        have hexp : -(7 / 4 : ℝ) * (4 : ℕ) = -((7 : ℕ) : ℝ) := by norm_num
        rw [hexp, Real.rpow_neg (by norm_num), Real.rpow_natCast]
        norm_num
      exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
    exact hle.trans h74
  have h2 : (2 : ℝ) ^ (-(((399 : ℝ) / 800) * (20 : ℕ))) ≤ 1 / 256 := by
    have hle : (2 : ℝ) ^ (-(((399 : ℝ) / 800) * (20 : ℕ))) ≤ (2 : ℝ) ^ (-(8 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h8 : (2 : ℝ) ^ (-(8 : ℝ)) = 1 / 256 := by
      rw [Real.rpow_neg (by norm_num)]; norm_num
    linarith
  have hb1 : 1 / (1 - (2 : ℝ) ^ (-(((399 : ℝ) / 800) * (4 : ℕ)))) ≤ 10 / 7 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hb2 : 1 / (1 - (2 : ℝ) ^ (-(((399 : ℝ) / 800) * (20 : ℕ)))) ≤ 256 / 255 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  linarith

private lemma geom_bound_B :
    1 / (1 - (2 : ℝ) ^ (-(((399 : ℝ) / 800) * (3 : ℕ)))) ≤ (5 / 2 : ℝ) := by
  have h1 : (2 : ℝ) ^ (-(((399 : ℝ) / 800) * (3 : ℕ))) ≤ 3 / 7 := by
    have hle : (2 : ℝ) ^ (-(((399 : ℝ) / 800) * (3 : ℕ))) ≤ (2 : ℝ) ^ (-(5 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h54 : (2 : ℝ) ^ (-(5 / 4 : ℝ)) ≤ 3 / 7 := by
      have hpow : ((2 : ℝ) ^ (-(5 / 4 : ℝ))) ^ (4 : ℕ) ≤ (3 / 7 : ℝ) ^ (4 : ℕ) := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ _) 4, ← Real.rpow_mul (by norm_num)]
        have hexp : -(5 / 4 : ℝ) * (4 : ℕ) = -((5 : ℕ) : ℝ) := by norm_num
        rw [hexp, Real.rpow_neg (by norm_num), Real.rpow_natCast]
        norm_num
      exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hpow
    exact hle.trans h54
  have hb : 1 / (1 - (2 : ℝ) ^ (-(((399 : ℝ) / 800) * (3 : ℕ)))) ≤ 7 / 4 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  linarith

private lemma discarded_certMoves_sum_le {o : ℕ} (ho : InABC15 o) {X : ℝ} (hX : (o : ℝ) ≤ X) :
    ∑ mv ∈ (certMoves o).filter (fun mv => (digitVal mv.1 : ℝ) * X < (2 : ℝ) ^ mv.2 * (o : ℝ)),
      ((X * (digitVal mv.1 : ℝ)) / ((o : ℝ) * (2 : ℝ) ^ mv.2)) ^ ((399 : ℝ) / 800) ≤ (5 / 2 : ℝ) := by
  have ho_pos : (0 : ℝ) < (o : ℝ) := by exact_mod_cast ho.1
  have hX_pos : 0 < X := lt_of_lt_of_le ho_pos hX
  set D := (certMoves o).filter (fun mv => (digitVal mv.1 : ℝ) * X < (2 : ℝ) ^ mv.2 * (o : ℝ))
  have hlt1_of : ∀ mv ∈ D, (X * (digitVal mv.1 : ℝ) / (o : ℝ)) / (2 : ℝ) ^ mv.2 < 1 := by
    intro mv hmv
    have hlt := (Finset.mem_filter.mp hmv).2
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ mv.2 := by positivity
    rw [div_lt_one h2pos, div_lt_iff₀ ho_pos]
    linarith
  have heq_arg : ∀ mv : Fin 5 × ℕ,
      (X * (digitVal mv.1 : ℝ)) / ((o : ℝ) * (2 : ℝ) ^ mv.2) =
        (X * (digitVal mv.1 : ℝ) / (o : ℝ)) / (2 : ℝ) ^ mv.2 := fun mv => by ring
  set k := (o % 643125) / 15 with hk_def
  have ho15 := ho.2.2
  rcases ho15 with h15 | h15 | h15
  · -- Class A
    let S1 : Finset ℕ := (D.filter (fun mv => mv.1 = 0)).image Prod.snd
    let S5 : Finset ℕ := (D.filter (fun mv => mv.1 = 2)).image Prod.snd
    have hD_sub : D ⊆ S1.image (fun v => ((0 : Fin 5), v)) ∪ S5.image (fun v => ((2 : Fin 5), v)) := by
      intro mv hmv
      have hcm := (Finset.mem_filter.mp hmv).1
      simp only [certMoves, ← hk_def, h15, ↓reduceIte, Finset.mem_union, Finset.mem_image] at hcm
      simp only [Finset.mem_union, Finset.mem_image, S1, S5, Finset.mem_filter]
      rcases hcm with ⟨v, _, rfl⟩ | ⟨v, _, rfl⟩
      · exact Or.inl ⟨v, ⟨(0, v), ⟨hmv, rfl⟩, rfl⟩, rfl⟩
      · exact Or.inr ⟨v, ⟨(2, v), ⟨hmv, rfl⟩, rfl⟩, rfl⟩
    have hdisj : Disjoint (S1.image (fun v => ((0 : Fin 5), v))) (S5.image (fun v => ((2 : Fin 5), v))) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_image] at hx1 hx2
      obtain ⟨_, _, rfl⟩ := hx1; obtain ⟨_, _, h2⟩ := hx2
      exact (by decide : (2 : Fin 5) ≠ 0) (congr_arg Prod.fst h2)
    have hS1_mod1 : ∀ u ∈ S1, u % 4 = 1 := by
      intro u hu
      simp only [S1, Finset.mem_image, Finset.mem_filter] at hu
      obtain ⟨⟨i, u'⟩, ⟨h1, hi⟩, rfl⟩ := hu
      dsimp only at hi; subst hi
      have hcm := (Finset.mem_filter.mp h1).1
      simp only [certMoves, ← hk_def, h15, ↓reduceIte, Finset.mem_union, Finset.mem_image] at hcm
      rcases hcm with ⟨a, ha, heq⟩ | ⟨_, _, heq⟩
      · have h' : a = u' := congr_arg Prod.snd heq
        subst h'
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      · exact absurd (congr_arg Prod.fst heq) (by decide : (2 : Fin 5) ≠ 0)
    have hS5_mod : ∀ u ∈ S5, ∀ v ∈ S5, u % 20 = v % 20 := by
      have hS5_mem : ∀ u ∈ S5, u ∈ (match k % 5 with
          | 0 => {20} | 1 => {16} | 2 => {12} | 3 => {8} | _ => {4, 24} : Finset ℕ) := by
        intro u hu
        simp only [S5, Finset.mem_image, Finset.mem_filter] at hu
        obtain ⟨⟨i, u'⟩, ⟨h1, hi⟩, rfl⟩ := hu
        dsimp only at hi; subst hi
        have hcm := (Finset.mem_filter.mp h1).1
        simp only [certMoves, ← hk_def, h15, ↓reduceIte, Finset.mem_union, Finset.mem_image] at hcm
        rcases hcm with ⟨_, _, heq⟩ | ⟨a, ha, heq⟩
        · exact absurd (congr_arg Prod.fst heq) (by decide : (0 : Fin 5) ≠ 2)
        · have h' : a = u' := congr_arg Prod.snd heq; subst h'; exact ha
      intro u hu v hv
      have hu' := hS5_mem u hu
      have hv' := hS5_mem v hv
      have hk5 : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
      rcases hk5 with hr | hr | hr | hr | hr
      · rw [hr] at hu' hv'; simp only [Finset.mem_singleton] at hu' hv'; rw [hu', hv']
      · rw [hr] at hu' hv'; simp only [Finset.mem_singleton] at hu' hv'; rw [hu', hv']
      · rw [hr] at hu' hv'; simp only [Finset.mem_singleton] at hu' hv'; rw [hu', hv']
      · rw [hr] at hu' hv'; simp only [Finset.mem_singleton] at hu' hv'; rw [hu', hv']
      · rw [hr] at hu' hv'; simp only [Finset.mem_insert, Finset.mem_singleton] at hu' hv'
        rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl <;> decide
    have hS1_lt : ∀ v ∈ S1, (X * (1 : ℝ) / (o : ℝ)) / (2 : ℝ) ^ v < 1 := by
      intro v hv
      simp only [S1, Finset.mem_image, Finset.mem_filter] at hv
      obtain ⟨⟨i, v'⟩, ⟨hmv, hi⟩, rfl⟩ := hv
      dsimp only at hi; subst hi
      simpa [digitVal] using hlt1_of (0, v') hmv
    have hS5_lt : ∀ v ∈ S5, (X * (5 : ℝ) / (o : ℝ)) / (2 : ℝ) ^ v < 1 := by
      intro v hv
      simp only [S5, Finset.mem_image, Finset.mem_filter] at hv
      obtain ⟨⟨i, v'⟩, ⟨hmv, hi⟩, rfl⟩ := hv
      dsimp only at hi; subst hi
      simpa [digitVal] using hlt1_of (2, v') hmv
    have hb1 := discarded_spaced_sum_le (p := 4) (γ := (399 : ℝ) / 800) (by omega)
      (by norm_num) (by positivity) S1 (fun u hu v hv => by rw [hS1_mod1 u hu, hS1_mod1 v hv]) hS1_lt
    have hb5 := discarded_spaced_sum_le (p := 20) (γ := (399 : ℝ) / 800) (by omega)
      (by norm_num) (by positivity) S5 hS5_mod hS5_lt
    calc ∑ mv ∈ D, ((X * (digitVal mv.1 : ℝ)) / ((o : ℝ) * (2 : ℝ) ^ mv.2)) ^ ((399 : ℝ) / 800)
        ≤ ∑ mv ∈ S1.image (fun v => ((0 : Fin 5), v)) ∪ S5.image (fun v => ((2 : Fin 5), v)),
            ((X * (digitVal mv.1 : ℝ)) / ((o : ℝ) * (2 : ℝ) ^ mv.2)) ^ ((399 : ℝ) / 800) :=
          Finset.sum_le_sum_of_subset_of_nonneg hD_sub fun _ _ _ => by positivity
      _ = ∑ v ∈ S1, ((X * (1 : ℝ) / (o : ℝ)) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) +
          ∑ v ∈ S5, ((X * (5 : ℝ) / (o : ℝ)) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) := by
          rw [Finset.sum_union hdisj,
              Finset.sum_image (fun a _ b _ h => congr_arg Prod.snd h),
              Finset.sum_image (fun a _ b _ h => congr_arg Prod.snd h)]
          congr 1
          · refine Finset.sum_congr rfl fun v _ => by rw [heq_arg]; simp [digitVal]
          · refine Finset.sum_congr rfl fun v _ => by rw [heq_arg]; simp [digitVal]
      _ ≤ 1 / (1 - (2 : ℝ) ^ (-(((399 : ℝ) / 800) * (4 : ℕ)))) +
          1 / (1 - (2 : ℝ) ^ (-(((399 : ℝ) / 800) * (20 : ℕ)))) := add_le_add hb1 hb5
      _ ≤ 5 / 2 := geom_bound_AC
  · -- Class B
    let S7 : Finset ℕ := (D.filter (fun mv => mv.1 = 3)).image Prod.snd
    have hD_sub : D ⊆ S7.image (fun v => ((3 : Fin 5), v)) := by
      intro mv hmv
      have hcm := (Finset.mem_filter.mp hmv).1
      simp only [certMoves, ← hk_def, h15, show (0 : ℕ) ≠ 1 by decide,
        show (0 : ℕ) ≠ 2 by decide, ↓reduceIte, Finset.mem_image] at hcm
      obtain ⟨v, _, rfl⟩ := hcm
      simp only [Finset.mem_image, S7, Finset.mem_filter]
      exact ⟨v, ⟨(3, v), ⟨hmv, rfl⟩, rfl⟩, rfl⟩
    have hS7_mod : ∀ u ∈ S7, ∀ v ∈ S7, u % 3 = v % 3 := by
      have hS7_mem : ∀ u ∈ S7, u ∈ (match k % 7 with
          | 4 => {1, 4, 7, 10, 13, 16, 19, 22, 25}
          | 2 => {2, 5, 8, 11, 14, 17, 20, 23}
          | 1 => {3, 6, 9, 12, 15, 18, 21, 24}
          | _ => ∅ : Finset ℕ) := by
        intro u hu
        simp only [S7, Finset.mem_image, Finset.mem_filter] at hu
        obtain ⟨⟨i, u'⟩, ⟨h1, hi⟩, rfl⟩ := hu
        dsimp only at hi; subst hi
        have hcm := (Finset.mem_filter.mp h1).1
        simp only [certMoves, ← hk_def, h15, show (0 : ℕ) ≠ 1 by decide,
          show (0 : ℕ) ≠ 2 by decide, ↓reduceIte, Finset.mem_image] at hcm
        obtain ⟨a, ha, heq⟩ := hcm
        have h' : a = u' := congr_arg Prod.snd heq; subst h'; exact ha
      intro u hu v hv
      have hu' := hS7_mem u hu
      have hv' := hS7_mem v hv
      have hk7 : k % 7 = 0 ∨ k % 7 = 1 ∨ k % 7 = 2 ∨ k % 7 = 3 ∨
          k % 7 = 4 ∨ k % 7 = 5 ∨ k % 7 = 6 := by omega
      rcases hk7 with hr | hr | hr | hr | hr | hr | hr
      · rw [hr] at hu'; simp at hu'
      · rw [hr] at hu' hv'
        have h1 : u % 3 = 0 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu'
          rcases hu' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        have h2 : v % 3 = 0 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv'
          rcases hv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [h1, h2]
      · rw [hr] at hu' hv'
        have h1 : u % 3 = 2 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu'
          rcases hu' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        have h2 : v % 3 = 2 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv'
          rcases hv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [h1, h2]
      · rw [hr] at hu'; simp at hu'
      · rw [hr] at hu' hv'
        have h1 : u % 3 = 1 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu'
          rcases hu' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        have h2 : v % 3 = 1 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv'
          rcases hv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [h1, h2]
      · rw [hr] at hu'; simp at hu'
      · rw [hr] at hu'; simp at hu'
    have hS7_lt : ∀ v ∈ S7, (X * (7 : ℝ) / (o : ℝ)) / (2 : ℝ) ^ v < 1 := by
      intro v hv
      simp only [S7, Finset.mem_image, Finset.mem_filter] at hv
      obtain ⟨⟨i, v'⟩, ⟨hmv, hi⟩, rfl⟩ := hv
      dsimp only at hi; subst hi
      simpa [digitVal] using hlt1_of (3, v') hmv
    have hb7 := discarded_spaced_sum_le (p := 3) (γ := (399 : ℝ) / 800) (by omega)
      (by norm_num) (by positivity) S7 hS7_mod hS7_lt
    calc ∑ mv ∈ D, ((X * (digitVal mv.1 : ℝ)) / ((o : ℝ) * (2 : ℝ) ^ mv.2)) ^ ((399 : ℝ) / 800)
        ≤ ∑ mv ∈ S7.image (fun v => ((3 : Fin 5), v)),
            ((X * (digitVal mv.1 : ℝ)) / ((o : ℝ) * (2 : ℝ) ^ mv.2)) ^ ((399 : ℝ) / 800) :=
          Finset.sum_le_sum_of_subset_of_nonneg hD_sub fun _ _ _ => by positivity
      _ = ∑ v ∈ S7, ((X * (7 : ℝ) / (o : ℝ)) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) := by
          rw [Finset.sum_image (fun a _ b _ h => congr_arg Prod.snd h)]
          refine Finset.sum_congr rfl fun v _ => by rw [heq_arg]; simp [digitVal]
      _ ≤ 1 / (1 - (2 : ℝ) ^ (-(((399 : ℝ) / 800) * (3 : ℕ)))) := hb7
      _ ≤ 5 / 2 := geom_bound_B
  · -- Class C
    let S1 : Finset ℕ := (D.filter (fun mv => mv.1 = 0)).image Prod.snd
    let S5 : Finset ℕ := (D.filter (fun mv => mv.1 = 2)).image Prod.snd
    have hD_sub : D ⊆ S1.image (fun v => ((0 : Fin 5), v)) ∪ S5.image (fun v => ((2 : Fin 5), v)) := by
      intro mv hmv
      have hcm := (Finset.mem_filter.mp hmv).1
      simp only [certMoves, ← hk_def, h15, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte,
        Finset.mem_union, Finset.mem_image] at hcm
      simp only [Finset.mem_union, Finset.mem_image, S1, S5, Finset.mem_filter]
      rcases hcm with ⟨v, _, rfl⟩ | ⟨v, _, rfl⟩
      · exact Or.inl ⟨v, ⟨(0, v), ⟨hmv, rfl⟩, rfl⟩, rfl⟩
      · exact Or.inr ⟨v, ⟨(2, v), ⟨hmv, rfl⟩, rfl⟩, rfl⟩
    have hdisj : Disjoint (S1.image (fun v => ((0 : Fin 5), v))) (S5.image (fun v => ((2 : Fin 5), v))) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_image] at hx1 hx2
      obtain ⟨_, _, rfl⟩ := hx1; obtain ⟨_, _, h2⟩ := hx2
      exact (by decide : (2 : Fin 5) ≠ 0) (congr_arg Prod.fst h2)
    have hS1_mod0 : ∀ u ∈ S1, u % 4 = 0 := by
      intro u hu
      simp only [S1, Finset.mem_image, Finset.mem_filter] at hu
      obtain ⟨⟨i, u'⟩, ⟨h1, hi⟩, rfl⟩ := hu
      dsimp only at hi; subst hi
      have hcm := (Finset.mem_filter.mp h1).1
      simp only [certMoves, ← hk_def, h15, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte,
        Finset.mem_union, Finset.mem_image] at hcm
      rcases hcm with ⟨a, ha, heq⟩ | ⟨_, _, heq⟩
      · have h' : a = u' := congr_arg Prod.snd heq; subst h'
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      · exact absurd (congr_arg Prod.fst heq) (by decide : (2 : Fin 5) ≠ 0)
    have hS5_mod : ∀ u ∈ S5, ∀ v ∈ S5, u % 20 = v % 20 := by
      have hS5_mem : ∀ u ∈ S5, u ∈ (match k % 5 with
          | 0 => {19} | 1 => {7} | 2 => {15} | 3 => {3, 23} | _ => {11} : Finset ℕ) := by
        intro u hu
        simp only [S5, Finset.mem_image, Finset.mem_filter] at hu
        obtain ⟨⟨i, u'⟩, ⟨h1, hi⟩, rfl⟩ := hu
        dsimp only at hi; subst hi
        have hcm := (Finset.mem_filter.mp h1).1
        simp only [certMoves, ← hk_def, h15, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte,
          Finset.mem_union, Finset.mem_image] at hcm
        rcases hcm with ⟨_, _, heq⟩ | ⟨a, ha, heq⟩
        · exact absurd (congr_arg Prod.fst heq) (by decide : (0 : Fin 5) ≠ 2)
        · have h' : a = u' := congr_arg Prod.snd heq; subst h'; exact ha
      intro u hu v hv
      have hu' := hS5_mem u hu
      have hv' := hS5_mem v hv
      have hk5 : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
      rcases hk5 with hr | hr | hr | hr | hr
      · rw [hr] at hu' hv'; simp only [Finset.mem_singleton] at hu' hv'; rw [hu', hv']
      · rw [hr] at hu' hv'; simp only [Finset.mem_singleton] at hu' hv'; rw [hu', hv']
      · rw [hr] at hu' hv'; simp only [Finset.mem_singleton] at hu' hv'; rw [hu', hv']
      · rw [hr] at hu' hv'; simp only [Finset.mem_insert, Finset.mem_singleton] at hu' hv'
        rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl <;> decide
      · rw [hr] at hu' hv'; simp only [Finset.mem_singleton] at hu' hv'; rw [hu', hv']
    have hS1_lt : ∀ v ∈ S1, (X * (1 : ℝ) / (o : ℝ)) / (2 : ℝ) ^ v < 1 := by
      intro v hv
      simp only [S1, Finset.mem_image, Finset.mem_filter] at hv
      obtain ⟨⟨i, v'⟩, ⟨hmv, hi⟩, rfl⟩ := hv
      dsimp only at hi; subst hi
      simpa [digitVal] using hlt1_of (0, v') hmv
    have hS5_lt : ∀ v ∈ S5, (X * (5 : ℝ) / (o : ℝ)) / (2 : ℝ) ^ v < 1 := by
      intro v hv
      simp only [S5, Finset.mem_image, Finset.mem_filter] at hv
      obtain ⟨⟨i, v'⟩, ⟨hmv, hi⟩, rfl⟩ := hv
      dsimp only at hi; subst hi
      simpa [digitVal] using hlt1_of (2, v') hmv
    have hb1 := discarded_spaced_sum_le (p := 4) (γ := (399 : ℝ) / 800) (by omega)
      (by norm_num) (by positivity) S1 (fun u hu v hv => by rw [hS1_mod0 u hu, hS1_mod0 v hv]) hS1_lt
    have hb5 := discarded_spaced_sum_le (p := 20) (γ := (399 : ℝ) / 800) (by omega)
      (by norm_num) (by positivity) S5 hS5_mod hS5_lt
    calc ∑ mv ∈ D, ((X * (digitVal mv.1 : ℝ)) / ((o : ℝ) * (2 : ℝ) ^ mv.2)) ^ ((399 : ℝ) / 800)
        ≤ ∑ mv ∈ S1.image (fun v => ((0 : Fin 5), v)) ∪ S5.image (fun v => ((2 : Fin 5), v)),
            ((X * (digitVal mv.1 : ℝ)) / ((o : ℝ) * (2 : ℝ) ^ mv.2)) ^ ((399 : ℝ) / 800) :=
          Finset.sum_le_sum_of_subset_of_nonneg hD_sub fun _ _ _ => by positivity
      _ = ∑ v ∈ S1, ((X * (1 : ℝ) / (o : ℝ)) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) +
          ∑ v ∈ S5, ((X * (5 : ℝ) / (o : ℝ)) / (2 : ℝ) ^ v) ^ ((399 : ℝ) / 800) := by
          rw [Finset.sum_union hdisj,
              Finset.sum_image (fun a _ b _ h => congr_arg Prod.snd h),
              Finset.sum_image (fun a _ b _ h => congr_arg Prod.snd h)]
          congr 1
          · refine Finset.sum_congr rfl fun v _ => by rw [heq_arg]; simp [digitVal]
          · refine Finset.sum_congr rfl fun v _ => by rw [heq_arg]; simp [digitVal]
      _ ≤ 1 / (1 - (2 : ℝ) ^ (-(((399 : ℝ) / 800) * (4 : ℕ)))) +
          1 / (1 - (2 : ℝ) ^ (-(((399 : ℝ) / 800) * (20 : ℕ)))) := add_le_add hb1 hb5
      _ ≤ 5 / 2 := geom_bound_AC

/-- Strong-induction predecessor-tree lower bound on `A ∪ B ∪ C` for every real `X ≥ o`:
    `NTree o ⌊X⌋₊ ≥ (2 / 5) * (w(o) / 65535) * (X / o)^(399 / 800)`. -/
private theorem lemma_basin1_lower_tree (o : ℕ) (X : ℝ) (ho : InABC15 o)
    (hX : (o : ℝ) ≤ X) (hnp : NonPeriodic o) :
    (2 / 5 : ℝ) * ((wCertNat o : ℝ) / 65535) * (X / (o : ℝ)) ^ ((399 : ℝ) / 800) ≤
      (NTree o ⌊X⌋₊ : ℝ) := by
  set eps : ℝ := (2 / 5 : ℝ) / 65535
  have heps_pos : 0 < eps := by unfold eps; norm_num
  suffices hstrong : ∀ N : ℕ, ∀ (o : ℕ) (X : ℝ), NTree o ⌊X⌋₊ = N →
      InABC15 o → (o : ℝ) ≤ X → NonPeriodic o →
      eps * (wCertNat o : ℝ) * (X / (o : ℝ)) ^ ((399 : ℝ) / 800) ≤ (NTree o ⌊X⌋₊ : ℝ) by
    have h := hstrong (NTree o ⌊X⌋₊) o X rfl ho hX hnp
    have heq : (2 / 5 : ℝ) * ((wCertNat o : ℝ) / 65535) * (X / (o : ℝ)) ^ ((399 : ℝ) / 800) =
        eps * (wCertNat o : ℝ) * (X / (o : ℝ)) ^ ((399 : ℝ) / 800) := by unfold eps; ring
    rw [heq]; exact h
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro o X hN_eq ho hX hnp
    classical
    have ho_posR : (0 : ℝ) < (o : ℝ) := by exact_mod_cast ho.1
    have hX_pos : 0 < X := lt_of_lt_of_le ho_posR hX
    have ho_le_fl : o ≤ ⌊X⌋₊ := Nat.le_floor hX
    let admitted : Finset (Fin 5 × ℕ) :=
      (certMoves o).filter fun mv => (2 : ℝ) ^ mv.2 * (o : ℝ) ≤ (digitVal mv.1 : ℝ) * X
    let discarded : Finset (Fin 5 × ℕ) :=
      (certMoves o).filter fun mv => ¬ ((2 : ℝ) ^ mv.2 * (o : ℝ) ≤ (digitVal mv.1 : ℝ) * X)
    have hpred_inj : Set.InjOn (predOf o) (admitted : Set _) := by
      intro mv1 h1 mv2 h2 hEq
      have h1m := (Finset.mem_filter.mp h1).1
      have h2m := (Finset.mem_filter.mp h2).1
      obtain ⟨_, _, hd1, heq1, _⟩ := predOf_props ho h1m
      obtain ⟨_, _, hd2, heq2, _⟩ := predOf_props ho h2m
      have hi : mv1.1 = mv2.1 := digitVal_inj (by rw [← hd1, ← hd2, hEq])
      have hpow : 2 ^ mv1.2 * o = 2 ^ mv2.2 * o := by rw [← heq1, ← heq2, hEq]
      have hexp := (two_pow_mul_odd_inj ho.2.1 ho.2.1 hpow).1
      exact Prod.ext hi hexp
    let S : Finset ℕ := admitted.image (predOf o)
    have hS_valid : ∀ m ∈ S, m ≤ ⌊X⌋₊ ∧ m % 2 = 1 ∧ ∃ v ≥ 1, d m * m + 1 = 2 ^ v * o := by
      intro m hm
      simp only [S, Finset.mem_image] at hm
      obtain ⟨mv, hmv, rfl⟩ := hm
      have hcm := (Finset.mem_filter.mp hmv).1
      have hle_R := (Finset.mem_filter.mp hmv).2
      obtain ⟨hm_abc, hv1, hdm, heq, _⟩ := predOf_props ho hcm
      have hm_le_X : (predOf o mv : ℝ) ≤ X := by
        have hd_posR : (0 : ℝ) < (digitVal mv.1 : ℝ) := by exact_mod_cast digitVal_pos mv.1
        have hmul_nat : digitVal mv.1 * predOf o mv < 2 ^ mv.2 * o := by
          rw [← hdm]; omega
        have hmul_R : (digitVal mv.1 : ℝ) * (predOf o mv : ℝ) < (2 : ℝ) ^ mv.2 * (o : ℝ) := by
          exact_mod_cast hmul_nat
        nlinarith
      exact ⟨Nat.le_floor hm_le_X, hm_abc.2.1, mv.2, hv1, heq⟩
    obtain ⟨hN_sum, hN_lt⟩ := NTree_ge_one_add_sum ho.1 ho.2.1 ho_le_fl hnp S hS_valid
    have hadm_le :
        eps * (X / (o : ℝ)) ^ ((399 : ℝ) / 800) *
          ∑ mv ∈ admitted,
            ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
              (wCertNat (predOf o mv) : ℝ) ≤
        ∑ m ∈ S, (NTree m ⌊X⌋₊ : ℝ) := by
      unfold S
      rw [Finset.sum_image (fun a ha b hb h => hpred_inj ha hb h), Finset.mul_sum]
      refine Finset.sum_le_sum fun mv hmv => ?_
      have hcm := (Finset.mem_filter.mp hmv).1
      have hle_R := (Finset.mem_filter.mp hmv).2
      obtain ⟨hm_abc, _, hdm, heq, hstep⟩ := predOf_props ho hcm
      have hm_in_S : predOf o mv ∈ admitted.image (predOf o) :=
        Finset.mem_image.mpr ⟨mv, hmv, rfl⟩
      have hlt_N : NTree (predOf o mv) ⌊X⌋₊ < N := by
        rw [← hN_eq]; exact hN_lt _ hm_in_S
      have hm_le_X : (predOf o mv : ℝ) ≤ X := by
        have hd_posR : (0 : ℝ) < (digitVal mv.1 : ℝ) := by exact_mod_cast digitVal_pos mv.1
        have hmul_nat : digitVal mv.1 * predOf o mv < 2 ^ mv.2 * o := by
          rw [← hdm]; omega
        have hmul_R : (digitVal mv.1 : ℝ) * (predOf o mv : ℝ) < (2 : ℝ) ^ mv.2 * (o : ℝ) := by
          exact_mod_cast hmul_nat
        nlinarith
      have hm_np : NonPeriodic (predOf o mv) :=
        nonperiodic_of_reaches ⟨mv.2 + 1, hstep⟩ hnp
      have hih := ih (NTree (predOf o mv) ⌊X⌋₊) hlt_N (predOf o mv) X rfl hm_abc hm_le_X hm_np
      have hratio : (X / (o : ℝ)) * ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ≤
          X / (predOf o mv : ℝ) := by
        have hm_posR : (0 : ℝ) < (predOf o mv : ℝ) := by exact_mod_cast hm_abc.1
        have h2pos : (0 : ℝ) < (2 : ℝ) ^ mv.2 := by positivity
        have hmul_nat : digitVal mv.1 * predOf o mv ≤ 2 ^ mv.2 * o := by
          rw [← hdm]; omega
        have hmul_R : (digitVal mv.1 : ℝ) * (predOf o mv : ℝ) ≤ (2 : ℝ) ^ mv.2 * (o : ℝ) := by
          exact_mod_cast hmul_nat
        rw [le_div_iff₀ hm_posR]
        have h1 : (X / (o : ℝ)) * ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) * (predOf o mv : ℝ) =
            X * ((digitVal mv.1 : ℝ) * (predOf o mv : ℝ)) / ((2 : ℝ) ^ mv.2 * (o : ℝ)) := by ring
        rw [h1, div_le_iff₀ (mul_pos h2pos ho_posR)]
        nlinarith
      have hpow : (X / (o : ℝ)) ^ ((399 : ℝ) / 800) *
            ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) ≤
          (X / (predOf o mv : ℝ)) ^ ((399 : ℝ) / 800) := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        exact Real.rpow_le_rpow (by positivity) hratio (by norm_num)
      calc eps * (X / (o : ℝ)) ^ ((399 : ℝ) / 800) *
            (((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
              (wCertNat (predOf o mv) : ℝ))
          = eps * (wCertNat (predOf o mv) : ℝ) *
              ((X / (o : ℝ)) ^ ((399 : ℝ) / 800) *
                ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800)) := by ring
        _ ≤ eps * (wCertNat (predOf o mv) : ℝ) *
              (X / (predOf o mv : ℝ)) ^ ((399 : ℝ) / 800) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ ≤ (NTree (predOf o mv) ⌊X⌋₊ : ℝ) := hih
    have hdisc_eq : discarded =
        (certMoves o).filter fun mv => (digitVal mv.1 : ℝ) * X < (2 : ℝ) ^ mv.2 * (o : ℝ) := by
      ext mv
      simp only [discarded, Finset.mem_filter, not_le]
    have hdisc_le :
        eps * (X / (o : ℝ)) ^ ((399 : ℝ) / 800) *
          ∑ mv ∈ discarded,
            ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
              (wCertNat (predOf o mv) : ℝ) ≤ 1 := by
      have hsum_le :
          eps * (X / (o : ℝ)) ^ ((399 : ℝ) / 800) *
            ∑ mv ∈ discarded,
              ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
                (wCertNat (predOf o mv) : ℝ) ≤
          (2 / 5 : ℝ) *
            ∑ mv ∈ discarded,
              ((X * (digitVal mv.1 : ℝ)) / ((o : ℝ) * (2 : ℝ) ^ mv.2)) ^ ((399 : ℝ) / 800) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum fun mv _ => ?_
        have hw_le : (wCertNat (predOf o mv) : ℝ) ≤ 65535 := by
          exact_mod_cast wCertNat_le (predOf o mv)
        have hcomb : (X / (o : ℝ)) ^ ((399 : ℝ) / 800) *
              ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) =
            ((X * (digitVal mv.1 : ℝ)) / ((o : ℝ) * (2 : ℝ) ^ mv.2)) ^ ((399 : ℝ) / 800) := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          congr 1; ring
        have heps_mul : eps * (wCertNat (predOf o mv) : ℝ) ≤ 2 / 5 := by
          unfold eps; linarith
        calc eps * (X / (o : ℝ)) ^ ((399 : ℝ) / 800) *
              (((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
                (wCertNat (predOf o mv) : ℝ))
            = (eps * (wCertNat (predOf o mv) : ℝ)) *
                ((X / (o : ℝ)) ^ ((399 : ℝ) / 800) *
                  ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800)) := by ring
          _ ≤ (2 / 5 : ℝ) *
                ((X / (o : ℝ)) ^ ((399 : ℝ) / 800) *
                  ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800)) :=
              mul_le_mul_of_nonneg_right heps_mul (by positivity)
          _ = (2 / 5 : ℝ) *
                ((X * (digitVal mv.1 : ℝ)) / ((o : ℝ) * (2 : ℝ) ^ mv.2)) ^ ((399 : ℝ) / 800) := by
              rw [hcomb]
      have hgeom := discarded_certMoves_sum_le ho hX
      rw [← hdisc_eq] at hgeom
      linarith
    have hsplit :
        ∑ mv ∈ certMoves o,
          ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
            (wCertNat (predOf o mv) : ℝ) =
        ∑ mv ∈ admitted,
          ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
            (wCertNat (predOf o mv) : ℝ) +
        ∑ mv ∈ discarded,
          ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
            (wCertNat (predOf o mv) : ℝ) :=
      (Finset.sum_filter_add_sum_filter_not (certMoves o) _ _).symm
    have hsub := certW_sub_eig ho
    have hN_cast : (1 : ℝ) + ∑ m ∈ S, (NTree m ⌊X⌋₊ : ℝ) ≤ (NTree o ⌊X⌋₊ : ℝ) := by
      exact_mod_cast hN_sum
    have hmul : eps * (wCertNat o : ℝ) * (X / (o : ℝ)) ^ ((399 : ℝ) / 800) ≤
        eps * (X / (o : ℝ)) ^ ((399 : ℝ) / 800) *
          ∑ mv ∈ certMoves o,
            ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ mv.2) ^ ((399 : ℝ) / 800) *
              (wCertNat (predOf o mv) : ℝ) := by
      have : eps * (wCertNat o : ℝ) * (X / (o : ℝ)) ^ ((399 : ℝ) / 800) =
          eps * (X / (o : ℝ)) ^ ((399 : ℝ) / 800) * (wCertNat o : ℝ) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hsub (by positivity)
    rw [hsplit, mul_add] at hmul
    linarith

/-! ## Section 5: Non-periodicity of `31` and Theorem 8 Part 1a (`thm:basin-sharp`) -/

private lemma cycle1_mem (j : ℕ) : f^[j] 1 = 1 ∨ f^[j] 1 = 2 := by
  induction j with
  | zero => exact Or.inl rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h <;> rw [h]
    · exact Or.inr (by decide)
    · exact Or.inl (by decide)

/-- `31` is non-periodic under `f = f_10`: its orbit enters the `1 ↔ 2` cycle at step `6`. -/
theorem nonperiodic_31 : NonPeriodic 31 := by
  intro k hk hcyc
  by_cases hlt : k < 6
  · interval_cases k <;> exact absurd hcyc (by decide)
  · have hge : 6 ≤ k := by omega
    have hstep : f^[k] 31 = f^[k - 6] 1 := by
      conv_lhs => rw [show k = (k - 6) + 6 by omega]
      rw [Function.iterate_add_apply, f_ex_31_reaches_1]
    rcases cycle1_mem (k - 6) with h1 | h2 <;> omega

private lemma rpow_31_le : (31 : ℝ) ^ ((399 : ℝ) / 800) ≤ 5568 / 1000 := by
  have h1 : (31 : ℝ) ^ ((399 : ℝ) / 800) ≤ (31 : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h2 : (31 : ℝ) ^ ((1 : ℝ) / 2) ≤ 5568 / 1000 := by
    have hsq : ((31 : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) ≤ (5568 / 1000 : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast ((31 : ℝ) ^ _) 2, ← Real.rpow_mul (by norm_num)]
      have : ((1 : ℝ) / 2) * (2 : ℕ) = 1 := by norm_num
      rw [this, Real.rpow_one]
      norm_num
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hsq
  exact h1.trans h2

/-- Theorem 8 (`thm:basin-sharp`, Part 1a, real cutoff): for every real `X ≥ 1`,
    `0.0806 * (X / 31)^(399/800) ≤ N1 ⌊X⌋₊` and `0.0145 * X^(399/800) ≤ N1 ⌊X⌋₊`. -/
theorem thm_basin1_sharp_lower_real (X : ℝ) (hX : 1 ≤ X) :
    (806 / 10000 : ℝ) * (X / 31) ^ ((399 : ℝ) / 800) ≤ (N1 ⌊X⌋₊ : ℝ) ∧
    (145 / 10000 : ℝ) * X ^ ((399 : ℝ) / 800) ≤ (N1 ⌊X⌋₊ : ℝ) := by
  by_cases hX31 : X < 31
  · have hfl1 : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by simpa using hX)
    have hN1_ge1 : (1 : ℝ) ≤ (N1 ⌊X⌋₊ : ℝ) := by
      have hcard : 1 ≤ N1 ⌊X⌋₊ := by
        classical
        unfold N1
        refine Finset.card_pos.mpr ⟨1, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨le_rfl, hfl1⟩, by decide, reaches_refl f 1⟩
      exact_mod_cast hcard
    have hdiv_le1 : (X / 31) ^ ((399 : ℝ) / 800) ≤ 1 := by
      have h1 : X / 31 ≤ 1 := by linarith
      calc (X / 31) ^ ((399 : ℝ) / 800)
          ≤ (1 : ℝ) ^ ((399 : ℝ) / 800) :=
            Real.rpow_le_rpow (by positivity) h1 (by norm_num)
        _ = 1 := Real.one_rpow _
    have hX_pow : X ^ ((399 : ℝ) / 800) ≤ 5568 / 1000 :=
      (Real.rpow_le_rpow (by positivity) hX31.le (by norm_num)).trans rpow_31_le
    exact ⟨by linarith, by linarith⟩
  · have hge31 : (31 : ℝ) ≤ X := not_lt.mp hX31
    have h31_abc : InABC15 31 := ⟨by omega, by decide, Or.inl (by decide)⟩
    have htree := lemma_basin1_lower_tree 31 X h31_abc hge31 nonperiodic_31
    rw [wCertNat_31] at htree
    have hsub : NTree 31 ⌊X⌋₊ ≤ N1 ⌊X⌋₊ := by
      classical
      unfold NTree N1
      refine Finset.card_le_card fun m hm => ?_
      simp only [Finset.mem_filter] at hm ⊢
      exact ⟨hm.1, hm.2.1, reaches_trans hm.2.2 ⟨6, f_ex_31_reaches_1⟩⟩
    have hN_ge : (2 / 5 : ℝ) * ((13484 : ℝ) / 65535) * (X / 31) ^ ((399 : ℝ) / 800) ≤
        (N1 ⌊X⌋₊ : ℝ) := by
      have hcast : (NTree 31 ⌊X⌋₊ : ℝ) ≤ (N1 ⌊X⌋₊ : ℝ) := by exact_mod_cast hsub
      have htree' : (2 / 5 : ℝ) * ((13484 : ℝ) / 65535) * (X / 31) ^ ((399 : ℝ) / 800) ≤
          (NTree 31 ⌊X⌋₊ : ℝ) := by simpa using htree
      exact htree'.trans hcast
    have hconst1 : (806 / 10000 : ℝ) ≤ (2 / 5 : ℝ) * ((13484 : ℝ) / 65535) := by norm_num
    have h1 : (806 / 10000 : ℝ) * (X / 31) ^ ((399 : ℝ) / 800) ≤ (N1 ⌊X⌋₊ : ℝ) :=
      (mul_le_mul_of_nonneg_right hconst1 (by positivity)).trans hN_ge
    have hsplit : X ^ ((399 : ℝ) / 800) =
        (31 : ℝ) ^ ((399 : ℝ) / 800) * (X / 31) ^ ((399 : ℝ) / 800) := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      congr 1; ring
    have hconst2 : (145 / 10000 : ℝ) * (31 : ℝ) ^ ((399 : ℝ) / 800) ≤
        (2 / 5 : ℝ) * ((13484 : ℝ) / 65535) := by
      have h31 := rpow_31_le
      linarith
    have h2 : (145 / 10000 : ℝ) * X ^ ((399 : ℝ) / 800) ≤ (N1 ⌊X⌋₊ : ℝ) := by
      rw [hsplit, ← mul_assoc]
      exact (mul_le_mul_of_nonneg_right hconst2 (by positivity)).trans hN_ge
    exact ⟨h1, h2⟩

/-- Theorem 8 (`thm:basin-sharp`, Part 1a, integer cutoff): for every integer `X ≥ 1`,
    `0.0806 * (X / 31)^(399/800) ≤ N1 X` and `0.0145 * X^(399/800) ≤ N1 X`. -/
theorem thm_basin1_sharp_lower (X : ℕ) (hX : 1 ≤ X) :
    (806 / 10000 : ℝ) * ((X : ℝ) / 31) ^ ((399 : ℝ) / 800) ≤ (N1 X : ℝ) ∧
    (145 / 10000 : ℝ) * (X : ℝ) ^ ((399 : ℝ) / 800) ≤ (N1 X : ℝ) := by
  have h := thm_basin1_sharp_lower_real (X : ℝ) (by exact_mod_cast hX)
  simpa [Nat.floor_natCast] using h

end Ouroboros
