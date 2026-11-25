module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import Ouroboros.EvenBasesCert
@[expose] public section

/-! # Section 2 (Even Bases): Markov drift classification -/

namespace Ouroboros
open EvenBasesCert

/-! ## Part 1: Multiples of 4 (`b = 4k`, `k ≥ 1`) -/
/-- Odd digit `2*i + 1 ∈ [1, 4k)` indexed by `i : Fin (2*k)`. -/
def digit4k {k : ℕ} (i : Fin (2 * k)) : ℕ := 2 * i.val + 1
lemma digit4k_pos {k : ℕ} (i : Fin (2 * k)) : 0 < digit4k i := by unfold digit4k; omega
lemma digit4k_lt {k : ℕ} (i : Fin (2 * k)) : digit4k i < 4 * k := by unfold digit4k; omega
lemma digit4k_odd {k : ℕ} (i : Fin (2 * k)) : digit4k i % 2 = 1 := by unfold digit4k; omega
/-- The two equiprobable next odd digits of `P_{4k}` from `i : Fin (2*k)`. -/
def next4kA (k : ℕ) (hk : 1 ≤ k) (i : Fin (2 * k)) : Fin (2 * k) :=
  let r := digit4k i; let c := ((r * r + 1) / 2) % (4 * k)
  ⟨c / 2, Nat.div_lt_of_lt_mul
    (Nat.lt_of_lt_of_eq (Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 3) (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)))
      (Nat.mul_assoc 2 2 k))⟩

def next4kB (k : ℕ) (hk : 1 ≤ k) (i : Fin (2 * k)) : Fin (2 * k) :=
  let r := digit4k i; let c := (((r * r + 1) / 2) + 2 * k) % (4 * k)
  ⟨c / 2, Nat.div_lt_of_lt_mul
    (Nat.lt_of_lt_of_eq (Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 3) (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)))
      (Nat.mul_assoc 2 2 k))⟩
private lemma sq_add_one_div_two_odd (r : ℕ) (hr : r % 2 = 1) : ((r * r + 1) / 2) % 2 = 1 := by
  have h : r = 2 * (r / 2) + 1 := by omega
  have h1 : (r * r + 1) / 2 = 2 * ((r / 2) * (r / 2) + r / 2) + 1 := by
    have : r * r + 1 = 2 * (2 * ((r / 2) * (r / 2) + r / 2) + 1) := by
      conv_lhs => rw [h]
      ring
    omega
  rw [h1]; omega
lemma digit4k_next4kA (k : ℕ) (hk : 1 ≤ k) (i : Fin (2 * k)) :
    digit4k (next4kA k hk i) = ((digit4k i * digit4k i + 1) / 2) % (4 * k) := by
  have hodd := sq_add_one_div_two_odd (digit4k i) (digit4k_odd i); have h2dvd : 2 ∣ 4 * k := ⟨2 * k, by ring⟩
  have hmod2 : (((digit4k i * digit4k i + 1) / 2) % (4 * k)) % 2 = 1 := by rw [Nat.mod_mod_of_dvd _ h2dvd]; exact hodd
  change 2 * ((((digit4k i * digit4k i + 1) / 2) % (4 * k)) / 2) + 1 =
    ((digit4k i * digit4k i + 1) / 2) % (4 * k)
  omega
lemma digit4k_next4kB (k : ℕ) (hk : 1 ≤ k) (i : Fin (2 * k)) :
    digit4k (next4kB k hk i) = (((digit4k i * digit4k i + 1) / 2) + 2 * k) % (4 * k) := by
  have hodd := sq_add_one_div_two_odd (digit4k i) (digit4k_odd i); have h2dvd : 2 ∣ 4 * k := ⟨2 * k, by ring⟩
  have hmod2 : ((((digit4k i * digit4k i + 1) / 2) + 2 * k) % (4 * k)) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ h2dvd]; omega
  change 2 * (((((digit4k i * digit4k i + 1) / 2) + 2 * k) % (4 * k)) / 2) + 1 =
    (((digit4k i * digit4k i + 1) / 2) + 2 * k) % (4 * k)
  omega
/-- Markov operator `P_{4k}` acting on functions `f : Fin (2*k) → ℝ`. -/
noncomputable def P4kOp (k : ℕ) (hk : 1 ≤ k) (f : Fin (2 * k) → ℝ) (i : Fin (2 * k)) : ℝ :=
  (1 / 2 : ℝ) * (f (next4kA k hk i) + f (next4kB k hk i))
/-- Stationarity of a probability law `π` on `Fin (2*k)` for `P_{4k}`. -/
def IsStationary4k (k : ℕ) (hk : 1 ≤ k) (π : Fin (2 * k) → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧ (∑ i : Fin (2 * k), π i = 1) ∧
  (∀ f : Fin (2 * k) → ℝ,
    ∑ i : Fin (2 * k), π i * P4kOp k hk f i = ∑ i : Fin (2 * k), π i * f i)
/-- Drift of a law `π` on `P_{4k}`: `E_π[ln D - ln 2]`. -/
noncomputable def drift4k {k : ℕ} (π : Fin (2 * k) → ℝ) : ℝ :=
  ∑ i : Fin (2 * k), π i * (Real.log (digit4k i : ℝ) - Real.log 2)
/-- The canonical stationary law on `{1, 2k+1}` (`i = 0` and `i = k`) in `P_{4k}`. -/
noncomputable def pi4kBase (k : ℕ) (_hk : 1 ≤ k) (i : Fin (2 * k)) : ℝ :=
  if i.val = 0 ∨ i.val = k then (1 / 2 : ℝ) else 0
lemma pi4kBase_stationary (k : ℕ) (hk : 1 ≤ k) : IsStationary4k k hk (pi4kBase k hk) := by
  let i0 : Fin (2 * k) := ⟨0, by omega⟩
  let ik : Fin (2 * k) := ⟨k, by omega⟩
  have hne : i0 ≠ ik := by intro h; have := congr_arg Fin.val h; dsimp [i0, ik] at this; omega
  have hA0 : next4kA k hk i0 = i0 := by
    apply Fin.ext; have h := digit4k_next4kA k hk i0; have hd0 : digit4k i0 = 1 := rfl; rw [hd0] at h
    have h1 : ((1 * 1 + 1) / 2) % (4 * k) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1] at h; change 2 * (next4kA k hk i0).val + 1 = 1 at h; change (next4kA k hk i0).val = 0; omega
  have hB0 : next4kB k hk i0 = ik := by
    apply Fin.ext; have h := digit4k_next4kB k hk i0; have hd0 : digit4k i0 = 1 := rfl; rw [hd0] at h
    have h1 : (((1 * 1 + 1) / 2) + 2 * k) % (4 * k) = 1 + 2 * k := Nat.mod_eq_of_lt (by omega)
    rw [h1] at h; change 2 * (next4kB k hk i0).val + 1 = 1 + 2 * k at h; change (next4kB k hk i0).val = k; omega
  have hAkBk : (next4kA k hk ik = i0 ∧ next4kB k hk ik = ik) ∨
      (next4kA k hk ik = ik ∧ next4kB k hk ik = i0) := by
    have hA := digit4k_next4kA k hk ik; have hB := digit4k_next4kB k hk ik
    have hsq : ((2 * k + 1) * (2 * k + 1) + 1) / 2 = 2 * k * (k + 1) + 1 := by
      have : (2 * k + 1) * (2 * k + 1) + 1 = 2 * (2 * k * (k + 1) + 1) := by ring
      omega
    have hdk : digit4k ik = 2 * k + 1 := rfl; rw [hdk, hsq] at hA hB
    by_cases hpar : k % 2 = 1
    · left
      have hdiv : 2 * k * (k + 1) = 4 * k * ((k + 1) / 2) := by
        have : 2 * ((k + 1) / 2) = k + 1 := by omega
        calc 2 * k * (k + 1) = 2 * k * (2 * ((k + 1) / 2)) := by rw [this]
          _ = 4 * k * ((k + 1) / 2) := by ring
      have h1 : (2 * k * (k + 1) + 1) % (4 * k) = 1 := by rw [hdiv, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      have h2 : (2 * k * (k + 1) + 1 + 2 * k) % (4 * k) = 2 * k + 1 := by
        rw [show 2 * k * (k + 1) + 1 + 2 * k = 4 * k * ((k + 1) / 2) + (2 * k + 1) by omega,
            Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      rw [h1] at hA; rw [h2] at hB
      change 2 * (next4kA k hk ik).val + 1 = 1 at hA; change 2 * (next4kB k hk ik).val + 1 = 2 * k + 1 at hB
      exact ⟨Fin.ext (show (next4kA k hk ik).val = 0 by omega),
             Fin.ext (show (next4kB k hk ik).val = k by omega)⟩
    · right
      have hdiv : 2 * k * (k + 1) = 4 * k * (k / 2) + 2 * k := by
        have : 2 * (k / 2) = k := by omega
        calc 2 * k * (k + 1) = 2 * k * (2 * (k / 2)) + 2 * k := by rw [this]; ring
          _ = 4 * k * (k / 2) + 2 * k := by ring
      have h1 : (2 * k * (k + 1) + 1) % (4 * k) = 2 * k + 1 := by
        rw [show 2 * k * (k + 1) + 1 = 4 * k * (k / 2) + (2 * k + 1) by omega,
            Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      have h2 : (2 * k * (k + 1) + 1 + 2 * k) % (4 * k) = 1 := by
        have hsum4 : 2 * k * (k + 1) + 1 + 2 * k = 4 * k * (k / 2 + 1) + 1 := by rw [hdiv]; ring
        rw [hsum4, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      rw [h1] at hA; rw [h2] at hB
      change 2 * (next4kA k hk ik).val + 1 = 2 * k + 1 at hA; change 2 * (next4kB k hk ik).val + 1 = 1 at hB
      exact ⟨Fin.ext (show (next4kA k hk ik).val = k by omega),
             Fin.ext (show (next4kB k hk ik).val = 0 by omega)⟩
  have hsum_pair : ∀ g : Fin (2 * k) → ℝ,
      ∑ i : Fin (2 * k), pi4kBase k hk i * g i = (1 / 2 : ℝ) * (g i0 + g ik) := by
    intro g
    have hsupp : ∀ i : Fin (2 * k), i ∉ ({i0, ik} : Finset (Fin (2 * k))) →
        pi4kBase k hk i * g i = 0 := by
      intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      have h1 : i.val ≠ 0 := fun h => hi.1 (Fin.ext h); have h2 : i.val ≠ k := fun h => hi.2 (Fin.ext h)
      simp [pi4kBase, h1, h2]
    rw [← Finset.sum_subset (Finset.subset_univ ({i0, ik} : Finset _)) (fun i _ hi => hsupp i hi)]
    rw [Finset.sum_pair hne]; simp only [pi4kBase, i0, ik, true_or, or_true, ↓reduceIte]; ring
  refine ⟨fun i => by unfold pi4kBase; split_ifs <;> norm_num, ?_, ?_⟩
  · have h := hsum_pair (fun _ => 1); simp only [mul_one] at h
    rw [h]; norm_num
  · intro f; rw [hsum_pair (P4kOp k hk f), hsum_pair f]; unfold P4kOp; rw [hA0, hB0]
    rcases hAkBk with ⟨hA, hB⟩ | ⟨hA, hB⟩ <;> (rw [hA, hB]; ring)
lemma pi4kBase_drift (k : ℕ) (hk : 1 ≤ k) : drift4k (pi4kBase k hk) = Real.log (Real.sqrt (2 * (k : ℝ) + 1) / 2) := by
  let i0 : Fin (2 * k) := ⟨0, by omega⟩
  let ik : Fin (2 * k) := ⟨k, by omega⟩
  have hne : i0 ≠ ik := by intro h; have := congr_arg Fin.val h; dsimp [i0, ik] at this; omega
  have hsupp : ∀ i : Fin (2 * k), i ∉ ({i0, ik} : Finset (Fin (2 * k))) →
      pi4kBase k hk i * (Real.log (digit4k i : ℝ) - Real.log 2) = 0 := by
    intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    have h1 : i.val ≠ 0 := fun h => hi.1 (Fin.ext h); have h2 : i.val ≠ k := fun h => hi.2 (Fin.ext h)
    simp [pi4kBase, h1, h2]
  unfold drift4k; rw [← Finset.sum_subset (Finset.subset_univ ({i0, ik} : Finset _)) (fun i _ hi => hsupp i hi)]
  rw [Finset.sum_pair hne]; simp only [pi4kBase, i0, ik, digit4k, true_or, or_true, ↓reduceIte]
  have hpos : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  rw [Real.log_div (Real.sqrt_pos.mpr hpos).ne' (by norm_num), Real.log_sqrt hpos.le]
  push_cast; simp only [Real.log_one]; ring
/-- Lemma (`lem:even-drift-bounds`, part 1a): every stationary law of `P_{4k}` has drift `≥ ln(√(2k+1) / 2)`. -/
theorem lem_even_drift_bounds_4k_all {k : ℕ} (hk : 1 ≤ k) {π : Fin (2 * k) → ℝ}
    (hstat : IsStationary4k k hk π) :
    Real.log (Real.sqrt (2 * (k : ℝ) + 1) / 2) ≤ drift4k π := by
  obtain ⟨hnn, hsum1, hinv⟩ := hstat
  have hdrift : drift4k π =
      ∑ i : Fin (2 * k), π i * (P4kOp k hk (fun j => Real.log (digit4k j : ℝ)) i - Real.log 2) := by
    unfold drift4k; have h1 := hinv (fun j => Real.log (digit4k j : ℝ))
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum1, one_mul] at h1 ⊢; linarith
  rw [hdrift]
  have hstep : ∀ i : Fin (2 * k),
      Real.log (Real.sqrt (2 * (k : ℝ) + 1) / 2) ≤
        P4kOp k hk (fun j => Real.log (digit4k j : ℝ)) i - Real.log 2 := by
    intro i; have hA := digit4k_next4kA k hk i; have hB := digit4k_next4kB k hk i; set a := digit4k (next4kA k hk i)
    set b := digit4k (next4kB k hk i); have ha_pos : 1 ≤ a := digit4k_pos _; have hb_pos : 1 ≤ b := digit4k_pos _
    have hdiff : b = a + 2 * k ∨ a = b + 2 * k := by
      have ha_lt : a < 4 * k := digit4k_lt _; have hc_mod : ((digit4k i * digit4k i + 1) / 2) % (4 * k) = a := hA.symm
      have hb_eq : b = (a + 2 * k) % (4 * k) := by
        rw [hB, Nat.add_mod, hc_mod, Nat.mod_eq_of_lt (by omega : 2 * k < 4 * k)]
      by_cases hlt : a + 2 * k < 4 * k
      · left; rw [hb_eq, Nat.mod_eq_of_lt hlt]
      · right; have hsub : a + 2 * k = (a - 2 * k) + 4 * k := by omega
        rw [hb_eq, hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
    have hprod : 2 * k + 1 ≤ a * b := by
      rcases hdiff with h | h <;> nlinarith
    have hprodR : (2 * (k : ℝ) + 1) ≤ (a : ℝ) * (b : ℝ) := by exact_mod_cast hprod
    have hpos : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
    have hlog : Real.log (2 * (k : ℝ) + 1) ≤ Real.log ((a : ℝ) * (b : ℝ)) := Real.log_le_log hpos hprodR
    rw [Real.log_mul (by positivity) (by positivity)] at hlog
    rw [Real.log_div (Real.sqrt_pos.mpr hpos).ne' (by norm_num), Real.log_sqrt hpos.le]
    unfold P4kOp; linarith
  calc Real.log (Real.sqrt (2 * (k : ℝ) + 1) / 2)
      = ∑ i : Fin (2 * k), π i * Real.log (Real.sqrt (2 * (k : ℝ) + 1) / 2) := by
        rw [← Finset.sum_mul, hsum1, one_mul]
    _ ≤ ∑ i : Fin (2 * k), π i * (P4kOp k hk (fun j => Real.log (digit4k j : ℝ)) i - Real.log 2) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hstep i) (hnn i)
/-- Lemma (`lem:even-drift-bounds`, part 1b): every stationary law of `P_{4k}` supported off `{1, 2k+1}` (i.e. -/
theorem lem_even_drift_bounds_4k_other {k : ℕ} (hk : 1 ≤ k) {π : Fin (2 * k) → ℝ}
    (hstat : IsStationary4k k hk π) (h0 : π ⟨0, by omega⟩ = 0) :
    Real.log (3 / 2 : ℝ) ≤ drift4k π ∧
    Real.log (Real.sqrt (2 * (k : ℝ) + 1) / 2) < drift4k π := by
  obtain ⟨hnn, hsum1, hinv⟩ := hstat
  let i0 : Fin (2 * k) := ⟨0, by omega⟩
  have hno0 : ∀ i : Fin (2 * k), 0 < π i → next4kA k hk i ≠ i0 ∧ next4kB k hk i ≠ i0 := by
    let ind0 : Fin (2 * k) → ℝ := fun j => if j = i0 then 1 else 0
    have hsum0 : ∑ j : Fin (2 * k), π j * P4kOp k hk ind0 j = 0 := by
      rw [hinv ind0]
      have : ∀ j : Fin (2 * k), π j * ind0 j = 0 := by
        intro j; unfold ind0; split_ifs with hj
        · rw [hj, h0, zero_mul]
        · rw [mul_zero]
      simp [this]
    have hterm_nn : ∀ j ∈ (Finset.univ : Finset (Fin (2 * k))),
        0 ≤ π j * P4kOp k hk ind0 j := by
      intro j _
      apply mul_nonneg (hnn j)
      unfold P4kOp ind0; split_ifs <;> norm_num
    have hall0 := (Finset.sum_eq_zero_iff_of_nonneg hterm_nn).mp hsum0; intro i hpi
    have hi0 := hall0 i (Finset.mem_univ i)
    have hop0 : P4kOp k hk ind0 i = 0 := (mul_eq_zero.mp hi0).resolve_left hpi.ne'; unfold P4kOp ind0 at hop0
    constructor
    · intro h; rw [h] at hop0; simp only [↓reduceIte] at hop0; split_ifs at hop0 <;> norm_num at hop0
    · intro h; rw [h] at hop0; simp only [↓reduceIte] at hop0; split_ifs at hop0 <;> norm_num at hop0
  have hdrift : drift4k π =
      ∑ i : Fin (2 * k), π i * (P4kOp k hk (fun j => Real.log (digit4k j : ℝ)) i - Real.log 2) := by
    unfold drift4k; have h1 := hinv (fun j => Real.log (digit4k j : ℝ))
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum1, one_mul] at h1 ⊢; linarith
  rw [hdrift]
  have hge3 : ∀ i : Fin (2 * k), 0 < π i →
      Real.log (3 / 2 : ℝ) ≤ P4kOp k hk (fun j => Real.log (digit4k j : ℝ)) i - Real.log 2 ∧
      Real.log (Real.sqrt (2 * (k : ℝ) + 1) / 2) <
        P4kOp k hk (fun j => Real.log (digit4k j : ℝ)) i - Real.log 2 := by
    intro i hpi; obtain ⟨hA_ne, hB_ne⟩ := hno0 i hpi; set a := digit4k (next4kA k hk i)
    set b := digit4k (next4kB k hk i)
    have ha3 : 3 ≤ a := by have hne : (next4kA k hk i).val ≠ 0 := fun h => hA_ne (Fin.ext h); unfold a digit4k; omega
    have hb3 : 3 ≤ b := by have hne : (next4kB k hk i).val ≠ 0 := fun h => hB_ne (Fin.ext h); unfold b digit4k; omega
    have hdiff : b = a + 2 * k ∨ a = b + 2 * k := by
      have hA := digit4k_next4kA k hk i; have hB := digit4k_next4kB k hk i; have ha_lt : a < 4 * k := digit4k_lt _
      have hb_eq : b = (a + 2 * k) % (4 * k) := by
        change digit4k (next4kB k hk i) = (a + 2 * k) % (4 * k)
        rw [hB, Nat.add_mod, ← hA, Nat.mod_eq_of_lt (by omega : 2 * k < 4 * k)]
      by_cases hlt : a + 2 * k < 4 * k
      · left; rw [hb_eq, Nat.mod_eq_of_lt hlt]
      · right; have hsub : a + 2 * k = (a - 2 * k) + 4 * k := by omega
        rw [hb_eq, hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
    have hprod_gt : 2 * k + 1 < a * b := by rcases hdiff with h | h <;> nlinarith
    have hpos : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
    constructor
    · have hlogA : Real.log 3 ≤ Real.log (a : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast ha3)
      have hlogB : Real.log 3 ≤ Real.log (b : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hb3)
      rw [Real.log_div (by norm_num) (by norm_num)]
      unfold P4kOp; linarith
    · have hlog : Real.log (2 * (k : ℝ) + 1) < Real.log ((a : ℝ) * (b : ℝ)) :=
        Real.log_lt_log hpos (by exact_mod_cast hprod_gt)
      rw [Real.log_mul (by positivity) (by positivity)] at hlog
      rw [Real.log_div (Real.sqrt_pos.mpr hpos).ne' (by norm_num), Real.log_sqrt hpos.le]
      unfold P4kOp; linarith
  have hex_pos : ∃ i : Fin (2 * k), 0 < π i := by
    by_contra hall
    push Not at hall
    have : ∑ i : Fin (2 * k), π i ≤ 0 := Finset.sum_nonpos fun i _ => hall i
    linarith
  constructor
  · calc Real.log (3 / 2 : ℝ)
        = ∑ i : Fin (2 * k), π i * Real.log (3 / 2 : ℝ) := by rw [← Finset.sum_mul, hsum1, one_mul]
      _ ≤ ∑ i : Fin (2 * k), π i * (P4kOp k hk (fun j => Real.log (digit4k j : ℝ)) i - Real.log 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rcases eq_or_lt_of_le (hnn i) with h | h
          · rw [← h, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left (hge3 i h).1 h.le
  · calc Real.log (Real.sqrt (2 * (k : ℝ) + 1) / 2)
        = ∑ i : Fin (2 * k), π i * Real.log (Real.sqrt (2 * (k : ℝ) + 1) / 2) := by
          rw [← Finset.sum_mul, hsum1, one_mul]
      _ < ∑ i : Fin (2 * k), π i * (P4kOp k hk (fun j => Real.log (digit4k j : ℝ)) i - Real.log 2) := by
          refine Finset.sum_lt_sum ?_ ?_
          · intro i _
            rcases eq_or_lt_of_le (hnn i) with h | h
            · rw [← h, zero_mul, zero_mul]
            · exact mul_le_mul_of_nonneg_left (hge3 i h).2.le h.le
          · obtain ⟨i, hpi⟩ := hex_pos; exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (hge3 i hpi).2 hpi⟩

theorem lem_even_drift_bounds_4k_nonpos {k : ℕ} (hk : 1 ≤ k) :
    (∃ π, IsStationary4k k hk π ∧ drift4k π ≤ 0) ↔ k = 1 := by
  constructor
  · rintro ⟨π, hstat, hle⟩; have hlb := lem_even_drift_bounds_4k_all hk hstat
    have hlog_le : Real.log (Real.sqrt (2 * (k : ℝ) + 1) / 2) ≤ 0 := hlb.trans hle
    have hpos : (0 : ℝ) < Real.sqrt (2 * (k : ℝ) + 1) / 2 := by positivity
    have hle1 : Real.sqrt (2 * (k : ℝ) + 1) / 2 ≤ 1 := by
      by_contra hgt; push Not at hgt
      have := Real.log_pos hgt; linarith
    have hsq : 2 * (k : ℝ) + 1 ≤ 4 := by
      have h1 : Real.sqrt (2 * (k : ℝ) + 1) ≤ 2 := by linarith
      have h2 := mul_self_le_mul_self (Real.sqrt_nonneg _) h1; rw [Real.mul_self_sqrt (by positivity)] at h2
      linarith
    have hnat : 2 * k + 1 ≤ 4 := by exact_mod_cast hsq
    omega
  · rintro rfl
    refine ⟨pi4kBase 1 (by omega), pi4kBase_stationary 1 (by omega), ?_⟩
    rw [pi4kBase_drift 1 (by omega)]
    apply Real.log_nonpos (by positivity)
    have h1 : Real.sqrt (2 * ((1 : ℕ) : ℝ) + 1) ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
      exact Real.sqrt_le_sqrt (by norm_num)
    exact (div_le_one (by norm_num)).mpr h1

/-! ## Part 2: Singly even bases (`b = 2M`, `M ≥ 1` odd) -/
/-- Unique odd digit in `[1, 2M)` congruent to `y (mod M)` for odd `M`. -/
def oddDigit2M (M : ℕ) (y : Fin M) : ℕ := oddDigitNat M y.val
lemma oddDigit2M_pos {M : ℕ} (hM : 1 ≤ M) (y : Fin M) : 1 ≤ oddDigit2M M y := by
  unfold oddDigit2M oddDigitNat
  cases h : Nat.beq (y.val % 2) 1 <;> dsimp only
  · omega
  · have := Nat.eq_of_beq_eq_true h; omega
lemma oddDigit2M_odd {M : ℕ} (hodd : M % 2 = 1) (y : Fin M) : oddDigit2M M y % 2 = 1 := by
  unfold oddDigit2M oddDigitNat
  cases h : Nat.beq (y.val % 2) 1 <;> dsimp only
  · have hne : y.val % 2 ≠ 1 := by intro heq; rw [heq] at h; simp at h
    omega
  · exact Nat.eq_of_beq_eq_true h
lemma oddDigit2M_ge_val {M : ℕ} (y : Fin M) : y.val ≤ oddDigit2M M y := by
  unfold oddDigit2M oddDigitNat
  cases Nat.beq (y.val % 2) 1 <;> dsimp only <;> omega
lemma oddDigit2M_of_even {M : ℕ} {y : Fin M} (hev : y.val % 2 = 0) : oddDigit2M M y = y.val + M := by
  unfold oddDigit2M oddDigitNat; simp [hev]
lemma oddDigit2M_lt {M : ℕ} (y : Fin M) : oddDigit2M M y < 2 * M := by
  unfold oddDigit2M oddDigitNat
  cases Nat.beq (y.val % 2) 1 <;> dsimp only <;> omega
/-- `H`: halving modulo odd `M`, i.e., multiplication by `(M + 1) / 2`. -/
def hStep2M (M : ℕ) (hM : 1 ≤ M) (y : Fin M) : Fin M :=
  ⟨hStepNat M y.val, Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)⟩
/-- `Q`: odd-step transition `y ↦ ((d(y)^2 + 1) / 2) mod M`. -/
def qStep2M (M : ℕ) (hM : 1 ≤ M) (y : Fin M) : Fin M :=
  ⟨qStepNat M y.val, Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)⟩
/-- Marginal 2-choice operator `K_M = (1/2)(H + Q)` on `Fin M`. -/
noncomputable def K2MOp (M : ℕ) (hM : 1 ≤ M) (f : Fin M → ℝ) (y : Fin M) : ℝ :=
  (1 / 2 : ℝ) * (f (hStep2M M hM y) + f (qStep2M M hM y))
/-- Full odd-to-odd Markov operator `P_{2M} = ∑_{v ≥ 1} 2^{-v} Q H^{v-1}` on `Fin M`. -/
noncomputable def P2MOp (M : ℕ) (hM : 1 ≤ M) (f : Fin M → ℝ) (y : Fin M) : ℝ :=
  ∑' v : ℕ, (2 : ℝ) ^ (-(v + 1 : ℤ)) * f ((hStep2M M hM)^[v] (qStep2M M hM y))
/-- Stationarity for `P_{2M}`. -/
def IsStationary2M (M : ℕ) (hM : 1 ≤ M) (π : Fin M → ℝ) : Prop :=
  (∀ y, 0 ≤ π y) ∧ (∑ y : Fin M, π y = 1) ∧
  (∀ f : Fin M → ℝ, ∑ y : Fin M, π y * P2MOp M hM f y = ∑ y : Fin M, π y * f y)
/-- Stationarity for `K_M = (1/2)(H + Q)`. -/
def IsStationaryKM (M : ℕ) (hM : 1 ≤ M) (π : Fin M → ℝ) : Prop :=
  (∀ y, 0 ≤ π y) ∧ (∑ y : Fin M, π y = 1) ∧
  (∀ f : Fin M → ℝ, ∑ y : Fin M, π y * K2MOp M hM f y = ∑ y : Fin M, π y * f y)
/-- Drift of a law `π` on `P_{2M}`: `E_π[ln D - 2 ln 2]`. -/
noncomputable def drift2M (M : ℕ) (π : Fin M → ℝ) : ℝ :=
  ∑ y : Fin M, π y * (Real.log (oddDigit2M M y : ℝ) - 2 * Real.log 2)
private lemma two_zpow_neg_succ (v : ℕ) : (2 : ℝ) ^ (-(v + 1 : ℤ)) = (1 / 2 : ℝ) ^ (v + 1) := by
  rw [show -(v + 1 : ℤ) = -((v + 1 : ℕ) : ℤ) by push_cast; rfl, zpow_neg, zpow_natCast,
      one_div, inv_pow]
private lemma two_zpow_neg_ge2 (v : ℕ) : (2 : ℝ) ^ (-((v + 2 : ℕ) : ℤ)) = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ v := by
  rw [zpow_neg, zpow_natCast, pow_add, mul_inv, ← inv_pow, ← one_div]
  norm_num; ring
private lemma summable_P2M_term (M : ℕ) (hM : 1 ≤ M) (f : Fin M → ℝ) (y : Fin M) :
    Summable fun v : ℕ => (2 : ℝ) ^ (-(v + 1 : ℤ)) * f ((hStep2M M hM)^[v] (qStep2M M hM y)) := by
  let B : ℝ := ∑ w : Fin M, |f w|
  have hB : ∀ w : Fin M, |f w| ≤ B := fun w =>
    Finset.single_le_sum (f := fun u => |f u|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)
  refine Summable.of_norm_bounded (g := fun v : ℕ => B * (1 / 2 : ℝ) ^ (v + 1)) ?_ ?_
  · exact (summable_geometric_two.comp_injective Nat.succ_injective).mul_left B
  · intro v; rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity), two_zpow_neg_succ, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB _) (by positivity)
private lemma P2MOp_sub_half_H (M : ℕ) (hM : 1 ≤ M) (f : Fin M → ℝ) (y : Fin M) :
    P2MOp M hM f y - (1 / 2 : ℝ) * P2MOp M hM (fun w => f (hStep2M M hM w)) y =
      (1 / 2 : ℝ) * f (qStep2M M hM y) := by
  unfold P2MOp; rw [(summable_P2M_term M hM f y).tsum_eq_zero_add]; simp only [Function.iterate_zero, id_eq]
  have h0 : (2 : ℝ) ^ (-((0 : ℕ) + 1 : ℤ)) = (1 / 2 : ℝ) := by norm_num
  rw [h0]
  have hshift : ∑' v : ℕ, (2 : ℝ) ^ (-((v + 1 : ℕ) + 1 : ℤ)) *
        f ((hStep2M M hM)^[v + 1] (qStep2M M hM y)) =
      (1 / 2 : ℝ) * ∑' v : ℕ, (2 : ℝ) ^ (-(v + 1 : ℤ)) *
        f (hStep2M M hM ((hStep2M M hM)^[v] (qStep2M M hM y))) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun v => ?_
    rw [Function.iterate_succ_apply']
    have hp : (2 : ℝ) ^ (-((v + 1 : ℕ) + 1 : ℤ)) = (1 / 2 : ℝ) * (2 : ℝ) ^ (-(v + 1 : ℤ)) := by
      have h1 : -((v + 1 : ℕ) + 1 : ℤ) = -(1 : ℤ) + (-(v + 1 : ℤ)) := by omega
      rw [h1, zpow_add₀ (by norm_num)]
      norm_num
    rw [hp, mul_assoc]
  rw [hshift]; ring
/-- Exact stationary-law equivalence (`lem:even-coding`(3)): `π P_{2M} = π ↔ π K_M = π` for `K_M = (1/2)(H + Q)`. -/
theorem stationary_P2M_iff_stationary_KM (M : ℕ) (hM : 1 ≤ M) (π : Fin M → ℝ) :
    IsStationary2M M hM π ↔ IsStationaryKM M hM π := by
  constructor
  · rintro ⟨hnn, hsum1, hinv⟩
    refine ⟨hnn, hsum1, fun f => ?_⟩
    have hP1 := hinv f; have hP2 := hinv (fun w => f (hStep2M M hM w))
    have hcomb : ∑ y : Fin M, π y * ((1 / 2 : ℝ) * f (qStep2M M hM y)) =
        ∑ y : Fin M, π y * f y - (1 / 2 : ℝ) * ∑ y : Fin M, π y * f (hStep2M M hM y) := by
      have hsub : ∀ y : Fin M, π y * ((1 / 2 : ℝ) * f (qStep2M M hM y)) =
          π y * P2MOp M hM f y - (1 / 2 : ℝ) * (π y * P2MOp M hM (fun w => f (hStep2M M hM w)) y) := by
        intro y; rw [← P2MOp_sub_half_H M hM f y]; ring
      simp_rw [hsub]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hP1, hP2]
    have hK : ∑ y : Fin M, π y * K2MOp M hM f y =
        (1 / 2 : ℝ) * ∑ y : Fin M, π y * f (hStep2M M hM y) +
        ∑ y : Fin M, π y * ((1 / 2 : ℝ) * f (qStep2M M hM y)) := by
      unfold K2MOp; rw [Finset.mul_sum, ← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun y _ => by ring
    linarith
  · rintro ⟨hnn, hsum1, hinv⟩
    refine ⟨hnn, hsum1, fun f => ?_⟩
    have hQ : ∀ g : Fin M → ℝ,
        (1 / 2 : ℝ) * ∑ y : Fin M, π y * g (qStep2M M hM y) =
          ∑ y : Fin M, π y * g y - (1 / 2 : ℝ) * ∑ y : Fin M, π y * g (hStep2M M hM y) := by
      intro g; have hk := hinv g
      have hK : ∑ y : Fin M, π y * K2MOp M hM g y =
          (1 / 2 : ℝ) * ∑ y : Fin M, π y * g (hStep2M M hM y) +
          (1 / 2 : ℝ) * ∑ y : Fin M, π y * g (qStep2M M hM y) := by
        unfold K2MOp; rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun y _ => by ring
      linarith
    have hteles : ∀ N : ℕ,
        ∑ v ∈ Finset.range N, (2 : ℝ) ^ (-(v + 1 : ℤ)) *
            (∑ y : Fin M, π y * f ((hStep2M M hM)^[v] (qStep2M M hM y))) =
          ∑ y : Fin M, π y * f y -
            (1 / 2 : ℝ) ^ N * (∑ y : Fin M, π y * f ((hStep2M M hM)^[N] y)) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, ih]; have hstep := hQ (fun w => f ((hStep2M M hM)^[N] w))
        have hpow : (2 : ℝ) ^ (-(N + 1 : ℤ)) = (1 / 2 : ℝ) ^ N * (1 / 2 : ℝ) := by rw [two_zpow_neg_succ, pow_succ]
        rw [hpow, mul_assoc, hstep]
        have hiter : ∀ y : Fin M,
            f ((hStep2M M hM)^[N] (hStep2M M hM y)) = f ((hStep2M M hM)^[N + 1] y) := by
          intro y; rw [Function.iterate_succ_apply]
        simp_rw [hiter]
        rw [pow_succ]; ring
    have htend_lhs : Filter.Tendsto
        (fun N : ℕ => ∑ v ∈ Finset.range N, (2 : ℝ) ^ (-(v + 1 : ℤ)) *
            (∑ y : Fin M, π y * f ((hStep2M M hM)^[v] (qStep2M M hM y))))
        Filter.atTop (nhds (∑ y : Fin M, π y * P2MOp M hM f y)) := by
      have hterm_eq' : ∀ N : ℕ,
          ∑ v ∈ Finset.range N, (2 : ℝ) ^ (-(v + 1 : ℤ)) *
              (∑ y : Fin M, π y * f ((hStep2M M hM)^[v] (qStep2M M hM y))) =
            ∑ y : Fin M, π y * ∑ v ∈ Finset.range N,
              (2 : ℝ) ^ (-(v + 1 : ℤ)) * f ((hStep2M M hM)^[v] (qStep2M M hM y)) := by
        intro N
        calc ∑ v ∈ Finset.range N, (2 : ℝ) ^ (-(v + 1 : ℤ)) *
              (∑ y : Fin M, π y * f ((hStep2M M hM)^[v] (qStep2M M hM y)))
            = ∑ v ∈ Finset.range N, ∑ y : Fin M,
                π y * ((2 : ℝ) ^ (-(v + 1 : ℤ)) * f ((hStep2M M hM)^[v] (qStep2M M hM y))) := by
              refine Finset.sum_congr rfl fun v _ => ?_
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun y _ => by ring
          _ = ∑ y : Fin M, ∑ v ∈ Finset.range N,
                π y * ((2 : ℝ) ^ (-(v + 1 : ℤ)) * f ((hStep2M M hM)^[v] (qStep2M M hM y))) :=
              Finset.sum_comm
          _ = ∑ y : Fin M, π y * ∑ v ∈ Finset.range N,
                (2 : ℝ) ^ (-(v + 1 : ℤ)) * f ((hStep2M M hM)^[v] (qStep2M M hM y)) := by
              refine Finset.sum_congr rfl fun y _ => (Finset.mul_sum _ _ _).symm
      simp_rw [hterm_eq']
      refine tendsto_finsetSum Finset.univ fun y _ => ?_
      exact ((summable_P2M_term M hM f y).hasSum.tendsto_sum_nat).const_mul (π y)
    have htend_rhs : Filter.Tendsto
        (fun N : ℕ => ∑ y : Fin M, π y * f y -
            (1 / 2 : ℝ) ^ N * (∑ y : Fin M, π y * f ((hStep2M M hM)^[N] y)))
        Filter.atTop (nhds (∑ y : Fin M, π y * f y)) := by
      let B : ℝ := ∑ w : Fin M, |f w|
      have hbound : ∀ N : ℕ,
          |(1 / 2 : ℝ) ^ N * (∑ y : Fin M, π y * f ((hStep2M M hM)^[N] y))| ≤
            B * (1 / 2 : ℝ) ^ N := by
        intro N; rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ N), mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc |∑ y : Fin M, π y * f ((hStep2M M hM)^[N] y)|
            ≤ ∑ y : Fin M, |π y * f ((hStep2M M hM)^[N] y)| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ y : Fin M, π y * |f ((hStep2M M hM)^[N] y)| := by
              refine Finset.sum_congr rfl fun y _ => by rw [abs_mul, abs_of_nonneg (hnn y)]
          _ ≤ ∑ y : Fin M, π y * B := by
              refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (hnn y)
              exact Finset.single_le_sum (f := fun u => |f u|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
          _ = B := by rw [← Finset.sum_mul, hsum1, one_mul]
      have hzero : Filter.Tendsto
          (fun N : ℕ => (1 / 2 : ℝ) ^ N * (∑ y : Fin M, π y * f ((hStep2M M hM)^[N] y)))
          Filter.atTop (nhds 0) := by
        refine squeeze_zero_norm (fun N => by simpa [Real.norm_eq_abs] using hbound N) ?_
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul B
      simpa using tendsto_const_nhds.sub hzero
    have heq_fn : (fun N : ℕ => ∑ v ∈ Finset.range N, (2 : ℝ) ^ (-(v + 1 : ℤ)) *
            (∑ y : Fin M, π y * f ((hStep2M M hM)^[v] (qStep2M M hM y)))) =
        (fun N : ℕ => ∑ y : Fin M, π y * f y -
            (1 / 2 : ℝ) ^ N * (∑ y : Fin M, π y * f ((hStep2M M hM)^[N] y))) :=
      funext hteles
    rw [heq_fn] at htend_lhs; exact tendsto_nhds_unique htend_lhs htend_rhs
private lemma tsum_two_neg_succ : ∑' v : ℕ, (2 : ℝ) ^ (-(v + 1 : ℤ)) = 1 := by
  have h : (fun v : ℕ => (2 : ℝ) ^ (-(v + 1 : ℤ))) = fun v : ℕ => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ v := by
    ext v; rw [two_zpow_neg_succ, pow_succ']
  rw [h, tsum_mul_left, tsum_geometric_two]; norm_num
private lemma tsum_two_neg_ge2 : ∑' v : ℕ, (2 : ℝ) ^ (-((v + 2 : ℕ) : ℤ)) = 1 / 2 := by
  have h : (fun v : ℕ => (2 : ℝ) ^ (-((v + 2 : ℕ) : ℤ))) =
      fun v : ℕ => (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ v := funext two_zpow_neg_ge2
  rw [h, tsum_mul_left, tsum_geometric_two]; norm_num
private lemma tsum_succ_mul_two_neg_ge2 : ∑' v : ℕ, ((v + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((v + 2 : ℕ) : ℤ)) = 1 := by
  have hgeom : HasSum (fun v : ℕ => ((v + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ v) 4 := by
    have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
    have h2 := hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    have h3 := h1.add h2
    have heq : (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ n) =
        fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n := by
      ext n; push_cast; ring
    rw [heq] at h3
    convert h3 using 1
    norm_num
  have hterm : (fun v : ℕ => ((v + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((v + 2 : ℕ) : ℤ))) =
      fun v : ℕ => (1 / 4 : ℝ) * (((v + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ v) := by
    ext v; rw [two_zpow_neg_ge2]; ring
  rw [hterm, tsum_mul_left, hgeom.tsum_eq]; norm_num
private lemma two_mul_hStep_mod {M : ℕ} (hM : 1 ≤ M) (hodd : M % 2 = 1) (y : Fin M) :
    (2 * (hStep2M M hM y).val) % M = y.val := by
  unfold hStep2M hStepNat; dsimp only; have h2inv : 2 * ((M + 1) / 2) = M + 1 := by omega
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  have hmul : 2 * (y.val * ((M + 1) / 2)) = y.val * (M + 1) := by
    calc 2 * (y.val * ((M + 1) / 2)) = y.val * (2 * ((M + 1) / 2)) := by ring
      _ = y.val * (M + 1) := by rw [h2inv]
  rw [hmul, mul_add, mul_one, mul_comm y.val M, Nat.mul_add_mod, Nat.mod_eq_of_lt y.isLt]
private lemma two_pow_mul_hStep_iter_mod {M : ℕ} (hM : 1 ≤ M) (hodd : M % 2 = 1)
    (v : ℕ) (y : Fin M) :
    (2 ^ v * ((hStep2M M hM)^[v] y).val) % M = y.val := by
  induction v with
  | zero => simp [Nat.mod_eq_of_lt y.isLt]
  | succ v ih =>
    rw [Function.iterate_succ_apply', pow_succ, mul_assoc, Nat.mul_mod,
        two_mul_hStep_mod hM hodd]
    have h1 : (2 ^ v % M * ((hStep2M M hM)^[v] y).val) % M =
        (2 ^ v * ((hStep2M M hM)^[v] y).val) % M := by
      simp [Nat.mul_mod]
    rw [h1, ih]
/-- Lemma (`lem:even-drift-bounds`, part 2a): for every odd `M ≥ 1` and every `y : Fin M`, -/
theorem lem_even_drift_bounds_2M_step {M : ℕ} (hM : 1 ≤ M) (hodd : M % 2 = 1) (y : Fin M) :
    (1 / 2 : ℝ) * Real.log ((M : ℝ) + 1) - Real.log 2 ≤
      P2MOp M hM (fun w => Real.log (oddDigit2M M w : ℝ)) y := by
  set y1 : Fin M := qStep2M M hM y
  by_cases hz : y1.val = 0
  ·
    have hiter0 : ∀ v : ℕ, ((hStep2M M hM)^[v] y1).val = 0 := by
      intro v
      induction v with
      | zero => exact hz
      | succ v ih =>
        rw [Function.iterate_succ_apply']; change ((hStep2M M hM)^[v] y1).val * ((M + 1) / 2) % M = 0
        rw [ih]; simp
    have hdM : ∀ v : ℕ, oddDigit2M M ((hStep2M M hM)^[v] y1) = M := by
      intro v; rw [oddDigit2M_of_even (by rw [hiter0 v]), hiter0 v, zero_add]
    unfold P2MOp
    simp_rw [show qStep2M M hM y = y1 from rfl, hdM]
    rw [tsum_mul_right, tsum_two_neg_succ, one_mul]
    have h4M2 : (M : ℝ) + 1 ≤ 4 * (M : ℝ) ^ 2 := by
      have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      nlinarith
    have hlog : Real.log ((M : ℝ) + 1) ≤ Real.log (4 * (M : ℝ) ^ 2) := Real.log_le_log (by positivity) h4M2
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hlog
    push_cast at hlog; linarith
  · by_cases hy1_odd : y1.val % 2 = 1
    ·
      unfold P2MOp; rw [(summable_P2M_term M hM (fun w => Real.log (oddDigit2M M w : ℝ)) y).tsum_eq_zero_add]
      simp only [Function.iterate_zero, id_eq]
      have h0_nn : 0 ≤ (2 : ℝ) ^ (-(0 + 1 : ℤ)) * Real.log (oddDigit2M M (qStep2M M hM y) : ℝ) := by
        apply mul_nonneg (by positivity)
        exact Real.log_nonneg (by exact_mod_cast oddDigit2M_pos hM _)
      have hterm_ge : ∀ v : ℕ,
          (2 : ℝ) ^ (-((v + 2 : ℕ) : ℤ)) *
            (Real.log ((M : ℝ) + 1) - ((v + 1 : ℕ) : ℝ) * Real.log 2) ≤
          (2 : ℝ) ^ (-((v + 1 : ℕ) + 1 : ℤ)) *
            Real.log (oddDigit2M M ((hStep2M M hM)^[v + 1] (qStep2M M hM y)) : ℝ) := by
        intro v; have hmod := two_pow_mul_hStep_iter_mod hM hodd (v + 1) y1; set yv := ((hStep2M M hM)^[v + 1] y1).val
        have h2yv_even : (2 ^ (v + 1) * yv) % 2 = 0 := by rw [pow_succ', mul_assoc]; omega
        have hdiv := Nat.div_add_mod (2 ^ (v + 1) * yv) M; rw [hmod] at hdiv
        have hq1 : 1 ≤ (2 ^ (v + 1) * yv) / M := by
          by_contra hq0
          have : (2 ^ (v + 1) * yv) / M = 0 := Nat.eq_zero_of_not_pos hq0
          rw [this, mul_zero, zero_add] at hdiv; omega
        have hge : M + 1 ≤ 2 ^ (v + 1) * yv := by
          have : M * 1 ≤ M * ((2 ^ (v + 1) * yv) / M) := Nat.mul_le_mul_left M hq1
          have hy1_1 : 1 ≤ y1.val := by omega
          omega
        have hdv_ge : M + 1 ≤ 2 ^ (v + 1) * oddDigit2M M ((hStep2M M hM)^[v + 1] y1) :=
          hge.trans (Nat.mul_le_mul_left _ (oddDigit2M_ge_val _))
        have hdv_pos : 0 < (oddDigit2M M ((hStep2M M hM)^[v + 1] y1) : ℝ) := by
          have := oddDigit2M_pos hM ((hStep2M M hM)^[v + 1] y1)
          positivity
        have hlog : Real.log ((M : ℝ) + 1) ≤
            Real.log ((2 : ℝ) ^ (v + 1) * (oddDigit2M M ((hStep2M M hM)^[v + 1] y1) : ℝ)) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hdv_ge)
        rw [Real.log_mul (by positivity) hdv_pos.ne', Real.log_pow] at hlog
        have hsub : Real.log ((M : ℝ) + 1) - ((v + 1 : ℕ) : ℝ) * Real.log 2 ≤
            Real.log (oddDigit2M M ((hStep2M M hM)^[v + 1] y1) : ℝ) := by linarith
        have hexp : (-((v + 1 : ℕ) + 1 : ℤ)) = -((v + 2 : ℕ) : ℤ) := by omega
        rw [hexp]; exact mul_le_mul_of_nonneg_left hsub (by positivity)
      have hs1 : Summable fun v : ℕ => (2 : ℝ) ^ (-((v + 2 : ℕ) : ℤ)) * Real.log ((M : ℝ) + 1) := by
        simp_rw [two_zpow_neg_ge2]
        exact (summable_geometric_two.mul_left (1 / 4)).mul_right _
      have hs2 : Summable fun v : ℕ =>
          (2 : ℝ) ^ (-((v + 2 : ℕ) : ℤ)) * (((v + 1 : ℕ) : ℝ) * Real.log 2) := by
        have h : (fun v : ℕ => (2 : ℝ) ^ (-((v + 2 : ℕ) : ℤ)) * (((v + 1 : ℕ) : ℝ) * Real.log 2)) =
            fun v : ℕ => ((1 / 4 : ℝ) * Real.log 2) * (((v + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ v) := by
          ext v; rw [two_zpow_neg_ge2]; ring
        rw [h]
        have hbase : Summable fun v : ℕ => ((v + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ v := by
          have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).summable
          have h2 := summable_geometric_two
          convert h1.add h2 using 1; ext n; push_cast; ring
        exact hbase.mul_left _
      have hs_lhs : Summable fun v : ℕ =>
          (2 : ℝ) ^ (-((v + 2 : ℕ) : ℤ)) *
            (Real.log ((M : ℝ) + 1) - ((v + 1 : ℕ) : ℝ) * Real.log 2) := by
        simpa [mul_sub] using hs1.sub hs2
      have hs_rhs : Summable fun v : ℕ =>
          (2 : ℝ) ^ (-((v + 1 : ℕ) + 1 : ℤ)) *
            Real.log (oddDigit2M M ((hStep2M M hM)^[v + 1] (qStep2M M hM y)) : ℝ) :=
        (summable_P2M_term M hM (fun w => Real.log (oddDigit2M M w : ℝ)) y).comp_injective
          Nat.succ_injective
      have htsum := Summable.tsum_le_tsum hterm_ge hs_lhs hs_rhs
      have hlhs_eval : ∑' v : ℕ, (2 : ℝ) ^ (-((v + 2 : ℕ) : ℤ)) *
            (Real.log ((M : ℝ) + 1) - ((v + 1 : ℕ) : ℝ) * Real.log 2) =
          (1 / 2 : ℝ) * Real.log ((M : ℝ) + 1) - Real.log 2 := by
        simp_rw [mul_sub]
        rw [hs1.tsum_sub hs2, tsum_mul_right, tsum_two_neg_ge2]
        have h2eq : ∑' v : ℕ, (2 : ℝ) ^ (-((v + 2 : ℕ) : ℤ)) * (((v + 1 : ℕ) : ℝ) * Real.log 2) =
            (∑' v : ℕ, ((v + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((v + 2 : ℕ) : ℤ))) * Real.log 2 := by
          rw [← tsum_mul_right]; refine tsum_congr fun v => by ring
        rw [h2eq, tsum_succ_mul_two_neg_ge2, one_mul]
      have h0_nn : 0 ≤ (2 : ℝ) ^ (-((0 : ℕ) + 1 : ℤ)) *
          Real.log (oddDigit2M M (qStep2M M hM y) : ℝ) :=
        mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast oddDigit2M_pos hM _))
      rw [hlhs_eval] at htsum
      calc (1 / 2 : ℝ) * Real.log ((M : ℝ) + 1) - Real.log 2
          ≤ ∑' v : ℕ, (2 : ℝ) ^ (-((v + 1 : ℕ) + 1 : ℤ)) *
              Real.log (oddDigit2M M ((hStep2M M hM)^[v + 1] (qStep2M M hM y)) : ℝ) := htsum
        _ ≤ (2 : ℝ) ^ (-((0 : ℕ) + 1 : ℤ)) * Real.log (oddDigit2M M (qStep2M M hM y) : ℝ) +
              ∑' v : ℕ, (2 : ℝ) ^ (-((v + 1 : ℕ) + 1 : ℤ)) *
                Real.log (oddDigit2M M ((hStep2M M hM)^[v + 1] (qStep2M M hM y)) : ℝ) :=
            le_add_of_nonneg_left h0_nn
    ·
      have hy1_ev : y1.val % 2 = 0 := by omega
      have hd1 : M + 2 ≤ oddDigit2M M y1 := by rw [oddDigit2M_of_even hy1_ev]; omega
      unfold P2MOp; rw [(summable_P2M_term M hM (fun w => Real.log (oddDigit2M M w : ℝ)) y).tsum_eq_zero_add]
      simp only [Function.iterate_zero, id_eq]
      have htail_nn : 0 ≤ ∑' v : ℕ, (2 : ℝ) ^ (-((v + 1 : ℕ) + 1 : ℤ)) *
          Real.log (oddDigit2M M ((hStep2M M hM)^[v + 1] (qStep2M M hM y)) : ℝ) :=
        tsum_nonneg fun v => mul_nonneg (by positivity)
          (Real.log_nonneg (by exact_mod_cast oddDigit2M_pos hM _))
      have hlog : Real.log ((M : ℝ) + 1) ≤ Real.log (oddDigit2M M y1 : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (by omega : M + 1 ≤ oddDigit2M M y1))
      have h0 : (2 : ℝ) ^ (-((0 : ℕ) + 1 : ℤ)) = 1 / 2 := by norm_num
      rw [h0]; have hln2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
/-- Lemma (`lem:even-drift-bounds`, part 2b): every stationary law of `P_{2M}` (`M ≥ 1` odd) has drift -/
theorem lem_even_drift_bounds_2M {M : ℕ} (hM : 1 ≤ M) (hodd : M % 2 = 1)
    {π : Fin M → ℝ} (hstat : IsStationary2M M hM π) :
    (1 / 2 : ℝ) * Real.log (((M : ℝ) + 1) / 64) ≤ drift2M M π := by
  obtain ⟨hnn, hsum1, hinv⟩ := hstat
  have hdrift : drift2M M π =
      ∑ y : Fin M, π y * (P2MOp M hM (fun w => Real.log (oddDigit2M M w : ℝ)) y - 2 * Real.log 2) := by
    unfold drift2M; have h1 := hinv (fun w => Real.log (oddDigit2M M w : ℝ))
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum1, one_mul] at h1 ⊢; linarith
  rw [hdrift]
  have hlog64 : (1 / 2 : ℝ) * Real.log (((M : ℝ) + 1) / 64) =
      (1 / 2 : ℝ) * Real.log ((M : ℝ) + 1) - 3 * Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num),
        show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    push_cast; ring
  rw [hlog64]
  calc (1 / 2 : ℝ) * Real.log ((M : ℝ) + 1) - 3 * Real.log 2
      = ∑ y : Fin M, π y * ((1 / 2 : ℝ) * Real.log ((M : ℝ) + 1) - 3 * Real.log 2) := by
        rw [← Finset.sum_mul, hsum1, one_mul]
    _ ≤ ∑ y : Fin M, π y *
          (P2MOp M hM (fun w => Real.log (oddDigit2M M w : ℝ)) y - 2 * Real.log 2) := by
        refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (hnn y)
        linarith [lem_even_drift_bounds_2M_step hM hodd y]
lemma drift2M_pos_of_ge_65 {M : ℕ} (hM : 65 ≤ M) (hodd : M % 2 = 1)
    {π : Fin M → ℝ} (hstat : IsStationary2M M (by omega) π) :
    0 < drift2M M π := by
  have hlb := lem_even_drift_bounds_2M (by omega) hodd hstat
  have hgt1 : (1 : ℝ) < ((M : ℝ) + 1) / 64 := by
    have : (65 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hpos : 0 < (1 / 2 : ℝ) * Real.log (((M : ℝ) + 1) / 64) := mul_pos (by norm_num) (Real.log_pos hgt1)
  linarith
lemma drift2M_gt_quarter_of_ge_105 {M : ℕ} (hM : 105 ≤ M) (hodd : M % 2 = 1)
    {π : Fin M → ℝ} (hstat : IsStationary2M M (by omega) π) :
    (1 / 4 : ℝ) < drift2M M π := by
  have hlb := lem_even_drift_bounds_2M (by omega) hodd hstat
  have hexp : Real.exp (1 / 2 : ℝ) < ((M : ℝ) + 1) / 64 := by
    have hM105 : (105 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have h1 : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by rw [sq, ← Real.exp_add]; norm_num
    have h2 : Real.exp 1 < ((106 / 64 : ℝ)) ^ 2 := by
      have he := Real.exp_one_lt_d9; norm_num at he ⊢; linarith
    have h3 : Real.exp (1 / 2 : ℝ) < 106 / 64 := by nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    linarith
  have hlog : (1 / 2 : ℝ) < Real.log (((M : ℝ) + 1) / 64) := by
    rw [← Real.log_exp (1 / 2 : ℝ)]; exact Real.log_lt_log (Real.exp_pos _) hexp
  linarith

/-! ## Part 3: Pure-kernel certificate bridge for finite odd `M ∈ [7, 103]` -/
private lemma exp_one_hundredth_le : Real.exp (1 / 100 : ℝ) ≤ 100 / 99 := by
  have h := Real.add_one_le_exp (-(1 / 100 : ℝ))
  have h1 : (99 / 100 : ℝ) ≤ (Real.exp (1 / 100 : ℝ))⁻¹ := by rw [← Real.exp_neg]; linarith
  have h2 := inv_anti₀ (by norm_num : (0 : ℝ) < 99 / 100) h1
  rw [inv_inv] at h2; linarith [show (99 / 100 : ℝ)⁻¹ = 100 / 99 by norm_num]
private lemma kVal_div_100_le_log (i : ℕ) (hi : i < 103) : (kVal i : ℝ) / 100 ≤ Real.log ((2 * i + 1 : ℕ) : ℝ) := by
  have hnat := kVal_sound i hi
  have hR : (100 : ℝ) ^ kVal i ≤ ((2 * i + 1 : ℕ) : ℝ) * (99 : ℝ) ^ kVal i := by exact_mod_cast hnat
  have hexp : Real.exp ((kVal i : ℝ) / 100) ≤ ((2 * i + 1 : ℕ) : ℝ) := by
    have hpow : Real.exp ((kVal i : ℝ) / 100) = (Real.exp (1 / 100 : ℝ)) ^ kVal i := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [hpow]
    calc (Real.exp (1 / 100 : ℝ)) ^ kVal i
        ≤ (100 / 99 : ℝ) ^ kVal i := pow_le_pow_left₀ (Real.exp_pos _).le exp_one_hundredth_le _
      _ = (100 : ℝ) ^ kVal i / (99 : ℝ) ^ kVal i := div_pow _ _ _
      _ ≤ ((2 * i + 1 : ℕ) : ℝ) := by rw [div_le_iff₀ (by positivity)]; exact hR
  rw [← Real.log_exp ((kVal i : ℝ) / 100)]; exact Real.log_le_log (Real.exp_pos _) hexp
private lemma uIter_eq_K2MOp_iter (M : ℕ) (hM : 1 ≤ M) :
    ∀ (i : ℕ) (y : Fin M),
      (uIter M i y.val : ℝ) / (100 * (2 : ℝ) ^ i) =
        (K2MOp M hM)^[i] (fun w => (kVal (oddDigitNat M w.val / 2) : ℝ) / 100) y := by
  intro i
  induction i with
  | zero => intro y; simp [uIter]
  | succ i ih =>
    intro y; rw [Function.iterate_succ_apply']
    have hK : K2MOp M hM ((K2MOp M hM)^[i] (fun w => (kVal (oddDigitNat M w.val / 2) : ℝ) / 100)) y =
        (1 / 2 : ℝ) * ((K2MOp M hM)^[i] (fun w => (kVal (oddDigitNat M w.val / 2) : ℝ) / 100) (hStep2M M hM y) +
          (K2MOp M hM)^[i] (fun w => (kVal (oddDigitNat M w.val / 2) : ℝ) / 100) (qStep2M M hM y)) := rfl
    rw [hK, ← ih (hStep2M M hM y), ← ih (qStep2M M hM y)]
    have hu : uIter M (i + 1) y.val = uIter M i (hStep2M M hM y).val + uIter M i (qStep2M M hM y).val := rfl
    rw [hu, Nat.cast_add, pow_succ]; ring
private lemma accIter_eq_sum_K2MOp (M : ℕ) (hM : 1 ≤ M) :
    ∀ (k : ℕ) (y : Fin M),
      (accIter M k y.val : ℝ) / (100 * (2 : ℝ) ^ k) =
        ∑ i ∈ Finset.range (k + 1),
          (K2MOp M hM)^[i] (fun w => (kVal (oddDigitNat M w.val / 2) : ℝ) / 100) y := by
  intro k
  induction k with
  | zero => intro y; simp [accIter, uIter]
  | succ k ih =>
    intro y; rw [Finset.sum_range_succ, ← ih y, ← uIter_eq_K2MOp_iter M hM (k + 1) y]
    have ha : accIter M (k + 1) y.val = 2 * accIter M k y.val + uIter M (k + 1) y.val := rfl
    rw [ha, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, pow_succ]; ring
private lemma stationary_KM_iter (M : ℕ) (hM : 1 ≤ M) {π : Fin M → ℝ}
    (hstat : IsStationaryKM M hM π) (f : Fin M → ℝ) :
    ∀ i : ℕ, ∑ y : Fin M, π y * (K2MOp M hM)^[i] f y = ∑ y : Fin M, π y * f y := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    rw [show (fun y => π y * (K2MOp M hM)^[i + 1] f y) =
        (fun y => π y * K2MOp M hM ((K2MOp M hM)^[i] f) y) by
      ext y; rw [Function.iterate_succ_apply']]
    rw [hstat.2.2 _, ih]
private lemma drift2M_gt_of_checkOneM {M L rhsMult : ℕ} (hM : 1 ≤ M) (hM103 : M ≤ 103)
    (hodd : M % 2 = 1) (hL : 1 ≤ L) (hcert : checkOneM M L rhsMult = true)
    {π : Fin M → ℝ} (hstat : IsStationary2M M hM π) :
    (rhsMult : ℝ) / 100 - 2 * Real.log 2 < drift2M M π := by
  have hstatK := (stationary_P2M_iff_stationary_KM M hM π).mp hstat; have hnn := hstatK.1; have hsum1 := hstatK.2.1
  let f : Fin M → ℝ := fun w => (kVal (oddDigitNat M w.val / 2) : ℝ) / 100
  have hf_le : ∀ w : Fin M, f w ≤ Real.log (oddDigit2M M w : ℝ) := by
    intro w; have hlt : oddDigitNat M w.val < 2 * M := oddDigit2M_lt w
    have hodd_d : oddDigitNat M w.val % 2 = 1 := oddDigit2M_odd hodd w
    have hi : oddDigitNat M w.val / 2 < 103 := by omega
    have h2i : 2 * (oddDigitNat M w.val / 2) + 1 = oddDigitNat M w.val := by omega
    have hlog := kVal_div_100_le_log (oddDigitNat M w.val / 2) hi; rw [h2i] at hlog; exact hlog
  have hpi_f : ∑ y : Fin M, π y * f y ≤ ∑ y : Fin M, π y * Real.log (oddDigit2M M y : ℝ) :=
    Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hf_le y) (hnn y)
  have hmean : (L : ℝ) * ∑ y : Fin M, π y * f y =
      ∑ y : Fin M, π y * ((accIter M (L - 1) y.val : ℝ) / (100 * (2 : ℝ) ^ (L - 1))) := by
    have hsum_iter : ∑ i ∈ Finset.range L, ∑ y : Fin M, π y * (K2MOp M hM)^[i] f y =
        (L : ℝ) * ∑ y : Fin M, π y * f y := by
      simp_rw [stationary_KM_iter M hM hstatK f]
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [← hsum_iter, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum]
    conv_lhs => rw [show L = (L - 1) + 1 by omega, ← accIter_eq_sum_K2MOp M hM (L - 1) y]
  have hpt : ∀ y : Fin M,
      (rhsMult : ℝ) / 100 * (L : ℝ) <
        (accIter M (L - 1) y.val : ℝ) / (100 * (2 : ℝ) ^ (L - 1)) := by
    intro y; have hnat := checkOneM_sound hM hL hcert y.val y.isLt
    have hR : (rhsMult : ℝ) * (L : ℝ) * (2 : ℝ) ^ (L - 1) < (accIter M (L - 1) y.val : ℝ) := by exact_mod_cast hnat
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 100 * (2 : ℝ) ^ (L - 1))]
    linarith
  have hex_pos : ∃ y : Fin M, 0 < π y := by
    by_contra hall; push Not at hall
    have : ∑ y : Fin M, π y ≤ 0 := Finset.sum_nonpos fun y _ => hall y
    linarith
  have hstrict : (rhsMult : ℝ) / 100 * (L : ℝ) < (L : ℝ) * ∑ y : Fin M, π y * f y := by
    rw [hmean]
    calc (rhsMult : ℝ) / 100 * (L : ℝ)
        = ∑ y : Fin M, π y * ((rhsMult : ℝ) / 100 * (L : ℝ)) := by rw [← Finset.sum_mul, hsum1, one_mul]
      _ < ∑ y : Fin M, π y * ((accIter M (L - 1) y.val : ℝ) / (100 * (2 : ℝ) ^ (L - 1))) := by
          refine Finset.sum_lt_sum ?_ ?_
          · intro y _; exact mul_le_mul_of_nonneg_left (hpt y).le (hnn y)
          · obtain ⟨y, hpy⟩ := hex_pos; exact ⟨y, Finset.mem_univ y, mul_lt_mul_of_pos_left (hpt y) hpy⟩
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hgt_f : (rhsMult : ℝ) / 100 < ∑ y : Fin M, π y * f y := by nlinarith
  have hdrift : drift2M M π =
      ∑ y : Fin M, π y * Real.log (oddDigit2M M y : ℝ) - 2 * Real.log 2 := by
    unfold drift2M; simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum1, one_mul]
  linarith
lemma two_log_two_lt_139 : 2 * Real.log 2 < 139 / 100 := by have h := Real.log_two_lt_d9; linarith
lemma drift2M_M7_pos {π : Fin 7 → ℝ} (hstat : IsStationary2M 7 (by omega) π) : 0 < drift2M 7 π := by
  have h := drift2M_gt_of_checkOneM (by omega) (by omega) (by decide) (by omega) checkM7_pos hstat
  have h2 := two_log_two_lt_139; norm_num at h; linarith
lemma drift2M_9_to_103_gt_quarter {M : ℕ} (hodd : M % 2 = 1) (hlo : 9 ≤ M) (hhi : M ≤ 103)
    {π : Fin M → ℝ} (hstat : IsStationary2M M (by omega) π) :
    (1 / 4 : ℝ) < drift2M M π := by
  obtain ⟨L, hL, hcert⟩ := checkOneM_9_to_103 M hodd hlo hhi
  have h := drift2M_gt_of_checkOneM (by omega) hhi hodd hL hcert hstat
  have h2 := two_log_two_lt_139; norm_num at h; linarith

/-! ## Part 4: Explicit unique stationary laws for `P_2, P_4, P_6, P_8, P_{10}, P_{14}` -/
private lemma stationary_KM_eval_basis {M : ℕ} (hM : 1 ≤ M) {π : Fin M → ℝ}
    (hstat : IsStationaryKM M hM π) (w : Fin M) :
    (∑ y : Fin M, π y * (if hStep2M M hM y = w then (1 / 2 : ℝ) else 0) +
     ∑ y : Fin M, π y * (if qStep2M M hM y = w then (1 / 2 : ℝ) else 0)) = π w := by
  have h := hstat.2.2 (fun u => if u = w then 1 else 0)
  have hrhs : ∑ y : Fin M, π y * (if y = w then (1 : ℝ) else 0) = π w := by simp
  rw [hrhs] at h; rw [← h, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  unfold K2MOp
  by_cases h1 : hStep2M M hM y = w <;> by_cases h2 : qStep2M M hM y = w <;> (simp [h1, h2]; try ring)
/-- `P_2` (`M = 1`): unique stationary law `π(0) = 1`, drift `-2 ln 2`. -/
theorem prop_P2_unique : ∃! π : Fin 1 → ℝ, IsStationary2M 1 (by omega) π ∧ drift2M 1 π = -2 * Real.log 2 := by
  refine ⟨fun _ => 1, ⟨?_, ?_⟩, ?_⟩
  · rw [stationary_P2M_iff_stationary_KM]
    refine ⟨fun _ => by norm_num, by simp, fun f => ?_⟩
    simp only [Fin.sum_univ_one, one_mul, K2MOp]; have h0h : hStep2M 1 (by omega) 0 = 0 := Subsingleton.elim _ _
    have h0q : qStep2M 1 (by omega) 0 = 0 := Subsingleton.elim _ _
    rw [h0h, h0q]; ring
  · unfold drift2M; simp [oddDigit2M, oddDigitNat]
  · intro π ⟨hstat, _⟩; ext i
    fin_cases i
    simpa using hstat.2.1
/-- `P_4` (`k = 1`): unique stationary law `(1/2, 1/2)` on `{1, 3}`, drift `(1/2) ln 3 - ln 2`. -/
theorem prop_P4_unique :
    ∃! π : Fin (2 * 1) → ℝ, IsStationary4k 1 (by omega) π ∧
      drift4k π = (1 / 2 : ℝ) * Real.log 3 - Real.log 2 := by
  refine ⟨pi4kBase 1 (by omega), ⟨pi4kBase_stationary 1 (by omega), ?_⟩, ?_⟩
  · rw [pi4kBase_drift 1 (by omega)]
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by norm_num)]
    norm_num; ring
  · intro π ⟨hstat, _⟩; have hsum : π 0 + π 1 = 1 := by have := hstat.2.1; rw [Fin.sum_univ_two] at this; exact this
    have h0 := hstat.2.2 (fun j => if j = (0 : Fin 2) then 1 else 0); rw [Fin.sum_univ_two] at h0
    simp only [P4kOp, next4kA, next4kB, digit4k] at h0; norm_num at h0; ext i
    fin_cases i <;> (simp only [pi4kBase]; norm_num; linarith)
/-- `P_6` (`M = 3`): unique stationary law `(0, 2/3, 1/3)` on `(3, 1, 5)`, drift `(1/3) ln 5 - 2 ln 2`. -/
theorem prop_P6_unique :
    ∃! π : Fin 3 → ℝ, IsStationary2M 3 (by omega) π ∧
      drift2M 3 π = (1 / 3 : ℝ) * Real.log 5 - 2 * Real.log 2 := by
  let pi6 : Fin 3 → ℝ := fun y => match y.val with | 0 => 0 | 1 => 2 / 3 | _ => 1 / 3
  have hstat6 : IsStationary2M 3 (by omega) pi6 := by
    rw [stationary_P2M_iff_stationary_KM]
    refine ⟨fun y => by fin_cases y <;> norm_num [pi6],
            by simp [Fin.sum_univ_three, pi6]; norm_num, fun f => ?_⟩
    simp only [Fin.sum_univ_three, K2MOp, hStep2M, qStep2M, hStepNat, qStepNat, oddDigitNat, pi6]
    norm_num; ring
  have hdrift6 : drift2M 3 pi6 = (1 / 3 : ℝ) * Real.log 5 - 2 * Real.log 2 := by
    unfold drift2M; simp only [Fin.sum_univ_three, oddDigit2M, oddDigitNat, pi6]
    norm_num; ring
  refine ⟨pi6, ⟨hstat6, hdrift6⟩, ?_⟩
  intro π ⟨hstat, _⟩; have hK := (stationary_P2M_iff_stationary_KM 3 (by omega) π).mp hstat
  have hsum : π 0 + π 1 + π 2 = 1 := by simpa [Fin.sum_univ_three] using hK.2.1
  have he0 := stationary_KM_eval_basis (by omega) hK (0 : Fin 3)
  have he2 := stationary_KM_eval_basis (by omega) hK (2 : Fin 3)
  simp only [Fin.sum_univ_three, hStep2M, qStep2M, hStepNat, qStepNat, oddDigitNat] at he0 he2; norm_num at he0 he2
  ext i
  fin_cases i <;> (simp only [pi6]; norm_num; linarith)
/-- `P_{10}` (`M = 5`): unique stationary law `(1/3, 1/5, 1/15, 4/15, 2/15)` on `(5, 1, 7, 3, 9)`, with exact -/
noncomputable def driftP10 : ℝ :=
  (4 / 15 : ℝ) * Real.log 3 + (1 / 3 : ℝ) * Real.log 5 +
  (1 / 15 : ℝ) * Real.log 7 + (2 / 15 : ℝ) * Real.log 9 - 2 * Real.log 2

theorem prop_P10_unique : ∃! π : Fin 5 → ℝ, IsStationary2M 5 (by omega) π ∧ drift2M 5 π = driftP10 := by
  let pi10 : Fin 5 → ℝ := fun y =>
    match y.val with | 0 => 1 / 3 | 1 => 1 / 5 | 2 => 1 / 15 | 3 => 4 / 15 | _ => 2 / 15
  have hstat10 : IsStationary2M 5 (by omega) pi10 := by
    rw [stationary_P2M_iff_stationary_KM]
    refine ⟨fun y => by fin_cases y <;> norm_num [pi10],
            by simp [Fin.sum_univ_five, pi10]; norm_num, fun f => ?_⟩
    simp only [Fin.sum_univ_five, K2MOp, hStep2M, qStep2M, hStepNat, qStepNat, oddDigitNat, pi10]
    norm_num; ring
  have hdrift10 : drift2M 5 pi10 = driftP10 := by
    unfold drift2M driftP10; simp only [Fin.sum_univ_five, oddDigit2M, oddDigitNat, pi10]
    norm_num; ring
  refine ⟨pi10, ⟨hstat10, hdrift10⟩, ?_⟩
  intro π ⟨hstat, _⟩; have hK := (stationary_P2M_iff_stationary_KM 5 (by omega) π).mp hstat
  have hsum : π 0 + π 1 + π 2 + π 3 + π 4 = 1 := by simpa [Fin.sum_univ_five] using hK.2.1
  have he0 := stationary_KM_eval_basis (by omega) hK (0 : Fin 5)
  have he2 := stationary_KM_eval_basis (by omega) hK (2 : Fin 5)
  have he3 := stationary_KM_eval_basis (by omega) hK (3 : Fin 5)
  have he4 := stationary_KM_eval_basis (by omega) hK (4 : Fin 5)
  simp only [Fin.sum_univ_five, hStep2M, qStep2M, hStepNat, qStepNat, oddDigitNat] at he0 he2 he3 he4
  norm_num at he0 he2 he3 he4; ext i
  fin_cases i <;> (simp only [pi10]; norm_num; linarith)
/-- Proposition (`prop:near-zero`, part 2a): `P_8` (`k = 2`) has unique stationary law `(1/2, 0, 1/2, 0)` on -/
theorem prop_near_zero_P8 :
    (∃! π : Fin (2 * 2) → ℝ, IsStationary4k 2 (by omega) π ∧
      drift4k π = Real.log (Real.sqrt 5 / 2)) ∧
    0 < Real.log (Real.sqrt 5 / 2) ∧ Real.log (Real.sqrt 5 / 2) < 1 / 4 := by
  refine ⟨⟨pi4kBase 2 (by omega), ⟨pi4kBase_stationary 2 (by omega), ?_⟩, ?_⟩, ?_, ?_⟩
  · rw [pi4kBase_drift 2 (by omega)]; norm_num
  · intro π ⟨hstat, _⟩
    have hsum : π 0 + π 1 + π 2 + π 3 = 1 := by have := hstat.2.1; rw [Fin.sum_univ_four] at this; exact this
    have he1 := hstat.2.2 (fun j => if j = (1 : Fin 4) then 1 else 0)
    have he3 := hstat.2.2 (fun j => if j = (3 : Fin 4) then 1 else 0)
    have he0 := hstat.2.2 (fun j => if j = (0 : Fin 4) then 1 else 0); rw [Fin.sum_univ_four] at he1 he3 he0
    simp only [P4kOp, next4kA, next4kB, digit4k] at he1 he3 he0; norm_num at he1 he3 he0; ext i
    fin_cases i <;> (simp only [pi4kBase]; norm_num; linarith)
  · apply Real.log_pos
    have : (2 : ℝ) < Real.sqrt 5 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  ·
    have hexp : Real.sqrt 5 / 2 < Real.exp (1 / 4 : ℝ) := by
      have h1 : (5 / 4 : ℝ) < Real.exp (1 / 2 : ℝ) := by
        have h2 : (25 / 16 : ℝ) < Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
        have hsq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by rw [sq, ← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos (1 / 2 : ℝ)]
      have hsq2 : (Real.exp (1 / 4 : ℝ)) ^ 2 = Real.exp (1 / 2 : ℝ) := by rw [sq, ← Real.exp_add]; norm_num
      have hsqL : (Real.sqrt 5 / 2) ^ 2 = 5 / 4 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
      nlinarith [Real.exp_pos (1 / 4 : ℝ), Real.sqrt_nonneg 5]
    rw [← Real.log_exp (1 / 4 : ℝ)]; exact Real.log_lt_log (by positivity) hexp
/-- Proposition (`prop:near-zero`, part 2b): `P_{14}` (`M = 7`) has unique stationary law -/
noncomputable def piP14 : Fin 7 → ℝ := fun y =>
  match y.val with
  | 0 => 0
  | 1 => 2 / 7
  | 2 => 1 / 14
  | 3 => 3 / 28
  | 4 => 1 / 7
  | 5 => 5 / 28
  | _ => 3 / 14

theorem prop_near_zero_P14 :
    (∃! π : Fin 7 → ℝ, IsStationary2M 7 (by omega) π ∧ π = piP14) ∧
    0 < drift2M 7 piP14 ∧ drift2M 7 piP14 < 1 / 4 := by
  have hstat14 : IsStationary2M 7 (by omega) piP14 := by
    rw [stationary_P2M_iff_stationary_KM]
    refine ⟨fun y => by fin_cases y <;> norm_num [piP14],
            by simp [Fin.sum_univ_succ, piP14]; norm_num, fun f => ?_⟩
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, K2MOp, hStep2M, qStep2M, hStepNat, qStepNat,
      oddDigitNat, piP14]
    norm_num; ring
  have huniq : ∀ π : Fin 7 → ℝ, IsStationary2M 7 (by omega) π → π = piP14 := by
    intro π hstat; have hK := (stationary_P2M_iff_stationary_KM 7 (by omega) π).mp hstat
    have hsum : π 0 + π 1 + π 2 + π 3 + π 4 + π 5 + π 6 = 1 := by
      have := hK.2.1
      rw [Fin.sum_univ_seven] at this; exact this
    have he0 := stationary_KM_eval_basis (by omega) hK (0 : Fin 7)
    have he2 := stationary_KM_eval_basis (by omega) hK (2 : Fin 7)
    have he3 := stationary_KM_eval_basis (by omega) hK (3 : Fin 7)
    have he4 := stationary_KM_eval_basis (by omega) hK (4 : Fin 7)
    have he5 := stationary_KM_eval_basis (by omega) hK (5 : Fin 7)
    have he6 := stationary_KM_eval_basis (by omega) hK (6 : Fin 7)
    simp only [Fin.sum_univ_seven, hStep2M, qStep2M, hStepNat, qStepNat,
      oddDigitNat] at he0 he2 he3 he4 he5 he6
    norm_num at he0 he2 he3 he4 he5 he6; ext i
    fin_cases i <;> (simp only [piP14]; norm_num; linarith)
  refine ⟨⟨piP14, ⟨hstat14, rfl⟩, fun π ⟨hs, _⟩ => huniq π hs⟩,
          drift2M_M7_pos hstat14, ?_⟩
  have hnum : (3 : ℝ) ^ 3 * 5 ^ 5 * 9 ^ 2 * 11 ^ 4 * 13 ^ 6 < (2 : ℝ) ^ 56 * (2 : ℝ) ^ 7 := by norm_num
  have h2_lt_e : (2 : ℝ) < Real.exp 1 := by have hgt := Real.exp_one_gt_d9; linarith
  have h27 : (2 : ℝ) ^ 7 < Real.exp 7 := by
    rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_lt_pow_left₀ h2_lt_e (by norm_num) (by norm_num)
  have hprod : (3 : ℝ) ^ 3 * 5 ^ 5 * 9 ^ 2 * 11 ^ 4 * 13 ^ 6 < (2 : ℝ) ^ 56 * Real.exp 7 :=
    hnum.trans (mul_lt_mul_of_pos_left h27 (by positivity))
  have hlog := Real.log_lt_log (by positivity) hprod
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (Real.exp_pos 7).ne', Real.log_exp] at hlog
  simp only [Real.log_pow] at hlog; push_cast at hlog
  have hd : drift2M 7 piP14 =
      ((3 : ℝ) * Real.log 3 + 5 * Real.log 5 + 2 * Real.log 9 + 4 * Real.log 11 +
       6 * Real.log 13 - 56 * Real.log 2) / 28 := by
    unfold drift2M; simp only [Fin.sum_univ_seven, oddDigit2M, oddDigitNat, piP14]
    norm_num; ring
  rw [hd]; linarith
/-- Proposition (`prop:near-zero`, part 3): strict ordering of the four non-positive drifts -/
theorem prop_near_zero_ordering :
    -2 * Real.log 2 < (1 / 3 : ℝ) * Real.log 5 - 2 * Real.log 2 ∧
    (1 / 3 : ℝ) * Real.log 5 - 2 * Real.log 2 < (1 / 2 : ℝ) * Real.log 3 - Real.log 2 ∧
    (1 / 2 : ℝ) * Real.log 3 - Real.log 2 < driftP10 ∧
    driftP10 < 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : 0 < Real.log 5 := Real.log_pos (by norm_num)
    linarith
  ·
    have hlog := Real.log_lt_log (by norm_num) (show (5 : ℝ) ^ 2 < 3 ^ 3 * 2 ^ 6 by norm_num)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow] at hlog
    push_cast at hlog; linarith
  ·
    have hlog := Real.log_lt_log (by positivity)
      (show (2 : ℝ) ^ 30 < 3 ^ 1 * 5 ^ 10 * 7 ^ 2 by norm_num)
    have h9 : Real.log 9 = 2 * Real.log 3 := by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at hlog
    push_cast at hlog; unfold driftP10; linarith
  ·
    have hlog := Real.log_lt_log (by positivity)
      (show (3 : ℝ) ^ 8 * 5 ^ 5 * 7 < 2 ^ 30 by norm_num)
    have h9 : Real.log 9 = 2 * Real.log 3 := by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow] at hlog
    push_cast at hlog; unfold driftP10; linarith

/-! ## Part 5: Unified all-even-base statements (`thm:even-bases`, `prop:near-zero`, `cor:drift-growth`) -/
/-- Unified statement: "even base `b ≥ 2` has a stationary law of `P_b` with drift in `I`". -/
def HasStationaryDriftIn (b : ℕ) (P : ℝ → Prop) : Prop :=
  if 4 ∣ b then
    ∃ (hk : 1 ≤ b / 4) (π : Fin (2 * (b / 4)) → ℝ),
      IsStationary4k (b / 4) hk π ∧ P (drift4k π)
  else
    ∃ (hM : 1 ≤ b / 2) (π : Fin (b / 2) → ℝ),
      IsStationary2M (b / 2) hM π ∧ P (drift2M (b / 2) π)
/-- Unified statement: "every stationary law of `P_b` satisfies `P (drift)`". -/
def AllStationaryDriftsSatisfy (b : ℕ) (P : ℝ → Prop) : Prop :=
  if 4 ∣ b then
    ∀ (hk : 1 ≤ b / 4) (π : Fin (2 * (b / 4)) → ℝ),
      IsStationary4k (b / 4) hk π → P (drift4k π)
  else
    ∀ (hM : 1 ≤ b / 2) (π : Fin (b / 2) → ℝ),
      IsStationary2M (b / 2) hM π → P (drift2M (b / 2) π)
/-- Theorem (`thm:even-bases`): for every even integer `b ≥ 2`, the Markov chain `P_b` has a stationary law with -/
theorem thm_even_bases {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) :
    HasStationaryDriftIn b (· ≤ 0) ↔ b = 2 ∨ b = 4 ∨ b = 6 ∨ b = 10 := by
  unfold HasStationaryDriftIn
  split_ifs with h4
  ·
    have hk : 1 ≤ b / 4 := by omega
    have hiff := lem_even_drift_bounds_4k_nonpos hk; constructor
    · rintro ⟨_, π, hstat, hle⟩; have hk1 : b / 4 = 1 := hiff.mp ⟨π, hstat, hle⟩
      right; left; omega
    · rintro (rfl | rfl | rfl | rfl)
      · omega
      · obtain ⟨π, hstat, hle⟩ := hiff.mpr rfl; exact ⟨hk, π, hstat, hle⟩
      · omega
      · omega
  ·
    have hM1 : 1 ≤ b / 2 := by omega
    have hModd : (b / 2) % 2 = 1 := by omega
    constructor
    · rintro ⟨_, π, hstat, hle⟩
      by_cases hMge65 : 65 ≤ b / 2
      · exfalso; linarith [drift2M_pos_of_ge_65 hMge65 hModd hstat]
      by_cases hMge9 : 9 ≤ b / 2
      · exfalso; linarith [drift2M_9_to_103_gt_quarter hModd hMge9 (by omega) hstat]
      by_cases hM7 : b / 2 = 7
      · exfalso; have hb14 : b = 14 := by omega
        subst hb14; linarith [drift2M_M7_pos hstat]
      · have hsmall : b / 2 = 1 ∨ b / 2 = 3 ∨ b / 2 = 5 := by omega
        rcases hsmall with h | h | h
        · left; omega
        · right; right; left; omega
        · right; right; right; omega
    · rintro (rfl | rfl | rfl | rfl)
      · obtain ⟨π, ⟨hstat, hdrift⟩, _⟩ := prop_P2_unique
        exact ⟨by omega, π, hstat, by rw [hdrift]; linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]⟩
      · omega
      · obtain ⟨π, ⟨hstat, hdrift⟩, _⟩ := prop_P6_unique
        exact ⟨by omega, π, hstat, by
          rw [hdrift]
          have := prop_near_zero_ordering
          linarith⟩
      · obtain ⟨π, ⟨hstat, hdrift⟩, _⟩ := prop_P10_unique
        exact ⟨by omega, π, hstat, by rw [hdrift]; exact prop_near_zero_ordering.2.2.2.le⟩
/-- Proposition (`prop:near-zero`, part 1): if even `b ≥ 2` and `b ∉ {2, 4, 6, 8, 10, 14}`, every stationary law -/
theorem prop_near_zero_outside {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0)
    (hne2 : b ≠ 2) (hne4 : b ≠ 4) (hne6 : b ≠ 6) (hne8 : b ≠ 8) (hne10 : b ≠ 10) (hne14 : b ≠ 14) :
    AllStationaryDriftsSatisfy b (fun x => (1 / 4 : ℝ) < x) := by
  unfold AllStationaryDriftsSatisfy
  split_ifs with h4
  · intro hk π hstat; have hk3 : 3 ≤ b / 4 := by omega
    have hlb := lem_even_drift_bounds_4k_all hk hstat
    have hexp : Real.exp (1 / 4 : ℝ) < Real.sqrt (2 * ((b / 4 : ℕ) : ℝ) + 1) / 2 := by
      have h7 : (7 : ℝ) ≤ 2 * ((b / 4 : ℕ) : ℝ) + 1 := by
        have : (3 : ℝ) ≤ ((b / 4 : ℕ) : ℝ) := by exact_mod_cast hk3
        linarith
      have he : Real.exp 1 < (7 / 4 : ℝ) ^ 2 := by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
      have hhalf : Real.exp (1 / 2 : ℝ) < 7 / 4 := by
        have hsq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by rw [sq, ← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos (1 / 2 : ℝ)]
      have hq : (Real.exp (1 / 4 : ℝ)) ^ 2 = Real.exp (1 / 2 : ℝ) := by rw [sq, ← Real.exp_add]; norm_num
      have hsqrt_ge : (7 / 4 : ℝ) ≤ (Real.sqrt (2 * ((b / 4 : ℕ) : ℝ) + 1) / 2) ^ 2 := by
        rw [div_pow, Real.sq_sqrt (by positivity)]; linarith
      nlinarith [Real.exp_pos (1 / 4 : ℝ), Real.sqrt_nonneg (2 * ((b / 4 : ℕ) : ℝ) + 1)]
    have hlog : (1 / 4 : ℝ) < Real.log (Real.sqrt (2 * ((b / 4 : ℕ) : ℝ) + 1) / 2) := by
      rw [← Real.log_exp (1 / 4 : ℝ)]; exact Real.log_lt_log (Real.exp_pos _) hexp
    linarith
  · intro hM π hstat; have hModd : (b / 2) % 2 = 1 := by omega
    have hM9 : 9 ≤ b / 2 := by omega
    by_cases hM105 : 105 ≤ b / 2
    · exact drift2M_gt_quarter_of_ge_105 hM105 hModd hstat
    · exact drift2M_9_to_103_gt_quarter hModd hM9 (by omega) hstat
/-- Proposition (`prop:near-zero`, band characterization): `P_b` has a stationary law in `[-1/4, 1/4]` iff -/
theorem prop_near_zero_band {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) :
    (HasStationaryDriftIn b (fun x => -(1 / 4 : ℝ) ≤ x ∧ x ≤ 1 / 4) ↔
      b = 4 ∨ b = 8 ∨ b = 10 ∨ b = 14) ∧
    (HasStationaryDriftIn b (fun x => -(1 / 4 : ℝ) ≤ x ∧ x < 0) ↔
      b = 4 ∨ b = 10) := by
  have hP2_lt : -2 * Real.log 2 < -(1 / 4 : ℝ) := by have := Real.log_two_gt_d9; linarith
  have hP6_lt : (1 / 3 : ℝ) * Real.log 5 - 2 * Real.log 2 < -(1 / 4 : ℝ) := by
    have he3 : Real.exp 3 < (2 : ℝ) ^ 5 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      have he := Real.exp_one_lt_d9; have h1 : Real.exp 1 < 3 := by linarith
      calc Real.exp 1 ^ 3 < (3 : ℝ) ^ 3 := pow_lt_pow_left₀ h1 (Real.exp_pos _).le (by norm_num)
        _ < (2 : ℝ) ^ 5 := by norm_num
    have hlog3 : (3 : ℝ) < 5 * Real.log 2 := by
      have h := Real.log_lt_log (Real.exp_pos 3) he3
      rw [Real.log_exp, Real.log_pow] at h; push_cast at h; exact h
    have hlog5 : 4 * Real.log 5 < 19 * Real.log 2 := by
      have h := Real.log_lt_log (by positivity) (show (5 : ℝ) ^ 4 < 2 ^ 19 by norm_num)
      rw [Real.log_pow, Real.log_pow] at h; push_cast at h; exact h
    linarith
  have hP4_in : -(1 / 4 : ℝ) ≤ (1 / 2 : ℝ) * Real.log 3 - Real.log 2 ∧
      (1 / 2 : ℝ) * Real.log 3 - Real.log 2 < 0 := by
    constructor
    ·
      have h1 : (16 / 9 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
      have hlog := Real.log_le_log (by norm_num) h1
      rw [Real.log_exp, Real.log_div (by norm_num) (by norm_num),
          show (16 : ℝ) = 2 ^ 4 by norm_num, show (9 : ℝ) = 3 ^ 2 by norm_num,
          Real.log_pow, Real.log_pow] at hlog
      push_cast at hlog; linarith
    · exact prop_near_zero_ordering.2.2.1.trans prop_near_zero_ordering.2.2.2
  have hP10_in : -(1 / 4 : ℝ) ≤ driftP10 ∧ driftP10 < 0 :=
    ⟨hP4_in.1.trans prop_near_zero_ordering.2.2.1.le, prop_near_zero_ordering.2.2.2⟩
  constructor
  · constructor
    · intro hhas
      by_contra hnot
      push Not at hnot
      obtain ⟨hne4, hne8, hne10, hne14⟩ := hnot
      by_cases hb2eq : b = 2
      · subst hb2eq; unfold HasStationaryDriftIn at hhas
        simp only [show ¬ 4 ∣ 2 by decide] at hhas
        obtain ⟨_, π, hstat, hlo, _⟩ := hhas
        obtain ⟨π0, ⟨_, hd0⟩, huniq⟩ := prop_P2_unique
        have hpi : π = π0 := huniq π ⟨hstat, by
          have hsum : π 0 = 1 := by simpa using hstat.2.1
          unfold drift2M; simp [oddDigit2M, oddDigitNat, hsum]⟩
        rw [hpi, hd0] at hlo; linarith
      by_cases hb6eq : b = 6
      · subst hb6eq; unfold HasStationaryDriftIn at hhas
        simp only [show ¬ 4 ∣ 6 by decide] at hhas
        obtain ⟨_, π, hstat, hlo, _⟩ := hhas
        obtain ⟨π0, ⟨hstat0, hd0⟩, huniq⟩ := prop_P6_unique
        have hK := (stationary_P2M_iff_stationary_KM 3 (by omega) π).mp hstat
        have hsum : π 0 + π 1 + π 2 = 1 := by simpa [Fin.sum_univ_three] using hK.2.1
        have he0 := stationary_KM_eval_basis (by omega) hK (0 : Fin 3)
        have he2 := stationary_KM_eval_basis (by omega) hK (2 : Fin 3)
        simp only [Fin.sum_univ_three, hStep2M, qStep2M, hStepNat, qStepNat, oddDigitNat] at he0 he2
        norm_num at he0 he2
        have hd_eq : drift2M 3 π = (1 / 3 : ℝ) * Real.log 5 - 2 * Real.log 2 := by
          unfold drift2M; simp only [Fin.sum_univ_three, oddDigit2M, oddDigitNat]; norm_num
          have h0 : π 0 = 0 := by linarith
          have h1 : π 1 = 2 / 3 := by linarith
          have h2 : π 2 = 1 / 3 := by linarith
          rw [h0, h1, h2]; ring
        rw [hd_eq] at hlo; linarith
      · have hout := prop_near_zero_outside hb2 hbeven hb2eq hne4 hb6eq hne8 hne10 hne14
        unfold HasStationaryDriftIn at hhas; unfold AllStationaryDriftsSatisfy at hout
        split_ifs at hhas hout with h4
        · obtain ⟨hk, π, hstat, _, hhi⟩ := hhas; linarith [hout hk π hstat]
        · obtain ⟨hM, π, hstat, _, hhi⟩ := hhas; linarith [hout hM π hstat]
    · rintro (rfl | rfl | rfl | rfl)
      · unfold HasStationaryDriftIn; simp only [show 4 ∣ 4 by decide]
        obtain ⟨π, ⟨hstat, hd⟩, _⟩ := prop_P4_unique
        exact ⟨by omega, π, hstat, by rw [hd]; exact ⟨hP4_in.1, by linarith [hP4_in.2]⟩⟩
      · unfold HasStationaryDriftIn; simp only [show 4 ∣ 8 by decide]
        obtain ⟨⟨π, ⟨hstat, hd⟩, _⟩, hpos, hlt⟩ := prop_near_zero_P8
        exact ⟨by omega, π, hstat, by rw [hd]; exact ⟨by linarith, hlt.le⟩⟩
      · unfold HasStationaryDriftIn; simp only [show ¬ 4 ∣ 10 by decide]
        obtain ⟨π, ⟨hstat, hd⟩, _⟩ := prop_P10_unique
        exact ⟨by omega, π, hstat, by rw [hd]; exact ⟨hP10_in.1, by linarith [hP10_in.2]⟩⟩
      · unfold HasStationaryDriftIn; simp only [show ¬ 4 ∣ 14 by decide]
        obtain ⟨⟨π, ⟨hstat, hpeq⟩, _⟩, hpos, hlt⟩ := prop_near_zero_P14
        exact ⟨by omega, π, hstat, by rw [hpeq]; exact ⟨by linarith, hlt.le⟩⟩
  · constructor
    · intro hhas
      have hnonpos : HasStationaryDriftIn b (· ≤ 0) := by
        unfold HasStationaryDriftIn at hhas ⊢
        split_ifs at hhas ⊢
        · obtain ⟨hk, π, hstat, _, hlt⟩ := hhas; exact ⟨hk, π, hstat, hlt.le⟩
        · obtain ⟨hM, π, hstat, _, hlt⟩ := hhas; exact ⟨hM, π, hstat, hlt.le⟩
      rcases (thm_even_bases hb2 hbeven).mp hnonpos with rfl | rfl | rfl | rfl
      · exfalso; unfold HasStationaryDriftIn at hhas
        simp only [show ¬ 4 ∣ 2 by decide] at hhas
        obtain ⟨_, π, hstat, hlo, _⟩ := hhas; have hsum : π 0 = 1 := by simpa using hstat.2.1
        have hd : drift2M 1 π = -2 * Real.log 2 := by unfold drift2M; simp [oddDigit2M, oddDigitNat, hsum]
        rw [hd] at hlo; linarith
      · left; rfl
      · exfalso; unfold HasStationaryDriftIn at hhas
        simp only [show ¬ 4 ∣ 6 by decide] at hhas
        obtain ⟨_, π, hstat, hlo, _⟩ := hhas; have hK := (stationary_P2M_iff_stationary_KM 3 (by omega) π).mp hstat
        have hsum : π 0 + π 1 + π 2 = 1 := by simpa [Fin.sum_univ_three] using hK.2.1
        have he0 := stationary_KM_eval_basis (by omega) hK (0 : Fin 3)
        have he2 := stationary_KM_eval_basis (by omega) hK (2 : Fin 3)
        simp only [Fin.sum_univ_three, hStep2M, qStep2M, hStepNat, qStepNat, oddDigitNat] at he0 he2
        norm_num at he0 he2
        have hd : drift2M 3 π = (1 / 3 : ℝ) * Real.log 5 - 2 * Real.log 2 := by
          unfold drift2M; simp only [Fin.sum_univ_three, oddDigit2M, oddDigitNat]; norm_num
          have h0 : π 0 = 0 := by linarith
          have h1 : π 1 = 2 / 3 := by linarith
          have h2 : π 2 = 1 / 3 := by linarith
          rw [h0, h1, h2]; ring
        rw [hd] at hlo; linarith
      · right; rfl
    · rintro (rfl | rfl)
      · unfold HasStationaryDriftIn; simp only [show 4 ∣ 4 by decide]
        obtain ⟨π, ⟨hstat, hd⟩, _⟩ := prop_P4_unique
        exact ⟨by omega, π, hstat, by rw [hd]; exact hP4_in⟩
      · unfold HasStationaryDriftIn; simp only [show ¬ 4 ∣ 10 by decide]
        obtain ⟨π, ⟨hstat, hd⟩, _⟩ := prop_P10_unique
        exact ⟨by omega, π, hstat, by rw [hd]; exact hP10_in⟩
/-- Corollary (`cor:drift-growth`, part 1): for every even `b ≥ 2`, every stationary law of `P_b` has drift -/
theorem cor_drift_growth {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) :
    AllStationaryDriftsSatisfy b
      (fun x => (1 / 2 : ℝ) * Real.log ((b : ℝ) + 2) - (7 / 2 : ℝ) * Real.log 2 ≤ x) := by
  unfold AllStationaryDriftsSatisfy
  split_ifs with h4
  · intro hk π hstat; have hlb := lem_even_drift_bounds_4k_all hk hstat
    have hbeq : (b : ℝ) + 2 = 2 * (2 * ((b / 4 : ℕ) : ℝ) + 1) := by
      have : b = 4 * (b / 4) := by omega
      have hR : (b : ℝ) = 4 * ((b / 4 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have hpos : (0 : ℝ) < 2 * ((b / 4 : ℕ) : ℝ) + 1 := by positivity
    rw [Real.log_div (Real.sqrt_pos.mpr hpos).ne' (by norm_num), Real.log_sqrt hpos.le] at hlb
    rw [hbeq, Real.log_mul (by norm_num) hpos.ne']
    have hln2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · intro hM π hstat; have hModd : (b / 2) % 2 = 1 := by omega
    have hlb := lem_even_drift_bounds_2M hM hModd hstat
    have hbeq : (((b / 2 : ℕ) : ℝ) + 1) / 64 = ((b : ℝ) + 2) / 128 := by
      have : b = 2 * (b / 2) := by omega
      have hR : (b : ℝ) = 2 * ((b / 2 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    rw [hbeq, Real.log_div (by positivity) (by norm_num),
        show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow] at hlb
    push_cast at hlb; linarith
/-- Corollary (`cor:drift-growth`, part 2): when `4 ∣ b`, the least drift over stationary laws equals -/
theorem cor_drift_growth_4k {k : ℕ} (hk : 1 ≤ k) :
    (∀ π, IsStationary4k k hk π →
      (1 / 2 : ℝ) * Real.log (4 * (k : ℝ) + 2) - (3 / 2 : ℝ) * Real.log 2 ≤ drift4k π) ∧
    (IsStationary4k k hk (pi4kBase k hk) ∧
      drift4k (pi4kBase k hk) = (1 / 2 : ℝ) * Real.log (4 * (k : ℝ) + 2) - (3 / 2 : ℝ) * Real.log 2) := by
  have heq : Real.log (Real.sqrt (2 * (k : ℝ) + 1) / 2) =
      (1 / 2 : ℝ) * Real.log (4 * (k : ℝ) + 2) - (3 / 2 : ℝ) * Real.log 2 := by
    have hpos : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
    rw [Real.log_div (Real.sqrt_pos.mpr hpos).ne' (by norm_num), Real.log_sqrt hpos.le,
        show (4 * (k : ℝ) + 2) = 2 * (2 * (k : ℝ) + 1) by ring,
        Real.log_mul (by norm_num) hpos.ne']
    ring
  refine ⟨fun π hstat => heq ▸ lem_even_drift_bounds_4k_all hk hstat,
          pi4kBase_stationary k hk, (pi4kBase_drift k hk).trans heq⟩

end Ouroboros
