module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Interval.Finset.Nat
@[expose] public section

/-! # Core definitions for the Ouroboros paper (Paper 1) -/

namespace Ouroboros
/-- Last base-`b` digit of `n`. -/
def d_b (b n : ℕ) : ℕ := n % b
/-- The base-`b` last-digit map: `n / 2` for even `n`, `(n % b) * n + 1` for odd `n`. -/
def f_b (b n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (n % b) * n + 1
/-- The base-10 Ouroboros map `f = f_10`. -/
def f (n : ℕ) : ℕ := f_b 10 n
/-- Last decimal digit `d(n) = n % 10`. -/
def d (n : ℕ) : ℕ := n % 10
/-- The shortcut map `T`: `n / 2` for even `n`, `(d(n) * n + 1) / 2` for odd `n`. -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (d n * n + 1) / 2
/-- Classical Collatz shortcut map `T_C`: `y / 2` for even `y`, `(3 * y + 1) / 2` for odd `y`. -/
def T_C (y : ℕ) : ℕ := if y % 2 = 0 then y / 2 else (3 * y + 1) / 2
/-- Orbit of `n` under `g` reaches `m`. -/
def Reaches (g : ℕ → ℕ) (n m : ℕ) : Prop := ∃ k : ℕ, g^[k] n = m
/-- `n` reaches `1` under `f`. -/
def InBasin1 (n : ℕ) : Prop := Reaches f n 1
/-- `n` reaches `5` under `f`. -/
def InBasin5 (n : ℕ) : Prop := Reaches f n 5
/-- The Ouroboros Conjecture (Conjecture 1): every positive integer reaches `1` or `5`. -/
def OuroborosConjecture : Prop := ∀ n : ℕ, 0 < n → Reaches f n 1 ∨ Reaches f n 5
open Classical in
/-- Count of odd integers `n ≤ X` whose orbit under `f` reaches `1`. -/
noncomputable def N1 (X : ℕ) : ℕ := ((Finset.Icc 1 X).filter (fun n => n % 2 = 1 ∧ Reaches f n 1)).card
open Classical in
/-- Count of all positive integers `n ≤ X` whose orbit under `f` reaches `1`. -/
noncomputable def N1All (X : ℕ) : ℕ := ((Finset.Icc 1 X).filter (fun n => Reaches f n 1)).card
open Classical in
/-- Count of odd integers `n ≤ X` whose orbit under `f` reaches `5`. -/
noncomputable def N5 (X : ℕ) : ℕ := ((Finset.Icc 1 X).filter (fun n => n % 2 = 1 ∧ Reaches f n 5)).card
open Classical in
/-- Count of all positive integers `n ≤ X` whose orbit under `f` reaches `5`. -/
noncomputable def N5All (X : ℕ) : ℕ := ((Finset.Icc 1 X).filter (fun n => Reaches f n 5)).card

/-! ### Basic facts and small orbit checks from Section 1 -/
lemma f_even {n : ℕ} (h : n % 2 = 0) : f n = n / 2 := by simp [f, f_b, h]
lemma f_odd {n : ℕ} (h : n % 2 = 1) : f n = d n * n + 1 := by
  have h2 : n % 2 ≠ 0 := by omega
  simp [f, f_b, d, h2]
lemma f_odd_even {n : ℕ} (h : n % 2 = 1) : f n % 2 = 0 := by
  rw [f_odd h]; have hd : d n % 2 = 1 := by unfold d; omega
  have hmul : (d n * n) % 2 = 1 := by rw [Nat.mul_mod, hd, h]
  omega
lemma T_eq_f_or_ff (n : ℕ) : T n = if n % 2 = 0 then f n else f (f n) := by
  by_cases h : n % 2 = 0
  · simp [T, f, f_b, h]
  · have h1 : n % 2 = 1 := by omega
    have hfe : f n % 2 = 0 := f_odd_even h1; simp only [T, h, ↓reduceIte]; rw [f_even hfe, f_odd h1]
/-- Every `T`-iterate of `n` is an `f`-iterate of `n`. -/
theorem T_iter_is_f_iter (k n : ℕ) : ∃ m : ℕ, T^[k] n = f^[m] n := by
  induction k generalizing n with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply]; obtain ⟨m, hm⟩ := ih (T n); have hT := T_eq_f_or_ff n
    split_ifs at hT with h
    · refine ⟨m + 1, ?_⟩
      rw [Function.iterate_succ_apply, ← hT, hm]
    · refine ⟨m + 2, ?_⟩
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← hT, hm]
lemma reaches_trans {g : ℕ → ℕ} {a b c : ℕ}
    (h1 : Reaches g a b) (h2 : Reaches g b c) : Reaches g a c := by
  rcases h1 with ⟨k1, hk1⟩
  rcases h2 with ⟨k2, hk2⟩
  refine ⟨k2 + k1, ?_⟩
  rw [Function.iterate_add_apply, hk1, hk2]
lemma reaches_step {g : ℕ → ℕ} {a b : ℕ} (h : Reaches g (g a) b) : Reaches g a b := reaches_trans ⟨1, rfl⟩ h
lemma reaches_refl (g : ℕ → ℕ) (a : ℕ) : Reaches g a a := ⟨0, rfl⟩
/-- The two known cycles and Section 1 examples. -/
theorem f_cycle_one : f^[2] 1 = 1 := by decide
theorem f_cycle_five : f^[6] 5 = 5 := by decide
theorem f_ex_3 : f 3 = 10 := by decide
theorem f_ex_7 : f 7 = 50 := by decide
theorem f_ex_9 : f 9 = 82 := by decide
theorem f_ex_11 : f 11 = 12 := by decide
theorem f_ex_31_reaches_1 : f^[6] 31 = 1 := by decide
theorem f_ex_3_reaches_5 : f^[2] 3 = 5 := by decide
theorem f_ex_7_reaches_5 : f^[40] 7 = 5 := by decide

end Ouroboros
