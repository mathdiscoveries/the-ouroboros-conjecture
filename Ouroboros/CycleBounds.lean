module
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic
public import Ouroboros.Defs
public import Ouroboros.DensityDescent
public import Ouroboros.BasinOne
public import Ouroboros.BasinFive
@[expose] public section

/-! # Cycle-Bound Algebra, Halving Budget, Tail Bound, and Short-Cycle Uniqueness -/

namespace Ouroboros

/-! ## Section 1: Cyclic indexing and the `OddCycle` structure -/
/-- Cyclic successor on `Fin m` (for `0 < m`). -/
def finNext {m : ℕ} (hm : 0 < m) (i : Fin m) : Fin m := ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩
/-- Cyclic predecessor on `Fin m` (for `0 < m`). -/
def finPrev {m : ℕ} (hm : 0 < m) (i : Fin m) : Fin m := ⟨(i.val + (m - 1)) % m, Nat.mod_lt _ hm⟩
/-- `finNext` is a bijection on `Fin m`. -/
def finNextEquiv {m : ℕ} (hm : 0 < m) : Fin m ≃ Fin m where
  toFun := finNext hm
  invFun := finPrev hm
  left_inv i := by
    apply Fin.ext; change ((i.val + 1) % m + (m - 1)) % m = i.val; have hi : i.val < m := i.isLt
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; have hsum : i.val + 1 + (m - 1) = i.val + m := by omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  right_inv i := by
    apply Fin.ext; change ((i.val + (m - 1)) % m + 1) % m = i.val; have hi : i.val < m := i.isLt
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; have hsum : i.val + (m - 1) + 1 = i.val + m := by omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
/-- Cyclic `r`-step advance on `Fin m`. -/
def finAdd {m : ℕ} (hm : 0 < m) (i : Fin m) (r : ℕ) : Fin m := ⟨(i.val + r) % m, Nat.mod_lt _ hm⟩
lemma finAdd_zero {m : ℕ} (hm : 0 < m) (i : Fin m) : finAdd hm i 0 = i := by
  apply Fin.ext; simp [finAdd, Nat.mod_eq_of_lt i.isLt]
lemma finAdd_succ {m : ℕ} (hm : 0 < m) (i : Fin m) (r : ℕ) : finAdd hm i (r + 1) = finNext hm (finAdd hm i r) := by
  apply Fin.ext; change (i.val + (r + 1)) % m = ((i.val + r) % m + 1) % m
  rw [Nat.add_mod ((i.val + r) % m) 1 m, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
lemma finAdd_self {m : ℕ} (hm : 0 < m) (i : Fin m) : finAdd hm i m = i := by
  apply Fin.ext; change (i.val + m) % m = i.val; rw [Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
/-- An odd-member cycle of `f = f_10` with `m ≥ 1` odd steps. -/
structure OddCycle (m : ℕ) where
  hm : 0 < m
  x : Fin m → ℕ
  k : Fin m → ℕ
  x_pos : ∀ i, 0 < x i
  x_odd : ∀ i, x i % 2 = 1
  k_pos : ∀ i, 1 ≤ k i
  step : ∀ i : Fin m, d (x i) * x i + 1 = 2 ^ (k i) * x (finNext hm i)

namespace OddCycle
variable {m : ℕ} (C : OddCycle m)
/-- Total number of halvings `K = ∑ k_i`. -/
def totalHalvings : ℕ := ∑ i : Fin m, C.k i
/-- Product of odd last digits `D = ∏ d(x_i)`. -/
def digitProd : ℕ := ∏ i : Fin m, d (C.x i)
/-- Count of odd members in `C` with last decimal digit `dig`. -/
def countDigit (dig : ℕ) : ℕ := (Finset.univ.filter (fun i : Fin m => d (C.x i) = dig)).card

def n1 : ℕ := C.countDigit 1
def n3 : ℕ := C.countDigit 3
def n5 : ℕ := C.countDigit 5
def n7 : ℕ := C.countDigit 7
def n9 : ℕ := C.countDigit 9
/-- Prime-factor exponents `(a, b, c)` of `D = 3^a 5^b 7^c`. -/
def aExp : ℕ := C.n3 + 2 * C.n9
def bExp : ℕ := C.n5
def cExp : ℕ := C.n7
/-- Count of transitions `d_1 → d_2` around the cycle. -/
def countTrans (d1 d2 : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => d (C.x i) = d1 ∧ d (C.x (finNext C.hm i)) = d2)).card
/-- A *further cycle* is an odd cycle avoiding the two known cycles `{1, 2}` and `{5, 26, 13, 40, 20, 10}` -/
def IsFurther : Prop := ∀ i : Fin m, C.x i ≠ 1 ∧ C.x i ≠ 5
lemma d_mem (i : Fin m) : d (C.x i) = 1 ∨ d (C.x i) = 3 ∨ d (C.x i) = 5 ∨ d (C.x i) = 7 ∨ d (C.x i) = 9 := by
  have hodd := C.x_odd i; unfold d; omega
lemma d_pos (i : Fin m) : 0 < d (C.x i) := by
  rcases C.d_mem i with h | h | h | h | h <;> omega
lemma d_le_nine (i : Fin m) : d (C.x i) ≤ 9 := by
  rcases C.d_mem i with h | h | h | h | h <;> omega
lemma digitProd_pos : 0 < C.digitProd := Finset.prod_pos (fun i _ => C.d_pos i)
/-- One odd step plus its `k_i` halvings advances `x_i` to `x_{i+1}` under `f`. -/
theorem f_step (i : Fin m) : f^[1 + C.k i] (C.x i) = C.x (finNext C.hm i) := by
  rw [Nat.add_comm, Function.iterate_add_apply, Function.iterate_one]
  rw [f_odd (C.x_odd i), C.step i, f_iter_two_pow]
/-- Every odd member reaches the next odd member under `f`. -/
theorem reaches_next (i : Fin m) : Reaches f (C.x i) (C.x (finNext C.hm i)) := ⟨1 + C.k i, C.f_step i⟩
/-- Any intermediate iterate within one odd-step block is `≥ C.x (finNext C.hm i)` (for `1 ≤ r ≤ 1 + k_i`). -/
private lemma f_step_partial (i : Fin m) {r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ 1 + C.k i) :
    f^[r] (C.x i) = 2 ^ (1 + C.k i - r) * C.x (finNext C.hm i) := by
  have hsplit : r = (r - 1) + 1 := by omega
  have hk : C.k i = (r - 1) + (1 + C.k i - r) := by omega
  conv_lhs => rw [hsplit]
  rw [Function.iterate_add_apply, Function.iterate_one, f_odd (C.x_odd i), C.step i]
  conv_lhs => rw [hk]
  rw [pow_add, mul_assoc, f_iter_two_pow]
/-- Every `f`-iterate (odd or even) starting from any odd member of `C` is at least every lower bound `X` on the -/
theorem f_orbit_ge_min {X : ℕ} (hmin : ∀ j : Fin m, X ≤ C.x j) (i : Fin m) (t : ℕ) : X ≤ f^[t] (C.x i) := by
  induction t using Nat.strong_induction_on generalizing i with
  | h t ih =>
    by_cases ht0 : t = 0
    · subst ht0; simpa using hmin i
    · by_cases hlt : t ≤ 1 + C.k i
      · rw [C.f_step_partial i (by omega) hlt]
        have hpow : 1 ≤ 2 ^ (1 + C.k i - t) := Nat.one_le_pow _ _ (by omega)
        have hnext := hmin (finNext C.hm i)
        calc X ≤ 1 * C.x (finNext C.hm i) := by simpa using hnext
          _ ≤ 2 ^ (1 + C.k i - t) * C.x (finNext C.hm i) := Nat.mul_le_mul_right _ hpow
      · have hgt : 1 + C.k i < t := by omega
        have hsub : t = (t - (1 + C.k i)) + (1 + C.k i) := by omega
        rw [hsub, Function.iterate_add_apply, C.f_step i]; exact ih (t - (1 + C.k i)) (by omega) (finNext C.hm i)
/-- Cumulative step count after `r` odd steps starting from index `i`. -/
private def blockSteps (C : OddCycle m) (i : Fin m) : ℕ → ℕ
  | 0 => 0
  | r + 1 => blockSteps C i r + (1 + C.k (finAdd C.hm i r))
private lemma f_blockSteps (i : Fin m) (r : ℕ) : f^[blockSteps C i r] (C.x i) = C.x (finAdd C.hm i r) := by
  induction r with
  | zero => simp [blockSteps, finAdd_zero]
  | succ r ih =>
    simp only [blockSteps]
    rw [Nat.add_comm (blockSteps C i r), Function.iterate_add_apply, ih, C.f_step, finAdd_succ]
private lemma blockSteps_eq_sum (i : Fin m) (r : ℕ) :
    blockSteps C i r = ∑ j ∈ Finset.range r, (1 + C.k (finAdd C.hm i j)) := by
  induction r with
  | zero => simp [blockSteps]
  | succ r ih => simp [blockSteps, Finset.sum_range_succ, ih]
private lemma blockSteps_full (i : Fin m) : blockSteps C i m = C.totalHalvings + m := by
  rw [C.blockSteps_eq_sum]
  have hbi : ∑ j ∈ Finset.range m, (1 + C.k (finAdd C.hm i j)) =
      ∑ j : Fin m, (1 + C.k (finAdd C.hm i j.val)) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => 1 + C.k (finAdd C.hm i j)) m]
  rw [hbi]
  let e : Fin m ≃ Fin m :=
    { toFun := fun j => finAdd C.hm i j.val
      invFun := fun j => ⟨(j.val + m - i.val) % m, Nat.mod_lt _ C.hm⟩
      left_inv := fun j => by
        apply Fin.ext; change ((i.val + j.val) % m + m - i.val) % m = j.val; have hi := i.isLt; have hj := j.isLt
        have hlt : (i.val + j.val) % m < m := Nat.mod_lt _ C.hm
        have h1 : (i.val + j.val) % m + m - i.val = (i.val + j.val) % m + (m - i.val) := by omega
        rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have h2 : i.val + j.val + (m - i.val) = j.val + m := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
      right_inv := fun j => by
        apply Fin.ext; change (i.val + (j.val + m - i.val) % m) % m = j.val; have hi := i.isLt; have hj := j.isLt
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; have h2 : i.val + (j.val + m - i.val) = j.val + m := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hj] }
  have hsum := Fintype.sum_equiv e (fun j => 1 + C.k (finAdd C.hm i j.val))
    (fun j => 1 + C.k j) (fun _ => rfl)
  rw [hsum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, totalHalvings, Nat.add_comm]
/-- Every odd member `x_i` of `C` is periodic under `f` with exact period `K + m`. -/
theorem f_periodic (i : Fin m) : f^[C.totalHalvings + m] (C.x i) = C.x i := by
  rw [← C.blockSteps_full i, C.f_blockSteps i m, finAdd_self]
/-- Every odd member `x_i` reaches every odd member `x_j` under `f`. -/
theorem reaches_any (i j : Fin m) : Reaches f (C.x i) (C.x j) := by
  let r := (j.val + m - i.val) % m
  refine ⟨blockSteps C i r, ?_⟩
  rw [C.f_blockSteps]; congr 1
  apply Fin.ext; change (i.val + (j.val + m - i.val) % m) % m = j.val; have hi := i.isLt; have hj := j.isLt
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; have h2 : i.val + (j.val + m - i.val) = j.val + m := by omega
  rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hj]

end OddCycle

/-! ## Section 2: Exact multiplicative loop product identity and logarithmic sandwich -/
/-- Exact multiplicative loop product identity in `ℕ`: `∏ (d(x_i) * x_i + 1) = 2^K * ∏ x_i`. -/
theorem cycle_prod_eq_nat {m : ℕ} (C : OddCycle m) :
    ∏ i : Fin m, (d (C.x i) * C.x i + 1) =
      2 ^ C.totalHalvings * ∏ i : Fin m, C.x i := by
  calc ∏ i : Fin m, (d (C.x i) * C.x i + 1)
      = ∏ i : Fin m, (2 ^ C.k i * C.x (finNext C.hm i)) := by refine Finset.prod_congr rfl (fun i _ => C.step i)
    _ = (∏ i : Fin m, 2 ^ C.k i) * (∏ i : Fin m, C.x (finNext C.hm i)) := Finset.prod_mul_distrib
    _ = 2 ^ (∑ i : Fin m, C.k i) * (∏ i : Fin m, C.x i) := by
          rw [Finset.prod_pow_eq_pow_sum]; congr 1
          exact Fintype.prod_equiv (finNextEquiv C.hm)
            (fun i => C.x (finNext C.hm i)) (fun i => C.x i) (fun _ => rfl)
/-- Every odd step has at least one halving, so `m ≤ K`. -/
theorem cycle_m_le_totalHalvings {m : ℕ} (C : OddCycle m) : m ≤ C.totalHalvings := by
  calc m = ∑ _i : Fin m, (1 : ℕ) := by simp
    _ ≤ ∑ i : Fin m, C.k i := Finset.sum_le_sum (fun i _ => C.k_pos i)
/-- The five odd-digit counts partition `m`: `n1 + n3 + n5 + n7 + n9 = m`. -/
theorem cycle_digit_counts_sum {m : ℕ} (C : OddCycle m) : C.n1 + C.n3 + C.n5 + C.n7 + C.n9 = m := by
  have hpart : ∀ i : Fin m,
      (if d (C.x i) = 1 then 1 else 0) +
      (if d (C.x i) = 3 then 1 else 0) +
      (if d (C.x i) = 5 then 1 else 0) +
      (if d (C.x i) = 7 then 1 else 0) +
      (if d (C.x i) = 9 then 1 else 0) = 1 := by
    intro i
    rcases C.d_mem i with h | h | h | h | h <;> simp [h]
  have hsum : ∑ i : Fin m, ((if d (C.x i) = 1 then 1 else 0) +
      (if d (C.x i) = 3 then 1 else 0) +
      (if d (C.x i) = 5 then 1 else 0) +
      (if d (C.x i) = 7 then 1 else 0) +
      (if d (C.x i) = 9 then 1 else 0)) = m := by
    simp [hpart]
  simp only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] at hsum; exact hsum
/-- Exact factorization of the digit product `D = 3^(n3 + 2*n9) * 5^n5 * 7^n7`. -/
theorem cycle_digitProd_factorization {m : ℕ} (C : OddCycle m) :
    C.digitProd = 3 ^ C.aExp * 5 ^ C.bExp * 7 ^ C.cExp := by
  have hfac : ∀ i : Fin m,
      d (C.x i) =
        3 ^ ((if d (C.x i) = 3 then 1 else 0) + 2 * (if d (C.x i) = 9 then 1 else 0)) *
        5 ^ (if d (C.x i) = 5 then 1 else 0) *
        7 ^ (if d (C.x i) = 7 then 1 else 0) := by
    intro i
    rcases C.d_mem i with h | h | h | h | h <;> simp [h]
  unfold OddCycle.digitProd OddCycle.aExp OddCycle.bExp OddCycle.cExp
  unfold OddCycle.n3 OddCycle.n5 OddCycle.n7 OddCycle.n9 OddCycle.countDigit
  calc ∏ i : Fin m, d (C.x i)
      = ∏ i : Fin m,
          (3 ^ ((if d (C.x i) = 3 then 1 else 0) + 2 * (if d (C.x i) = 9 then 1 else 0)) *
           5 ^ (if d (C.x i) = 5 then 1 else 0) *
           7 ^ (if d (C.x i) = 7 then 1 else 0)) :=
        Finset.prod_congr rfl (fun i _ => hfac i)
    _ = (∏ i : Fin m, 3 ^ ((if d (C.x i) = 3 then 1 else 0) +
            2 * (if d (C.x i) = 9 then 1 else 0))) *
        (∏ i : Fin m, 5 ^ (if d (C.x i) = 5 then 1 else 0)) *
        (∏ i : Fin m, 7 ^ (if d (C.x i) = 7 then 1 else 0)) := by
        simp only [Finset.prod_mul_distrib]
    _ = 3 ^ (∑ i : Fin m, ((if d (C.x i) = 3 then 1 else 0) +
            2 * (if d (C.x i) = 9 then 1 else 0))) *
        5 ^ (∑ i : Fin m, (if d (C.x i) = 5 then 1 else 0)) *
        7 ^ (∑ i : Fin m, (if d (C.x i) = 7 then 1 else 0)) := by
        simp only [Finset.prod_pow_eq_pow_sum]
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Nat.cast_id]
/-- Strict inequality `D < 2^K` for every odd cycle. -/
theorem cycle_digitProd_lt_two_pow {m : ℕ} (C : OddCycle m) : C.digitProd < 2 ^ C.totalHalvings := by
  have hprod := cycle_prod_eq_nat C
  have hlt : C.digitProd * ∏ i : Fin m, C.x i < ∏ i : Fin m, (d (C.x i) * C.x i + 1) := by
    rw [OddCycle.digitProd, ← Finset.prod_mul_distrib]; have i0 : Fin m := ⟨0, C.hm⟩
    rw [← Finset.mul_prod_erase Finset.univ (fun j => d (C.x j) * C.x j) (Finset.mem_univ i0),
      ← Finset.mul_prod_erase Finset.univ (fun j => d (C.x j) * C.x j + 1) (Finset.mem_univ i0)]
    have hrest_pos : 0 < ∏ j ∈ Finset.univ.erase i0, (d (C.x j) * C.x j + 1) :=
      Finset.prod_pos (fun j _ => by positivity)
    have hrest_le : ∏ j ∈ Finset.univ.erase i0, (d (C.x j) * C.x j) ≤
        ∏ j ∈ Finset.univ.erase i0, (d (C.x j) * C.x j + 1) :=
      Finset.prod_le_prod (fun _ _ => Nat.le_succ _)
    have hlt0 : d (C.x i0) * C.x i0 < d (C.x i0) * C.x i0 + 1 := Nat.lt_succ_self _
    calc (d (C.x i0) * C.x i0) * ∏ j ∈ Finset.univ.erase i0, (d (C.x j) * C.x j)
        ≤ (d (C.x i0) * C.x i0) * ∏ j ∈ Finset.univ.erase i0, (d (C.x j) * C.x j + 1) :=
          Nat.mul_le_mul_left _ hrest_le
      _ < (d (C.x i0) * C.x i0 + 1) * ∏ j ∈ Finset.univ.erase i0, (d (C.x j) * C.x j + 1) :=
          Nat.mul_lt_mul_of_pos_right hlt0 hrest_pos
  rw [hprod] at hlt; exact Nat.lt_of_mul_lt_mul_right hlt
/-- Purely arithmetic characterization of all-digit-1 cycles: `D = 1` if and only if `x_i = 1` and `k_i = 1` for -/
theorem cycle_all_ones_iff {m : ℕ} (C : OddCycle m) : C.digitProd = 1 ↔ ∀ i : Fin m, C.x i = 1 ∧ C.k i = 1 := by
  constructor
  · intro hD
    have hd1 : ∀ i : Fin m, d (C.x i) = 1 := by
      intro i
      by_contra hne
      have hge2 : 2 ≤ d (C.x i) := by
        rcases C.d_mem i with h | h | h | h | h <;> omega
      have hle : d (C.x i) ≤ C.digitProd := by
        have hmem : i ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ i
        have hsplit := Finset.mul_prod_erase Finset.univ (fun j => d (C.x j)) hmem
        have hpos : 1 ≤ ∏ j ∈ Finset.univ.erase i, d (C.x j) :=
          Nat.succ_le_of_lt (Finset.prod_pos (fun j _ => C.d_pos j))
        calc d (C.x i) = d (C.x i) * 1 := (mul_one _).symm
          _ ≤ d (C.x i) * ∏ j ∈ Finset.univ.erase i, d (C.x j) := Nat.mul_le_mul_left _ hpos
          _ = C.digitProd := hsplit
      omega
    have hprod := cycle_prod_eq_nat C
    have hle1 : ∏ i : Fin m, (d (C.x i) * C.x i + 1) ≤ ∏ i : Fin m, (2 * C.x i) := by
      refine Finset.prod_le_prod (fun i _ => ?_)
      rw [hd1 i, one_mul]
      have := C.x_pos i; omega
    have hle2 : ∏ i : Fin m, (2 * C.x i) = 2 ^ m * ∏ i : Fin m, C.x i := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hle3 : 2 ^ m ≤ 2 ^ C.totalHalvings := Nat.pow_le_pow_right (by omega) (cycle_m_le_totalHalvings C)
    have hpx_pos : 0 < ∏ i : Fin m, C.x i := Finset.prod_pos (fun i _ => C.x_pos i)
    have hEq_all : ∏ i : Fin m, (d (C.x i) * C.x i + 1) = ∏ i : Fin m, (2 * C.x i) := by
      have : 2 ^ m * ∏ i : Fin m, C.x i ≤ 2 ^ C.totalHalvings * ∏ i : Fin m, C.x i := Nat.mul_le_mul_right _ hle3
      omega
    have hEq_K : C.totalHalvings = m := by
      have h2eq : 2 ^ C.totalHalvings * ∏ i : Fin m, C.x i = 2 ^ m * ∏ i : Fin m, C.x i := by
        rw [← hprod, hEq_all, hle2]
      have hpow : 2 ^ C.totalHalvings = 2 ^ m := Nat.eq_of_mul_eq_mul_right hpx_pos h2eq
      exact Nat.pow_right_injective (by omega) hpow
    intro i
    have hx1 : C.x i = 1 := by
      by_contra hne
      have hlt_i : d (C.x i) * C.x i + 1 < 2 * C.x i := by rw [hd1 i, one_mul]; have := C.x_pos i; omega
      have hstrict : ∏ j : Fin m, (d (C.x j) * C.x j + 1) < ∏ j : Fin m, (2 * C.x j) := by
        rw [← Finset.mul_prod_erase Finset.univ (fun j => d (C.x j) * C.x j + 1) (Finset.mem_univ i),
          ← Finset.mul_prod_erase Finset.univ (fun j => 2 * C.x j) (Finset.mem_univ i)]
        have hrest_pos : 0 < ∏ j ∈ Finset.univ.erase i, (2 * C.x j) :=
          Finset.prod_pos (fun j _ => by have := C.x_pos j; omega)
        have hrest_le : ∏ j ∈ Finset.univ.erase i, (d (C.x j) * C.x j + 1) ≤
            ∏ j ∈ Finset.univ.erase i, (2 * C.x j) := by
          refine Finset.prod_le_prod (fun j _ => ?_)
          rw [hd1 j, one_mul]; have := C.x_pos j; omega
        calc (d (C.x i) * C.x i + 1) * ∏ j ∈ Finset.univ.erase i, (d (C.x j) * C.x j + 1)
            ≤ (d (C.x i) * C.x i + 1) * ∏ j ∈ Finset.univ.erase i, (2 * C.x j) := Nat.mul_le_mul_left _ hrest_le
          _ < (2 * C.x i) * ∏ j ∈ Finset.univ.erase i, (2 * C.x j) := Nat.mul_lt_mul_of_pos_right hlt_i hrest_pos
      omega
    have hk1 : C.k i = 1 := by
      by_contra hne
      have hgt_i : 1 < C.k i := by have := C.k_pos i; omega
      have hstrict : m < C.totalHalvings := by
        calc m = ∑ _j : Fin m, (1 : ℕ) := by simp
          _ < ∑ j : Fin m, C.k j := Finset.sum_lt_sum (fun j _ => C.k_pos j) ⟨i, Finset.mem_univ i, hgt_i⟩
      omega
    exact ⟨hx1, hk1⟩
  · intro h; unfold OddCycle.digitProd
    refine Finset.prod_eq_one (fun i _ => ?_)
    rw [(h i).1]; decide
/-- Exact real multiplicative cycle identity: `2^K = D * ∏ (1 + 1 / (d(x_i) * x_i))`. -/
theorem cycle_real_prod_eq {m : ℕ} (C : OddCycle m) :
    (2 : ℝ) ^ C.totalHalvings =
      (C.digitProd : ℝ) * ∏ i : Fin m, (1 + (1 : ℝ) / ((d (C.x i) : ℝ) * (C.x i : ℝ))) := by
  have hnat : ((∏ i : Fin m, (d (C.x i) * C.x i + 1) : ℕ) : ℝ) =
      ((2 ^ C.totalHalvings * ∏ i : Fin m, C.x i : ℕ) : ℝ) :=
    congrArg (Nat.cast (R := ℝ)) (cycle_prod_eq_nat C)
  have hpx_ne : (∏ i : Fin m, (C.x i : ℝ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun i _ => ?_)
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (C.x_pos i))
  have hstep : ∏ i : Fin m, ((d (C.x i) : ℝ) * (C.x i : ℝ) + 1) =
      (∏ i : Fin m, (d (C.x i) : ℝ)) * (∏ i : Fin m, (C.x i : ℝ)) *
      ∏ i : Fin m, (1 + (1 : ℝ) / ((d (C.x i) : ℝ) * (C.x i : ℝ))) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hd_ne : (d (C.x i) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (C.d_pos i))
    have hx_ne : (C.x i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (C.x_pos i))
    field_simp
  push_cast at hnat; rw [hstep] at hnat
  have hD : (C.digitProd : ℝ) = ∏ i : Fin m, (d (C.x i) : ℝ) := by unfold OddCycle.digitProd; push_cast; rfl
  rw [hD]
  have hmul : ((∏ i : Fin m, (d (C.x i) : ℝ)) *
      ∏ i : Fin m, (1 + (1 : ℝ) / ((d (C.x i) : ℝ) * (C.x i : ℝ)))) *
      (∏ i : Fin m, (C.x i : ℝ)) =
      (2 : ℝ) ^ C.totalHalvings * (∏ i : Fin m, (C.x i : ℝ)) := by
    linarith
  exact (mul_right_cancel₀ hpx_ne hmul).symm
/-- Exact logarithmic cycle sandwich (Paper 1 Section 3 and Paper 2 Eq. `eq:cycle-chain`): -/
theorem cycle_log_sandwich {m : ℕ} (C : OddCycle m) {X : ℕ}
    (hX : 1 ≤ X) (hmin : ∀ i : Fin m, X ≤ C.x i) :
    0 < (C.totalHalvings : ℝ) * Real.log 2 - Real.log (C.digitProd : ℝ) ∧
    (C.totalHalvings : ℝ) * Real.log 2 - Real.log (C.digitProd : ℝ) <
      ∑ i : Fin m, (1 : ℝ) / ((d (C.x i) : ℝ) * (C.x i : ℝ)) ∧
    ∑ i : Fin m, (1 : ℝ) / ((d (C.x i) : ℝ) * (C.x i : ℝ)) ≤
      ((C.n1 : ℝ) + (C.n3 : ℝ) / 3 + (C.n5 : ℝ) / 5 + (C.n7 : ℝ) / 7 + (C.n9 : ℝ) / 9) /
        (X : ℝ) ∧
    ((C.n1 : ℝ) + (C.n3 : ℝ) / 3 + (C.n5 : ℝ) / 5 + (C.n7 : ℝ) / 7 + (C.n9 : ℝ) / 9) /
        (X : ℝ) ≤ (m : ℝ) / (X : ℝ) ∧
    (m : ℝ) / (X : ℝ) ≤ (C.totalHalvings : ℝ) / (X : ℝ) := by
  have hD_pos : (0 : ℝ) < (C.digitProd : ℝ) := Nat.cast_pos.mpr C.digitProd_pos
  have hX_pos : (0 : ℝ) < (X : ℝ) := Nat.cast_pos.mpr (by omega)
  have hterm_pos : ∀ i : Fin m,
      (0 : ℝ) < 1 + (1 : ℝ) / ((d (C.x i) : ℝ) * (C.x i : ℝ)) := by
    intro i
    have hd : (0 : ℝ) < (d (C.x i) : ℝ) := Nat.cast_pos.mpr (C.d_pos i)
    have hx : (0 : ℝ) < (C.x i : ℝ) := Nat.cast_pos.mpr (C.x_pos i)
    positivity
  have hlog_eq : (C.totalHalvings : ℝ) * Real.log 2 - Real.log (C.digitProd : ℝ) =
      ∑ i : Fin m, Real.log (1 + (1 : ℝ) / ((d (C.x i) : ℝ) * (C.x i : ℝ))) := by
    have h1 := congrArg Real.log (cycle_real_prod_eq C); rw [Real.log_pow] at h1
    have hprod_ne : (∏ i : Fin m, (1 + (1 : ℝ) / ((d (C.x i) : ℝ) * (C.x i : ℝ)))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (hterm_pos i))
    rw [Real.log_mul (ne_of_gt hD_pos) hprod_ne,
      Real.log_prod (fun i _ => ne_of_gt (hterm_pos i))] at h1
    linarith
  have hpos : 0 < (C.totalHalvings : ℝ) * Real.log 2 - Real.log (C.digitProd : ℝ) := by
    rw [hlog_eq]; have i0 : Fin m := ⟨0, C.hm⟩
    refine Finset.sum_pos (fun i _ => ?_) ⟨i0, Finset.mem_univ i0⟩
    refine Real.log_pos ?_
    have hd : (0 : ℝ) < (d (C.x i) : ℝ) := Nat.cast_pos.mpr (C.d_pos i)
    have hx : (0 : ℝ) < (C.x i : ℝ) := Nat.cast_pos.mpr (C.x_pos i)
    have : (0 : ℝ) < 1 / ((d (C.x i) : ℝ) * (C.x i : ℝ)) := by positivity
    linarith
  have hlt : (C.totalHalvings : ℝ) * Real.log 2 - Real.log (C.digitProd : ℝ) <
      ∑ i : Fin m, (1 : ℝ) / ((d (C.x i) : ℝ) * (C.x i : ℝ)) := by
    rw [hlog_eq]; have i0 : Fin m := ⟨0, C.hm⟩
    refine Finset.sum_lt_sum_of_nonempty ⟨i0, Finset.mem_univ i0⟩ (fun i _ => ?_)
    have hd : (0 : ℝ) < (d (C.x i) : ℝ) := Nat.cast_pos.mpr (C.d_pos i)
    have hx : (0 : ℝ) < (C.x i : ℝ) := Nat.cast_pos.mpr (C.x_pos i)
    have hne : (1 : ℝ) + 1 / ((d (C.x i) : ℝ) * (C.x i : ℝ)) ≠ 1 := by
      have : (0 : ℝ) < 1 / ((d (C.x i) : ℝ) * (C.x i : ℝ)) := by positivity
      linarith
    have hloglt := Real.log_lt_sub_one_of_pos (hterm_pos i) hne; linarith
  have hsum_d : ∑ i : Fin m, (1 : ℝ) / (d (C.x i) : ℝ) =
      (C.n1 : ℝ) + (C.n3 : ℝ) / 3 + (C.n5 : ℝ) / 5 + (C.n7 : ℝ) / 7 + (C.n9 : ℝ) / 9 := by
    have hitem : ∀ i : Fin m, (1 : ℝ) / (d (C.x i) : ℝ) =
        (if d (C.x i) = 1 then (1 : ℝ) else 0) +
        (if d (C.x i) = 3 then (1 : ℝ) / 3 else 0) +
        (if d (C.x i) = 5 then (1 : ℝ) / 5 else 0) +
        (if d (C.x i) = 7 then (1 : ℝ) / 7 else 0) +
        (if d (C.x i) = 9 then (1 : ℝ) / 9 else 0) := by
      intro i
      rcases C.d_mem i with h | h | h | h | h <;> simp [h]
    simp_rw [hitem]
    simp only [Finset.sum_add_distrib]
    have hcnt : ∀ (dig : ℕ) (c : ℝ),
        ∑ i : Fin m, (if d (C.x i) = dig then c else 0) = (C.countDigit dig : ℝ) * c := by
      intro dig c; simp [OddCycle.countDigit, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
    rw [hcnt 1 1, hcnt 3 (1 / 3), hcnt 5 (1 / 5), hcnt 7 (1 / 7), hcnt 9 (1 / 9)]
    unfold OddCycle.n1 OddCycle.n3 OddCycle.n5 OddCycle.n7 OddCycle.n9; ring
  have hbound1 : ∑ i : Fin m, (1 : ℝ) / ((d (C.x i) : ℝ) * (C.x i : ℝ)) ≤
      ((C.n1 : ℝ) + (C.n3 : ℝ) / 3 + (C.n5 : ℝ) / 5 + (C.n7 : ℝ) / 7 + (C.n9 : ℝ) / 9) /
        (X : ℝ) := by
    rw [← hsum_d, Finset.sum_div]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hd : (0 : ℝ) < (d (C.x i) : ℝ) := Nat.cast_pos.mpr (C.d_pos i)
    have hx : (X : ℝ) ≤ (C.x i : ℝ) := Nat.cast_le.mpr (hmin i)
    rw [div_div]; exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hx (le_of_lt hd))
  have hbound2 : ((C.n1 : ℝ) + (C.n3 : ℝ) / 3 + (C.n5 : ℝ) / 5 + (C.n7 : ℝ) / 7 +
      (C.n9 : ℝ) / 9) / (X : ℝ) ≤ (m : ℝ) / (X : ℝ) := by
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hX_pos)
    have hm_sum : (C.n1 : ℝ) + C.n3 + C.n5 + C.n7 + C.n9 = (m : ℝ) := by exact_mod_cast cycle_digit_counts_sum C
    have hn3 : (0 : ℝ) ≤ C.n3 := Nat.cast_nonneg _
    have hn5 : (0 : ℝ) ≤ C.n5 := Nat.cast_nonneg _
    have hn7 : (0 : ℝ) ≤ C.n7 := Nat.cast_nonneg _
    have hn9 : (0 : ℝ) ≤ C.n9 := Nat.cast_nonneg _
    linarith
  have hbound3 : (m : ℝ) / (X : ℝ) ≤ (C.totalHalvings : ℝ) / (X : ℝ) :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr (cycle_m_le_totalHalvings C)) (le_of_lt hX_pos)
  exact ⟨hpos, hlt, hbound1, hbound2, hbound3⟩
/-- When `∀ i, X ≤ x_i` (`X ≥ 2`) and `2 * K ≤ X`, `D > 1` and `K` is forced to be the exact bit length of `D`: -/
theorem cycle_bit_length_forced {m : ℕ} (C : OddCycle m) {X : ℕ}
    (hX : 2 ≤ X) (hmin : ∀ i : Fin m, X ≤ C.x i) (hK : 2 * C.totalHalvings ≤ X) :
    1 < C.digitProd ∧ 2 ^ (C.totalHalvings - 1) < C.digitProd ∧
      C.digitProd < 2 ^ C.totalHalvings := by
  have hD_gt1 : 1 < C.digitProd := by
    have hpos := C.digitProd_pos
    by_contra hle
    have hD1 : C.digitProd = 1 := by omega
    have hall := (cycle_all_ones_iff C).mp hD1; have h0 := hall ⟨0, C.hm⟩; have hm0 := hmin ⟨0, C.hm⟩; omega
  have hD_lt := cycle_digitProd_lt_two_pow C; have hs := cycle_log_sandwich C (by omega) hmin
  have hgap_lt : (C.totalHalvings : ℝ) * Real.log 2 - Real.log (C.digitProd : ℝ) <
      (C.totalHalvings : ℝ) / (X : ℝ) := by linarith
  have hKX : (C.totalHalvings : ℝ) / (X : ℝ) ≤ 1 / 2 := by
    have hX_pos : (0 : ℝ) < (X : ℝ) := Nat.cast_pos.mpr (by omega)
    rw [div_le_div_iff₀ hX_pos (by norm_num : (0 : ℝ) < 2)]
    have : (2 * C.totalHalvings : ℝ) ≤ (X : ℝ) := by exact_mod_cast hK
    linarith
  have hln2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hK1 : 1 ≤ C.totalHalvings := le_trans C.hm (cycle_m_le_totalHalvings C)
  have hlog_lt : Real.log ((2 ^ (C.totalHalvings - 1) : ℕ) : ℝ) < Real.log (C.digitProd : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_sub hK1, Nat.cast_one]; linarith
  have hpow_lt_real : ((2 ^ (C.totalHalvings - 1) : ℕ) : ℝ) < (C.digitProd : ℝ) := by
    have h1 : (0 : ℝ) < ((2 ^ (C.totalHalvings - 1) : ℕ) : ℝ) := by positivity
    have h2 : (0 : ℝ) < (C.digitProd : ℝ) := Nat.cast_pos.mpr C.digitProd_pos
    exact (Real.log_lt_log_iff h1 h2).mp hlog_lt
  exact ⟨hD_gt1, Nat.cast_lt.mp hpow_lt_real, hD_lt⟩

/-! ## Section 3: Paper 2 Lemma `lem:halving-budget` -/
private lemma two_pow_mod_five_cycle (v : ℕ) :
    (v % 4 = 0 → 2 ^ v % 5 = 1) ∧
    (v % 4 = 1 → 2 ^ v % 5 = 2) ∧
    (v % 4 = 2 → 2 ^ v % 5 = 4) ∧
    (v % 4 = 3 → 2 ^ v % 5 = 3) := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [pow_succ, Nat.mul_mod]
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [ih.2.2.2 (by omega)]
    · rw [ih.1 (by omega)]
    · rw [ih.2.1 (by omega)]
    · rw [ih.2.2.1 (by omega)]
/-- Paper 2 Lemma `lem:halving-budget`(1): exact modulo-5 transition table for consecutive odd iterates -/
theorem lem_last_digit_transition {n n' v : ℕ}
    (hn : n % 2 = 1) (hn' : n' % 2 = 1) (_hv : 1 ≤ v)
    (heq : d n * n + 1 = 2 ^ v * n') :
    ((d n = 1 ∨ d n = 9) →
      (d n' = 1 ↔ v % 4 = 1) ∧
      (d n' = 3 ↔ v % 4 = 2) ∧
      (d n' = 9 ↔ v % 4 = 3) ∧
      (d n' = 7 ↔ v % 4 = 0) ∧
      d n' ≠ 5) ∧
    (d n = 5 →
      (d n' = 1 ↔ v % 4 = 0) ∧
      (d n' = 3 ↔ v % 4 = 1) ∧
      (d n' = 9 ↔ v % 4 = 2) ∧
      (d n' = 7 ↔ v % 4 = 3) ∧
      d n' ≠ 5) ∧
    ((d n = 3 ∨ d n = 7) → d n' = 5) := by
  have h25 := two_pow_mod_five_cycle v; have hd_n : d n % 5 = n % 5 := by unfold d; omega
  have hd_n' : d n' % 5 = n' % 5 := by unfold d; omega
  have hn'_cases : d n' = 1 ∨ d n' = 3 ∨ d n' = 5 ∨ d n' = 7 ∨ d n' = 9 := by unfold d; omega
  have hmod5 : (d n * (n % 5) + 1) % 5 = ((2 ^ v % 5) * (n' % 5)) % 5 := by
    have h1 : (d n * n + 1) % 5 = (2 ^ v * n') % 5 := congrArg (· % 5) heq
    rw [Nat.add_mod, Nat.mul_mod (d n) n 5, Nat.mul_mod (2 ^ v) n' 5] at h1
    rw [Nat.add_mod, Nat.mul_mod (d n) (n % 5) 5, Nat.mod_mod]; exact h1
  have hv4 : v % 4 = 0 ∨ v % 4 = 1 ∨ v % 4 = 2 ∨ v % 4 = 3 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro h19
    have hlhs : (d n * (n % 5) + 1) % 5 = 2 := by
      rcases h19 with h | h <;> (rw [h] at hd_n ⊢; omega)
    rw [hlhs] at hmod5
    rcases hv4 with h | h | h | h <;> [rw [h25.1 h] at hmod5; rw [h25.2.1 h] at hmod5;
      rw [h25.2.2.1 h] at hmod5; rw [h25.2.2.2 h] at hmod5] <;>
    rcases hn'_cases with hd' | hd' | hd' | hd' | hd' <;>
    (rw [hd'] at hd_n' ⊢; omega)
  · intro h5; have hlhs : (d n * (n % 5) + 1) % 5 = 1 := by rw [h5] at hd_n ⊢; omega
    rw [hlhs] at hmod5
    rcases hv4 with h | h | h | h <;> [rw [h25.1 h] at hmod5; rw [h25.2.1 h] at hmod5;
      rw [h25.2.2.1 h] at hmod5; rw [h25.2.2.2 h] at hmod5] <;>
    rcases hn'_cases with hd' | hd' | hd' | hd' | hd' <;>
    (rw [hd'] at hd_n' ⊢; omega)
  · intro h37; have h5 := (lemma_after_3_or_7_is_5 hn hn' heq).mpr; exact h5 (by unfold d at h37; exact h37)
/-- Conservation law for every base-10 cycle: `n_5 = n_3 + n_7`. -/
theorem cycle_n5_eq_n3_add_n7 {m : ℕ} (C : OddCycle m) : C.n5 = C.n3 + C.n7 := by
  have hbij : C.n5 = (Finset.univ.filter (fun i : Fin m =>
      d (C.x (finNext C.hm i)) = 5)).card := by
    unfold OddCycle.n5 OddCycle.countDigit; simp only [Finset.card_filter]
    exact (Fintype.sum_equiv (finNextEquiv C.hm)
      (fun i => if d (C.x (finNext C.hm i)) = 5 then 1 else 0)
      (fun i => if d (C.x i) = 5 then 1 else 0)
      (fun _ => rfl)).symm
  rw [hbij]
  have hiff : ∀ i : Fin m,
      (d (C.x (finNext C.hm i)) = 5) ↔ (d (C.x i) = 3 ∨ d (C.x i) = 7) := fun i =>
    lemma_after_3_or_7_is_5 (C.x_odd i) (C.x_odd (finNext C.hm i)) (C.step i)
  have hfilt : Finset.univ.filter (fun i : Fin m => d (C.x (finNext C.hm i)) = 5) =
      Finset.univ.filter (fun i : Fin m => d (C.x i) = 3) ∪
      Finset.univ.filter (fun i : Fin m => d (C.x i) = 7) := by
    ext i; simp [hiff i]
  rw [hfilt, Finset.card_union_of_disjoint]
  · rfl
  · rw [Finset.disjoint_filter]; intro i _ h3 h7; omega
/-- Exact digit-count parity obstruction (Paper 1 Section 3 / `cycle-bound` test 3 / Paper 2 Lemma -/
theorem cycle_digit_parity {m : ℕ} (C : OddCycle m) :
    C.cExp ≤ C.bExp ∧ C.bExp - C.cExp ≤ C.aExp ∧
      C.aExp + C.cExp = C.bExp + 2 * C.n9 ∧
      ((C.aExp : ℤ) - (C.bExp : ℤ) + (C.cExp : ℤ)) % 2 = 0 := by
  have h5 := cycle_n5_eq_n3_add_n7 C; unfold OddCycle.aExp OddCycle.bExp OddCycle.cExp
  refine ⟨by omega, by omega, by omega, ?_⟩
  have hz : (C.n3 + 2 * C.n9 : ℤ) - (C.n5 : ℤ) + (C.n7 : ℤ) = 2 * (C.n9 : ℤ) := by
    have : (C.n5 : ℤ) = (C.n3 : ℤ) + (C.n7 : ℤ) := by exact_mod_cast h5
    linarith
  push_cast; rw [hz]; omega
/-- No `5` is followed by a `5`, so `2 * n_5 ≤ m`. -/
theorem cycle_no_five_to_five {m : ℕ} (C : OddCycle m) : C.countTrans 5 5 = 0 ∧ 2 * C.n5 ≤ m := by
  have h0 : C.countTrans 5 5 = 0 := by
    unfold OddCycle.countTrans; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro i _ ⟨h5, h5'⟩
    have htr := (lem_last_digit_transition (C.x_odd i) (C.x_odd (finNext C.hm i))
      (C.k_pos i) (C.step i)).2.1 h5
    exact htr.2.2.2.2 h5'
  have h5 := cycle_n5_eq_n3_add_n7 C; have hsum := cycle_digit_counts_sum C; exact ⟨h0, by omega⟩
/-- Per-step base halving weight by incoming last digit. -/
private def inBaseWeight (dig : ℕ) : ℕ :=
  if dig = 1 then 1
  else if dig = 3 then 2
  else if dig = 9 then 3
  else if dig = 7 then 4
  else 0
/-- Paper 2 Lemma `lem:halving-budget`(2), sharp form with `+ 4 * t_{5,1}`: -/
theorem lem_halving_budget_sharp {m : ℕ} (C : OddCycle m) :
    C.n1 + 2 * C.n3 + 4 * C.n7 + 3 * C.n9 + 4 * C.countTrans 5 1 ≤ C.totalHalvings := by
  have hstep_le : ∀ i : Fin m,
      inBaseWeight (d (C.x (finNext C.hm i))) +
      (if d (C.x (finNext C.hm i)) = 5 then 1 else 0) +
      4 * (if d (C.x i) = 5 ∧ d (C.x (finNext C.hm i)) = 1 then 1 else 0) ≤
      C.k i + (if d (C.x i) = 5 then 1 else 0) := by
    intro i
    have htr := lem_last_digit_transition (C.x_odd i) (C.x_odd (finNext C.hm i))
      (C.k_pos i) (C.step i)
    have hk := C.k_pos i
    rcases C.d_mem i with h1 | h3 | h5 | h7 | h9
    · have ht := htr.1 (Or.inl h1)
      rcases C.d_mem (finNext C.hm i) with h1' | h3' | h5' | h7' | h9'
      · have := ht.1.mp h1'; simp [inBaseWeight, h1, h1']; omega
      · have := ht.2.1.mp h3'; simp [inBaseWeight, h1, h3']; omega
      · exact absurd h5' ht.2.2.2.2
      · have := ht.2.2.2.1.mp h7'; simp [inBaseWeight, h1, h7']; omega
      · have := ht.2.2.1.mp h9'; simp [inBaseWeight, h1, h9']; omega
    · have h5' := htr.2.2 (Or.inl h3)
      simp [inBaseWeight, h3, h5']; omega
    · have ht := htr.2.1 h5
      rcases C.d_mem (finNext C.hm i) with h1' | h3' | h5' | h7' | h9'
      · have := ht.1.mp h1'; simp [inBaseWeight, h5, h1']; omega
      · have := ht.2.1.mp h3'; simp [inBaseWeight, h5, h3']; omega
      · exact absurd h5' ht.2.2.2.2
      · have := ht.2.2.2.1.mp h7'; simp [inBaseWeight, h5, h7']; omega
      · have := ht.2.2.1.mp h9'; simp [inBaseWeight, h5, h9']; omega
    · have h5' := htr.2.2 (Or.inr h7)
      simp [inBaseWeight, h7, h5']; omega
    · have ht := htr.1 (Or.inr h9)
      rcases C.d_mem (finNext C.hm i) with h1' | h3' | h5' | h7' | h9'
      · have := ht.1.mp h1'; simp [inBaseWeight, h9, h1']; omega
      · have := ht.2.1.mp h3'; simp [inBaseWeight, h9, h3']; omega
      · exact absurd h5' ht.2.2.2.2
      · have := ht.2.2.2.1.mp h7'; simp [inBaseWeight, h9, h7']; omega
      · have := ht.2.2.1.mp h9'; simp [inBaseWeight, h9, h9']; omega
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hstep_le i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hbase_eq : ∑ i : Fin m, inBaseWeight (d (C.x (finNext C.hm i))) =
      ∑ i : Fin m, inBaseWeight (d (C.x i)) :=
    Fintype.sum_equiv (finNextEquiv C.hm)
      (fun i => inBaseWeight (d (C.x (finNext C.hm i))))
      (fun i => inBaseWeight (d (C.x i))) (fun _ => rfl)
  have h5_eq : ∑ i : Fin m, (if d (C.x (finNext C.hm i)) = 5 then 1 else 0) =
      ∑ i : Fin m, (if d (C.x i) = 5 then 1 else 0) :=
    Fintype.sum_equiv (finNextEquiv C.hm)
      (fun i => if d (C.x (finNext C.hm i)) = 5 then 1 else 0)
      (fun i => if d (C.x i) = 5 then 1 else 0) (fun _ => rfl)
  have hbase_expand : ∑ i : Fin m, inBaseWeight (d (C.x i)) =
      C.n1 + 2 * C.n3 + 4 * C.n7 + 3 * C.n9 := by
    have hpt : ∀ i : Fin m, inBaseWeight (d (C.x i)) =
        (if d (C.x i) = 1 then 1 else 0) +
        2 * (if d (C.x i) = 3 then 1 else 0) +
        4 * (if d (C.x i) = 7 then 1 else 0) +
        3 * (if d (C.x i) = 9 then 1 else 0) := by
      intro i; rcases C.d_mem i with h | h | h | h | h <;> simp [inBaseWeight, h]
    simp_rw [hpt]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Nat.cast_id]; rfl
  have ht51 : ∑ i : Fin m, (if d (C.x i) = 5 ∧ d (C.x (finNext C.hm i)) = 1 then 1 else 0) =
      C.countTrans 5 1 := by
    simp [OddCycle.countTrans]
  rw [hbase_eq, hbase_expand, h5_eq, ht51] at hsum
  unfold OddCycle.totalHalvings; omega
/-- Paper 2 Lemma `lem:halving-budget`(2): `K ≥ n1 + 2*n3 + 4*n7 + 3*n9`, equivalently -/
theorem lem_halving_budget {m : ℕ} (C : OddCycle m) :
    C.n1 + 2 * C.n3 + 4 * C.n7 + 3 * C.n9 ≤ C.totalHalvings ∧
      2 * C.n1 + 3 * C.aExp + C.bExp + 7 * C.cExp ≤ 2 * C.totalHalvings := by
  have hsharp := lem_halving_budget_sharp C; have h5 := cycle_n5_eq_n3_add_n7 C
  unfold OddCycle.aExp OddCycle.bExp OddCycle.cExp; exact ⟨by omega, by omega⟩

/-! ## Section 4: Minimum-element transfer from a finite descent sweep -/
/-- Discharges `1, 2, 3, 4, 5, 6` in kernel: every odd member of a further cycle is `≥ 7`. -/
theorem small_not_further_cycle {m : ℕ} (C : OddCycle m) (hf : C.IsFurther) : ∀ i : Fin m, 7 ≤ C.x i := by
  intro i; have hodd := C.x_odd i; have hne1 := (hf i).1; have hne5 := (hf i).2
  have hne3 : C.x i ≠ 3 := by
    intro h3; have hper := C.f_periodic i; rw [h3] at hper
    have hpos : 0 < C.totalHalvings + m := by have := C.hm; omega
    exact nonperiodic_three (C.totalHalvings + m) hpos hper
  omega
/-- Exact minimum-element transfer theorem: if every integer `n ∈ [7, X)` falls below itself under `f`, then -/
theorem cycle_min_ge_of_descent {m X : ℕ} (C : OddCycle m) (hf : C.IsFurther)
    (hsweep : ∀ n : ℕ, 7 ≤ n → n < X → ∃ t : ℕ, 1 ≤ t ∧ f^[t] n < n) :
    ∀ i : Fin m, X ≤ C.x i := by
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, C.hm⟩, Finset.mem_univ _⟩
  obtain ⟨i0, _, hi0⟩ := Finset.exists_min_image Finset.univ C.x hne
  have hmin : ∀ j : Fin m, C.x i0 ≤ C.x j := fun j => hi0 j (Finset.mem_univ j)
  have hge7 : 7 ≤ C.x i0 := small_not_further_cycle C hf i0
  have hgeX : X ≤ C.x i0 := by
    by_contra hlt
    obtain ⟨t, _, hdrop⟩ := hsweep (C.x i0) hge7 (by omega)
    have hstay := C.f_orbit_ge_min hmin i0 t; omega
  intro i; exact le_trans hgeX (hmin i)
/-- End-to-end transfer from a finite descent sweep `[7, X)` to the full logarithmic and halving-budget cycle -/
theorem cycle_further_log_bounds {m X : ℕ} (C : OddCycle m) (hX : 2 ≤ X)
    (hf : C.IsFurther)
    (hsweep : ∀ n : ℕ, 7 ≤ n → n < X → ∃ t : ℕ, 1 ≤ t ∧ f^[t] n < n) :
    (∀ i : Fin m, X ≤ C.x i) ∧
    0 < (C.totalHalvings : ℝ) * Real.log 2 - Real.log (C.digitProd : ℝ) ∧
    (C.totalHalvings : ℝ) * Real.log 2 - Real.log (C.digitProd : ℝ) <
      ((C.n1 : ℝ) + (C.n3 : ℝ) / 3 + (C.n5 : ℝ) / 5 + (C.n7 : ℝ) / 7 + (C.n9 : ℝ) / 9) /
        (X : ℝ) ∧
    C.n5 = C.n3 + C.n7 ∧
    2 * C.n1 + 3 * C.aExp + C.bExp + 7 * C.cExp ≤ 2 * C.totalHalvings := by
  have hmin := cycle_min_ge_of_descent C hf hsweep; have hs := cycle_log_sandwich C (by omega) hmin
  have h5 := cycle_n5_eq_n3_add_n7 C; have hbud := (lem_halving_budget C).2
  exact ⟨hmin, hs.1, lt_of_lt_of_le hs.2.1 hs.2.2.1, h5, hbud⟩

/-! ## Section 5: Paper 2 Lemma `lem:cycle-tail` and Lattice-Box Reduction -/
/-- Paper 2 Lemma `lem:cycle-tail`: any cycle with every odd member `≥ X`, `1 ≤ L ≤ X / 2`, and `K > L` halvings -/
theorem lem_cycle_tail {m X L : ℕ} (C : OddCycle m)
    (hX : 2 ≤ X) (hmin : ∀ i : Fin m, X ≤ C.x i)
    (_hL : 1 ≤ L) (hLX : 2 * L ≤ X) (hK : L < C.totalHalvings) :
    2 ^ L < 9 ^ m := by
  by_contra hle
  push Not at hle
  have hD_le_9m : C.digitProd ≤ 9 ^ m := by
    calc C.digitProd = ∏ i : Fin m, d (C.x i) := rfl
      _ ≤ ∏ _i : Fin m, (9 : ℕ) := Finset.prod_le_prod (fun i _ => C.d_le_nine i)
      _ = 9 ^ m := by simp
  have hD_le_2L : C.digitProd ≤ 2 ^ L := le_trans hD_le_9m hle
  have h8m : 2 ^ (3 * m) ≤ 2 ^ L := by
    calc 2 ^ (3 * m) = (2 ^ 3) ^ m := by rw [pow_mul]
      _ = 8 ^ m := by norm_num
      _ ≤ 9 ^ m := Nat.pow_le_pow_left (by omega) m
      _ ≤ 2 ^ L := hle
  have h3m_le_L : 3 * m ≤ L := (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp h8m
  have hs := cycle_log_sandwich C (by omega) hmin
  have hgap_lt : (C.totalHalvings : ℝ) * Real.log 2 - Real.log (C.digitProd : ℝ) <
      (m : ℝ) / (X : ℝ) := by linarith
  have hlogD_le : Real.log (C.digitProd : ℝ) ≤ (L : ℝ) * Real.log 2 := by
    have h1 : (C.digitProd : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := Nat.cast_le.mpr hD_le_2L
    have hlog := Real.log_le_log (Nat.cast_pos.mpr C.digitProd_pos) h1
    simpa [Nat.cast_pow, Real.log_pow] using hlog
  have hKL : (1 : ℝ) ≤ (C.totalHalvings : ℝ) - (L : ℝ) := by
    have : (L : ℝ) + 1 ≤ (C.totalHalvings : ℝ) := by exact_mod_cast hK
    linarith
  have hln2_le : Real.log 2 ≤ (C.totalHalvings : ℝ) * Real.log 2 - Real.log (C.digitProd : ℝ) := by
    have hln2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  have hmX : (m : ℝ) / (X : ℝ) ≤ 1 / 6 := by
    have hX_pos : (0 : ℝ) < (X : ℝ) := Nat.cast_pos.mpr (by omega)
    rw [div_le_div_iff₀ hX_pos (by norm_num : (0 : ℝ) < 6)]
    have h6m : (6 * m : ℝ) ≤ (X : ℝ) := by
      have : 6 * m ≤ X := by omega
      exact_mod_cast this
    linarith
  linarith [Real.log_two_gt_d9]
/-- Pure-kernel proof of `3^306 < 2^485` via small-exponent rational enclosures (`10000 * 3^53 < 10021 * 2^84` -/
private lemma three_pow_306_lt_two_pow_485 : (3 : ℕ) ^ 306 < 2 ^ 485 := by
  have h53 : 10000 * 3 ^ 53 < 10021 * 2 ^ 84 := by norm_num
  have h41 : 10000 * 3 ^ 41 < 9887 * 2 ^ 65 := by norm_num
  have hcoef : 10021 ^ 5 * 9887 < 10000 ^ 6 := by norm_num
  have hpow5 : (10000 * 3 ^ 53) ^ 5 < (10021 * 2 ^ 84) ^ 5 := pow_lt_pow_left₀ h53 (Nat.zero_le _) (by decide)
  have hmul : (10000 * 3 ^ 53) ^ 5 * (10000 * 3 ^ 41) <
      (10021 * 2 ^ 84) ^ 5 * (9887 * 2 ^ 65) :=
    Nat.mul_lt_mul_of_lt_of_lt hpow5 h41
  have hlhs : (10000 * 3 ^ 53) ^ 5 * (10000 * 3 ^ 41) = 10000 ^ 6 * 3 ^ 306 := by
    rw [mul_pow, ← pow_mul, mul_mul_mul_comm, ← pow_succ, ← pow_add]
  have hrhs : (10021 * 2 ^ 84) ^ 5 * (9887 * 2 ^ 65) = (10021 ^ 5 * 9887) * 2 ^ 485 := by
    rw [mul_pow, ← pow_mul, mul_mul_mul_comm, ← pow_add]
  rw [hlhs, hrhs] at hmul
  have hpos2 : 0 < (2 : ℕ) ^ 485 := pow_pos (by decide) 485
  have hlt : 10000 ^ 6 * 3 ^ 306 < 10000 ^ 6 * 2 ^ 485 := lt_trans hmul (Nat.mul_lt_mul_of_pos_right hcoef hpos2)
  exact Nat.lt_of_mul_lt_mul_left hlt
/-- Pure-kernel proof of `2^1054 < 3^665` via small-exponent rational enclosures ( -/
private lemma two_pow_1054_lt_three_pow_665 : (2 : ℕ) ^ 1054 < 3 ^ 665 := by
  have h84 : 1000000 * 2 ^ 84 < 997915 * 3 ^ 53 := by norm_num
  have h65 : 1000000 * 2 ^ 65 < 1011530 * 3 ^ 41 := by norm_num
  have hcoef : 997915 ^ 11 * 1011530 ^ 2 < 1000000 ^ 13 := by norm_num
  have hpow11 : (1000000 * 2 ^ 84) ^ 11 < (997915 * 3 ^ 53) ^ 11 := pow_lt_pow_left₀ h84 (Nat.zero_le _) (by decide)
  have hpow2 : (1000000 * 2 ^ 65) ^ 2 < (1011530 * 3 ^ 41) ^ 2 := pow_lt_pow_left₀ h65 (Nat.zero_le _) (by decide)
  have hmul : (1000000 * 2 ^ 84) ^ 11 * (1000000 * 2 ^ 65) ^ 2 <
      (997915 * 3 ^ 53) ^ 11 * (1011530 * 3 ^ 41) ^ 2 :=
    Nat.mul_lt_mul_of_lt_of_lt hpow11 hpow2
  have hlhs : (1000000 * 2 ^ 84) ^ 11 * (1000000 * 2 ^ 65) ^ 2 = 1000000 ^ 13 * 2 ^ 1054 := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_mul_mul_comm, ← pow_add, ← pow_add]
  have hrhs : (997915 * 3 ^ 53) ^ 11 * (1011530 * 3 ^ 41) ^ 2 =
      (997915 ^ 11 * 1011530 ^ 2) * 3 ^ 665 := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_mul_mul_comm, ← pow_add]
  rw [hlhs, hrhs] at hmul
  have hpos3 : 0 < (3 : ℕ) ^ 665 := pow_pos (by decide) 665
  have hlt : 1000000 ^ 13 * 2 ^ 1054 < 1000000 ^ 13 * 3 ^ 665 :=
    lt_trans hmul (Nat.mul_lt_mul_of_pos_right hcoef hpos3)
  exact Nat.lt_of_mul_lt_mul_left hlt
/-- Pure-kernel proof of `9^20189 < 2^64000` via the convergent witness `3^306 < 2^485`. -/
theorem nine_pow_20189_lt_two_pow_64000 : 9 ^ 20189 < 2 ^ 64000 := by
  have hw := three_pow_306_lt_two_pow_485
  have h9 : (9 : ℕ) = 3 ^ 2 := by decide
  have he1 : 2 * (20189 * 306) = 306 * 40378 := by decide
  have he2 : 485 * 40378 < 64000 * 306 := by decide
  have hne40378 : (40378 : ℕ) ≠ 0 := by decide
  have hne306 : (306 : ℕ) ≠ 0 := by decide
  have h1 : (9 ^ 20189) ^ 306 < (2 ^ 64000) ^ 306 := by
    calc (9 ^ 20189) ^ 306
        = ((3 ^ 2) ^ 20189) ^ 306 := by rw [h9]
      _ = 3 ^ (2 * (20189 * 306)) := by rw [← pow_mul, ← pow_mul]
      _ = 3 ^ (306 * 40378) := by rw [he1]
      _ = (3 ^ 306) ^ 40378 := by rw [pow_mul]
      _ < (2 ^ 485) ^ 40378 := pow_lt_pow_left₀ hw (Nat.zero_le _) hne40378
      _ = 2 ^ (485 * 40378) := by rw [← pow_mul]
      _ < 2 ^ (64000 * 306) := pow_lt_pow_right₀ (by decide) he2
      _ = (2 ^ 64000) ^ 306 := by rw [pow_mul]
  exact (pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) hne306).mp h1
/-- Pure-kernel proof of `2^64000 < 9^20190` via the convergent witness `2^1054 < 3^665`. -/
theorem two_pow_64000_lt_nine_pow_20190 : 2 ^ 64000 < 9 ^ 20190 := by
  have hw := two_pow_1054_lt_three_pow_665
  have h9 : (3 : ℕ) ^ 2 = 9 := by decide
  have he1 : 64000 * 665 < 1054 * 40380 := by decide
  have he2 : 665 * 40380 = 2 * (20190 * 665) := by decide
  have hne40380 : (40380 : ℕ) ≠ 0 := by decide
  have hne665 : (665 : ℕ) ≠ 0 := by decide
  have s1 : (2 ^ 64000) ^ 665 = 2 ^ (64000 * 665) := (pow_mul 2 64000 665).symm
  have s2 : 2 ^ (64000 * 665) < 2 ^ (1054 * 40380) := pow_lt_pow_right₀ (by decide) he1
  have s3 : 2 ^ (1054 * 40380) = (2 ^ 1054) ^ 40380 := pow_mul 2 1054 40380
  have s4 : (2 ^ 1054) ^ 40380 < (3 ^ 665) ^ 40380 := pow_lt_pow_left₀ hw (Nat.zero_le _) hne40380
  have s5 : (3 ^ 665) ^ 40380 = 3 ^ (665 * 40380) := (pow_mul 3 665 40380).symm
  have s6 : 3 ^ (665 * 40380) = 3 ^ (2 * (20190 * 665)) := congrArg (3 ^ ·) he2
  have s7 : 3 ^ (2 * (20190 * 665)) = (3 ^ 2) ^ (20190 * 665) := pow_mul 3 2 (20190 * 665)
  have s8 : (3 ^ 2) ^ (20190 * 665) = ((3 ^ 2) ^ 20190) ^ 665 := pow_mul (3 ^ 2) 20190 665
  have s9 : ((3 ^ 2) ^ 20190) ^ 665 = (9 ^ 20190) ^ 665 := congrArg (fun b => (b ^ 20190) ^ 665) h9
  have h1 : (2 ^ 64000) ^ 665 < (9 ^ 20190) ^ 665 :=
    lt_of_eq_of_lt s1 (lt_trans (lt_of_lt_of_eq s2 s3)
      (lt_of_lt_of_eq s4 (s5.trans (s6.trans (s7.trans (s8.trans s9))))))
  exact (pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) hne665).mp h1
/-- Paper 2 Theorem `thm:cycle-bounds-10e15` high-halving tail (`K > 64,000` at `X = 10^15`): forces `m ≥ 20,190` -/
theorem thm_cycle_tail_64000 {m : ℕ} (C : OddCycle m)
    (hmin : ∀ i : Fin m, 10 ^ 15 ≤ C.x i) (hK : 64000 < C.totalHalvings) :
    20190 ≤ m ∧ 84191 ≤ C.totalHalvings + m := by
  have h9m : 2 ^ 64000 < 9 ^ m := lem_cycle_tail C (by norm_num) hmin (by norm_num) (by norm_num) hK
  have hlt : 9 ^ 20189 < 9 ^ m := lt_trans nine_pow_20189_lt_two_pow_64000 h9m; have h19 : 1 < 9 := by decide
  have hm : 20189 < m := (pow_lt_pow_iff_right₀ h19).mp hlt
  exact ⟨Nat.succ_le_of_lt hm, Nat.add_le_add (Nat.succ_le_of_lt hK) (Nat.succ_le_of_lt hm)⟩
/-- Paper 2 Theorem `thm:cycle-bounds-10e15` exact lattice-box reduction: for any scaling `S ≥ 1` and integer -/
theorem cycle_lattice_box {m X L S lam3 lam5 lam7 : ℕ} (C : OddCycle m)
    (hX : 2 ≤ X) (hmin : ∀ i : Fin m, X ≤ C.x i)
    (_hL : 1 ≤ L) (_hLX : 2 * L ≤ X) (hKL : C.totalHalvings ≤ L) (hS : 1 ≤ S)
    (h3 : (lam3 : ℝ) ≤ (S : ℝ) * Real.logb 2 3 ∧ (S : ℝ) * Real.logb 2 3 < (lam3 : ℝ) + 1)
    (h5 : (lam5 : ℝ) ≤ (S : ℝ) * Real.logb 2 5 ∧ (S : ℝ) * Real.logb 2 5 < (lam5 : ℝ) + 1)
    (h7 : (lam7 : ℝ) ≤ (S : ℝ) * Real.logb 2 7 ∧ (S : ℝ) * Real.logb 2 7 < (lam7 : ℝ) + 1) :
    C.aExp * lam3 < L * S ∧
    C.bExp * lam5 < L * S ∧
    C.cExp * lam7 < L * S ∧
    1 ≤ (C.totalHalvings : ℤ) * (S : ℤ) -
      (C.aExp : ℤ) * (lam3 : ℤ) - (C.bExp : ℤ) * (lam5 : ℤ) - (C.cExp : ℤ) * (lam7 : ℤ) ∧
    ((C.totalHalvings : ℤ) * (S : ℤ) -
      (C.aExp : ℤ) * (lam3 : ℤ) - (C.bExp : ℤ) * (lam5 : ℤ) - (C.cExp : ℤ) * (lam7 : ℤ) : ℝ) <
      (3 * (L : ℝ) * (S : ℝ)) / (2 * (X : ℝ)) + (L : ℝ) := by
  have hln2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2D : Real.logb 2 (C.digitProd : ℝ) =
      (C.aExp : ℝ) * Real.logb 2 3 + (C.bExp : ℝ) * Real.logb 2 5 +
      (C.cExp : ℝ) * Real.logb 2 7 := by
    rw [cycle_digitProd_factorization C]; push_cast
    rw [Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity),
      Real.logb_pow, Real.logb_pow, Real.logb_pow]
  have hD_lt_2K : (C.digitProd : ℝ) < (2 : ℝ) ^ C.totalHalvings := by exact_mod_cast cycle_digitProd_lt_two_pow C
  have hlog2D_lt_K : Real.logb 2 (C.digitProd : ℝ) < (C.totalHalvings : ℝ) := by
    have hlog := Real.log_lt_log (Nat.cast_pos.mpr C.digitProd_pos) hD_lt_2K; rw [Real.log_pow] at hlog
    unfold Real.logb; exact (div_lt_iff₀ hln2_pos).mpr hlog
  have hlog2D_lt_L : Real.logb 2 (C.digitProd : ℝ) < (L : ℝ) := lt_of_lt_of_le hlog2D_lt_K (Nat.cast_le.mpr hKL)
  have hS_pos : (0 : ℝ) < (S : ℝ) := Nat.cast_pos.mpr (by omega)
  have h3_pos : (0 : ℝ) < Real.logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)
  have h5_pos : (0 : ℝ) < Real.logb 2 5 := Real.logb_pos (by norm_num) (by norm_num)
  have h7_pos : (0 : ℝ) < Real.logb 2 7 := Real.logb_pos (by norm_num) (by norm_num)
  have ha_lt : C.aExp * lam3 < L * S := by
    have hreal : ((C.aExp * lam3 : ℕ) : ℝ) < ((L * S : ℕ) : ℝ) := by
      push_cast
      have h1 : (C.aExp : ℝ) * (lam3 : ℝ) ≤ (C.aExp : ℝ) * ((S : ℝ) * Real.logb 2 3) :=
        mul_le_mul_of_nonneg_left h3.1 (Nat.cast_nonneg _)
      have h2 : (C.aExp : ℝ) * Real.logb 2 3 ≤ Real.logb 2 (C.digitProd : ℝ) := by
        rw [hlog2D]
        have : 0 ≤ (C.bExp : ℝ) * Real.logb 2 5 := by positivity
        have : 0 ≤ (C.cExp : ℝ) * Real.logb 2 7 := by positivity
        linarith
      nlinarith
    exact Nat.cast_lt.mp hreal
  have hb_lt : C.bExp * lam5 < L * S := by
    have hreal : ((C.bExp * lam5 : ℕ) : ℝ) < ((L * S : ℕ) : ℝ) := by
      push_cast
      have h1 : (C.bExp : ℝ) * (lam5 : ℝ) ≤ (C.bExp : ℝ) * ((S : ℝ) * Real.logb 2 5) :=
        mul_le_mul_of_nonneg_left h5.1 (Nat.cast_nonneg _)
      have h2 : (C.bExp : ℝ) * Real.logb 2 5 ≤ Real.logb 2 (C.digitProd : ℝ) := by
        rw [hlog2D]
        have : 0 ≤ (C.aExp : ℝ) * Real.logb 2 3 := by positivity
        have : 0 ≤ (C.cExp : ℝ) * Real.logb 2 7 := by positivity
        linarith
      nlinarith
    exact Nat.cast_lt.mp hreal
  have hc_lt : C.cExp * lam7 < L * S := by
    have hreal : ((C.cExp * lam7 : ℕ) : ℝ) < ((L * S : ℕ) : ℝ) := by
      push_cast
      have h1 : (C.cExp : ℝ) * (lam7 : ℝ) ≤ (C.cExp : ℝ) * ((S : ℝ) * Real.logb 2 7) :=
        mul_le_mul_of_nonneg_left h7.1 (Nat.cast_nonneg _)
      have h2 : (C.cExp : ℝ) * Real.logb 2 7 ≤ Real.logb 2 (C.digitProd : ℝ) := by
        rw [hlog2D]
        have : 0 ≤ (C.aExp : ℝ) * Real.logb 2 3 := by positivity
        have : 0 ≤ (C.bExp : ℝ) * Real.logb 2 5 := by positivity
        linarith
      nlinarith
    exact Nat.cast_lt.mp hreal
  let F : ℤ := (C.totalHalvings : ℤ) * (S : ℤ) -
    (C.aExp : ℤ) * (lam3 : ℤ) - (C.bExp : ℤ) * (lam5 : ℤ) - (C.cExp : ℤ) * (lam7 : ℤ)
  have hF_real : (F : ℝ) =
      (S : ℝ) * ((C.totalHalvings : ℝ) - Real.logb 2 (C.digitProd : ℝ)) +
      (C.aExp : ℝ) * ((S : ℝ) * Real.logb 2 3 - (lam3 : ℝ)) +
      (C.bExp : ℝ) * ((S : ℝ) * Real.logb 2 5 - (lam5 : ℝ)) +
      (C.cExp : ℝ) * ((S : ℝ) * Real.logb 2 7 - (lam7 : ℝ)) := by
    simp only [F]; push_cast; rw [hlog2D]; ring
  have hF_pos_real : (0 : ℝ) < (F : ℝ) := by
    rw [hF_real]
    have h1 : 0 < (S : ℝ) * ((C.totalHalvings : ℝ) - Real.logb 2 (C.digitProd : ℝ)) :=
      mul_pos hS_pos (sub_pos.mpr hlog2D_lt_K)
    have h2 : 0 ≤ (C.aExp : ℝ) * ((S : ℝ) * Real.logb 2 3 - (lam3 : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr h3.1)
    have h3' : 0 ≤ (C.bExp : ℝ) * ((S : ℝ) * Real.logb 2 5 - (lam5 : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr h5.1)
    have h4 : 0 ≤ (C.cExp : ℝ) * ((S : ℝ) * Real.logb 2 7 - (lam7 : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr h7.1)
    linarith
  have hF_ge1 : (1 : ℤ) ≤ F := by
    have h0 : (0 : ℤ) < F := by exact_mod_cast hF_pos_real
    omega
  have hlog23_ge1 : (1 : ℝ) ≤ Real.logb 2 3 := by rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]; norm_num
  have hlog25_ge1 : (1 : ℝ) ≤ Real.logb 2 5 := by rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]; norm_num
  have hlog27_ge1 : (1 : ℝ) ≤ Real.logb 2 7 := by rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]; norm_num
  have habc_lt_L : (C.aExp : ℝ) + (C.bExp : ℝ) + (C.cExp : ℝ) < (L : ℝ) := by
    have h1 : (C.aExp : ℝ) ≤ (C.aExp : ℝ) * Real.logb 2 3 := le_mul_of_one_le_right (Nat.cast_nonneg _) hlog23_ge1
    have h2 : (C.bExp : ℝ) ≤ (C.bExp : ℝ) * Real.logb 2 5 := le_mul_of_one_le_right (Nat.cast_nonneg _) hlog25_ge1
    have h3' : (C.cExp : ℝ) ≤ (C.cExp : ℝ) * Real.logb 2 7 := le_mul_of_one_le_right (Nat.cast_nonneg _) hlog27_ge1
    linarith only [h1, h2, h3', hlog2D, hlog2D_lt_L]
  have hs := cycle_log_sandwich C (by omega) hmin
  have hgap_lt : (C.totalHalvings : ℝ) * Real.log 2 - Real.log (C.digitProd : ℝ) <
      (L : ℝ) / (X : ℝ) := by
    have hKL' : (C.totalHalvings : ℝ) / (X : ℝ) ≤ (L : ℝ) / (X : ℝ) :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr hKL) (Nat.cast_nonneg _)
    linarith only [hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2, hKL']
  have hG_lt : (C.totalHalvings : ℝ) - Real.logb 2 (C.digitProd : ℝ) <
      (3 * (L : ℝ)) / (2 * (X : ℝ)) := by
    have hG_eq : ((C.totalHalvings : ℝ) - Real.logb 2 (C.digitProd : ℝ)) * Real.log 2 =
        (C.totalHalvings : ℝ) * Real.log 2 - Real.log (C.digitProd : ℝ) := by
      unfold Real.logb; field_simp
    have hln2_gt : (2 / 3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hG_pos : 0 < (C.totalHalvings : ℝ) - Real.logb 2 (C.digitProd : ℝ) := sub_pos.mpr hlog2D_lt_K
    have hmul : (2 / 3 : ℝ) * ((C.totalHalvings : ℝ) - Real.logb 2 (C.digitProd : ℝ)) <
        (L : ℝ) / (X : ℝ) := by
      have h1 : (2 / 3 : ℝ) * ((C.totalHalvings : ℝ) - Real.logb 2 (C.digitProd : ℝ)) <
          ((C.totalHalvings : ℝ) - Real.logb 2 (C.digitProd : ℝ)) * Real.log 2 := by
        rw [mul_comm (2 / 3 : ℝ)]; exact mul_lt_mul_of_pos_left hln2_gt hG_pos
      linarith only [h1, hG_eq, hgap_lt]
    have hdiv : (3 * (L : ℝ)) / (2 * (X : ℝ)) = (3 / 2 : ℝ) * ((L : ℝ) / (X : ℝ)) := by ring
    linarith only [hmul, hdiv]
  have hF_lt : (F : ℝ) < (3 * (L : ℝ) * (S : ℝ)) / (2 * (X : ℝ)) + (L : ℝ) := by
    rw [hF_real]
    have h1 : (S : ℝ) * ((C.totalHalvings : ℝ) - Real.logb 2 (C.digitProd : ℝ)) <
        (3 * (L : ℝ) * (S : ℝ)) / (2 * (X : ℝ)) := by
      have htmp := mul_lt_mul_of_pos_left hG_lt hS_pos
      have heq : (S : ℝ) * (3 * (L : ℝ) / (2 * (X : ℝ))) =
          (3 * (L : ℝ) * (S : ℝ)) / (2 * (X : ℝ)) := by ring
      linarith only [htmp, heq]
    have h2 : (C.aExp : ℝ) * ((S : ℝ) * Real.logb 2 3 - (lam3 : ℝ)) ≤ (C.aExp : ℝ) := by
      have hsub : (S : ℝ) * Real.logb 2 3 - (lam3 : ℝ) ≤ 1 := by linarith only [h3.2]
      simpa using mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg C.aExp)
    have h3' : (C.bExp : ℝ) * ((S : ℝ) * Real.logb 2 5 - (lam5 : ℝ)) ≤ (C.bExp : ℝ) := by
      have hsub : (S : ℝ) * Real.logb 2 5 - (lam5 : ℝ) ≤ 1 := by linarith only [h5.2]
      simpa using mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg C.bExp)
    have h4 : (C.cExp : ℝ) * ((S : ℝ) * Real.logb 2 7 - (lam7 : ℝ)) ≤ (C.cExp : ℝ) := by
      have hsub : (S : ℝ) * Real.logb 2 7 - (lam7 : ℝ) ≤ 1 := by linarith only [h7.2]
      simpa using mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg C.cExp)
    linarith only [h1, h2, h3', h4, habc_lt_L]
  exact ⟨ha_lt, hb_lt, hc_lt, hF_ge1, by simpa [F] using hF_lt⟩

/-! ## Section 6: Unconditional classification of `m = 1, 2, 3` odd-member cycles -/
/-- If any odd member of `C` equals `1`, then EVERY odd member equals `1` and every `k_i = 1`. -/
theorem cycle_contains_one_iff {m : ℕ} (C : OddCycle m) :
    (∃ i : Fin m, C.x i = 1) ↔ ∀ j : Fin m, C.x j = 1 ∧ C.k j = 1 := by
  constructor
  · rintro ⟨i, hi⟩
    have hstep1 : ∀ j : Fin m, C.x j = 1 → C.x (finNext C.hm j) = 1 ∧ C.k j = 1 := by
      intro j hj; have hst := C.step j; rw [hj] at hst; have hd1 : d 1 = 1 := by decide
      rw [hd1] at hst; have hk := C.k_pos j; have hxp := C.x_pos (finNext C.hm j)
      have h2k : 2 ^ C.k j ≥ 2 := calc 2 ^ C.k j ≥ 2 ^ 1 := Nat.pow_le_pow_right (by omega) hk
        _ = 2 := by norm_num
      have h2k_eq : 2 ^ C.k j = 2 := by nlinarith
      have hk1 : C.k j = 1 := by
        have : 2 ^ C.k j = 2 ^ 1 := by simpa using h2k_eq
        exact Nat.pow_right_injective (by omega) this
      rw [hk1] at hst; exact ⟨by omega, hk1⟩
    have hadd : ∀ r : ℕ, C.x (finAdd C.hm i r) = 1 := by
      intro r
      induction r with
      | zero => rw [finAdd_zero]; exact hi
      | succ r ih => rw [finAdd_succ]; exact (hstep1 _ ih).1
    intro j
    have hj_eq : C.x j = 1 := by
      let r := (j.val + m - i.val) % m
      have hfin : finAdd C.hm i r = j := by
        apply Fin.ext; change (i.val + (j.val + m - i.val) % m) % m = j.val; have hi' := i.isLt; have hj' := j.isLt
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; have h2 : i.val + (j.val + m - i.val) = j.val + m := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hj']
      rw [← hfin]; exact hadd r
    exact ⟨hj_eq, (hstep1 j hj_eq).2⟩
  · intro h; exact ⟨⟨0, C.hm⟩, (h ⟨0, C.hm⟩).1⟩
/-- Unconditional uniqueness of 1-odd-member cycles: `{1, 2}` is the ONLY `m = 1` cycle. -/
theorem cycle_m1_unique (C : OddCycle 1) : C.x 0 = 1 ∧ C.k 0 = 1 := by
  have hst := C.step 0
  have hnext : finNext C.hm (0 : Fin 1) = 0 := by apply Fin.ext; simp [finNext]
  rw [hnext] at hst
  have hx1 : C.x 0 = 1 := by
    have hdvd : C.x 0 ∣ 1 := by
      have hle : d (C.x 0) ≤ 2 ^ C.k 0 := by
        have hlt := cycle_digitProd_lt_two_pow C; have hD : C.digitProd = d (C.x 0) := by simp [OddCycle.digitProd]
        have hK : C.totalHalvings = C.k 0 := by simp [OddCycle.totalHalvings]
        rw [hD, hK] at hlt; omega
      refine ⟨2 ^ C.k 0 - d (C.x 0), ?_⟩
      rw [Nat.mul_sub_left_distrib]
      have : C.x 0 * d (C.x 0) = d (C.x 0) * C.x 0 := Nat.mul_comm _ _
      have : C.x 0 * 2 ^ C.k 0 = 2 ^ C.k 0 * C.x 0 := Nat.mul_comm _ _
      omega
    exact Nat.dvd_one.mp hdvd
  exact ((cycle_contains_one_iff C).mp ⟨0, hx1⟩) 0
/-- Helper: no power of 2 lies strictly between `a` and `b` when `2^r ≤ a` and `b < 2^(r+1)`. -/
private lemma no_pow2_between {K r a b : ℕ} (h1 : 2 ^ r ≤ a) (h2 : a < 2 ^ K)
    (h3 : 2 ^ K ≤ b) (h4 : b < 2 ^ (r + 1)) : False := by
  have hKr : r < K := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp (lt_of_le_of_lt h1 h2)
  have hKlt : K < r + 1 := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp (lt_of_le_of_lt h3 h4)
  omega
/-- Helper: if `2^r ≤ a < 2^K ≤ b < 2^(r+2)` and `2^(r+1)` is the only power of 2 in `(a, b]`, then `K = r + 1`. -/
private lemma unique_pow2_between {K r a b : ℕ} (h1 : 2 ^ r ≤ a) (h2 : a < 2 ^ K)
    (h3 : 2 ^ K ≤ b) (h4 : b < 2 ^ (r + 2)) : K = r + 1 := by
  have hKr : r < K := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp (lt_of_le_of_lt h1 h2)
  have hKlt : K < r + 2 := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp (lt_of_le_of_lt h3 h4)
  omega
/-- Helper for `m = 2`: solve `(5, 3)` pair directly. -/
private lemma cycle_m2_five_three {x0 x1 k0 k1 : ℕ}
    (hx0_odd : x0 % 2 = 1) (hx1_odd : x1 % 2 = 1)
    (hk0 : 1 ≤ k0) (hk1 : 1 ≤ k1)
    (hd0 : d x0 = 5) (hd1 : d x1 = 3)
    (h0 : 5 * x0 + 1 = 2 ^ k0 * x1) (h1 : 3 * x1 + 1 = 2 ^ k1 * x0) :
    x0 = 5 ∧ x1 = 13 ∧ k0 = 1 ∧ k1 = 3 := by
  have hx0_ge : 5 ≤ x0 := by unfold d at hd0; omega
  have hx1_ge : 3 ≤ x1 := by unfold d at hd1; omega
  have hprod : (5 * x0 + 1) * (3 * x1 + 1) = 2 ^ (k0 + k1) * (x0 * x1) := by
    calc (5 * x0 + 1) * (3 * x1 + 1) = (2 ^ k0 * x1) * (2 ^ k1 * x0) := by rw [h0, h1]
      _ = 2 ^ (k0 + k1) * (x0 * x1) := by rw [pow_add]; ring
  have hgt : 15 < 2 ^ (k0 + k1) := by
    have : 15 * (x0 * x1) < 2 ^ (k0 + k1) * (x0 * x1) := by nlinarith
    exact Nat.lt_of_mul_lt_mul_right this
  have hle : 2 ^ (k0 + k1) ≤ 17 := by
    have hlt18 : 2 ^ (k0 + k1) * (x0 * x1) < 18 * (x0 * x1) := by nlinarith
    have := Nat.lt_of_mul_lt_mul_right hlt18
    omega
  have hK4 : k0 + k1 = 4 := unique_pow2_between (r := 3) (by norm_num) hgt hle (by norm_num)
  have htr := (lem_last_digit_transition hx0_odd hx1_odd hk0 (by rw [hd0]; exact h0)).2.1 hd0
  have hk0_mod : k0 % 4 = 1 := htr.2.1.mp hd1; have hk0_eq : k0 = 1 := by omega
  have hk1_eq : k1 = 3 := by omega
  rw [hk0_eq] at h0; rw [hk1_eq] at h1; norm_num at h0 h1; exact ⟨by omega, by omega, hk0_eq, hk1_eq⟩
/-- Helper for `m = 2`: rule out `(1, 9)` pair. -/
private lemma cycle_m2_one_nine_absurd {x0 x1 k0 k1 : ℕ}
    (hx0_pos : 0 < x0) (hx0_odd : x0 % 2 = 1) (hx1_odd : x1 % 2 = 1)
    (hk0 : 1 ≤ k0) (hk1 : 1 ≤ k1)
    (hd0 : d x0 = 1) (hd1 : d x1 = 9)
    (h0 : 1 * x0 + 1 = 2 ^ k0 * x1) (h1 : 9 * x1 + 1 = 2 ^ k1 * x0) : False := by
  have hx1_ge : 9 ≤ x1 := by unfold d at hd1; omega
  have hprod : (x0 + 1) * (9 * x1 + 1) = 2 ^ (k0 + k1) * (x0 * x1) := by
    calc (x0 + 1) * (9 * x1 + 1) = (2 ^ k0 * x1) * (2 ^ k1 * x0) := by rw [← h0, ← h1]; ring
      _ = 2 ^ (k0 + k1) * (x0 * x1) := by rw [pow_add]; ring
  have hgt : 9 < 2 ^ (k0 + k1) := by
    have : 9 * (x0 * x1) < 2 ^ (k0 + k1) * (x0 * x1) := by nlinarith
    exact Nat.lt_of_mul_lt_mul_right this
  have hle : 2 ^ (k0 + k1) ≤ 19 := by
    have hlt20 : 2 ^ (k0 + k1) * (x0 * x1) < 20 * (x0 * x1) := by nlinarith
    have := Nat.lt_of_mul_lt_mul_right hlt20
    omega
  have hK4 : k0 + k1 = 4 := unique_pow2_between (r := 3) (by norm_num) hgt hle (by norm_num)
  have htr := (lem_last_digit_transition hx0_odd hx1_odd hk0 (by rw [hd0]; exact h0)).1 (Or.inl hd0)
  have hk0_mod : k0 % 4 = 3 := htr.2.2.1.mp hd1; have hk0_eq : k0 = 3 := by omega
  have hk1_eq : k1 = 1 := by omega
  rw [hk0_eq] at h0; rw [hk1_eq] at h1; norm_num at h0 h1; omega
/-- Unconditional classification of ALL 2-odd-member cycles of `f = f_10`: every `OddCycle 2` is either the -/
theorem cycle_m2_classification (C : OddCycle 2) :
    (C.x 0 = 1 ∧ C.x 1 = 1 ∧ C.k 0 = 1 ∧ C.k 1 = 1) ∨
    (C.x 0 = 5 ∧ C.x 1 = 13 ∧ C.k 0 = 1 ∧ C.k 1 = 3) ∨
    (C.x 0 = 13 ∧ C.x 1 = 5 ∧ C.k 0 = 3 ∧ C.k 1 = 1) := by
  have hn0 : finNext C.hm (0 : Fin 2) = 1 := by apply Fin.ext; simp [finNext]
  have hn1 : finNext C.hm (1 : Fin 2) = 0 := by apply Fin.ext; simp [finNext]
  have hst0 := C.step 0; rw [hn0] at hst0; have hst1 := C.step 1; rw [hn1] at hst1
  have h5_0 := lemma_after_3_or_7_is_5 (C.x_odd 0) (C.x_odd 1) hst0
  have h5_1 := lemma_after_3_or_7_is_5 (C.x_odd 1) (C.x_odd 0) hst1
  rcases C.d_mem 0 with hd0 | hd0 | hd0 | hd0 | hd0 <;>
  rcases C.d_mem 1 with hd1 | hd1 | hd1 | hd1 | hd1
  ·
    left; have hD : C.digitProd = 1 := by simp [OddCycle.digitProd, Fin.prod_univ_two, hd0, hd1]
    have hall := (cycle_all_ones_iff C).mp hD; exact ⟨(hall 0).1, (hall 1).1, (hall 0).2, (hall 1).2⟩
  ·
    have : C.x 0 % 10 = 5 := h5_1.mpr (Or.inl hd1); unfold d at hd0; omega
  ·
    have : C.x 0 % 10 = 3 ∨ C.x 0 % 10 = 7 := h5_0.mp hd1; unfold d at hd0; omega
  ·
    have : C.x 0 % 10 = 5 := h5_1.mpr (Or.inr hd1); unfold d at hd0; omega
  ·
    rw [hd0] at hst0; rw [hd1] at hst1
    exact absurd (cycle_m2_one_nine_absurd (C.x_pos 0) (C.x_odd 0) (C.x_odd 1)
      (C.k_pos 0) (C.k_pos 1) hd0 hd1 hst0 hst1) id
  ·
    have : C.x 1 % 10 = 5 := h5_0.mpr (Or.inl hd0); unfold d at hd1; omega
  ·
    have : C.x 1 % 10 = 5 := h5_0.mpr (Or.inl hd0); unfold d at hd1; omega
  ·
    rw [hd0] at hst0; rw [hd1] at hst1
    obtain ⟨h1, h0, hk1, hk0⟩ := cycle_m2_five_three (C.x_odd 1) (C.x_odd 0)
      (C.k_pos 1) (C.k_pos 0) hd1 hd0 hst1 hst0
    exact Or.inr (Or.inr ⟨h0, h1, hk0, hk1⟩)
  ·
    have : C.x 1 % 10 = 5 := h5_0.mpr (Or.inl hd0); unfold d at hd1; omega
  ·
    have : C.x 1 % 10 = 5 := h5_0.mpr (Or.inl hd0); unfold d at hd1; omega
  ·
    have : C.x 1 % 10 = 3 ∨ C.x 1 % 10 = 7 := h5_1.mp hd0; unfold d at hd1; omega
  ·
    rw [hd0] at hst0; rw [hd1] at hst1
    obtain ⟨h0, h1, hk0, hk1⟩ := cycle_m2_five_three (C.x_odd 0) (C.x_odd 1)
      (C.k_pos 0) (C.k_pos 1) hd0 hd1 hst0 hst1
    exact Or.inr (Or.inl ⟨h0, h1, hk0, hk1⟩)
  ·
    have : C.x 0 % 10 = 3 ∨ C.x 0 % 10 = 7 := h5_0.mp hd1; unfold d at hd0; omega
  ·
    rw [hd0] at hst0; rw [hd1] at hst1; have hx0_ge : 5 ≤ C.x 0 := by unfold d at hd0; omega
    have hx1_ge : 7 ≤ C.x 1 := by unfold d at hd1; omega
    have hprod : (5 * C.x 0 + 1) * (7 * C.x 1 + 1) = 2 ^ (C.k 0 + C.k 1) * (C.x 0 * C.x 1) := by
      calc (5 * C.x 0 + 1) * (7 * C.x 1 + 1) = (2 ^ C.k 0 * C.x 1) * (2 ^ C.k 1 * C.x 0) := by rw [hst0, hst1]
        _ = 2 ^ (C.k 0 + C.k 1) * (C.x 0 * C.x 1) := by rw [pow_add]; ring
    have hgt : 35 < 2 ^ (C.k 0 + C.k 1) := by
      have : 35 * (C.x 0 * C.x 1) < 2 ^ (C.k 0 + C.k 1) * (C.x 0 * C.x 1) := by nlinarith
      exact Nat.lt_of_mul_lt_mul_right this
    have hle : 2 ^ (C.k 0 + C.k 1) ≤ 38 := by
      have : 2 ^ (C.k 0 + C.k 1) * (C.x 0 * C.x 1) < 39 * (C.x 0 * C.x 1) := by nlinarith
      have := Nat.lt_of_mul_lt_mul_right this; omega
    exact absurd (no_pow2_between (r := 5) (by norm_num) hgt hle (by norm_num)) id
  ·
    have : C.x 1 % 10 = 3 ∨ C.x 1 % 10 = 7 := h5_1.mp hd0; unfold d at hd1; omega
  ·
    have : C.x 1 % 10 = 5 := h5_0.mpr (Or.inr hd0); unfold d at hd1; omega
  ·
    have : C.x 1 % 10 = 5 := h5_0.mpr (Or.inr hd0); unfold d at hd1; omega
  ·
    rw [hd0] at hst0; rw [hd1] at hst1; have hx0_ge : 7 ≤ C.x 0 := by unfold d at hd0; omega
    have hx1_ge : 5 ≤ C.x 1 := by unfold d at hd1; omega
    have hprod : (7 * C.x 0 + 1) * (5 * C.x 1 + 1) = 2 ^ (C.k 0 + C.k 1) * (C.x 0 * C.x 1) := by
      calc (7 * C.x 0 + 1) * (5 * C.x 1 + 1) = (2 ^ C.k 0 * C.x 1) * (2 ^ C.k 1 * C.x 0) := by rw [hst0, hst1]
        _ = 2 ^ (C.k 0 + C.k 1) * (C.x 0 * C.x 1) := by rw [pow_add]; ring
    have hgt : 35 < 2 ^ (C.k 0 + C.k 1) := by
      have : 35 * (C.x 0 * C.x 1) < 2 ^ (C.k 0 + C.k 1) * (C.x 0 * C.x 1) := by nlinarith
      exact Nat.lt_of_mul_lt_mul_right this
    have hle : 2 ^ (C.k 0 + C.k 1) ≤ 38 := by
      have : 2 ^ (C.k 0 + C.k 1) * (C.x 0 * C.x 1) < 39 * (C.x 0 * C.x 1) := by nlinarith
      have := Nat.lt_of_mul_lt_mul_right this; omega
    exact absurd (no_pow2_between (r := 5) (by norm_num) hgt hle (by norm_num)) id
  ·
    have : C.x 1 % 10 = 5 := h5_0.mpr (Or.inr hd0); unfold d at hd1; omega
  ·
    have : C.x 1 % 10 = 5 := h5_0.mpr (Or.inr hd0); unfold d at hd1; omega
  ·
    rw [hd0] at hst0; rw [hd1] at hst1
    exact absurd (cycle_m2_one_nine_absurd (C.x_pos 1) (C.x_odd 1) (C.x_odd 0)
      (C.k_pos 1) (C.k_pos 0) hd1 hd0 hst1 hst0) id
  ·
    have : C.x 0 % 10 = 5 := h5_1.mpr (Or.inl hd1); unfold d at hd0; omega
  ·
    have : C.x 0 % 10 = 3 ∨ C.x 0 % 10 = 7 := h5_0.mp hd1; unfold d at hd0; omega
  ·
    have : C.x 0 % 10 = 5 := h5_1.mpr (Or.inr hd1); unfold d at hd0; omega
  ·
    rw [hd0] at hst0; rw [hd1] at hst1; have hx0_ge : 9 ≤ C.x 0 := by unfold d at hd0; omega
    have hx1_ge : 9 ≤ C.x 1 := by unfold d at hd1; omega
    have hprod : (9 * C.x 0 + 1) * (9 * C.x 1 + 1) = 2 ^ (C.k 0 + C.k 1) * (C.x 0 * C.x 1) := by
      calc (9 * C.x 0 + 1) * (9 * C.x 1 + 1) = (2 ^ C.k 0 * C.x 1) * (2 ^ C.k 1 * C.x 0) := by rw [hst0, hst1]
        _ = 2 ^ (C.k 0 + C.k 1) * (C.x 0 * C.x 1) := by rw [pow_add]; ring
    have hgt : 81 < 2 ^ (C.k 0 + C.k 1) := by
      have : 81 * (C.x 0 * C.x 1) < 2 ^ (C.k 0 + C.k 1) * (C.x 0 * C.x 1) := by nlinarith
      exact Nat.lt_of_mul_lt_mul_right this
    have hle : 2 ^ (C.k 0 + C.k 1) ≤ 83 := by
      have : 2 ^ (C.k 0 + C.k 1) * (C.x 0 * C.x 1) < 84 * (C.x 0 * C.x 1) := by nlinarith
      have := Nat.lt_of_mul_lt_mul_right this; omega
    exact absurd (no_pow2_between (r := 6) (by norm_num) hgt hle (by norm_num)) id
/-- Helper: if `5` lies in an `OddCycle 3`, contradiction (since the 5-cycle has odd period 2). -/
private lemma cycle_m3_no_five (C : OddCycle 3) : ∀ i : Fin 3, C.x i ≠ 5 := by
  have h5_next : ∀ i : Fin 3, C.x i = 5 → C.x (finNext C.hm i) = 13 := by
    intro i hi; have hst := C.step i; rw [hi] at hst
    have : d 5 * 5 + 1 = 26 := by decide
    rw [this] at hst; have hodd := C.x_odd (finNext C.hm i); have hk := C.k_pos i
    have h2 : 2 ^ C.k i * C.x (finNext C.hm i) = 2 ^ 1 * 13 := by omega
    exact (two_pow_mul_odd_inj hodd (by omega) h2).2
  have h13_next : ∀ i : Fin 3, C.x i = 13 → C.x (finNext C.hm i) = 5 := by
    intro i hi; have hst := C.step i; rw [hi] at hst
    have : d 13 * 13 + 1 = 40 := by decide
    rw [this] at hst
    have hodd := C.x_odd (finNext C.hm i); have h2 : 2 ^ C.k i * C.x (finNext C.hm i) = 2 ^ 3 * 5 := by omega
    exact (two_pow_mul_odd_inj hodd (by omega) h2).2
  intro i hi; have h1 : C.x (finNext C.hm i) = 13 := h5_next i hi
  have h2 : C.x (finNext C.hm (finNext C.hm i)) = 5 := h13_next _ h1
  have h3 : C.x (finNext C.hm (finNext C.hm (finNext C.hm i))) = 13 := h5_next _ h2
  have hcyc : finNext C.hm (finNext C.hm (finNext C.hm i)) = i := by
    apply Fin.ext
    fin_cases i <;> simp [finNext]
  rw [hcyc] at h3; omega
/-- Helper: rational upper-bound factor for any odd member `x ≥ 7` of a further cycle: -/
private lemma further_factor_bound {x : ℕ} (hx_ge7 : 7 ≤ x) (_hx_odd : x % 2 = 1) :
    (d x = 1 → 11 * (d x * x + 1) ≤ 12 * x) ∧
    (d x = 3 → 13 * (d x * x + 1) ≤ 40 * x) ∧
    (d x = 5 → 15 * (d x * x + 1) ≤ 76 * x) ∧
    (d x = 7 → 7 * (d x * x + 1) ≤ 50 * x) ∧
    (d x = 9 → 9 * (d x * x + 1) ≤ 82 * x) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h]; unfold d at h; omega
  · rw [h]; unfold d at h; omega
  · rw [h]; unfold d at h; omega
  · rw [h]; unfold d at h; omega
  · rw [h]; unfold d at h; omega
/-- Helper: the 8 possible nonnegative integer solutions to `a5 = a3 + a7` and sum `= 3`. -/
private lemma m3_digit_cases {a1 a3 a5 a7 a9 : ℕ}
    (h5 : a5 = a3 + a7) (hsum : a1 + a3 + a5 + a7 + a9 = 3) :
    (a1 = 3 ∧ a3 = 0 ∧ a5 = 0 ∧ a7 = 0 ∧ a9 = 0) ∨
    (a1 = 2 ∧ a3 = 0 ∧ a5 = 0 ∧ a7 = 0 ∧ a9 = 1) ∨
    (a1 = 1 ∧ a3 = 0 ∧ a5 = 0 ∧ a7 = 0 ∧ a9 = 2) ∨
    (a1 = 0 ∧ a3 = 0 ∧ a5 = 0 ∧ a7 = 0 ∧ a9 = 3) ∨
    (a1 = 1 ∧ a3 = 1 ∧ a5 = 1 ∧ a7 = 0 ∧ a9 = 0) ∨
    (a1 = 0 ∧ a3 = 1 ∧ a5 = 1 ∧ a7 = 0 ∧ a9 = 1) ∨
    (a1 = 1 ∧ a3 = 0 ∧ a5 = 1 ∧ a7 = 1 ∧ a9 = 0) ∨
    (a1 = 0 ∧ a3 = 0 ∧ a5 = 1 ∧ a7 = 1 ∧ a9 = 1) := by
  have ha3 : a3 ≤ 1 := by omega
  have ha7 : a7 ≤ 1 := by omega
  have ha1 : a1 ≤ 3 := by omega
  interval_cases a3 <;> interval_cases a7 <;> interval_cases a1 <;>
    first
    | exact Or.inl (by omega)
    | exact Or.inr (Or.inl (by omega))
    | exact Or.inr (Or.inr (Or.inl (by omega)))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))))
/-- Unconditional exclusion of ALL non-trivial 3-odd-member cycles of `f = f_10`: every `OddCycle 3` is the -/
theorem cycle_m3_unique (C : OddCycle 3) : ∀ i : Fin 3, C.x i = 1 ∧ C.k i = 1 := by
  by_cases h1 : ∃ i : Fin 3, C.x i = 1
  · exact (cycle_contains_one_iff C).mp h1
  · exfalso; have hf : C.IsFurther := fun i => ⟨fun hi => h1 ⟨i, hi⟩, cycle_m3_no_five C i⟩
    have hge7 : ∀ i : Fin 3, 7 ≤ C.x i := small_not_further_cycle C hf
    have h5 := cycle_n5_eq_n3_add_n7 C; have hsum := cycle_digit_counts_sum C; have hcases := m3_digit_cases h5 hsum
    have hD_fac := cycle_digitProd_factorization C; have hD_lt := cycle_digitProd_lt_two_pow C
    have hprod := cycle_prod_eq_nat C
    have hpx_pos : 0 < ∏ i : Fin 3, C.x i := Finset.prod_pos (fun i _ => C.x_pos i)
    have hfac : ∀ i : Fin 3,
        (if d (C.x i) = 1 then 11 else if d (C.x i) = 3 then 13 else
         if d (C.x i) = 5 then 15 else if d (C.x i) = 7 then 7 else 9) *
        (d (C.x i) * C.x i + 1) ≤
        (if d (C.x i) = 1 then 12 else if d (C.x i) = 3 then 40 else
         if d (C.x i) = 5 then 76 else if d (C.x i) = 7 then 50 else 82) * C.x i := by
      intro i; have hb := further_factor_bound (hge7 i) (C.x_odd i)
      rcases C.d_mem i with h | h | h | h | h
      · simpa [h] using hb.1 h
      · simpa [h] using hb.2.1 h
      · simpa [h] using hb.2.2.1 h
      · simpa [h] using hb.2.2.2.1 h
      · simpa [h] using hb.2.2.2.2 h
    have hmul_prod :
        (∏ i : Fin 3, (if d (C.x i) = 1 then 11 else if d (C.x i) = 3 then 13 else
          if d (C.x i) = 5 then 15 else if d (C.x i) = 7 then 7 else 9)) *
        (2 ^ C.totalHalvings) ≤
        ∏ i : Fin 3, (if d (C.x i) = 1 then 12 else if d (C.x i) = 3 then 40 else
          if d (C.x i) = 5 then 76 else if d (C.x i) = 7 then 50 else 82) := by
      have hle_p : ∏ i : Fin 3, ((if d (C.x i) = 1 then 11 else if d (C.x i) = 3 then 13 else
          if d (C.x i) = 5 then 15 else if d (C.x i) = 7 then 7 else 9) *
          (d (C.x i) * C.x i + 1)) ≤
          ∏ i : Fin 3, ((if d (C.x i) = 1 then 12 else if d (C.x i) = 3 then 40 else
          if d (C.x i) = 5 then 76 else if d (C.x i) = 7 then 50 else 82) * C.x i) :=
        Finset.prod_le_prod (fun i _ => hfac i)
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hprod, ← mul_assoc] at hle_p
      exact Nat.le_of_mul_le_mul_right hle_p hpx_pos
    have hden_eq : (∏ i : Fin 3, (if d (C.x i) = 1 then 11 else if d (C.x i) = 3 then 13 else
        if d (C.x i) = 5 then 15 else if d (C.x i) = 7 then 7 else 9)) =
        11 ^ C.n1 * 13 ^ C.n3 * 15 ^ C.n5 * 7 ^ C.n7 * 9 ^ C.n9 := by
      have hpt : ∀ i : Fin 3,
          (if d (C.x i) = 1 then 11 else if d (C.x i) = 3 then 13 else
           if d (C.x i) = 5 then 15 else if d (C.x i) = 7 then 7 else 9) =
          11 ^ (if d (C.x i) = 1 then 1 else 0) *
          13 ^ (if d (C.x i) = 3 then 1 else 0) *
          15 ^ (if d (C.x i) = 5 then 1 else 0) *
          7 ^ (if d (C.x i) = 7 then 1 else 0) *
          9 ^ (if d (C.x i) = 9 then 1 else 0) := by
        intro i; rcases C.d_mem i with h | h | h | h | h <;> simp [h]
      simp_rw [hpt]
      simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.sum_boole, Nat.cast_id]; rfl
    have hnum_eq : (∏ i : Fin 3, (if d (C.x i) = 1 then 12 else if d (C.x i) = 3 then 40 else
        if d (C.x i) = 5 then 76 else if d (C.x i) = 7 then 50 else 82)) =
        12 ^ C.n1 * 40 ^ C.n3 * 76 ^ C.n5 * 50 ^ C.n7 * 82 ^ C.n9 := by
      have hpt : ∀ i : Fin 3,
          (if d (C.x i) = 1 then 12 else if d (C.x i) = 3 then 40 else
           if d (C.x i) = 5 then 76 else if d (C.x i) = 7 then 50 else 82) =
          12 ^ (if d (C.x i) = 1 then 1 else 0) *
          40 ^ (if d (C.x i) = 3 then 1 else 0) *
          76 ^ (if d (C.x i) = 5 then 1 else 0) *
          50 ^ (if d (C.x i) = 7 then 1 else 0) *
          82 ^ (if d (C.x i) = 9 then 1 else 0) := by
        intro i; rcases C.d_mem i with h | h | h | h | h <;> simp [h]
      simp_rw [hpt]
      simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.sum_boole, Nat.cast_id]; rfl
    rw [hden_eq, hnum_eq] at hmul_prod
    rcases hcases with ⟨h1', h3', h5', h7', h9'⟩ | ⟨h1', h3', h5', h7', h9'⟩ |
      ⟨h1', h3', h5', h7', h9'⟩ | ⟨h1', h3', h5', h7', h9'⟩ |
      ⟨h1', h3', h5', h7', h9'⟩ | ⟨h1', h3', h5', h7', h9'⟩ |
      ⟨h1', h3', h5', h7', h9'⟩ | ⟨h1', h3', h5', h7', h9'⟩
    ·
      have hD1 : C.digitProd = 1 := by
        rw [hD_fac]; unfold OddCycle.aExp OddCycle.bExp OddCycle.cExp
        rw [h3', h5', h7', h9']; norm_num
      have hall := (cycle_all_ones_iff C).mp hD1; exact h1 ⟨0, (hall 0).1⟩
    ·
      rw [h1', h3', h5', h7', h9'] at hmul_prod; norm_num at hmul_prod
      have hD9 : C.digitProd = 9 := by
        rw [hD_fac]; unfold OddCycle.aExp OddCycle.bExp OddCycle.cExp
        rw [h3', h5', h7', h9']; norm_num
      rw [hD9] at hD_lt; have hle : 2 ^ C.totalHalvings ≤ 11 := by omega
      exact no_pow2_between (r := 3) (by norm_num) hD_lt hle (by norm_num)
    ·
      rw [h1', h3', h5', h7', h9'] at hmul_prod; norm_num at hmul_prod
      have hD81 : C.digitProd = 81 := by
        rw [hD_fac]; unfold OddCycle.aExp OddCycle.bExp OddCycle.cExp
        rw [h3', h5', h7', h9']; norm_num
      rw [hD81] at hD_lt; have hle : 2 ^ C.totalHalvings ≤ 91 := by omega
      exact no_pow2_between (r := 6) (by norm_num) hD_lt hle (by norm_num)
    ·
      rw [h1', h3', h5', h7', h9'] at hmul_prod; norm_num at hmul_prod
      have hD729 : C.digitProd = 729 := by
        rw [hD_fac]; unfold OddCycle.aExp OddCycle.bExp OddCycle.cExp
        rw [h3', h5', h7', h9']; norm_num
      rw [hD729] at hD_lt; have hle : 2 ^ C.totalHalvings ≤ 757 := by omega
      exact no_pow2_between (r := 9) (by norm_num) hD_lt hle (by norm_num)
    ·
      rw [h1', h3', h5', h7', h9'] at hmul_prod; norm_num at hmul_prod
      have hD15 : C.digitProd = 15 := by
        rw [hD_fac]; unfold OddCycle.aExp OddCycle.bExp OddCycle.cExp
        rw [h3', h5', h7', h9']; norm_num
      rw [hD15] at hD_lt; have hle : 2 ^ C.totalHalvings ≤ 17 := by omega
      have hK4 : C.totalHalvings = 4 := unique_pow2_between (r := 3) (by norm_num) hD_lt hle (by norm_num)
      have ht51_pos : 1 ≤ C.countTrans 5 1 := by
        have hex5 : ∃ i : Fin 3, d (C.x i) = 5 := by
          have hpos : 0 < (Finset.univ.filter (fun i : Fin 3 => d (C.x i) = 5)).card := by change 0 < C.n5; omega
          obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos; exact ⟨i, (Finset.mem_filter.mp hi).2⟩
        obtain ⟨i5, hi5⟩ := hex5
        have hnot5 : d (C.x (finNext C.hm i5)) ≠ 5 :=
          ((lem_last_digit_transition (C.x_odd i5) (C.x_odd (finNext C.hm i5))
            (C.k_pos i5) (C.step i5)).2.1 hi5).2.2.2.2
        have hnot7 : ∀ j : Fin 3, d (C.x j) ≠ 7 := by
          intro j hj
          have hmem : j ∈ Finset.univ.filter (fun i : Fin 3 => d (C.x i) = 7) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
          have : 0 < C.n7 := Finset.card_pos.mpr ⟨j, hmem⟩
          omega
        have hnot9 : ∀ j : Fin 3, d (C.x j) ≠ 9 := by
          intro j hj
          have hmem : j ∈ Finset.univ.filter (fun i : Fin 3 => d (C.x i) = 9) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
          have : 0 < C.n9 := Finset.card_pos.mpr ⟨j, hmem⟩
          omega
        have hnot3 : d (C.x (finNext C.hm i5)) ≠ 3 := by
          intro h3n
          have hnext5 : d (C.x (finNext C.hm (finNext C.hm i5))) = 5 :=
            (lem_last_digit_transition (C.x_odd _) (C.x_odd _) (C.k_pos _) (C.step _)).2.2
              (Or.inl h3n)
          have hne : finNext C.hm (finNext C.hm i5) ≠ i5 := by
            intro heq; have hval := congrArg Fin.val heq
            fin_cases i5 <;> simp [finNext] at hval
          have hge2 : 2 ≤ (Finset.univ.filter (fun i : Fin 3 => d (C.x i) = 5)).card := by
            have hsub : ({i5, finNext C.hm (finNext C.hm i5)} : Finset (Fin 3)) ⊆
                Finset.univ.filter (fun i : Fin 3 => d (C.x i) = 5) := by
              intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
              rcases hj with rfl | rfl <;> simp [hi5, hnext5]
            have hcard : ({i5, finNext C.hm (finNext C.hm i5)} : Finset (Fin 3)).card = 2 := Finset.card_pair hne.symm
            exact hcard ▸ Finset.card_le_card hsub
          change 2 ≤ C.n5 at hge2; omega
        have hd1n : d (C.x (finNext C.hm i5)) = 1 := by
          rcases C.d_mem (finNext C.hm i5) with h | h | h | h | h
          · exact h
          · exact absurd h hnot3
          · exact absurd h hnot5
          · exact absurd h (hnot7 _)
          · exact absurd h (hnot9 _)
        exact Finset.card_pos.mpr ⟨i5, Finset.mem_filter.mpr ⟨Finset.mem_univ i5, hi5, hd1n⟩⟩
      have hbud := lem_halving_budget_sharp C; omega
    ·
      rw [h1', h3', h5', h7', h9'] at hmul_prod; norm_num at hmul_prod
      have hD135 : C.digitProd = 135 := by
        rw [hD_fac]; unfold OddCycle.aExp OddCycle.bExp OddCycle.cExp
        rw [h3', h5', h7', h9']; norm_num
      rw [hD135] at hD_lt; have hle : 2 ^ C.totalHalvings ≤ 142 := by omega
      exact no_pow2_between (r := 7) (by norm_num) hD_lt hle (by norm_num)
    ·
      rw [h1', h3', h5', h7', h9'] at hmul_prod; norm_num at hmul_prod
      have hD35 : C.digitProd = 35 := by
        rw [hD_fac]; unfold OddCycle.aExp OddCycle.bExp OddCycle.cExp
        rw [h3', h5', h7', h9']; norm_num
      rw [hD35] at hD_lt; have hle : 2 ^ C.totalHalvings ≤ 40 := by omega
      exact no_pow2_between (r := 5) (by norm_num) hD_lt hle (by norm_num)
    ·
      rw [h1', h3', h5', h7', h9'] at hmul_prod; norm_num at hmul_prod
      have hD315 : C.digitProd = 315 := by
        rw [hD_fac]; unfold OddCycle.aExp OddCycle.bExp OddCycle.cExp
        rw [h3', h5', h7', h9']; norm_num
      rw [hD315] at hD_lt; have hle : 2 ^ C.totalHalvings ≤ 330 := by omega
      exact no_pow2_between (r := 8) (by norm_num) hD_lt hle (by norm_num)

/-! ## Section 7: Augusto Santi (2025) alternating 3-and-5 map comparison -/
/-- Augusto Santi's alternating 3-and-5 map on `(n, b) : ℕ × Bool` (`false` = multiply odd `n` by `3`, `true` = -/
def santiStep (st : ℕ × Bool) : ℕ × Bool :=
  if st.1 % 2 = 0 then (st.1 / 2, st.2)
  else ((if st.2 then 5 else 3) * st.1 + 1, !st.2)
/-- Santi's "cycle A" `5 → 26 → 13 → 40 → 20 → 10 → 5` is a 6-cycle of both `santiStep` and `f = f_10`, matching -/
theorem santi_cycleA_shared :
    santiStep^[6] (5, true) = (5, true) ∧
    f^[6] 5 = 5 ∧
    ∀ j : Fin 6, (santiStep^[j.val] (5, true)).1 = f^[j.val] 5 := by
  refine ⟨by decide, by decide, ?_⟩
  intro j; fin_cases j <;> decide
/-- Santi's "cycle B" `7 → 22 → 11 → 56 → 28 → 14 → 7` is a 6-cycle of `santiStep`, but NOT a cycle of `f = f_10` -/
theorem santi_cycleB_not_ouroboros :
    santiStep^[6] (7, false) = (7, false) ∧
    (santiStep (7, false)).1 = 22 ∧
    f 7 = 50 ∧
    f^[40] 7 = 5 := by
  refine ⟨by decide, by decide, by decide, by decide⟩
/-- Santi's "cycle C" `7 → 36 → 18 → 9 → 28 → 14 → 7` is a 6-cycle of `santiStep`, but NOT a cycle of `f = f_10` -/
theorem santi_cycleC_not_ouroboros :
    santiStep^[6] (7, true) = (7, true) ∧
    (santiStep (7, true)).1 = 36 ∧
    f 7 = 50 := by
  refine ⟨by decide, by decide, by decide⟩
/-- The Ouroboros trivial 2-cycle `1 → 2 → 1` is NOT a 2-cycle of `santiStep` for either initial parity flag. -/
theorem ouroboros_cycle1_not_santi :
    f^[2] 1 = 1 ∧
    santiStep^[2] (1, false) ≠ (1, false) ∧
    santiStep^[2] (1, true) ≠ (1, true) := by
  refine ⟨by decide, by decide, by decide⟩

end Ouroboros
