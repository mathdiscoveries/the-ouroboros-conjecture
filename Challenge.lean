module

public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.Nat
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Palomar Challenge: The Ouroboros Conjecture: Competing Attractors in Base 10 Among Last-Digit Collatz Maps
Defines the base-`b` last-digit Collatz map `f_b`, the base-10 Ouroboros map `f = f_b 10`,
the open conjecture `OuroborosConjecture`, the basin counting functions `N1`, `N1All`, `N5`,
`N5All`, the Terras exceptional sets `E_k` and `NoDescent`, the even-base Markov drift
and stopping-density predicates (`HasStationaryDriftIn`, `AllStationaryDriftsSatisfy`,
`D_k`, `DescentSet`, `p_k`, `p_infty`), the odd-base trapdoor, attraction, divergence, and
Markov absorption predicates (`ZSet`, `RSet`, `DivSet`, `OddCyl`, `cylStep`, `oddTrapMass`,
`oddRunMass`), the base-10 odd-cycle structure `OddCycle`, the inverse-tree charging
structure (`TypeId`, `movesOf`, `childType`, `NTree`), the `2`-adic Cantor closure
(`B1Padic`, `KCal`, `HasBoxDim`), and the reversed base-`b` suffix closures
(`suffixClosure1`, `suffixClosure5`, `boxCoverNumber`), together with 38 compared theorems
covering 15 of 16 proved main results of the companion paper.
-/

@[expose] public section

open scoped Topology ENNReal

namespace OuroborosChallenge
/-- Last base-`b` digit of `n`. -/
def d_b (b n : ℕ) : ℕ := n % b
/-- Base-`b` last-digit Collatz map: `n / 2` for even `n`, `(n % b) * n + 1` for odd `n`. -/
def f_b (b n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (n % b) * n + 1
/-- Base-10 Ouroboros map `f = f_b 10`. -/
def f (n : ℕ) : ℕ := f_b 10 n
/-- Last decimal digit `d(n) = n % 10`. -/
def d (n : ℕ) : ℕ := n % 10
/-- Shortcut map `T`: `n / 2` for even `n`, `(d(n) * n + 1) / 2` for odd `n`. -/
def T (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (d n * n + 1) / 2
/-- Classical Collatz shortcut map `T_C`. -/
def T_C (y : ℕ) : ℕ :=
  if y % 2 = 0 then y / 2 else (3 * y + 1) / 2
/-- Orbit of `n` under `g` reaches `m`. -/
def Reaches (g : ℕ → ℕ) (n m : ℕ) : Prop :=
  ∃ k : ℕ, g^[k] n = m
/-- Formal statement of the open Ouroboros Conjecture: every positive integer reaches `1` or `5` under `f_b 10`. -/
def OuroborosConjecture : Prop :=
  ∀ n : ℕ, 0 < n → Reaches (f_b 10) n 1 ∨ Reaches (f_b 10) n 5
open Classical in
/-- Count of odd integers `n ≤ X` whose orbit under `f` reaches `1`. -/
noncomputable def N1 (X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun n => n % 2 = 1 ∧ Reaches f n 1)).card
open Classical in
/-- Count of all positive integers `n ≤ X` whose orbit under `f` reaches `1`. -/
noncomputable def N1All (X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun n => Reaches f n 1)).card
open Classical in
/-- Count of odd integers `n ≤ X` whose orbit under `f` reaches `5`. -/
noncomputable def N5 (X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun n => n % 2 = 1 ∧ Reaches f n 5)).card
open Classical in
/-- Count of all positive integers `n ≤ X` whose orbit under `f` reaches `5`. -/
noncomputable def N5All (X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun n => Reaches f n 5)).card
/-- Terras exceptional set `E_k = {n ≥ 2 | ∀ 1 ≤ j ≤ k, T^[j] n ≥ n}`. -/
def E_k (k : ℕ) : Set ℕ :=
  {n | 2 ≤ n ∧ ∀ j, 1 ≤ j → j ≤ k → n ≤ T^[j] n}
/-- Integers `n ≥ 2` with no `f`-iterate strictly below `n`. -/
def NoDescent : Set ℕ :=
  {n | 2 ≤ n ∧ ∀ m : ℕ, 1 ≤ m → n ≤ f^[m] n}
open Classical in
/-- Count of integers in `[1, N]` belonging to `S`. -/
noncomputable def countUpTo (S : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => n ∈ S)).card
/-- Odd digit `2 * i + 1 ∈ [1, 4k)` indexed by `i : Fin (2 * k)`. -/
def digit4k {k : ℕ} (i : Fin (2 * k)) : ℕ := 2 * i.val + 1
/-- First transition of `P_{4k}` on odd residues mod `4k`. -/
def next4kA (k : ℕ) (hk : 1 ≤ k) (i : Fin (2 * k)) : Fin (2 * k) :=
  let r := digit4k i; let c := ((r * r + 1) / 2) % (4 * k)
  ⟨c / 2, Nat.div_lt_of_lt_mul
    (Nat.lt_of_lt_of_eq (Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 3) (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)))
      (Nat.mul_assoc 2 2 k))⟩
/-- Second transition of `P_{4k}` on odd residues mod `4k`. -/
def next4kB (k : ℕ) (hk : 1 ≤ k) (i : Fin (2 * k)) : Fin (2 * k) :=
  let r := digit4k i; let c := (((r * r + 1) / 2) + 2 * k) % (4 * k)
  ⟨c / 2, Nat.div_lt_of_lt_mul
    (Nat.lt_of_lt_of_eq (Nat.mod_lt _ (Nat.mul_pos (Nat.succ_pos 3) (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)))
      (Nat.mul_assoc 2 2 k))⟩
/-- Odd-step Markov operator `P_{4k}` on `Fin (2 * k)`. -/
noncomputable def P4kOp (k : ℕ) (hk : 1 ≤ k) (g : Fin (2 * k) → ℝ) (i : Fin (2 * k)) : ℝ :=
  (1 / 2 : ℝ) * (g (next4kA k hk i) + g (next4kB k hk i))
/-- Stationarity for `P_{4k}`. -/
def IsStationary4k (k : ℕ) (hk : 1 ≤ k) (π : Fin (2 * k) → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧ (∑ i : Fin (2 * k), π i = 1) ∧
  (∀ g : Fin (2 * k) → ℝ,
    ∑ i : Fin (2 * k), π i * P4kOp k hk g i = ∑ i : Fin (2 * k), π i * g i)
/-- Drift of a law `π` on `P_{4k}`: `E_π[ln D - ln 2]`. -/
noncomputable def drift4k {k : ℕ} (π : Fin (2 * k) → ℝ) : ℝ :=
  ∑ i : Fin (2 * k), π i * (Real.log (digit4k i : ℝ) - Real.log 2)
/-- Unique odd digit in `[1, 2M)` congruent to `y (mod M)` for odd `M`. -/
def oddDigitNat (M y : Nat) : Nat :=
  match Nat.beq (y % 2) 1 with
  | true => y
  | false => y + M
/-- Halving step modulo odd `M`. -/
def hStepNat (M y : Nat) : Nat := (y * ((M + 1) / 2)) % M
/-- Odd-step transition `((d(y)^2 + 1) / 2) mod M` for odd `M`. -/
def qStepNat (M y : Nat) : Nat :=
  let d := oddDigitNat M y
  ((d * d + 1) / 2) % M
/-- Odd digit for `y : Fin M` in base `2M`. -/
def oddDigit2M (M : ℕ) (y : Fin M) : ℕ := oddDigitNat M y.val
/-- Halving operator `H` on `Fin M`. -/
def hStep2M (M : ℕ) (hM : 1 ≤ M) (y : Fin M) : Fin M :=
  ⟨hStepNat M y.val, Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)⟩
/-- Odd-step operator `Q` on `Fin M`. -/
def qStep2M (M : ℕ) (hM : 1 ≤ M) (y : Fin M) : Fin M :=
  ⟨qStepNat M y.val, Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)⟩
/-- Full odd-to-odd Markov operator `P_{2M}` on `Fin M`. -/
noncomputable def P2MOp (M : ℕ) (hM : 1 ≤ M) (g : Fin M → ℝ) (y : Fin M) : ℝ :=
  ∑' v : ℕ, (2 : ℝ) ^ (-(v + 1 : ℤ)) * g ((hStep2M M hM)^[v] (qStep2M M hM y))
/-- Stationarity for `P_{2M}`. -/
def IsStationary2M (M : ℕ) (hM : 1 ≤ M) (π : Fin M → ℝ) : Prop :=
  (∀ y, 0 ≤ π y) ∧ (∑ y : Fin M, π y = 1) ∧
  (∀ g : Fin M → ℝ, ∑ y : Fin M, π y * P2MOp M hM g y = ∑ y : Fin M, π y * g y)
/-- Drift of a law `π` on `P_{2M}`: `E_π[ln D - 2 ln 2]`. -/
noncomputable def drift2M (M : ℕ) (π : Fin M → ℝ) : ℝ :=
  ∑ y : Fin M, π y * (Real.log (oddDigit2M M y : ℝ) - 2 * Real.log 2)
/-- Even base `b` admits a stationary law whose drift satisfies predicate `P`. -/
def HasStationaryDriftIn (b : ℕ) (P : ℝ → Prop) : Prop :=
  if 4 ∣ b then
    ∃ (hk : 1 ≤ b / 4) (π : Fin (2 * (b / 4)) → ℝ),
      IsStationary4k (b / 4) hk π ∧ P (drift4k π)
  else
    ∃ (hM : 1 ≤ b / 2) (π : Fin (b / 2) → ℝ),
      IsStationary2M (b / 2) hM π ∧ P (drift2M (b / 2) π)
/-- Every stationary law of even base `b` has drift satisfying `P`. -/
def AllStationaryDriftsSatisfy (b : ℕ) (P : ℝ → Prop) : Prop :=
  if 4 ∣ b then
    ∀ (hk : 1 ≤ b / 4) (π : Fin (2 * (b / 4)) → ℝ),
      IsStationary4k (b / 4) hk π → P (drift4k π)
  else
    ∀ (hM : 1 ≤ b / 2) (π : Fin (b / 2) → ℝ),
      IsStationary2M (b / 2) hM π → P (drift2M (b / 2) π)
/-- Odd-base trapdoor set: positive integers whose `f_b`-orbit hits a multiple of `b`. -/
def ZSet (b : ℕ) : Set ℕ := {n | 1 ≤ n ∧ ∃ j : ℕ, b ∣ (f_b b)^[j] n}
/-- Finite density fraction `|S ∩ [1, N]| / N`. -/
noncomputable def countFrac (S : Set ℕ) (N : ℕ) : ℝ :=
  open Classical in (((Finset.Icc 1 N).filter (· ∈ S)).card : ℝ) / (N : ℝ)
/-- Cyclic successor on `Fin m`. -/
def finNext {m : ℕ} (hm : 0 < m) (i : Fin m) : Fin m := ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩
/-- An `m`-odd-member cycle of `f = f_10`. -/
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
def totalHalvings : ℕ := ∑ i : Fin m, C.k i
def countDigit (dig : ℕ) : ℕ := (Finset.univ.filter (fun i : Fin m => d (C.x i) = dig)).card
def n1 : ℕ := C.countDigit 1
def n3 : ℕ := C.countDigit 3
def n5 : ℕ := C.countDigit 5
def n7 : ℕ := C.countDigit 7
def n9 : ℕ := C.countDigit 9
def aExp : ℕ := C.n3 + 2 * C.n9
def bExp : ℕ := C.n5
def cExp : ℕ := C.n7
end OddCycle
/-- Base-4 conjugacy: `2y + 1` reaches `3` under `f_4` iff `y` reaches `1` under shortcut Collatz `T_C`. -/
theorem prop_base4_reaches_three_iff (y : ℕ) :
    Reaches (f_b 4) (2 * y + 1) 3 ↔ Reaches T_C y 1 := by sorry
/-- Base-4 universal attraction to `{1, 3}` is equivalent to the classical Collatz conjecture. -/
theorem prop_base4_iff_collatz :
    (∀ n : ℕ, 0 < n → Reaches (f_b 4) n 1 ∨ Reaches (f_b 4) n 3) ↔
    (∀ y : ℕ, 0 < y → Reaches T_C y 1) := by sorry
/-- In base `2`, every positive integer reaches `1`. -/
theorem prop_base2_reaches_one (n : ℕ) (hn : 0 < n) : Reaches (f_b 2) n 1 := by sorry
/-- In base `5`, every positive integer reaches `1`. -/
theorem prop_base5_reaches_one (n : ℕ) (hn : 0 < n) : Reaches (f_b 5) n 1 := by sorry
/-- Quantitative exponential Terras descent bound in base `10`. -/
theorem thm_terras_bound (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (countUpTo (E_k k) N : ℝ) / (N : ℝ) ≤
        (1124953 / 1000000 : ℝ) * (996423 / 1000000 : ℝ) ^ k + ε := by sorry
/-- Natural density-one descent in base `10`. -/
theorem thm_terras_density_one (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (countUpTo NoDescent N : ℝ) / (N : ℝ) ≤ ε := by sorry
/-- Modulo-30 residue law for odd integers in the basin of `1`. -/
theorem thm_residue_law {n : ℕ} (hn : n % 2 = 1) (h : Reaches f n 1) :
    n % 30 = 1 ∨ n % 30 = 15 ∨ n % 30 = 17 := by sorry
/-- Basin-of-1 lower power-law bound `N1(X) ≥ c * X^γ` with `a₁ + a₁^4 = 1`, `γ = log₂(1 / a₁)`. -/
theorem thm_basin1_lower :
    ∃ a₁ : ℝ, 0 < a₁ ∧ a₁ < 1 ∧ a₁ + a₁ ^ 4 = 1 ∧
      ∃ c : ℝ, 0 < c ∧ ∀ X : ℕ, 1 ≤ X →
        c * (X : ℝ) ^ (Real.logb 2 (1 / a₁)) ≤ (N1 X : ℝ) := by sorry
/-- Explicit basin-of-1 upper bound `N1(X) ≤ 2.44 * X^0.626383` for all `X ≥ 1`. -/
theorem thm_basin1_upper_explicit (X : ℕ) (hX : 1 ≤ X) :
    (N1 X : ℝ) ≤ (244 / 100 : ℝ) * (X : ℝ) ^ ((626383 : ℝ) / 1000000) := by sorry
/-- Basin of `1` has natural density `0`. -/
theorem thm_basin1_density_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → (N1All X : ℝ) / (X : ℝ) ≤ ε := by sorry
/-- Unconditional basin-of-5 lower bound `N5(X) ≥ 0.000605 * X^0.65` for all `X ≥ 3` (`Q = 14175` kernel certificate). -/
theorem thm_basin5_tight (X : ℕ) (hX : 3 ≤ X) :
    (605 / 1000000 : ℝ) * (X : ℝ) ^ ((65 : ℝ) / 100) ≤ (N5 X : ℝ) := by sorry
/-- Unconditional explicit basin separation bound `N1(X) / N5(X) ≤ C * X^{-0.0236}` for all `X ≥ 3`. -/
theorem cor_basin_separation_unconditional (X : ℕ) (hX : 3 ≤ X) :
    (N1 X : ℝ) / (N5 X : ℝ) ≤
      ((244 / 100 : ℝ) / (10766 / 100000000 : ℝ)) * (X : ℝ) ^ (-(236 / 10000 : ℝ)) := by sorry
/-- Strict asymptotic basin separation: `N1(X) / N5(X) → 0` and `N1All(X) / N5All(X) → 0`. -/
theorem cor_basin_separation_tendsto_zero_unconditional (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (N1 X : ℝ) / (N5 X : ℝ) ≤ ε ∧ (N1All X : ℝ) / (N5All X : ℝ) ≤ ε := by sorry
/-- Complete even-base drift sign classification: nonpositive stationary drift iff `b ∈ {2, 4, 6, 10}`. -/
theorem thm_even_bases {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) :
    HasStationaryDriftIn b (· ≤ 0) ↔ b = 2 ∨ b = 4 ∨ b = 6 ∨ b = 10 := by sorry
/-- Near-zero drift band classification: `|drift| ≤ 1/4` iff `b ∈ {4, 8, 10, 14}`; `[-1/4, 0)` iff `b ∈ {4, 10}`. -/
theorem prop_near_zero_band {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) :
    (HasStationaryDriftIn b (fun x => -(1 / 4 : ℝ) ≤ x ∧ x ≤ 1 / 4) ↔
      b = 4 ∨ b = 8 ∨ b = 10 ∨ b = 14) ∧
    (HasStationaryDriftIn b (fun x => -(1 / 4 : ℝ) ≤ x ∧ x < 0) ↔
      b = 4 ∨ b = 10) := by sorry
/-- Universal logarithmic drift growth across all even bases `b ≥ 2`. -/
theorem cor_drift_growth {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) :
    AllStationaryDriftsSatisfy b
      (fun x => (1 / 2 : ℝ) * Real.log ((b : ℝ) + 2) - (7 / 2 : ℝ) * Real.log 2 ≤ x) := by sorry
/-- Odd-base even-digit runaway divergence theorem. -/
theorem prop_odd_runaway {b : ℕ} (hb : b % 2 = 1) (S : Set ℕ)
    (hS_even : ∀ d ∈ S, d % 2 = 0 ∧ 2 ≤ d)
    (hS_closed : ∀ d ∈ S, (d * d + 1) % b ∈ S)
    {n : ℕ} (hn_odd : n % 2 = 1) (hn_S : n % b ∈ S) :
    ∀ k : ℕ, ((f_b b)^[k] n) % 2 = 1 ∧
             ((f_b b)^[k] n) % b ∈ S ∧
             2 ^ k * n ≤ (f_b b)^[k] n := by sorry
/-- Rootless odd-base trapdoor characterization whenever `p ∣ b` with prime `p ≡ 3 (mod 4)`. -/
theorem thm_odd_trapdoor_rootless {b p : ℕ} (hb_odd : b % 2 = 1)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3) (hpb : p ∣ b) :
    (∀ x : ℕ, (x * x + 1) % b ≠ 0) ∧
    (∀ n : ℕ, n ∈ ZSet b ↔ 1 ≤ n ∧ b ∣ n) := by sorry
/-- Certified base-17 runaway divergence for every odd `n ≡ 16 (mod 17)`. -/
theorem lem_base17_runaway {n : ℕ} (hn1 : 1 ≤ n) (hn_odd : n % 2 = 1) (hn17 : n % 17 = 16) :
    (∀ i : ℕ, ¬ 17 ∣ (f_b 17)^[i] n ∧ (f_b 17)^[i] n ≠ 1) ∧
    (∀ i : ℕ, (f_b 17)^[i] n < (f_b 17)^[i + 10] n) ∧
    Filter.Tendsto (fun i => (f_b 17)^[i] n) Filter.atTop Filter.atTop := by sorry
/-- Exact trapdoor density `1 / b` for rootless odd bases (`p ∣ b`, `p ≡ 3 (mod 4)`). -/
theorem thm_odd_densities_rootless {b p : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3) (hpb : p ∣ b) :
    Filter.Tendsto (countFrac (ZSet b)) Filter.atTop (nhds (1 / (b : ℝ))) := by sorry
/-- Exact digit-count cancellation law `n_5 = n_3 + n_7` for every base-10 odd cycle. -/
theorem cycle_n5_eq_n3_add_n7 {m : ℕ} (C : OddCycle m) :
    C.n5 = C.n3 + C.n7 := by sorry
/-- Halving-budget lower bounds for every base-10 odd cycle. -/
theorem lem_halving_budget {m : ℕ} (C : OddCycle m) :
    C.n1 + 2 * C.n3 + 4 * C.n7 + 3 * C.n9 ≤ C.totalHalvings ∧
      2 * C.n1 + 3 * C.aExp + C.bExp + 7 * C.cExp ≤ 2 * C.totalHalvings := by sorry
/-- High-halving cycle tail bound at threshold `10^15`: `K > 64000` forces `m ≥ 20190` and `K + m ≥ 84191`. -/
theorem thm_cycle_tail_64000 {m : ℕ} (C : OddCycle m)
    (hmin : ∀ i : Fin m, 10 ^ 15 ≤ C.x i) (hK : 64000 < C.totalHalvings) :
    20190 ≤ m ∧ 84191 ≤ C.totalHalvings + m := by sorry
/-- Unconditional uniqueness of `1`-odd-member base-10 cycles (`1 → 2 → 1`). -/
theorem cycle_m1_unique (C : OddCycle 1) : C.x 0 = 1 ∧ C.k 0 = 1 := by sorry
/-- Unconditional classification of all `2`-odd-member base-10 cycles (`{1}` or `{5, 13}`). -/
theorem cycle_m2_classification (C : OddCycle 2) :
    (C.x 0 = 1 ∧ C.x 1 = 1 ∧ C.k 0 = 1 ∧ C.k 1 = 1) ∨
    (C.x 0 = 5 ∧ C.x 1 = 13 ∧ C.k 0 = 1 ∧ C.k 1 = 3) ∨
    (C.x 0 = 13 ∧ C.x 1 = 5 ∧ C.k 0 = 3 ∧ C.k 1 = 1) := by sorry
/-- Unconditional uniqueness of `3`-odd-member base-10 cycles (no further cycle with `3` odd members). -/
theorem cycle_m3_unique (C : OddCycle 3) :
    ∀ i : Fin 3, C.x i = 1 ∧ C.k i = 1 := by sorry
/-- Non-vacuity check: `1 → 2 → 1` is a `2`-step cycle of `f`. -/
theorem f_cycle_one : f^[2] 1 = 1 := by sorry
/-- Non-vacuity check: `5 → 26 → 13 → 40 → 20 → 10 → 5` is a `6`-step cycle of `f`. -/
theorem f_cycle_five : f^[6] 5 = 5 := by sorry

/-! ## Additional Definitions for Weighted Tree Charging, Even-Base Stopping Dichotomy, 2-adic Cantor Closure, and Suffix Dimension -/

/-- The five odd decimal digits indexed by `Fin 5`. -/
def digitVal (i : Fin 5) : ℕ :=
  match i.val with
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | _ => 9
/-- Proof term that every odd decimal digit is positive. -/
lemma digitValPos (i : Fin 5) : 0 < digitVal i :=
  Fin.cases (motive := fun j : Fin 5 => 0 < digitVal j) Nat.zero_lt_one
    (Fin.cases (Nat.succ_pos 2)
      (Fin.cases (Nat.succ_pos 4)
        (Fin.cases (Nat.succ_pos 6)
          (Fin.cases (Nat.succ_pos 8) (fun j => j.elim0))))) i
/-- Proof term that every odd decimal digit divides `1575`. -/
lemma digitValDvd1575 (i : Fin 5) : digitVal i ∣ 1575 :=
  Fin.cases (motive := fun j : Fin 5 => digitVal j ∣ 1575) ⟨1575, rfl⟩
    (Fin.cases ⟨525, rfl⟩
      (Fin.cases ⟨315, rfl⟩
        (Fin.cases ⟨225, rfl⟩
          (Fin.cases ⟨175, rfl⟩ (fun j => j.elim0))))) i
/-- Decidable predecessor congruence condition on `x = 2^v * o` for digit `digitVal i`. -/
def predCondBool (i : Fin 5) (x : ℕ) : Bool :=
  match i.val with
  | 0 => x % 5 == 2
  | 1 => (x % 5 == 0) && (x % 3 == 1)
  | 2 => x % 25 == 1
  | 3 => (x % 5 == 0) && (x % 7 == 1)
  | _ => (x % 5 == 2) && (x % 9 == 1)
/-- Residue type `(i, ρ)` with modulus `Q / digitVal i`. -/
abbrev TypeId (Q : ℕ) := Σ i : Fin 5, Fin (Q / digitVal i)
/-- Allowed moves `(i, vc)` from residue `R mod Q` with `v = vc.val + 1 ≤ P`. -/
def movesOf (Q P : ℕ) (R : Fin Q) : Finset (Fin 5 × Fin P) :=
  Finset.univ.filter fun mv => predCondBool mv.1 (2 ^ (mv.2.val + 1) * R.val)
/-- Child type produced by move `mv` from residue `R mod Q`. -/
def childType (Q P : ℕ) (hQ : 1575 ∣ Q) (hQpos : 0 < Q) (R : Fin Q) (mv : Fin 5 × Fin P) : TypeId Q :=
  let d := digitVal mv.1
  let r' := ((2 ^ (mv.2.val + 1) * R.val + Q - 1) % Q) / d
  ⟨mv.1, ⟨r', (Nat.div_lt_iff_lt_mul (digitValPos mv.1)).mpr
    (Nat.lt_of_lt_of_eq (Nat.mod_lt _ hQpos) (Nat.div_mul_cancel (Nat.dvd_trans (digitValDvd1575 mv.1) hQ)).symm)⟩⟩
open Classical in
/-- Count of odd integers `m ≤ X` whose forward orbit under `f` visits `o`. -/
noncomputable def NTree (o X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun m => m % 2 = 1 ∧ Reaches f m o)).card
/-- Terras shortcut map `T_b` for even base `b ≥ 2`. -/
def T_b (b n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else ((n % b) * n + 1) / 2
/-- Affine pair `(A_j, B_j)` along the `T_b`-orbit of `n`: `2^j * T_b^j(n) = A_j * n + B_j`. -/
def affAB (b n : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | j + 1 =>
    let (A, B) := affAB b n j
    let x := (T_b b)^[j] n
    if x % 2 = 0 then (A, B) else ((x % b) * A, (x % b) * B + 2 ^ j)
/-- Finite-horizon non-descent set `D_k(b) = {n ≥ 1 | ∀ 1 ≤ j ≤ k, T_b^j(n) ≥ n}`. -/
def D_k (b k : ℕ) : Set ℕ :=
  {n | 1 ≤ n ∧ ∀ j, 1 ≤ j → j ≤ k → n ≤ (T_b b)^[j] n}
/-- Positive integers eventually descending strictly below their starting value under `f_b`. -/
def DescentSet (b : ℕ) : Set ℕ :=
  {n | 1 ≤ n ∧ ∃ m : ℕ, 1 ≤ m ∧ (f_b b)^[m] n < n}
/-- Exact natural density `d(S) = lim_{N → ∞} |S ∩ [1, N]| / N`. -/
def HasNaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun N : ℕ => (countUpTo S N : ℝ) / (N : ℝ)) Filter.atTop (nhds d)
/-- Surviving residue classes modulo `b * 2^(k - 1)` for horizon `k ≥ 1`. -/
def SurvRes (b k : ℕ) : Finset (Fin (b * 2 ^ (k - 1))) :=
  Finset.univ.filter fun r => ∀ j : Fin k, 2 ^ (j.val + 1) < (affAB b r.val (j.val + 1)).1
/-- Exact finite-horizon non-descent density `p_k(b)`. -/
noncomputable def p_k (b k : ℕ) : ℝ :=
  ((SurvRes b k).card : ℝ) / ((b * 2 ^ (k - 1) : ℕ) : ℝ)
/-- Limiting non-descent density `p_infty(b) = inf_{k ≥ 1} p_k(b)`. -/
noncomputable def p_infty (b : ℕ) : ℝ :=
  ⨅ k : ℕ, p_k b (k + 1)
/-- Full basin of `1` under `f`. -/
def InBasin1 (n : ℕ) : Prop := Reaches f n 1
/-- Full basin of `5` under `f`. -/
def InBasin5 (n : ℕ) : Prop := Reaches f n 5
/-- Admissible odd residues `{1, 15, 17} (mod 30)` for the basin of `1`. -/
def InABC (n : ℕ) : Prop := n % 30 = 1 ∨ n % 30 = 15 ∨ n % 30 = 17
/-- Allowed residue modulo `30`: either even or in `{1, 15, 17} (mod 30)`. -/
def AllowedMod30 (n : ℕ) : Prop := n % 2 = 0 ∨ InABC n
/-- Survival predicate: `T^[j](30k + r)` stays allowed modulo `30` for all `j ≤ h`. -/
def Survives (r h k : ℕ) : Prop := ∀ j ≤ h, AllowedMod30 (T^[j] (30 * k + r))
/-- Odd integer starting in `{1, 15, 17} (mod 30)` that stays allowed until exiting at `19` or `23 (mod 30)` at some step `j ≥ 1`. -/
def ExitsAt19Or23 (n : ℕ) : Prop :=
  InABC n ∧ ∃ j : ℕ, 1 ≤ j ∧ (∀ i < j, AllowedMod30 (T^[i] n)) ∧
    (T^[j] n % 30 = 19 ∨ T^[j] n % 30 = 23)
/-- Odd basin of `1` embedded in the `2`-adic integers `ℤ_[2]`. -/
def B1Padic : Set ℤ_[2] := {x | ∃ n : ℕ, (n % 2 = 1 ∧ Reaches f n 1) ∧ (n : ℤ_[2]) = x}
/-- Sheet coordinate set `K_r = {k ≥ 0 | 30k + r ∈ B_1}` embedded in `ℤ_[2]`. -/
def KrPadic (r : ℕ) : Set ℤ_[2] := {x | ∃ k : ℕ, ((30 * k + r) % 2 = 1 ∧ Reaches f (30 * k + r) 1) ∧ (k : ℤ_[2]) = x}
/-- Compact `2`-adic survival shell `𝒦_r ⊂ ℤ_[2]`. -/
def KCal (r : ℕ) : Set ℤ_[2] := {x | ∀ h : ℕ, Survives r h (x.appr h)}
/-- Affine sheet embedding `k ↦ 30k + r` on `ℤ_[2]`. -/
noncomputable def affine30 (r : ℕ) (x : ℤ_[2]) : ℤ_[2] := 30 * x + (r : ℤ_[2])
/-- Prepending a finite bit prefix `p` to an infinite bit sequence `x : ℕ → Bool`. -/
def prependBits (p : List Bool) (x : ℕ → Bool) : ℕ → Bool :=
  fun j => if h : j < p.length then p[j] else x (j - p.length)
/-- Prefix-code Cantor set `Σ = {0, 1000, 1001}^ω ⊂ {0, 1}^ℕ`. -/
def SigmaBits : Set (ℕ → Bool) :=
  {x | ∃ pos : ℕ → ℕ, pos 0 = 0 ∧ ∀ i : ℕ,
    (pos (i + 1) = pos i + 1 ∧ x (pos i) = false) ∨
    (pos (i + 1) = pos i + 4 ∧ x (pos i) = true ∧ x (pos i + 1) = false ∧ x (pos i + 2) = false)}
/-- Image of `𝒦_15`: disjoint union `000 Σ ⊔ 001 Σ`. -/
def Sigma15Bits : Set (ℕ → Bool) :=
  (prependBits [false, false, false] '' SigmaBits) ∪ (prependBits [false, false, true] '' SigmaBits)
/-- Halving-itinerary map `Ψ_r : ℤ_[2] → {0, 1}^ℕ` recording the parity of `⌊T^j(30 x + r) / 30⌋`. -/
noncomputable def itin (r : ℕ) (x : ℤ_[2]) (j : ℕ) : Bool :=
  decide ((T^[j] (30 * x.appr (j + 1) + r) / 30) % 2 = 1)
/-- Minimum cardinality of a finite cover of `s` with sets of extended diameter `≤ ε`. -/
noncomputable def boxCoverNum {X : Type*} [PseudoEMetricSpace X] (s : Set X) (ε : ℝ) : ℕ :=
  sInf {N : ℕ | ∃ F : Finset (Set X), F.card = N ∧ s ⊆ ⋃ U ∈ F, U ∧
    ∀ U ∈ F, Metric.ediam U ≤ ENNReal.ofReal ε}
/-- Exact box-counting (Minkowski) dimension `lim_{ε → 0^+} log N(s, ε) / log(1 / ε) = d`. -/
def HasBoxDim {X : Type*} [PseudoEMetricSpace X] (s : Set X) (d : ℝ) : Prop :=
  Filter.Tendsto (fun ε : ℝ => Real.log (boxCoverNum s ε : ℝ) / Real.log (1 / ε))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds d)
/-- The 8 live residues modulo `30` under the base-10 shortcut automaton. -/
def liveMod30 : Finset ℕ := {0, 1, 2, 4, 8, 15, 16, 17}
/-- Exact `2`-adic exponent `h = max(0, v_2(m) - 1)` for congruence-class completions. -/
def suffixH (m : ℕ) : ℕ := m.factorization 2 - 1
/-- Modulus `M = 30 * 2^h` of the congruence-class completion criterion. -/
def suffixM (m : ℕ) : ℕ := 30 * 2 ^ suffixH m
/-- Compatibility modulus `p = gcd(m, 30 * 2^h)`. -/
def suffixP (m : ℕ) : ℕ := Nat.gcd m (suffixM m)
/-- The `j`-th base-`b` digit of `n` (units digit at `j = 0`). -/
def baseDigit (b j n : ℕ) : ℕ := (n / b ^ j) % b
/-- Reversed base-`b` fractional expansion `∑_{j ≥ 0} d_j(n) b^{-(j+1)} ∈ [0, 1]`. -/
noncomputable def revExp (b n : ℕ) : ℝ :=
  ∑' j : ℕ, (baseDigit b j n : ℝ) / (b : ℝ) ^ (j + 1)
/-- Reversed base-`b` suffix closure `ℰ_b ⊂ [0, 1]` of the full basin of `1`. -/
def suffixClosure1 (b : ℕ) : Set ℝ :=
  closure (revExp b '' {n : ℕ | 0 < n ∧ InBasin1 n})
/-- Reversed base-`b` suffix closure `ℰ_{5,b} ⊂ [0, 1]` of the full basin of `5`. -/
def suffixClosure5 (b : ℕ) : Set ℝ :=
  closure (revExp b '' {n : ℕ | 0 < n ∧ InBasin5 n})
/-- Minimum cardinality of a finite cover of `E ⊆ ℝ` with sets of diameter `≤ δ`. -/
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

/-! ## Additional Compared Headline Theorems (7 new main results; 35 total) -/

/-- Individual child-weight charging inequality on the inverse tree of `3` (Lemma 20). -/
theorem lem_weighted_tree3
    {Q Vmax : ℕ} (hQ1575 : 1575 ∣ Q) (hQpos : 0 < Q)
    {s L : ℝ} (hs : 0 < s) (hL : 0 < L)
    (w : TypeId Q → ℝ) (hw_nn : ∀ t, 0 ≤ w t)
    (hexpand : ∀ (t : TypeId Q) (R : Fin Q),
      R.val % (Q / digitVal t.1) = t.2.val →
      w t ≤ ∑ mv ∈ movesOf Q Vmax R,
        ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) ^ s *
          w (childType Q Vmax hQ1575 hQpos R mv))
    (hbudget : ∀ R : Fin Q,
      ∑ mv ∈ movesOf Q Vmax R, w (childType Q Vmax hQ1575 hQpos R mv) ≤ L)
    {o X : ℕ} (ho_pos : 0 < o) (ho_odd : o % 2 = 1) (ho_tree : Reaches f o 3) (ho_le : o ≤ X)
    (t : TypeId Q) (ht : o % (Q / digitVal t.1) = t.2.val) :
    ((X : ℝ) / (o : ℝ)) ^ s * w t ≤ L * (NTree o X : ℝ) := by sorry
/-- Improved unconditional basin-of-5 lower bound via individual child-weight charging (Theorem 8, Part 2). -/
theorem thm_basin5_sharp (X : ℕ) (hX : 3 ≤ X) :
    ((98959 : ℝ) / ((2269527 : ℝ) * (3 : ℝ) ^ ((13 : ℝ) / 20))) * (X : ℝ) ^ ((13 : ℝ) / 20) ≤
      (N5 X : ℝ) := by sorry
/-- Explicit decimal basin-of-5 lower bound `N5(X) > 0.02134 * X^(13/20)` for every `X ≥ 3`. -/
theorem thm_basin5_sharp_gt (X : ℕ) (hX : 3 ≤ X) :
    (2134 / 100000 : ℝ) * (X : ℝ) ^ ((13 : ℝ) / 20) < (N5 X : ℝ) := by sorry
/-- Complete all-even-base non-descent stopping dichotomy (Theorem 11): `p_∞(b) = 0 ↔ b ∈ {2, 4, 6, 10}`. -/
theorem thm_even_stopping {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) :
    (∀ k : ℕ, 1 ≤ k → HasNaturalDensity (D_k b k) (p_k b k)) ∧
    Filter.Tendsto (fun k : ℕ => p_k b (k + 1)) Filter.atTop (nhds (p_infty b)) ∧
    (p_infty b = 0 ↔ b = 2 ∨ b = 4 ∨ b = 6 ∨ b = 10) ∧
    ((b = 2 ∨ b = 4 ∨ b = 6 ∨ b = 10) → HasNaturalDensity (DescentSet b) 1) ∧
    ((b ≠ 2 ∧ b ≠ 4 ∧ b ≠ 6 ∧ b ≠ 10) → ∃ η : ℝ, 0 < η ∧ ∀ k : ℕ, 1 ≤ k → η ≤ p_k b k) := by sorry
/-- Exact `2`-adic Cantor closure of `B_1`, self-similar ultrametric isometry onto `Σ` and `000Σ ⊔ 001Σ`,
    Hausdorff measure and `dimH = dimB = β = -log₂ a`, and elementary quartic bounds (Theorem 18). -/
theorem thm_cantor :
    ∃ a₁ a : ℝ,
      (0 < a₁ ∧ a₁ < 1 ∧ a₁ + a₁ ^ 4 = 1) ∧
      (∃! x : ℝ, 0 < x ∧ x < 1 ∧ x + x ^ 4 = 1) ∧
      (0 < a ∧ a < 1 ∧ a + 2 * a ^ 4 = 1) ∧
      (∃! x : ℝ, 0 < x ∧ x < 1 ∧ x + 2 * x ^ 4 = 1) ∧
      let γ := -Real.logb 2 a₁
      let β := -Real.logb 2 a
      ((464958 / 1000000 : ℝ) < γ ∧ γ < (464959 / 1000000 : ℝ)) ∧
      ((626382135 / 1000000000 : ℝ) < β ∧ β < (626382145 / 1000000000 : ℝ)) ∧
      ((626382 / 1000000 : ℝ) < β ∧ β < (626383 / 1000000 : ℝ)) ∧
      ((∀ r : ℕ, (r = 1 ∨ r = 15 ∨ r = 17) → closure (KrPadic r) = KCal r) ∧
        closure B1Padic =
          affine30 1 '' KCal 1 ∪ affine30 15 '' KCal 15 ∪ affine30 17 '' KCal 17 ∧
        (∀ (x : ℤ_[2]) (ρ : ℝ), (Metric.ball x ρ ∩ closure B1Padic).Nonempty →
          {n : ℕ | 1 ≤ n ∧ Reaches f n 1 ∧ (n : ℤ_[2]) ∈ Metric.ball x ρ}.Infinite ∧
          {n : ℕ | 1 ≤ n ∧ InABC n ∧ ExitsAt19Or23 n ∧ (n : ℤ_[2]) ∈ Metric.ball x ρ}.Infinite) ∧
        IsNowhereDense (closure B1Padic)) ∧
      (((∀ r x y, x = y ↔ itin r x = itin r y) ∧
          (∀ r x y, x ≠ y →
            dist x y = (2 : ℝ) ^ (-((sInf {j : ℕ | itin r x j ≠ itin r y j} : ℕ) : ℤ))) ∧
          (∀ r : ℕ, (r = 1 ∨ r = 17) → itin r '' KCal r = SigmaBits) ∧
          itin 15 '' KCal 15 = Sigma15Bits) ∧
        Disjoint (prependBits [false, false, false] '' SigmaBits)
          (prependBits [false, false, true] '' SigmaBits) ∧
        ENNReal.ofReal (1 / 2) ≤
          @MeasureTheory.Measure.hausdorffMeasure ℤ_[2] _ (borel ℤ_[2])
            (@BorelSpace.mk ℤ_[2] _ (borel ℤ_[2]) rfl) β (closure B1Padic) ∧
        @MeasureTheory.Measure.hausdorffMeasure ℤ_[2] _ (borel ℤ_[2])
          (@BorelSpace.mk ℤ_[2] _ (borel ℤ_[2]) rfl) β (closure B1Padic) ≤
          ENNReal.ofReal (a⁻¹ ^ 2 + a) ∧
        @MeasureTheory.Measure.hausdorffMeasure ℤ_[2] _ (borel ℤ_[2])
          (@BorelSpace.mk ℤ_[2] _ (borel ℤ_[2]) rfl) β (closure B1Padic) <
          ENNReal.ofReal (3031 / 1000) ∧
        dimH (closure B1Padic) = ENNReal.ofReal β ∧
        HasBoxDim (closure B1Padic) β) ∧
      ((∀ X : ℝ, 1 ≤ X → a₁ ^ 9 * X ^ γ ≤ (N1 ⌊X⌋₊ : ℝ) ∧ (N1 ⌊X⌋₊ : ℝ) ≤ X ^ β) ∧
        (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → (N1All X : ℝ) / (X : ℝ) ≤ ε)) := by sorry
/-- Congruence-class completion dichotomy for `B_5` and `B_1` in every modulus `m ≥ 1` (Theorem 29). -/
theorem thm_suffix_class (a m : ℕ) (hm : 1 ≤ m) :
    Set.Infinite {n : ℕ | 0 < n ∧ n % m = a % m ∧ InBasin5 n} ∧
    (Set.Infinite {n : ℕ | 0 < n ∧ n % m = a % m ∧ InBasin1 n} ↔
      ∃ x : ℕ, x < suffixM m ∧ x % suffixP m = a % suffixP m ∧
        T^[suffixH m] x % 30 ∈ liveMod30) ∧
    ((¬ ∃ x : ℕ, x < suffixM m ∧ x % suffixP m = a % suffixP m ∧
        T^[suffixH m] x % 30 ∈ liveMod30) →
      ∀ n : ℕ, n % m = a % m → ¬ InBasin1 n) := by sorry
/-- Exact Hausdorff and box-counting dimension of reversed base-`b` suffix closures `ℰ_b` and `ℰ_{5,b}` (Corollary 30). -/
theorem cor_suffix_dimension :
    ∃ lam : ℝ,
      0 < lam ∧ lam ^ 4 = lam ^ 3 + 2 ∧
      (154368901 / 10 ^ 8 : ℝ) < lam ∧ lam < (1543689014 / 10 ^ 9 : ℝ) ∧
      (∃! l : ℝ, 0 < l ∧ l ^ 4 = l ^ 3 + 2) ∧
      (∀ (b t u : ℕ), 2 ≤ b → u % 2 = 1 → b = 2 ^ t * u →
        let s := (Real.log (u : ℝ) + (t : ℝ) * Real.log lam) / Real.log (b : ℝ)
        suffixClosure1 b ⊆ Set.Icc (0 : ℝ) 1 ∧
        dimH (suffixClosure1 b) = ENNReal.ofReal s ∧
        lowerBoxDim (suffixClosure1 b) = s ∧
        upperBoxDim (suffixClosure1 b) = s ∧
        Filter.Tendsto
          (fun δ : ℝ => Real.log (boxCoverNumber (suffixClosure1 b) δ : ℝ) / Real.log (1 / δ))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds s) ∧
        suffixClosure5 b = Set.Icc (0 : ℝ) 1) ∧
      (let s2 := Real.log lam / Real.log 2
       dimH (suffixClosure1 2) = ENNReal.ofReal s2 ∧
       (626382135 / 1000000000 : ℝ) < s2 ∧ s2 < (626382145 / 1000000000 : ℝ) ∧
       (6245 / 10000 : ℝ) < s2) ∧
      (let s10 := (Real.log 5 + Real.log lam) / Real.log 10
       dimH (suffixClosure1 10) = ENNReal.ofReal s10 ∧
       (887529815 / 1000000000 : ℝ) < s10 ∧ s10 < (887529825 / 1000000000 : ℝ)) ∧
      (dimH (suffixClosure1 7) = ENNReal.ofReal 1 ∧
       suffixClosure1 7 = Set.Icc (0 : ℝ) 1) := by sorry

/-! ## Additional Definitions and Headline Theorems for Sharpened Basin Bounds (Theorem 8) and Odd-Base Absorption Survey (Theorem 13) -/

/-- Odd-base attraction set `R(b) = {n ≥ 1 | f_b^k(n) = 1 for some k}`. -/
def RSet (b : ℕ) : Set ℕ := {n | 1 ≤ n ∧ Reaches (f_b b) n 1}
/-- Odd-base divergence set `E(b) = {n ≥ 1 | f_b^i(n) → ∞}`. -/
def DivSet (b : ℕ) : Set ℕ :=
  {n | 1 ≤ n ∧ Filter.Tendsto (fun i => (f_b b)^[i] n) Filter.atTop Filter.atTop}
/-- Congruence cylinder `(x mod b, c mod 2^j)` for the odd-base Markov chain. -/
structure OddCyl where
  x : ℕ
  c : ℕ
  j : ℕ
/-- Deterministic one-step cylinder transition map for odd base `b ≥ 3`. -/
noncomputable def cylStep (b : ℕ) (C : OddCyl) : OddCyl :=
  if C.c % 2 = 0 then
    ⟨(C.x * ((b + 1) / 2)) % b, (C.c / 2) % 2 ^ (C.j - 1), C.j - 1⟩
  else
    let a := padicValNat 2 C.x
    ⟨(C.x * C.x + 1) % b, (C.x * C.c + 1) % 2 ^ (C.j + a), C.j + a⟩
/-- Cylinder inclusion predicate `C1 ⊆ C2` modulo `(b, 2^{C2.j})`. -/
def CylSubset (b : ℕ) (C1 C2 : OddCyl) : Prop :=
  C1.x % b = C2.x % b ∧ C2.j ≤ C1.j ∧ C1.c % 2 ^ C2.j = C2.c % 2 ^ C2.j
/-- Deterministic stretch from `⟨x, 1, 1⟩` absorbs into the zero-digit trap (`x_s = 0 mod b`). -/
def IsTrapStretch (b x : ℕ) : Prop :=
  ∃ s : ℕ, 1 ≤ s ∧
    (∀ i < s, 1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).x ∧
              ((cylStep b)^[i] ⟨x, 1, 1⟩).x < b ∧
              1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).j) ∧
    ((cylStep b)^[s] ⟨x, 1, 1⟩).x = 0
/-- Deterministic stretch from `⟨x, 1, 1⟩` returns to a zero-bit state `⟨y, 0, 0⟩`. -/
def IsZeroStretch (b x y : ℕ) : Prop :=
  1 ≤ y ∧ y < b ∧ ∃ s : ℕ, 1 ≤ s ∧
    (∀ i < s, 1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).x ∧
              ((cylStep b)^[i] ⟨x, 1, 1⟩).x < b ∧
              1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).j) ∧
    (cylStep b)^[s] ⟨x, 1, 1⟩ = ⟨y, 0, 0⟩
/-- Deterministic stretch from `⟨x, 1, 1⟩` enters a self-returning escape cylinder `C0`. -/
def IsCertifiedEscape (b x : ℕ) : Prop :=
  ∃ (s p : ℕ) (C0 : OddCyl),
    1 ≤ p ∧
    (∀ i ≤ s, 1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).x ∧
              ((cylStep b)^[i] ⟨x, 1, 1⟩).x < b ∧
              1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).j) ∧
    CylSubset b ((cylStep b)^[s] ⟨x, 1, 1⟩) C0 ∧
    (∀ i ≤ p, 1 ≤ ((cylStep b)^[i] C0).x ∧
              ((cylStep b)^[i] C0).x < b ∧
              1 ≤ ((cylStep b)^[i] C0).j) ∧
    CylSubset b ((cylStep b)^[p] C0) C0
/-- Canonical outcome of the deterministic stretch from `⟨x, 1, 1⟩` in the odd-base Markov chain. -/
inductive OddStretchOutcome where
  | trap
  | escape
  | toState (y : ℕ)
  | unresolved
/-- Canonical certificate-free stretch outcome for residue `x` modulo `b`. -/
noncomputable def oddStretchOutcome (b x : ℕ) : OddStretchOutcome :=
  open Classical in
  if IsTrapStretch b x then .trap
  else if IsCertifiedEscape b x then .escape
  else if h : ∃ y, IsZeroStretch b x y then .toState (Classical.choose h)
  else .unresolved
/-- Finite-depth (`m`-step) Markov absorption probability into trap (`ZSet b`) from state `x`. -/
noncomputable def oddTrapProb (b : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | m + 1, x =>
    (1 / 2 : ℝ) * oddTrapProb b m ((x * ((b + 1) / 2)) % b) +
    (1 / 2 : ℝ) * OddStretchOutcome.casesOn (oddStretchOutcome b x) 1 0 (fun y => oddTrapProb b m y) 0
/-- Finite-depth (`m`-step) Markov absorption probability into escape (`DivSet b`) from state `x`. -/
noncomputable def oddRunProb (b : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | m + 1, x =>
    (1 / 2 : ℝ) * oddRunProb b m ((x * ((b + 1) / 2)) % b) +
    (1 / 2 : ℝ) * OddStretchOutcome.casesOn (oddStretchOutcome b x) 0 1 (fun y => oddRunProb b m y) 0
/-- Per-state infinite-horizon trap absorption probability `t_b(x) = sup_m oddTrapProb b m x`. -/
noncomputable def oddTrapStateMass (b x : ℕ) : ℝ := ⨆ m, oddTrapProb b m x
/-- Per-state infinite-horizon escape absorption probability `r_b(x) = sup_m oddRunProb b m x`. -/
noncomputable def oddRunStateMass (b x : ℕ) : ℝ := ⨆ m, oddRunProb b m x
/-- Canonical odd-base trap absorption mass `τ_b = (1 + ∑_{x=1}^{b-1} t_b(x)) / b`. -/
noncomputable def oddTrapMass (b : ℕ) : ℝ :=
  (1 + ∑ x ∈ Finset.Ico 1 b, oddTrapStateMass b x) / (b : ℝ)
/-- Canonical odd-base escape absorption mass `ρ_b = (∑_{x=1}^{b-1} r_b(x)) / b`. -/
noncomputable def oddRunMass (b : ℕ) : ℝ :=
  (∑ x ∈ Finset.Ico 1 b, oddRunStateMass b x) / (b : ℝ)
/-- All 999 odd bases `3 ≤ b ≤ 1,999`. -/
def allOddBases1999 : Finset ℕ := (Finset.Icc 3 1999).filter (fun b => b % 2 = 1)

/-- Complete sharpened basin bounds for base 10 (Theorem 8): sharpened Archimedean lower and upper
    bounds on `N_1(⌊X⌋)`, strict separation `0.6245 < β = dimH(closure B_1)`, sharpened
    weighted-charging lower bound `N_5(X) > 0.02134 * X^{13/20}`, and ratio bound
    `N_1(X) / N_5(X) = O(X^{-0.0255})`. -/
theorem thm_basin_sharp :
    (∀ X : ℝ, 1 ≤ X →
      (806 / 10000 : ℝ) * (X / 31) ^ ((399 : ℝ) / 800) ≤ (N1 ⌊X⌋₊ : ℝ) ∧
      (145 / 10000 : ℝ) * X ^ ((399 : ℝ) / 800) ≤ (N1 ⌊X⌋₊ : ℝ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → (N1 ⌊X⌋₊ : ℝ) ≤ C * X ^ ((6245 : ℝ) / 10000)) ∧
    (∃ a : ℝ, (0 < a ∧ a < 1 ∧ a + 2 * a ^ 4 = 1) ∧
      let β := -Real.logb 2 a
      Filter.limsup (fun X : ℝ => Real.log (N1 ⌊X⌋₊ : ℝ) / Real.log X) Filter.atTop ≤
        (6245 / 10000 : ℝ) ∧
      (6245 / 10000 : ℝ) < β ∧
      (626382135 / 1000000000 : ℝ) < β ∧ β < (626382145 / 1000000000 : ℝ) ∧
      dimH (closure B1Padic) = ENNReal.ofReal β ∧
      ENNReal.ofReal (6245 / 10000 : ℝ) < dimH (closure B1Padic)) ∧
    (∀ X : ℕ, 3 ≤ X →
      ((98959 : ℝ) / ((2269527 : ℝ) * (3 : ℝ) ^ ((13 : ℝ) / 20))) * (X : ℝ) ^ ((13 : ℝ) / 20) ≤
        (N5 X : ℝ) ∧
      (2134 / 100000 : ℝ) * (X : ℝ) ^ ((13 : ℝ) / 20) < (N5 X : ℝ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 3 ≤ X →
      (N1 X : ℝ) / (N5 X : ℝ) ≤ C * (X : ℝ) ^ (-(255 : ℝ) / 10000)) := by sorry
/-- Universal odd-base Markov absorption theorem for every odd `b ≥ 3` and certified 905/999
    odd-base survey through `b ≤ 1,999` (27 trap-only + 878 split; Theorem 13). -/
theorem thm_odd_survey :
    (∀ b : ℕ, 3 ≤ b → b % 2 = 1 →
      (1 : ℝ) / (b : ℝ) ≤ oddTrapMass b ∧
      0 ≤ oddRunMass b ∧
      oddTrapMass b + oddRunMass b ≤ 1 ∧
      (∀ ε > 0, ∀ᶠ N in Filter.atTop, oddTrapMass b - ε ≤ countFrac (ZSet b) N) ∧
      (∀ ε > 0, ∀ᶠ N in Filter.atTop, oddRunMass b - ε ≤ countFrac (DivSet b) N) ∧
      (oddTrapMass b + oddRunMass b = 1 →
        Filter.Tendsto (countFrac (ZSet b)) Filter.atTop (nhds (oddTrapMass b)) ∧
        Filter.Tendsto (countFrac (RSet b)) Filter.atTop (nhds (oddTrapMass b)) ∧
        Filter.Tendsto (countFrac (DivSet b)) Filter.atTop (nhds (oddRunMass b)) ∧
        (∃ qτ qρ : ℚ, (qτ : ℝ) = oddTrapMass b ∧ (qρ : ℝ) = oddRunMass b ∧ qτ + qρ = 1))) ∧
    allOddBases1999.card = 999 ∧
    ∃ (trapOnlyBases splitBases : Finset ℕ),
      trapOnlyBases ⊆ allOddBases1999 ∧
      splitBases ⊆ allOddBases1999 ∧
      Disjoint trapOnlyBases splitBases ∧
      trapOnlyBases.card = 27 ∧
      splitBases.card = 878 ∧
      (trapOnlyBases ∪ splitBases).card = 905 ∧
      (∀ b ∈ trapOnlyBases,
        oddTrapMass b = 1 ∧ oddRunMass b = 0 ∧
        oddTrapMass b + oddRunMass b = 1 ∧
        Filter.Tendsto (countFrac (ZSet b)) Filter.atTop (nhds (1 : ℝ)) ∧
        Filter.Tendsto (countFrac (RSet b)) Filter.atTop (nhds (1 : ℝ)) ∧
        Filter.Tendsto (countFrac (DivSet b)) Filter.atTop (nhds (0 : ℝ))) ∧
      (∀ b ∈ splitBases,
        0 < oddTrapMass b ∧ 0 < oddRunMass b ∧
        oddTrapMass b + oddRunMass b = 1 ∧
        (∃ qτ qρ : ℚ, (qτ : ℝ) = oddTrapMass b ∧ (qρ : ℝ) = oddRunMass b ∧ qτ + qρ = 1) ∧
        Filter.Tendsto (countFrac (ZSet b)) Filter.atTop (nhds (oddTrapMass b)) ∧
        Filter.Tendsto (countFrac (RSet b)) Filter.atTop (nhds (oddTrapMass b)) ∧
        Filter.Tendsto (countFrac (DivSet b)) Filter.atTop (nhds (oddRunMass b))) := by sorry
/-- Exact odd-base table evaluations for `b = 3, 5, 7, 13` (including `τ_13 = 13210/16991`,
    `ρ_13 = 3781/16991`). -/
theorem thm_odd_table_examples :
    (oddTrapMass 3 = 1 / 3 ∧ oddRunMass 3 = 2 / 3) ∧
    (oddTrapMass 5 = 1 ∧ oddRunMass 5 = 0) ∧
    (oddTrapMass 7 = 1 / 7 ∧ oddRunMass 7 = 0) ∧
    (oddTrapMass 13 = 13210 / 16991 ∧ oddRunMass 13 = 3781 / 16991 ∧
      Filter.Tendsto (countFrac (ZSet 13)) Filter.atTop (nhds ((13210 : ℝ) / 16991)) ∧
      Filter.Tendsto (countFrac (RSet 13)) Filter.atTop (nhds ((13210 : ℝ) / 16991)) ∧
      Filter.Tendsto (countFrac (DivSet 13)) Filter.atTop (nhds ((3781 : ℝ) / 16991))) := by sorry

end OuroborosChallenge
