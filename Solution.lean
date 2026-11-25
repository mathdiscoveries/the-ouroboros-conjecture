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
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Ouroboros

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
private def toOuroCycle {m : ℕ} (C : OddCycle m) : Ouroboros.OddCycle m :=
  ⟨C.hm, C.x, C.k, C.x_pos, C.x_odd, C.k_pos, C.step⟩
theorem prop_base4_reaches_three_iff (y : ℕ) :
    Reaches (f_b 4) (2 * y + 1) 3 ↔ Reaches T_C y 1 :=
  Ouroboros.prop_base4_reaches_three_iff y
theorem prop_base4_iff_collatz :
    (∀ n : ℕ, 0 < n → Reaches (f_b 4) n 1 ∨ Reaches (f_b 4) n 3) ↔
    (∀ y : ℕ, 0 < y → Reaches T_C y 1) :=
  Ouroboros.prop_base4_iff_collatz
theorem prop_base2_reaches_one (n : ℕ) (hn : 0 < n) : Reaches (f_b 2) n 1 :=
  Ouroboros.prop_base2_reaches_one n hn
theorem prop_base5_reaches_one (n : ℕ) (hn : 0 < n) : Reaches (f_b 5) n 1 :=
  Ouroboros.prop_base5_reaches_one n hn
theorem thm_terras_bound (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (countUpTo (E_k k) N : ℝ) / (N : ℝ) ≤
        (1124953 / 1000000 : ℝ) * (996423 / 1000000 : ℝ) ^ k + ε :=
  Ouroboros.thm_terras_bound k hk ε hε
theorem thm_terras_density_one (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (countUpTo NoDescent N : ℝ) / (N : ℝ) ≤ ε :=
  Ouroboros.thm_terras_density_one ε hε
theorem thm_residue_law {n : ℕ} (hn : n % 2 = 1) (h : Reaches f n 1) :
    n % 30 = 1 ∨ n % 30 = 15 ∨ n % 30 = 17 :=
  Ouroboros.thm_residue_law hn h
theorem thm_basin1_lower :
    ∃ a₁ : ℝ, 0 < a₁ ∧ a₁ < 1 ∧ a₁ + a₁ ^ 4 = 1 ∧
      ∃ c : ℝ, 0 < c ∧ ∀ X : ℕ, 1 ≤ X →
        c * (X : ℝ) ^ (Real.logb 2 (1 / a₁)) ≤ (N1 X : ℝ) :=
  ⟨Ouroboros.a1, Ouroboros.a1_spec.1, Ouroboros.a1_spec.2.1, Ouroboros.a1_spec.2.2,
    Ouroboros.thm_basin1_lower⟩
theorem thm_basin1_upper_explicit (X : ℕ) (hX : 1 ≤ X) :
    (N1 X : ℝ) ≤ (244 / 100 : ℝ) * (X : ℝ) ^ ((626383 : ℝ) / 1000000) :=
  Ouroboros.thm_basin1_upper_explicit X hX
theorem thm_basin1_density_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → (N1All X : ℝ) / (X : ℝ) ≤ ε :=
  Ouroboros.thm_basin1_density_zero ε hε
theorem thm_basin5_tight (X : ℕ) (hX : 3 ≤ X) :
    (605 / 1000000 : ℝ) * (X : ℝ) ^ ((65 : ℝ) / 100) ≤ (N5 X : ℝ) :=
  Ouroboros.thm_basin5_tight X hX
theorem cor_basin_separation_unconditional (X : ℕ) (hX : 3 ≤ X) :
    (N1 X : ℝ) / (N5 X : ℝ) ≤
      ((244 / 100 : ℝ) / (10766 / 100000000 : ℝ)) * (X : ℝ) ^ (-(236 / 10000 : ℝ)) :=
  Ouroboros.cor_basin_separation_unconditional X hX
theorem cor_basin_separation_tendsto_zero_unconditional (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (N1 X : ℝ) / (N5 X : ℝ) ≤ ε ∧ (N1All X : ℝ) / (N5All X : ℝ) ≤ ε :=
  Ouroboros.cor_basin_separation_tendsto_zero_unconditional ε hε
theorem thm_even_bases {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) :
    HasStationaryDriftIn b (· ≤ 0) ↔ b = 2 ∨ b = 4 ∨ b = 6 ∨ b = 10 :=
  Ouroboros.thm_even_bases hb2 hbeven
theorem prop_near_zero_band {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) :
    (HasStationaryDriftIn b (fun x => -(1 / 4 : ℝ) ≤ x ∧ x ≤ 1 / 4) ↔
      b = 4 ∨ b = 8 ∨ b = 10 ∨ b = 14) ∧
    (HasStationaryDriftIn b (fun x => -(1 / 4 : ℝ) ≤ x ∧ x < 0) ↔
      b = 4 ∨ b = 10) :=
  Ouroboros.prop_near_zero_band hb2 hbeven
theorem cor_drift_growth {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) :
    AllStationaryDriftsSatisfy b
      (fun x => (1 / 2 : ℝ) * Real.log ((b : ℝ) + 2) - (7 / 2 : ℝ) * Real.log 2 ≤ x) :=
  Ouroboros.cor_drift_growth hb2 hbeven
theorem prop_odd_runaway {b : ℕ} (hb : b % 2 = 1) (S : Set ℕ)
    (hS_even : ∀ d ∈ S, d % 2 = 0 ∧ 2 ≤ d)
    (hS_closed : ∀ d ∈ S, (d * d + 1) % b ∈ S)
    {n : ℕ} (hn_odd : n % 2 = 1) (hn_S : n % b ∈ S) :
    ∀ k : ℕ, ((f_b b)^[k] n) % 2 = 1 ∧
             ((f_b b)^[k] n) % b ∈ S ∧
             2 ^ k * n ≤ (f_b b)^[k] n :=
  Ouroboros.prop_odd_runaway hb S hS_even hS_closed hn_odd hn_S
theorem thm_odd_trapdoor_rootless {b p : ℕ} (hb_odd : b % 2 = 1)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3) (hpb : p ∣ b) :
    (∀ x : ℕ, (x * x + 1) % b ≠ 0) ∧
    (∀ n : ℕ, n ∈ ZSet b ↔ 1 ≤ n ∧ b ∣ n) :=
  Ouroboros.thm_odd_trapdoor_rootless hb_odd hp hp3 hpb
theorem lem_base17_runaway {n : ℕ} (hn1 : 1 ≤ n) (hn_odd : n % 2 = 1) (hn17 : n % 17 = 16) :
    (∀ i : ℕ, ¬ 17 ∣ (f_b 17)^[i] n ∧ (f_b 17)^[i] n ≠ 1) ∧
    (∀ i : ℕ, (f_b 17)^[i] n < (f_b 17)^[i + 10] n) ∧
    Filter.Tendsto (fun i => (f_b 17)^[i] n) Filter.atTop Filter.atTop :=
  Ouroboros.lem_base17_runaway hn1 hn_odd hn17
theorem thm_odd_densities_rootless {b p : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3) (hpb : p ∣ b) :
    Filter.Tendsto (countFrac (ZSet b)) Filter.atTop (nhds (1 / (b : ℝ))) :=
  Ouroboros.thm_odd_densities_rootless hb3 hb_odd hp hp3 hpb
theorem cycle_n5_eq_n3_add_n7 {m : ℕ} (C : OddCycle m) :
    C.n5 = C.n3 + C.n7 :=
  Ouroboros.cycle_n5_eq_n3_add_n7 (toOuroCycle C)
theorem lem_halving_budget {m : ℕ} (C : OddCycle m) :
    C.n1 + 2 * C.n3 + 4 * C.n7 + 3 * C.n9 ≤ C.totalHalvings ∧
      2 * C.n1 + 3 * C.aExp + C.bExp + 7 * C.cExp ≤ 2 * C.totalHalvings :=
  Ouroboros.lem_halving_budget (toOuroCycle C)
theorem thm_cycle_tail_64000 {m : ℕ} (C : OddCycle m)
    (hmin : ∀ i : Fin m, 10 ^ 15 ≤ C.x i) (hK : 64000 < C.totalHalvings) :
    20190 ≤ m ∧ 84191 ≤ C.totalHalvings + m :=
  Ouroboros.thm_cycle_tail_64000 (toOuroCycle C) hmin hK
theorem cycle_m1_unique (C : OddCycle 1) : C.x 0 = 1 ∧ C.k 0 = 1 :=
  Ouroboros.cycle_m1_unique (toOuroCycle C)
theorem cycle_m2_classification (C : OddCycle 2) :
    (C.x 0 = 1 ∧ C.x 1 = 1 ∧ C.k 0 = 1 ∧ C.k 1 = 1) ∨
    (C.x 0 = 5 ∧ C.x 1 = 13 ∧ C.k 0 = 1 ∧ C.k 1 = 3) ∨
    (C.x 0 = 13 ∧ C.x 1 = 5 ∧ C.k 0 = 3 ∧ C.k 1 = 1) :=
  Ouroboros.cycle_m2_classification (toOuroCycle C)
theorem cycle_m3_unique (C : OddCycle 3) :
    ∀ i : Fin 3, C.x i = 1 ∧ C.k i = 1 :=
  Ouroboros.cycle_m3_unique (toOuroCycle C)
theorem f_cycle_one : f^[2] 1 = 1 := Ouroboros.f_cycle_one
theorem f_cycle_five : f^[6] 5 = 5 := Ouroboros.f_cycle_five

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

private lemma NTree_eq (o X : ℕ) : NTree o X = Ouroboros.NTree o X := by
  unfold NTree Ouroboros.NTree
  congr 1

private lemma T_b_eq (b n : ℕ) : T_b b n = Ouroboros.T_b b n := rfl

private lemma affAB_eq (b n j : ℕ) : affAB b n j = Ouroboros.affAB b n j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [affAB, Ouroboros.affAB, ih]
    rfl

private lemma SurvRes_eq (b k : ℕ) : SurvRes b k = Ouroboros.SurvRes b k := by
  ext r
  simp only [SurvRes, Ouroboros.SurvRes, Finset.mem_filter, Finset.mem_univ, true_and, affAB_eq]

private lemma p_k_eq (b k : ℕ) : p_k b k = Ouroboros.p_k b k := by
  simp only [p_k, Ouroboros.p_k, SurvRes_eq]

private lemma p_infty_eq (b : ℕ) : p_infty b = Ouroboros.p_infty b := by
  simp only [p_infty, Ouroboros.p_infty, p_k_eq]

private lemma D_k_eq (b k : ℕ) : D_k b k = Ouroboros.D_k b k := rfl
private lemma DescentSet_eq (b : ℕ) : DescentSet b = Ouroboros.DescentSet b := rfl

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
    ((X : ℝ) / (o : ℝ)) ^ s * w t ≤ L * (NTree o X : ℝ) := by
  rw [NTree_eq]
  exact Ouroboros.lem_weighted_tree3 hQ1575 hQpos hs hL w hw_nn hexpand hbudget
    ho_pos ho_odd ho_tree ho_le t ht

theorem thm_basin5_sharp (X : ℕ) (hX : 3 ≤ X) :
    ((98959 : ℝ) / ((2269527 : ℝ) * (3 : ℝ) ^ ((13 : ℝ) / 20))) * (X : ℝ) ^ ((13 : ℝ) / 20) ≤
      (N5 X : ℝ) :=
  Ouroboros.thm_basin5_sharp X hX

theorem thm_basin5_sharp_gt (X : ℕ) (hX : 3 ≤ X) :
    (2134 / 100000 : ℝ) * (X : ℝ) ^ ((13 : ℝ) / 20) < (N5 X : ℝ) :=
  Ouroboros.thm_basin5_sharp_gt X hX

theorem thm_even_stopping {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) :
    (∀ k : ℕ, 1 ≤ k → HasNaturalDensity (D_k b k) (p_k b k)) ∧
    Filter.Tendsto (fun k : ℕ => p_k b (k + 1)) Filter.atTop (nhds (p_infty b)) ∧
    (p_infty b = 0 ↔ b = 2 ∨ b = 4 ∨ b = 6 ∨ b = 10) ∧
    ((b = 2 ∨ b = 4 ∨ b = 6 ∨ b = 10) → HasNaturalDensity (DescentSet b) 1) ∧
    ((b ≠ 2 ∧ b ≠ 4 ∧ b ≠ 6 ∧ b ≠ 10) → ∃ η : ℝ, 0 < η ∧ ∀ k : ℕ, 1 ≤ k → η ≤ p_k b k) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Ouroboros.thm_even_stopping hb2 hbeven
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, fun hne => ?_⟩
  · rw [D_k_eq, p_k_eq]; exact h1 k hk
  · simpa only [p_k_eq, p_infty_eq] using h2
  · rw [p_infty_eq]; exact h3
  · intro hb; rw [DescentSet_eq]; exact h4 hb
  · obtain ⟨η, hη, hlb⟩ := h5 hne
    exact ⟨η, hη, fun k hk => by rw [p_k_eq]; exact hlb k hk⟩

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
        (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → (N1All X : ℝ) / (X : ℝ) ≤ ε)) := by
  obtain ⟨ha1, hu1, haS, huS, ⟨hg_eq, hb_eq⟩, hg6, hb8, hb6, hpart1,
    ⟨hiso, himg1, himg15, _, hHlo, hHhi, hHlt, hdimH, hdimB⟩, hpart3⟩ := Ouroboros.thm_cantor
  refine ⟨Ouroboros.a1, Ouroboros.aStar, ha1, hu1, haS, huS, ?_⟩
  dsimp only
  rw [← hg_eq, ← hb_eq]
  refine ⟨hg6, hb8, hb6, hpart1, ⟨?_, ?_, hHlo, hHhi, hHlt, hdimH, hdimB⟩, hpart3⟩
  · have hitin : ∀ r x, itin r x = (Ouroboros.psiMap r x).bit := fun _ _ => rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r x y
      rw [hitin, hitin]
      constructor
      · intro h; rw [h]
      · intro h
        exact (hiso r).injective (Ouroboros.BitSeq.ext h)
    · intro r x y hxy
      classical
      have hpsi_ne : Ouroboros.psiMap r x ≠ Ouroboros.psiMap r y := fun h =>
        hxy ((hiso r).injective h)
      have hdist : dist x y = dist (Ouroboros.psiMap r x) (Ouroboros.psiMap r y) :=
        ((hiso r).dist_eq x y).symm
      rw [hdist, Ouroboros.bitSeq_dist_of_ne hpsi_ne]
      have hsInf : sInf {j : ℕ | itin r x j ≠ itin r y j} =
          Ouroboros.firstDiff hpsi_ne := by
        unfold Ouroboros.firstDiff
        apply le_antisymm
        · exact Nat.sInf_le (Nat.find_spec (Ouroboros.bitSeq_exists_ne hpsi_ne))
        · refine le_csInf ⟨_, Nat.find_spec (Ouroboros.bitSeq_exists_ne hpsi_ne)⟩ fun j hj => ?_
          exact Nat.find_min' (Ouroboros.bitSeq_exists_ne hpsi_ne) hj
      rw [hsInf]
    · intro r hr
      ext f
      simp only [Set.mem_image, hitin]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hmem : Ouroboros.psiMap r x ∈ Ouroboros.SigmaSet := by
          rw [← himg1 r hr]; exact ⟨x, hx, rfl⟩
        exact hmem
      · intro hf
        have hmem : (⟨f⟩ : Ouroboros.BitSeq) ∈ Ouroboros.psiMap r '' Ouroboros.KCal r := by
          rw [himg1 r hr]; exact hf
        obtain ⟨x, hx, hx_eq⟩ := hmem
        exact ⟨x, hx, congr_arg Ouroboros.BitSeq.bit hx_eq⟩
    · ext f
      simp only [Set.mem_image, hitin]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hmem : Ouroboros.psiMap 15 x ∈ Ouroboros.Sigma15Set := by
          rw [← himg15]; exact ⟨x, hx, rfl⟩
        rcases hmem with ⟨y, hy, hy_eq⟩ | ⟨y, hy, hy_eq⟩
        · left; exact ⟨y.bit, hy, congr_arg Ouroboros.BitSeq.bit hy_eq⟩
        · right; exact ⟨y.bit, hy, congr_arg Ouroboros.BitSeq.bit hy_eq⟩
      · intro hf
        have hmem : (⟨f⟩ : Ouroboros.BitSeq) ∈ Ouroboros.psiMap 15 '' Ouroboros.KCal 15 := by
          rw [himg15]
          rcases hf with ⟨y, hy, hy_eq⟩ | ⟨y, hy, hy_eq⟩
          · left; exact ⟨⟨y⟩, hy, Ouroboros.BitSeq.ext hy_eq⟩
          · right; exact ⟨⟨y⟩, hy, Ouroboros.BitSeq.ext hy_eq⟩
        obtain ⟨x, hx, hx_eq⟩ := hmem
        exact ⟨x, hx, congr_arg Ouroboros.BitSeq.bit hx_eq⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨x, _, rfl⟩ ⟨y, _, heq⟩
    have h2 := congr_fun heq 2
    simp [prependBits] at h2

theorem thm_suffix_class (a m : ℕ) (hm : 1 ≤ m) :
    Set.Infinite {n : ℕ | 0 < n ∧ n % m = a % m ∧ InBasin5 n} ∧
    (Set.Infinite {n : ℕ | 0 < n ∧ n % m = a % m ∧ InBasin1 n} ↔
      ∃ x : ℕ, x < suffixM m ∧ x % suffixP m = a % suffixP m ∧
        T^[suffixH m] x % 30 ∈ liveMod30) ∧
    ((¬ ∃ x : ℕ, x < suffixM m ∧ x % suffixP m = a % suffixP m ∧
        T^[suffixH m] x % 30 ∈ liveMod30) →
      ∀ n : ℕ, n % m = a % m → ¬ InBasin1 n) :=
  Ouroboros.thm_suffix_class a m hm

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
       suffixClosure1 7 = Set.Icc (0 : ℝ) 1) := by
  obtain ⟨⟨hl0, hlq, hl_lo, hl_hi, hlu⟩, hgen,
    ⟨_, _, hb2_lo, hb2_hi, hb2_gt⟩,
    ⟨hb10_dim, hb10_lo, hb10_hi⟩,
    ⟨hb7_dim, _, hb7_eq⟩⟩ := Ouroboros.cor_suffix_dimension
  have hs2 : Ouroboros.suffixDimVal 2 = Real.log Ouroboros.suffixLambda / Real.log 2 := by
    have h := Ouroboros.suffixDimVal_eq_of_fac (b := 2) (t := 1) (u := 1)
      (by norm_num) (by decide) (by norm_num)
    simpa [Real.log_one] using h
  have hs10 : Ouroboros.suffixDimVal 10 = (Real.log 5 + Real.log Ouroboros.suffixLambda) / Real.log 10 := by
    have h := Ouroboros.suffixDimVal_eq_of_fac (b := 10) (t := 1) (u := 5)
      (by norm_num) (by decide) (by norm_num)
    simpa using h
  refine ⟨Ouroboros.suffixLambda, hl0, hlq, hl_lo, hl_hi, hlu, hgen, ?_, ?_, ⟨hb7_dim, hb7_eq⟩⟩
  · dsimp only
    rw [← hs2]
    exact ⟨Ouroboros.suffixClosure1_dimH (by norm_num), hb2_lo, hb2_hi, hb2_gt⟩
  · dsimp only
    rw [← hs10]
    exact ⟨hb10_dim, hb10_lo, hb10_hi⟩

end OuroborosChallenge
