module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Tactic
public import Ouroboros.OddBases
public import Ouroboros.OddSurveyCertData
public import Ouroboros.OddSurveyCert

@[expose] public section

/-!
# Odd-Base Survey Theorem (`thm:odd-survey`, universal odd `b ≥ 3` & `905 / 999` through `1,999`)

Defines the canonical Section 6.2 odd-base Markov chain and its finite-cylinder absorption
masses `oddTrapMass b` (`τ_b`) and `oddRunMass b` (`ρ_b`) for every odd base `b ≥ 3`,
completely independent of any certificate data:
- `oddStretchOutcome b x`: canonical deterministic stretch outcome from `(x, 1, 1)` into
  trap (`IsTrapStretch`), certified escape (`IsCertifiedEscape`), zero-bit return
  (`IsZeroStretch`), or unresolved.
- `oddTrapProb b m x`, `oddRunProb b m x`: depth-`m` Markov absorption probabilities.
- `oddTrapStateMass b x`, `oddRunStateMass b x`, `oddTrapMass b`, `oddRunMass b`:
  infinite-horizon absorption masses satisfying the finite absorption linear system
  (`oddTrapStateMass_eq`, `oddRunStateMass_eq`) and universal lower-density bounds
  `∀ ε > 0, ∀ᶠ N in atTop, oddTrapMass b - ε ≤ countFrac (ZSet b) N` and
  `oddRunMass b - ε ≤ countFrac (DivSet b) N` (`thm_odd_absorption_universal`).
- Whenever `oddTrapMass b + oddRunMass b = 1`, all three natural densities exist with
  `d(ZSet b) = d(RSet b) = oddTrapMass b`, `d(DivSet b) = oddRunMass b`, and `oddTrapMass b`,
  `oddRunMass b` are exact rationals uniquely solving the finite absorption linear system
  (`oddTrapStateMass_unique_of_full`, `oddRunStateMass_unique_of_full`,
  `oddAbsorption_rational_of_full`).
- Soundness of the pure-kernel certificate checker `Ouroboros.OddSurveyCert.checkBaseCert`
  establishes `oddTrapMass b + oddRunMass b = 1` across 905 of the 999 odd bases
  `3 ≤ b ≤ 1,999` (27 trap-only with `oddTrapMass b = 1`, 878 split with both masses
  strictly positive; `thm_odd_survey`), together with concrete Table `tab:odd` evaluations
  (`thm_odd_table_examples`, including `b = 3, 5, 7, 13`).
-/

namespace Ouroboros

open Filter Topology Ouroboros.OddSurveyCert

/-! ## Section 0: Canonical Section 6.2 Stretch Outcomes and Markov Absorption Masses -/

/-- The deterministic cylinder stretch from `⟨x, 1, 1⟩` absorbs into the zero-digit trap
    (`x_s = 0 mod b`) at some step `s ≥ 1`, staying valid (`1 ≤ x_i < b`, `1 ≤ j_i`)
    for all `i < s`. -/
def IsTrapStretch (b x : ℕ) : Prop :=
  ∃ s : ℕ, 1 ≤ s ∧
    (∀ i < s, 1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).x ∧
              ((cylStep b)^[i] ⟨x, 1, 1⟩).x < b ∧
              1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).j) ∧
    ((cylStep b)^[s] ⟨x, 1, 1⟩).x = 0

/-- The deterministic cylinder stretch from `⟨x, 1, 1⟩` returns to a zero-bit state
    `⟨y, 0, 0⟩` (`1 ≤ y < b`) at some step `s ≥ 1`, staying valid for all `i < s`. -/
def IsZeroStretch (b x y : ℕ) : Prop :=
  1 ≤ y ∧ y < b ∧ ∃ s : ℕ, 1 ≤ s ∧
    (∀ i < s, 1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).x ∧
              ((cylStep b)^[i] ⟨x, 1, 1⟩).x < b ∧
              1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).j) ∧
    (cylStep b)^[s] ⟨x, 1, 1⟩ = ⟨y, 0, 0⟩

/-- The deterministic cylinder stretch from `⟨x, 1, 1⟩` enters a self-returning escape
    cylinder `C0` (`1 ≤ p`, valid along all steps `i ≤ p`, and `(cylStep b)^[p] C0 ⊆ C0`).
    Covers both direct self-return (`C0 = (cylStep b)^[s] ⟨x, 1, 1⟩`) and entry into an
    earlier escape cylinder (as in `b = 19, x = 4`). -/
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

/-- Canonical outcome of the deterministic stretch from `⟨x, 1, 1⟩` in the Section 6.2
    odd-base finite-state Markov chain. -/
inductive OddStretchOutcome where
  | trap
  | escape
  | toState (y : ℕ)
  | unresolved
  deriving DecidableEq

/-- Canonical stretch outcome for residue `x` modulo `b` (certificate-free). -/
noncomputable def oddStretchOutcome (b x : ℕ) : OddStretchOutcome :=
  open Classical in
  if IsTrapStretch b x then .trap
  else if IsCertifiedEscape b x then .escape
  else if h : ∃ y, IsZeroStretch b x y then .toState (Classical.choose h)
  else .unresolved

/-- Finite-depth (`m`-step) Markov absorption probability into trap (`Z_b`) from state `x`. -/
noncomputable def oddTrapProb (b : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | m + 1, x =>
    (1 / 2 : ℝ) * oddTrapProb b m ((x * ((b + 1) / 2)) % b) +
    (1 / 2 : ℝ) * match oddStretchOutcome b x with
      | .trap => 1
      | .escape => 0
      | .toState y => oddTrapProb b m y
      | .unresolved => 0

/-- Finite-depth (`m`-step) Markov absorption probability into certified escape (`E_b`)
    from state `x`. -/
noncomputable def oddRunProb (b : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | m + 1, x =>
    (1 / 2 : ℝ) * oddRunProb b m ((x * ((b + 1) / 2)) % b) +
    (1 / 2 : ℝ) * match oddStretchOutcome b x with
      | .trap => 0
      | .escape => 1
      | .toState y => oddRunProb b m y
      | .unresolved => 0

/-- Per-state infinite-horizon trap absorption probability `t_b(x) = sup_m oddTrapProb b m x`. -/
noncomputable def oddTrapStateMass (b x : ℕ) : ℝ := ⨆ m, oddTrapProb b m x

/-- Per-state infinite-horizon escape absorption probability `r_b(x) = sup_m oddRunProb b m x`. -/
noncomputable def oddRunStateMass (b x : ℕ) : ℝ := ⨆ m, oddRunProb b m x

/-- Canonical Section 6.2 trap absorption mass `τ_b = (1 + ∑_{x=1}^{b-1} t_b(x)) / b`. -/
noncomputable def oddTrapMass (b : ℕ) : ℝ :=
  (1 + ∑ x ∈ Finset.Ico 1 b, oddTrapStateMass b x) / (b : ℝ)

/-- Canonical Section 6.2 escape absorption mass `ρ_b = (∑_{x=1}^{b-1} r_b(x)) / b`. -/
noncomputable def oddRunMass (b : ℕ) : ℝ :=
  (∑ x ∈ Finset.Ico 1 b, oddRunStateMass b x) / (b : ℝ)

/-! ## Section 1: Arithmetic & `p2v2` ↔ `2 ^ padicValNat 2` -/

private lemma padicValNat_two_eq_of_dvd_not_dvd {x k : ℕ} (hx : 1 ≤ x)
    (hdvd : 2 ^ k ∣ x) (hndvd : ¬ 2 ^ (k + 1) ∣ x) :
    padicValNat 2 x = k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hge : k ≤ padicValNat 2 x := (padicValNat_dvd_iff_le (by omega)).mp hdvd
  have hlt : ¬ k + 1 ≤ padicValNat 2 x := fun h => hndvd ((padicValNat_dvd_iff_le (by omega)).mpr h)
  omega

private lemma p2v2_eq_two_pow_padicValNat {x : ℕ} (hx1 : 1 ≤ x) (hxb : x < 2048) :
    p2v2 x = 2 ^ padicValNat 2 x := by
  unfold p2v2
  cases h1 : Nat.beq (x % 2) 0 with
  | false =>
    have hnd : ¬ 2 ^ 1 ∣ x := by
      intro hd; have hm : x % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
      rw [hm] at h1; exact absurd h1 (by decide)
    rw [padicValNat_two_eq_of_dvd_not_dvd hx1 (by simp) hnd]; rfl
  | true =>
    have hd1 : 2 ^ 1 ∣ x := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h1)
    cases h2 : Nat.beq (x % 4) 0 with
    | false =>
      have hnd : ¬ 2 ^ 2 ∣ x := by
        intro hd; have hm : x % 4 = 0 := Nat.mod_eq_zero_of_dvd hd
        rw [hm] at h2; exact absurd h2 (by decide)
      rw [padicValNat_two_eq_of_dvd_not_dvd hx1 hd1 hnd]; rfl
    | true =>
      have hd2 : 2 ^ 2 ∣ x := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h2)
      cases h3 : Nat.beq (x % 8) 0 with
      | false =>
        have hnd : ¬ 2 ^ 3 ∣ x := by
          intro hd; have hm : x % 8 = 0 := Nat.mod_eq_zero_of_dvd hd
          rw [hm] at h3; exact absurd h3 (by decide)
        rw [padicValNat_two_eq_of_dvd_not_dvd hx1 hd2 hnd]; rfl
      | true =>
        have hd3 : 2 ^ 3 ∣ x := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h3)
        cases h4 : Nat.beq (x % 16) 0 with
        | false =>
          have hnd : ¬ 2 ^ 4 ∣ x := by
            intro hd; have hm : x % 16 = 0 := Nat.mod_eq_zero_of_dvd hd
            rw [hm] at h4; exact absurd h4 (by decide)
          rw [padicValNat_two_eq_of_dvd_not_dvd hx1 hd3 hnd]; rfl
        | true =>
          have hd4 : 2 ^ 4 ∣ x := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h4)
          cases h5 : Nat.beq (x % 32) 0 with
          | false =>
            have hnd : ¬ 2 ^ 5 ∣ x := by
              intro hd; have hm : x % 32 = 0 := Nat.mod_eq_zero_of_dvd hd
              rw [hm] at h5; exact absurd h5 (by decide)
            rw [padicValNat_two_eq_of_dvd_not_dvd hx1 hd4 hnd]; rfl
          | true =>
            have hd5 : 2 ^ 5 ∣ x := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h5)
            cases h6 : Nat.beq (x % 64) 0 with
            | false =>
              have hnd : ¬ 2 ^ 6 ∣ x := by
                intro hd; have hm : x % 64 = 0 := Nat.mod_eq_zero_of_dvd hd
                rw [hm] at h6; exact absurd h6 (by decide)
              rw [padicValNat_two_eq_of_dvd_not_dvd hx1 hd5 hnd]; rfl
            | true =>
              have hd6 : 2 ^ 6 ∣ x := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h6)
              cases h7 : Nat.beq (x % 128) 0 with
              | false =>
                have hnd : ¬ 2 ^ 7 ∣ x := by
                  intro hd; have hm : x % 128 = 0 := Nat.mod_eq_zero_of_dvd hd
                  rw [hm] at h7; exact absurd h7 (by decide)
                rw [padicValNat_two_eq_of_dvd_not_dvd hx1 hd6 hnd]; rfl
              | true =>
                have hd7 : 2 ^ 7 ∣ x := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h7)
                cases h8 : Nat.beq (x % 256) 0 with
                | false =>
                  have hnd : ¬ 2 ^ 8 ∣ x := by
                    intro hd; have hm : x % 256 = 0 := Nat.mod_eq_zero_of_dvd hd
                    rw [hm] at h8; exact absurd h8 (by decide)
                  rw [padicValNat_two_eq_of_dvd_not_dvd hx1 hd7 hnd]; rfl
                | true =>
                  have hd8 : 2 ^ 8 ∣ x := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h8)
                  cases h9 : Nat.beq (x % 512) 0 with
                  | false =>
                    have hnd : ¬ 2 ^ 9 ∣ x := by
                      intro hd; have hm : x % 512 = 0 := Nat.mod_eq_zero_of_dvd hd
                      rw [hm] at h9; exact absurd h9 (by decide)
                    rw [padicValNat_two_eq_of_dvd_not_dvd hx1 hd8 hnd]; rfl
                  | true =>
                    have hd9 : 2 ^ 9 ∣ x := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h9)
                    cases h10 : Nat.beq (x % 1024) 0 with
                    | false =>
                      have hnd : ¬ 2 ^ 10 ∣ x := by
                        intro hd; have hm : x % 1024 = 0 := Nat.mod_eq_zero_of_dvd hd
                        rw [hm] at h10; exact absurd h10 (by decide)
                      rw [padicValNat_two_eq_of_dvd_not_dvd hx1 hd9 hnd]; rfl
                    | true =>
                      have hd10 : 2 ^ 10 ∣ x := Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true h10)
                      have hnd11 : ¬ 2 ^ 11 ∣ x := by
                        intro hd
                        have := Nat.le_of_dvd (by omega) hd
                        omega
                      rw [padicValNat_two_eq_of_dvd_not_dvd hx1 hd10 hnd11]; rfl

private lemma half_pos_lt {b x : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (hx1 : 1 ≤ x) (hxb : x < b) :
    1 ≤ (x * ((b + 1) / 2)) % b ∧ (x * ((b + 1) / 2)) % b < b := by
  refine ⟨?_, Nat.mod_lt _ (by omega)⟩
  by_contra h0
  have hmod : (x * ((b + 1) / 2)) % b = 0 := by omega
  have hdvd : b ∣ x * ((b + 1) / 2) := Nat.dvd_of_mod_eq_zero hmod
  have h2 : 2 * ((b + 1) / 2) = b + 1 := by omega
  have hcop : Nat.Coprime b ((b + 1) / 2) := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hg1 : Nat.gcd b ((b + 1) / 2) ∣ b := Nat.gcd_dvd_left _ _
    have hg2 : Nat.gcd b ((b + 1) / 2) ∣ 2 * ((b + 1) / 2) :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) 2
    rw [h2] at hg2
    have hg3 : Nat.gcd b ((b + 1) / 2) ∣ 1 := by
      obtain ⟨k1, hk1⟩ := hg1
      obtain ⟨k2, hk2⟩ := hg2
      refine ⟨k2 - k1, ?_⟩
      have hle : k1 ≤ k2 := by nlinarith
      zify [hle]; linarith
    exact Nat.eq_one_of_dvd_one hg3
  have hbx : b ∣ x := hcop.dvd_of_dvd_mul_right hdvd
  have := Nat.le_of_dvd (by omega) hbx
  omega

private lemma cylStep_x_lt {b : ℕ} (hb3 : 3 ≤ b) (C : OddCyl) :
    (cylStep b C).x < b := by
  unfold cylStep
  split_ifs <;> exact Nat.mod_lt _ (by omega)

private lemma cylStep_c_lt {b : ℕ} (C : OddCyl) :
    (cylStep b C).c < 2 ^ (cylStep b C).j := by
  unfold cylStep
  split_ifs <;> exact Nat.mod_lt _ (by positivity)

private lemma two_pow_div_two {j : ℕ} (hj : 1 ≤ j) : 2 ^ j / 2 = 2 ^ (j - 1) := by
  conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
  exact Nat.mul_div_cancel _ (by omega)

private lemma cylStep_even_eq {b : ℕ} {C : OddCyl} (hj : 1 ≤ C.j)
    (hc_lt : C.c < 2 ^ C.j) (hev : C.c % 2 = 0) :
    cylStep b C = ⟨(C.x * ((b + 1) / 2)) % b, C.c / 2, C.j - 1⟩ := by
  unfold cylStep
  simp only [hev, ↓reduceIte]
  have hlt : C.c / 2 < 2 ^ (C.j - 1) := by
    rw [← two_pow_div_two hj]
    have h2 : 2 ^ C.j = 2 * (2 ^ C.j / 2) := by
      rw [two_pow_div_two hj, ← pow_succ', show C.j - 1 + 1 = C.j by omega]
    omega
  rw [Nat.mod_eq_of_lt hlt]

private lemma cylStep_odd_eq {b : ℕ} {C : OddCyl} (hodd : C.c % 2 ≠ 0) :
    cylStep b C =
      ⟨(C.x * C.x + 1) % b, (C.x * C.c + 1) % 2 ^ (C.j + padicValNat 2 C.x),
       C.j + padicValNat 2 C.x⟩ := by
  unfold cylStep
  simp [hodd]

/-! ## Section 2: `checkSeed` and `CylSubset` Monotonicity → `DivSet b` -/

private lemma divSet_of_iter {b s n : ℕ} (hn1 : 1 ≤ n)
    (hdiv : (f_b b)^[s] n ∈ DivSet b) : n ∈ DivSet b := by
  refine ⟨hn1, ?_⟩
  have htend := hdiv.2
  rw [Filter.tendsto_atTop_atTop] at htend ⊢
  intro M
  obtain ⟨N, hN⟩ := htend M
  refine ⟨N + s, fun i hi => ?_⟩
  have hsplit : i = (i - s) + s := by omega
  rw [hsplit, Function.iterate_add_apply]
  exact hN (i - s) (by omega)

private lemma zSet_of_iter {b s n : ℕ} (hn1 : 1 ≤ n)
    (hz : (f_b b)^[s] n ∈ ZSet b) : n ∈ ZSet b := by
  refine ⟨hn1, ?_⟩
  obtain ⟨_, j, hj⟩ := hz
  exact ⟨j + s, by rw [Function.iterate_add_apply]; exact hj⟩

private lemma runSeedSteps_zero_trap {b inv2 : ℕ} :
    ∀ n, runSeedSteps b inv2 n 0 0 0 = (0, 0, 0)
  | 0 => rfl
  | n + 1 => by simp [runSeedSteps]

private lemma runSeedSteps_add {b inv2 : ℕ} :
    ∀ n1 n2 x c m,
      runSeedSteps b inv2 (n1 + n2) x c m =
      let (x1, c1, m1) := runSeedSteps b inv2 n1 x c m
      runSeedSteps b inv2 n2 x1 c1 m1 := by
  intro n1
  induction n1 with
  | zero => intro n2 x c m; simp [runSeedSteps]
  | succ n1 ih =>
    intro n2 x c m
    rw [show n1 + 1 + n2 = (n1 + n2) + 1 by omega]
    simp only [runSeedSteps]
    cases Nat.beq x 0 with
    | true => simp [runSeedSteps_zero_trap]
    | false =>
      cases Nat.ble m 1 with
      | true => simp [runSeedSteps_zero_trap]
      | false =>
        cases Nat.beq (c % 2) 0 with
        | true => exact ih n2 ((x * inv2) % b) (c / 2) (m / 2)
        | false => exact ih n2 ((x * x + 1) % b) ((x * c + 1) % (m * p2v2 x)) (m * p2v2 x)

private lemma runSeedChunks_eq_runSeedSteps {b inv2 : ℕ} :
    ∀ chunks n x c m, n ≤ chunks * 180 →
      runSeedChunks b inv2 chunks n x c m = runSeedSteps b inv2 n x c m := by
  intro chunks
  induction chunks with
  | zero =>
    intro n x c m hn
    have hn0 : n = 0 := by omega
    subst hn0; rfl
  | succ chunks ih =>
    intro n x c m hn
    simp only [runSeedChunks]
    cases hle : Nat.ble n 180 with
    | true => rfl
    | false =>
      have hgt : 180 < n := by
        have hnot : ¬ n ≤ 180 := fun h => by
          have : Nat.ble n 180 = true := Nat.ble_eq.mpr h
          rw [this] at hle; exact absurd hle (by decide)
        omega
      rcases h1 : runSeedSteps b inv2 180 x c m with ⟨x1, c1, m1⟩
      rw [ih (n - 180) x1 c1 m1 (by omega)]
      have hadd := runSeedSteps_add (b := b) (inv2 := inv2) 180 (n - 180) x c m
      rw [show 180 + (n - 180) = n by omega, h1] at hadd
      exact hadd.symm

private lemma runSeedSteps_sound {b : ℕ} (hb3 : 3 ≤ b) (hb_lt : b < 2048) (hb_odd : b % 2 = 1) :
    ∀ (n : ℕ) (C : OddCyl),
      1 ≤ C.x → C.x < b → C.c < 2 ^ C.j →
      let (x', c', m') := runSeedSteps b ((b + 1) / 2) n C.x C.c (2 ^ C.j)
      1 ≤ x' → 2 ≤ m' →
      (∀ i ≤ n, 1 ≤ ((cylStep b)^[i] C).x ∧ ((cylStep b)^[i] C).x < b ∧
                1 ≤ ((cylStep b)^[i] C).j) ∧
      x' = ((cylStep b)^[n] C).x ∧
      c' = ((cylStep b)^[n] C).c ∧
      m' = 2 ^ ((cylStep b)^[n] C).j := by
  intro n
  induction n with
  | zero =>
    intro C hx1 hxb _ hx' hm'
    have hj1 : 1 ≤ C.j := by
      by_contra h0; have : C.j = 0 := by omega
      rw [this] at hm'; norm_num at hm'
    refine ⟨fun i hi => ?_, rfl, rfl, rfl⟩
    have : i = 0 := by omega
    subst this; exact ⟨hx1, hxb, hj1⟩
  | succ n ih =>
    intro C hx1 hxb hc_lt
    unfold runSeedSteps
    have hx0 : Nat.beq C.x 0 = false := by
      cases h : Nat.beq C.x 0 with
      | false => rfl
      | true => have := Nat.eq_of_beq_eq_true h; omega
    rw [hx0]
    cases hm1 : Nat.ble (2 ^ C.j) 1 with
    | true =>
      dsimp only; intro hx' _; omega
    | false =>
      have hj1 : 1 ≤ C.j := by
        by_contra h0; have : C.j = 0 := by omega
        rw [this] at hm1; exact absurd hm1 (by decide)
      cases hev : Nat.beq (C.c % 2) 0 with
      | true =>
        have hc0 : C.c % 2 = 0 := Nat.eq_of_beq_eq_true hev
        have hstep : cylStep b C = ⟨(C.x * ((b + 1) / 2)) % b, C.c / 2, C.j - 1⟩ :=
          cylStep_even_eq hj1 hc_lt hc0
        have hpos := half_pos_lt hb3 hb_odd hx1 hxb
        have hdiv2 : 2 ^ C.j / 2 = 2 ^ (C.j - 1) := two_pow_div_two hj1
        have hclt' : C.c / 2 < 2 ^ (C.j - 1) := by
          have := cylStep_c_lt (b := b) C; rw [hstep] at this; exact this
        dsimp only
        rw [hdiv2]
        have hih := ih ⟨(C.x * ((b + 1) / 2)) % b, C.c / 2, C.j - 1⟩ hpos.1 hpos.2 hclt'
        dsimp only at hih ⊢
        intro hx' hm'
        obtain ⟨hval, hx_eq, hc_eq, hm_eq⟩ := hih hx' hm'
        refine ⟨fun i hi => ?_, ?_, ?_, ?_⟩
        · cases i with
          | zero => exact ⟨hx1, hxb, hj1⟩
          | succ i => rw [Function.iterate_succ_apply, hstep]; exact hval i (by omega)
        · rw [Function.iterate_succ_apply, hstep]; exact hx_eq
        · rw [Function.iterate_succ_apply, hstep]; exact hc_eq
        · rw [Function.iterate_succ_apply, hstep]; exact hm_eq
      | false =>
        have hodd : C.c % 2 ≠ 0 := fun h => by rw [h] at hev; exact absurd hev (by decide)
        have hstep := cylStep_odd_eq (b := b) hodd
        have hp2 : p2v2 C.x = 2 ^ padicValNat 2 C.x := p2v2_eq_two_pow_padicValNat hx1 (by omega)
        have hmul : 2 ^ C.j * p2v2 C.x = 2 ^ (C.j + padicValNat 2 C.x) := by
          rw [hp2, ← pow_add]
        dsimp only
        rw [hmul]
        by_cases hx1_zero : (C.x * C.x + 1) % b = 0
        · rw [hx1_zero]
          cases n with
          | zero => dsimp only [runSeedSteps]; intro hx' _; omega
          | succ n' => dsimp only [runSeedSteps]; intro hx' _; omega
        · have hx1_pos : 1 ≤ (C.x * C.x + 1) % b := by omega
          have hx1_lt : (C.x * C.x + 1) % b < b := Nat.mod_lt _ (by omega)
          have hclt' : (C.x * C.c + 1) % 2 ^ (C.j + padicValNat 2 C.x) < 2 ^ (C.j + padicValNat 2 C.x) :=
            Nat.mod_lt _ (Nat.pow_pos (by decide))
          have hih := ih ⟨(C.x * C.x + 1) % b, (C.x * C.c + 1) % 2 ^ (C.j + padicValNat 2 C.x),
              C.j + padicValNat 2 C.x⟩ hx1_pos hx1_lt hclt'
          dsimp only at hih ⊢
          intro hx' hm'
          obtain ⟨hval, hx_eq, hc_eq, hm_eq⟩ := hih hx' hm'
          refine ⟨fun i hi => ?_, ?_, ?_, ?_⟩
          · cases i with
            | zero => exact ⟨hx1, hxb, hj1⟩
            | succ i => rw [Function.iterate_succ_apply, hstep]; exact hval i (by omega)
          · rw [Function.iterate_succ_apply, hstep]; exact hx_eq
          · rw [Function.iterate_succ_apply, hstep]; exact hc_eq
          · rw [Function.iterate_succ_apply, hstep]; exact hm_eq

private lemma cylSubset_refl {b : ℕ} (C : OddCyl) : CylSubset b C C :=
  ⟨rfl, le_refl _, rfl⟩

private lemma cylSubset_trans {b : ℕ} {C1 C2 C3 : OddCyl}
    (h12 : CylSubset b C1 C2) (h23 : CylSubset b C2 C3) : CylSubset b C1 C3 := by
  refine ⟨h12.1.trans h23.1, le_trans h23.2.1 h12.2.1, ?_⟩
  have hd : 2 ^ C3.j ∣ 2 ^ C2.j := pow_dvd_pow 2 h23.2.1
  rw [← Nat.mod_mod_of_dvd C1.c hd, h12.2.2, Nat.mod_mod_of_dvd C2.c hd, h23.2.2]

private lemma checkSeed_sound {b : ℕ} (hb3 : 3 ≤ b) (hb_lt : b < 2048) (hb_odd : b % 2 = 1)
    {s : ℕ × ℕ × ℕ} (hs : checkSeed b ((b + 1) / 2) s = true) :
    1 ≤ s.1 ∧ s.1 < b ∧ IsCertifiedEscape b s.1 := by
  rcases s with ⟨x, kStart, p⟩
  unfold checkSeed at hs
  have ha1 := Bool.and_eq_true_iff.mp hs
  have ha2 := Bool.and_eq_true_iff.mp ha1.1
  have ha3 := Bool.and_eq_true_iff.mp ha2.1
  have ha4 := Bool.and_eq_true_iff.mp ha3.1
  have ha5 := Bool.and_eq_true_iff.mp ha4.1
  have hx1 : 1 ≤ x := Nat.ble_eq.mp ha5.1
  have hxb : x + 1 ≤ b := Nat.ble_eq.mp ha5.2
  have hp1 : 1 ≤ p := Nat.ble_eq.mp ha4.2
  have hk_le : kStart ≤ 1440 := Nat.ble_eq.mp ha3.2
  have hp_le : p ≤ 1440 := Nat.ble_eq.mp ha2.2
  have hrest := ha1.2
  rw [runSeedChunks_eq_runSeedSteps 8 kStart x 1 2 (by omega)] at hrest
  rcases h1 : runSeedSteps b ((b + 1) / 2) kStart x 1 2 with ⟨x1, c1, m1⟩
  rw [h1] at hrest
  dsimp only at hrest
  have hb1 := Bool.and_eq_true_iff.mp hrest
  have hb2 := Bool.and_eq_true_iff.mp hb1.1
  have hx1_pos : 1 ≤ x1 := Nat.ble_eq.mp hb2.1
  have hm1_ge2 : 2 ≤ m1 := Nat.ble_eq.mp hb2.2
  have hrest2 := hb1.2
  rw [runSeedChunks_eq_runSeedSteps 8 p x1 c1 m1 (by omega)] at hrest2
  rcases h2 : runSeedSteps b ((b + 1) / 2) p x1 c1 m1 with ⟨x2, c2, m2⟩
  rw [h2] at hrest2
  dsimp only at hrest2
  have hc1 := Bool.and_eq_true_iff.mp hrest2
  have hc2 := Bool.and_eq_true_iff.mp hc1.1
  have hc3 := Bool.and_eq_true_iff.mp hc2.1
  have hc4 := Bool.and_eq_true_iff.mp hc3.1
  have hx2_pos : 1 ≤ x2 := Nat.ble_eq.mp hc4.1
  have hm2_ge2 : 2 ≤ m2 := Nat.ble_eq.mp hc4.2
  have hx2_eq : Nat.beq x2 x1 = true := hc3.2
  have hm12 : m1 ≤ m2 := Nat.ble_eq.mp hc2.2
  have hc_eq : Nat.beq (c2 % m1) (c1 % m1) = true := hc1.2
  have hs1 := runSeedSteps_sound hb3 hb_lt hb_odd kStart ⟨x, 1, 1⟩ hx1 (by dsimp; omega) (by dsimp; norm_num)
  rw [show (2 : ℕ) ^ 1 = 2 by norm_num, h1] at hs1
  obtain ⟨hval1, hx1_eq, hc1_eq, hm1_eq⟩ := hs1 hx1_pos hm1_ge2
  set C1 := (cylStep b)^[kStart] ⟨x, 1, 1⟩
  have hC1_val := hval1 kStart (le_refl kStart)
  have hC1_clt : C1.c < 2 ^ C1.j := by
    dsimp only [C1]
    cases kStart with
    | zero => norm_num
    | succ k' => rw [Function.iterate_succ_apply']; exact cylStep_c_lt _
  have hs2 := runSeedSteps_sound hb3 hb_lt hb_odd p C1 hC1_val.1 hC1_val.2.1 hC1_clt
  rw [← hx1_eq, ← hc1_eq, ← hm1_eq, h2] at hs2
  obtain ⟨hval2, hx2_eq', hc2_eq', hm2_eq'⟩ := hs2 hx2_pos hm2_ge2
  have hret : CylSubset b ((cylStep b)^[p] C1) C1 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← hx2_eq', Nat.eq_of_beq_eq_true hx2_eq, hx1_eq]
    · have hpow_le : 2 ^ C1.j ≤ 2 ^ ((cylStep b)^[p] C1).j := by
        rw [← hm1_eq, ← hm2_eq']; exact hm12
      exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow_le
    · rw [← hc2_eq', ← hc1_eq, ← hm1_eq]
      exact Nat.eq_of_beq_eq_true hc_eq
  exact ⟨hx1, by omega, kStart, p, C1, hp1, hval1, cylSubset_refl C1, hval2, hret⟩

private lemma checkSeeds_sound {b : ℕ} (hb3 : 3 ≤ b) (hb_lt : b < 2048) (hb_odd : b % 2 = 1)
    {seeds : List (ℕ × ℕ × ℕ)} (h : checkSeeds b ((b + 1) / 2) seeds = true) :
    ∀ s ∈ seeds, 1 ≤ s.1 ∧ s.1 < b ∧ IsCertifiedEscape b s.1 := by
  induction seeds with
  | nil => intro _ hm; cases hm
  | cons s rest ih =>
    simp only [checkSeeds, Bool.and_eq_true] at h
    intro t ht
    cases ht with
    | head => exact checkSeed_sound hb3 hb_lt hb_odd h.1
    | tail _ hmem => exact ih h.2 t hmem

private lemma memSeeds_sound {x : ℕ} {seeds : List (ℕ × ℕ × ℕ)}
    (h : memSeeds x seeds = true) : ∃ s ∈ seeds, s.1 = x := by
  induction seeds with
  | nil => simp [memSeeds] at h
  | cons s rest ih =>
    rcases s with ⟨sx, k, p⟩
    simp only [memSeeds] at h
    cases hb : Nat.beq x sx with
    | true => exact ⟨(sx, k, p), List.mem_cons_self .., (Nat.eq_of_beq_eq_true hb).symm⟩
    | false =>
      rw [hb] at h
      obtain ⟨t, ht, htx⟩ := ih h
      exact ⟨t, List.mem_cons_of_mem _ ht, htx⟩

/-- Monotonicity of `cylStep` under `CylSubset`. -/
private lemma cylSubset_cylStep {b : ℕ} {C1 C2 : OddCyl}
    (hsub : CylSubset b C1 C2)
    (_hx1 : 1 ≤ C1.x) (hx1_lt : C1.x < b)
    (_hx2 : 1 ≤ C2.x) (hx2_lt : C2.x < b)
    (hj2 : 1 ≤ C2.j) :
    CylSubset b (cylStep b C1) (cylStep b C2) := by
  have hx_eq : C1.x = C2.x := by
    have := hsub.1
    rw [Nat.mod_eq_of_lt hx1_lt, Nat.mod_eq_of_lt hx2_lt] at this
    exact this
  have h2dvd : 2 ∣ 2 ^ C2.j := dvd_pow_self 2 (by omega)
  have hpar : C1.c % 2 = C2.c % 2 := by
    rw [← Nat.mod_mod_of_dvd C1.c h2dvd, hsub.2.2, Nat.mod_mod_of_dvd C2.c h2dvd]
  have hj_le0 : C2.j ≤ C1.j := hsub.2.1
  unfold cylStep
  by_cases hev : C2.c % 2 = 0
  · have hev1 : C1.c % 2 = 0 := by omega
    simp only [hev, hev1, ↓reduceIte, CylSubset, hx_eq]
    refine ⟨trivial, by omega, ?_⟩
    have hj_eq : 2 ^ C2.j = 2 * 2 ^ (C2.j - 1) := by
      conv_lhs => rw [show C2.j = (C2.j - 1) + 1 by omega, pow_succ']
    have hdvd_sub : 2 ^ (C2.j - 1) ∣ 2 ^ (C1.j - 1) := pow_dvd_pow 2 (by omega)
    rw [Nat.mod_mod_of_dvd _ hdvd_sub, Nat.mod_mod,
        nat_div_mod_two C1.c, nat_div_mod_two C2.c, ← hj_eq, hsub.2.2]
  · have hodd1 : C1.c % 2 ≠ 0 := by omega
    simp only [hev, hodd1, ↓reduceIte, CylSubset, hx_eq]
    set a := padicValNat 2 C2.x
    have hj_le : C2.j + a ≤ C1.j + a := by omega
    refine ⟨trivial, hj_le, ?_⟩
    have hdvd_sub : 2 ^ (C2.j + a) ∣ 2 ^ (C1.j + a) := pow_dvd_pow 2 hj_le
    rw [Nat.mod_mod_of_dvd _ hdvd_sub, Nat.mod_mod]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2a_dvd : 2 ^ a ∣ C2.x := pow_padicValNat_dvd
    obtain ⟨u, hu⟩ := h2a_dvd
    have hcast : (C1.c : ZMod (2 ^ C2.j)) = (C2.c : ZMod (2 ^ C2.j)) :=
      (ZMod.natCast_eq_natCast_iff' C1.c C2.c (2 ^ C2.j)).mpr hsub.2.2
    have hdiff : (2 ^ C2.j : ℤ) ∣ (C1.c : ℤ) - (C2.c : ℤ) := by
      have : (((C1.c : ℤ) - (C2.c : ℤ) : ℤ) : ZMod (2 ^ C2.j)) = 0 := by
        push_cast; exact sub_eq_zero.mpr hcast
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
    obtain ⟨k, hk⟩ := hdiff
    have hmul_dvd : (2 ^ (C2.j + a) : ℤ) ∣
        ((C2.x * C1.c + 1 : ℕ) : ℤ) - ((C2.x * C2.c + 1 : ℕ) : ℤ) := by
      have h1 : ((C2.x * C1.c + 1 : ℕ) : ℤ) - ((C2.x * C2.c + 1 : ℕ) : ℤ) =
          (C2.x : ℤ) * ((C1.c : ℤ) - (C2.c : ℤ)) := by push_cast; ring
      rw [h1, hu, pow_add]
      push_cast
      refine ⟨(u : ℤ) * k, ?_⟩
      rw [hk]; ring
    have hzm : (((C2.x * C1.c + 1 : ℕ) : ZMod (2 ^ (C2.j + a))) =
        ((C2.x * C2.c + 1 : ℕ) : ZMod (2 ^ (C2.j + a)))) := by
      apply sub_eq_zero.mp
      have h0 : ((((C2.x * C1.c + 1 : ℕ) : ℤ) - ((C2.x * C2.c + 1 : ℕ) : ℤ)) :
          ZMod (2 ^ (C2.j + a))) = 0 := by
        rw [← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact_mod_cast hmul_dvd
      simpa [Int.cast_sub, Int.cast_natCast] using h0
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hzm

private lemma cylSubset_cylStep_iter {b : ℕ} (hb3 : 3 ≤ b) :
    ∀ (t : ℕ) (C1 C2 : OddCyl),
      CylSubset b C1 C2 → C1.x < b → C2.x < b →
      (∀ i < t, 1 ≤ ((cylStep b)^[i] C2).x ∧ ((cylStep b)^[i] C2).x < b ∧
                1 ≤ ((cylStep b)^[i] C2).j) →
      ∀ i ≤ t,
        CylSubset b ((cylStep b)^[i] C1) ((cylStep b)^[i] C2) ∧
        (i < t → 1 ≤ ((cylStep b)^[i] C1).x ∧ ((cylStep b)^[i] C1).x < b ∧
                 1 ≤ ((cylStep b)^[i] C1).j) := by
  intro t
  induction t with
  | zero =>
    intro C1 C2 hsub _ _ _ i hi
    have : i = 0 := by omega
    subst this
    exact ⟨hsub, fun h => by omega⟩
  | succ t ih =>
    intro C1 C2 hsub hlt1 hlt2 hval i hi
    have hv0 := hval 0 (by omega)
    simp only [Function.iterate_zero, id_eq] at hv0
    have hx1_eq : C1.x = C2.x := by
      have := hsub.1
      rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at this; exact this
    have hv1_0 : 1 ≤ C1.x ∧ C1.x < b ∧ 1 ≤ C1.j :=
      ⟨by omega, hlt1, le_trans hv0.2.2 hsub.2.1⟩
    cases i with
    | zero => exact ⟨hsub, fun _ => hv1_0⟩
    | succ i =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      have hsub' := cylSubset_cylStep hsub hv1_0.1 hlt1 hv0.1 hlt2 hv0.2.2
      have hval' : ∀ r < t, 1 ≤ ((cylStep b)^[r] (cylStep b C2)).x ∧
          ((cylStep b)^[r] (cylStep b C2)).x < b ∧ 1 ≤ ((cylStep b)^[r] (cylStep b C2)).j := by
        intro r hr
        have := hval (r + 1) (by omega)
        rwa [Function.iterate_succ_apply] at this
      have hres := ih (cylStep b C1) (cylStep b C2) hsub' (cylStep_x_lt hb3 C1) (cylStep_x_lt hb3 C2) hval' i (by omega)
      exact ⟨hres.1, fun hlt => hres.2 (by omega)⟩

/-! ## Section 3: `traceRunLoop` & `tracePureLoop` Soundness -/

private lemma traceRunChunk_sound {b : ℕ} (hb3 : 3 ≤ b) (hb_lt : b < 2048) (hb_odd : b % 2 = 1)
    (dt : QT) :
    ∀ (fuel : ℕ) (C : OddCyl),
      1 ≤ C.x → C.x < b → 1 ≤ C.j → C.c < 2 ^ C.j →
      match traceRunChunk b ((b + 1) / 2) dt fuel C.x C.c (2 ^ C.j) with
      | (2, _, _, _) =>
        ∃ s y, 1 ≤ y ∧ y < b ∧ getTag dt y = 1 ∧
          (∀ i ≤ s, 1 ≤ ((cylStep b)^[i] C).x ∧ ((cylStep b)^[i] C).x < b ∧
                    1 ≤ ((cylStep b)^[i] C).j) ∧
          CylSubset b ((cylStep b)^[s] C) ⟨y, 1, 1⟩
      | (0, x', c', m') =>
        ∃ s,
          (∀ i ≤ s, 1 ≤ ((cylStep b)^[i] C).x ∧ ((cylStep b)^[i] C).x < b ∧
                    1 ≤ ((cylStep b)^[i] C).j) ∧
          x' = ((cylStep b)^[s] C).x ∧ c' = ((cylStep b)^[s] C).c ∧ m' = 2 ^ ((cylStep b)^[s] C).j
      | _ => True := by
  intro fuel
  induction fuel with
  | zero =>
    intro C hx1 hxb hj1 _
    simp only [traceRunChunk]
    exact ⟨0, fun i hi => by
      have hi0 : i = 0 := by omega
      subst hi0; exact ⟨hx1, hxb, hj1⟩, rfl, rfl, rfl⟩
  | succ fuel ih =>
    intro C hx1 hxb hj1 hc_lt
    simp only [traceRunChunk]
    cases hev : Nat.beq (C.c % 2) 0 with
    | true =>
      have hc0 : C.c % 2 = 0 := Nat.eq_of_beq_eq_true hev
      have hdiv2 : 2 ^ C.j / 2 = 2 ^ (C.j - 1) := two_pow_div_two hj1
      dsimp only
      rw [hdiv2]
      cases hm1 : Nat.beq (2 ^ (C.j - 1)) 1 with
      | true => trivial
      | false =>
        have hj' : 1 ≤ C.j - 1 := by
          by_contra h0; have : C.j - 1 = 0 := by omega
          rw [this] at hm1; exact absurd hm1 (by decide)
        have hstep := cylStep_even_eq (b := b) hj1 hc_lt hc0
        have hpos := half_pos_lt hb3 hb_odd hx1 hxb
        have hclt' : C.c / 2 < 2 ^ (C.j - 1) := by
          have := cylStep_c_lt (b := b) C; rw [hstep] at this; exact this
        have hih := ih ⟨(C.x * ((b + 1) / 2)) % b, C.c / 2, C.j - 1⟩ hpos.1 hpos.2 hj' hclt'
        dsimp only at hih ⊢
        rcases htr : traceRunChunk b ((b + 1) / 2) dt fuel ((C.x * ((b + 1) / 2)) % b) (C.c / 2) (2 ^ (C.j - 1)) with
          ⟨r, x', c', m'⟩
        rw [htr] at hih
        match r with
        | 2 =>
          obtain ⟨s, y, hy1, hyb, htg, hval, hsub⟩ := hih
          refine ⟨s + 1, y, hy1, hyb, htg, fun i hi => ?_, ?_⟩
          · cases i with
            | zero => exact ⟨hx1, hxb, hj1⟩
            | succ i => rw [Function.iterate_succ_apply, hstep]; exact hval i (by omega)
          · rw [Function.iterate_succ_apply, hstep]; exact hsub
        | 0 =>
          obtain ⟨s, hval, hxe, hce, hme⟩ := hih
          refine ⟨s + 1, fun i hi => ?_, ?_, ?_, ?_⟩
          · cases i with
            | zero => exact ⟨hx1, hxb, hj1⟩
            | succ i => rw [Function.iterate_succ_apply, hstep]; exact hval i (by omega)
          · rw [Function.iterate_succ_apply, hstep]; exact hxe
          · rw [Function.iterate_succ_apply, hstep]; exact hce
          · rw [Function.iterate_succ_apply, hstep]; exact hme
        | 1 => trivial
        | _ + 3 => trivial
    | false =>
      have hodd : C.c % 2 ≠ 0 := fun h => by rw [h] at hev; exact absurd hev (by decide)
      cases htg : Nat.beq (getTag dt C.x) 1 with
      | true =>
        refine ⟨0, C.x, hx1, hxb, Nat.eq_of_beq_eq_true htg, fun i hi => ?_, ?_⟩
        · have hi0 : i = 0 := by omega
          subst hi0; exact ⟨hx1, hxb, hj1⟩
        · exact ⟨rfl, hj1, by simpa using (show C.c % 2 = 1 by omega)⟩
      | false =>
        cases hx0 : Nat.beq ((C.x * C.x + 1) % b) 0 with
        | true => trivial
        | false =>
          have hx1_pos : 1 ≤ (C.x * C.x + 1) % b := by
            have hne : (C.x * C.x + 1) % b ≠ 0 := fun h => by rw [h] at hx0; exact absurd hx0 (by decide)
            omega
          have hx1_lt : (C.x * C.x + 1) % b < b := Nat.mod_lt _ (by omega)
          have hstep := cylStep_odd_eq (b := b) hodd
          have hp2 : p2v2 C.x = 2 ^ padicValNat 2 C.x := p2v2_eq_two_pow_padicValNat hx1 (by omega)
          have hmul : 2 ^ C.j * p2v2 C.x = 2 ^ (C.j + padicValNat 2 C.x) := by rw [hp2, ← pow_add]
          dsimp only
          rw [hmul]
          have hclt' : (C.x * C.c + 1) % 2 ^ (C.j + padicValNat 2 C.x) < 2 ^ (C.j + padicValNat 2 C.x) :=
            Nat.mod_lt _ (Nat.pow_pos (by decide))
          have hih := ih ⟨(C.x * C.x + 1) % b, (C.x * C.c + 1) % 2 ^ (C.j + padicValNat 2 C.x),
              C.j + padicValNat 2 C.x⟩ hx1_pos hx1_lt (Nat.le_add_right_of_le hj1) hclt'
          dsimp only at hih ⊢
          rcases htr : traceRunChunk b ((b + 1) / 2) dt fuel ((C.x * C.x + 1) % b)
              ((C.x * C.c + 1) % 2 ^ (C.j + padicValNat 2 C.x)) (2 ^ (C.j + padicValNat 2 C.x)) with
            ⟨r, x', c', m'⟩
          rw [htr] at hih
          match r with
          | 2 =>
            obtain ⟨s, y, hy1, hyb, htg', hval, hsub⟩ := hih
            refine ⟨s + 1, y, hy1, hyb, htg', fun i hi => ?_, ?_⟩
            · cases i with
              | zero => exact ⟨hx1, hxb, hj1⟩
              | succ i => rw [Function.iterate_succ_apply, hstep]; exact hval i (by omega)
            · rw [Function.iterate_succ_apply, hstep]; exact hsub
          | 0 =>
            obtain ⟨s, hval, hxe, hce, hme⟩ := hih
            refine ⟨s + 1, fun i hi => ?_, ?_, ?_, ?_⟩
            · cases i with
              | zero => exact ⟨hx1, hxb, hj1⟩
              | succ i => rw [Function.iterate_succ_apply, hstep]; exact hval i (by omega)
            · rw [Function.iterate_succ_apply, hstep]; exact hxe
            · rw [Function.iterate_succ_apply, hstep]; exact hce
            · rw [Function.iterate_succ_apply, hstep]; exact hme
          | 1 => trivial
          | _ + 3 => trivial

private lemma traceRunLoop_sound {b : ℕ} (hb3 : 3 ≤ b) (hb_lt : b < 2048) (hb_odd : b % 2 = 1)
    (dt : QT) :
    ∀ (k : ℕ) (C : OddCyl),
      1 ≤ C.x → C.x < b → 1 ≤ C.j → C.c < 2 ^ C.j →
      traceRunLoop b ((b + 1) / 2) dt k C.x C.c (2 ^ C.j) = true →
      ∃ s y, 1 ≤ y ∧ y < b ∧ getTag dt y = 1 ∧
        (∀ i ≤ s, 1 ≤ ((cylStep b)^[i] C).x ∧ ((cylStep b)^[i] C).x < b ∧
                  1 ≤ ((cylStep b)^[i] C).j) ∧
        CylSubset b ((cylStep b)^[s] C) ⟨y, 1, 1⟩ := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ h; simp [traceRunLoop] at h
  | succ k ih =>
    intro C hx1 hxb hj1 hc_lt h
    simp only [traceRunLoop] at h
    have hc := traceRunChunk_sound hb3 hb_lt hb_odd dt 180 C hx1 hxb hj1 hc_lt
    rcases htr : traceRunChunk b ((b + 1) / 2) dt 180 C.x C.c (2 ^ C.j) with ⟨r, x', c', m'⟩
    rw [htr] at hc h
    match r with
    | 2 => exact hc
    | 0 =>
      obtain ⟨s1, hval1, hxe, hce, hme⟩ := hc
      set C1 := (cylStep b)^[s1] C
      have hC1_val := hval1 s1 (le_refl s1)
      have hC1_clt : C1.c < 2 ^ C1.j := by
        dsimp only [C1]
        cases s1 with
        | zero => exact hc_lt
        | succ s1' => rw [Function.iterate_succ_apply']; exact cylStep_c_lt _
      rw [hxe, hce, hme] at h
      obtain ⟨s2, y, hy1, hyb, htg, hval2, hsub⟩ := ih C1 hC1_val.1 hC1_val.2.1 hC1_val.2.2 hC1_clt h
      refine ⟨s1 + s2, y, hy1, hyb, htg, fun i hi => ?_, ?_⟩
      · by_cases hle : i ≤ s1
        · exact hval1 i hle
        · rw [show i = (i - s1) + s1 by omega, Function.iterate_add_apply]
          exact hval2 (i - s1) (by omega)
      · rw [show s1 + s2 = s2 + s1 by omega, Function.iterate_add_apply]; exact hsub
    | 1 => simp at h
    | _ + 3 => simp at h

private lemma tracePureChunk_sound {b : ℕ} (hb3 : 3 ≤ b) (hb_lt : b < 2048) (hb_odd : b % 2 = 1) :
    ∀ (fuel : ℕ) (C : OddCyl),
      1 ≤ C.x → C.x < b → 1 ≤ C.j → C.c < 2 ^ C.j →
      match tracePureChunk b ((b + 1) / 2) fuel C.x C.c (2 ^ C.j) with
      | (1, _, _, _) =>
        ∃ s, 1 ≤ s ∧
          (∀ i < s, 1 ≤ ((cylStep b)^[i] C).x ∧ ((cylStep b)^[i] C).x < b ∧
                    1 ≤ ((cylStep b)^[i] C).j) ∧
          ((cylStep b)^[s] C).x = 0
      | (y + 3, _, _, _) =>
        1 ≤ y ∧ y < b ∧ ∃ s, 1 ≤ s ∧
          (∀ i < s, 1 ≤ ((cylStep b)^[i] C).x ∧ ((cylStep b)^[i] C).x < b ∧
                    1 ≤ ((cylStep b)^[i] C).j) ∧
          (cylStep b)^[s] C = ⟨y, 0, 0⟩
      | (0, x', c', m') =>
        ∃ s,
          (∀ i ≤ s, 1 ≤ ((cylStep b)^[i] C).x ∧ ((cylStep b)^[i] C).x < b ∧
                    1 ≤ ((cylStep b)^[i] C).j) ∧
          x' = ((cylStep b)^[s] C).x ∧ c' = ((cylStep b)^[s] C).c ∧ m' = 2 ^ ((cylStep b)^[s] C).j
      | (2, _, _, _) => False := by
  intro fuel
  induction fuel with
  | zero =>
    intro C hx1 hxb hj1 _
    simp only [tracePureChunk]
    exact ⟨0, fun i hi => by
      have hi0 : i = 0 := by omega
      subst hi0; exact ⟨hx1, hxb, hj1⟩, rfl, rfl, rfl⟩
  | succ fuel ih =>
    intro C hx1 hxb hj1 hc_lt
    simp only [tracePureChunk]
    cases hev : Nat.beq (C.c % 2) 0 with
    | true =>
      have hc0 : C.c % 2 = 0 := Nat.eq_of_beq_eq_true hev
      have hdiv2 : 2 ^ C.j / 2 = 2 ^ (C.j - 1) := two_pow_div_two hj1
      have hstep := cylStep_even_eq (b := b) hj1 hc_lt hc0
      have hpos := half_pos_lt hb3 hb_odd hx1 hxb
      dsimp only
      rw [hdiv2]
      cases hm1 : Nat.beq (2 ^ (C.j - 1)) 1 with
      | true =>
        have hj0 : C.j - 1 = 0 := by
          have h1 : 2 ^ (C.j - 1) = 1 := Nat.eq_of_beq_eq_true hm1
          by_contra hne
          have : 2 ^ 1 ≤ 2 ^ (C.j - 1) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have hc_div : C.c / 2 = 0 := by
          have : C.j = 1 := by omega
          rw [this] at hc_lt; omega
        have hstep0 : cylStep b C = ⟨(C.x * ((b + 1) / 2)) % b, 0, 0⟩ := by
          rw [hstep, hj0, hc_div]
        rw [show 3 + (C.x * ((b + 1) / 2)) % b = (C.x * ((b + 1) / 2)) % b + 3 by omega]
        refine ⟨hpos.1, hpos.2, 1, le_refl 1, fun i hi => ?_, hstep0⟩
        have hi0 : i = 0 := by omega
        subst hi0; exact ⟨hx1, hxb, hj1⟩
      | false =>
        have hj' : 1 ≤ C.j - 1 := by
          by_contra h0; have : C.j - 1 = 0 := by omega
          rw [this] at hm1; exact absurd hm1 (by decide)
        have hclt' : C.c / 2 < 2 ^ (C.j - 1) := by
          have := cylStep_c_lt (b := b) C; rw [hstep] at this; exact this
        have hih := ih ⟨(C.x * ((b + 1) / 2)) % b, C.c / 2, C.j - 1⟩ hpos.1 hpos.2 hj' hclt'
        dsimp only at hih ⊢
        rcases htr : tracePureChunk b ((b + 1) / 2) fuel ((C.x * ((b + 1) / 2)) % b) (C.c / 2) (2 ^ (C.j - 1)) with
          ⟨r, x', c', m'⟩
        rw [htr] at hih
        match r with
        | 1 =>
          obtain ⟨s, hs1, hval, hx0⟩ := hih
          refine ⟨s + 1, by omega, fun i hi => ?_, ?_⟩
          · cases i with
            | zero => exact ⟨hx1, hxb, hj1⟩
            | succ i => rw [Function.iterate_succ_apply, hstep]; exact hval i (by omega)
          · rw [Function.iterate_succ_apply, hstep]; exact hx0
        | y + 3 =>
          obtain ⟨hy1, hyb, s, hs1, hval, hy_eq⟩ := hih
          refine ⟨hy1, hyb, s + 1, by omega, fun i hi => ?_, ?_⟩
          · cases i with
            | zero => exact ⟨hx1, hxb, hj1⟩
            | succ i => rw [Function.iterate_succ_apply, hstep]; exact hval i (by omega)
          · rw [Function.iterate_succ_apply, hstep]; exact hy_eq
        | 0 =>
          obtain ⟨s, hval, hxe, hce, hme⟩ := hih
          refine ⟨s + 1, fun i hi => ?_, ?_, ?_, ?_⟩
          · cases i with
            | zero => exact ⟨hx1, hxb, hj1⟩
            | succ i => rw [Function.iterate_succ_apply, hstep]; exact hval i (by omega)
          · rw [Function.iterate_succ_apply, hstep]; exact hxe
          · rw [Function.iterate_succ_apply, hstep]; exact hce
          · rw [Function.iterate_succ_apply, hstep]; exact hme
        | 2 => exact hih
    | false =>
      have hodd : C.c % 2 ≠ 0 := fun h => by rw [h] at hev; exact absurd hev (by decide)
      have hstep := cylStep_odd_eq (b := b) hodd
      dsimp only
      cases hx0 : Nat.beq ((C.x * C.x + 1) % b) 0 with
      | true =>
        refine ⟨1, le_refl 1, fun i hi => ?_, ?_⟩
        · have hi0 : i = 0 := by omega
          subst hi0; exact ⟨hx1, hxb, hj1⟩
        · rw [Function.iterate_one, hstep]
          exact Nat.eq_of_beq_eq_true hx0
      | false =>
        have hx1_pos : 1 ≤ (C.x * C.x + 1) % b := by
          have hne : (C.x * C.x + 1) % b ≠ 0 := fun h => by rw [h] at hx0; exact absurd hx0 (by decide)
          omega
        have hx1_lt : (C.x * C.x + 1) % b < b := Nat.mod_lt _ (by omega)
        have hp2 : p2v2 C.x = 2 ^ padicValNat 2 C.x := p2v2_eq_two_pow_padicValNat hx1 (by omega)
        have hmul : 2 ^ C.j * p2v2 C.x = 2 ^ (C.j + padicValNat 2 C.x) := by rw [hp2, ← pow_add]
        rw [hmul]
        have hclt' : (C.x * C.c + 1) % 2 ^ (C.j + padicValNat 2 C.x) < 2 ^ (C.j + padicValNat 2 C.x) :=
          Nat.mod_lt _ (Nat.pow_pos (by decide))
        have hih := ih ⟨(C.x * C.x + 1) % b, (C.x * C.c + 1) % 2 ^ (C.j + padicValNat 2 C.x),
            C.j + padicValNat 2 C.x⟩ hx1_pos hx1_lt (Nat.le_add_right_of_le hj1) hclt'
        dsimp only at hih ⊢
        rcases htr : tracePureChunk b ((b + 1) / 2) fuel ((C.x * C.x + 1) % b)
            ((C.x * C.c + 1) % 2 ^ (C.j + padicValNat 2 C.x)) (2 ^ (C.j + padicValNat 2 C.x)) with
          ⟨r, x', c', m'⟩
        rw [htr] at hih
        match r with
        | 1 =>
          obtain ⟨s, hs1, hval, hx0'⟩ := hih
          refine ⟨s + 1, by omega, fun i hi => ?_, ?_⟩
          · cases i with
            | zero => exact ⟨hx1, hxb, hj1⟩
            | succ i => rw [Function.iterate_succ_apply, hstep]; exact hval i (by omega)
          · rw [Function.iterate_succ_apply, hstep]; exact hx0'
        | y + 3 =>
          obtain ⟨hy1, hyb, s, hs1, hval, hy_eq⟩ := hih
          refine ⟨hy1, hyb, s + 1, by omega, fun i hi => ?_, ?_⟩
          · cases i with
            | zero => exact ⟨hx1, hxb, hj1⟩
            | succ i => rw [Function.iterate_succ_apply, hstep]; exact hval i (by omega)
          · rw [Function.iterate_succ_apply, hstep]; exact hy_eq
        | 0 =>
          obtain ⟨s, hval, hxe, hce, hme⟩ := hih
          refine ⟨s + 1, fun i hi => ?_, ?_, ?_, ?_⟩
          · cases i with
            | zero => exact ⟨hx1, hxb, hj1⟩
            | succ i => rw [Function.iterate_succ_apply, hstep]; exact hval i (by omega)
          · rw [Function.iterate_succ_apply, hstep]; exact hxe
          · rw [Function.iterate_succ_apply, hstep]; exact hce
          · rw [Function.iterate_succ_apply, hstep]; exact hme
        | 2 => exact hih

private lemma tracePureLoop_sound {b : ℕ} (hb3 : 3 ≤ b) (hb_lt : b < 2048) (hb_odd : b % 2 = 1) :
    ∀ (k : ℕ) (C : OddCyl),
      1 ≤ C.x → C.x < b → 1 ≤ C.j → C.c < 2 ^ C.j →
      match tracePureLoop b ((b + 1) / 2) k C.x C.c (2 ^ C.j) with
      | 1 =>
        ∃ s, 1 ≤ s ∧
          (∀ i < s, 1 ≤ ((cylStep b)^[i] C).x ∧ ((cylStep b)^[i] C).x < b ∧
                    1 ≤ ((cylStep b)^[i] C).j) ∧
          ((cylStep b)^[s] C).x = 0
      | y + 3 =>
        1 ≤ y ∧ y < b ∧ ∃ s, 1 ≤ s ∧
          (∀ i < s, 1 ≤ ((cylStep b)^[i] C).x ∧ ((cylStep b)^[i] C).x < b ∧
                    1 ≤ ((cylStep b)^[i] C).j) ∧
          (cylStep b)^[s] C = ⟨y, 0, 0⟩
      | _ => True := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _; simp [tracePureLoop]
  | succ k ih =>
    intro C hx1 hxb hj1 hc_lt
    simp only [tracePureLoop]
    have hc := tracePureChunk_sound hb3 hb_lt hb_odd 180 C hx1 hxb hj1 hc_lt
    rcases htr : tracePureChunk b ((b + 1) / 2) 180 C.x C.c (2 ^ C.j) with ⟨r, x', c', m'⟩
    rw [htr] at hc
    match r with
    | 1 => exact hc
    | y + 3 => exact hc
    | 2 => exact False.elim hc
    | 0 =>
      obtain ⟨s1, hval1, hxe, hce, hme⟩ := hc
      set C1 := (cylStep b)^[s1] C
      have hC1_val := hval1 s1 (le_refl s1)
      have hC1_clt : C1.c < 2 ^ C1.j := by
        dsimp only [C1]
        cases s1 with
        | zero => exact hc_lt
        | succ s1' => rw [Function.iterate_succ_apply']; exact cylStep_c_lt _
      rw [hxe, hce, hme]
      show (match tracePureLoop b ((b + 1) / 2) k C1.x C1.c (2 ^ C1.j) with
        | 1 =>
          ∃ s, 1 ≤ s ∧
            (∀ i < s, 1 ≤ ((cylStep b)^[i] C).x ∧ ((cylStep b)^[i] C).x < b ∧
                      1 ≤ ((cylStep b)^[i] C).j) ∧
            ((cylStep b)^[s] C).x = 0
        | y + 3 =>
          1 ≤ y ∧ y < b ∧ ∃ s, 1 ≤ s ∧
            (∀ i < s, 1 ≤ ((cylStep b)^[i] C).x ∧ ((cylStep b)^[i] C).x < b ∧
                      1 ≤ ((cylStep b)^[i] C).j) ∧
            (cylStep b)^[s] C = ⟨y, 0, 0⟩
        | _ => True)
      have hih := ih C1 hC1_val.1 hC1_val.2.1 hC1_val.2.2 hC1_clt
      rcases hl : tracePureLoop b ((b + 1) / 2) k C1.x C1.c (2 ^ C1.j) with _ | _ | _ | y
      · trivial
      · rw [hl] at hih
        obtain ⟨s2, hs2, hval2, hx0⟩ := hih
        refine ⟨s1 + s2, by omega, fun i hi => ?_, ?_⟩
        · by_cases hle : i < s1
          · exact hval1 i (by omega)
          · rw [show i = (i - s1) + s1 by omega, Function.iterate_add_apply]
            exact hval2 (i - s1) (by omega)
        · rw [show s1 + s2 = s2 + s1 by omega, Function.iterate_add_apply]; exact hx0
      · trivial
      · rw [hl] at hih
        obtain ⟨hy1, hyb, s2, hs2, hval2, hy_eq⟩ := hih
        refine ⟨hy1, hyb, s1 + s2, by omega, fun i hi => ?_, ?_⟩
        · by_cases hle : i < s1
          · exact hval1 i (by omega)
          · rw [show i = (i - s1) + s1 by omega, Function.iterate_add_apply]
            exact hval2 (i - s1) (by omega)
        · rw [show s1 + s2 = s2 + s1 by omega, Function.iterate_add_apply]; exact hy_eq

/-! ## Section 4: Stretch Outcomes, Pullback Bijection & Exact Markov Contraction -/

private lemma cylStep_iter_mem {b : ℕ} (hb_odd : b % 2 = 1) :
    ∀ (s : ℕ) (C : OddCyl),
      (∀ i < s, 1 ≤ ((cylStep b)^[i] C).x ∧ ((cylStep b)^[i] C).x < b ∧
                1 ≤ ((cylStep b)^[i] C).j) →
      ∀ n, MemOddCyl b C n → MemOddCyl b ((cylStep b)^[s] C) ((f_b b)^[s] n) := by
  intro s
  induction s with
  | zero => intro _ _ n hn; simpa using hn
  | succ s ih =>
    intro C hval n hn
    have hv0 := hval 0 (by omega)
    simp only [Function.iterate_zero, id_eq] at hv0
    have hn1 := lem_odd_cylinders_step hb_odd hv0.1 hv0.2.1 hv0.2.2 hn
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (cylStep b C) (fun i hi => by
      have := hval (i + 1) (by omega); rwa [Function.iterate_succ_apply] at this) (f_b b n) hn1

/-- Multi-step cylinder pullback along a valid stretch `C → ... → ⟨y, 0, 0⟩`. -/
lemma stretch_pullback {b : ℕ} (hb_odd : b % 2 = 1) :
    ∀ (s : ℕ) (C : OddCyl) (y : ℕ),
      (∀ i < s, 1 ≤ ((cylStep b)^[i] C).x ∧ ((cylStep b)^[i] C).x < b ∧
                1 ≤ ((cylStep b)^[i] C).j) →
      (cylStep b)^[s] C = ⟨y, 0, 0⟩ →
      ∀ (e cStar : ℕ),
        ∃ c0 : ℕ, c0 < 2 ^ (C.j + e) ∧ c0 % 2 ^ C.j = C.c % 2 ^ C.j ∧
          ∀ n, (MemOddCyl b C n ∧ MemOddCyl b ⟨y, cStar, e⟩ ((f_b b)^[s] n)) ↔
            MemOddCyl b ⟨C.x, c0, C.j + e⟩ n := by
  intro s
  induction s with
  | zero =>
    intro C y _ hC e cStar
    simp only [Function.iterate_zero, id_eq] at hC
    subst hC
    refine ⟨cStar % 2 ^ e, by simpa using Nat.mod_lt cStar (Nat.pow_pos (by decide : 0 < 2) (n := e)),
      by simp [Nat.mod_one], fun n => ?_⟩
    simp only [Function.iterate_zero, id_eq, zero_add]
    constructor
    · rintro ⟨_, h2⟩
      exact ⟨h2.1, h2.2.1, by simpa [Nat.mod_mod] using h2.2.2⟩
    · intro h
      exact ⟨⟨h.1, h.2.1, by simp [Nat.mod_one]⟩, ⟨h.1, h.2.1, by simpa [Nat.mod_mod] using h.2.2⟩⟩
  | succ s ih =>
    intro C y hval hC e cStar
    have hv0 := hval 0 (by omega)
    simp only [Function.iterate_zero, id_eq] at hv0
    have hval' : ∀ i < s, 1 ≤ ((cylStep b)^[i] (cylStep b C)).x ∧
        ((cylStep b)^[i] (cylStep b C)).x < b ∧ 1 ≤ ((cylStep b)^[i] (cylStep b C)).j := by
      intro i hi
      have := hval (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    have hC' : (cylStep b)^[s] (cylStep b C) = ⟨y, 0, 0⟩ := by
      rwa [Function.iterate_succ_apply] at hC
    obtain ⟨c1, hc1_lt, hc1_mod, hiff1⟩ := ih (cylStep b C) y hval' hC' e cStar
    obtain ⟨c0, hc0_lt, hc0_mod, hiff0⟩ :=
      lem_odd_cylinders_pullback hb_odd hv0.1 hv0.2.1 hv0.2.2 e c1 hc1_mod
    refine ⟨c0, hc0_lt, hc0_mod, fun n => ?_⟩
    rw [Function.iterate_succ_apply]
    constructor
    · rintro ⟨hnC, hfn⟩
      have hn1 : MemOddCyl b (cylStep b C) (f_b b n) :=
        lem_odd_cylinders_step hb_odd hv0.1 hv0.2.1 hv0.2.2 hnC
      have h1 : MemOddCyl b ⟨(cylStep b C).x, c1, (cylStep b C).j + e⟩ (f_b b n) :=
        (hiff1 (f_b b n)).mp ⟨hn1, hfn⟩
      exact (hiff0 n).mp ⟨hnC, h1⟩
    · intro hn0
      obtain ⟨hnC, h1⟩ := (hiff0 n).mpr hn0
      exact ⟨hnC, ((hiff1 (f_b b n)).mpr h1).2⟩

/-- Existence of a positive integer in any cylinder `⟨x, c, j⟩` when `b` is odd (`gcd(b, 2^j) = 1`). -/
private lemma exists_memOddCyl {b x c j : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1) :
    ∃ n : ℕ, MemOddCyl b ⟨x, c, j⟩ n := by
  have hcop : Nat.Coprime b (2 ^ j) :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).symm.pow_right j
  let k := Nat.chineseRemainder hcop x c
  let n := k.val + b * 2 ^ j
  refine ⟨n, ?_, ?_, ?_⟩
  · have : 1 ≤ b * 2 ^ j := Nat.mul_pos (by omega) (by positivity)
    omega
  · have hmod := k.property.1
    dsimp [n]
    rw [Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod]
    exact hmod
  · have hmod := k.property.2
    dsimp [n]
    rw [Nat.add_mod, Nat.mul_mod_left, add_zero, Nat.mod_mod]
    exact hmod

/-- Even-half pullback: `n ∈ ⟨x, 2 * c, m + 1⟩` iff `n` is even in `x mod b` and `n / 2 ∈ ⟨half(x), c, m⟩`. -/
private lemma even_half_memOddCyl {b x c m n : ℕ} (_hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (_hx1 : 1 ≤ x) (_hxb : x < b) (hc_lt : c < 2 ^ m)
    (hn : MemOddCyl b ⟨x, 2 * c, m + 1⟩ n) :
    MemOddCyl b ⟨(x * ((b + 1) / 2)) % b, c, m⟩ (f_b b n) := by
  have h2dvd : 2 ∣ 2 ^ (m + 1) := dvd_pow_self 2 (by omega)
  have hpar : n % 2 = 0 := by
    have h1 := Nat.mod_mod_of_dvd n h2dvd
    have h2 := Nat.mod_mod_of_dvd (2 * c) h2dvd
    rw [← h1, hn.2.2, h2]; omega
  rw [f_b_even hpar]
  have h2lt : 2 * c < 2 ^ (m + 1) := by rw [pow_succ']; omega
  have hn1 := hn.1
  have hge1 : 1 ≤ n / 2 := by omega
  refine ⟨hge1, ?_, ?_⟩
  · have h2inv : (2 * ((b + 1) / 2)) % b = 1 % b := by
      have : 2 * ((b + 1) / 2) = b + 1 := by omega
      rw [this, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
    have hmul : (n / 2) % b = ((n / 2) * (2 * ((b + 1) / 2))) % b := by
      rw [Nat.mul_mod, h2inv, ← Nat.mul_mod, mul_one]
    have h2n : n / 2 * 2 = n := by omega
    rw [hmul, ← mul_assoc, h2n, Nat.mul_mod, hn.2.1]
    simp [Nat.mul_mod]
  · have hmod := hn.2.2
    rw [Nat.mod_eq_of_lt h2lt, pow_succ'] at hmod
    rw [nat_div_mod_two n (2 ^ m), hmod, Nat.mul_div_cancel_left _ (by omega), Nat.mod_eq_of_lt hc_lt]

/-- Periodic cylinder union density lower bound via CRT mod `b * 2^m`. -/
private lemma cyl_union_lower_density {b m : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    {S : Set ℕ} {F : ℕ → Finset ℕ} (inclZero : Bool)
    (hF_sub : ∀ x, 1 ≤ x → x < b → ∀ c ∈ F x, c < 2 ^ m)
    (hF_mem : ∀ x, 1 ≤ x → x < b → ∀ c ∈ F x, ∀ n, MemOddCyl b ⟨x, c, m⟩ n → n ∈ S)
    (hZ0 : inclZero = true → ∀ n, 1 ≤ n → b ∣ n → n ∈ S) :
    let α : ℝ :=
      ((if inclZero then (1 : ℝ) else 0) +
        ∑ x ∈ Finset.Ico 1 b, ((F x).card : ℝ) / (2 ^ m : ℝ)) / (b : ℝ)
    ∀ ε > 0, ∀ᶠ N in atTop, α - ε ≤ countFrac S N := by
  classical
  intro α ε hε
  set M := b * 2 ^ m with hM_def
  have hM_pos : 0 < M := Nat.mul_pos (by omega) (by positivity)
  have hcop : Nat.Coprime b (2 ^ m) :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).symm.pow_right m
  -- Build the set `A ⊆ Finset.range M` of good residues mod `M`:
  let A : Finset ℕ := (Finset.range M).filter fun r =>
    (inclZero = true ∧ r % b = 0) ∨ (1 ≤ r % b ∧ r % b < b ∧ r % 2 ^ m ∈ F (r % b))
  have hA_card : (A.card : ℝ) / (M : ℝ) = α := by
    -- Biject `A` with the disjoint union of `(x, c)` pairs via CRT!
    let P0 : Finset (ℕ × ℕ) :=
      if inclZero then (Finset.range (2 ^ m)).image (fun c => (0, c)) else ∅
    let Ppos : Finset (ℕ × ℕ) :=
      (Finset.Ico 1 b).biUnion fun x => (F x).image (fun c => (x, c))
    have hdisj : Disjoint P0 Ppos := by
      rw [Finset.disjoint_left]
      intro ⟨x, c⟩ h1 h2
      simp only [P0, Ppos] at h1 h2
      split_ifs at h1 with hi
      · simp only [Finset.mem_image] at h1
        rcases h1 with ⟨_, _, heq⟩
        simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_image] at h2
        rcases h2 with ⟨x', hx', _, _, heq2⟩
        cases heq; cases heq2; omega
      · exact absurd h1 (Finset.notMem_empty _)
    have hbij : A.card = (P0 ∪ Ppos).card := by
      refine Finset.card_bij (fun r _ => (r % b, r % 2 ^ m)) ?_ ?_ ?_
      · intro r hr
        simp only [A, Finset.mem_filter, Finset.mem_range] at hr
        rw [Finset.mem_union]
        rcases hr.2 with ⟨hi, h0⟩ | ⟨hx1, hxb, hcF⟩
        · left
          simp only [P0, hi, ↓reduceIte, Finset.mem_image, Finset.mem_range]
          exact ⟨r % 2 ^ m, Nat.mod_lt _ (by positivity), by rw [h0]⟩
        · right
          simp only [Ppos, Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_image]
          exact ⟨r % b, ⟨hx1, hxb⟩, r % 2 ^ m, hcF, rfl⟩
      · intro r1 hr1 r2 hr2 heq
        simp only [A, Finset.mem_filter, Finset.mem_range] at hr1 hr2
        have h1 : r1 % b = r2 % b := congr_arg Prod.fst heq
        have h2 : r1 % 2 ^ m = r2 % 2 ^ m := congr_arg Prod.snd heq
        have hd1 : (b : ℤ) ∣ (r1 : ℤ) - (r2 : ℤ) := by
          have : ((r1 : ZMod b) = (r2 : ZMod b)) := (ZMod.natCast_eq_natCast_iff' r1 r2 b).mpr h1
          have h0 : (((r1 : ℤ) - (r2 : ℤ) : ℤ) : ZMod b) = 0 := by push_cast; exact sub_eq_zero.mpr this
          exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
        have hd2 : (2 ^ m : ℤ) ∣ (r1 : ℤ) - (r2 : ℤ) := by
          have : ((r1 : ZMod (2 ^ m)) = (r2 : ZMod (2 ^ m))) :=
            (ZMod.natCast_eq_natCast_iff' r1 r2 (2 ^ m)).mpr h2
          have h0 : (((r1 : ℤ) - (r2 : ℤ) : ℤ) : ZMod (2 ^ m)) = 0 := by
            push_cast; exact sub_eq_zero.mpr this
          exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
        have hcopZ : IsCoprime (b : ℤ) (2 ^ m : ℤ) := by
          exact_mod_cast hcop.isCoprime
        have hdM : (M : ℤ) ∣ (r1 : ℤ) - (r2 : ℤ) := by
          rw [hM_def]; push_cast; exact hcopZ.mul_dvd hd1 hd2
        have hlt1 : (r1 : ℤ) < M := by exact_mod_cast hr1.1
        have hlt2 : (r2 : ℤ) < M := by exact_mod_cast hr2.1
        obtain ⟨q, hq⟩ := hdM
        have hq0 : q = 0 := by nlinarith
        have heqZ : (r1 : ℤ) = (r2 : ℤ) := by nlinarith
        exact_mod_cast heqZ
      · intro ⟨x, c⟩ hmem
        have hxc : (inclZero = true ∧ x = 0 ∧ c < 2 ^ m) ∨ (1 ≤ x ∧ x < b ∧ c ∈ F x) := by
          rw [Finset.mem_union] at hmem
          rcases hmem with h1 | h2
          · simp only [P0] at h1
            split_ifs at h1 with hi
            · simp only [Finset.mem_image, Finset.mem_range] at h1
              rcases h1 with ⟨c', hc', heq⟩
              cases heq; left; exact ⟨hi, rfl, hc'⟩
            · exact absurd h1 (Finset.notMem_empty _)
          · simp only [Ppos, Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_image] at h2
            rcases h2 with ⟨x', hx', c', hc', heq⟩
            cases heq; right; exact ⟨hx'.1, hx'.2, hc'⟩
        let k := Nat.chineseRemainder hcop x c
        let r := k.val % M
        have hrb : r % b = x % b := by
          have hd : b ∣ M := dvd_mul_right b _
          rw [Nat.mod_mod_of_dvd _ hd]; exact k.property.1
        have hr2 : r % 2 ^ m = c % 2 ^ m := by
          have hd : 2 ^ m ∣ M := dvd_mul_left _ b
          rw [Nat.mod_mod_of_dvd _ hd]; exact k.property.2
        refine ⟨r, ?_, ?_⟩
        · simp only [A, Finset.mem_filter, Finset.mem_range]
          refine ⟨Nat.mod_lt _ hM_pos, ?_⟩
          rcases hxc with ⟨hi, rfl, _⟩ | ⟨hx1, hxb, hcF⟩
          · left; exact ⟨hi, by simpa using hrb⟩
          · right
            have hclt := hF_sub x hx1 hxb c hcF
            rw [hrb, Nat.mod_eq_of_lt hxb, hr2, Nat.mod_eq_of_lt hclt]
            exact ⟨hx1, hxb, hcF⟩
        · rcases hxc with ⟨_, rfl, hclt⟩ | ⟨hx1, hxb, hcF⟩
          · ext <;> simp [hrb, hr2, Nat.mod_eq_of_lt hclt]
          · have hclt := hF_sub x hx1 hxb c hcF
            ext <;> simp [hrb, hr2, Nat.mod_eq_of_lt hxb, Nat.mod_eq_of_lt hclt]
    have hcard_union : (P0 ∪ Ppos).card =
        (if inclZero then 2 ^ m else 0) + ∑ x ∈ Finset.Ico 1 b, (F x).card := by
      rw [Finset.card_union_of_disjoint hdisj]
      congr 1
      · simp only [P0]
        split_ifs
        · rw [Finset.card_image_of_injective _ (fun a₁ a₂ h => by simpa using h), Finset.card_range]
        · simp
      · simp only [Ppos]
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.card_image_of_injective _ (fun a₁ a₂ h => by simpa using h)]
        · intro x1 _ x2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro ⟨a, c⟩ h1 h2
          simp only [Finset.mem_image] at h1 h2
          rcases h1 with ⟨_, _, e1⟩; rcases h2 with ⟨_, _, e2⟩
          cases e1; cases e2; exact hne rfl
    rw [hbij, hcard_union]
    have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
    have h2pos : (0 : ℝ) < (2 ^ m : ℝ) := by positivity
    have hsum_div : (∑ x ∈ Finset.Ico 1 b, ((F x).card : ℝ)) / (2 ^ m : ℝ) =
        ∑ x ∈ Finset.Ico 1 b, ((F x).card : ℝ) / (2 ^ m : ℝ) := Finset.sum_div ..
    have h2ne : (2 ^ m : ℝ) ≠ 0 := ne_of_gt h2pos
    dsimp only [α]
    rw [hM_def]
    push_cast
    rw [mul_comm (b : ℝ) (2 ^ m : ℝ), ← div_div, add_div, hsum_div]
    split_ifs
    · rw [div_self h2ne]
    · rw [zero_div]
  -- Every `n ≥ 1` with `n % M ∈ A` belongs to `S`!
  have hA_in_S : ∀ n, 1 ≤ n → n % M ∈ A → n ∈ S := by
    intro n hn1 hr
    simp only [A, Finset.mem_filter, Finset.mem_range] at hr
    have hnb : (n % M) % b = n % b := Nat.mod_mod_of_dvd n (dvd_mul_right b _)
    have hn2 : (n % M) % 2 ^ m = n % 2 ^ m := Nat.mod_mod_of_dvd n (dvd_mul_left _ b)
    rw [hnb, hn2] at hr
    rcases hr.2 with ⟨hi, h0⟩ | ⟨hx1, hxb, hcF⟩
    · exact hZ0 hi n hn1 (Nat.dvd_of_mod_eq_zero h0)
    · have hclt := hF_sub (n % b) hx1 hxb (n % 2 ^ m) hcF
      refine hF_mem (n % b) hx1 hxb (n % 2 ^ m) hcF n ⟨hn1, ?_, ?_⟩
      · rw [Nat.mod_eq_of_lt hxb]
      · rw [Nat.mod_eq_of_lt hclt]
  -- Periodic counting on `[1, N]`: at least `(N / M) * A.card` elements of `S` in `Finset.Icc 1 N`!
  obtain ⟨N0, hN0⟩ := exists_nat_gt ((M : ℝ) / ε)
  rw [Filter.eventually_atTop]
  refine ⟨max 1 N0, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_left hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hMposR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
  have hcard_ge : (N / M) * A.card ≤ ((Finset.Icc 1 N).filter (· ∈ S)).card := by
    let Q : Finset (ℕ × ℕ) := Finset.range (N / M) ×ˢ A
    have hQ_card : Q.card = (N / M) * A.card := by simp [Q]
    rw [← hQ_card]
    refine Finset.card_le_card_of_injOn (fun p => if p.2 = 0 then (p.1 + 1) * M else p.1 * M + p.2) ?_ ?_
    · intro ⟨q, r⟩ hqr
      simp only [Q, Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hqr
      have hrM : r < M := (Finset.mem_range.mp (Finset.mem_filter.mp hqr.2).1)
      have hqM : (q + 1) * M ≤ N := by
        have h1 : q + 1 ≤ N / M := hqr.1
        calc (q + 1) * M ≤ (N / M) * M := Nat.mul_le_mul_right M h1
          _ ≤ N := Nat.div_mul_le_self N M
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      split_ifs with hr0
      · subst hr0
        refine ⟨⟨by nlinarith, hqM⟩, hA_in_S ((q + 1) * M) (by nlinarith) ?_⟩
        simpa [Nat.mul_mod_left] using hqr.2
      · refine ⟨⟨by omega, by nlinarith⟩, hA_in_S (q * M + r) (by omega) ?_⟩
        rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hrM]
        exact hqr.2
    · intro ⟨q1, r1⟩ h1 ⟨q2, r2⟩ h2 heq
      simp only [Q, Finset.mem_coe, Finset.mem_product, Finset.mem_range] at h1 h2
      have hr1 : r1 < M := (Finset.mem_range.mp (Finset.mem_filter.mp h1.2).1)
      have hr2 : r2 < M := (Finset.mem_range.mp (Finset.mem_filter.mp h2.2).1)
      dsimp only at heq
      split_ifs at heq with h10 h20 h20
      · subst h10; subst h20
        have := Nat.eq_of_mul_eq_mul_right hM_pos heq
        ext <;> omega
      · subst h10
        have hmod := congr_arg (· % M) heq
        simp only [Nat.mul_mod_left, Nat.add_mod, zero_add, Nat.mod_eq_of_lt hr2] at hmod
        exact absurd hmod.symm h20
      · subst h20
        have hmod := congr_arg (· % M) heq
        simp only [Nat.mul_mod_left, Nat.add_mod, zero_add, Nat.mod_eq_of_lt hr1] at hmod
        exact absurd hmod h10
      · have hmod := congr_arg (· % M) heq
        simp only [Nat.add_mod, Nat.mul_mod_left, zero_add,
          Nat.mod_eq_of_lt hr1, Nat.mod_eq_of_lt hr2] at hmod
        subst hmod
        have hqeq : q1 * M = q2 * M := by omega
        have := Nat.eq_of_mul_eq_mul_right hM_pos hqeq
        ext <;> omega
  have hA_le_M : (A.card : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  have hdiv_gt : (N : ℝ) - (M : ℝ) < ((N / M : ℕ) : ℝ) * (M : ℝ) := by
    have : N < (N / M) * M + M := by
      have h := Nat.div_add_mod N M
      have hm := Nat.mod_lt N hM_pos
      nlinarith
    have hR : (N : ℝ) < ((N / M : ℕ) : ℝ) * (M : ℝ) + (M : ℝ) := by exact_mod_cast this
    linarith
  have hMN : (M : ℝ) / (N : ℝ) < ε := by
    rw [div_lt_iff₀ hNpos]
    have hN0_le : (N0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_of_max_le_right hN
    have : (M : ℝ) / ε < (N : ℝ) := lt_of_lt_of_le hN0 hN0_le
    exact (div_lt_iff₀ hε).mp this |> fun h => by linarith
  unfold countFrac
  rw [← hA_card]
  have h1 : ((N / M : ℕ) : ℝ) * (A.card : ℝ) ≤
      (((Finset.Icc 1 N).filter (· ∈ S)).card : ℝ) := by exact_mod_cast hcard_ge
  have h2 : ((N : ℝ) - (M : ℝ)) / (M : ℝ) * (A.card : ℝ) ≤ ((N / M : ℕ) : ℝ) * (A.card : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [div_le_iff₀ hMposR]; linarith
  have h3 : (A.card : ℝ) / (M : ℝ) - (M : ℝ) / (N : ℝ) ≤
      ((N : ℝ) - (M : ℝ)) / (M : ℝ) * (A.card : ℝ) / (N : ℝ) := by
    have h4 : ((N : ℝ) - (M : ℝ)) / (M : ℝ) * (A.card : ℝ) / (N : ℝ) =
        (A.card : ℝ) / (M : ℝ) - (A.card : ℝ) / (N : ℝ) := by field_simp
    rw [h4]
    have hAN : (A.card : ℝ) / (N : ℝ) ≤ (M : ℝ) / (N : ℝ) :=
      div_le_div_of_nonneg_right hA_le_M (le_of_lt hNpos)
    linarith
  have h5 : ((N : ℝ) - (M : ℝ)) / (M : ℝ) * (A.card : ℝ) / (N : ℝ) ≤
      (((Finset.Icc 1 N).filter (· ∈ S)).card : ℝ) / (N : ℝ) :=
    div_le_div_of_nonneg_right (h2.trans h1) (le_of_lt hNpos)
  linarith

/-! ## Section 4.5: Universal Section 6.2 Canonical Markov Absorption (All Odd `b ≥ 3`) -/

private lemma isCertifiedEscape_all_valid {b x : ℕ} (hb3 : 3 ≤ b)
    (hesc : IsCertifiedEscape b x) :
    ∀ k : ℕ, 1 ≤ ((cylStep b)^[k] ⟨x, 1, 1⟩).x ∧
             ((cylStep b)^[k] ⟨x, 1, 1⟩).x < b ∧
             1 ≤ ((cylStep b)^[k] ⟨x, 1, 1⟩).j := by
  obtain ⟨s, p, C0, hp1, hval_s, hsub_s, hval_p, hsub_p⟩ := hesc
  have hC0_lt : C0.x < b := by simpa using (hval_p 0 (by omega)).2.1
  have hq : ∀ q : ℕ, CylSubset b ((cylStep b)^[s + q * p] ⟨x, 1, 1⟩) C0 := by
    intro q
    induction q with
    | zero => simpa using hsub_s
    | succ q ih =>
      rw [show s + (q + 1) * p = p + (s + q * p) by ring, Function.iterate_add_apply]
      have hClt : ((cylStep b)^[s + q * p] ⟨x, 1, 1⟩).x < b := by
        cases hsq : s + q * p with
        | zero =>
          have h0 := (hval_s 0 (by omega)).2.1
          simpa using h0
        | succ n' => rw [Function.iterate_succ_apply']; exact cylStep_x_lt hb3 _
      have hmono := cylSubset_cylStep_iter hb3 p ((cylStep b)^[s + q * p] ⟨x, 1, 1⟩) C0
        ih hClt hC0_lt (fun i hi => hval_p i (by omega)) p (le_refl p)
      exact cylSubset_trans hmono.1 hsub_p
  intro k
  by_cases hle : k ≤ s
  · exact hval_s k hle
  · set q := (k - s) / p
    set r := (k - s) % p
    have hr : r < p := Nat.mod_lt _ (by omega)
    have hdm : p * q + r = k - s := Nat.div_add_mod (k - s) p
    have hk_eq : k = r + (s + q * p) := by
      have : s + (k - s) = k := by omega
      nlinarith
    rw [hk_eq, Function.iterate_add_apply]
    have hClt : ((cylStep b)^[s + q * p] ⟨x, 1, 1⟩).x < b := by
      cases hsq : s + q * p with
      | zero =>
        have h0 := (hval_s 0 (by omega)).2.1
        simpa using h0
      | succ n' => rw [Function.iterate_succ_apply']; exact cylStep_x_lt hb3 _
    exact (cylSubset_cylStep_iter hb3 p ((cylStep b)^[s + q * p] ⟨x, 1, 1⟩) C0
      (hq q) hClt hC0_lt (fun i hi => hval_p i (by omega)) r (by omega)).2 hr

private lemma isCertifiedEscape_of_step {b x y s1 : ℕ} (hb3 : 3 ≤ b)
    (hyb : y < b)
    (hval1 : ∀ i ≤ s1, 1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).x ∧
                       ((cylStep b)^[i] ⟨x, 1, 1⟩).x < b ∧
                       1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).j)
    (hsub1 : CylSubset b ((cylStep b)^[s1] ⟨x, 1, 1⟩) ⟨y, 1, 1⟩)
    (hy_esc : IsCertifiedEscape b y) :
    IsCertifiedEscape b x := by
  obtain ⟨s2, p, C0, hp1, hval2, hsub2, hval_p, hsub_p⟩ := hy_esc
  have hmono := cylSubset_cylStep_iter hb3 s2 ((cylStep b)^[s1] ⟨x, 1, 1⟩) ⟨y, 1, 1⟩
    hsub1 (hval1 s1 (le_refl s1)).2.1 hyb (fun i hi => hval2 i (by omega))
  refine ⟨s1 + s2, p, C0, hp1, ?_, ?_, hval_p, hsub_p⟩
  · intro i hi
    by_cases hle : i ≤ s1
    · exact hval1 i hle
    · by_cases hlt : i < s1 + s2
      · rw [show i = (i - s1) + s1 by omega, Function.iterate_add_apply]
        exact (hmono (i - s1) (by omega)).2 (by omega)
      · have hi_eq : i = s2 + s1 := by omega
        rw [hi_eq, Function.iterate_add_apply]
        have hsub_end := (hmono s2 (le_refl s2)).1
        have hv_end := hval2 s2 (le_refl s2)
        have hClt_end : ((cylStep b)^[s2] ((cylStep b)^[s1] ⟨x, 1, 1⟩)).x < b := by
          cases s2 with
          | zero => simpa using (hval1 s1 (le_refl s1)).2.1
          | succ s2' => rw [Function.iterate_succ_apply']; exact cylStep_x_lt hb3 _
        have hx_eq : ((cylStep b)^[s2] ((cylStep b)^[s1] ⟨x, 1, 1⟩)).x =
            ((cylStep b)^[s2] ⟨y, 1, 1⟩).x := by
          have := hsub_end.1
          rw [Nat.mod_eq_of_lt hClt_end, Nat.mod_eq_of_lt hv_end.2.1] at this
          exact this
        exact ⟨hx_eq ▸ hv_end.1, hClt_end, le_trans hv_end.2.2 hsub_end.2.1⟩
  · rw [show s1 + s2 = s2 + s1 by omega, Function.iterate_add_apply]
    exact cylSubset_trans (hmono s2 (le_refl s2)).1 hsub2

private lemma isTrapStretch_not_escape {b x : ℕ} (hb3 : 3 ≤ b)
    (ht : IsTrapStretch b x) (he : IsCertifiedEscape b x) : False := by
  obtain ⟨s, _, _, hx0⟩ := ht
  have hv := (isCertifiedEscape_all_valid hb3 he s).1
  omega

private lemma isZeroStretch_not_escape {b x y : ℕ} (hb3 : 3 ≤ b)
    (hz : IsZeroStretch b x y) (he : IsCertifiedEscape b x) : False := by
  obtain ⟨_, _, s, _, _, hys⟩ := hz
  have hv := (isCertifiedEscape_all_valid hb3 he s).2.2
  rw [hys] at hv
  dsimp only at hv; omega

private lemma isTrapStretch_not_zero {b x y : ℕ}
    (ht : IsTrapStretch b x) (hz : IsZeroStretch b x y) : False := by
  obtain ⟨s1, _, hval1, hx0⟩ := ht
  obtain ⟨hy1, _, s2, _, hval2, hys⟩ := hz
  rcases lt_trichotomy s1 s2 with hlt | heq | hgt
  · have := (hval2 s1 hlt).1; omega
  · subst heq; rw [hys] at hx0; dsimp only at hx0; omega
  · have := (hval1 s2 hgt).2.2; rw [hys] at this; dsimp only at this; omega

private lemma isZeroStretch_unique {b x y1 y2 : ℕ}
    (h1 : IsZeroStretch b x y1) (h2 : IsZeroStretch b x y2) : y1 = y2 := by
  obtain ⟨_, _, s1, _, hval1, hys1⟩ := h1
  obtain ⟨_, _, s2, _, hval2, hys2⟩ := h2
  rcases lt_trichotomy s1 s2 with hlt | heq | hgt
  · have := (hval2 s1 hlt).2.2; rw [hys1] at this; dsimp only at this; omega
  · subst heq; rw [hys1] at hys2; cases hys2; rfl
  · have := (hval1 s2 hgt).2.2; rw [hys2] at this; dsimp only at this; omega

theorem oddStretchOutcome_eq_trap_iff {b x : ℕ} :
    oddStretchOutcome b x = .trap ↔ IsTrapStretch b x := by
  unfold oddStretchOutcome
  split_ifs with ht he hz <;> simp_all

theorem oddStretchOutcome_eq_escape_iff {b x : ℕ} (hb3 : 3 ≤ b) :
    oddStretchOutcome b x = .escape ↔ IsCertifiedEscape b x := by
  unfold oddStretchOutcome
  split_ifs with ht he hz
  · exact ⟨(fun h => by cases h), fun he' => absurd he' (isTrapStretch_not_escape hb3 ht)⟩
  · exact ⟨fun _ => he, fun _ => rfl⟩
  · exact ⟨(fun h => by cases h), fun he' => absurd he' he⟩
  · exact ⟨(fun h => by cases h), fun he' => absurd he' he⟩

theorem oddStretchOutcome_eq_toState_iff {b x y : ℕ} (hb3 : 3 ≤ b) :
    oddStretchOutcome b x = .toState y ↔ IsZeroStretch b x y := by
  unfold oddStretchOutcome
  split_ifs with ht he hz
  · exact ⟨(fun h => by cases h), fun hz' => False.elim (isTrapStretch_not_zero ht hz')⟩
  · exact ⟨(fun h => by cases h), fun hz' => False.elim (isZeroStretch_not_escape hb3 hz' he)⟩
  · constructor
    · intro h; cases h; exact Classical.choose_spec hz
    · intro hz'; congr 1; exact isZeroStretch_unique (Classical.choose_spec hz) hz'
  · exact ⟨(fun h => by cases h), fun hz' => False.elim (hz ⟨y, hz'⟩)⟩

theorem oddStretchOutcome_eq_unresolved_iff {b x : ℕ} :
    oddStretchOutcome b x = .unresolved ↔
      ¬ IsTrapStretch b x ∧ ¬ IsCertifiedEscape b x ∧ ¬ ∃ y, IsZeroStretch b x y := by
  unfold oddStretchOutcome
  split_ifs with ht he hz <;> simp_all

/-- Soundness of a trap stretch: every `n ∈ ⟨x, 1, 1⟩` reaches a multiple of `b` (`ZSet b`). -/
theorem isTrapStretch_zSet {b x n : ℕ} (hb_odd : b % 2 = 1)
    (ht : IsTrapStretch b x) (hn : MemOddCyl b ⟨x, 1, 1⟩ n) : n ∈ ZSet b := by
  obtain ⟨s, _, hval, hx0⟩ := ht
  have hms := cylStep_iter_mem hb_odd s ⟨x, 1, 1⟩ hval n hn
  have hmod := hms.2.1
  rw [hx0] at hmod
  exact ⟨hn.1, s, Nat.dvd_of_mod_eq_zero (by simpa using hmod)⟩

/-- Soundness of a certified escape stretch: every `n ∈ ⟨x, 1, 1⟩` diverges (`DivSet b`). -/
theorem isCertifiedEscape_divSet {b x n : ℕ} (hb_odd : b % 2 = 1)
    (hesc : IsCertifiedEscape b x) (hn : MemOddCyl b ⟨x, 1, 1⟩ n) : n ∈ DivSet b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, p, C0, hp1, hval_s, hsub_s, hval_p, hsub_p⟩ := hesc
  set m0 := (f_b b)^[s] n
  have hm0 : MemOddCyl b C0 m0 :=
    memOddCyl_of_subset hsub_s (cylStep_iter_mem hb_odd s ⟨x, 1, 1⟩ (fun i hi => hval_s i (by omega)) n hn)
  have hstep_C0 : ∀ m, MemOddCyl b C0 m →
      ∀ r ≤ p, MemOddCyl b ((cylStep b)^[r] C0) ((f_b b)^[r] m) := fun m hm r hr =>
    cylStep_iter_mem hb_odd r C0 (fun i hi => hval_p i (by omega)) m hm
  have hclosed_C0 : ∀ m, MemOddCyl b C0 m → MemOddCyl b C0 ((f_b b)^[p] m) := fun m hm =>
    memOddCyl_of_subset hsub_p (hstep_C0 m hm p (le_refl p))
  have haff := stretchAffine_spec hb_odd p C0 (fun i hi => hval_p i (by omega))
  rcases hres : stretchAffine b C0 p with ⟨A, B, h⟩
  rw [hres] at haff
  obtain ⟨haff_eq, haff_bits, hA1, hB_cond⟩ := haff
  have hh_le_v2 : h ≤ padicValNat 2 A := by have := hsub_p.2.1; omega
  have h2h_le_A : 2 ^ h ≤ A :=
    Nat.le_of_dvd (by omega) (dvd_trans (pow_dvd_pow 2 hh_le_v2) pow_padicValNat_dvd)
  have hh_lt_p : h < p := by
    by_contra hge
    have hA_one : ∀ (t : ℕ) (C : OddCyl), (stretchAffine b C t).2.2 ≤ t ∧
        ((stretchAffine b C t).2.2 = t → (stretchAffine b C t).1 = 1) := by
      intro t
      induction t with
      | zero => intro C; simp [stretchAffine]
      | succ t ih =>
        intro C
        have hprev := ih (cylStep b C)
        rcases hsp : stretchAffine b (cylStep b C) t with ⟨A', B', h'⟩
        rw [hsp] at hprev
        have hst : stretchAffine b C (t + 1) =
            if C.c % 2 = 0 then (A', 2 * B', h' + 1) else (A' * C.x, A' + B', h') := by
          simp [stretchAffine, hsp]
        rw [hst]
        split_ifs
        · exact ⟨by dsimp at hprev ⊢; omega, fun heq => hprev.2 (by dsimp at heq ⊢; omega)⟩
        · exact ⟨by dsimp at hprev ⊢; omega, fun heq => by dsimp at hprev heq ⊢; omega⟩
    have hspec := hA_one p C0
    rw [hres] at hspec; dsimp only at hspec
    have hAeq1 : A = 1 := hspec.2 (by omega)
    rw [hAeq1, padicValNat.eq_zero_of_not_dvd (by omega)] at hh_le_v2
    omega
  have hB1 : 1 ≤ B := hB_cond hh_lt_p
  have hgrow_C0 : ∀ m, MemOddCyl b C0 m → m < (f_b b)^[p] m := by
    intro m hm
    have hmul : 2 ^ h * m < 2 ^ h * (f_b b)^[p] m := by
      rw [haff_eq m hm]
      have := Nat.mul_le_mul_right m h2h_le_A
      omega
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hiter_C0 : ∀ q : ℕ, MemOddCyl b C0 ((f_b b)^[q * p] m0) ∧ q ≤ (f_b b)^[q * p] m0 := by
    intro q
    induction q with
    | zero => exact ⟨by simpa using hm0, Nat.zero_le _⟩
    | succ q ih =>
      rw [show (q + 1) * p = p + q * p by ring, Function.iterate_add_apply]
      exact ⟨hclosed_C0 _ ih.1, by have := hgrow_C0 _ ih.1; omega⟩
  have hback : ∀ m, MemOddCyl b C0 m → ∀ r ≤ p, m ≤ 2 ^ r * (f_b b)^[r] m := by
    intro m hm r hr
    induction r with
    | zero => simp
    | succ r ih =>
      have hv := hval_p r (by omega)
      have hu := hstep_C0 m hm r (by omega)
      set u := (f_b b)^[r] m
      have hu_mod : u % b = ((cylStep b)^[r] C0).x := by
        rw [hu.2.1, Nat.mod_eq_of_lt hv.2.1]
      have hu_le : u ≤ 2 * f_b b u := by
        by_cases hev : u % 2 = 0
        · rw [f_b_even hev]; omega
        · rw [f_b_odd (by omega), hu_mod]; nlinarith [hv.1]
      have hih := ih (by omega)
      rw [Function.iterate_succ_apply', pow_succ']
      calc m ≤ 2 ^ r * u := hih
        _ ≤ 2 ^ r * (2 * f_b b u) := Nat.mul_le_mul_left (2 ^ r) hu_le
        _ = 2 * 2 ^ r * f_b b u := by ring
  refine divSet_of_iter (s := s) hn.1 ⟨hm0.1, ?_⟩
  rw [Filter.tendsto_atTop_atTop]
  intro M
  refine ⟨(M * 2 ^ p) * p, fun i hi => ?_⟩
  set q := i / p
  set r := i % p
  have hr : r < p := Nat.mod_lt _ (by omega)
  have hdm : p * q + r = i := Nat.div_add_mod i p
  have hi_eq : i = r + q * p := by linarith [mul_comm p q]
  have hq_ge : M * 2 ^ p ≤ q := (Nat.le_div_iff_mul_le (by omega)).mpr hi
  have h2r_le : 2 ^ r ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
  have hq_spec := hiter_C0 q
  have hbk := hback ((f_b b)^[q * p] m0) hq_spec.1 r (by omega)
  have hiter_eq : (f_b b)^[r] ((f_b b)^[q * p] m0) = (f_b b)^[i] m0 := by
    rw [← Function.iterate_add_apply, ← hi_eq]
  rw [hiter_eq] at hbk
  have hmul : 2 ^ p * M ≤ 2 ^ p * (f_b b)^[i] m0 := by
    calc 2 ^ p * M = M * 2 ^ p := mul_comm _ _
      _ ≤ q := hq_ge
      _ ≤ (f_b b)^[q * p] m0 := hq_spec.2
      _ ≤ 2 ^ r * (f_b b)^[i] m0 := hbk
      _ ≤ 2 ^ p * (f_b b)^[i] m0 := Nat.mul_le_mul_right _ h2r_le
  exact Nat.le_of_mul_le_mul_left hmul (by positivity)

private lemma oddProb_bounds {b : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1) :
    ∀ m x, 1 ≤ x → x < b →
      0 ≤ oddTrapProb b m x ∧ 0 ≤ oddRunProb b m x ∧
      oddTrapProb b m x + oddRunProb b m x ≤ 1 := by
  intro m
  induction m with
  | zero => intro x _ _; simp [oddTrapProb, oddRunProb]
  | succ m ih =>
    intro x hx1 hxb
    have hhalf := half_pos_lt hb3 hb_odd hx1 hxb
    have ihh := ih _ hhalf.1 hhalf.2
    simp only [oddTrapProb, oddRunProb]
    cases ho : oddStretchOutcome b x with
    | trap => dsimp only; refine ⟨by linarith, by linarith, by linarith⟩
    | escape => dsimp only; refine ⟨by linarith, by linarith, by linarith⟩
    | unresolved => dsimp only; refine ⟨by linarith, by linarith, by linarith⟩
    | toState y =>
      have hy := (oddStretchOutcome_eq_toState_iff hb3).mp ho
      have ihy := ih y hy.1 hy.2.1
      dsimp only; refine ⟨by linarith, by linarith, by linarith⟩

private lemma oddProb_mono {b : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1) :
    ∀ m x, 1 ≤ x → x < b →
      oddTrapProb b m x ≤ oddTrapProb b (m + 1) x ∧
      oddRunProb b m x ≤ oddRunProb b (m + 1) x := by
  intro m
  induction m with
  | zero =>
    intro x hx1 hxb
    have hb := oddProb_bounds hb3 hb_odd 1 x hx1 hxb
    exact ⟨by simpa [oddTrapProb] using hb.1, by simpa [oddRunProb] using hb.2.1⟩
  | succ m ih =>
    intro x hx1 hxb
    have hhalf := half_pos_lt hb3 hb_odd hx1 hxb
    have ihh := ih _ hhalf.1 hhalf.2
    have ht1 : oddTrapProb b (m + 1) x =
        (1 / 2 : ℝ) * oddTrapProb b m ((x * ((b + 1) / 2)) % b) +
        (1 / 2 : ℝ) * match oddStretchOutcome b x with
          | .trap => 1 | .escape => 0 | .toState y => oddTrapProb b m y | .unresolved => 0 := rfl
    have ht2 : oddTrapProb b (m + 2) x =
        (1 / 2 : ℝ) * oddTrapProb b (m + 1) ((x * ((b + 1) / 2)) % b) +
        (1 / 2 : ℝ) * match oddStretchOutcome b x with
          | .trap => 1 | .escape => 0 | .toState y => oddTrapProb b (m + 1) y | .unresolved => 0 := rfl
    have hr1 : oddRunProb b (m + 1) x =
        (1 / 2 : ℝ) * oddRunProb b m ((x * ((b + 1) / 2)) % b) +
        (1 / 2 : ℝ) * match oddStretchOutcome b x with
          | .trap => 0 | .escape => 1 | .toState y => oddRunProb b m y | .unresolved => 0 := rfl
    have hr2 : oddRunProb b (m + 2) x =
        (1 / 2 : ℝ) * oddRunProb b (m + 1) ((x * ((b + 1) / 2)) % b) +
        (1 / 2 : ℝ) * match oddStretchOutcome b x with
          | .trap => 0 | .escape => 1 | .toState y => oddRunProb b (m + 1) y | .unresolved => 0 := rfl
    rw [ht1, ht2, hr1, hr2]
    cases ho : oddStretchOutcome b x with
    | trap => dsimp only; exact ⟨by linarith, by linarith⟩
    | escape => dsimp only; exact ⟨by linarith, by linarith⟩
    | unresolved => dsimp only; exact ⟨by linarith, by linarith⟩
    | toState y =>
      have hy := (oddStretchOutcome_eq_toState_iff hb3).mp ho
      have ihy := ih y hy.1 hy.2.1
      dsimp only; exact ⟨by linarith, by linarith⟩

private lemma oddTrapProb_tendsto {b x : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (hx1 : 1 ≤ x) (hxb : x < b) :
    Tendsto (fun m => oddTrapProb b m x) atTop (𝓝 (oddTrapStateMass b x)) := by
  refine tendsto_atTop_ciSup (monotone_nat_of_le_succ fun m => (oddProb_mono hb3 hb_odd m x hx1 hxb).1)
    ⟨1, ?_⟩
  rintro _ ⟨m, rfl⟩
  have hb := oddProb_bounds hb3 hb_odd m x hx1 hxb
  linarith

private lemma oddRunProb_tendsto {b x : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (hx1 : 1 ≤ x) (hxb : x < b) :
    Tendsto (fun m => oddRunProb b m x) atTop (𝓝 (oddRunStateMass b x)) := by
  refine tendsto_atTop_ciSup (monotone_nat_of_le_succ fun m => (oddProb_mono hb3 hb_odd m x hx1 hxb).2)
    ⟨1, ?_⟩
  rintro _ ⟨m, rfl⟩
  have hb := oddProb_bounds hb3 hb_odd m x hx1 hxb
  linarith

private lemma oddStateMass_bounds {b x : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (hx1 : 1 ≤ x) (hxb : x < b) :
    0 ≤ oddTrapStateMass b x ∧ 0 ≤ oddRunStateMass b x ∧
    oddTrapStateMass b x + oddRunStateMass b x ≤ 1 := by
  have ht := oddTrapProb_tendsto hb3 hb_odd hx1 hxb
  have hr := oddRunProb_tendsto hb3 hb_odd hx1 hxb
  refine ⟨ge_of_tendsto ht (Eventually.of_forall fun m => (oddProb_bounds hb3 hb_odd m x hx1 hxb).1),
          ge_of_tendsto hr (Eventually.of_forall fun m => (oddProb_bounds hb3 hb_odd m x hx1 hxb).2.1),
          le_of_tendsto (ht.add hr) (Eventually.of_forall fun m => (oddProb_bounds hb3 hb_odd m x hx1 hxb).2.2)⟩

/-- Fixed-point linear absorption equation for `oddTrapStateMass b x` (valid for ALL odd `b ≥ 3`). -/
theorem oddTrapStateMass_eq {b x : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (hx1 : 1 ≤ x) (hxb : x < b) :
    oddTrapStateMass b x =
      (1 / 2 : ℝ) * oddTrapStateMass b ((x * ((b + 1) / 2)) % b) +
      (1 / 2 : ℝ) * match oddStretchOutcome b x with
        | .trap => 1
        | .escape => 0
        | .toState y => oddTrapStateMass b y
        | .unresolved => 0 := by
  have hhalf := half_pos_lt hb3 hb_odd hx1 hxb
  have hL : Tendsto (fun m => oddTrapProb b (m + 1) x) atTop (𝓝 (oddTrapStateMass b x)) :=
    (oddTrapProb_tendsto hb3 hb_odd hx1 hxb).comp (tendsto_add_atTop_nat 1)
  have hH := (oddTrapProb_tendsto hb3 hb_odd hhalf.1 hhalf.2).const_mul (1 / 2 : ℝ)
  have hR : Tendsto (fun m => oddTrapProb b (m + 1) x) atTop
      (𝓝 ((1 / 2 : ℝ) * oddTrapStateMass b ((x * ((b + 1) / 2)) % b) +
        (1 / 2 : ℝ) * match oddStretchOutcome b x with
          | .trap => 1 | .escape => 0 | .toState y => oddTrapStateMass b y | .unresolved => 0)) := by
    simp only [oddTrapProb]
    cases ho : oddStretchOutcome b x with
    | trap => exact hH.add tendsto_const_nhds
    | escape => exact hH.add tendsto_const_nhds
    | unresolved => exact hH.add tendsto_const_nhds
    | toState y =>
      have hy := (oddStretchOutcome_eq_toState_iff hb3).mp ho
      exact hH.add ((oddTrapProb_tendsto hb3 hb_odd hy.1 hy.2.1).const_mul (1 / 2 : ℝ))
  exact tendsto_nhds_unique hL hR

/-- Fixed-point linear absorption equation for `oddRunStateMass b x` (valid for ALL odd `b ≥ 3`). -/
theorem oddRunStateMass_eq {b x : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (hx1 : 1 ≤ x) (hxb : x < b) :
    oddRunStateMass b x =
      (1 / 2 : ℝ) * oddRunStateMass b ((x * ((b + 1) / 2)) % b) +
      (1 / 2 : ℝ) * match oddStretchOutcome b x with
        | .trap => 0
        | .escape => 1
        | .toState y => oddRunStateMass b y
        | .unresolved => 0 := by
  have hhalf := half_pos_lt hb3 hb_odd hx1 hxb
  have hL : Tendsto (fun m => oddRunProb b (m + 1) x) atTop (𝓝 (oddRunStateMass b x)) :=
    (oddRunProb_tendsto hb3 hb_odd hx1 hxb).comp (tendsto_add_atTop_nat 1)
  have hH := (oddRunProb_tendsto hb3 hb_odd hhalf.1 hhalf.2).const_mul (1 / 2 : ℝ)
  have hR : Tendsto (fun m => oddRunProb b (m + 1) x) atTop
      (𝓝 ((1 / 2 : ℝ) * oddRunStateMass b ((x * ((b + 1) / 2)) % b) +
        (1 / 2 : ℝ) * match oddStretchOutcome b x with
          | .trap => 0 | .escape => 1 | .toState y => oddRunStateMass b y | .unresolved => 0)) := by
    simp only [oddRunProb]
    cases ho : oddStretchOutcome b x with
    | trap => exact hH.add tendsto_const_nhds
    | escape => exact hH.add tendsto_const_nhds
    | unresolved => exact hH.add tendsto_const_nhds
    | toState y =>
      have hy := (oddStretchOutcome_eq_toState_iff hb3).mp ho
      exact hH.add ((oddRunProb_tendsto hb3 hb_odd hy.1 hy.2.1).const_mul (1 / 2 : ℝ))
  exact tendsto_nhds_unique hL hR

noncomputable def canonOutS (b x : ℕ) : ℕ :=
  open Classical in
  match oddStretchOutcome b x with
  | .toState y =>
    if h : IsZeroStretch b x y then Classical.choose h.2.2 else 0
  | _ => 0

noncomputable def canonPull (b x e cStar : ℕ) : ℕ :=
  open Classical in
  if hb : 3 ≤ b ∧ b % 2 = 1 then
    match oddStretchOutcome b x with
    | .toState y =>
      if h : IsZeroStretch b x y then
        Classical.choose (stretch_pullback hb.2 (Classical.choose h.2.2) ⟨x, 1, 1⟩ y
          (Classical.choose_spec h.2.2).2.1 (Classical.choose_spec h.2.2).2.2 e cStar)
      else 2 * cStar + 1
    | _ => 2 * cStar + 1
  else 2 * cStar + 1

private lemma canonPull_spec {b x y : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (ho : oddStretchOutcome b x = .toState y) (e cStar : ℕ) :
    canonPull b x e cStar < 2 ^ (1 + e) ∧
    canonPull b x e cStar % 2 = 1 ∧
    ∀ n, (MemOddCyl b ⟨x, 1, 1⟩ n ∧ MemOddCyl b ⟨y, cStar, e⟩ ((f_b b)^[canonOutS b x] n)) ↔
      MemOddCyl b ⟨x, canonPull b x e cStar, 1 + e⟩ n := by
  have hz : IsZeroStretch b x y := (oddStretchOutcome_eq_toState_iff hb3).mp ho
  have hb : 3 ≤ b ∧ b % 2 = 1 := ⟨hb3, hb_odd⟩
  dsimp only [canonPull, canonOutS]
  simp only [dite_eq_left_of_eq_true (eq_true hb), ho, dite_eq_left_of_eq_true (eq_true hz)]
  have hs := Classical.choose_spec (stretch_pullback hb_odd (Classical.choose hz.2.2) ⟨x, 1, 1⟩ y
    (Classical.choose_spec hz.2.2).2.1 (Classical.choose_spec hz.2.2).2.2 e cStar)
  exact ⟨hs.1, by simpa using hs.2.1, hs.2.2⟩

private lemma canonPull_inj {b x y : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (ho : oddStretchOutcome b x = .toState y) (e c1 c2 : ℕ)
    (hc1 : c1 < 2 ^ e) (hc2 : c2 < 2 ^ e) (heq : canonPull b x e c1 = canonPull b x e c2) :
    c1 = c2 := by
  obtain ⟨n, hn⟩ := exists_memOddCyl (b := b) (x := x) (c := canonPull b x e c1) (j := 1 + e) hb3 hb_odd
  have h1 := ((canonPull_spec hb3 hb_odd ho e c1).2.2 n).mpr hn
  have h2 := ((canonPull_spec hb3 hb_odd ho e c2).2.2 n).mpr (heq ▸ hn)
  have hmod : c1 % 2 ^ e = c2 % 2 ^ e := h1.2.2.2.symm.trans h2.2.2.2
  rwa [Nat.mod_eq_of_lt hc1, Nat.mod_eq_of_lt hc2] at hmod

/-- Canonical depth-`m` trap and escape cylinder residue sets (completely certificate-free). -/
noncomputable def canonTrapCylSet (b : ℕ) : ℕ → ℕ → Finset ℕ
  | 0, _ => ∅
  | m + 1, x =>
    open Classical in
    let half := (x * ((b + 1) / 2)) % b
    ((canonTrapCylSet b m half).image (fun c => 2 * c)) ∪
    match oddStretchOutcome b x with
    | .trap => (Finset.range (2 ^ m)).image (fun c => 2 * c + 1)
    | .toState y => (canonTrapCylSet b m y).image (fun c => canonPull b x m c)
    | _ => ∅

noncomputable def canonRunCylSet (b : ℕ) : ℕ → ℕ → Finset ℕ
  | 0, _ => ∅
  | m + 1, x =>
    open Classical in
    let half := (x * ((b + 1) / 2)) % b
    ((canonRunCylSet b m half).image (fun c => 2 * c)) ∪
    match oddStretchOutcome b x with
    | .escape => (Finset.range (2 ^ m)).image (fun c => 2 * c + 1)
    | .toState y => (canonRunCylSet b m y).image (fun c => canonPull b x m c)
    | _ => ∅

private lemma canon_cyl_props {b : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1) :
    ∀ m x, 1 ≤ x → x < b →
      (∀ c ∈ canonTrapCylSet b m x, c < 2 ^ m) ∧
      (∀ c ∈ canonRunCylSet b m x, c < 2 ^ m) ∧
      (∀ c ∈ canonTrapCylSet b m x, ∀ n, MemOddCyl b ⟨x, c, m⟩ n → n ∈ ZSet b) ∧
      (∀ c ∈ canonRunCylSet b m x, ∀ n, MemOddCyl b ⟨x, c, m⟩ n → n ∈ DivSet b) ∧
      ((canonTrapCylSet b m x).card : ℝ) / (2 ^ m : ℝ) = oddTrapProb b m x ∧
      ((canonRunCylSet b m x).card : ℝ) / (2 ^ m : ℝ) = oddRunProb b m x := by
  classical
  let half (x : ℕ) : ℕ := (x * ((b + 1) / 2)) % b
  intro m
  induction m with
  | zero => intro x _ _; simp [canonTrapCylSet, canonRunCylSet, oddTrapProb, oddRunProb]
  | succ m ih =>
    intro x hx1 hxb
    have hhalf := half_pos_lt hb3 hb_odd hx1 hxb
    have ihh := ih (half x) hhalf.1 hhalf.2
    have hpow_eq : 2 ^ (1 + m) = 2 ^ (m + 1) := by rw [add_comm]
    have h2pos : (0 : ℝ) < (2 ^ m : ℝ) := by positivity
    have hT_sub : ∀ c ∈ canonTrapCylSet b (m + 1) x, c < 2 ^ (m + 1) := by
      intro c hc
      simp only [canonTrapCylSet, Finset.mem_union] at hc
      rcases hc with hL | hR
      · simp only [Finset.mem_image] at hL; rcases hL with ⟨c', hc', rfl⟩
        have := ihh.1 c' hc'; rw [pow_succ']; omega
      · cases ho : oddStretchOutcome b x with
        | trap =>
          rw [ho] at hR; simp only [Finset.mem_image, Finset.mem_range] at hR
          rcases hR with ⟨c', hc', rfl⟩; rw [pow_succ']; omega
        | escape => rw [ho] at hR; exact absurd hR (Finset.notMem_empty _)
        | unresolved => rw [ho] at hR; exact absurd hR (Finset.notMem_empty _)
        | toState y =>
          rw [ho] at hR; simp only [Finset.mem_image] at hR
          rcases hR with ⟨c', _, rfl⟩
          have := (canonPull_spec hb3 hb_odd ho m c').1; omega
    have hE_sub : ∀ c ∈ canonRunCylSet b (m + 1) x, c < 2 ^ (m + 1) := by
      intro c hc
      simp only [canonRunCylSet, Finset.mem_union] at hc
      rcases hc with hL | hR
      · simp only [Finset.mem_image] at hL; rcases hL with ⟨c', hc', rfl⟩
        have := ihh.2.1 c' hc'; rw [pow_succ']; omega
      · cases ho : oddStretchOutcome b x with
        | escape =>
          rw [ho] at hR; simp only [Finset.mem_image, Finset.mem_range] at hR
          rcases hR with ⟨c', hc', rfl⟩; rw [pow_succ']; omega
        | trap => rw [ho] at hR; exact absurd hR (Finset.notMem_empty _)
        | unresolved => rw [ho] at hR; exact absurd hR (Finset.notMem_empty _)
        | toState y =>
          rw [ho] at hR; simp only [Finset.mem_image] at hR
          rcases hR with ⟨c', _, rfl⟩
          have := (canonPull_spec hb3 hb_odd ho m c').1; omega
    have hT_mem : ∀ c ∈ canonTrapCylSet b (m + 1) x, ∀ n, MemOddCyl b ⟨x, c, m + 1⟩ n → n ∈ ZSet b := by
      intro c hc n hn
      simp only [canonTrapCylSet, Finset.mem_union] at hc
      rcases hc with hL | hR
      · simp only [Finset.mem_image] at hL; rcases hL with ⟨c', hc', rfl⟩
        exact zSet_of_iter (s := 1) hn.1
          (ihh.2.2.1 c' hc' (f_b b n) (even_half_memOddCyl hb3 hb_odd hx1 hxb (ihh.1 c' hc') hn))
      · cases ho : oddStretchOutcome b x with
        | trap =>
          rw [ho] at hR; simp only [Finset.mem_image, Finset.mem_range] at hR
          rcases hR with ⟨c', _, rfl⟩
          have hn1 : MemOddCyl b ⟨x, 1, 1⟩ n := by
            refine ⟨hn.1, hn.2.1, ?_⟩
            have hd : 2 ^ 1 ∣ 2 ^ (m + 1) := pow_dvd_pow 2 (by omega)
            rw [← Nat.mod_mod_of_dvd n hd, hn.2.2, Nat.mod_mod_of_dvd _ hd]; simp
          exact isTrapStretch_zSet hb_odd (oddStretchOutcome_eq_trap_iff.mp ho) hn1
        | escape => rw [ho] at hR; exact absurd hR (Finset.notMem_empty _)
        | unresolved => rw [ho] at hR; exact absurd hR (Finset.notMem_empty _)
        | toState y =>
          rw [ho] at hR; simp only [Finset.mem_image] at hR
          rcases hR with ⟨c', hc', rfl⟩
          have hy := (oddStretchOutcome_eq_toState_iff hb3).mp ho
          have ihy := ih y hy.1 hy.2.1
          have hn' : MemOddCyl b ⟨x, canonPull b x m c', 1 + m⟩ n := by simpa [add_comm] using hn
          have hpair := ((canonPull_spec hb3 hb_odd ho m c').2.2 n).mpr hn'
          exact zSet_of_iter (s := canonOutS b x) hn.1 (ihy.2.2.1 c' hc' _ hpair.2)
    have hE_mem : ∀ c ∈ canonRunCylSet b (m + 1) x, ∀ n, MemOddCyl b ⟨x, c, m + 1⟩ n → n ∈ DivSet b := by
      intro c hc n hn
      simp only [canonRunCylSet, Finset.mem_union] at hc
      rcases hc with hL | hR
      · simp only [Finset.mem_image] at hL; rcases hL with ⟨c', hc', rfl⟩
        exact divSet_of_iter (s := 1) hn.1
          (ihh.2.2.2.1 c' hc' (f_b b n) (even_half_memOddCyl hb3 hb_odd hx1 hxb (ihh.2.1 c' hc') hn))
      · cases ho : oddStretchOutcome b x with
        | escape =>
          rw [ho] at hR; simp only [Finset.mem_image, Finset.mem_range] at hR
          rcases hR with ⟨c', _, rfl⟩
          have hn1 : MemOddCyl b ⟨x, 1, 1⟩ n := by
            refine ⟨hn.1, hn.2.1, ?_⟩
            have hd : 2 ^ 1 ∣ 2 ^ (m + 1) := pow_dvd_pow 2 (by omega)
            rw [← Nat.mod_mod_of_dvd n hd, hn.2.2, Nat.mod_mod_of_dvd _ hd]; simp
          exact isCertifiedEscape_divSet hb_odd ((oddStretchOutcome_eq_escape_iff hb3).mp ho) hn1
        | trap => rw [ho] at hR; exact absurd hR (Finset.notMem_empty _)
        | unresolved => rw [ho] at hR; exact absurd hR (Finset.notMem_empty _)
        | toState y =>
          rw [ho] at hR; simp only [Finset.mem_image] at hR
          rcases hR with ⟨c', hc', rfl⟩
          have hy := (oddStretchOutcome_eq_toState_iff hb3).mp ho
          have ihy := ih y hy.1 hy.2.1
          have hn' : MemOddCyl b ⟨x, canonPull b x m c', 1 + m⟩ n := by simpa [add_comm] using hn
          have hpair := ((canonPull_spec hb3 hb_odd ho m c').2.2 n).mpr hn'
          exact divSet_of_iter (s := canonOutS b x) hn.1 (ihy.2.2.2.1 c' hc' _ hpair.2)
    have hT_card : ((canonTrapCylSet b (m + 1) x).card : ℝ) / (2 ^ (m + 1) : ℝ) = oddTrapProb b (m + 1) x := by
      simp only [canonTrapCylSet, oddTrapProb]
      have hcardL : ((canonTrapCylSet b m (half x)).image (fun c => 2 * c)).card =
          (canonTrapCylSet b m (half x)).card :=
        Finset.card_image_of_injective _ (fun a₁ a₂ h => by omega)
      cases ho : oddStretchOutcome b x with
      | trap =>
        have hdj : Disjoint ((canonTrapCylSet b m (half x)).image (fun c => 2 * c))
            ((Finset.range (2 ^ m)).image (fun c => 2 * c + 1)) := by
          rw [Finset.disjoint_left]; intro c h1 h2
          simp only [Finset.mem_image] at h1 h2
          rcases h1 with ⟨_, _, rfl⟩; rcases h2 with ⟨_, _, heq⟩; omega
        rw [Finset.card_union_of_disjoint hdj, hcardL,
            Finset.card_image_of_injective _ (fun a₁ a₂ h => by omega), Finset.card_range,
            ← ihh.2.2.2.2.1]
        push_cast; rw [pow_succ']; field_simp
      | escape =>
        rw [Finset.union_empty, hcardL, ← ihh.2.2.2.2.1]
        rw [pow_succ']; field_simp; ring
      | unresolved =>
        rw [Finset.union_empty, hcardL, ← ihh.2.2.2.2.1]
        rw [pow_succ']; field_simp; ring
      | toState y =>
        have hy := (oddStretchOutcome_eq_toState_iff hb3).mp ho
        have ihy := ih y hy.1 hy.2.1
        have hdj : Disjoint ((canonTrapCylSet b m (half x)).image (fun c => 2 * c))
            ((canonTrapCylSet b m y).image (fun c => canonPull b x m c)) := by
          rw [Finset.disjoint_left]; intro c h1 h2
          simp only [Finset.mem_image] at h1 h2
          rcases h1 with ⟨_, _, rfl⟩; rcases h2 with ⟨c2, _, heq⟩
          have hp := (canonPull_spec hb3 hb_odd ho m c2).2.1; omega
        have hcardR : ((canonTrapCylSet b m y).image (fun c => canonPull b x m c)).card =
            (canonTrapCylSet b m y).card :=
          Finset.card_image_of_injOn fun c1 hc1 c2 hc2 heq =>
            canonPull_inj hb3 hb_odd ho m c1 c2 (ihy.1 c1 hc1) (ihy.1 c2 hc2) heq
        dsimp only
        rw [Finset.card_union_of_disjoint hdj, hcardL, hcardR, ← ihh.2.2.2.2.1, ← ihy.2.2.2.2.1]
        push_cast; rw [pow_succ']; field_simp
    have hE_card : ((canonRunCylSet b (m + 1) x).card : ℝ) / (2 ^ (m + 1) : ℝ) = oddRunProb b (m + 1) x := by
      simp only [canonRunCylSet, oddRunProb]
      have hcardL : ((canonRunCylSet b m (half x)).image (fun c => 2 * c)).card =
          (canonRunCylSet b m (half x)).card :=
        Finset.card_image_of_injective _ (fun a₁ a₂ h => by omega)
      cases ho : oddStretchOutcome b x with
      | escape =>
        have hdj : Disjoint ((canonRunCylSet b m (half x)).image (fun c => 2 * c))
            ((Finset.range (2 ^ m)).image (fun c => 2 * c + 1)) := by
          rw [Finset.disjoint_left]; intro c h1 h2
          simp only [Finset.mem_image] at h1 h2
          rcases h1 with ⟨_, _, rfl⟩; rcases h2 with ⟨_, _, heq⟩; omega
        rw [Finset.card_union_of_disjoint hdj, hcardL,
            Finset.card_image_of_injective _ (fun a₁ a₂ h => by omega), Finset.card_range,
            ← ihh.2.2.2.2.2]
        push_cast; rw [pow_succ']; field_simp
      | trap =>
        rw [Finset.union_empty, hcardL, ← ihh.2.2.2.2.2]
        rw [pow_succ']; field_simp; ring
      | unresolved =>
        rw [Finset.union_empty, hcardL, ← ihh.2.2.2.2.2]
        rw [pow_succ']; field_simp; ring
      | toState y =>
        have hy := (oddStretchOutcome_eq_toState_iff hb3).mp ho
        have ihy := ih y hy.1 hy.2.1
        have hdj : Disjoint ((canonRunCylSet b m (half x)).image (fun c => 2 * c))
            ((canonRunCylSet b m y).image (fun c => canonPull b x m c)) := by
          rw [Finset.disjoint_left]; intro c h1 h2
          simp only [Finset.mem_image] at h1 h2
          rcases h1 with ⟨_, _, rfl⟩; rcases h2 with ⟨c2, _, heq⟩
          have hp := (canonPull_spec hb3 hb_odd ho m c2).2.1; omega
        have hcardR : ((canonRunCylSet b m y).image (fun c => canonPull b x m c)).card =
            (canonRunCylSet b m y).card :=
          Finset.card_image_of_injOn fun c1 hc1 c2 hc2 heq =>
            canonPull_inj hb3 hb_odd ho m c1 c2 (ihy.2.1 c1 hc1) (ihy.2.1 c2 hc2) heq
        dsimp only
        rw [Finset.card_union_of_disjoint hdj, hcardL, hcardR, ← ihh.2.2.2.2.2, ← ihy.2.2.2.2.2]
        push_cast; rw [pow_succ']; field_simp
    exact ⟨hT_sub, hE_sub, hT_mem, hE_mem, hT_card, hE_card⟩

/-- Universal finite-cylinder lower-density bound for `oddTrapMass b` (every odd `b ≥ 3`). -/
theorem oddTrapMass_lower_density {b : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1) :
    ∀ ε > 0, ∀ᶠ N in atTop, oddTrapMass b - ε ≤ countFrac (ZSet b) N := by
  intro ε hε
  have hsum_tend : Tendsto (fun m => (1 + ∑ x ∈ Finset.Ico 1 b, oddTrapProb b m x) / (b : ℝ))
      atTop (𝓝 (oddTrapMass b)) := by
    unfold oddTrapMass
    exact ((tendsto_const_nhds.add (tendsto_finsetSum _ fun x hx =>
      oddTrapProb_tendsto hb3 hb_odd (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2)).div_const (b : ℝ))
  obtain ⟨m, hm⟩ := Metric.tendsto_atTop.mp hsum_tend (ε / 2) (by linarith)
  have hτm : oddTrapMass b - ε / 2 ≤ (1 + ∑ x ∈ Finset.Ico 1 b, oddTrapProb b m x) / (b : ℝ) := by
    have h1 := hm m (le_refl m); rw [Real.dist_eq, abs_lt] at h1; linarith
  have hprop := canon_cyl_props hb3 hb_odd m
  have hlow := cyl_union_lower_density hb3 hb_odd (S := ZSet b) (F := canonTrapCylSet b m) true
    (fun x hx1 hxb => (hprop x hx1 hxb).1)
    (fun x hx1 hxb => (hprop x hx1 hxb).2.2.1)
    (fun _ n hn1 hdvd => ⟨hn1, 0, by simpa using hdvd⟩) (ε / 2) (by linarith)
  have hsum_eq : ∑ x ∈ Finset.Ico 1 b, ((canonTrapCylSet b m x).card : ℝ) / (2 ^ m : ℝ) =
      ∑ x ∈ Finset.Ico 1 b, oddTrapProb b m x :=
    Finset.sum_congr rfl fun x hx => (hprop x (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2).2.2.2.2.1
  filter_upwards [hlow] with N hN
  simp only [↓reduceIte, hsum_eq] at hN; linarith

/-- Universal finite-cylinder lower-density bound for `oddRunMass b` (every odd `b ≥ 3`). -/
theorem oddRunMass_lower_density {b : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1) :
    ∀ ε > 0, ∀ᶠ N in atTop, oddRunMass b - ε ≤ countFrac (DivSet b) N := by
  intro ε hε
  have hsum_tend : Tendsto (fun m => (∑ x ∈ Finset.Ico 1 b, oddRunProb b m x) / (b : ℝ))
      atTop (𝓝 (oddRunMass b)) := by
    unfold oddRunMass
    exact ((tendsto_finsetSum _ fun x hx =>
      oddRunProb_tendsto hb3 hb_odd (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2).div_const (b : ℝ))
  obtain ⟨m, hm⟩ := Metric.tendsto_atTop.mp hsum_tend (ε / 2) (by linarith)
  have hρm : oddRunMass b - ε / 2 ≤ (∑ x ∈ Finset.Ico 1 b, oddRunProb b m x) / (b : ℝ) := by
    have h1 := hm m (le_refl m); rw [Real.dist_eq, abs_lt] at h1; linarith
  have hprop := canon_cyl_props hb3 hb_odd m
  have hlow := cyl_union_lower_density hb3 hb_odd (S := DivSet b) (F := canonRunCylSet b m) false
    (fun x hx1 hxb => (hprop x hx1 hxb).2.1)
    (fun x hx1 hxb => (hprop x hx1 hxb).2.2.2.1)
    (fun h => by cases h) (ε / 2) (by linarith)
  have hsum_eq : ∑ x ∈ Finset.Ico 1 b, ((canonRunCylSet b m x).card : ℝ) / (2 ^ m : ℝ) =
      ∑ x ∈ Finset.Ico 1 b, oddRunProb b m x :=
    Finset.sum_congr rfl fun x hx => (hprop x (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2).2.2.2.2.2
  filter_upwards [hlow] with N hN
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add, hsum_eq] at hN; linarith

private lemma oddStateMass_full_of_sum_one {b : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (hfull : oddTrapMass b + oddRunMass b = 1) :
    ∀ x, 1 ≤ x → x < b → oddTrapStateMass b x + oddRunStateMass b x = 1 := by
  have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hcard : (Finset.Ico 1 b).card = b - 1 := by simp
  have hsum1 : ∑ _x ∈ Finset.Ico 1 b, (1 : ℝ) = (b : ℝ) - 1 := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one, Nat.cast_sub (by omega), Nat.cast_one]
  have hsum_zero : ∑ x ∈ Finset.Ico 1 b, (1 - (oddTrapStateMass b x + oddRunStateMass b x)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum1]
    unfold oddTrapMass oddRunMass at hfull
    have hmul : (1 + ∑ x ∈ Finset.Ico 1 b, oddTrapStateMass b x) +
        (∑ x ∈ Finset.Ico 1 b, oddRunStateMass b x) = (b : ℝ) := by
      have h1 := congr_arg (· * (b : ℝ)) hfull
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hbpos), div_mul_cancel₀ _ (ne_of_gt hbpos), one_mul] at h1
      exact h1
    linarith
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun x hx => by
    have := (oddStateMass_bounds hb3 hb_odd (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2).2.2
    linarith).mp hsum_zero
  intro x hx1 hxb
  have h0 := hall x (Finset.mem_Ico.mpr ⟨hx1, hxb⟩)
  linarith

private lemma oddAbsorption_homog_zero {b : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (hfull : oddTrapMass b + oddRunMass b = 1) {w : ℕ → ℝ}
    (hw : ∀ x, 1 ≤ x → x < b →
      w x = (1 / 2 : ℝ) * w ((x * ((b + 1) / 2)) % b) +
            (1 / 2 : ℝ) * match oddStretchOutcome b x with
              | .toState y => w y
              | _ => 0) :
    ∀ x, 1 ≤ x → x < b → w x = 0 := by
  have hne : (Finset.Ico 1 b).Nonempty := Finset.nonempty_Ico.mpr (by omega)
  let M : ℝ := (Finset.Ico 1 b).sup' hne (fun x => |w x|)
  have hM_ge : ∀ x, 1 ≤ x → x < b → |w x| ≤ M := fun x hx1 hxb =>
    Finset.le_sup' (fun z => |w z|) (Finset.mem_Ico.mpr ⟨hx1, hxb⟩)
  have hM_nonneg : 0 ≤ M := (abs_nonneg (w 1)).trans (hM_ge 1 (le_refl 1) (by omega))
  let u (m x : ℕ) : ℝ := 1 - oddTrapProb b m x - oddRunProb b m x
  have hu_bound : ∀ m x, 1 ≤ x → x < b → |w x| ≤ M * u m x := by
    intro m
    induction m with
    | zero =>
      intro x hx1 hxb
      simpa [u, oddTrapProb, oddRunProb] using hM_ge x hx1 hxb
    | succ m ih =>
      intro x hx1 hxb
      have hhalf := half_pos_lt hb3 hb_odd hx1 hxb
      have ihh := ih _ hhalf.1 hhalf.2
      have hwx := hw x hx1 hxb
      have hu_eq : u (m + 1) x = (1 / 2 : ℝ) * u m ((x * ((b + 1) / 2)) % b) +
          (1 / 2 : ℝ) * match oddStretchOutcome b x with
            | .trap => 0
            | .escape => 0
            | .toState y => u m y
            | .unresolved => 1 := by
        dsimp only [u, oddTrapProb, oddRunProb]
        cases oddStretchOutcome b x <;> ring
      rw [hwx, hu_eq]
      cases ho : oddStretchOutcome b x with
      | trap =>
        simp only [mul_zero, add_zero, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
        nlinarith
      | escape =>
        simp only [mul_zero, add_zero, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
        nlinarith
      | unresolved =>
        simp only [mul_zero, add_zero, mul_one, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
        nlinarith
      | toState y =>
        have hy := (oddStretchOutcome_eq_toState_iff hb3).mp ho
        have ihy := ih y hy.1 hy.2.1
        have htri := abs_add_le ((1 / 2 : ℝ) * w ((x * ((b + 1) / 2)) % b)) ((1 / 2 : ℝ) * w y)
        rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)] at htri
        nlinarith
  intro x hx1 hxb
  have hst := oddStateMass_full_of_sum_one hb3 hb_odd hfull x hx1 hxb
  have hu_tend : Tendsto (fun m => M * u m x) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m => u m x) atTop (𝓝 (1 - oddTrapStateMass b x - oddRunStateMass b x)) :=
      (tendsto_const_nhds.sub (oddTrapProb_tendsto hb3 hb_odd hx1 hxb)).sub
        (oddRunProb_tendsto hb3 hb_odd hx1 hxb)
    rw [show 1 - oddTrapStateMass b x - oddRunStateMass b x = 0 by linarith] at h1
    simpa [mul_zero] using h1.const_mul M
  have hle0 : |w x| ≤ 0 := ge_of_tendsto hu_tend (Eventually.of_forall fun m => hu_bound m x hx1 hxb)
  exact abs_eq_zero.mp (le_antisymm hle0 (abs_nonneg _))

/-- Uniqueness of the trap absorption linear system whenever `oddTrapMass b + oddRunMass b = 1`. -/
theorem oddTrapStateMass_unique_of_full {b : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (hfull : oddTrapMass b + oddRunMass b = 1) {v : ℕ → ℝ}
    (hv : ∀ x, 1 ≤ x → x < b →
      v x = (1 / 2 : ℝ) * v ((x * ((b + 1) / 2)) % b) +
            (1 / 2 : ℝ) * match oddStretchOutcome b x with
              | .trap => 1 | .escape => 0 | .toState y => v y | .unresolved => 0) :
    (∀ x, 1 ≤ x → x < b → v x = oddTrapStateMass b x) ∧
    (1 + ∑ x ∈ Finset.Ico 1 b, v x) / (b : ℝ) = oddTrapMass b := by
  have hdiff : ∀ x, 1 ≤ x → x < b → v x - oddTrapStateMass b x = 0 :=
    oddAbsorption_homog_zero hb3 hb_odd hfull (w := fun x => v x - oddTrapStateMass b x) fun x hx1 hxb => by
      have h1 := hv x hx1 hxb
      have h2 := oddTrapStateMass_eq hb3 hb_odd hx1 hxb
      cases ho : oddStretchOutcome b x <;> rw [ho] at h1 h2 <;> linarith
  have hpt : ∀ x, 1 ≤ x → x < b → v x = oddTrapStateMass b x := fun x hx1 hxb =>
    sub_eq_zero.mp (hdiff x hx1 hxb)
  refine ⟨hpt, ?_⟩
  unfold oddTrapMass
  congr 2
  exact Finset.sum_congr rfl fun x hx => hpt x (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2

/-- Uniqueness of the escape absorption linear system whenever `oddTrapMass b + oddRunMass b = 1`. -/
theorem oddRunStateMass_unique_of_full {b : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (hfull : oddTrapMass b + oddRunMass b = 1) {v : ℕ → ℝ}
    (hv : ∀ x, 1 ≤ x → x < b →
      v x = (1 / 2 : ℝ) * v ((x * ((b + 1) / 2)) % b) +
            (1 / 2 : ℝ) * match oddStretchOutcome b x with
              | .trap => 0 | .escape => 1 | .toState y => v y | .unresolved => 0) :
    (∀ x, 1 ≤ x → x < b → v x = oddRunStateMass b x) ∧
    (∑ x ∈ Finset.Ico 1 b, v x) / (b : ℝ) = oddRunMass b := by
  have hdiff : ∀ x, 1 ≤ x → x < b → v x - oddRunStateMass b x = 0 :=
    oddAbsorption_homog_zero hb3 hb_odd hfull (w := fun x => v x - oddRunStateMass b x) fun x hx1 hxb => by
      have h1 := hv x hx1 hxb
      have h2 := oddRunStateMass_eq hb3 hb_odd hx1 hxb
      cases ho : oddStretchOutcome b x <;> rw [ho] at h1 h2 <;> linarith
  have hpt : ∀ x, 1 ≤ x → x < b → v x = oddRunStateMass b x := fun x hx1 hxb =>
    sub_eq_zero.mp (hdiff x hx1 hxb)
  refine ⟨hpt, ?_⟩
  unfold oddRunMass
  congr 1
  exact Finset.sum_congr rfl fun x hx => hpt x (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2

/-- Exact rationality of the finite-chain absorption masses whenever `oddTrapMass b + oddRunMass b = 1`. -/
theorem oddAbsorption_rational_of_full {b : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (hfull : oddTrapMass b + oddRunMass b = 1) :
    ∃ qτ qρ : ℚ, (qτ : ℝ) = oddTrapMass b ∧ (qρ : ℝ) = oddRunMass b ∧ qτ + qρ = 1 := by
  let halfIdx (i : Fin (b - 1)) : Fin (b - 1) :=
    ⟨((i.val + 1) * ((b + 1) / 2)) % b - 1, by
      have h := half_pos_lt hb3 hb_odd (x := i.val + 1) (by omega) (by omega)
      omega⟩
  let stretchTerm (v : Fin (b - 1) → ℚ) (i : Fin (b - 1)) : ℚ :=
    match oddStretchOutcome b (i.val + 1) with
    | .toState y => if hy : 1 ≤ y ∧ y < b then v ⟨y - 1, by omega⟩ else 0
    | _ => 0
  let L : (Fin (b - 1) → ℚ) →ₗ[ℚ] (Fin (b - 1) → ℚ) :=
    { toFun := fun v i => v i - (1 / 2 : ℚ) * v (halfIdx i) - (1 / 2 : ℚ) * stretchTerm v i
      map_add' := fun u v => by
        ext i; dsimp only [Pi.add_apply, stretchTerm]
        cases oddStretchOutcome b (i.val + 1) with
        | trap => dsimp only; ring
        | escape => dsimp only; ring
        | unresolved => dsimp only; ring
        | toState y => dsimp only; split_ifs <;> ring
      map_smul' := fun c v => by
        ext i; dsimp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, stretchTerm]
        cases oddStretchOutcome b (i.val + 1) with
        | trap => dsimp only; ring
        | escape => dsimp only; ring
        | unresolved => dsimp only; ring
        | toState y => dsimp only; split_ifs <;> ring }
  have hcast_L : ∀ (v : Fin (b - 1) → ℚ) (x : ℕ) (hx1 : 1 ≤ x) (hxb : x < b),
      let i : Fin (b - 1) := ⟨x - 1, by omega⟩
      let vR : ℕ → ℝ := fun z => if hz : 1 ≤ z ∧ z < b then (v ⟨z - 1, by omega⟩ : ℝ) else 0
      (L v i : ℝ) = vR x - (1 / 2 : ℝ) * vR ((x * ((b + 1) / 2)) % b) -
        (1 / 2 : ℝ) * match oddStretchOutcome b x with | .toState y => vR y | _ => 0 := by
    intro v x hx1 hxb
    have hhalf := half_pos_lt hb3 hb_odd hx1 hxb
    have hhalfIdx : halfIdx ⟨x - 1, by omega⟩ = ⟨((x * ((b + 1) / 2)) % b) - 1, by omega⟩ :=
      Fin.ext (by dsimp [halfIdx]; rw [show x - 1 + 1 = x by omega])
    dsimp only [L, LinearMap.coe_mk, AddHom.coe_mk, stretchTerm]
    rw [dite_eq_left_of_eq_true (eq_true (show 1 ≤ x ∧ x < b from ⟨hx1, hxb⟩)),
        dite_eq_left_of_eq_true (eq_true hhalf), hhalfIdx, show x - 1 + 1 = x by omega]
    cases ho : oddStretchOutcome b x with
    | trap => dsimp only; push_cast; ring
    | escape => dsimp only; push_cast; ring
    | unresolved => dsimp only; push_cast; ring
    | toState y =>
      have hy := (oddStretchOutcome_eq_toState_iff hb3).mp ho
      have hcond : 1 ≤ y ∧ y < b := ⟨hy.1, hy.2.1⟩
      dsimp only
      simp only [dite_eq_left_of_eq_true (eq_true hcond)]
      push_cast; ring
  have hL_ker : ∀ w : Fin (b - 1) → ℚ, L w = 0 → w = 0 := by
    intro w hLw
    let wR (x : ℕ) : ℝ := if hx : 1 ≤ x ∧ x < b then (w ⟨x - 1, by omega⟩ : ℝ) else 0
    have hwR : ∀ x, 1 ≤ x → x < b →
        wR x = (1 / 2 : ℝ) * wR ((x * ((b + 1) / 2)) % b) +
               (1 / 2 : ℝ) * match oddStretchOutcome b x with | .toState y => wR y | _ => 0 := by
      intro x hx1 hxb
      have h1 := hcast_L w x hx1 hxb
      dsimp only at h1
      rw [congr_fun hLw ⟨x - 1, by omega⟩, Pi.zero_apply, Rat.cast_zero] at h1
      linarith
    have hzero := oddAbsorption_homog_zero hb3 hb_odd hfull hwR
    ext i
    have hz := hzero (i.val + 1) (by omega) (by omega)
    have hval : wR (i.val + 1) = (w i : ℝ) := by
      have hc : 1 ≤ i.val + 1 ∧ i.val + 1 < b := ⟨by omega, by omega⟩
      dsimp only [wR]
      rw [dite_eq_left_of_eq_true (eq_true hc)]
      congr 1
    rw [hval] at hz
    exact Rat.cast_eq_zero.mp hz
  have hInj : Function.Injective L := by
    intro u v huv
    have hsub : L (u - v) = 0 := by rw [map_sub, huv, sub_self]
    exact sub_eq_zero.mp (hL_ker (u - v) hsub)
  have hSurj : Function.Surjective L := LinearMap.injective_iff_surjective.mp hInj
  let rhsT : Fin (b - 1) → ℚ := fun i =>
    match oddStretchOutcome b (i.val + 1) with | .trap => 1 / 2 | _ => 0
  let rhsE : Fin (b - 1) → ℚ := fun i =>
    match oddStretchOutcome b (i.val + 1) with | .escape => 1 / 2 | _ => 0
  obtain ⟨vT, hvT⟩ := hSurj rhsT
  obtain ⟨vE, hvE⟩ := hSurj rhsE
  let vTR (x : ℕ) : ℝ := if hx : 1 ≤ x ∧ x < b then (vT ⟨x - 1, by omega⟩ : ℝ) else 0
  let vER (x : ℕ) : ℝ := if hx : 1 ≤ x ∧ x < b then (vE ⟨x - 1, by omega⟩ : ℝ) else 0
  have hvT_eq : ∀ x, 1 ≤ x → x < b →
      vTR x = (1 / 2 : ℝ) * vTR ((x * ((b + 1) / 2)) % b) +
              (1 / 2 : ℝ) * match oddStretchOutcome b x with
                | .trap => 1 | .escape => 0 | .toState y => vTR y | .unresolved => 0 := by
    intro x hx1 hxb
    have h1 := hcast_L vT x hx1 hxb
    dsimp only at h1
    rw [congr_fun hvT ⟨x - 1, by omega⟩] at h1
    dsimp only [rhsT] at h1
    rw [show x - 1 + 1 = x by omega] at h1
    cases ho : oddStretchOutcome b x <;> rw [ho] at h1 <;> dsimp only at h1 ⊢ <;> push_cast at h1 <;> linarith
  have hvE_eq : ∀ x, 1 ≤ x → x < b →
      vER x = (1 / 2 : ℝ) * vER ((x * ((b + 1) / 2)) % b) +
              (1 / 2 : ℝ) * match oddStretchOutcome b x with
                | .trap => 0 | .escape => 1 | .toState y => vER y | .unresolved => 0 := by
    intro x hx1 hxb
    have h1 := hcast_L vE x hx1 hxb
    dsimp only at h1
    rw [congr_fun hvE ⟨x - 1, by omega⟩] at h1
    dsimp only [rhsE] at h1
    rw [show x - 1 + 1 = x by omega] at h1
    cases ho : oddStretchOutcome b x <;> rw [ho] at h1 <;> dsimp only at h1 ⊢ <;> push_cast at h1 <;> linarith
  have huniqT := oddTrapStateMass_unique_of_full hb3 hb_odd hfull hvT_eq
  have huniqE := oddRunStateMass_unique_of_full hb3 hb_odd hfull hvE_eq
  let qτ : ℚ := (1 + ∑ i : Fin (b - 1), vT i) / (b : ℚ)
  let qρ : ℚ := (∑ i : Fin (b - 1), vE i) / (b : ℚ)
  have hsum_cast : ∀ (v : Fin (b - 1) → ℚ),
      ∑ i : Fin (b - 1), (v i : ℝ) =
        ∑ x ∈ Finset.Ico 1 b, (if hx : 1 ≤ x ∧ x < b then (v ⟨x - 1, by omega⟩ : ℝ) else 0) := by
    intro v
    refine Finset.sum_bij (fun i _ => i.val + 1)
      (fun i _ => Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
      (fun i _ j _ h => Fin.ext (by omega))
      (fun x hx => ⟨⟨x - 1, by have := Finset.mem_Ico.mp hx; omega⟩, Finset.mem_univ _, by
        dsimp only; have := Finset.mem_Ico.mp hx; omega⟩)
      (fun i _ => ?_)
    have hc : 1 ≤ i.val + 1 ∧ i.val + 1 < b := ⟨by omega, by omega⟩
    rw [dite_eq_left_of_eq_true (eq_true hc)]
    congr 1
  have hqτ : (qτ : ℝ) = oddTrapMass b := by
    dsimp only [qτ]; push_cast; rw [hsum_cast vT]; exact huniqT.2
  have hqρ : (qρ : ℝ) = oddRunMass b := by
    dsimp only [qρ]; push_cast; rw [hsum_cast vE]; exact huniqE.2
  have hqsum : qτ + qρ = 1 := by
    exact_mod_cast (show ((qτ + qρ : ℚ) : ℝ) = (1 : ℝ) by push_cast; rw [hqτ, hqρ, hfull])
  exact ⟨qτ, qρ, hqτ, hqρ, hqsum⟩

/-- Universal odd-base finite-cylinder absorption theorem (Theorem 13, general clause for every
    odd `b ≥ 3`): the canonical Section 6.2 masses `oddTrapMass b` (`τ_b`) and `oddRunMass b`
    (`ρ_b`) satisfy `1 / b ≤ τ_b`, `0 ≤ ρ_b`, `τ_b + ρ_b ≤ 1`, lower-density bounds for `Z_b`
    and `E_b`, and whenever `τ_b + ρ_b = 1` all three natural densities exist with
    `d(Z_b) = d(R_b) = τ_b` and `d(E_b) = ρ_b` as exact rationals. -/
theorem thm_odd_absorption_universal {b : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1) :
    (1 : ℝ) / (b : ℝ) ≤ oddTrapMass b ∧
    0 ≤ oddRunMass b ∧
    oddTrapMass b + oddRunMass b ≤ 1 ∧
    (∀ ε > 0, ∀ᶠ N in atTop, oddTrapMass b - ε ≤ countFrac (ZSet b) N) ∧
    (∀ ε > 0, ∀ᶠ N in atTop, oddRunMass b - ε ≤ countFrac (DivSet b) N) ∧
    (oddTrapMass b + oddRunMass b = 1 →
      Tendsto (countFrac (ZSet b)) atTop (𝓝 (oddTrapMass b)) ∧
      Tendsto (countFrac (RSet b)) atTop (𝓝 (oddTrapMass b)) ∧
      Tendsto (countFrac (DivSet b)) atTop (𝓝 (oddRunMass b)) ∧
      (∃ qτ qρ : ℚ, (qτ : ℝ) = oddTrapMass b ∧ (qρ : ℝ) = oddRunMass b ∧ qτ + qρ = 1)) := by
  have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hτ_ge : (1 : ℝ) / (b : ℝ) ≤ oddTrapMass b := by
    unfold oddTrapMass
    apply div_le_div_of_nonneg_right _ (le_of_lt hbpos)
    have hnn := Finset.sum_nonneg fun x hx =>
      (oddStateMass_bounds hb3 hb_odd (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2).1
    linarith
  have hρ_nn : 0 ≤ oddRunMass b := by
    unfold oddRunMass
    exact div_nonneg (Finset.sum_nonneg fun x hx =>
      (oddStateMass_bounds hb3 hb_odd (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2).2.1)
      (le_of_lt hbpos)
  have hsum_le : oddTrapMass b + oddRunMass b ≤ 1 := by
    unfold oddTrapMass oddRunMass
    rw [← add_div, div_le_one hbpos]
    have h1 : ∑ x ∈ Finset.Ico 1 b, (oddTrapStateMass b x + oddRunStateMass b x) ≤
        ∑ _x ∈ Finset.Ico 1 b, (1 : ℝ) :=
      Finset.sum_le_sum fun x hx =>
        (oddStateMass_bounds hb3 hb_odd (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2).2.2
    have hcard : (Finset.Ico 1 b).card = b - 1 := by simp
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul, mul_one,
        Nat.cast_sub (by omega), Nat.cast_one] at h1
    linarith
  have hZ_low := oddTrapMass_lower_density hb3 hb_odd
  have hD_low := oddRunMass_lower_density hb3 hb_odd
  refine ⟨hτ_ge, hρ_nn, hsum_le, hZ_low, hD_low, fun hfull => ?_⟩
  have hdj := thm_odd_densities_disjoint hb3 hb_odd
  have hsq := thm_odd_densities_squeeze hdj.1 (Set.Subset.refl _) hdj.2 hfull hZ_low hD_low
  exact ⟨hsq.1, hsq.2.1, hsq.2.2, oddAbsorption_rational_of_full hb3 hb_odd hfull⟩

/-! ## Section 5: Modular Soundness of `checkRes` & Exact BFS Full Absorption -/

private lemma tag1_step_sound {b : ℕ} {isSplit : Bool} {seeds : List (ℕ × ℕ × ℕ)} {dt : QT}
    (hb3 : 3 ≤ b) (hb_lt : b < 2048) (hb_odd : b % 2 = 1)
    (hseed_ok : ∀ s ∈ seeds, 1 ≤ s.1 ∧ s.1 < b ∧ IsCertifiedEscape b s.1)
    (hres_all : ∀ x, 1 ≤ x → x < b → checkRes b ((b + 1) / 2) isSplit seeds dt x = true) :
    ∀ x, 1 ≤ x → x < b → getTag dt x = 1 →
      isSplit = true ∧
      (IsCertifiedEscape b x ∨
       ∃ s y, 1 ≤ s ∧ 1 ≤ y ∧ y < b ∧ getTag dt y = 1 ∧
         (∀ i ≤ s, 1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).x ∧ ((cylStep b)^[i] ⟨x, 1, 1⟩).x < b ∧
                   1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).j) ∧
         CylSubset b ((cylStep b)^[s] ⟨x, 1, 1⟩) ⟨y, 1, 1⟩) := by
  intro x hx1 hxb htg
  have hr := hres_all x hx1 hxb
  unfold checkRes at hr
  rw [htg] at hr
  cases isSplit with
  | false => simp at hr
  | true =>
    refine ⟨rfl, ?_⟩
    cases hm : memSeeds x seeds with
    | true =>
      left
      obtain ⟨s, hs_mem, hs_x⟩ := memSeeds_sound hm
      have hsd := hseed_ok s hs_mem
      rw [hs_x] at hsd
      exact hsd.2.2
    | false =>
      right
      simp only [hm] at hr
      cases hx0 : Nat.beq ((x * x + 1) % b) 0 with
      | true => simp [hx0] at hr
      | false =>
        simp only [hx0] at hr
        have hx1_pos : 1 ≤ (x * x + 1) % b := by
          have : (x * x + 1) % b ≠ 0 := fun h => by rw [h] at hx0; exact absurd hx0 (by decide)
          omega
        have hx1_lt : (x * x + 1) % b < b := Nat.mod_lt _ (by omega)
        have hstep1 : cylStep b ⟨x, 1, 1⟩ =
            ⟨(x * x + 1) % b, (x * 1 + 1) % 2 ^ (1 + padicValNat 2 x), 1 + padicValNat 2 x⟩ :=
          cylStep_odd_eq (by dsimp; decide)
        have hp2 : 2 * p2v2 x = 2 ^ (1 + padicValNat 2 x) := by
          rw [p2v2_eq_two_pow_padicValNat hx1 (by omega), pow_add, pow_one]
        have htr_ok : traceRunLoop b ((b + 1) / 2) dt 8
            (cylStep b ⟨x, 1, 1⟩).x (cylStep b ⟨x, 1, 1⟩).c (2 ^ (cylStep b ⟨x, 1, 1⟩).j) = true := by
          rw [hstep1]; simpa [hp2, mul_one] using hr
        obtain ⟨s, y, hy1, hyb, hty, hval, hsub⟩ :=
          traceRunLoop_sound hb3 hb_lt hb_odd dt 8 (cylStep b ⟨x, 1, 1⟩)
            (by rw [hstep1]; exact hx1_pos) (by rw [hstep1]; exact hx1_lt)
            (by rw [hstep1]; exact Nat.le_add_right 1 _) (cylStep_c_lt _) htr_ok
        refine ⟨s + 1, y, by omega, hy1, hyb, hty, fun i hi => ?_, ?_⟩
        · cases i with
          | zero => exact ⟨hx1, hxb, le_refl 1⟩
          | succ i => rw [Function.iterate_succ_apply]; exact hval i (by omega)
        · rw [Function.iterate_succ_apply]; exact hsub

private lemma tag1_escape_sound {b : ℕ} {isSplit : Bool} {seeds : List (ℕ × ℕ × ℕ)} {dt : QT}
    (hb3 : 3 ≤ b) (hb_lt : b < 2048) (hb_odd : b % 2 = 1)
    (hseed_ok : ∀ s ∈ seeds, 1 ≤ s.1 ∧ s.1 < b ∧ IsCertifiedEscape b s.1)
    (hres_all : ∀ x, 1 ≤ x → x < b → checkRes b ((b + 1) / 2) isSplit seeds dt x = true) :
    ∀ x, 1 ≤ x → x < b → getTag dt x = 1 → IsCertifiedEscape b x := by
  classical
  have htag1_step := tag1_step_sound hb3 hb_lt hb_odd hseed_ok hres_all
  intro x0 hx0_1 hx0_b htg0
  let P_dir (x : ℕ) : Prop := IsCertifiedEscape b x
  let next1 (x : ℕ) : ℕ :=
    if h : 1 ≤ x ∧ x < b ∧ getTag dt x = 1 then
      if hdir : P_dir x then x
      else
        have hex := (htag1_step x h.1 h.2.1 h.2.2).2.resolve_left hdir
        Classical.choose (Classical.choose_spec hex)
    else x
  let step1 (x : ℕ) : ℕ :=
    if h : 1 ≤ x ∧ x < b ∧ getTag dt x = 1 then
      if hdir : P_dir x then 0
      else
        have hex := (htag1_step x h.1 h.2.1 h.2.2).2.resolve_left hdir
        Classical.choose hex
    else 0
  have hstep1_spec : ∀ x, 1 ≤ x → x < b → getTag dt x = 1 → ¬ P_dir x →
      1 ≤ step1 x ∧ 1 ≤ next1 x ∧ next1 x < b ∧ getTag dt (next1 x) = 1 ∧
      (∀ i ≤ step1 x, 1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).x ∧
                      ((cylStep b)^[i] ⟨x, 1, 1⟩).x < b ∧
                      1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).j) ∧
      CylSubset b ((cylStep b)^[step1 x] ⟨x, 1, 1⟩) ⟨next1 x, 1, 1⟩ := by
    intro x hx1 hxb htg hnd
    have hcond : 1 ≤ x ∧ x < b ∧ getTag dt x = 1 := ⟨hx1, hxb, htg⟩
    simp only [step1, next1, hcond, hnd, ↓reduceDIte]
    exact Classical.choose_spec (Classical.choose_spec ((htag1_step x hx1 hxb htg).2.resolve_left hnd))
  have hnext_inv : ∀ k, 1 ≤ next1^[k] x0 ∧ next1^[k] x0 < b ∧ getTag dt (next1^[k] x0) = 1 := by
    intro k
    induction k with
    | zero => exact ⟨hx0_1, hx0_b, htg0⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      by_cases hdir : P_dir (next1^[k] x0)
      · simp only [next1, ih, hdir, ↓reduceDIte]; exact ih
      · have hs := hstep1_spec (next1^[k] x0) ih.1 ih.2.1 ih.2.2 hdir
        exact ⟨hs.2.1, hs.2.2.1, hs.2.2.2.1⟩
  have hcomp : ∀ (m r : ℕ), (∀ t < m, ¬ P_dir (next1^[r + t] x0)) →
      ∀ (C : OddCyl), CylSubset b C ⟨next1^[r] x0, 1, 1⟩ → C.x < b →
      ∃ S : ℕ, (m ≤ S) ∧
        (∀ i ≤ S, 1 ≤ ((cylStep b)^[i] C).x ∧ ((cylStep b)^[i] C).x < b ∧
                  1 ≤ ((cylStep b)^[i] C).j) ∧
        CylSubset b ((cylStep b)^[S] C) ⟨next1^[r + m] x0, 1, 1⟩ := by
    intro m
    induction m with
    | zero =>
      intro r _ C hsub hClt
      have hinv := hnext_inv r
      have hx_eq : C.x = next1^[r] x0 := by
        have := hsub.1; rw [Nat.mod_eq_of_lt hClt, Nat.mod_eq_of_lt hinv.2.1] at this; exact this
      refine ⟨0, le_refl 0, fun i hi => ?_, by simpa using hsub⟩
      have : i = 0 := by omega
      subst this
      exact ⟨hx_eq ▸ hinv.1, hClt, le_trans (le_refl 1) hsub.2.1⟩
    | succ m ih =>
      intro r hnd C hsub hClt
      have hinv := hnext_inv r
      have hnd0 : ¬ P_dir (next1^[r] x0) := by simpa using hnd 0 (by omega)
      have hs := hstep1_spec (next1^[r] x0) hinv.1 hinv.2.1 hinv.2.2 hnd0
      set s0 := step1 (next1^[r] x0)
      have hmono := cylSubset_cylStep_iter hb3 s0 C ⟨next1^[r] x0, 1, 1⟩ hsub hClt hinv.2.1
        (fun i hi => hs.2.2.2.2.1 i (by omega))
      have hsub1 : CylSubset b ((cylStep b)^[s0] C) ⟨next1^[r + 1] x0, 1, 1⟩ := by
        rw [Function.iterate_succ_apply']
        exact cylSubset_trans (hmono s0 (le_refl s0)).1 hs.2.2.2.2.2
      have hC1_lt : ((cylStep b)^[s0] C).x < b := by
        cases s0 with
        | zero => exact hClt
        | succ s0' => rw [Function.iterate_succ_apply']; exact cylStep_x_lt hb3 _
      obtain ⟨S2, hS2_ge, hval2, hsub2⟩ := ih (r + 1)
        (fun t ht => by
          have := hnd (t + 1) (by omega)
          rwa [show r + (t + 1) = r + 1 + t by omega] at this)
        ((cylStep b)^[s0] C) hsub1 hC1_lt
      refine ⟨s0 + S2, by omega, fun i hi => ?_, ?_⟩
      · by_cases hle : i < s0
        · exact (hmono i (by omega)).2 hle
        · rw [show i = (i - s0) + s0 by omega, Function.iterate_add_apply]
          exact hval2 (i - s0) (by omega)
      · rw [show s0 + S2 = S2 + s0 by omega, Function.iterate_add_apply,
            show r + (m + 1) = r + 1 + m by omega]
        exact hsub2
  by_cases hex_dir : ∃ r ≤ b, P_dir (next1^[r] x0)
  · let r := Nat.find hex_dir
    have hr_spec : r ≤ b ∧ P_dir (next1^[r] x0) := Nat.find_spec hex_dir
    have hnd_lt : ∀ t < r, ¬ P_dir (next1^[0 + t] x0) := by
      intro t ht hdir
      have : r ≤ t := Nat.find_min' hex_dir ⟨by omega, by simpa using hdir⟩
      omega
    obtain ⟨S, _, hval, hsub⟩ := hcomp r 0 hnd_lt ⟨x0, 1, 1⟩ (cylSubset_refl _) hx0_b
    exact isCertifiedEscape_of_step hb3 (hnext_inv r).2.1 hval (by simpa using hsub) hr_spec.2
  · push Not at hex_dir
    let f : Fin (b + 1) → Fin b := fun k => ⟨next1^[k.val] x0, (hnext_inv k.val).2.1⟩
    have hcard : Fintype.card (Fin b) < Fintype.card (Fin (b + 1)) := by simp
    obtain ⟨k1, k2, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
    wlog hlt : k1.val < k2.val generalizing k1 k2
    · exact this k2 k1 hne.symm heq.symm (by omega)
    have heq_val : next1^[k1.val] x0 = next1^[k2.val] x0 := congr_arg Fin.val heq
    obtain ⟨S1, _, hval1, hsub1⟩ := hcomp k1.val 0
      (fun t ht => by simpa using hex_dir t (by omega)) ⟨x0, 1, 1⟩ (cylSubset_refl _) hx0_b
    set z := next1^[k1.val] x0
    have hz_inv := hnext_inv k1.val
    obtain ⟨P, hP_ge, hvalP, hsubP⟩ := hcomp (k2.val - k1.val) k1.val
      (fun t ht => hex_dir (k1.val + t) (by omega)) ⟨z, 1, 1⟩ (cylSubset_refl _) hz_inv.2.1
    rw [show k1.val + (k2.val - k1.val) = k2.val by omega, ← heq_val] at hsubP
    exact ⟨S1, P, ⟨z, 1, 1⟩, by omega, hval1, by simpa [z] using hsub1, hvalP, hsubP⟩

private lemma tag0_trap_stretch_sound {b : ℕ} {isSplit : Bool} {seeds : List (ℕ × ℕ × ℕ)} {dt : QT}
    (hb3 : 3 ≤ b) (hb_lt : b < 2048) (hb_odd : b % 2 = 1)
    (hres_all : ∀ x, 1 ≤ x → x < b → checkRes b ((b + 1) / 2) isSplit seeds dt x = true) :
    ∀ x, 1 ≤ x → x < b → getTag dt x = 0 → IsTrapStretch b x := by
  intro x hx1 hxb htg
  have hr := hres_all x hx1 hxb
  unfold checkRes at hr
  rw [htg] at hr
  have hstep1 : cylStep b ⟨x, 1, 1⟩ =
      ⟨(x * x + 1) % b, (x * 1 + 1) % 2 ^ (1 + padicValNat 2 x), 1 + padicValNat 2 x⟩ :=
    cylStep_odd_eq (by dsimp; decide)
  by_cases hx_odd : x % 2 = 1
  · have hbeq : Nat.beq (x % 2) 1 = true := by rw [hx_odd]; rfl
    rw [hbeq] at hr
    have hx0 : (x * x + 1) % b = 0 := Nat.eq_of_beq_eq_true hr
    refine ⟨1, le_refl 1, fun i hi => ?_, by rw [Function.iterate_one, hstep1]; exact hx0⟩
    have : i = 0 := by omega
    subst this; exact ⟨hx1, hxb, le_refl 1⟩
  · have hbeq : Nat.beq (x % 2) 1 = false := by
      cases h : Nat.beq (x % 2) 1 with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true h) hx_odd
    rw [hbeq] at hr
    dsimp only at hr
    cases hx0 : Nat.beq ((x * x + 1) % b) 0 with
    | true =>
      have h0 : (x * x + 1) % b = 0 := Nat.eq_of_beq_eq_true hx0
      refine ⟨1, le_refl 1, fun i hi => ?_, by rw [Function.iterate_one, hstep1]; exact h0⟩
      have : i = 0 := by omega
      subst this; exact ⟨hx1, hxb, le_refl 1⟩
    | false =>
      rw [hx0] at hr
      dsimp only at hr
      have hx1_pos : 1 ≤ (x * x + 1) % b := by
        have : (x * x + 1) % b ≠ 0 := fun h => by rw [h] at hx0; exact absurd hx0 (by decide)
        omega
      have hx1_lt : (x * x + 1) % b < b := Nat.mod_lt _ (by omega)
      have hp2 : 2 * p2v2 x = 2 ^ (1 + padicValNat 2 x) := by
        rw [p2v2_eq_two_pow_padicValNat hx1 (by omega), pow_add, pow_one]
      have htr := tracePureLoop_sound hb3 hb_lt hb_odd 12 (cylStep b ⟨x, 1, 1⟩)
        (by rw [hstep1]; exact hx1_pos) (by rw [hstep1]; exact hx1_lt)
        (by rw [hstep1]; exact Nat.le_add_right 1 _) (cylStep_c_lt _)
      have hl1 : tracePureLoop b ((b + 1) / 2) 12 (cylStep b ⟨x, 1, 1⟩).x (cylStep b ⟨x, 1, 1⟩).c
          (2 ^ (cylStep b ⟨x, 1, 1⟩).j) = 1 := by
        rw [hstep1]; simpa [hp2, mul_one] using Nat.eq_of_beq_eq_true hr
      rw [hl1] at htr
      obtain ⟨s, hs1, hval, hx_zero⟩ := htr
      refine ⟨s + 1, by omega, fun i hi => ?_, by rw [Function.iterate_succ_apply]; exact hx_zero⟩
      cases i with
      | zero => exact ⟨hx1, hxb, le_refl 1⟩
      | succ i => rw [Function.iterate_succ_apply]; exact hval i (by omega)

private lemma tag_zero_sound {b : ℕ} {isSplit : Bool} {seeds : List (ℕ × ℕ × ℕ)} {dt : QT}
    (hb3 : 3 ≤ b) (hb_lt : b < 2048) (hb_odd : b % 2 = 1)
    (hres_all : ∀ x, 1 ≤ x → x < b → checkRes b ((b + 1) / 2) isSplit seeds dt x = true) :
    ∀ x, 1 ≤ x → x < b → 2 ≤ getTag dt x →
      ∃ y, IsZeroStretch b x y ∧
        (tagDist (getTag dt ((x * ((b + 1) / 2)) % b)) < tagDist (getTag dt x) ∨
         tagDist (getTag dt y) < tagDist (getTag dt x)) := by
  set inv2 := (b + 1) / 2
  intro x hx1 hxb htg_ge
  have hr := hres_all x hx1 hxb
  unfold checkRes at hr
  rcases htg_eq : getTag dt x with _ | _ | d
  · omega
  · omega
  · rw [htg_eq] at hr
    have hstep1 : cylStep b ⟨x, 1, 1⟩ =
        ⟨(x * x + 1) % b, (x * 1 + 1) % 2 ^ (1 + padicValNat 2 x), 1 + padicValNat 2 x⟩ :=
      cylStep_odd_eq (by dsimp; decide)
    have hunpack : ∀ y, checkZeroDist b inv2 dt x (d + 1) (y + 3) = true →
        tagDist (getTag dt ((x * inv2) % b)) < d + 1 ∨ tagDist (getTag dt y) < d + 1 := by
      intro y hcz
      unfold checkZeroDist at hcz
      cases h1 : Nat.ble (tagDist (getTag dt ((x * inv2) % b)) + 1) (d + 1) with
      | true => left; have := Nat.ble_eq.mp h1; omega
      | false =>
        rw [h1] at hcz
        right; have := Nat.ble_eq.mp hcz; omega
    by_cases hx_odd : x % 2 = 1
    · have hbeq : Nat.beq (x % 2) 1 = true := by rw [hx_odd]; rfl
      rw [hbeq] at hr
      dsimp only at hr
      cases hx0 : Nat.beq ((x * x + 1) % b) 0 with
      | true => rw [hx0] at hr; simp at hr
      | false =>
        rw [hx0] at hr
        have hx1_pos : 1 ≤ (x * x + 1) % b := by
          have : (x * x + 1) % b ≠ 0 := fun h => by rw [h] at hx0; exact absurd hx0 (by decide)
          omega
        have hx1_lt : (x * x + 1) % b < b := Nat.mod_lt _ (by omega)
        have hpos2 := half_pos_lt hb3 hb_odd hx1_pos hx1_lt
        have hv2_0 : padicValNat 2 x = 0 :=
          padicValNat_two_eq_of_dvd_not_dvd hx1 (by simp) (by omega)
        have hst1' : cylStep b ⟨x, 1, 1⟩ = ⟨(x * x + 1) % b, 0, 1⟩ := by
          rw [hstep1, hv2_0]; simp [show (x + 1) % 2 = 0 by omega]
        have hst2' : (cylStep b)^[2] ⟨x, 1, 1⟩ = ⟨((x * x + 1) % b * inv2) % b, 0, 0⟩ := by
          rw [Function.iterate_succ_apply, Function.iterate_one, hst1',
              cylStep_even_eq (le_refl 1) (by dsimp; norm_num) rfl]
          simp [inv2]
        rw [show 3 + ((x * x + 1) % b * inv2) % b = ((x * x + 1) % b * inv2) % b + 3 by omega] at hr
        refine ⟨((x * x + 1) % b * inv2) % b,
          ⟨hpos2.1, hpos2.2, 2, by omega, fun i hi => ?_, hst2'⟩,
          by dsimp only [tagDist]; exact hunpack _ hr⟩
        interval_cases i
        · exact ⟨hx1, hxb, le_refl 1⟩
        · rw [Function.iterate_one, hst1']; exact ⟨hx1_pos, hx1_lt, le_refl 1⟩
    · have hbeq : Nat.beq (x % 2) 1 = false := by
        cases h : Nat.beq (x % 2) 1 with
        | false => rfl
        | true => exact absurd (Nat.eq_of_beq_eq_true h) hx_odd
      rw [hbeq] at hr
      dsimp only at hr
      cases hx0 : Nat.beq ((x * x + 1) % b) 0 with
      | true => rw [hx0] at hr; simp at hr
      | false =>
        rw [hx0] at hr
        dsimp only at hr
        have hx1_pos : 1 ≤ (x * x + 1) % b := by
          have : (x * x + 1) % b ≠ 0 := fun h => by rw [h] at hx0; exact absurd hx0 (by decide)
          omega
        have hx1_lt : (x * x + 1) % b < b := Nat.mod_lt _ (by omega)
        have hp2 : 2 * p2v2 x = 2 ^ (1 + padicValNat 2 x) := by
          rw [p2v2_eq_two_pow_padicValNat hx1 (by omega), pow_add, pow_one]
        have htr := tracePureLoop_sound hb3 hb_lt hb_odd 12 (cylStep b ⟨x, 1, 1⟩)
          (by rw [hstep1]; exact hx1_pos) (by rw [hstep1]; exact hx1_lt)
          (by rw [hstep1]; exact Nat.le_add_right 1 _) (cylStep_c_lt _)
        have htr_eq : tracePureLoop b inv2 12 ((x * x + 1) % b) ((x + 1) % (2 * p2v2 x)) (2 * p2v2 x) =
            tracePureLoop b inv2 12 (cylStep b ⟨x, 1, 1⟩).x (cylStep b ⟨x, 1, 1⟩).c
              (2 ^ (cylStep b ⟨x, 1, 1⟩).j) := by
          rw [hstep1]; simp [hp2, mul_one]
        rw [htr_eq] at hr
        rcases hl : tracePureLoop b inv2 12 (cylStep b ⟨x, 1, 1⟩).x (cylStep b ⟨x, 1, 1⟩).c
            (2 ^ (cylStep b ⟨x, 1, 1⟩).j) with _ | _ | _ | y
        · rw [hl] at hr; simp [checkZeroDist] at hr
        · rw [hl] at hr; simp [checkZeroDist] at hr
        · rw [hl] at hr; simp [checkZeroDist] at hr
        · rw [hl] at htr hr
          obtain ⟨hy1, hyb, s, hs1, hval, hy_eq⟩ := htr
          refine ⟨y, ⟨hy1, hyb, s + 1, by omega, fun i hi => ?_, by rw [Function.iterate_succ_apply]; exact hy_eq⟩,
            by dsimp only [tagDist]; exact hunpack y hr⟩
          cases i with
          | zero => exact ⟨hx1, hxb, le_refl 1⟩
          | succ i => rw [Function.iterate_succ_apply]; exact hval i (by omega)

/-- BFS contraction on the canonical residual `u(m, x) = 1 - oddTrapProb b m x - oddRunProb b m x`
    proving full absorption `oddTrapMass b + oddRunMass b = 1`. -/
private lemma cert_full_absorption {b : ℕ} {dt : QT}
    (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (htag0 : ∀ x, 1 ≤ x → x < b → getTag dt x = 0 → oddStretchOutcome b x = .trap)
    (htag1 : ∀ x, 1 ≤ x → x < b → getTag dt x = 1 → oddStretchOutcome b x = .escape)
    (htag2 : ∀ x, 1 ≤ x → x < b → 2 ≤ getTag dt x →
      ∃ y, 1 ≤ y ∧ y < b ∧ oddStretchOutcome b x = .toState y ∧
        (tagDist (getTag dt ((x * ((b + 1) / 2)) % b)) < tagDist (getTag dt x) ∨
         tagDist (getTag dt y) < tagDist (getTag dt x))) :
    oddTrapMass b + oddRunMass b = 1 := by
  let half (x : ℕ) : ℕ := (x * ((b + 1) / 2)) % b
  let u (m x : ℕ) : ℝ := 1 - oddTrapProb b m x - oddRunProb b m x
  have hu_nonneg : ∀ m x, 1 ≤ x → x < b → 0 ≤ u m x := fun m x hx1 hxb => by
    have := (oddProb_bounds hb3 hb_odd m x hx1 hxb).2.2; dsimp [u]; linarith
  have hu_le_one : ∀ m x, 1 ≤ x → x < b → u m x ≤ 1 := fun m x hx1 hxb => by
    have h := oddProb_bounds hb3 hb_odd m x hx1 hxb; dsimp [u]; linarith
  have hu_anti : ∀ m x, 1 ≤ x → x < b → u (m + 1) x ≤ u m x := fun m x hx1 hxb => by
    have h := oddProb_mono hb3 hb_odd m x hx1 hxb; dsimp [u]; linarith
  have hu_anti_le : ∀ {m1 m2 x}, m1 ≤ m2 → 1 ≤ x → x < b → u m2 x ≤ u m1 x := by
    intro m1 m2 x hle hx1 hxb
    induction hle with
    | refl => exact le_refl _
    | step _ ih => exact (hu_anti _ x hx1 hxb).trans ih
  have hu_bfs : ∀ (k d : ℕ) (x : ℕ) (M : ℝ), 0 ≤ M →
      (∀ z, 1 ≤ z → z < b → u k z ≤ M) →
      1 ≤ x → x < b → tagDist (getTag dt x) ≤ d →
      u (k + d + 1) x ≤ (1 - (1 / 2 : ℝ) ^ (d + 1)) * M := by
    intro k d
    induction d with
    | zero =>
      intro x M _ hM_all hx1 hxb hd0
      have htg1 : getTag dt x = 0 ∨ getTag dt x = 1 := by
        rcases h : getTag dt x with _ | _ | q
        · left; rfl
        · right; rfl
        · rw [h] at hd0; simp [tagDist] at hd0
      have hhalf := half_pos_lt hb3 hb_odd hx1 hxb
      have hMh := hM_all (half x) hhalf.1 hhalf.2
      rw [show k + 0 + 1 = k + 1 by omega]
      dsimp only [u, oddTrapProb, oddRunProb] at hMh ⊢
      rcases htg1 with h0 | h1
      · rw [htag0 x hx1 hxb h0]; dsimp only; linarith
      · rw [htag1 x hx1 hxb h1]; dsimp only; linarith
    | succ d ih =>
      intro x M hM hM_all hx1 hxb hle
      by_cases h0 : tagDist (getTag dt x) ≤ d
      · have h1 := ih x M hM hM_all hx1 hxb h0
        have h2 := hu_anti (k + d + 1) x hx1 hxb
        have hpow : (1 / 2 : ℝ) ^ (d + 2) ≤ (1 / 2 : ℝ) ^ (d + 1) := by
          rw [pow_succ]; nlinarith [show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (d + 1) by positivity]
        rw [show k + (d + 1) + 1 = (k + d + 1) + 1 by omega]
        nlinarith
      · have htg2 : 2 ≤ getTag dt x := by
          rcases h : getTag dt x with _ | _ | q
          · rw [h] at h0; simp [tagDist] at h0
          · rw [h] at h0; simp [tagDist] at h0
          · omega
        obtain ⟨y, hy1, hyb, hoy, hdec⟩ := htag2 x hx1 hxb htg2
        have hhalf := half_pos_lt hb3 hb_odd hx1 hxb
        have hu_step : u (k + (d + 1) + 1) x =
            (1 / 2 : ℝ) * u (k + d + 1) (half x) + (1 / 2 : ℝ) * u (k + d + 1) y := by
          rw [show k + (d + 1) + 1 = (k + d + 1) + 1 by omega]
          dsimp only [u, oddTrapProb, oddRunProb, half]
          rw [hoy]; ring
        rw [hu_step]
        have hbound_all : ∀ z, 1 ≤ z → z < b → u (k + d + 1) z ≤ M := fun z hz1 hzb =>
          (hu_anti_le (by omega) hz1 hzb).trans (hM_all z hz1 hzb)
        rcases hdec with hdh | hdy
        · have h1 := ih (half x) M hM hM_all hhalf.1 hhalf.2 (by dsimp only [half]; omega)
          have h2 := hbound_all y hy1 hyb
          rw [pow_succ]; linarith
        · have h1 := hbound_all (half x) hhalf.1 hhalf.2
          have h2 := ih y M hM hM_all hy1 hyb (by omega)
          rw [pow_succ]; linarith
  have hdist_le_14 : ∀ x, tagDist (getTag dt x) ≤ 14 := by
    intro x
    have hlt16 : getTag dt x < 16 := Nat.mod_lt _ (by decide)
    rcases h : getTag dt x with _ | _ | d
    · simp [tagDist]
    · simp [tagDist]
    · simp [tagDist]; omega
  set θ : ℝ := 1 - (1 / 2 : ℝ) ^ 15
  have hθ_nonneg : 0 ≤ θ := by norm_num [θ]
  have hθ_lt1 : θ < 1 := by norm_num [θ]
  have hu_pow : ∀ k x, 1 ≤ x → x < b → u (k * 15) x ≤ θ ^ k := by
    intro k
    induction k with
    | zero => intro x hx1 hxb; simpa using hu_le_one 0 x hx1 hxb
    | succ k ih =>
      intro x hx1 hxb
      rw [show (k + 1) * 15 = k * 15 + 14 + 1 by omega, pow_succ']
      exact hu_bfs (k * 15) 14 x (θ ^ k) (pow_nonneg hθ_nonneg k) ih hx1 hxb (hdist_le_14 x)
  have hsub_tend : Tendsto (fun k => k * 15) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun N => ⟨N, fun k hk => by omega⟩
  have hst_one : ∀ x, 1 ≤ x → x < b → oddTrapStateMass b x + oddRunStateMass b x = 1 := by
    intro x hx1 hxb
    have h1 : Tendsto (fun k => u (k * 15) x) atTop (𝓝 (1 - oddTrapStateMass b x - oddRunStateMass b x)) :=
      (tendsto_const_nhds.sub ((oddTrapProb_tendsto hb3 hb_odd hx1 hxb).comp hsub_tend)).sub
        ((oddRunProb_tendsto hb3 hb_odd hx1 hxb).comp hsub_tend)
    have h0 : Tendsto (fun k => u (k * 15) x) atTop (𝓝 0) :=
      squeeze_zero (fun k => hu_nonneg (k * 15) x hx1 hxb) (fun k => hu_pow k x hx1 hxb)
        (tendsto_pow_atTop_nhds_zero_of_lt_one hθ_nonneg hθ_lt1)
    have heq := tendsto_nhds_unique h1 h0
    linarith
  have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  unfold oddTrapMass oddRunMass
  rw [← add_div, add_assoc, ← Finset.sum_add_distrib]
  have hsum_eq : ∑ x ∈ Finset.Ico 1 b, (oddTrapStateMass b x + oddRunStateMass b x) = (b : ℝ) - 1 := by
    have hcard : (Finset.Ico 1 b).card = b - 1 := by simp
    calc ∑ x ∈ Finset.Ico 1 b, (oddTrapStateMass b x + oddRunStateMass b x)
        = ∑ _x ∈ Finset.Ico 1 b, (1 : ℝ) :=
          Finset.sum_congr rfl fun x hx => hst_one x (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2
      _ = (b : ℝ) - 1 := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one, Nat.cast_sub (by omega), Nat.cast_one]
  rw [hsum_eq]
  have : 1 + ((b : ℝ) - 1) = (b : ℝ) := by ring
  rw [this, div_self (ne_of_gt hbpos)]

/-- Soundness of `checkBaseCert`: any odd base `b ∈ [3, 1999]` passing `checkBaseCert`
    establishes full absorption `oddTrapMass b + oddRunMass b = 1` for the canonical
    Section 6.2 absorption masses, exact rationality, and exact natural densities
    `d(Z_b) = d(R_b) = oddTrapMass b` and `d(DivSet b) = oddRunMass b`, with
    `oddTrapMass b = 1, oddRunMass b = 0` when `isSplit = false`, and
    `0 < oddRunMass b` when `isSplit = true`. -/
theorem thm_odd_base_certified_densities {b : ℕ} {isSplit : Bool}
    {seeds : List (ℕ × ℕ × ℕ)} {dt : QT}
    (hcert : checkBaseCert b isSplit seeds dt = true) :
    0 < oddTrapMass b ∧
    0 ≤ oddRunMass b ∧
    oddTrapMass b + oddRunMass b = 1 ∧
    (∃ qτ qρ : ℚ, (qτ : ℝ) = oddTrapMass b ∧ (qρ : ℝ) = oddRunMass b ∧ qτ + qρ = 1) ∧
    (isSplit = false → oddTrapMass b = 1 ∧ oddRunMass b = 0) ∧
    (isSplit = true → 0 < oddRunMass b) ∧
    Tendsto (countFrac (ZSet b)) atTop (𝓝 (oddTrapMass b)) ∧
    Tendsto (countFrac (RSet b)) atTop (𝓝 (oddTrapMass b)) ∧
    Tendsto (countFrac (DivSet b)) atTop (𝓝 (oddRunMass b)) := by
  unfold checkBaseCert at hcert
  simp only [Bool.and_eq_true, Nat.ble_eq] at hcert
  obtain ⟨⟨⟨⟨⟨hb3, hb1999⟩, hbo⟩, hsp⟩, hseeds⟩, hrng⟩ := hcert
  have hb_odd : b % 2 = 1 := Nat.eq_of_beq_eq_true hbo
  have hb_lt : b < 2048 := by omega
  have hseed_ok := checkSeeds_sound hb3 hb_lt hb_odd hseeds
  have hres_all : ∀ x, 1 ≤ x → x < b → checkRes b ((b + 1) / 2) isSplit seeds dt x = true :=
    fun x hx1 hxb => checkRange_sound b ((b + 1) / 2) isSplit seeds dt 11 0 hrng x (by omega) (by omega) hx1 hxb
  have htag1_step := tag1_step_sound hb3 hb_lt hb_odd hseed_ok hres_all
  have htag1_esc := tag1_escape_sound hb3 hb_lt hb_odd hseed_ok hres_all
  have htag0_trap := tag0_trap_stretch_sound hb3 hb_lt hb_odd hres_all
  have htag_zero := tag_zero_sound hb3 hb_lt hb_odd hres_all
  have hout0 : ∀ x, 1 ≤ x → x < b → getTag dt x = 0 → oddStretchOutcome b x = .trap :=
    fun x hx1 hxb h0 => oddStretchOutcome_eq_trap_iff.mpr (htag0_trap x hx1 hxb h0)
  have hout1 : ∀ x, 1 ≤ x → x < b → getTag dt x = 1 → oddStretchOutcome b x = .escape :=
    fun x hx1 hxb h1 => (oddStretchOutcome_eq_escape_iff hb3).mpr (htag1_esc x hx1 hxb h1)
  have hout2 : ∀ x, 1 ≤ x → x < b → 2 ≤ getTag dt x →
      ∃ y, 1 ≤ y ∧ y < b ∧ oddStretchOutcome b x = .toState y ∧
        (tagDist (getTag dt ((x * ((b + 1) / 2)) % b)) < tagDist (getTag dt x) ∨
         tagDist (getTag dt y) < tagDist (getTag dt x)) := by
    intro x hx1 hxb h2
    obtain ⟨y, hz, hdec⟩ := htag_zero x hx1 hxb h2
    exact ⟨y, hz.1, hz.2.1, (oddStretchOutcome_eq_toState_iff hb3).mpr hz, hdec⟩
  have hfull : oddTrapMass b + oddRunMass b = 1 :=
    cert_full_absorption hb3 hb_odd hout0 hout1 hout2
  have huniv := thm_odd_absorption_universal hb3 hb_odd
  obtain ⟨htZ, htR, htD, hrat⟩ := huniv.2.2.2.2.2 hfull
  have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hτ_pos : 0 < oddTrapMass b := lt_of_lt_of_le (by positivity) huniv.1
  refine ⟨hτ_pos, huniv.2.1, hfull, hrat, ?_, ?_, htZ, htR, htD⟩
  · intro hsf
    have hno_esc : ∀ x, 1 ≤ x → x < b → oddStretchOutcome b x ≠ .escape := by
      intro x hx1 hxb
      rcases htg : getTag dt x with _ | _ | d
      · rw [hout0 x hx1 hxb htg]; decide
      · have hst := (htag1_step x hx1 hxb htg).1
        rw [hsf] at hst; exact absurd hst (by decide)
      · obtain ⟨y, _, _, hoy, _⟩ := hout2 x hx1 hxb (by omega)
        rw [hoy]; intro h; cases h
    have hrun0 : ∀ m x, 1 ≤ x → x < b → oddRunProb b m x = 0 := by
      intro m
      induction m with
      | zero => intro x _ _; rfl
      | succ m ih =>
        intro x hx1 hxb
        have hhalf := half_pos_lt hb3 hb_odd hx1 hxb
        simp only [oddRunProb, ih _ hhalf.1 hhalf.2, mul_zero, zero_add]
        cases ho : oddStretchOutcome b x with
        | trap => simp
        | unresolved => simp
        | escape => exact absurd ho (hno_esc x hx1 hxb)
        | toState y =>
          have hy := (oddStretchOutcome_eq_toState_iff hb3).mp ho
          dsimp only; rw [ih y hy.1 hy.2.1, mul_zero]
    have hρ0 : oddRunMass b = 0 := by
      unfold oddRunMass
      have hsum0 : ∑ x ∈ Finset.Ico 1 b, oddRunStateMass b x = 0 :=
        Finset.sum_eq_zero fun x hx => by
          have hx' := Finset.mem_Ico.mp hx
          have hfn : (fun m => oddRunProb b m x) = fun _ => (0 : ℝ) := funext fun m => hrun0 m x hx'.1 hx'.2
          exact tendsto_nhds_unique (oddRunProb_tendsto hb3 hb_odd hx'.1 hx'.2)
            (by rw [hfn]; exact tendsto_const_nhds)
      rw [hsum0, zero_div]
    exact ⟨by linarith, hρ0⟩
  · intro hst
    cases seeds with
    | nil => simp [hst] at hsp
    | cons s0 rest =>
      have hs0 := hseed_ok s0 (List.mem_cons_self ..)
      have ho_s0 : oddStretchOutcome b s0.1 = .escape :=
        (oddStretchOutcome_eq_escape_iff hb3).mpr hs0.2.2
      have hprob1 : oddRunProb b 1 s0.1 = (1 / 2 : ℝ) := by
        simp [oddRunProb, ho_s0]
      have hst_ge : (1 / 2 : ℝ) ≤ oddRunStateMass b s0.1 := by
        have hbdd : BddAbove (Set.range fun m => oddRunProb b m s0.1) := ⟨1, by
          rintro _ ⟨m, rfl⟩
          have hb := oddProb_bounds hb3 hb_odd m s0.1 hs0.1 hs0.2.1; linarith⟩
        rw [← hprob1]
        exact le_ciSup hbdd 1
      have hsum_ge : (1 / 2 : ℝ) ≤ ∑ x ∈ Finset.Ico 1 b, oddRunStateMass b x := by
        have hsingle : oddRunStateMass b s0.1 ≤ ∑ x ∈ Finset.Ico 1 b, oddRunStateMass b x :=
          Finset.single_le_sum
            (fun x hx => (oddStateMass_bounds hb3 hb_odd (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2).2.1)
            (Finset.mem_Ico.mpr ⟨hs0.1, hs0.2.1⟩)
        linarith
      unfold oddRunMass
      exact div_pos (by linarith) hbpos

/-! ## Section 6: Theorem 13 (`thm:odd-survey`) & Table `tab:odd` Sanity Corollary -/

/-- All 999 odd bases `b` with `3 ≤ b ≤ 1,999`. -/
def allOddBases1999 : Finset ℕ := (Finset.Icc 3 1999).filter (fun b => b % 2 = 1)

/-- The 27 odd bases `3 ≤ b ≤ 1,999` certified trap-only (`oddTrapMass b = 1, oddRunMass b = 0`). -/
def trapOnlyBases : Finset ℕ := trapOnlyList.toFinset

/-- The 878 odd bases `3 ≤ b ≤ 1,999` certified split (`0 < oddTrapMass b, 0 < oddRunMass b,
    oddTrapMass b + oddRunMass b = 1`). -/
def splitBases : Finset ℕ := splitList.toFinset

/-- All 905 resolved odd bases `3 ≤ b ≤ 1,999` (`trapOnlyBases ∪ splitBases`). -/
def resolvedOddBases : Finset ℕ := trapOnlyBases ∪ splitBases

private lemma allOddBases1999_eq_image :
    allOddBases1999 = (Finset.range 999).image (fun k => 2 * k + 3) := by
  ext b
  simp only [allOddBases1999, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨h3, h1999⟩, hodd⟩
    exact ⟨(b - 3) / 2, by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨by omega, by omega⟩, by omega⟩

/-- There are exactly 999 odd bases `b` with `3 ≤ b ≤ 1,999`. -/
theorem allOddBases1999_card : allOddBases1999.card = 999 := by
  rw [allOddBases1999_eq_image,
      Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]

/-- **Theorem 13 (`thm:odd-survey`)**:
    1. For EVERY odd base `b ≥ 3`, finite-cylinder absorption produces canonical Markov
       masses `τ_b = oddTrapMass b` (for `Z_b`) and `ρ_b = oddRunMass b` (for `E_b`)
       satisfying `1/b ≤ τ_b`, `0 ≤ ρ_b`, `τ_b + ρ_b ≤ 1` and lower-density bounds for
       `Z_b` and `E_b`; whenever `τ_b + ρ_b = 1`, all three natural densities exist with
       `d(Z_b) = d(R_b) = τ_b` and `d(E_b) = ρ_b` as exact rationals.
    2. Across all 999 odd bases `3 ≤ b ≤ 1,999`, the pure-kernel absorption certificate
       establishes `τ_b + ρ_b = 1` in 905 bases: 27 trap-only (`τ_b = 1, ρ_b = 0`) and
       878 split (`0 < τ_b, 0 < ρ_b`, both exact rationals). -/
theorem thm_odd_survey :
    (∀ b : ℕ, 3 ≤ b → b % 2 = 1 →
      (1 : ℝ) / (b : ℝ) ≤ oddTrapMass b ∧
      0 ≤ oddRunMass b ∧
      oddTrapMass b + oddRunMass b ≤ 1 ∧
      (∀ ε > 0, ∀ᶠ N in atTop, oddTrapMass b - ε ≤ countFrac (ZSet b) N) ∧
      (∀ ε > 0, ∀ᶠ N in atTop, oddRunMass b - ε ≤ countFrac (DivSet b) N) ∧
      (oddTrapMass b + oddRunMass b = 1 →
        Tendsto (countFrac (ZSet b)) atTop (𝓝 (oddTrapMass b)) ∧
        Tendsto (countFrac (RSet b)) atTop (𝓝 (oddTrapMass b)) ∧
        Tendsto (countFrac (DivSet b)) atTop (𝓝 (oddRunMass b)) ∧
        (∃ qτ qρ : ℚ, (qτ : ℝ) = oddTrapMass b ∧ (qρ : ℝ) = oddRunMass b ∧ qτ + qρ = 1))) ∧
    allOddBases1999.card = 999 ∧
    trapOnlyBases ⊆ allOddBases1999 ∧
    splitBases ⊆ allOddBases1999 ∧
    Disjoint trapOnlyBases splitBases ∧
    trapOnlyBases.card = 27 ∧
    splitBases.card = 878 ∧
    resolvedOddBases.card = 905 ∧
    (∀ b ∈ trapOnlyBases,
      oddTrapMass b = 1 ∧ oddRunMass b = 0 ∧
      oddTrapMass b + oddRunMass b = 1 ∧
      Tendsto (countFrac (ZSet b)) atTop (𝓝 (1 : ℝ)) ∧
      Tendsto (countFrac (RSet b)) atTop (𝓝 (1 : ℝ)) ∧
      Tendsto (countFrac (DivSet b)) atTop (𝓝 (0 : ℝ))) ∧
    (∀ b ∈ splitBases,
      0 < oddTrapMass b ∧ 0 < oddRunMass b ∧
      oddTrapMass b + oddRunMass b = 1 ∧
      (∃ qτ qρ : ℚ, (qτ : ℝ) = oddTrapMass b ∧ (qρ : ℝ) = oddRunMass b ∧ qτ + qρ = 1) ∧
      Tendsto (countFrac (ZSet b)) atTop (𝓝 (oddTrapMass b)) ∧
      Tendsto (countFrac (RSet b)) atTop (𝓝 (oddTrapMass b)) ∧
      Tendsto (countFrac (DivSet b)) atTop (𝓝 (oddRunMass b))) := by
  have htrap_nodup : trapOnlyList.Nodup := trapOnlyList_pairwise_lt.imp (fun h => ne_of_lt h)
  have hsplit_nodup : splitList.Nodup := splitList_pairwise_lt.imp (fun h => ne_of_lt h)
  have htrap_card : trapOnlyBases.card = 27 := by
    rw [trapOnlyBases, List.toFinset_card_of_nodup htrap_nodup, trapOnlyList_length]
  have hsplit_card : splitBases.card = 878 := by
    rw [splitBases, List.toFinset_card_of_nodup hsplit_nodup, splitList_length]
  have hdisj : Disjoint trapOnlyBases splitBases := by
    rw [Finset.disjoint_left]
    intro x hxT hxS
    exact trapOnly_split_disjoint x (List.mem_toFinset.mp hxT) (List.mem_toFinset.mp hxS)
  have hres_card : resolvedOddBases.card = 905 := by
    rw [resolvedOddBases, Finset.card_union_of_disjoint hdisj, htrap_card, hsplit_card]
  have htrap_sub : trapOnlyBases ⊆ allOddBases1999 := by
    intro b hb
    have hr := trapOnlyList_in_range b (List.mem_toFinset.mp hb)
    simp only [allOddBases1999, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hr.1, hr.2.1⟩, hr.2.2⟩
  have hsplit_sub : splitBases ⊆ allOddBases1999 := by
    intro b hb
    have hr := splitList_in_range b (List.mem_toFinset.mp hb)
    simp only [allOddBases1999, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hr.1, hr.2.1⟩, hr.2.2⟩
  refine ⟨fun b hb3 hb_odd => thm_odd_absorption_universal hb3 hb_odd,
    allOddBases1999_card, htrap_sub, hsplit_sub, hdisj, htrap_card, hsplit_card, hres_card, ?_, ?_⟩
  · intro b hb
    obtain ⟨seeds, dt, hcert⟩ := trapOnly_cert_all b (List.mem_toFinset.mp hb)
    obtain ⟨_, _, hsum, _, htr, _, htZ, htR, htD⟩ := thm_odd_base_certified_densities hcert
    obtain ⟨hτ1, hρ0⟩ := htr rfl
    rw [hτ1] at htZ htR
    rw [hρ0] at htD
    exact ⟨hτ1, hρ0, hsum, htZ, htR, htD⟩
  · intro b hb
    obtain ⟨seeds, dt, hcert⟩ := split_cert_all b (List.mem_toFinset.mp hb)
    obtain ⟨hτ_pos, _, hsum, hrat, _, hsp, htZ, htR, htD⟩ := thm_odd_base_certified_densities hcert
    exact ⟨hτ_pos, hsp rfl, hsum, hrat, htZ, htR, htD⟩

/-- Unified 905-base corollary of `thm_odd_survey`: every `b ∈ resolvedOddBases`
    has exact rational canonical masses `oddTrapMass b`, `oddRunMass b` summing to `1`
    and exact natural densities `d(Z_b) = d(R_b) = oddTrapMass b` and `d(E_b) = oddRunMass b`. -/
theorem thm_odd_survey_resolved :
    ∀ b ∈ resolvedOddBases,
      0 < oddTrapMass b ∧ 0 ≤ oddRunMass b ∧
      oddTrapMass b + oddRunMass b = 1 ∧
      (∃ qτ qρ : ℚ, (qτ : ℝ) = oddTrapMass b ∧ (qρ : ℝ) = oddRunMass b ∧ qτ + qρ = 1) ∧
      Tendsto (countFrac (ZSet b)) atTop (𝓝 (oddTrapMass b)) ∧
      Tendsto (countFrac (RSet b)) atTop (𝓝 (oddTrapMass b)) ∧
      Tendsto (countFrac (DivSet b)) atTop (𝓝 (oddRunMass b)) := by
  have h := thm_odd_survey
  intro b hb
  rcases Finset.mem_union.mp hb with hT | hS
  · obtain ⟨hτ1, hρ0, hsum, htZ, htR, htD⟩ := h.2.2.2.2.2.2.2.2.1 b hT
    refine ⟨by linarith, by linarith, hsum, ⟨1, 0, by simp [hτ1], by simp [hρ0], by norm_num⟩, ?_, ?_, ?_⟩
    · rwa [hτ1]
    · rwa [hτ1]
    · rwa [hρ0]
  · obtain ⟨hτ, hρ, hsum, hrat, htZ, htR, htD⟩ := h.2.2.2.2.2.2.2.2.2 b hS
    exact ⟨hτ, le_of_lt hρ, hsum, hrat, htZ, htR, htD⟩

private lemma oddStretchOutcome_of_tracePure_trap {b x k : ℕ}
    (hb3 : 3 ≤ b) (hb_lt : b < 2048) (hb_odd : b % 2 = 1) (hx1 : 1 ≤ x) (hxb : x < b)
    (h : tracePureLoop b ((b + 1) / 2) k x 1 2 = 1) :
    oddStretchOutcome b x = .trap := by
  have htr := tracePureLoop_sound hb3 hb_lt hb_odd k ⟨x, 1, 1⟩ hx1 hxb (le_refl 1) (by norm_num)
  rw [show (2 : ℕ) ^ 1 = 2 by norm_num, h] at htr
  exact oddStretchOutcome_eq_trap_iff.mpr htr

private lemma oddStretchOutcome_of_tracePure_toState {b x y k : ℕ}
    (hb3 : 3 ≤ b) (hb_lt : b < 2048) (hb_odd : b % 2 = 1) (hx1 : 1 ≤ x) (hxb : x < b)
    (h : tracePureLoop b ((b + 1) / 2) k x 1 2 = y + 3) :
    oddStretchOutcome b x = .toState y := by
  have htr := tracePureLoop_sound hb3 hb_lt hb_odd k ⟨x, 1, 1⟩ hx1 hxb (le_refl 1) (by norm_num)
  rw [show (2 : ℕ) ^ 1 = 2 by norm_num, h] at htr
  exact (oddStretchOutcome_eq_toState_iff hb3).mpr htr

private lemma oddStretchOutcome_of_checkSeed {b x kStart p : ℕ}
    (hb3 : 3 ≤ b) (hb_lt : b < 2048) (hb_odd : b % 2 = 1)
    (h : checkSeed b ((b + 1) / 2) (x, kStart, p) = true) :
    oddStretchOutcome b x = .escape :=
  (oddStretchOutcome_eq_escape_iff hb3).mpr (checkSeed_sound hb3 hb_lt hb_odd h).2.2

/-- Concrete Table `tab:odd` sanity corollary: exact values of `oddTrapMass b` (`τ_b`) and
    `oddRunMass b` (`ρ_b`) for `b = 3, 5, 7, 13` (including the unresolved base `b = 7` with
    residual `6/7`, and the split base `b = 13` with `τ_13 = 13,210/16,991` and
    `ρ_13 = 3,781/16,991` promoted to exact natural densities directly by `thm_odd_survey`
    and `oddTrapStateMass_unique_of_full`). -/
theorem thm_odd_table_examples :
    (oddTrapMass 3 = 1 / 3 ∧ oddRunMass 3 = 2 / 3) ∧
    (oddTrapMass 5 = 1 ∧ oddRunMass 5 = 0) ∧
    (oddTrapMass 7 = 1 / 7 ∧ oddRunMass 7 = 0) ∧
    (oddTrapMass 13 = 13210 / 16991 ∧ oddRunMass 13 = 3781 / 16991 ∧
      Tendsto (countFrac (ZSet 13)) atTop (𝓝 ((13210 : ℝ) / 16991)) ∧
      Tendsto (countFrac (RSet 13)) atTop (𝓝 ((13210 : ℝ) / 16991)) ∧
      Tendsto (countFrac (DivSet 13)) atTop (𝓝 ((3781 : ℝ) / 16991))) := by
  -- b = 3: x=1 -> toState 1, x=2 -> escape; full absorption from cert_3
  have hb3_res : oddTrapMass 3 = 1 / 3 ∧ oddRunMass 3 = 2 / 3 := by
    obtain ⟨seeds, dt, hcert⟩ := cert_3
    have hfull := (thm_odd_base_certified_densities hcert).2.2.1
    have ho1 : oddStretchOutcome 3 1 = .toState 1 :=
      oddStretchOutcome_of_tracePure_toState (k := 1) (by omega) (by omega) rfl (by omega) (by omega) rfl
    have ho2 : oddStretchOutcome 3 2 = .escape :=
      oddStretchOutcome_of_checkSeed (kStart := 0) (p := 1) (by omega) (by omega) rfl rfl
    have huniq := (oddTrapStateMass_unique_of_full (b := 3) (by omega) rfl hfull (v := fun _ => (0 : ℝ))
      (fun x hx1 hxb => by
        interval_cases x
        · rw [ho1]; norm_num
        · rw [ho2]; norm_num)).2
    have hτ : oddTrapMass 3 = 1 / 3 := by
      rw [← huniq]; norm_num
    exact ⟨hτ, by linarith⟩
  -- b = 5: certified trap-only from cert_5
  have hb5_res : oddTrapMass 5 = 1 ∧ oddRunMass 5 = 0 := by
    obtain ⟨seeds, dt, hcert⟩ := cert_5
    exact (thm_odd_base_certified_densities hcert).2.2.2.2.1 rfl
  -- b = 7: every nonzero state returns to a zero-bit state -> τ_7 = 1/7, ρ_7 = 0
  have hb7_res : oddTrapMass 7 = 1 / 7 ∧ oddRunMass 7 = 0 := by
    have hall_to : ∀ x, 1 ≤ x → x < 7 → ∃ y, oddStretchOutcome 7 x = .toState y := by
      intro x hx1 hxb
      interval_cases x
      · exact ⟨1, oddStretchOutcome_of_tracePure_toState (k := 1) (by omega) (by omega) rfl (by omega) (by omega) rfl⟩
      · exact ⟨3, oddStretchOutcome_of_tracePure_toState (k := 1) (by omega) (by omega) rfl (by omega) (by omega) rfl⟩
      · exact ⟨5, oddStretchOutcome_of_tracePure_toState (k := 1) (by omega) (by omega) rfl (by omega) (by omega) rfl⟩
      · exact ⟨3, oddStretchOutcome_of_tracePure_toState (k := 1) (by omega) (by omega) rfl (by omega) (by omega) rfl⟩
      · exact ⟨6, oddStretchOutcome_of_tracePure_toState (k := 1) (by omega) (by omega) rfl (by omega) (by omega) rfl⟩
      · exact ⟨5, oddStretchOutcome_of_tracePure_toState (k := 1) (by omega) (by omega) rfl (by omega) (by omega) rfl⟩
    have hprob0 : ∀ m x, 1 ≤ x → x < 7 → oddTrapProb 7 m x = 0 ∧ oddRunProb 7 m x = 0 := by
      intro m
      induction m with
      | zero => intro x _ _; exact ⟨rfl, rfl⟩
      | succ m ih =>
        intro x hx1 hxb
        have hhalf := half_pos_lt (b := 7) (by omega) rfl hx1 hxb
        obtain ⟨y, hoy⟩ := hall_to x hx1 hxb
        have hy := (oddStretchOutcome_eq_toState_iff (by omega)).mp hoy
        simp only [oddTrapProb, oddRunProb, hoy, (ih _ hhalf.1 hhalf.2).1, (ih _ hhalf.1 hhalf.2).2,
          (ih y hy.1 hy.2.1).1, (ih y hy.1 hy.2.1).2]
        norm_num
    have hst0 : ∀ x, 1 ≤ x → x < 7 → oddTrapStateMass 7 x = 0 ∧ oddRunStateMass 7 x = 0 := by
      intro x hx1 hxb
      refine ⟨tendsto_nhds_unique (oddTrapProb_tendsto (b := 7) (by omega) rfl hx1 hxb)
          (by rw [show (fun m => oddTrapProb 7 m x) = fun _ => (0 : ℝ) from
                funext fun m => (hprob0 m x hx1 hxb).1]; exact tendsto_const_nhds),
        tendsto_nhds_unique (oddRunProb_tendsto (b := 7) (by omega) rfl hx1 hxb)
          (by rw [show (fun m => oddRunProb 7 m x) = fun _ => (0 : ℝ) from
                funext fun m => (hprob0 m x hx1 hxb).2]; exact tendsto_const_nhds)⟩
    have hsumT : ∑ x ∈ Finset.Ico 1 7, oddTrapStateMass 7 x = 0 :=
      Finset.sum_eq_zero fun x hx => (hst0 x (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2).1
    have hsumE : ∑ x ∈ Finset.Ico 1 7, oddRunStateMass 7 x = 0 :=
      Finset.sum_eq_zero fun x hx => (hst0 x (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2).2
    unfold oddTrapMass oddRunMass
    rw [hsumT, hsumE]; norm_num
  -- b = 13: exact Table 1 rational solution τ_13 = 13210/16991, ρ_13 = 3781/16991
  have hb13_res : oddTrapMass 13 = 13210 / 16991 ∧ oddRunMass 13 = 3781 / 16991 ∧
      Tendsto (countFrac (ZSet 13)) atTop (𝓝 ((13210 : ℝ) / 16991)) ∧
      Tendsto (countFrac (RSet 13)) atTop (𝓝 ((13210 : ℝ) / 16991)) ∧
      Tendsto (countFrac (DivSet 13)) atTop (𝓝 ((3781 : ℝ) / 16991)) := by
    obtain ⟨seeds, dt, hcert⟩ := cert_13
    obtain ⟨_, _, hfull, _, _, _, htZ, htR, htD⟩ := thm_odd_base_certified_densities hcert
    have ho1 : oddStretchOutcome 13 1 = .toState 1 :=
      oddStretchOutcome_of_tracePure_toState (k := 1) (by omega) (by omega) rfl (by omega) (by omega) rfl
    have ho2 : oddStretchOutcome 13 2 = .trap :=
      oddStretchOutcome_of_tracePure_trap (k := 1) (by omega) (by omega) rfl (by omega) (by omega) rfl
    have ho3 : oddStretchOutcome 13 3 = .toState 5 :=
      oddStretchOutcome_of_tracePure_toState (k := 1) (by omega) (by omega) rfl (by omega) (by omega) rfl
    have ho4 : oddStretchOutcome 13 4 = .escape :=
      oddStretchOutcome_of_checkSeed (kStart := 0) (p := 1) (by omega) (by omega) rfl rfl
    have ho5 : oddStretchOutcome 13 5 = .trap :=
      oddStretchOutcome_of_tracePure_trap (k := 1) (by omega) (by omega) rfl (by omega) (by omega) rfl
    have ho6 : oddStretchOutcome 13 6 = .toState 2 :=
      oddStretchOutcome_of_tracePure_toState (k := 1) (by omega) (by omega) rfl (by omega) (by omega) rfl
    have ho7 : oddStretchOutcome 13 7 = .toState 12 :=
      oddStretchOutcome_of_tracePure_toState (k := 1) (by omega) (by omega) rfl (by omega) (by omega) rfl
    have ho8 : oddStretchOutcome 13 8 = .trap :=
      oddStretchOutcome_of_tracePure_trap (k := 1) (by omega) (by omega) rfl (by omega) (by omega) rfl
    have ho9 : oddStretchOutcome 13 9 = .toState 2 :=
      oddStretchOutcome_of_tracePure_toState (k := 1) (by omega) (by omega) rfl (by omega) (by omega) rfl
    have ho10 : oddStretchOutcome 13 10 = .escape :=
      oddStretchOutcome_of_checkSeed (kStart := 0) (p := 1) (by omega) (by omega) rfl rfl
    have ho11 : oddStretchOutcome 13 11 = .toState 9 :=
      oddStretchOutcome_of_tracePure_toState (k := 1) (by omega) (by omega) rfl (by omega) (by omega) rfl
    have ho12 : oddStretchOutcome 13 12 = .trap :=
      oddStretchOutcome_of_tracePure_trap (k := 1) (by omega) (by omega) rfl (by omega) (by omega) rfl
    let v13 : ℕ → ℝ
      | 1 => 905 / 1307
      | 2 => 1106 / 1307
      | 3 => 1076 / 1307
      | 4 => 553 / 1307
      | 5 => 1222 / 1307
      | 6 => 1091 / 1307
      | 7 => 905 / 1307
      | 8 => 930 / 1307
      | 9 => 1137 / 1307
      | 10 => 611 / 1307
      | 11 => 1168 / 1307
      | 12 => 1199 / 1307
      | _ => 0
    have huniq := (oddTrapStateMass_unique_of_full (b := 13) (by omega) rfl hfull (v := v13)
      (fun x hx1 hxb => by
        interval_cases x
        · rw [ho1]; norm_num [v13]
        · rw [ho2]; norm_num [v13]
        · rw [ho3]; norm_num [v13]
        · rw [ho4]; norm_num [v13]
        · rw [ho5]; norm_num [v13]
        · rw [ho6]; norm_num [v13]
        · rw [ho7]; norm_num [v13]
        · rw [ho8]; norm_num [v13]
        · rw [ho9]; norm_num [v13]
        · rw [ho10]; norm_num [v13]
        · rw [ho11]; norm_num [v13]
        · rw [ho12]; norm_num [v13])).2
    have hτ : oddTrapMass 13 = 13210 / 16991 := by
      rw [← huniq]
      have hico : Finset.Ico 1 13 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by decide
      rw [hico]
      norm_num [v13]
    have hρ : oddRunMass 13 = 3781 / 16991 := by linarith
    rw [hτ] at htZ htR
    rw [hρ] at htD
    exact ⟨hτ, hρ, htZ, htR, htD⟩
  exact ⟨hb3_res, hb5_res, hb7_res, hb13_res⟩

end Ouroboros
