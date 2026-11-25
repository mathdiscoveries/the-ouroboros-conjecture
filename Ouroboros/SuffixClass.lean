module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic
public import Ouroboros.Defs
public import Ouroboros.BasinOne

@[expose] public section

/-!
# Section 7: Congruence-Class Completions (`thm:suffix-class`, Theorem 29)

Formalizes Theorem 29 (`thm:suffix-class`) of the Ouroboros paper:
1. **Basin of 5 (`thm_suffix_class_B5`)**: Every congruence class `a mod m` (`m ≥ 1`) contains
   infinitely many members of `B_5` (`InBasin5`).
2. **Basin of 1 (`thm_suffix_class_B1_necessity`, `thm_suffix_class_B1_sufficiency`)**: Putting
   `h = padicValNat 2 m - 1` (i.e. `max(0, v_2(m) - 1)`), `M = 30 * 2^h`, and `p = gcd(m, M)`,
   the congruence class `a mod m` contains infinitely many members of `B_1` (`InBasin1`) if and
   only if some `0 ≤ x < M` satisfies `x ≡ a (mod p)` and
   `T^[h] x % 30 ∈ {0, 1, 2, 4, 8, 15, 16, 17}`; if no such `x` exists, the congruence class
   contains NO member of `B_1`.
3. **Combined Theorem 29 (`thm_suffix_class`)** packaging the `B_5` infinitude and `B_1`
   dichotomy (necessity and sufficiency) together.
-/

namespace Ouroboros

/-! ## The 30-state halving automaton and backward closure of `S` -/

/-- The 8 live residues modulo `30` that can reach `1 mod 30` under the shortcut graph. -/
def liveMod30 : Finset ℕ := {0, 1, 2, 4, 8, 15, 16, 17}

/-- One step of the 30-state shortcut automaton: `T(r)` (`s = false`) or `T(r) + 15` (`s = true`). -/
def step30 (r : Fin 30) (s : Bool) : Fin 30 :=
  ⟨(T r.val + if s then 15 else 0) % 30, Nat.mod_lt _ (by omega)⟩

/-- Iterate `step30` along a list of choice bits. -/
def run30 : Fin 30 → List Bool → Fin 30
  | r, [] => r
  | r, s :: ls => run30 (step30 r s) ls

lemma T_mod_30_eq (n : ℕ) :
    T n % 30 = (step30 ⟨n % 30, Nat.mod_lt n (by omega)⟩ (decide ((n / 30) % 2 = 1))).val := by
  set r := n % 30 with hr_def
  set q := n / 30
  have hdiv : 30 * q + r = n := Nat.div_add_mod n 30
  simp only [step30]
  rw [← hr_def]
  by_cases hev : n % 2 = 0
  · have hrev : r % 2 = 0 := by omega
    have hTn : T n = 15 * q + T r := by
      simp only [T, hev, hrev, ↓reduceIte]; omega
    rw [hTn]
    by_cases hq : q % 2 = 1
    · simp only [hq, decide_true, ↓reduceIte]; omega
    · have hq0 : q % 2 = 0 := by omega
      simp only [show ¬ q % 2 = 1 by omega, decide_false, Bool.false_eq_true, ↓reduceIte]; omega
  · have hrodd : r % 2 = 1 := by omega
    have hdr_eq : d n = d r := by unfold d; omega
    have hdr_odd : d r % 2 = 1 := by unfold d; omega
    have hTn : T n = 15 * (d r * q) + T r := by
      have h1 : n % 2 ≠ 0 := hev
      have h2 : r % 2 ≠ 0 := by omega
      simp only [T, h1, h2, ↓reduceIte, hdr_eq]
      have hmul : d r * n + 1 = 2 * (15 * (d r * q)) + (d r * r + 1) := by
        rw [← hdiv]; ring
      have hev_rr : (d r * r + 1) % 2 = 0 := by
        rw [Nat.add_mod, Nat.mul_mod, hdr_odd, hrodd]
      omega
    rw [hTn]
    have hpar : (d r * q) % 2 = q % 2 := by rw [Nat.mul_mod, hdr_odd, one_mul, Nat.mod_mod]
    by_cases hq : q % 2 = 1
    · have h1 : (d r * q) % 2 = 1 := hpar.trans hq
      simp only [hq, decide_true, ↓reduceIte]; omega
    · have h0 : (d r * q) % 2 = 0 := by omega
      simp only [show ¬ q % 2 = 1 by omega, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

private lemma liveMod30_backward_step :
    ∀ r : Fin 30, ∀ s : Bool, (step30 r s).val ∈ liveMod30 → r.val ∈ liveMod30 := by
  decide

lemma liveMod30_backward_iter (k n : ℕ) (h : T^[k] n % 30 ∈ liveMod30) :
    n % 30 ∈ liveMod30 := by
  induction k generalizing n with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply] at h
    have hTn : T n % 30 ∈ liveMod30 := ih (T n) h
    rw [T_mod_30_eq] at hTn
    exact liveMod30_backward_step ⟨n % 30, Nat.mod_lt n (by omega)⟩ _ hTn

/-- Explicit paths of length `≤ 5` from every live residue in `liveMod30` to `1 mod 30`. -/
private def pathTo1 (r : Fin 30) : List Bool :=
  match r.val with
  | 1 => []
  | 2 => [false]
  | 4 => [false, false]
  | 8 => [false, false, false]
  | 15 => [false, false, false, false]
  | 16 => [false, false, false, false]
  | 0 => [true, false, false, false, false]
  | 17 => [true, false, false, false, false]
  | _ => []

private lemma pathTo1_spec :
    ∀ r : Fin 30, r.val ∈ liveMod30 → (run30 r (pathTo1 r)).val = 1 := by
  decide

/-- All boolean lists of length `≤ 4` (used to discharge 30-state reachability to `{1, 11, 21}`). -/
private def boolLists : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 =>
    let prev := boolLists k
    prev ++ prev.map (false :: ·) ++ prev.map (true :: ·)

private lemma all_reach_digit1_bool :
    ∀ r : Fin 30, (boolLists 4).any (fun l => (run30 r l).val % 10 == 1) = true := by
  decide

lemma all_reach_digit1_30 (r : Fin 30) :
    ∃ l : List Bool, (run30 r l).val % 10 = 1 := by
  have h := List.any_eq_true.mp (all_reach_digit1_bool r)
  rcases h with ⟨l, _, hl⟩
  exact ⟨l, eq_of_beq hl⟩

/-! ## `Reaches f n 1 ↔ Reaches T n 1` and arithmetic-progression lifting -/

lemma T_one : T 1 = 1 := by decide

lemma reaches_T_of_reaches_f_one {n : ℕ} (h : Reaches f n 1) : Reaches T n 1 := by
  rcases h with ⟨k, hk⟩
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    cases k with
    | zero => exact ⟨0, by simpa using hk⟩
    | succ k =>
      by_cases hev : n % 2 = 0
      · have hT : T n = f n := by rw [T_eq_f_or_ff]; simp [hev]
        rw [Function.iterate_succ_apply, ← hT] at hk
        obtain ⟨j, hj⟩ := ih k (by omega) hk
        exact ⟨j + 1, by rw [Function.iterate_succ_apply, hj]⟩
      · have hodd : n % 2 = 1 := by omega
        have hfev : f n % 2 = 0 := f_odd_even hodd
        cases k with
        | zero =>
          change f n = 1 at hk
          omega
        | succ k =>
          have hT : T n = f (f n) := by rw [T_eq_f_or_ff]; simp [hev]
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← hT] at hk
          obtain ⟨j, hj⟩ := ih k (by omega) hk
          exact ⟨j + 1, by rw [Function.iterate_succ_apply, hj]⟩

lemma T_shift_one (c D : ℕ) (hD : D % 2 = 1) :
    ∃ E : ℕ, E % 2 = 1 ∧ ∀ j : ℕ, T (c + 30 * 2 * D * j) = T c + 30 * E * j := by
  by_cases hev : c % 2 = 0
  · refine ⟨D, hD, fun j => ?_⟩
    have h2split : c + 30 * 2 * D * j = c + 2 * (30 * D * j) := by ring
    have hev' : (c + 30 * 2 * D * j) % 2 = 0 := by rw [h2split, Nat.add_mul_mod_self_left, hev]
    simp only [T, hev, hev', ↓reduceIte]
    rw [h2split, Nat.add_mul_div_left _ _ (by omega : 0 < 2)]
  · have hodd : c % 2 = 1 := by omega
    have hdo : d c % 2 = 1 := by unfold d; omega
    refine ⟨d c * D, by rw [Nat.mul_mod, hdo, hD], fun j => ?_⟩
    have h2split : c + 30 * 2 * D * j = c + 2 * (30 * D * j) := by ring
    have h10split : c + 30 * 2 * D * j = c + 10 * (6 * D * j) := by ring
    have hodd' : (c + 30 * 2 * D * j) % 2 = 1 := by rw [h2split, Nat.add_mul_mod_self_left, hodd]
    have hd_eq : d (c + 30 * 2 * D * j) = d c := by
      unfold d; rw [h10split, Nat.add_mul_mod_self_left]
    have hne : c % 2 ≠ 0 := hev
    have hne' : (c + 30 * 2 * D * j) % 2 ≠ 0 := by omega
    simp only [T, hne, hne', ↓reduceIte, hd_eq]
    have hmul : d c * (c + 30 * 2 * D * j) + 1 = (d c * c + 1) + 2 * (30 * (d c * D) * j) := by
      ring
    have hev_c : (d c * c + 1) % 2 = 0 := by rw [Nat.add_mod, Nat.mul_mod, hdo, hodd]
    rw [hmul, Nat.add_mul_div_left _ _ (by omega : 0 < 2)]

lemma T_shift_pow (k : ℕ) :
    ∀ c D : ℕ, D % 2 = 1 →
      ∃ E : ℕ, E % 2 = 1 ∧ ∀ j : ℕ, T^[k] (c + 30 * 2 ^ k * D * j) = T^[k] c + 30 * E * j := by
  induction k with
  | zero =>
    intro c D hD
    exact ⟨D, hD, fun j => by simp⟩
  | succ k ih =>
    intro c D hD
    obtain ⟨E1, hE1, hstep⟩ := T_shift_one c D hD
    obtain ⟨E2, hE2, hrest⟩ := ih (T c) E1 hE1
    refine ⟨E2, hE2, fun j => ?_⟩
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have h1 : c + 30 * 2 ^ (k + 1) * D * j = c + 30 * 2 * D * (2 ^ k * j) := by
      rw [pow_succ]; ring
    rw [h1, hstep]
    have h2 : T c + 30 * E1 * (2 ^ k * j) = T c + 30 * 2 ^ k * E1 * j := by ring
    rw [h2, hrest]

lemma T_shift_mod30 (h x q : ℕ) :
    T^[h] (x + 30 * 2 ^ h * q) % 30 = T^[h] x % 30 := by
  obtain ⟨E, _, hEq⟩ := T_shift_pow h x 1 (by decide)
  have h1 := hEq q
  simp only [mul_one] at h1
  rw [h1, show T^[h] x + 30 * E * q = T^[h] x + 30 * (E * q) by ring, Nat.add_mul_mod_self_left]

lemma T_step_prog_bit (b E : ℕ) (hE : E % 2 = 1) (s : Bool) :
    ∃ c0 j0 E' : ℕ, E' % 2 = 1 ∧
      c0 % 30 = (step30 ⟨b % 30, Nat.mod_lt b (by omega)⟩ s).val ∧
      ∀ j : ℕ, T (b + 30 * E * (2 * j + j0)) = c0 + 30 * E' * j := by
  let j0 : ℕ := if decide ((b / 30) % 2 = 1) == s then 0 else 1
  let b' := b + 30 * E * j0
  obtain ⟨E', hE', hshift⟩ := T_shift_one b' E hE
  refine ⟨T b', j0, E', hE', ?_, fun j => ?_⟩
  · rw [T_mod_30_eq b']
    have hmod : b' % 30 = b % 30 := by
      have : b' = b + 30 * (E * j0) := by dsimp only [b']; ring
      rw [this, Nat.add_mul_mod_self_left]
    have hdiv : (b' / 30) % 2 = ((b / 30) + E * j0) % 2 := by
      have : b' = b + 30 * (E * j0) := by dsimp only [b']; ring
      rw [this, Nat.add_mul_div_left _ _ (by omega : 0 < 30)]
    have hbit : decide ((b' / 30) % 2 = 1) = s := by
      rw [hdiv]
      cases hs : s <;> by_cases hb : (b / 30) % 2 = 1
      · simp [j0, hs, hb, Nat.add_mod, hE]
      · simp [j0, hs, hb]
      · simp [j0, hs, hb]
      · simp [j0, hs, hb, Nat.add_mod, hE]; omega
    have hfin : (⟨b' % 30, Nat.mod_lt b' (by omega)⟩ : Fin 30) =
        ⟨b % 30, Nat.mod_lt b (by omega)⟩ := Fin.ext hmod
    rw [hfin, hbit]
  · have heq : b + 30 * E * (2 * j + j0) = b' + 30 * 2 * E * j := by
      dsimp only [b']; ring
    rw [heq, hshift]

lemma T_run_prog (l : List Bool) :
    ∀ b E : ℕ, E % 2 = 1 →
      ∃ c0 E' A B : ℕ, E' % 2 = 1 ∧ 0 < A ∧
        c0 % 30 = (run30 ⟨b % 30, Nat.mod_lt b (by omega)⟩ l).val ∧
        ∀ j : ℕ, T^[l.length] (b + 30 * E * (A * j + B)) = c0 + 30 * E' * j := by
  induction l with
  | nil =>
    intro b E hE
    exact ⟨b, E, 1, 0, hE, by omega, rfl, fun j => by simp⟩
  | cons s ls ih =>
    intro b E hE
    obtain ⟨c1, j0, E1, hE1, hc1, hstep⟩ := T_step_prog_bit b E hE s
    obtain ⟨c0, E', A1, B1, hE', hA1, hc0, hrest⟩ := ih c1 E1 hE1
    refine ⟨c0, E', 2 * A1, 2 * B1 + j0, hE', by omega, ?_, fun j => ?_⟩
    · simp only [run30]
      have hfin : (⟨c1 % 30, Nat.mod_lt c1 (by omega)⟩ : Fin 30) =
          step30 ⟨b % 30, Nat.mod_lt b (by omega)⟩ s := Fin.ext hc1
      rw [← hfin]
      exact hc0
    · simp only [List.length_cons, Function.iterate_succ_apply]
      have h1 : b + 30 * E * (2 * A1 * j + (2 * B1 + j0)) =
          b + 30 * E * (2 * (A1 * j + B1) + j0) := by ring
      rw [h1, hstep, hrest]

/-! ## The `+30` inverse commutator `P(u) = 64u - 33`, `Q(u) = 64u - 3` (`eq:commutator`) -/

/-- Backward digit-1 inverse move `L(u) = 2u - 1`. -/
def moveL (u : ℕ) : ℕ := 2 * u - 1

/-- Backward digit-1 inverse move `H(u) = 32u - 1`. -/
def moveH (u : ℕ) : ℕ := 32 * u - 1

/-- Commutator generator `P(u) = H(L(u)) = 64u - 33`. -/
private def commP (u : ℕ) : ℕ := 64 * u - 33

/-- Shifted commutator generator `Q(u) = L(H(u)) = 64u - 3 = P(u) + 30`. -/
private def commQ (u : ℕ) : ℕ := 64 * u - 3

private lemma moveL_props {u : ℕ} (hu1 : 1 ≤ u) (hu10 : u % 10 = 1) :
    1 ≤ moveL u ∧ moveL u % 10 = 1 ∧ Reaches f (moveL u) u := by
  refine ⟨by unfold moveL; omega, by unfold moveL; omega, ⟨2, ?_⟩⟩
  have hodd : moveL u % 2 = 1 := by unfold moveL; omega
  have hd : d (moveL u) = 1 := by unfold d moveL; omega
  rw [Function.iterate_succ_apply, f_odd hodd, hd, one_mul]
  have heq : moveL u + 1 = 2 * u := by unfold moveL; omega
  rw [heq, Function.iterate_one, f_even (by omega)]
  omega

private lemma moveH_props {u : ℕ} (hu1 : 1 ≤ u) (hu10 : u % 10 = 1) :
    1 ≤ moveH u ∧ moveH u % 10 = 1 ∧ Reaches f (moveH u) u := by
  refine ⟨by unfold moveH; omega, by unfold moveH; omega, ⟨6, ?_⟩⟩
  have hodd : moveH u % 2 = 1 := by unfold moveH; omega
  have hd : d (moveH u) = 1 := by unfold d moveH; omega
  rw [Function.iterate_succ_apply, f_odd hodd, hd, one_mul]
  have heq : moveH u + 1 = 2 ^ 5 * u := by unfold moveH; omega
  rw [heq, f_iter_two_pow 5 u]

private lemma commP_props {u : ℕ} (hu1 : 1 ≤ u) (hu10 : u % 10 = 1) :
    u + 30 ≤ commP u ∧ commP u % 10 = 1 ∧ Reaches f (commP u) u := by
  have heq : commP u = moveH (moveL u) := by unfold commP moveH moveL; omega
  obtain ⟨hL1, hL10, hLr⟩ := moveL_props hu1 hu10
  obtain ⟨_, hH10, hHr⟩ := moveH_props hL1 hL10
  rw [heq]
  exact ⟨by unfold moveH moveL; omega, hH10, reaches_trans hHr hLr⟩

private lemma commQ_props {u : ℕ} (hu1 : 1 ≤ u) (hu10 : u % 10 = 1) :
    commQ u = commP u + 30 ∧ 1 ≤ commQ u ∧ commQ u % 10 = 1 ∧ Reaches f (commQ u) u := by
  have heq : commQ u = moveL (moveH u) := by unfold commQ moveL moveH; omega
  obtain ⟨hH1, hH10, hHr⟩ := moveH_props hu1 hu10
  obtain ⟨hL1, hL10, hLr⟩ := moveL_props hH1 hH10
  refine ⟨by unfold commQ commP; omega, ?_, ?_, ?_⟩
  · rw [heq]; exact hL1
  · rw [heq]; exact hL10
  · rw [heq]; exact reaches_trans hLr hHr

private lemma commP_iter_props (k : ℕ) {u : ℕ} (hu1 : 1 ≤ u) (hu10 : u % 10 = 1) :
    u + 30 * k ≤ commP^[k] u ∧ commP^[k] u % 10 = 1 ∧ Reaches f (commP^[k] u) u := by
  induction k with
  | zero => exact ⟨by simp, hu10, reaches_refl f u⟩
  | succ k ih =>
    obtain ⟨hge, h10, hr⟩ := ih
    rw [Function.iterate_succ_apply']
    have hge1 : 1 ≤ commP^[k] u := le_trans hu1 (le_trans (Nat.le_add_right u _) hge)
    obtain ⟨hge', h10', hr'⟩ := commP_props hge1 h10
    exact ⟨by omega, h10', reaches_trans hr' hr⟩

/-- Any odd-step arithmetic progression `b + 30 * E * j` matching a digit-1 seed `u` modulo `30`
    contains arbitrarily large terms reaching `u` under `f`. -/
theorem comm_hit_prog (u b E : ℕ) (hu1 : 1 ≤ u) (hu10 : u % 10 = 1)
    (hE : 1 ≤ E) (hEodd : E % 2 = 1) (hmod : b % 30 = u % 30) :
    ∀ N : ℕ, ∃ j : ℕ, N ≤ j ∧ Reaches f (b + 30 * E * j) u := by
  set q := 15 * E
  have hq_pos : 0 < q := by omega
  have : NeZero q := ⟨by omega⟩
  have hq_odd : q % 2 = 1 := by omega
  have hcop64 : Nat.Coprime 64 q := by
    have h2 : Nat.Coprime 2 q := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
    simpa using h2.pow_left 6
  let u64 : (ZMod q)ˣ := ZMod.unitOfCoprime 64 hcop64
  have hu64_val : (u64 : ZMod q) = (64 : ZMod q) := by simp [u64]
  let g : Equiv.Perm (ZMod q) :=
    { toFun := fun x => (64 : ZMod q) * x - 33
      invFun := fun x => (u64⁻¹ : (ZMod q)ˣ) * (x + 33)
      left_inv := fun x => by
        calc ((u64⁻¹ : (ZMod q)ˣ) : ZMod q) * ((64 : ZMod q) * x - 33 + 33)
            = ((u64⁻¹ : (ZMod q)ˣ) : ZMod q) * ((u64 : ZMod q) * x) := by rw [hu64_val]; ring
          _ = (((u64⁻¹ * u64 : (ZMod q)ˣ) : ZMod q)) * x := by push_cast; ring
          _ = x := by simp
      right_inv := fun x => by
        calc (64 : ZMod q) * (((u64⁻¹ : (ZMod q)ˣ) : ZMod q) * (x + 33)) - 33
            = (((u64 * u64⁻¹ : (ZMod q)ˣ) : ZMod q)) * (x + 33) - 33 := by
                rw [← hu64_val]; push_cast; ring
          _ = x := by simp }
  let s : ℕ := orderOf g
  have hs_pos : 1 ≤ s := orderOf_pos g
  have hg_pow : ∀ x : ZMod q, g^[s] x = x := by
    intro x
    have hpow : g ^ s = 1 := pow_orderOf_eq_one g
    have h1 : (g ^ s) x = x := by rw [hpow]; rfl
    simpa [Equiv.Perm.coe_pow] using h1
  have hcommP_zmod : ∀ k x : ℕ, 1 ≤ x →
      (commP^[k] x : ZMod q) = g^[k] (x : ZMod q) := by
    intro k
    induction k with
    | zero => intro x _; simp
    | succ k ih =>
      intro x hx
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hge : 1 ≤ commP^[k] x := by
        clear ih
        induction k with
        | zero => exact hx
        | succ k ih2 =>
          rw [Function.iterate_succ_apply']
          have h1 : 1 ≤ commP^[k] x := ih2
          change 1 ≤ 64 * commP^[k] x - 33
          omega
      have hsub : 33 ≤ 64 * commP^[k] x := by omega
      change ((64 * commP^[k] x - 33 : ℕ) : ZMod q) = (64 : ZMod q) * g^[k] (x : ZMod q) - 33
      rw [Nat.cast_sub hsub, Nat.cast_mul, ih x hx]
      norm_cast
  let step30P (x : ℕ) : ℕ := commQ (commP^[s - 1] x)
  have hstep30P : ∀ x : ℕ, 1 ≤ x → x % 10 = 1 →
      1 ≤ step30P x ∧ step30P x % 10 = 1 ∧ Reaches f (step30P x) x ∧
      (step30P x : ZMod q) = (x : ZMod q) + 30 := by
    intro x hx1 hx10
    obtain ⟨hge, h10, hr⟩ := commP_iter_props (s - 1) hx1 hx10
    obtain ⟨hQP, hQ1, hQ10, hQr⟩ := commQ_props (by omega) h10
    refine ⟨hQ1, hQ10, reaches_trans hQr hr, ?_⟩
    have hPs : commP (commP^[s - 1] x) = commP^[s] x := by
      conv_rhs => rw [show s = (s - 1) + 1 by omega, Function.iterate_succ_apply']
    change (commQ (commP^[s - 1] x) : ZMod q) = (x : ZMod q) + 30
    rw [hQP, hPs, Nat.cast_add, hcommP_zmod s x hx1, hg_pow]
    norm_cast
  have hstep30P_iter : ∀ t : ℕ,
      1 ≤ step30P^[t] u ∧ step30P^[t] u % 10 = 1 ∧ Reaches f (step30P^[t] u) u ∧
      (step30P^[t] u : ZMod q) = (u : ZMod q) + 30 * (t : ZMod q) := by
    intro t
    induction t with
    | zero => exact ⟨hu1, hu10, reaches_refl f u, by simp⟩
    | succ t ih =>
      obtain ⟨h1, h10, hr, hz⟩ := ih
      rw [Function.iterate_succ_apply']
      obtain ⟨h1', h10', hr', hz'⟩ := hstep30P (step30P^[t] u) h1 h10
      refine ⟨h1', h10', reaches_trans hr' hr, ?_⟩
      rw [hz', hz]; push_cast; ring
  let t : ℕ := (((b / 30 : ℕ) : ZMod q) - ((u / 30 : ℕ) : ZMod q)).val
  let v : ℕ := step30P^[t] u
  obtain ⟨hv1, hv10, hvr, hvz⟩ := hstep30P_iter t
  have hv_mod_q : v % q = b % q := by
    have ht_cast : (t : ZMod q) = ((b / 30 : ℕ) : ZMod q) - ((u / 30 : ℕ) : ZMod q) :=
      ZMod.natCast_zmod_val _
    have hbv : (v : ZMod q) = (b : ZMod q) := by
      have hb_eq : (b : ZMod q) = 30 * ((b / 30 : ℕ) : ZMod q) + ((b % 30 : ℕ) : ZMod q) := by
        conv_lhs => rw [(Nat.div_add_mod b 30).symm]
        push_cast; rfl
      have hu_eq : (u : ZMod q) = 30 * ((u / 30 : ℕ) : ZMod q) + ((u % 30 : ℕ) : ZMod q) := by
        conv_lhs => rw [(Nat.div_add_mod u 30).symm]
        push_cast; rfl
      rw [hvz, ht_cast, hb_eq, hu_eq, hmod]
      ring
    exact (ZMod.natCast_eq_natCast_iff' v b q).mp hbv
  intro N
  let r : ℕ := b + 30 * E * N
  let w : ℕ := commP^[s * r] v
  obtain ⟨hw_ge, hw10, hwr⟩ := commP_iter_props (s * r) hv1 hv10
  have hw_mod_q : w % q = b % q := by
    have hz : (w : ZMod q) = (v : ZMod q) := by
      rw [hcommP_zmod (s * r) v hv1]
      have hsr : g^[s * r] (v : ZMod q) = (v : ZMod q) := by
        have : (g ^ (s * r)) (v : ZMod q) = (v : ZMod q) := by
          rw [pow_mul, pow_orderOf_eq_one, one_pow]; rfl
        simpa [Equiv.Perm.coe_pow] using this
      exact hsr
    have hmod_qv : w % q = v % q := (ZMod.natCast_eq_natCast_iff' w v q).mp hz
    exact hmod_qv.trans hv_mod_q
  have hw_mod_2 : w % 2 = b % 2 := by
    have h1 : w % 10 = 1 := hw10
    omega
  have hcop2q : Nat.Coprime 2 q := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
  have hw_mod_30E : w % (30 * E) = b % (30 * E) := by
    have hmul : 2 * q = 30 * E := by dsimp only [q]; ring
    rw [← hmul]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop2q).mp ⟨hw_mod_2, hw_mod_q⟩
  have hw_ge_r : b + 30 * E * N ≤ w := by
    have h1 : r ≤ s * r := Nat.le_mul_of_pos_left r hs_pos
    have h2 : v + 30 * (s * r) ≤ w := hw_ge
    have h3 : r = b + 30 * E * N := rfl
    omega
  have hdvd_diff : 30 * E ∣ (w - b) := by
    have h1 := Nat.div_add_mod w (30 * E)
    have h2 := Nat.div_add_mod b (30 * E)
    refine ⟨w / (30 * E) - b / (30 * E), ?_⟩
    have hle : b / (30 * E) ≤ w / (30 * E) := Nat.div_le_div_right (by omega)
    rw [Nat.mul_sub_left_distrib]
    omega
  let j : ℕ := (w - b) / (30 * E)
  have hw_eq : b + 30 * E * j = w := by
    have hmul : 30 * E * j = w - b := Nat.mul_div_cancel' hdvd_diff
    omega
  refine ⟨j, ?_, ?_⟩
  · have : 30 * E * N ≤ 30 * E * j := by omega
    exact Nat.le_of_mul_le_mul_left this (by omega)
  · rw [hw_eq]
    exact reaches_trans hwr hvr

/-! ## CRT refinement of `a mod m` by `x mod M` -/

/-- Exact 2-adic exponent `h = max(0, v_2(m) - 1)` via `m.factorization 2 - 1`. -/
def suffixH (m : ℕ) : ℕ := m.factorization 2 - 1

/-- Modulus `M = 30 * 2^h` of Theorem 29. -/
def suffixM (m : ℕ) : ℕ := 30 * 2 ^ suffixH m

/-- Compatibility modulus `p = gcd(m, M)` of Theorem 29. -/
def suffixP (m : ℕ) : ℕ := Nat.gcd m (suffixM m)

lemma suffix_odd_quot (m : ℕ) (hm : 1 ≤ m) :
    let h := suffixH m
    let M := suffixM m
    let p := suffixP m
    let D := m / p
    D % 2 = 1 ∧ Nat.lcm M m = 30 * 2 ^ h * D ∧
    (∀ a x : ℕ, x % p = a % p →
      ∃ n0 : ℕ, n0 % M = x % M ∧ n0 % m = a % m) := by
  intro h M p D
  have hm0 : m ≠ 0 := by omega
  have hM0 : M ≠ 0 := by dsimp only [M, suffixM]; positivity
  -- Show v_2(m) ≤ v_2(M) = 1 + h, hence v_2(p) = v_2(m) and D = m / p is odd!
  have hvM : M.factorization 2 = 1 + h := by
    have h30 : (30 : ℕ).factorization 2 = 1 := by
      have : (30 : ℕ) = 2 ^ 1 * 15 := by norm_num
      rw [this, Nat.factorization_mul (by norm_num) (by norm_num)]
      simp only [Finsupp.coe_add, Pi.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
        Finsupp.single_eq_same]
      have h15 : (15 : ℕ).factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by decide)
      omega
    dsimp only [M, suffixM]
    rw [Nat.factorization_mul (by norm_num) (by positivity), Finsupp.coe_add, Pi.add_apply,
        h30, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  have hvm_le : m.factorization 2 ≤ M.factorization 2 := by
    rw [hvM]; dsimp only [h, suffixH]; omega
  have hvp : p.factorization 2 = m.factorization 2 := by
    dsimp only [p, suffixP]
    rw [Nat.factorization_gcd hm0 hM0, Finsupp.inf_apply, min_eq_left hvm_le]
  have hp_dvd_m : p ∣ m := Nat.gcd_dvd_left m M
  have hp0 : p ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left M (by omega))
  have hD_odd : D % 2 = 1 := by
    have hD0 : D ≠ 0 := by
      have : p * D = m := Nat.mul_div_cancel' hp_dvd_m
      intro h0; rw [h0, mul_zero] at this; exact hm0 this.symm
    have hfac : D.factorization 2 = 0 := by
      have hmul : p * D = m := Nat.mul_div_cancel' hp_dvd_m
      have hf := congr_arg (fun n => n.factorization 2) hmul
      rw [Nat.factorization_mul hp0 hD0, Finsupp.coe_add, Pi.add_apply, hvp] at hf
      omega
    have hndvd : ¬ 2 ∣ D := by
      intro hdvd
      have hpos : 0 < D.factorization 2 :=
        (Nat.prime_two.dvd_iff_one_le_factorization hD0).mp hdvd
      omega
    omega
  have hlcm : Nat.lcm M m = 30 * 2 ^ h * D := by
    have h1 : Nat.gcd M m * Nat.lcm M m = M * m := Nat.gcd_mul_lcm M m
    have h2 : Nat.gcd M m = p := Nat.gcd_comm M m
    have h3 : p * D = m := Nat.mul_div_cancel' hp_dvd_m
    have h4 : p * Nat.lcm M m = p * (M * D) := by
      calc p * Nat.lcm M m = Nat.gcd M m * Nat.lcm M m := by rw [h2]
        _ = M * m := h1
        _ = M * (p * D) := by rw [h3]
        _ = p * (M * D) := by ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) h4
  refine ⟨hD_odd, hlcm, fun a x hxa => ?_⟩
  -- Generalized CRT from Bezout's identity for p = gcd(m, M):
  let A : ℤ := Nat.gcdA m M
  let B : ℤ := Nat.gcdB m M
  have hbez : (p : ℤ) = (m : ℤ) * A + (M : ℤ) * B := Nat.gcd_eq_gcd_ab m M
  have hp_dvd_diff : (p : ℤ) ∣ ((x : ℤ) - (a : ℤ)) := by
    rw [dvd_sub_comm, ← Int.modEq_iff_dvd]
    exact Int.natCast_modEq_iff.mpr hxa
  obtain ⟨k, hk⟩ := hp_dvd_diff
  let z : ℤ := (a : ℤ) + (m : ℤ) * A * k
  have hzm : z ≡ (a : ℤ) [ZMOD (m : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-(A * k), ?_⟩
    dsimp only [z]; ring
  have hzM : z ≡ (x : ℤ) [ZMOD (M : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨B * k, ?_⟩
    have h1 : (x : ℤ) - z = (x : ℤ) - (a : ℤ) - (m : ℤ) * A * k := by dsimp only [z]; ring
    rw [h1, hk, hbez]; ring
  let L : ℕ := M * m
  have hLpos : 0 < L := Nat.mul_pos (Nat.pos_of_ne_zero hM0) (by omega)
  let n0 : ℕ := (z % (L : ℤ)).toNat
  have hznn : 0 ≤ z % (L : ℤ) := Int.emod_nonneg z (by exact_mod_cast (ne_of_gt hLpos))
  have hn0_cast : (n0 : ℤ) = z % (L : ℤ) := Int.toNat_of_nonneg hznn
  have hn0_modL : (n0 : ℤ) ≡ z [ZMOD (L : ℤ)] := by
    rw [hn0_cast]; exact Int.mod_modEq z (L : ℤ)
  have hn0_M : n0 % M = x % M := by
    have h1 : (n0 : ℤ) ≡ (x : ℤ) [ZMOD (M : ℤ)] :=
      (hn0_modL.of_dvd (by exact_mod_cast dvd_mul_right M m)).trans hzM
    exact Int.natCast_modEq_iff.mp h1
  have hn0_m : n0 % m = a % m := by
    have h1 : (n0 : ℤ) ≡ (a : ℤ) [ZMOD (m : ℤ)] :=
      (hn0_modL.of_dvd (by exact_mod_cast dvd_mul_left m M)).trans hzm
    exact Int.natCast_modEq_iff.mp h1
  exact ⟨n0, hn0_M, hn0_m⟩

/-! ## Seeds for `B_1` and `B_5` and main completions theorem -/

private lemma seed_1_in_B1 : Reaches f 1 1 := ⟨0, rfl⟩
private lemma seed_211_in_B5 : Reaches f 211 5 := ⟨9, by decide⟩
private lemma seed_11_in_B5 : Reaches f 11 5 := ⟨5, by decide⟩
private lemma seed_21_in_B5 : Reaches f 21 5 := ⟨7, by decide⟩

/-- Core progression-to-orbit lifting: if `x < M` satisfies `x % p = a % p`, and `T^[h] x % 30`
    reaches `u % 30` in `step30` for a digit-1 seed `u ≥ 1`, then `a mod m` contains arbitrarily
    large positive integers reaching `u` under `f`. -/
private lemma suffix_lift_seed (a m x u : ℕ) (hm : 1 ≤ m) (hu1 : 1 ≤ u) (hu10 : u % 10 = 1)
    (hxa : x % suffixP m = a % suffixP m)
    (l : List Bool)
    (hl : (run30 ⟨T^[suffixH m] x % 30, Nat.mod_lt _ (by omega)⟩ l).val = u % 30) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ n % m = a % m ∧ Reaches f n u := by
  set h := suffixH m
  set M := suffixM m
  set p := suffixP m
  set D := m / p
  obtain ⟨hDodd, hlcm, hcrt⟩ := suffix_odd_quot m hm
  obtain ⟨n0, hn0M, hn0m⟩ := hcrt a x hxa
  have hDpos : 1 ≤ D := Nat.pos_of_ne_zero fun h0 => by
    have h1 : D % 2 = 1 := hDodd
    rw [h0] at h1; exact absurd h1 (by decide)
  have hm_dvd_step : m ∣ 30 * 2 ^ h * D := by
    rw [← hlcm]; exact Nat.dvd_lcm_right M m
  obtain ⟨E1, hE1odd, hTh⟩ := T_shift_pow h n0 D hDodd
  have hTh_mod30 : T^[h] n0 % 30 = T^[h] x % 30 := by
    have h1 := T_shift_mod30 h (n0 % M) (n0 / M)
    have h2 := T_shift_mod30 h (x % M) (x / M)
    have hdiv1 : n0 % M + 30 * 2 ^ h * (n0 / M) = n0 := by
      have := Nat.mod_add_div n0 M; simpa [M, suffixM, mul_assoc] using this
    have hdiv2 : x % M + 30 * 2 ^ h * (x / M) = x := by
      have := Nat.mod_add_div x M; simpa [M, suffixM, mul_assoc] using this
    rw [hdiv1] at h1; rw [hdiv2] at h2
    rw [h1, hn0M, ← h2]
  obtain ⟨c0, E', A, B, hE'odd, hApos, hc0_mod, hrun⟩ := T_run_prog l (T^[h] n0) E1 hE1odd
  have hc0_u : c0 % 30 = u % 30 := by
    rw [hc0_mod]
    have hfin : (⟨T^[h] n0 % 30, Nat.mod_lt _ (by omega)⟩ : Fin 30) =
        ⟨T^[h] x % 30, Nat.mod_lt _ (by omega)⟩ := Fin.ext hTh_mod30
    rw [hfin, hl]
  have hE'pos : 1 ≤ E' := by omega
  intro N
  obtain ⟨j, hjN, hreach_u⟩ := comm_hit_prog u c0 E' hu1 hu10 hE'pos hE'odd hc0_u (N + 1)
  let n : ℕ := n0 + 30 * 2 ^ h * D * (A * j + B)
  have hstep_pos : 1 ≤ 30 * 2 ^ h * D := by
    have : 0 < 30 * 2 ^ h * D := by positivity
    omega
  have hn_ge : N ≤ n := by
    have h1 : j ≤ A * j + B := by nlinarith
    have h2 : A * j + B ≤ 30 * 2 ^ h * D * (A * j + B) := Nat.le_mul_of_pos_left _ hstep_pos
    omega
  have hn_pos : 0 < n := by
    have h1 : 1 ≤ A * j + B := by nlinarith
    have h2 : 1 ≤ 30 * 2 ^ h * D * (A * j + B) := Nat.mul_pos hstep_pos h1
    omega
  have hn_mod_m : n % m = a % m := by
    obtain ⟨q, hq⟩ := hm_dvd_step
    have heq : n = n0 + m * (q * (A * j + B)) := by dsimp only [n]; rw [hq]; ring
    rw [heq, Nat.add_mul_mod_self_left, hn0m]
  have hT_eq : T^[l.length + h] n = c0 + 30 * E' * j := by
    rw [Function.iterate_add_apply]
    dsimp only [n]
    rw [hTh (A * j + B), hrun j]
  obtain ⟨k_f, hk_f⟩ := T_iter_is_f_iter (l.length + h) n
  have hreach_c : Reaches f n (c0 + 30 * E' * j) := ⟨k_f, hk_f.symm.trans hT_eq⟩
  exact ⟨n, hn_ge, hn_pos, hn_mod_m, reaches_trans hreach_c hreach_u⟩

/-- **Theorem 29 (`thm:suffix-class`, Part 1 — Basin of 5)**:
    Every congruence class `a mod m` (`m ≥ 1`) contains infinitely many members of `B_5`. -/
theorem thm_suffix_class_B5 (a m : ℕ) (hm : 1 ≤ m) :
    Set.Infinite {n : ℕ | 0 < n ∧ n % m = a % m ∧ InBasin5 n} := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  let x := a % suffixM m
  have hxa : x % suffixP m = a % suffixP m := Nat.mod_mod_of_dvd a (Nat.gcd_dvd_right m (suffixM m))
  obtain ⟨l, hl⟩ := all_reach_digit1_30 ⟨T^[suffixH m] x % 30, Nat.mod_lt _ (by omega)⟩
  set r := (run30 ⟨T^[suffixH m] x % 30, Nat.mod_lt _ (by omega)⟩ l).val
  have hr_lt : r < 30 := (run30 _ l).isLt
  have hr_cases : r = 1 ∨ r = 11 ∨ r = 21 := by omega
  rcases hr_cases with hr1 | hr11 | hr21
  · obtain ⟨n, hnN, hn_pos, hnm, hru⟩ :=
      suffix_lift_seed a m x 211 hm (by omega) (by decide) hxa l (by simpa [r] using hr1) (N + 1)
    exact ⟨n, ⟨hn_pos, hnm, reaches_trans hru seed_211_in_B5⟩, by omega⟩
  · obtain ⟨n, hnN, hn_pos, hnm, hru⟩ :=
      suffix_lift_seed a m x 11 hm (by omega) (by decide) hxa l (by simpa [r] using hr11) (N + 1)
    exact ⟨n, ⟨hn_pos, hnm, reaches_trans hru seed_11_in_B5⟩, by omega⟩
  · obtain ⟨n, hnN, hn_pos, hnm, hru⟩ :=
      suffix_lift_seed a m x 21 hm (by omega) (by decide) hxa l (by simpa [r] using hr21) (N + 1)
    exact ⟨n, ⟨hn_pos, hnm, reaches_trans hru seed_21_in_B5⟩, by omega⟩

/-- **Theorem 29 (`thm:suffix-class`, Part 2a — Necessity / Empty-class dichotomy for `B_1`)**:
    If `a mod m` contains even a single member `n` of `B_1`, then some `0 ≤ x < M` satisfies
    `x ≡ a (mod p)` and `T^[h] x % 30 ∈ {0, 1, 2, 4, 8, 15, 16, 17}`. -/
theorem thm_suffix_class_B1_necessity (a m : ℕ) (_hm : 1 ≤ m)
    (n : ℕ) (hnm : n % m = a % m) (hB1 : InBasin1 n) :
    ∃ x : ℕ, x < suffixM m ∧ x % suffixP m = a % suffixP m ∧
      T^[suffixH m] x % 30 ∈ liveMod30 := by
  set h := suffixH m
  set M := suffixM m
  set p := suffixP m
  have hMpos : 0 < M := by dsimp only [M, suffixM]; positivity
  obtain ⟨k, hk⟩ := reaches_T_of_reaches_f_one hB1
  have hk_pad : T^[max k h] n = 1 := by
    have hadd : max k h = (max k h - k) + k := by omega
    rw [hadd, Function.iterate_add_apply, hk]
    clear hk hadd
    induction (max k h - k) with
    | zero => rfl
    | succ t ih => rw [Function.iterate_succ_apply', ih, T_one]
  have hTh_live : T^[h] n % 30 ∈ liveMod30 := by
    have hsplit : max k h = (max k h - h) + h := by omega
    rw [hsplit, Function.iterate_add_apply] at hk_pad
    apply liveMod30_backward_iter (max k h - h) (T^[h] n)
    rw [hk_pad]
    decide
  refine ⟨n % M, Nat.mod_lt n hMpos, ?_, ?_⟩
  · have hpM : p ∣ M := Nat.gcd_dvd_right m M
    have hpm : p ∣ m := Nat.gcd_dvd_left m M
    rw [Nat.mod_mod_of_dvd n hpM, ← Nat.mod_mod_of_dvd n hpm, hnm, Nat.mod_mod_of_dvd a hpm]
  · have h1 := T_shift_mod30 h (n % M) (n / M)
    have hdiv : n % M + 30 * 2 ^ h * (n / M) = n := by
      have := Nat.mod_add_div n M; simpa [M, suffixM, mul_assoc] using this
    rw [hdiv] at h1
    rw [← h1]
    exact hTh_live

/-- **Theorem 29 (`thm:suffix-class`, Part 2b — Sufficiency for `B_1`)**:
    If some `0 ≤ x < M` satisfies `x ≡ a (mod p)` and `T^[h] x % 30 ∈ liveMod30`, then
    `a mod m` contains infinitely many members of `B_1`. -/
theorem thm_suffix_class_B1_sufficiency (a m : ℕ) (hm : 1 ≤ m)
    (x : ℕ) (_hx : x < suffixM m) (hxa : x % suffixP m = a % suffixP m)
    (hlive : T^[suffixH m] x % 30 ∈ liveMod30) :
    Set.Infinite {n : ℕ | 0 < n ∧ n % m = a % m ∧ InBasin1 n} := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  let r : Fin 30 := ⟨T^[suffixH m] x % 30, Nat.mod_lt _ (by omega)⟩
  have hl : (run30 r (pathTo1 r)).val = 1 % 30 := pathTo1_spec r hlive
  obtain ⟨n, hnN, hn_pos, hnm, hru⟩ :=
    suffix_lift_seed a m x 1 hm (by omega) (by decide) hxa (pathTo1 r) hl (N + 1)
  exact ⟨n, ⟨hn_pos, hnm, hru⟩, by omega⟩

/-- **Theorem 29 (`thm:suffix-class`, complete statement)**:
    For every congruence class `a mod m` (`m ≥ 1`):
    1. `a mod m` contains infinitely many members of `B_5`.
    2. `a mod m` contains infinitely many members of `B_1` iff some `0 ≤ x < 30 * 2^h`
       satisfies `x ≡ a (mod gcd(m, 30 * 2^h))` and `T^[h] x % 30 ∈ {0, 1, 2, 4, 8, 15, 16, 17}`,
       where `h = max(0, v_2(m) - 1) = m.factorization 2 - 1`.
    3. If no such `x` exists, `a mod m` contains NO member of `B_1` at all. -/
theorem thm_suffix_class (a m : ℕ) (hm : 1 ≤ m) :
    Set.Infinite {n : ℕ | 0 < n ∧ n % m = a % m ∧ InBasin5 n} ∧
    (Set.Infinite {n : ℕ | 0 < n ∧ n % m = a % m ∧ InBasin1 n} ↔
      ∃ x : ℕ, x < suffixM m ∧ x % suffixP m = a % suffixP m ∧
        T^[suffixH m] x % 30 ∈ liveMod30) ∧
    ((¬ ∃ x : ℕ, x < suffixM m ∧ x % suffixP m = a % suffixP m ∧
        T^[suffixH m] x % 30 ∈ liveMod30) →
      ∀ n : ℕ, n % m = a % m → ¬ InBasin1 n) := by
  refine ⟨thm_suffix_class_B5 a m hm, ⟨?_, ?_⟩, ?_⟩
  · intro hinf
    obtain ⟨n, hn⟩ := hinf.nonempty
    exact thm_suffix_class_B1_necessity a m hm n hn.2.1 hn.2.2
  · rintro ⟨x, hx, hxa, hlive⟩
    exact thm_suffix_class_B1_sufficiency a m hm x hx hxa hlive
  · intro hno n hnm hB1
    exact hno (thm_suffix_class_B1_necessity a m hm n hnm hB1)

end Ouroboros
