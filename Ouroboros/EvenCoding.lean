module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import Ouroboros.Defs
public import Ouroboros.EvenBases
@[expose] public section

/-! # Section 2 (Even Bases): Coding & stopping-density certificates (`lem:even-coding`, `prop:stopping-certs`) -/

namespace Ouroboros

/-! ## Shortcut map `T_b` and affine tracking `(A_j, B_j)` -/
/-- Terras shortcut map for even base `b ≥ 2`: `n / 2` if `n` is even, `((n % b)*n + 1) / 2` if odd. -/
def T_b (b n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else ((n % b) * n + 1) / 2
lemma T_b_even {b n : ℕ} (h : n % 2 = 0) : T_b b n = n / 2 := by simp [T_b, h]
lemma T_b_odd {b n : ℕ} (h : n % 2 = 1) : T_b b n = ((n % b) * n + 1) / 2 := by simp [T_b, show n % 2 ≠ 0 by omega]
lemma two_mul_T_b {b n : ℕ} (hbeven : b % 2 = 0) : 2 * T_b b n = if n % 2 = 0 then n else (n % b) * n + 1 := by
  by_cases h : n % 2 = 0
  · simp only [T_b, h, ↓reduceIte]; omega
  · have hodd : n % 2 = 1 := by omega
    have hd_odd : (n % b) % 2 = 1 := by
      have h2dvd : 2 ∣ b := Nat.dvd_of_mod_eq_zero hbeven
      rw [Nat.mod_mod_of_dvd n h2dvd]; exact hodd
    have hev : ((n % b) * n + 1) % 2 = 0 := by rw [Nat.add_mod, Nat.mul_mod, hd_odd, hodd]
    simp only [T_b, h, ↓reduceIte]; omega
/-- Affine pair `(A_j, B_j)` along the `T_b`-orbit of `n`: `2^j * T_b^j(n) = A_j * n + B_j`. -/
def affAB (b n : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | j + 1 =>
    let (A, B) := affAB b n j
    let x := (T_b b)^[j] n
    if x % 2 = 0 then (A, B) else ((x % b) * A, (x % b) * B + 2 ^ j)
/-- Affine identity, parity of `A_j`, and upper bound on `B_j` for even `b ≥ 2`. -/
theorem lem_even_affine {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) (n j : ℕ) : let (A, B) := affAB b n j
    2 ^ j * (T_b b)^[j] n = A * n + B ∧
    A % 2 = 1 ∧
    B ≤ j * b ^ j ∧
    (1 ≤ j → A ≠ 2 ^ j) := by
  induction j with
  | zero => simp [affAB]
  | succ j ih =>
    rcases hres : affAB b n j with ⟨A, B⟩
    rw [hres] at ih; obtain ⟨heq, hAodd, hBle, _⟩ := ih; simp only [affAB, hres]
    split_ifs with hev
    · refine ⟨?_, hAodd, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', T_b_even hev, pow_succ, mul_assoc]
        have h2x : 2 * ((T_b b)^[j] n / 2) = (T_b b)^[j] n := by omega
        rw [h2x, heq]
      · calc B ≤ j * b ^ j := hBle
          _ ≤ (j + 1) * b ^ (j + 1) := by
              have hpow : b ^ j ≤ b ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
              exact Nat.mul_le_mul (by omega) hpow
      · intro _ hAeq
        have : 2 ^ (j + 1) % 2 = 0 := by rw [pow_succ]; omega
        omega
    · have hxodd : (T_b b)^[j] n % 2 = 1 := by omega
      have h2dvd : 2 ∣ b := Nat.dvd_of_mod_eq_zero hbeven
      have hd_odd : ((T_b b)^[j] n % b) % 2 = 1 := by rw [Nat.mod_mod_of_dvd _ h2dvd]; exact hxodd
      have hA'_odd : ((T_b b)^[j] n % b * A) % 2 = 1 := by rw [Nat.mul_mod, hd_odd, hAodd]
      refine ⟨?_, hA'_odd, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', pow_succ, mul_assoc, two_mul_T_b hbeven]; simp only [hev, ↓reduceIte]
        calc 2 ^ j * ((T_b b)^[j] n % b * (T_b b)^[j] n + 1)
            = (T_b b)^[j] n % b * (2 ^ j * (T_b b)^[j] n) + 2 ^ j := by ring
          _ = (T_b b)^[j] n % b * (A * n + B) + 2 ^ j := by rw [heq]
          _ = (T_b b)^[j] n % b * A * n + ((T_b b)^[j] n % b * B + 2 ^ j) := by ring
      · have hd_lt : (T_b b)^[j] n % b ≤ b - 1 := by have := Nat.mod_lt ((T_b b)^[j] n) (by omega : 0 < b); omega
        have h2le : 2 ^ j ≤ b ^ j := Nat.pow_le_pow_left hb2 j
        have h1 : (T_b b)^[j] n % b * B ≤ b * (j * b ^ j) := Nat.mul_le_mul (by omega) hBle
        have h2 : b * (j * b ^ j) = j * b ^ (j + 1) := by rw [pow_succ]; ring
        have h3 : 2 ^ j ≤ b ^ (j + 1) := h2le.trans (Nat.pow_le_pow_right (by omega) (by omega))
        calc (T_b b)^[j] n % b * B + 2 ^ j
            ≤ j * b ^ (j + 1) + b ^ (j + 1) := by omega
          _ = (j + 1) * b ^ (j + 1) := by ring
      · intro _ hAeq
        have : 2 ^ (j + 1) % 2 = 0 := by rw [pow_succ]; omega
        omega

/-! ## Lemma `lem:even-coding` -/
/-- Lemma (`lem:even-coding`, part 1): if `n ≡ n' (mod b * 2^(k-1))` (`k ≥ 1`), then `n` and `n'` share -/
theorem lem_even_coding_mod {b k n n' : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) (hk : 1 ≤ k)
    (hmod : n % (b * 2 ^ (k - 1)) = n' % (b * 2 ^ (k - 1))) :
    (∀ j ≤ k, affAB b n j = affAB b n' j) ∧
    (∀ j < k, (T_b b)^[j] n % b = (T_b b)^[j] n' % b ∧
              (T_b b)^[j] n % 2 = (T_b b)^[j] n' % 2) := by
  have h2dvd : 2 ∣ b := Nat.dvd_of_mod_eq_zero hbeven
  have hstep : ∀ j ≤ k, affAB b n j = affAB b n' j ∧
      (j < k → (T_b b)^[j] n % b = (T_b b)^[j] n' % b) := by
    intro j hj
    induction j with
    | zero =>
      refine ⟨rfl, fun _ => ?_⟩
      simp only [Function.iterate_zero, id_eq]; have hdvd : b ∣ b * 2 ^ (k - 1) := dvd_mul_right b _
      rw [← Nat.mod_mod_of_dvd n hdvd, hmod, Nat.mod_mod_of_dvd n' hdvd]
    | succ j ih =>
      obtain ⟨hAB_eq, hmod_j⟩ := ih (by omega)
      have hmodb : (T_b b)^[j] n % b = (T_b b)^[j] n' % b := hmod_j (by omega)
      have hpar : (T_b b)^[j] n % 2 = (T_b b)^[j] n' % 2 := by
        rw [← Nat.mod_mod_of_dvd _ h2dvd, hmodb, Nat.mod_mod_of_dvd _ h2dvd]
      have hAB_succ : affAB b n (j + 1) = affAB b n' (j + 1) := by simp only [affAB, hAB_eq, hmodb, hpar]
      refine ⟨hAB_succ, fun hlt => ?_⟩
      rcases hres : affAB b n (j + 1) with ⟨A, B⟩
      have haff1 := lem_even_affine hb2 hbeven n (j + 1); have haff2 := lem_even_affine hb2 hbeven n' (j + 1)
      rw [hres] at haff1; rw [← hAB_succ, hres] at haff2; have h1 := haff1.1; have h2 := haff2.1
      have hdvd : b * 2 ^ (j + 1) ∣ b * 2 ^ (k - 1) := Nat.mul_dvd_mul_left b (pow_dvd_pow 2 (by omega))
      have hnn' : n % (b * 2 ^ (j + 1)) = n' % (b * 2 ^ (j + 1)) := by
        rw [← Nat.mod_mod_of_dvd n hdvd, hmod, Nat.mod_mod_of_dvd n' hdvd]
      have hmul_mod : (2 ^ (j + 1) * (T_b b)^[j + 1] n) % (2 ^ (j + 1) * b) =
          (2 ^ (j + 1) * (T_b b)^[j + 1] n') % (2 ^ (j + 1) * b) := by
        rw [h1, h2, mul_comm (2 ^ (j + 1)) b, Nat.add_mod, Nat.mul_mod, hnn',
            ← Nat.mul_mod, ← Nat.add_mod]
      rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at hmul_mod
      exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (j + 1)) hmul_mod
  refine ⟨fun j hj => (hstep j hj).1, fun j hj => ?_⟩
  have hm := (hstep j (by omega)).2 hj
  refine ⟨hm, ?_⟩
  rw [← Nat.mod_mod_of_dvd _ h2dvd, hm, Nat.mod_mod_of_dvd _ h2dvd]
/-- Parity-bit coding map for singly even `b = 2M` (`M` odd): `n ↦ (n mod M, j ↦ parity of T_{2M}^j(n))` for -/
def code2M (M k : ℕ) (hM : 1 ≤ M) (n : Fin (M * 2 ^ k)) : Fin M × (Fin k → Bool) :=
  (⟨n.val % M, Nat.mod_lt _ (by omega)⟩, fun j => ((T_b (2 * M))^[j.val] n.val % 2 == 1))
/-- Lemma (`lem:even-coding`, part 2a): for `b = 2M` (`M ≥ 1` odd) and `k ≥ 1`, `code2M` is a bijection from -/
theorem lem_even_coding_bij_2M {M k : ℕ} (hM : 1 ≤ M) (hModd : M % 2 = 1) (_hk : 1 ≤ k) :
    Function.Bijective (code2M M k hM) := by
  have hcard : Fintype.card (Fin (M * 2 ^ k)) = Fintype.card (Fin M × (Fin k → Bool)) := by
    simp [Fintype.card_fin, Fintype.card_prod, Fintype.card_bool]
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, hcard⟩
  intro n n' hEq
  have hmodM : n.val % M = n'.val % M := by
    have := congr_arg (fun p => p.1.val) hEq
    simpa [code2M] using this
  have hbits : ∀ j : Fin k, ((T_b (2 * M))^[j.val] n.val % 2) = ((T_b (2 * M))^[j.val] n'.val % 2) := by
    intro j
    have := congr_fun (congr_arg Prod.snd hEq) j
    simp only [code2M] at this
    by_cases h1 : (T_b (2 * M))^[j.val] n.val % 2 = 1 <;>
    by_cases h2 : (T_b (2 * M))^[j.val] n'.val % 2 = 1 <;> simp_all
  have hmod_all : ∀ j ≤ k, n.val % (M * 2 ^ j) = n'.val % (M * 2 ^ j) := by
    intro j hj
    induction j with
    | zero => simpa using hmodM
    | succ j ih =>
      have hprev := ih (by omega)
      have hAB : affAB (2 * M) n.val j = affAB (2 * M) n'.val j := by
        cases j with
        | zero => rfl
        | succ j' =>
          have h2M_eq : (2 * M) * 2 ^ (j' + 1 - 1) = M * 2 ^ (j' + 1) := by
            simp only [Nat.add_sub_cancel]; rw [pow_succ]; ring
          have hprev' : n.val % ((2 * M) * 2 ^ (j' + 1 - 1)) =
              n'.val % ((2 * M) * 2 ^ (j' + 1 - 1)) := by
            rw [h2M_eq]; exact hprev
          have hcod := lem_even_coding_mod (b := 2 * M) (k := j' + 1) (by omega) (by omega)
            (by omega) hprev'
          exact hcod.1 (j' + 1) le_rfl
      rcases hres : affAB (2 * M) n.val j with ⟨A, B⟩
      have haff1 := lem_even_affine (b := 2 * M) (by omega) (by omega) n.val j
      have haff2 := lem_even_affine (b := 2 * M) (by omega) (by omega) n'.val j
      rw [hres] at haff1; rw [← hAB, hres] at haff2; have hpar := hbits ⟨j, by omega⟩
      have hmod2 : n.val % 2 ^ (j + 1) = n'.val % 2 ^ (j + 1) := by
        have h1 : (A * n.val + B) % 2 ^ (j + 1) = (A * n'.val + B) % 2 ^ (j + 1) := by
          rw [← haff1.1, ← haff2.1, pow_succ, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hpar]
        have hzm : ((A * n.val + B : ℕ) : ZMod (2 ^ (j + 1))) =
            ((A * n'.val + B : ℕ) : ZMod (2 ^ (j + 1))) :=
          (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h1
        push_cast at hzm
        have hzm2 : (A : ZMod (2 ^ (j + 1))) * (n.val : ZMod (2 ^ (j + 1))) =
            (A : ZMod (2 ^ (j + 1))) * (n'.val : ZMod (2 ^ (j + 1))) := add_right_cancel hzm
        have hcopA : Nat.Coprime A (2 ^ (j + 1)) :=
          (Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))).pow_right _
        let uA : (ZMod (2 ^ (j + 1)))ˣ := ZMod.unitOfCoprime A hcopA
        have hzm3 : (uA : ZMod (2 ^ (j + 1))) * (n.val : ZMod (2 ^ (j + 1))) =
            (uA : ZMod (2 ^ (j + 1))) * (n'.val : ZMod (2 ^ (j + 1))) := by
          have hcoe : (uA : ZMod (2 ^ (j + 1))) = (A : ZMod (2 ^ (j + 1))) := by simp [uA]
          rw [hcoe]; exact hzm2
        have hcancel : (n.val : ZMod (2 ^ (j + 1))) = (n'.val : ZMod (2 ^ (j + 1))) := by
          have := congr_arg (((uA⁻¹ : (ZMod (2 ^ (j + 1)))ˣ) : ZMod (2 ^ (j + 1))) * ·) hzm3
          simpa [← mul_assoc] using this
        exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcancel
      have hcopM : Nat.Coprime M (2 ^ (j + 1)) :=
        (Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))).pow_right _
      exact (Nat.modEq_and_modEq_iff_modEq_mul hcopM).mp ⟨hmodM, hmod2⟩
  have hfull := hmod_all k le_rfl; rw [Nat.mod_eq_of_lt n.isLt, Nat.mod_eq_of_lt n'.isLt] at hfull
  exact Fin.ext hfull
/-- Lemma (`lem:even-coding`, part 2b): for `b = 4k` (`k ≥ 1`), `T_{4k}` maps odd integers to odd integers, and -/
theorem lem_even_coding_4k_step {k n : ℕ} (_hk : 1 ≤ k) (hn : n % 2 = 1) :
    T_b (4 * k) n % 2 = 1 ∧
    let r := n % (4 * k); let c := ((r * r + 1) / 2) % (4 * k)
    (T_b (4 * k) n % (4 * k) = c ∨ T_b (4 * k) n % (4 * k) = (c + 2 * k) % (4 * k)) := by
  have h2dvd : 2 ∣ 4 * k := ⟨2 * k, by ring⟩
  set r := n % (4 * k); set q := n / (4 * k); have hdiv : 4 * k * q + r = n := Nat.div_add_mod n (4 * k)
  have hr_odd : r % 2 = 1 := by rw [← Nat.mod_mod_of_dvd n h2dvd] at hn; exact hn
  have hr2_ev : (r * r + 1) % 2 = 0 := by rw [Nat.add_mod, Nat.mul_mod, hr_odd]
  have hT_eq : T_b (4 * k) n = (r * r + 1) / 2 + 2 * k * (r * q) := by
    rw [T_b_odd hn]; have hnum : r * n + 1 = (r * r + 1) + 2 * (2 * k * (r * q)) := by rw [← hdiv]; ring
    rw [hnum]; omega
  have hodd_c : ((r * r + 1) / 2) % 2 = 1 := by
    have h : r = 2 * (r / 2) + 1 := by omega
    have hsq : r * r + 1 = 2 * (2 * ((r / 2) * (r / 2) + r / 2) + 1) := by
      calc r * r + 1 = (2 * (r / 2) + 1) * (2 * (r / 2) + 1) + 1 := by rw [← h]
        _ = 2 * (2 * ((r / 2) * (r / 2) + r / 2) + 1) := by ring
    have hhalf : (r * r + 1) / 2 = 2 * ((r / 2) * (r / 2) + r / 2) + 1 := by omega
    rw [hhalf]; omega
  refine ⟨by
    rw [hT_eq, Nat.add_mod, hodd_c]
    have hev2 : (2 * k * (r * q)) % 2 = 0 := by rw [mul_assoc]; exact Nat.mul_mod_right 2 _
    rw [hev2], ?_⟩
  by_cases hqev : (r * q) % 2 = 0
  · left
    have h4dvd : 4 * k ∣ 2 * k * (r * q) := by
      refine ⟨(r * q) / 2, ?_⟩
      have hq2 : r * q = 2 * ((r * q) / 2) := by omega
      calc 2 * k * (r * q) = 2 * k * (2 * ((r * q) / 2)) := by conv_lhs => rw [hq2]
        _ = 4 * k * ((r * q) / 2) := by ring
    obtain ⟨m, hm⟩ := h4dvd; rw [hT_eq, hm, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod]
  · right; have hqodd : (r * q) % 2 = 1 := by omega
    have hsplit : 2 * k * (r * q) = 4 * k * ((r * q) / 2) + 2 * k := by
      have hq2 : r * q = 2 * ((r * q) / 2) + 1 := by omega
      calc 2 * k * (r * q) = 2 * k * (2 * ((r * q) / 2) + 1) := by conv_lhs => rw [hq2]
        _ = 4 * k * ((r * q) / 2) + 2 * k := by ring
    rw [hT_eq, hsplit]
    have h1 : ((r * r + 1) / 2 + (4 * k * (r * q / 2) + 2 * k)) % (4 * k) =
        ((r * r + 1) / 2 + 2 * k) % (4 * k) := by
      rw [show (r * r + 1) / 2 + (4 * k * (r * q / 2) + 2 * k) =
            4 * k * (r * q / 2) + ((r * r + 1) / 2 + 2 * k) by ring,
          Nat.mul_add_mod]
    rw [h1, Nat.add_mod, Nat.add_mod ((r * r + 1) / 2 % (4 * k)) (2 * k), Nat.mod_mod]
/-- Lemma (`lem:even-coding`, part 3): class-level dichotomy on any residue class modulo `N_k`: if -/
theorem lem_even_coding_class_dichotomy {b k n : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0)
    (_hk : 1 ≤ k) :
    ((∀ j, 1 ≤ j → j ≤ k → 2 ^ j < (affAB b n j).1) →
      ∀ j, 1 ≤ j → j ≤ k → n ≤ (T_b b)^[j] n) ∧
    ((∃ j, 1 ≤ j ∧ j ≤ k ∧ (affAB b n j).1 < 2 ^ j) →
      ∃ j, 1 ≤ j ∧ j ≤ k ∧ ((affAB b n j).2 < n → (T_b b)^[j] n < n)) := by
  constructor
  · intro hall j hj1 hjk; have haff := lem_even_affine hb2 hbeven n j
    rcases hres : affAB b n j with ⟨A, B⟩
    rw [hres] at haff; have hgt : 2 ^ j < A := by have := hall j hj1 hjk; rw [hres] at this; exact this
    have hmul : 2 ^ j * n ≤ 2 ^ j * (T_b b)^[j] n := by rw [haff.1]; nlinarith
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)
  · rintro ⟨j, hj1, hjk, hlt⟩
    refine ⟨j, hj1, hjk, fun hnB => ?_⟩
    have haff := lem_even_affine hb2 hbeven n j
    rcases hres : affAB b n j with ⟨A, B⟩
    rw [hres] at haff hlt hnB
    have hmul : 2 ^ j * (T_b b)^[j] n < 2 ^ j * n := by
      rw [haff.1]; have h1 : A + 1 ≤ 2 ^ j := by omega
      have h2 : A * n + n ≤ 2 ^ j * n := by nlinarith
      omega
    exact Nat.lt_of_mul_lt_mul_left hmul

/-! ## Proposition `prop:stopping-certs`: Decay, survival, and uniform `b = 4k` lower bound -/
section AbstractCerts
variable {α : Type*} [Fintype α]
/-- Forward tilted operator `(M_t^+ w)(z) = mult(z)^t * ∑ z', P(z, z') * w(z')`. -/
noncomputable def Mplus (P : α → α → ℝ) (mult : α → ℝ) (t : ℝ) (w : α → ℝ) (z : α) : ℝ :=
  (mult z) ^ t * ∑ z' : α, P z z' * w z'
/-- Backward tilted operator `(M_t^- w)(z) = mult(z)^{-t} * ∑ z', P(z, z') * w(z')`. -/
noncomputable def Mminus (P : α → α → ℝ) (mult : α → ℝ) (t : ℝ) (w : α → ℝ) (z : α) : ℝ :=
  (mult z) ^ (-t) * ∑ z' : α, P z z' * w z'
/-- Finite-horizon survival probability: probability from `(z, prod)` that the running product stays strictly -/
noncomputable def surviveProb (P : α → α → ℝ) (mult : α → ℝ) : ℕ → α → ℝ → ℝ
  | 0, _, _ => 1
  | n + 1, z, prod =>
    if 1 < prod * mult z then
      ∑ z' : α, P z z' * surviveProb P mult n z' (prod * mult z)
    else 0
/-- Finite-horizon ruin probability: probability from `z` that the running product drops to `≤ ρ` within `n` steps. -/
noncomputable def ruinProb (P : α → α → ℝ) (mult : α → ℝ) : ℕ → α → ℝ → ℝ
  | 0, _, _ => 0
  | n + 1, z, rho =>
    if mult z ≤ rho then 1
    else ∑ z' : α, P z z' * ruinProb P mult n z' (rho / mult z)
lemma surviveProb_nonneg {P : α → α → ℝ} (hP : ∀ z z', 0 ≤ P z z') (mult : α → ℝ) :
    ∀ n z prod, 0 ≤ surviveProb P mult n z prod := by
  intro n
  induction n with
  | zero => intro _ _; norm_num [surviveProb]
  | succ n ih =>
    intro z prod; unfold surviveProb
    split_ifs
    · exact Finset.sum_nonneg fun z' _ => mul_nonneg (hP z z') (ih z' _)
    · norm_num
lemma ruinProb_nonneg {P : α → α → ℝ} (hP : ∀ z z', 0 ≤ P z z') (mult : α → ℝ) :
    ∀ n z rho, 0 ≤ ruinProb P mult n z rho := by
  intro n
  induction n with
  | zero => intro _ _; norm_num [ruinProb]
  | succ n ih =>
    intro z rho; unfold ruinProb
    split_ifs
    · norm_num
    · exact Finset.sum_nonneg fun z' _ => mul_nonneg (hP z z') (ih z' _)
/-- Monotonicity: `surviveProb (n+1) ≤ surviveProb n` when `P` is row-stochastic. -/
lemma surviveProb_antitone {P : α → α → ℝ} (hP : ∀ z z', 0 ≤ P z z')
    (hP1 : ∀ z, ∑ z' : α, P z z' = 1) (mult : α → ℝ) :
    ∀ n z prod, surviveProb P mult (n + 1) z prod ≤ surviveProb P mult n z prod := by
  intro n
  induction n with
  | zero =>
    intro z prod; simp only [surviveProb, mul_one, hP1 z]
    split_ifs <;> norm_num
  | succ n ih =>
    intro z prod; unfold surviveProb
    split_ifs with hgt
    · exact Finset.sum_le_sum fun z' _ => mul_le_mul_of_nonneg_left (ih z' _) (hP z z')
    · exact le_refl 0
/-- Exact relation `surviveProb n z prod + ruinProb n z (1 / prod) = 1` for `prod > 0` under row-stochastic `P`. -/
lemma surviveProb_add_ruinProb {P : α → α → ℝ} (hP1 : ∀ z, ∑ z' : α, P z z' = 1)
    {mult : α → ℝ} (hmult : ∀ z, 0 < mult z) :
    ∀ n z (prod : ℝ), 0 < prod →
      surviveProb P mult n z prod + ruinProb P mult n z (1 / prod) = 1 := by
  intro n
  induction n with
  | zero => intro _ _ _; simp [surviveProb, ruinProb]
  | succ n ih =>
    intro z prod hprod; unfold surviveProb ruinProb
    have hiff : 1 < prod * mult z ↔ ¬ mult z ≤ 1 / prod := by rw [le_div_iff₀ hprod, mul_comm]; exact not_le.symm
    by_cases h1 : 1 < prod * mult z
    · have h2 : ¬ mult z ≤ 1 / prod := hiff.mp h1; simp only [h1, h2, ↓reduceIte]; rw [← Finset.sum_add_distrib]
      have hdiv : 1 / prod / mult z = 1 / (prod * mult z) := by field_simp
      simp_rw [← mul_add, hdiv, ih _ (prod * mult z) (mul_pos hprod (hmult z)), mul_one]
      exact hP1 z
    · have h2 : mult z ≤ 1 / prod := not_not.mp (mt hiff.mpr h1); simp only [h1, h2, ↓reduceIte]; ring
/-- Proposition (`prop:stopping-certs`, part 1a — Decay inequality): if `M_t^+ w ≤ λ w` with `w ≥ wmin > 0`, -/
theorem prop_stopping_certs_decay {P : α → α → ℝ} (hP : ∀ z z', 0 ≤ P z z')
    {mult : α → ℝ} (hmult : ∀ z, 0 < mult z)
    {t lam wmin : ℝ} (ht : 0 < t) (hlam : 0 < lam) (hwmin : 0 < wmin)
    {w : α → ℝ} (hw : ∀ z, wmin ≤ w z) (hsub : ∀ z, Mplus P mult t w z ≤ lam * w z)
    {μ : α → ℝ} (hμ : ∀ z, 0 ≤ μ z) (n : ℕ) :
    ∑ z : α, μ z * surviveProb P mult n z 1 ≤
      ((∑ z : α, μ z * w z) / wmin) * lam ^ n := by
  have hpoint : ∀ m z (prod : ℝ), 1 ≤ prod →
      surviveProb P mult m z prod * wmin ≤ prod ^ t * lam ^ m * w z := by
    intro m
    induction m with
    | zero =>
      intro z prod hprod; simp only [surviveProb, one_mul, pow_zero, mul_one]
      have h1 : 1 ≤ prod ^ t := Real.one_le_rpow hprod ht.le; have h2 : wmin ≤ 1 * w z := by linarith [hw z]
      exact h2.trans (mul_le_mul_of_nonneg_right h1 (by linarith [hw z]))
    | succ m ih =>
      intro z prod hprod; unfold surviveProb
      split_ifs with hgt
      · rw [Finset.sum_mul]
        have hstep : ∑ z' : α, P z z' * surviveProb P mult m z' (prod * mult z) * wmin ≤
            ∑ z' : α, P z z' * ((prod * mult z) ^ t * lam ^ m * w z') := by
          refine Finset.sum_le_sum fun z' _ => ?_
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (ih z' (prod * mult z) hgt.le) (hP z z')
        have hfact : ∑ z' : α, P z z' * ((prod * mult z) ^ t * lam ^ m * w z') =
            prod ^ t * lam ^ m * Mplus P mult t w z := by
          unfold Mplus; rw [Real.mul_rpow (by linarith) (hmult z).le, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun z' _ => by ring
        calc ∑ z' : α, P z z' * surviveProb P mult m z' (prod * mult z) * wmin
            ≤ prod ^ t * lam ^ m * Mplus P mult t w z := hfact ▸ hstep
          _ ≤ prod ^ t * lam ^ m * (lam * w z) := mul_le_mul_of_nonneg_left (hsub z) (by positivity)
          _ = prod ^ t * lam ^ (m + 1) * w z := by rw [pow_succ]; ring
      · rw [zero_mul]
        have : 0 ≤ w z := by linarith [hw z]
        positivity
  have hsum : (∑ z : α, μ z * surviveProb P mult n z 1) * wmin ≤
      (∑ z : α, μ z * w z) * lam ^ n := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun z _ => ?_
    have hz := hpoint n z 1 le_rfl; rw [Real.one_rpow, one_mul] at hz
    have hmul := mul_le_mul_of_nonneg_left hz (hμ z); linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hwmin]; exact hsum
/-- Proposition (`prop:stopping-certs`, part 1b — Supermartingale ruin bound): if `M_t^- w ≤ w` with -/
theorem prop_stopping_certs_survival {P : α → α → ℝ} (hP : ∀ z z', 0 ≤ P z z')
    (hP1 : ∀ z, ∑ z' : α, P z z' = 1)
    {mult : α → ℝ} (hmult : ∀ z, 0 < mult z)
    {t wmin : ℝ} (ht : 0 < t) (hwmin : 0 < wmin)
    {w : α → ℝ} (hw : ∀ z, wmin ≤ w z) (hsub : ∀ z, Mminus P mult t w z ≤ w z) :
    ∀ n z (rho : ℝ), 0 < rho → ruinProb P mult n z rho ≤ rho ^ t * w z / wmin := by
  intro n
  induction n with
  | zero =>
    intro z rho hrho; simp only [ruinProb]
    have : 0 ≤ w z := by linarith [hw z]
    positivity
  | succ n ih =>
    intro z rho hrho; unfold ruinProb
    split_ifs with hle
    ·
      rw [le_div_iff₀ hwmin, one_mul]
      have hge_M : (mult z) ^ (-t) * wmin ≤ Mminus P mult t w z := by
        unfold Mminus
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos (hmult z) (-t)).le
        calc wmin = ∑ z' : α, P z z' * wmin := by rw [← Finset.sum_mul, hP1 z, one_mul]
          _ ≤ ∑ z' : α, P z z' * w z' := Finset.sum_le_sum fun z' _ => mul_le_mul_of_nonneg_left (hw z') (hP z z')
      have hpow : (mult z) ^ t ≤ rho ^ t := Real.rpow_le_rpow (hmult z).le hle ht.le
      have h1 : (mult z) ^ (-t) * wmin ≤ w z := hge_M.trans (hsub z)
      have h2 := mul_le_mul_of_nonneg_left h1 (Real.rpow_pos_of_pos (hmult z) t).le
      rw [← mul_assoc, ← Real.rpow_add (hmult z), add_neg_cancel, Real.rpow_zero, one_mul] at h2
      exact h2.trans (mul_le_mul_of_nonneg_right hpow (by linarith [hw z]))
    · calc ∑ z' : α, P z z' * ruinProb P mult n z' (rho / mult z)
          ≤ ∑ z' : α, P z z' * ((rho / mult z) ^ t * w z' / wmin) :=
            Finset.sum_le_sum fun z' _ =>
              mul_le_mul_of_nonneg_left (ih z' (rho / mult z) (div_pos hrho (hmult z))) (hP z z')
        _ = rho ^ t * Mminus P mult t w z / wmin := by
            unfold Mminus; rw [Real.div_rpow hrho.le (hmult z).le, Real.rpow_neg (hmult z).le, div_eq_mul_inv]
            rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]; refine Finset.sum_congr rfl fun z' _ => by ring
        _ ≤ rho ^ t * w z / wmin := by
            apply div_le_div_of_nonneg_right _ hwmin.le; exact mul_le_mul_of_nonneg_left (hsub z) (by positivity)

end AbstractCerts

/-! ## Proposition `prop:stopping-certs`, part 3: Uniform lower bound for `b = 4k` (`k ≥ 4, k ≠ 6`) -/
/-- Transition matrix of `P_{4k}` on `Fin (2*k)`. -/
noncomputable def P4kMat (k : ℕ) (hk : 1 ≤ k) (i j : Fin (2 * k)) : ℝ :=
  (if next4kA k hk i = j then (1 / 2 : ℝ) else 0) +
  (if next4kB k hk i = j then (1 / 2 : ℝ) else 0)
lemma P4kMat_nonneg {k : ℕ} (hk : 1 ≤ k) (i j : Fin (2 * k)) : 0 ≤ P4kMat k hk i j := by
  unfold P4kMat; split_ifs <;> norm_num
lemma P4kMat_sum_one {k : ℕ} (hk : 1 ≤ k) (i : Fin (2 * k)) : ∑ j : Fin (2 * k), P4kMat k hk i j = 1 := by
  unfold P4kMat; rw [Finset.sum_add_distrib]
  simp; norm_num
lemma P4kMat_sum_mul {k : ℕ} (hk : 1 ≤ k) (f : Fin (2 * k) → ℝ) (i : Fin (2 * k)) :
    ∑ j : Fin (2 * k), P4kMat k hk i j * f j = (1 / 2 : ℝ) * (f (next4kA k hk i) + f (next4kB k hk i)) := by
  unfold P4kMat
  simp_rw [add_mul, Finset.sum_add_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]; ring
/-- Uniform stopping-certificate vector on `P_{4k}`: `w(1) = 1`, `w(r) = 2/5` for `r ≠ 1`. -/
noncomputable def w4kUnif (k : ℕ) (i : Fin (2 * k)) : ℝ := if i.val = 0 then 1 else 2 / 5
/-- Step multiplier `r / 2` on `P_{4k}`. -/
noncomputable def mult4k {k : ℕ} (i : Fin (2 * k)) : ℝ := (digit4k i : ℝ) / 2
private lemma rpow_neg_half_eq_sqrt_inv {x : ℝ} (hx : 0 < x) : x ^ (-(1 / 2 : ℝ)) = Real.sqrt x⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.sqrt_inv, ← Real.sqrt_eq_rpow]
/-- Proposition (`prop:stopping-certs`, part 3): for every `b = 4k` with `k ≥ 4` and `k ≠ 6`, `w4kUnif` satisfies -/
theorem prop_stopping_certs_4k_uniform {k : ℕ} (hk4 : 4 ≤ k) (hk6 : k ≠ 6) :
    (∀ i : Fin (2 * k), Mminus (P4kMat k (by omega)) mult4k (1 / 2 : ℝ) (w4kUnif k) i ≤ w4kUnif k i) ∧
    (∀ n : ℕ, 1 ≤ n →
      (1 / (2 * ((4 * k : ℕ) : ℝ))) *
          (∑ i : Fin (2 * k), if 1 ≤ i.val then 1 - Real.sqrt (2 / (digit4k i : ℝ)) else 0) ≤
        (1 / (2 * ((2 * k : ℕ) : ℝ))) *
          ∑ i : Fin (2 * k), surviveProb (P4kMat k (by omega)) mult4k n i 1) ∧
    0 < (1 / (2 * ((4 * k : ℕ) : ℝ))) *
          (∑ i : Fin (2 * k), if 1 ≤ i.val then 1 - Real.sqrt (2 / (digit4k i : ℝ)) else 0) := by
  have hk1 : 1 ≤ k := by omega
  have hmult_pos : ∀ i : Fin (2 * k), 0 < mult4k i := fun i => by
    unfold mult4k
    have hpos : (0 : ℝ) < (digit4k i : ℝ) := by exact_mod_cast digit4k_pos i
    exact div_pos hpos (by norm_num)
  have hAB_ne : ∀ i : Fin (2 * k), next4kA k hk1 i ≠ next4kB k hk1 i := by
    intro i hEq; have hA := digit4k_next4kA k hk1 i; have hB := digit4k_next4kB k hk1 i
    have hEqd : digit4k (next4kA k hk1 i) = digit4k (next4kB k hk1 i) := congr_arg digit4k hEq; rw [hA, hB] at hEqd
    set c := ((digit4k i * digit4k i + 1) / 2) % (4 * k); have hc_lt : c < 4 * k := Nat.mod_lt _ (by omega)
    have hB' : (((digit4k i * digit4k i + 1) / 2) + 2 * k) % (4 * k) = (c + 2 * k) % (4 * k) := by
      rw [Nat.add_mod, Nat.add_mod c (2 * k), Nat.mod_mod]
    rw [hB'] at hEqd
    by_cases hlt : c + 2 * k < 4 * k
    · rw [Nat.mod_eq_of_lt hlt] at hEqd; omega
    · have : c + 2 * k = (c - 2 * k) + 4 * k := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hEqd; omega
  have hhit0_dvd : ∀ i : Fin (2 * k),
      ((next4kA k hk1 i).val = 0 ∨ (next4kB k hk1 i).val = 0) →
      4 * k ∣ digit4k i * digit4k i - 1 := by
    intro i h0; have hodd := digit4k_odd i; have h1 : 1 ≤ digit4k i * digit4k i := by have := digit4k_pos i; nlinarith
    have hev : (digit4k i * digit4k i + 1) % 2 = 0 := by rw [Nat.add_mod, Nat.mul_mod, hodd]
    rcases h0 with hA0 | hB0
    · have hA := digit4k_next4kA k hk1 i; unfold digit4k at hA; rw [hA0] at hA; simp only [mul_zero, zero_add] at hA
      have hdvd : 4 * k ∣ (digit4k i * digit4k i + 1) / 2 - 1 := by
        have hmod : ((digit4k i * digit4k i + 1) / 2) % (4 * k) = 1 := hA.symm
        have hdiv := Nat.div_add_mod ((digit4k i * digit4k i + 1) / 2) (4 * k)
        exact ⟨((digit4k i * digit4k i + 1) / 2) / (4 * k), by omega⟩
      have hmul2 : digit4k i * digit4k i - 1 = 2 * ((digit4k i * digit4k i + 1) / 2 - 1) := by omega
      rw [hmul2]; exact dvd_mul_of_dvd_right hdvd 2
    · have hB := digit4k_next4kB k hk1 i; unfold digit4k at hB; rw [hB0] at hB; simp only [mul_zero, zero_add] at hB
      have h2k : 2 * k ∣ (digit4k i * digit4k i + 1) / 2 - 1 := by
        have h4dvd : 4 * k ∣ (digit4k i * digit4k i + 1) / 2 + 2 * k - 1 := by
          have hmod : ((digit4k i * digit4k i + 1) / 2 + 2 * k) % (4 * k) = 1 := hB.symm
          have hdiv := Nat.div_add_mod ((digit4k i * digit4k i + 1) / 2 + 2 * k) (4 * k)
          exact ⟨((digit4k i * digit4k i + 1) / 2 + 2 * k) / (4 * k), by omega⟩
        have h2kdvd : 2 * k ∣ (digit4k i * digit4k i + 1) / 2 + 2 * k - 1 := dvd_trans ⟨2, by ring⟩ h4dvd
        have heq : (digit4k i * digit4k i + 1) / 2 + 2 * k - 1 =
            ((digit4k i * digit4k i + 1) / 2 - 1) + 2 * k := by omega
        rw [heq] at h2kdvd; exact (Nat.dvd_add_left (dvd_refl (2 * k))).mp h2kdvd
      have hmul2 : digit4k i * digit4k i - 1 = 2 * ((digit4k i * digit4k i + 1) / 2 - 1) := by omega
      rw [hmul2]; obtain ⟨m, hm⟩ := h2k; exact ⟨m, by rw [hm]; ring⟩
  have hsub : ∀ i : Fin (2 * k),
      Mminus (P4kMat k hk1) mult4k (1 / 2 : ℝ) (w4kUnif k) i ≤ w4kUnif k i := by
    intro i; unfold Mminus; rw [P4kMat_sum_mul, rpow_neg_half_eq_sqrt_inv (hmult_pos i)]
    have hinv : (mult4k i)⁻¹ = 2 / (digit4k i : ℝ) := by unfold mult4k; field_simp
    rw [hinv]
    by_cases hi0 : i.val = 0
    ·
      have hd1 : (digit4k i : ℝ) = 1 := by unfold digit4k; rw [hi0]; norm_num
      have hw_sum : (1 / 2 : ℝ) * (w4kUnif k (next4kA k hk1 i) + w4kUnif k (next4kB k hk1 i)) ≤
          7 / 10 := by
        unfold w4kUnif; have hne := hAB_ne i
        split_ifs with h1 h2
        · exfalso; exact hne (Fin.ext (h1.trans h2.symm))
        · norm_num
        · norm_num
        · norm_num
      have hw_i : w4kUnif k i = 1 := by simp [w4kUnif, hi0]
      rw [hw_i, hd1, div_one]
      have hsq : Real.sqrt 2 * (7 / 10 : ℝ) ≤ 1 := by
        have h1 : (Real.sqrt 2 * (7 / 10 : ℝ)) ^ 2 ≤ 1 ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
        nlinarith [Real.sqrt_nonneg 2]
      calc Real.sqrt 2 * ((1 / 2 : ℝ) * (w4kUnif k (next4kA k hk1 i) + w4kUnif k (next4kB k hk1 i)))
          ≤ Real.sqrt 2 * (7 / 10 : ℝ) := mul_le_mul_of_nonneg_left hw_sum (Real.sqrt_nonneg _)
        _ ≤ 1 := hsq
    ·
      have hw_i : w4kUnif k i = 2 / 5 := by simp [w4kUnif, hi0]
      rw [hw_i]
      by_cases hhit : (next4kA k hk1 i).val = 0 ∨ (next4kB k hk1 i).val = 0
      ·
        have hdvd := hhit0_dvd i hhit
        have hr_ge7 : 7 ≤ digit4k i := by
          have hr_ge3 : 3 ≤ digit4k i := by unfold digit4k; omega
          have hne3 : digit4k i ≠ 3 := by
            intro h3; rw [h3] at hdvd
            have := Nat.le_of_dvd (by norm_num) hdvd; omega
          have hne5 : digit4k i ≠ 5 := by
            intro h5; rw [h5] at hdvd; have hle := Nat.le_of_dvd (by norm_num) hdvd
            have hk_cases : k = 4 ∨ k = 5 := by omega
            rcases hk_cases with rfl | rfl <;> omega
          have hodd := digit4k_odd i; omega
        have hw_sum : (1 / 2 : ℝ) * (w4kUnif k (next4kA k hk1 i) + w4kUnif k (next4kB k hk1 i)) ≤
            7 / 10 := by
          unfold w4kUnif; have hne := hAB_ne i
          split_ifs with h1 h2
          · exfalso; exact hne (Fin.ext (h1.trans h2.symm))
          · norm_num
          · norm_num
          · norm_num
        have hsqrt_le : Real.sqrt (2 / (digit4k i : ℝ)) * (7 / 10 : ℝ) ≤ 2 / 5 := by
          have h7 : (7 : ℝ) ≤ (digit4k i : ℝ) := by exact_mod_cast hr_ge7
          have h1 : (Real.sqrt (2 / (digit4k i : ℝ)) * (7 / 10 : ℝ)) ^ 2 ≤ (2 / 5 : ℝ) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]
            have h2 : 2 / (digit4k i : ℝ) ≤ 2 / 7 := by exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h7
            linarith
          nlinarith [Real.sqrt_nonneg (2 / (digit4k i : ℝ))]
        calc Real.sqrt (2 / (digit4k i : ℝ)) *
              ((1 / 2 : ℝ) * (w4kUnif k (next4kA k hk1 i) + w4kUnif k (next4kB k hk1 i)))
            ≤ Real.sqrt (2 / (digit4k i : ℝ)) * (7 / 10 : ℝ) := mul_le_mul_of_nonneg_left hw_sum (Real.sqrt_nonneg _)
          _ ≤ 2 / 5 := hsqrt_le
      ·
        push Not at hhit
        have hwA : w4kUnif k (next4kA k hk1 i) = 2 / 5 := by simp [w4kUnif, hhit.1]
        have hwB : w4kUnif k (next4kB k hk1 i) = 2 / 5 := by simp [w4kUnif, hhit.2]
        rw [hwA, hwB]
        have hr_ge3 : (3 : ℝ) ≤ (digit4k i : ℝ) := by
          have : 3 ≤ digit4k i := by unfold digit4k; omega
          exact_mod_cast this
        have hsqrt1 : Real.sqrt (2 / (digit4k i : ℝ)) ≤ 1 := by
          rw [← Real.sqrt_one]; apply Real.sqrt_le_sqrt; rw [div_le_one (by linarith)]
          linarith
        linarith
  have hw_ge : ∀ i : Fin (2 * k), (2 / 5 : ℝ) ≤ w4kUnif k i := by intro i; unfold w4kUnif; split_ifs <;> norm_num
  have hruin := prop_stopping_certs_survival (P4kMat_nonneg hk1) (P4kMat_sum_one hk1)
    hmult_pos (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 2 / 5) hw_ge hsub
  have hsurv : ∀ n : ℕ, 1 ≤ n →
      (1 / (2 * ((4 * k : ℕ) : ℝ))) *
          (∑ i : Fin (2 * k), if 1 ≤ i.val then 1 - Real.sqrt (2 / (digit4k i : ℝ)) else 0) ≤
        (1 / (2 * ((2 * k : ℕ) : ℝ))) *
          ∑ i : Fin (2 * k), surviveProb (P4kMat k hk1) mult4k n i 1 := by
    intro n hn
    cases n with
    | zero => omega
    | succ n =>
      have hfactor : (1 / (2 * ((4 * k : ℕ) : ℝ))) = (1 / (2 * ((2 * k : ℕ) : ℝ))) * (1 / 2 : ℝ) := by push_cast; ring
      rw [hfactor, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi1 : 1 ≤ i.val
      · simp only [hi1, ↓reduceIte]
        have hr_ge3 : (3 : ℝ) ≤ (digit4k i : ℝ) := by
          have : 3 ≤ digit4k i := by unfold digit4k; omega
          exact_mod_cast this
        have hgt1 : 1 < mult4k i := by unfold mult4k; linarith
        unfold surviveProb; simp only [one_mul, hgt1, ↓reduceIte]; rw [P4kMat_sum_mul]
        have hsurv_nz : ∀ j : Fin (2 * k), j.val ≠ 0 →
            1 - Real.sqrt (2 / (digit4k i : ℝ)) ≤
              surviveProb (P4kMat k hk1) mult4k n j (mult4k i) := by
          intro j hj
          have hadd := surviveProb_add_ruinProb (P4kMat_sum_one hk1) hmult_pos n j (mult4k i) (hmult_pos i)
          have hr_j := hruin n j (1 / mult4k i) (div_pos zero_lt_one (hmult_pos i))
          have hwj : w4kUnif k j = 2 / 5 := by simp [w4kUnif, hj]
          rw [hwj] at hr_j
          have hpow : (1 / mult4k i) ^ (1 / 2 : ℝ) = Real.sqrt (2 / (digit4k i : ℝ)) := by
            rw [← Real.sqrt_eq_rpow]
            congr 1; unfold mult4k; field_simp
          rw [hpow] at hr_j
          have hcancel : Real.sqrt (2 / (digit4k i : ℝ)) * (2 / 5 : ℝ) / (2 / 5 : ℝ) =
              Real.sqrt (2 / (digit4k i : ℝ)) := by ring
          rw [hcancel] at hr_j; linarith
        have hnnA := surviveProb_nonneg (P4kMat_nonneg hk1) mult4k n (next4kA k hk1 i) (mult4k i)
        have hnnB := surviveProb_nonneg (P4kMat_nonneg hk1) mult4k n (next4kB k hk1 i) (mult4k i)
        by_cases hA0 : (next4kA k hk1 i).val = 0
        · have hBnz : (next4kB k hk1 i).val ≠ 0 := fun hB0 => hAB_ne i (Fin.ext (hA0.trans hB0.symm))
          have hB := hsurv_nz _ hBnz; linarith
        · have hA := hsurv_nz _ hA0; linarith
      · simp only [hi1, ↓reduceIte, mul_zero]; exact surviveProb_nonneg (P4kMat_nonneg hk1) mult4k (n + 1) i 1
  have hpos : 0 < (1 / (2 * ((4 * k : ℕ) : ℝ))) *
      (∑ i : Fin (2 * k), if 1 ≤ i.val then 1 - Real.sqrt (2 / (digit4k i : ℝ)) else 0) := by
    apply mul_pos (by positivity)
    have hterm_nn : ∀ i : Fin (2 * k),
        0 ≤ (if 1 ≤ i.val then 1 - Real.sqrt (2 / (digit4k i : ℝ)) else 0) := by
      intro i; split_ifs with hi1
      · have hr3 : (3 : ℝ) ≤ (digit4k i : ℝ) := by
          have : 3 ≤ digit4k i := by unfold digit4k; omega
          exact_mod_cast this
        have h1 : Real.sqrt (2 / (digit4k i : ℝ)) ≤ 1 := by
          rw [← Real.sqrt_one]; apply Real.sqrt_le_sqrt
          rw [div_le_one (by linarith)]; linarith
        linarith
      · norm_num
    let i1 : Fin (2 * k) := ⟨1, by omega⟩
    have hi1_pos : 0 < (if 1 ≤ i1.val then 1 - Real.sqrt (2 / (digit4k i1 : ℝ)) else 0) := by
      simp only [i1, le_refl, ↓reduceIte, digit4k]
      have h1 : Real.sqrt (2 / ((2 * 1 + 1 : ℕ) : ℝ)) < 1 := by
        rw [← Real.sqrt_one]; apply Real.sqrt_lt_sqrt (by positivity); norm_num
      linarith
    exact Finset.sum_pos' (fun i _ => hterm_nn i) ⟨i1, Finset.mem_univ i1, hi1_pos⟩
  exact ⟨hsub, hsurv, hpos⟩

end Ouroboros
