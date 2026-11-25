module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Tactic
public import Ouroboros.Defs
@[expose] public section

/-! # Section 4: Markov chain and density-one descent (Lemmas 4–5 and Theorem 6) -/

namespace Ouroboros

/-! ## Lemma 4: After a 3 or 7 comes a 5, and converse -/
/-- Lemma 4: If `n` and `m` are odd and `d(n) * n + 1 = 2^v * m` (`v ≥ 1`), then `m` ends in `5` if and only if -/
theorem lemma_after_3_or_7_is_5 {n m v : ℕ}
    (hn : n % 2 = 1) (hm : m % 2 = 1)
    (heq : d n * n + 1 = 2 ^ v * m) :
    m % 10 = 5 ↔ n % 10 = 3 ∨ n % 10 = 7 := by
  have hm5 : m % 10 = 5 ↔ 5 ∣ m := by omega
  have hcop : Nat.Coprime 5 (2 ^ v) := by exact (show Nat.Coprime 5 2 by decide).pow_right v
  have h5mul : 5 ∣ m ↔ 5 ∣ (2 ^ v * m) := by
    constructor
    · intro h; exact dvd_mul_of_dvd_right h _
    · intro h; exact hcop.dvd_of_dvd_mul_left h
  rw [hm5, h5mul, ← heq, Nat.dvd_iff_mod_eq_zero]; have hd : d n % 5 = n % 5 := by unfold d; omega
  have hmod : (d n * n + 1) % 5 = ((n % 5) * (n % 5) + 1) % 5 := by simp [Nat.add_mod, Nat.mul_mod, hd]
  rw [hmod]; have h5 : n % 5 = (n % 10) % 5 := by omega
  have h10 : n % 10 < 10 := Nat.mod_lt n (by omega)
  rw [h5]
  interval_cases h : n % 10 <;> omega

/-! ## Lemma 5: Coding modulo `5 * 2^k` -/
/-- Odd last digit determined by residue `s (mod 5)`: `δ(0) = 5, δ(1) = 1, δ(2) = 7, δ(3) = 3, δ(4) = 9`. -/
def delta (s : Fin 5) : ℕ :=
  match s.val with
  | 0 => 5
  | 1 => 1
  | 2 => 7
  | 3 => 3
  | _ => 9
lemma delta_odd (s : Fin 5) : delta s % 2 = 1 := by fin_cases s <;> decide
lemma delta_eq_d {n : ℕ} (hn : n % 2 = 1) : delta ⟨n % 5, Nat.mod_lt n (by omega)⟩ = d n := by
  have h5 : n % 5 = (n % 10) % 5 := by omega
  have h10 : n % 10 < 10 := Nat.mod_lt n (by omega)
  unfold delta d; simp only [h5]
  interval_cases h : n % 10 <;> first | omega | rfl
/-- Next mod-5 state under one shortcut step with parity bit `b` (`true` = odd). -/
def stepState (s : Fin 5) (b : Bool) : Fin 5 :=
  if b then ⟨(3 * (delta s * s.val + 1)) % 5, Nat.mod_lt _ (by omega)⟩
  else ⟨(3 * s.val) % 5, Nat.mod_lt _ (by omega)⟩
/-- Multiplier of one shortcut step from state `s` with parity bit `b`. -/
def stepMult (s : Fin 5) (b : Bool) : ℕ := if b then delta s else 1
lemma stepMult_odd (s : Fin 5) (b : Bool) : stepMult s b % 2 = 1 := by
  cases b
  · simp [stepMult]
  · simp [stepMult, delta_odd]
/-- One step of `T` updates `n % 5` according to `stepState`. -/
lemma T_mod5 (n : ℕ) : T n % 5 = (stepState ⟨n % 5, Nat.mod_lt n (by omega)⟩ (decide (n % 2 = 1))).val := by
  by_cases hev : n % 2 = 0
  · have hdec : decide (n % 2 = 1) = false := by simp [hev]
    rw [hdec]; simp only [T, hev, ↓reduceIte, stepState, Bool.false_eq_true]; have h2 : 2 * (n / 2) = n := by omega
    have hmul : (3 * (2 * (n / 2))) % 5 = (3 * n) % 5 := by rw [h2]
    have h6 : (3 * (2 * (n / 2))) % 5 = (n / 2) % 5 := by omega
    rw [← h6, hmul]; simp [Nat.mul_mod]
  · have hodd : n % 2 = 1 := by omega
    have hdec : decide (n % 2 = 1) = true := by simp [hodd]
    rw [hdec]; simp only [T, hev, ↓reduceIte, stepState]
    have hd : d n = delta ⟨n % 5, Nat.mod_lt n (by omega)⟩ := (delta_eq_d hodd).symm
    rw [hd]; have hdo := delta_odd ⟨n % 5, Nat.mod_lt n (by omega)⟩
    have hmul_odd : (delta ⟨n % 5, Nat.mod_lt n (by omega)⟩ * n) % 2 = 1 := by rw [Nat.mul_mod, hdo, hodd]
    have h2 : 2 * ((delta ⟨n % 5, Nat.mod_lt n (by omega)⟩ * n + 1) / 2) =
        delta ⟨n % 5, Nat.mod_lt n (by omega)⟩ * n + 1 := by omega
    have h6 : ((delta ⟨n % 5, Nat.mod_lt n (by omega)⟩ * n + 1) / 2) % 5 =
        (3 * (delta ⟨n % 5, Nat.mod_lt n (by omega)⟩ * n + 1)) % 5 := by omega
    rw [h6]; simp [Nat.mul_mod, Nat.add_mod]
/-- One step of `T` satisfies `2 * T n = stepMult * n + (if odd then 1 else 0)`. -/
lemma two_mul_T (n : ℕ) :
    2 * T n = stepMult ⟨n % 5, Nat.mod_lt n (by omega)⟩ (decide (n % 2 = 1)) * n +
      (if decide (n % 2 = 1) then 1 else 0) := by
  by_cases hev : n % 2 = 0
  · simp [T, stepMult, hev]; omega
  · have hodd : n % 2 = 1 := by omega
    have hd := delta_eq_d hodd; have hdo := delta_odd ⟨n % 5, Nat.mod_lt n (by omega)⟩
    have hmul_odd : (delta ⟨n % 5, Nat.mod_lt n (by omega)⟩ * n) % 2 = 1 := by rw [Nat.mul_mod, hdo, hodd]
    have hdec : decide (n % 2 = 1) = true := by simp [hodd]
    simp only [T, hev, ↓reduceIte, hdec, stepMult]; rw [← hd]
    generalize delta ⟨n % 5, Nat.mod_lt n (by omega)⟩ * n = x at hmul_odd ⊢
    omega
/-- Recursive triple `(s_k, A_k, B_k)` for a length-`k` parity word `e : Fin k → Bool` starting at state -/
def codeTriple : (k : ℕ) → Fin 5 → (Fin k → Bool) → Fin 5 × ℕ × ℕ
  | 0, s, _ => (s, 1, 0)
  | k + 1, s, e =>
    let (sk, ak, bk) := codeTriple k s (fun j => e j.castSucc)
    let b := e (Fin.last k)
    (stepState sk b, stepMult sk b * ak, stepMult sk b * bk + (if b then 2 ^ k else 0))

def codeState (k : ℕ) (s : Fin 5) (e : Fin k → Bool) : Fin 5 := (codeTriple k s e).1
def codeA (k : ℕ) (s : Fin 5) (e : Fin k → Bool) : ℕ := (codeTriple k s e).2.1
def codeB (k : ℕ) (s : Fin 5) (e : Fin k → Bool) : ℕ := (codeTriple k s e).2.2
/-- Parity vector of the first `k` shortcut iterates of `n`. -/
def parityVec (k : ℕ) (n : ℕ) : Fin k → Bool := fun j => decide (T^[j.val] n % 2 = 1)
/-- Coding map `n ↦ (n % 5, e_0(n), ..., e_{k-1}(n))`. -/
def codingMap (k : ℕ) (n : ℕ) : Fin 5 × (Fin k → Bool) := (⟨n % 5, Nat.mod_lt n (by omega)⟩, parityVec k n)
lemma codeA_odd (k : ℕ) (s : Fin 5) (e : Fin k → Bool) : codeA k s e % 2 = 1 := by
  induction k with
  | zero => simp [codeA, codeTriple]
  | succ k ih =>
    simp only [codeA, codeTriple]; have h1 := stepMult_odd (codeTriple k s (fun j => e j.castSucc)).1 (e (Fin.last k))
    have h2 := ih (fun j => e j.castSucc); simp only [codeA] at h2; rw [Nat.mul_mod, h1, h2]
/-- Lemma 5 (affine and mod-5 law): for every `k` and `n`, `T^[k] n % 5 = s_k` and `2^k * T^[k] n = A_k * n + B_k`. -/
theorem lemma_coding_affine (k n : ℕ) :
    T^[k] n % 5 = (codeState k (codingMap k n).1 (codingMap k n).2).val ∧
    2 ^ k * T^[k] n = codeA k (codingMap k n).1 (codingMap k n).2 * n +
      codeB k (codingMap k n).1 (codingMap k n).2 := by
  induction k with
  | zero => simp [codeState, codeA, codeB, codeTriple, codingMap]
  | succ k ih =>
    obtain ⟨hs, haff⟩ := ih
    have hinit : (fun j : Fin k => (codingMap (k + 1) n).2 j.castSucc) = (codingMap k n).2 := by funext j; rfl
    have hs_eq : (codingMap (k + 1) n).1 = (codingMap k n).1 := rfl
    set tr := codeTriple k (codingMap k n).1 (codingMap k n).2
    have hlast : (codingMap (k + 1) n).2 (Fin.last k) = decide (T^[k] n % 2 = 1) := rfl
    have hst : (⟨T^[k] n % 5, Nat.mod_lt _ (by omega)⟩ : Fin 5) = tr.1 := by ext; exact hs
    constructor
    · rw [Function.iterate_succ_apply', T_mod5, hst]; simp only [codeState, codeTriple, hs_eq, hinit, hlast]; rfl
    · rw [Function.iterate_succ_apply', pow_succ, mul_assoc]; rw [two_mul_T (T^[k] n), hst]
      simp only [codeA, codeB, codeTriple, hs_eq, hinit, hlast]
      have haff' : 2 ^ k * T^[k] n = tr.2.1 * n + tr.2.2 := haff; set m := stepMult tr.1 (decide (T^[k] n % 2 = 1))
      calc 2 ^ k * (m * T^[k] n + if decide (T^[k] n % 2 = 1) then 1 else 0)
          = m * (2 ^ k * T^[k] n) + (if decide (T^[k] n % 2 = 1) then 2 ^ k else 0) := by
              split_ifs <;> ring
        _ = m * (tr.2.1 * n + tr.2.2) + (if decide (T^[k] n % 2 = 1) then 2 ^ k else 0) := by rw [haff']
        _ = m * tr.2.1 * n + (m * tr.2.2 + if decide (T^[k] n % 2 = 1) then 2 ^ k else 0) := by ring
/-- Shifting `n` by `5 * 2^k * t` preserves the length-`k` code and shifts `T^[k] n` by `5 * A_k * t`. -/
lemma coding_shift (k n t : ℕ) :
    codingMap k (n + 5 * 2 ^ k * t) = codingMap k n ∧
    T^[k] (n + 5 * 2 ^ k * t) = T^[k] n + 5 * codeA k (codingMap k n).1 (codingMap k n).2 * t := by
  induction k generalizing t with
  | zero =>
    constructor
    · ext
      · simp [codingMap]
      · rename_i j; exact Fin.elim0 j
    · simp [codeA, codeTriple]
  | succ k ih =>
    have hshift : n + 5 * 2 ^ (k + 1) * t = n + 5 * 2 ^ k * (2 * t) := by ring
    obtain ⟨hc, htk⟩ := ih (2 * t); rw [← hshift] at hc htk
    have hmod2 : T^[k] (n + 5 * 2 ^ (k + 1) * t) % 2 = T^[k] n % 2 := by
      have hev : 5 * codeA k (codingMap k n).1 (codingMap k n).2 * (2 * t) =
          2 * (5 * codeA k (codingMap k n).1 (codingMap k n).2 * t) := by ring
      rw [htk, hev]; omega
    have hc_succ : codingMap (k + 1) (n + 5 * 2 ^ (k + 1) * t) = codingMap (k + 1) n := by
      refine Prod.ext ?_ ?_
      · ext; simp only [codingMap]; have h5 : n + 5 * 2 ^ (k + 1) * t = n + 5 * (2 ^ (k + 1) * t) := by ring
        rw [h5, Nat.add_mul_mod_self_left]
      · funext j
        refine Fin.lastCases ?_ ?_ j
        · simp [codingMap, parityVec, hmod2]
        · intro i
          have := congr_fun (congr_arg Prod.snd hc) i
          simpa [codingMap, parityVec] using this
    refine ⟨hc_succ, ?_⟩
    obtain ⟨_, haff1⟩ := lemma_coding_affine (k + 1) (n + 5 * 2 ^ (k + 1) * t)
    obtain ⟨_, haff2⟩ := lemma_coding_affine (k + 1) n; rw [hc_succ] at haff1
    set A := codeA (k + 1) (codingMap (k + 1) n).1 (codingMap (k + 1) n).2
    set B := codeB (k + 1) (codingMap (k + 1) n).1 (codingMap (k + 1) n).2
    have hpow : 2 ^ (k + 1) * T^[k + 1] (n + 5 * 2 ^ (k + 1) * t) =
        2 ^ (k + 1) * (T^[k + 1] n + 5 * A * t) := by
      calc 2 ^ (k + 1) * T^[k + 1] (n + 5 * 2 ^ (k + 1) * t)
          = A * (n + 5 * 2 ^ (k + 1) * t) + B := haff1
        _ = (A * n + B) + 2 ^ (k + 1) * (5 * A * t) := by ring
        _ = 2 ^ (k + 1) * T^[k + 1] n + 2 ^ (k + 1) * (5 * A * t) := by rw [← haff2]
        _ = 2 ^ (k + 1) * (T^[k + 1] n + 5 * A * t) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hpow
/-- `codingMap k` depends only on `n % (5 * 2^k)`. -/
theorem lemma_coding_mod (k n : ℕ) : codingMap k n = codingMap k (n % (5 * 2 ^ k)) := by
  conv_lhs => rw [← Nat.mod_add_div n (5 * 2 ^ k)]
  exact (coding_shift k (n % (5 * 2 ^ k)) (n / (5 * 2 ^ k))).1
/-- Injectivity of `codingMap k` on `{0, ..., 5 * 2^k - 1}`. -/
lemma coding_inj_lt (k : ℕ) : ∀ a b : ℕ, a < 5 * 2 ^ k → b < 5 * 2 ^ k → codingMap k a = codingMap k b → a = b := by
  induction k with
  | zero =>
    intro a b ha hb h; have h5 := congr_arg (fun p => p.1.val) h; simp only [codingMap] at h5
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h5
    exact h5
  | succ k ih =>
    intro a b ha hb h
    have hprev : codingMap k a = codingMap k b := by
      refine Prod.ext (by simpa [codingMap] using congr_arg Prod.fst h) ?_
      funext j
      have := congr_fun (congr_arg Prod.snd h) j.castSucc
      simpa [codingMap, parityVec] using this
    have hmod_eq : a % (5 * 2 ^ k) = b % (5 * 2 ^ k) := by
      apply ih _ _ (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
      rw [← lemma_coding_mod k a, ← lemma_coding_mod k b]; exact hprev
    have ha_lt : a / (5 * 2 ^ k) < 2 :=
      Nat.div_lt_of_lt_mul (by linarith [show 5 * 2 ^ (k + 1) = 2 * (5 * 2 ^ k) by ring])
    have hb_lt : b / (5 * 2 ^ k) < 2 :=
      Nat.div_lt_of_lt_mul (by linarith [show 5 * 2 ^ (k + 1) = 2 * (5 * 2 ^ k) by ring])
    have ha_div : a / (5 * 2 ^ k) = 0 ∨ a / (5 * 2 ^ k) = 1 := by generalize a / (5 * 2 ^ k) = qa at ha_lt ⊢; omega
    have hb_div : b / (5 * 2 ^ k) = 0 ∨ b / (5 * 2 ^ k) = 1 := by generalize b / (5 * 2 ^ k) = qb at hb_lt ⊢; omega
    have hlast : decide (T^[k] a % 2 = 1) = decide (T^[k] b % 2 = 1) := by
      have := congr_fun (congr_arg Prod.snd h) (Fin.last k)
      simpa [codingMap, parityVec] using this
    set r := a % (5 * 2 ^ k)
    have ha_eq : a = r + 5 * 2 ^ k * (a / (5 * 2 ^ k)) := by have := Nat.mod_add_div a (5 * 2 ^ k); omega
    have hb_eq : b = r + 5 * 2 ^ k * (b / (5 * 2 ^ k)) := by have := Nat.mod_add_div b (5 * 2 ^ k); omega
    have hta := (coding_shift k r (a / (5 * 2 ^ k))).2; have htb := (coding_shift k r (b / (5 * 2 ^ k))).2
    rw [← ha_eq] at hta; rw [← hb_eq] at htb; have hAodd := codeA_odd k (codingMap k r).1 (codingMap k r).2
    have hdiv_eq : a / (5 * 2 ^ k) = b / (5 * 2 ^ k) := by
      rcases ha_div with ha0 | ha1 <;> rcases hb_div with hb0 | hb1
      · omega
      · rw [ha0] at hta; rw [hb1] at htb; simp only [mul_zero, add_zero, mul_one] at hta htb; rw [hta, htb] at hlast
        have hne : (T^[k] r + 5 * codeA k (codingMap k r).1 (codingMap k r).2) % 2 ≠
            T^[k] r % 2 := by omega
        by_cases hp : T^[k] r % 2 = 1
        · simp [hp] at hlast; omega
        · simp [hp] at hlast; omega
      · rw [ha1] at hta; rw [hb0] at htb; simp only [mul_zero, add_zero, mul_one] at hta htb; rw [hta, htb] at hlast
        have hne : (T^[k] r + 5 * codeA k (codingMap k r).1 (codingMap k r).2) % 2 ≠
            T^[k] r % 2 := by omega
        by_cases hp : T^[k] r % 2 = 1
        · simp [hp] at hlast; omega
        · simp [hp] at hlast; omega
      · omega
    rw [ha_eq, hb_eq, hdiv_eq]
/-- Lemma 5 (bijection): `codingMap k` induces a bijection from `Fin (5 * 2^k)` onto `Fin 5 × (Fin k → Bool)`. -/
theorem lemma_coding_bijective (k : ℕ) : Function.Bijective (fun r : Fin (5 * 2 ^ k) => codingMap k r.val) := by
  have hinj : Function.Injective (fun r : Fin (5 * 2 ^ k) => codingMap k r.val) := by
    intro a b h; ext; exact coding_inj_lt k a.val b.val a.isLt b.isLt h
  have hcard : Fintype.card (Fin (5 * 2 ^ k)) = Fintype.card (Fin 5 × (Fin k → Bool)) := by
    simp [Fintype.card_fin, Fintype.card_prod, Fintype.card_pi, Fintype.card_bool]
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩

/-! ## Theorem 6: Density-one descent via Collatz–Wielandt certificate -/
/-- The positive certificate vector `u` at `t = 0.11`. -/
noncomputable def certU (s : Fin 5) : ℝ :=
  match s.val with
  | 0 => 1
  | 1 => 837748 / 1000000
  | 2 => 965453 / 1000000
  | 3 => 964025 / 1000000
  | _ => 944908 / 1000000
lemma certU_pos (s : Fin 5) : 0 < certU s := by fin_cases s <;> norm_num [certU]
lemma certU_ge_min (s : Fin 5) : (837748 / 1000000 : ℝ) ≤ certU s := by fin_cases s <;> norm_num [certU]
lemma certU_sum : ∑ s : Fin 5, certU s = 4712134 / 1000000 := by
  rw [Fin.sum_univ_five]
  norm_num [certU]
/-- Helper: `x^(11/100) ≤ r` follows from the integer-exponent inequality `x^11 ≤ r^100`. -/
lemma rpow_11_100_le {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) (h : x ^ (11 : ℕ) ≤ r ^ (100 : ℕ)) :
    x ^ ((11 : ℝ) / 100) ≤ r := by
  have h100 : (x ^ ((11 : ℝ) / 100)) ^ (100 : ℕ) ≤ r ^ (100 : ℕ) := by
    rw [← Real.rpow_natCast (x ^ ((11 : ℝ) / 100)) 100, ← Real.rpow_mul hx]
    have hexp : ((11 : ℝ) / 100) * (100 : ℕ) = (11 : ℕ) := by norm_num
    rw [hexp, Real.rpow_natCast]; exact h
  exact le_of_pow_le_pow_left₀ (by norm_num) hr h100
lemma rpow_half_le : ((1 / 2 : ℝ)) ^ ((11 : ℝ) / 100) ≤ 9265881 / 10000000 :=
  rpow_11_100_le (by norm_num) (by norm_num) (by norm_num)
lemma rpow_3_2_le : ((3 / 2 : ℝ)) ^ ((11 : ℝ) / 100) ≤ 10456109 / 10000000 :=
  rpow_11_100_le (by norm_num) (by norm_num) (by norm_num)
lemma rpow_5_2_le : ((5 / 2 : ℝ)) ^ ((11 : ℝ) / 100) ≤ 11060466 / 10000000 :=
  rpow_11_100_le (by norm_num) (by norm_num) (by norm_num)
lemma rpow_7_2_le : ((7 / 2 : ℝ)) ^ ((11 : ℝ) / 100) ≤ 11477506 / 10000000 :=
  rpow_11_100_le (by norm_num) (by norm_num) (by norm_num)
lemma rpow_9_2_le : ((9 / 2 : ℝ)) ^ ((11 : ℝ) / 100) ≤ 11799224 / 10000000 :=
  rpow_11_100_le (by norm_num) (by norm_num) (by norm_num)
/-- Collatz–Wielandt step inequality `(M_t u)_s ≤ 0.996423 * u_s` for every state `s ∈ Fin 5`. -/
lemma cert_step_le (s : Fin 5) :
    (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ ((11 : ℝ) / 100)) * certU (stepState s false) +
    (1 / 2 : ℝ) * (((delta s : ℝ) / 2) ^ ((11 : ℝ) / 100)) * certU (stepState s true) ≤
      (996423 / 1000000 : ℝ) * certU s := by
  have h0 := rpow_half_le; have h3 := rpow_3_2_le; have h5 := rpow_5_2_le; have h7 := rpow_7_2_le
  have h9 := rpow_9_2_le
  fin_cases s <;> (simp only [stepState, delta, certU]; norm_num at *; linarith)
/-- Splitting off the first bit of a length-`(k + 1)` word in `codeTriple`. -/
lemma codeTriple_cons (k : ℕ) (s : Fin 5) (e : Fin (k + 1) → Bool) :
    codeState (k + 1) s e = codeState k (stepState s (e 0)) (fun j => e j.succ) ∧
    codeA (k + 1) s e =
      stepMult s (e 0) * codeA k (stepState s (e 0)) (fun j => e j.succ) := by
  induction k with
  | zero => simp [codeState, codeA, codeTriple]
  | succ k ih =>
    have ih' := ih (fun j => e j.castSucc)
    have h0 : Fin.castSucc (0 : Fin (k + 1)) = (0 : Fin (k + 2)) := rfl
    have htail : (fun j : Fin k => e j.succ.castSucc) =
        (fun j : Fin k => e j.castSucc.succ) := by
      funext j; rfl
    have hl : (Fin.last k).succ = Fin.last (k + 1) := rfl; obtain ⟨hs, hA⟩ := ih'; rw [h0, htail] at hs hA
    constructor
    · change stepState (codeState (k + 1) s (fun j => e j.castSucc)) (e (Fin.last (k + 1))) =
          stepState (codeState k (stepState s (e 0)) (fun j => e j.castSucc.succ))
            (e (Fin.last k).succ)
      rw [hs, hl]
    · change stepMult (codeState (k + 1) s (fun j => e j.castSucc)) (e (Fin.last (k + 1))) *
          codeA (k + 1) s (fun j => e j.castSucc) =
          stepMult s (e 0) *
            (stepMult (codeState k (stepState s (e 0)) (fun j => e j.castSucc.succ))
              (e (Fin.last k).succ) *
              codeA k (stepState s (e 0)) (fun j => e j.castSucc.succ))
      rw [hs, hA, hl]; ring
/-- Weighted sum over all `2^k` parity words from state `s`: -/
lemma weighted_moment_bound (k : ℕ) (s : Fin 5) :
    ((2 : ℝ) ^ k)⁻¹ *
      ∑ e : Fin k → Bool,
        (((codeA k s e : ℝ) / (2 : ℝ) ^ k) ^ ((11 : ℝ) / 100) * certU (codeState k s e)) ≤
      (996423 / 1000000 : ℝ) ^ k * certU s := by
  induction k generalizing s with
  | zero => simp [codeA, codeState, codeTriple]
  | succ k ih =>
    let eqv : (Fin (k + 1) → Bool) ≃ Bool × (Fin k → Bool) :=
      { toFun := fun e => (e 0, fun j => e j.succ)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := fun e => by
          funext j; refine Fin.cases ?_ ?_ j <;> simp
        right_inv := fun ⟨b, f⟩ => by simp }
    rw [Fintype.sum_equiv eqv _ (fun p =>
      (((stepMult s p.1 * codeA k (stepState s p.1) p.2 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1)) ^
        ((11 : ℝ) / 100) * certU (codeState k (stepState s p.1) p.2))]
    · rw [Fintype.sum_prod_type, Fintype.sum_bool]
      have hsplit : ∀ b : Bool,
          ∑ f : Fin k → Bool,
            (((stepMult s b * codeA k (stepState s b) f : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1)) ^
              ((11 : ℝ) / 100) * certU (codeState k (stepState s b) f) =
          (((stepMult s b : ℝ) / 2) ^ ((11 : ℝ) / 100)) *
            ∑ f : Fin k → Bool,
              (((codeA k (stepState s b) f : ℝ) / (2 : ℝ) ^ k) ^ ((11 : ℝ) / 100) *
                certU (codeState k (stepState s b) f)) := by
        intro b; rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        have hfrac : (((stepMult s b * codeA k (stepState s b) f : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1)) =
            ((stepMult s b : ℝ) / 2) * ((codeA k (stepState s b) f : ℝ) / (2 : ℝ) ^ k) := by
          push_cast; rw [pow_succ]; ring
        rw [hfrac, Real.mul_rpow (by positivity) (by positivity)]
        ring
      rw [hsplit true, hsplit false]
      have hpow : ((2 : ℝ) ^ (k + 1))⁻¹ = (1 / 2 : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by rw [pow_succ]; field_simp
      rw [hpow]; have htrue := ih (stepState s true); have hfalse := ih (stepState s false)
      have hc_t : 0 ≤ ((stepMult s true : ℝ) / 2) ^ ((11 : ℝ) / 100) := by positivity
      have hc_f : 0 ≤ ((stepMult s false : ℝ) / 2) ^ ((11 : ℝ) / 100) := by positivity
      have hstep := cert_step_le s
      have hmt : (stepMult s true : ℝ) = delta s := by simp [stepMult]
      have hmf : (stepMult s false : ℝ) = 1 := by simp [stepMult]
      rw [hmt, hmf]
      have h1 : (1 / 2 : ℝ) * ((2 : ℝ) ^ k)⁻¹ *
          ((((delta s : ℝ) / 2) ^ ((11 : ℝ) / 100) *
              ∑ f : Fin k → Bool,
                (((codeA k (stepState s true) f : ℝ) / (2 : ℝ) ^ k) ^ ((11 : ℝ) / 100) *
                  certU (codeState k (stepState s true) f))) +
            (((1 : ℝ) / 2) ^ ((11 : ℝ) / 100) *
              ∑ f : Fin k → Bool,
                (((codeA k (stepState s false) f : ℝ) / (2 : ℝ) ^ k) ^ ((11 : ℝ) / 100) *
                  certU (codeState k (stepState s false) f)))) ≤
          (996423 / 1000000 : ℝ) ^ k *
            ((1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ ((11 : ℝ) / 100)) * certU (stepState s false) +
             (1 / 2 : ℝ) * (((delta s : ℝ) / 2) ^ ((11 : ℝ) / 100)) * certU (stepState s true)) := by
        have ht' : ((delta s : ℝ) / 2) ^ ((11 : ℝ) / 100) *
            (((2 : ℝ) ^ k)⁻¹ *
              ∑ f : Fin k → Bool,
                (((codeA k (stepState s true) f : ℝ) / (2 : ℝ) ^ k) ^ ((11 : ℝ) / 100) *
                  certU (codeState k (stepState s true) f))) ≤
            ((delta s : ℝ) / 2) ^ ((11 : ℝ) / 100) *
              ((996423 / 1000000 : ℝ) ^ k * certU (stepState s true)) :=
          mul_le_mul_of_nonneg_left htrue (by positivity)
        have hf' : ((1 / 2 : ℝ) ^ ((11 : ℝ) / 100)) *
            (((2 : ℝ) ^ k)⁻¹ *
              ∑ f : Fin k → Bool,
                (((codeA k (stepState s false) f : ℝ) / (2 : ℝ) ^ k) ^ ((11 : ℝ) / 100) *
                  certU (codeState k (stepState s false) f))) ≤
            ((1 / 2 : ℝ) ^ ((11 : ℝ) / 100)) *
              ((996423 / 1000000 : ℝ) ^ k * certU (stepState s false)) :=
          mul_le_mul_of_nonneg_left hfalse (by positivity)
        linarith
      calc _ ≤ (996423 / 1000000 : ℝ) ^ k *
                ((1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ ((11 : ℝ) / 100)) * certU (stepState s false) +
                 (1 / 2 : ℝ) * (((delta s : ℝ) / 2) ^ ((11 : ℝ) / 100)) * certU (stepState s true)) := h1
        _ ≤ (996423 / 1000000 : ℝ) ^ k * ((996423 / 1000000 : ℝ) * certU s) :=
              mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = (996423 / 1000000 : ℝ) ^ (k + 1) * certU s := by rw [pow_succ]; ring
    · intro e; obtain ⟨hs, hA⟩ := codeTriple_cons k s e; simp only [eqv, Equiv.coe_fn_mk]; rw [hs, hA]
/-- Number of bad codes `(s, e)` of length `k` with `codeA k s e ≥ 2^k`. -/
def badCodeCount (k : ℕ) : ℕ := (Finset.univ.filter (fun p : Fin 5 × (Fin k → Bool) => 2 ^ k ≤ codeA k p.1 p.2)).card
/-- Fraction of bad codes modulo `5 * 2^k` is at most `1.124953 * 0.996423^k`. -/
theorem bad_code_fraction_le (k : ℕ) :
    (badCodeCount k : ℝ) / (5 * 2 ^ k : ℝ) ≤
      (1124953 / 1000000 : ℝ) * (996423 / 1000000 : ℝ) ^ k := by
  have hmin_pos : (0 : ℝ) < 837748 / 1000000 := by norm_num
  have h1 : (837748 / 1000000 : ℝ) * (badCodeCount k : ℝ) ≤
      ∑ p : Fin 5 × (Fin k → Bool),
        (((codeA k p.1 p.2 : ℝ) / (2 : ℝ) ^ k) ^ ((11 : ℝ) / 100) * certU (codeState k p.1 p.2)) := by
    have hcard : (837748 / 1000000 : ℝ) * (badCodeCount k : ℝ) =
        ∑ _p ∈ Finset.univ.filter (fun p : Fin 5 × (Fin k → Bool) => 2 ^ k ≤ codeA k p.1 p.2),
          (837748 / 1000000 : ℝ) := by
      simp [badCodeCount, mul_comm]
    rw [hcard]
    calc ∑ _p ∈ Finset.univ.filter (fun p : Fin 5 × (Fin k → Bool) => 2 ^ k ≤ codeA k p.1 p.2),
            (837748 / 1000000 : ℝ)
        ≤ ∑ p ∈ Finset.univ.filter (fun p : Fin 5 × (Fin k → Bool) => 2 ^ k ≤ codeA k p.1 p.2),
            (((codeA k p.1 p.2 : ℝ) / (2 : ℝ) ^ k) ^ ((11 : ℝ) / 100) *
              certU (codeState k p.1 p.2)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hbad : 2 ^ k ≤ codeA k p.1 p.2 := (Finset.mem_filter.mp hp).2
          have hge1 : (1 : ℝ) ≤ (codeA k p.1 p.2 : ℝ) / (2 : ℝ) ^ k := by
            rw [one_le_div (by positivity)]
            exact_mod_cast hbad
          have hrpow1 : (1 : ℝ) ≤ ((codeA k p.1 p.2 : ℝ) / (2 : ℝ) ^ k) ^ ((11 : ℝ) / 100) :=
            Real.one_le_rpow hge1 (by norm_num)
          have hu := certU_ge_min (codeState k p.1 p.2); nlinarith
      _ ≤ ∑ p : Fin 5 × (Fin k → Bool),
            (((codeA k p.1 p.2 : ℝ) / (2 : ℝ) ^ k) ^ ((11 : ℝ) / 100) *
              certU (codeState k p.1 p.2)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro p _ _; exact mul_nonneg (by positivity) (certU_pos _).le
  have hsum : ((2 : ℝ) ^ k)⁻¹ *
      ∑ p : Fin 5 × (Fin k → Bool),
        (((codeA k p.1 p.2 : ℝ) / (2 : ℝ) ^ k) ^ ((11 : ℝ) / 100) * certU (codeState k p.1 p.2)) ≤
      (4712134 / 1000000 : ℝ) * (996423 / 1000000 : ℝ) ^ k := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    calc ∑ s : Fin 5, ((2 : ℝ) ^ k)⁻¹ *
            ∑ e : Fin k → Bool,
              (((codeA k s e : ℝ) / (2 : ℝ) ^ k) ^ ((11 : ℝ) / 100) * certU (codeState k s e))
        ≤ ∑ s : Fin 5, (996423 / 1000000 : ℝ) ^ k * certU s := Finset.sum_le_sum fun s _ => weighted_moment_bound k s
      _ = (996423 / 1000000 : ℝ) ^ k * ∑ s : Fin 5, certU s := by rw [← Finset.mul_sum]
      _ = (4712134 / 1000000 : ℝ) * (996423 / 1000000 : ℝ) ^ k := by rw [certU_sum]; ring
  have h2 : (837748 / 1000000 : ℝ) * ((badCodeCount k : ℝ) / (2 : ℝ) ^ k) ≤
      (4712134 / 1000000 : ℝ) * (996423 / 1000000 : ℝ) ^ k := by
    have : (837748 / 1000000 : ℝ) * ((badCodeCount k : ℝ) / (2 : ℝ) ^ k) =
        ((2 : ℝ) ^ k)⁻¹ * ((837748 / 1000000 : ℝ) * (badCodeCount k : ℝ)) := by ring
    rw [this]; exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans hsum
  have hC : (4712134 / 1000000 : ℝ) / (5 * (837748 / 1000000 : ℝ)) ≤ 1124953 / 1000000 := by norm_num
  have h3 : (badCodeCount k : ℝ) / (5 * 2 ^ k : ℝ) ≤
      ((4712134 / 1000000 : ℝ) / (5 * (837748 / 1000000 : ℝ))) * (996423 / 1000000 : ℝ) ^ k := by
    have hpos5 : (0 : ℝ) < 5 * (837748 / 1000000 : ℝ) := by norm_num
    have h4 : (5 * (837748 / 1000000 : ℝ)) * ((badCodeCount k : ℝ) / (5 * 2 ^ k : ℝ)) =
        (837748 / 1000000 : ℝ) * ((badCodeCount k : ℝ) / (2 : ℝ) ^ k) := by field_simp
    have h5 : (badCodeCount k : ℝ) / (5 * 2 ^ k : ℝ) ≤
        ((4712134 / 1000000 : ℝ) * (996423 / 1000000 : ℝ) ^ k) / (5 * (837748 / 1000000 : ℝ)) := by
      rw [le_div_iff₀ hpos5]; linarith
    have h6 : ((4712134 / 1000000 : ℝ) * (996423 / 1000000 : ℝ) ^ k) /
        (5 * (837748 / 1000000 : ℝ)) =
        ((4712134 / 1000000 : ℝ) / (5 * (837748 / 1000000 : ℝ))) * (996423 / 1000000 : ℝ) ^ k := by
      ring
    exact h5.trans_eq h6
  exact h3.trans (mul_le_mul_of_nonneg_right hC (by positivity))
/-- The exceptional set `E_k = {n ≥ 2 | ∀ 1 ≤ j ≤ k, T^[j] n ≥ n}`. -/
def E_k (k : ℕ) : Set ℕ :=
  {n | 2 ≤ n ∧ ∀ j, 1 ≤ j → j ≤ k → n ≤ T^[j] n}
open Classical in
/-- Count of integers in `[1, N]` belonging to `S`. -/
noncomputable def countUpTo (S : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => n ∈ S)).card
/-- Finite-`N` upper bound for `E_k`: for every `k ≥ 1`, there is a constant `M_k` such that for all `N ≥ 1`, -/
lemma countUpTo_Ek_le (k : ℕ) (hk : 1 ≤ k) :
    ∃ M : ℕ, ∀ N : ℕ,
      countUpTo (E_k k) N ≤ badCodeCount k * (N / (5 * 2 ^ k) + 1) + M := by
  classical
  let m := 5 * 2 ^ k; have hm_pos : 0 < m := by positivity
  let M := Finset.univ.sup (fun p : Fin 5 × (Fin k → Bool) => codeB k p.1 p.2)
  refine ⟨M, fun N => ?_⟩
  let badRes : Finset (Fin m) :=
    Finset.univ.filter (fun r : Fin m => 2 ^ k ≤ codeA k (codingMap k r.val).1 (codingMap k r.val).2)
  have hbadCard : badRes.card = badCodeCount k := by
    let eqv : Fin m ≃ Fin 5 × (Fin k → Bool) :=
      Equiv.ofBijective (fun r : Fin m => codingMap k r.val) (lemma_coding_bijective k)
    have : badCodeCount k = (Finset.univ.filter (fun r : Fin m =>
        2 ^ k ≤ codeA k (eqv r).1 (eqv r).2)).card := by
      unfold badCodeCount
      symm
      exact Finset.card_bij (fun r _ => eqv r)
        (fun r hr => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢; exact hr)
        (fun a _ b _ h => eqv.injective h)
        (fun p hp => ⟨eqv.symm p, by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; simpa using hp, eqv.apply_symm_apply p⟩)
    rw [this]; rfl
  let S := (Finset.Icc 1 N).filter (fun n => n ∈ E_k k)
  let Sbad := S.filter (fun n => 2 ^ k ≤ codeA k (codingMap k n).1 (codingMap k n).2)
  let Sgood := S.filter (fun n => ¬ 2 ^ k ≤ codeA k (codingMap k n).1 (codingMap k n).2)
  have hsplit : S.card = Sbad.card + Sgood.card := by
    rw [← Finset.card_filter_add_card_filter_not (s := S)
      (p := fun n => 2 ^ k ≤ codeA k (codingMap k n).1 (codingMap k n).2)]
  have hgood_sub : Sgood ⊆ Finset.Icc 1 M := by
    intro n hn; simp only [Sgood, S, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨hn1, _⟩, ⟨_, hEk⟩⟩, hgood⟩ := hn
    have hlt : codeA k (codingMap k n).1 (codingMap k n).2 < 2 ^ k := by omega
    have hle : n ≤ T^[k] n := hEk k hk le_rfl; have haff := (lemma_coding_affine k n).2
    have hBn : n ≤ codeB k (codingMap k n).1 (codingMap k n).2 := by
      have : 2 ^ k * n ≤ codeA k (codingMap k n).1 (codingMap k n).2 * n +
          codeB k (codingMap k n).1 (codingMap k n).2 := by
        rw [← haff]; exact Nat.mul_le_mul_left _ hle
      have hdiff : (codeA k (codingMap k n).1 (codingMap k n).2 + 1) * n ≤ 2 ^ k * n := Nat.mul_le_mul_right n hlt
      nlinarith
    have hBM : codeB k (codingMap k n).1 (codingMap k n).2 ≤ M :=
      Finset.le_sup (f := fun p : Fin 5 × (Fin k → Bool) => codeB k p.1 p.2) (Finset.mem_univ _)
    exact Finset.mem_Icc.mpr ⟨hn1, hBn.trans hBM⟩
  have hgood_card : Sgood.card ≤ M := by
    calc Sgood.card ≤ (Finset.Icc 1 M).card := Finset.card_le_card hgood_sub
      _ = M := by simp
  have hbad_card : Sbad.card ≤ badRes.card * (N / m + 1) := by
    rw [← Finset.card_range (N / m + 1), ← Finset.card_product]
    refine Finset.card_le_card_of_injOn
      (fun n => (⟨n % m, Nat.mod_lt n hm_pos⟩, n / m)) ?_ ?_
    · intro n hn
      have hn' : (1 ≤ n ∧ n ≤ N) ∧ n ∈ E_k k ∧ 2 ^ k ≤ codeA k (codingMap k n).1 (codingMap k n).2 := by
        have h1 := Finset.mem_filter.mp hn; have h2 := Finset.mem_filter.mp h1.1
        exact ⟨Finset.mem_Icc.mp h2.1, h2.2, h1.2⟩
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · simp only [badRes, Finset.mem_filter, Finset.mem_univ, true_and]; rw [← lemma_coding_mod k n]; exact hn'.2.2
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hn'.1.2))
    · intro a _ b _ h; have h1 : a % m = b % m := congr_arg (fun p => p.1.val) h
      have h2 : a / m = b / m := congr_arg Prod.snd h; have ha := Nat.div_add_mod a m; have hb := Nat.div_add_mod b m
      rw [← ha, ← hb, h1, h2]
  change S.card ≤ badCodeCount k * (N / m + 1) + M; rw [hsplit, ← hbadCard]; omega
/-- Theorem 6 (quantitative exceptional-set bound): for every `k ≥ 1` and every `ε > 0`, for all sufficiently -/
theorem thm_terras_bound (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (countUpTo (E_k k) N : ℝ) / (N : ℝ) ≤
        (1124953 / 1000000 : ℝ) * (996423 / 1000000 : ℝ) ^ k + ε := by
  obtain ⟨M, hM⟩ := countUpTo_Ek_le k hk; obtain ⟨N₀, hN₀⟩ := exists_nat_gt (((badCodeCount k + M : ℕ) : ℝ) / ε)
  refine ⟨max 1 N₀, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_left hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hNgt : ((badCodeCount k + M : ℕ) : ℝ) / ε < (N : ℝ) :=
    lt_of_lt_of_le hN₀ (by exact_mod_cast le_of_max_le_right hN)
  have herr : ((badCodeCount k + M : ℕ) : ℝ) / (N : ℝ) < ε := by rwa [div_lt_iff₀ hNpos, ← div_lt_iff₀' hε]
  have hcnt : (countUpTo (E_k k) N : ℝ) ≤
      (badCodeCount k : ℝ) * ((N : ℝ) / (5 * 2 ^ k : ℝ)) + ((badCodeCount k + M : ℕ) : ℝ) := by
    have hdiv : ((N / (5 * 2 ^ k) : ℕ) : ℝ) ≤ (N : ℝ) / (5 * 2 ^ k : ℝ) := by
      have h0 : ((N / (5 * 2 ^ k) : ℕ) : ℝ) ≤ (N : ℝ) / ((5 * 2 ^ k : ℕ) : ℝ) := Nat.cast_div_le
      push_cast at h0; exact h0
    have hnat : (countUpTo (E_k k) N : ℝ) ≤
        (badCodeCount k : ℝ) * (((N / (5 * 2 ^ k) : ℕ) : ℝ) + 1) + (M : ℝ) := by
      exact_mod_cast hM N
    push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) (badCodeCount k)]
  have hfrac : (countUpTo (E_k k) N : ℝ) / (N : ℝ) ≤
      (badCodeCount k : ℝ) / (5 * 2 ^ k : ℝ) + ((badCodeCount k + M : ℕ) : ℝ) / (N : ℝ) := by
    rw [div_le_iff₀ hNpos]
    calc (countUpTo (E_k k) N : ℝ)
        ≤ (badCodeCount k : ℝ) * ((N : ℝ) / (5 * 2 ^ k : ℝ)) + ((badCodeCount k + M : ℕ) : ℝ) := hcnt
      _ = ((badCodeCount k : ℝ) / (5 * 2 ^ k : ℝ) + ((badCodeCount k + M : ℕ) : ℝ) / (N : ℝ)) *
            (N : ℝ) := by field_simp
  have hbad := bad_code_fraction_le k; linarith
/-- The set of integers `n ≥ 2` with no `f`-iterate strictly below `n`. -/
def NoDescent : Set ℕ :=
  {n | 2 ≤ n ∧ ∀ m : ℕ, 1 ≤ m → n ≤ f^[m] n}
lemma noDescent_subset_Ek (k : ℕ) : NoDescent ⊆ E_k k := by
  intro n ⟨hn2, hno⟩
  refine ⟨hn2, fun j hj1 _ => ?_⟩
  obtain ⟨m, hm⟩ := T_iter_is_f_iter j n; rw [hm]
  by_cases hm0 : m = 0
  · subst hm0; simp
  · exact hno m (by omega)
/-- Theorem 6 (natural density 1 descent): the set of `n ≥ 2` with no `f`-iterate strictly below `n` has natural -/
theorem thm_terras_density_one (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (countUpTo NoDescent N : ℝ) / (N : ℝ) ≤ ε := by
  have hlt1 : (996423 / 1000000 : ℝ) < 1 := by norm_num
  have hnn : (0 : ℝ) ≤ 996423 / 1000000 := by norm_num
  have htend : Filter.Tendsto (fun k : ℕ => (1124953 / 1000000 : ℝ) * (996423 / 1000000 : ℝ) ^ k)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hnn hlt1).const_mul (1124953 / 1000000 : ℝ)
  have hev := (Metric.tendsto_atTop.mp htend) (ε / 2) (by linarith)
  obtain ⟨k0, hk0⟩ := hev; let k := max 1 k0
  have hsmall : (1124953 / 1000000 : ℝ) * (996423 / 1000000 : ℝ) ^ k < ε / 2 := by
    have h := hk0 k (le_max_right 1 k0); rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h
    exact h
  obtain ⟨N₀, hN₀⟩ := thm_terras_bound k (le_max_left 1 k0) (ε / 2) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  have hsub : countUpTo NoDescent N ≤ countUpTo (E_k k) N := by
    classical
    unfold countUpTo
    refine Finset.card_le_card fun n hn => ?_
    simp only [Finset.mem_filter] at hn ⊢; exact ⟨hn.1, noDescent_subset_Ek k hn.2⟩
  have hdiv : (countUpTo NoDescent N : ℝ) / (N : ℝ) ≤ (countUpTo (E_k k) N : ℝ) / (N : ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hsub) (by positivity)
  linarith [hN₀ N hN]

end Ouroboros
