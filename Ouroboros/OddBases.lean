module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Tactic
public import Ouroboros.Defs
@[expose] public section

/-! # Odd Bases: Trapdoor, Cylinders, Runaway Classes, and Densities -/

namespace Ouroboros
open Filter Topology

/-! ## Helper: f_b steps and divisibility -/
lemma f_b_even {b n : ℕ} (h : n % 2 = 0) : f_b b n = n / 2 := by unfold f_b; simp [h]
lemma f_b_odd {b n : ℕ} (h : n % 2 = 1) : f_b b n = (n % b) * n + 1 := by
  unfold f_b
  have : n % 2 ≠ 0 := by omega
  simp [this]
lemma f_b_two_pow_mul (b v m : ℕ) : (f_b b)^[v] (2 ^ v * m) = m := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [Function.iterate_succ_apply, pow_succ, mul_assoc, mul_comm 2 m, ← mul_assoc]
    have hev : (2 ^ v * m * 2) % 2 = 0 := by omega
    rw [f_b_even hev, Nat.mul_div_cancel _ (by omega)]
    exact ih
lemma nat_div_mod_two (a k : ℕ) : (a / 2) % k = (a % (2 * k)) / 2 := by
  by_cases hk : k = 0
  · subst hk; simp
  · have hk0 : 0 < k := Nat.pos_of_ne_zero hk; have h1 := Nat.div_add_mod a (2 * k)
    have h1' : a = 2 * (k * (a / (2 * k))) + a % (2 * k) := by linarith
    have h2 : a / 2 = k * (a / (2 * k)) + (a % (2 * k)) / 2 := by omega
    have hlt : (a % (2 * k)) / 2 < k := by have := Nat.mod_lt a (by omega : 0 < 2 * k); omega
    rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

/-! ## Theorem `thm:odd-trapdoor`: Odd-base zero-digit trapdoor -/
/-- Set of positive integers whose `f_b`-orbit hits a multiple of `b`. -/
def ZSet (b : ℕ) : Set ℕ := {n | 1 ≤ n ∧ ∃ j : ℕ, b ∣ (f_b b)^[j] n}
/-- Set of positive integers whose `f_b`-orbit reaches `1`. -/
def RSet (b : ℕ) : Set ℕ := {n | 1 ≤ n ∧ Reaches (f_b b) n 1}
/-- Roots of `x^2 + 1 = 0` in `ZMod b`. -/
noncomputable def trapRoots (b : ℕ) [NeZero b] : Finset (ZMod b) := Finset.univ.filter fun x : ZMod b => x ^ 2 + 1 = 0
/-- Theorem `thm:odd-trapdoor`(1): For odd `b ≥ 3`, every positive multiple `n = 2^v * m` of `b` (`m` odd) -/
theorem thm_odd_trapdoor_multiple {b v m : ℕ} (hb3 : 3 ≤ b) (hm_odd : m % 2 = 1)
    (hbm : b ∣ m) :
    (f_b b)^[v] (2 ^ v * m) = m ∧
    (f_b b)^[v + 1] (2 ^ v * m) = 1 ∧
    (∀ j ≤ v, b ∣ (f_b b)^[j] (2 ^ v * m) ∧ (f_b b)^[j] (2 ^ v * m) ≠ 1) := by
  have hv : (f_b b)^[v] (2 ^ v * m) = m := f_b_two_pow_mul b v m
  have hv1 : (f_b b)^[v + 1] (2 ^ v * m) = 1 := by
    rw [Function.iterate_succ_apply', hv, f_b_odd hm_odd, Nat.mod_eq_zero_of_dvd hbm]; simp
  refine ⟨hv, hv1, fun j hj => ?_⟩
  have hsplit : 2 ^ v * m = 2 ^ j * (2 ^ (v - j) * m) := by rw [← mul_assoc, ← pow_add, show j + (v - j) = v by omega]
  rw [hsplit, f_b_two_pow_mul]; have hdvd : b ∣ 2 ^ (v - j) * m := dvd_mul_of_dvd_right hbm _
  have hne1 : 2 ^ (v - j) * m ≠ 1 := by
    intro h1; rw [h1] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  exact ⟨hdvd, hne1⟩
/-- Theorem `thm:odd-trapdoor`(2): For odd `b ≥ 3`, if `b ∤ n` and `b ∣ f_b b n`, then `n` is odd and -/
theorem thm_odd_trapdoor_entry {b n : ℕ} (_hb_odd : b % 2 = 1)
    (hnd : ¬ b ∣ n) (hfd : b ∣ f_b b n) :
    n % 2 = 1 ∧ (n * n + 1) % b = 0 := by
  have hn_odd : n % 2 = 1 := by
    by_contra hev
    have h0 : n % 2 = 0 := by omega
    rw [f_b_even h0] at hfd; have hn2 : n = 2 * (n / 2) := by omega
    exact hnd (by rw [hn2]; exact dvd_mul_of_dvd_right hfd 2)
  rw [f_b_odd hn_odd] at hfd; have hmod : ((n % b) * n + 1) % b = 0 := Nat.mod_eq_zero_of_dvd hfd
  have heq : ((n % b) * n + 1) % b = (n * n + 1) % b := by simp [Nat.add_mod, Nat.mul_mod]
  exact ⟨hn_odd, heq ▸ hmod⟩
/-- Theorem `thm:odd-trapdoor`(3): If a prime `p ≡ 3 (mod 4)` divides odd `b ≥ 3`, then `x^2 + 1 ≡ 0 (mod b)` has -/
theorem thm_odd_trapdoor_rootless {b p : ℕ} (hb_odd : b % 2 = 1)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3) (hpb : p ∣ b) :
    (∀ x : ℕ, (x * x + 1) % b ≠ 0) ∧
    (∀ n : ℕ, n ∈ ZSet b ↔ 1 ≤ n ∧ b ∣ n) := by
  have : Fact p.Prime := ⟨hp⟩
  have hno_root : ∀ x : ℕ, (x * x + 1) % b ≠ 0 := by
    intro x h0; have hbdvd : b ∣ x * x + 1 := Nat.dvd_of_mod_eq_zero h0
    have hpdvd : p ∣ x * x + 1 := dvd_trans hpb hbdvd
    have hzp : ((x * x + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpdvd
    push_cast at hzp
    have hsq : (x : ZMod p) ^ 2 = -1 := by rw [sq]; exact eq_neg_of_add_eq_zero_left hzp
    have hiff := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp ⟨(x : ZMod p), by rw [← sq]; exact hsq.symm⟩
    exact hiff hp3
  refine ⟨hno_root, fun n => ⟨?_, fun ⟨hn1, hbn⟩ => ⟨hn1, 0, by simpa using hbn⟩⟩⟩
  rintro ⟨hn1, j, hj⟩
  refine ⟨hn1, ?_⟩
  induction j with
  | zero => simpa using hj
  | succ j ih =>
    rw [Function.iterate_succ_apply'] at hj
    by_cases hd : b ∣ (f_b b)^[j] n
    · exact ih hd
    · exfalso; have ⟨_, hroot⟩ := thm_odd_trapdoor_entry hb_odd hd hj; exact hno_root _ hroot
/-- Helper: For an odd prime `p ≡ 1 (mod 4)` and `e ≥ 1`, there are exactly `2` roots of `x^2 + 1 = 0` in -/
lemma card_trapRoots_prime_pow {p e : ℕ} (hp : Nat.Prime p) (hp1 : p % 4 = 1) (he : 1 ≤ e) :
    letI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
    (trapRoots (p ^ e)).card = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  induction e with
  | zero => omega
  | succ e ih =>
    cases e with
    | zero =>
      have : NeZero p := ⟨hp.ne_zero⟩
      have hp_card : (trapRoots p).card = 2 := by
        obtain ⟨r, hr⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
        have hr' : r ^ 2 = -1 := by rw [sq]; exact hr.symm
        have hne : r ≠ -r := by
          intro h
          have h2r : (2 : ZMod p) * r = 0 := by
            have : r + r = 0 := by rw [← eq_neg_iff_add_eq_zero]; exact h
            rw [two_mul]; exact this
          rcases mul_eq_zero.mp h2r with h2 | hr0
          · have hp_dvd2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2)
            have := Nat.le_of_dvd (by omega) hp_dvd2
            omega
          · rw [hr0, zero_pow (by norm_num)] at hr'
            have : (1 : ZMod p) = 0 := by
              have := congr_arg Neg.neg hr'
              simpa using this.symm
            exact one_ne_zero this
        have hset : trapRoots p = {r, -r} := by
          ext x
          simp only [trapRoots, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro hx
            have hfac : (x - r) * (x + r) = 0 := by
              have : (x - r) * (x + r) = x ^ 2 - r ^ 2 := by ring
              rw [this, hr', sub_neg_eq_add]; exact hx
            rcases mul_eq_zero.mp hfac with h | h
            · left; exact sub_eq_zero.mp h
            · right; exact eq_neg_of_add_eq_zero_left h
          · rintro (rfl | rfl)
            · rw [hr']; ring
            · rw [neg_sq, hr']; ring
        rw [hset, Finset.card_pair hne]
      have hsame : ∀ (a c : ℕ) [NeZero a] [NeZero c], a = c →
          (trapRoots a).card = (trapRoots c).card := by
        rintro a _ _ _ rfl; rfl
      exact (hsame (p ^ 1) p (pow_one p)).trans hp_card
    | succ e =>
      have he1 : 1 ≤ e + 1 := by omega
      have hprev := ih he1
      have : NeZero (p ^ (e + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      have : NeZero (p ^ (e + 2)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      let proj : ZMod (p ^ (e + 2)) →+* ZMod (p ^ (e + 1)) :=
        ZMod.castHom (pow_dvd_pow p (by omega : e + 1 ≤ e + 2)) (ZMod (p ^ (e + 1)))
      have hproj_mem : ∀ x ∈ trapRoots (p ^ (e + 2)), proj x ∈ trapRoots (p ^ (e + 1)) := by
        intro x hx; simp only [trapRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        have := congr_arg proj hx
        simpa [map_add, map_pow, map_one, map_zero] using this
      suffices hbij : (trapRoots (p ^ (e + 2))).card = (trapRoots (p ^ (e + 1))).card by
        exact hbij.trans hprev
      refine Finset.card_bij (fun x _ => proj x) hproj_mem ?_ ?_
      · intro x hx y hy hxy; simp only [trapRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
        set a := x.val; set b := y.val
        have hxa : (a : ZMod (p ^ (e + 2))) = x := ZMod.natCast_zmod_val x
        have hyb : (b : ZMod (p ^ (e + 2))) = y := ZMod.natCast_zmod_val y
        have hdvd_diff : (p ^ (e + 1) : ℤ) ∣ (a : ℤ) - (b : ℤ) := by
          have hcast : ((a : ℤ) : ZMod (p ^ (e + 1))) = ((b : ℤ) : ZMod (p ^ (e + 1))) := by
            have h1 : proj x = (a : ZMod (p ^ (e + 1))) := by rw [← hxa]; simp [proj]
            have h2 : proj y = (b : ZMod (p ^ (e + 1))) := by rw [← hyb]; simp [proj]
            simpa [h1, h2] using hxy
          rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd] at hcast; exact_mod_cast hcast
        obtain ⟨t, ht⟩ := hdvd_diff
        have hsq_x : (p ^ (e + 2) : ℤ) ∣ (a : ℤ) ^ 2 + 1 := by
          have : (((a : ℤ) ^ 2 + 1 : ℤ) : ZMod (p ^ (e + 2))) = 0 := by push_cast; rw [hxa]; exact hx
          exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
        have hsq_y : (p ^ (e + 2) : ℤ) ∣ (b : ℤ) ^ 2 + 1 := by
          have : (((b : ℤ) ^ 2 + 1 : ℤ) : ZMod (p ^ (e + 2))) = 0 := by push_cast; rw [hyb]; exact hy
          exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
        have hdiff_sq : (p ^ (e + 2) : ℤ) ∣ (a : ℤ) ^ 2 - (b : ℤ) ^ 2 := by
          have : (a : ℤ) ^ 2 - (b : ℤ) ^ 2 = ((a : ℤ) ^ 2 + 1) - ((b : ℤ) ^ 2 + 1) := by ring
          rw [this]; exact dvd_sub hsq_x hsq_y
        have hprod : (a : ℤ) ^ 2 - (b : ℤ) ^ 2 = (p ^ (e + 1) : ℤ) * (t * ((a : ℤ) + (b : ℤ))) := by
          calc (a : ℤ) ^ 2 - (b : ℤ) ^ 2 = ((a : ℤ) - (b : ℤ)) * ((a : ℤ) + (b : ℤ)) := by ring
            _ = (p ^ (e + 1) : ℤ) * t * ((a : ℤ) + (b : ℤ)) := by rw [ht]
            _ = (p ^ (e + 1) : ℤ) * (t * ((a : ℤ) + (b : ℤ))) := by ring
        rw [hprod, show (p ^ (e + 2) : ℤ) = (p ^ (e + 1) : ℤ) * (p : ℤ) by ring] at hdiff_sq
        have hpe_ne : (p ^ (e + 1) : ℤ) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
        have hpt : (p : ℤ) ∣ t * ((a : ℤ) + (b : ℤ)) := (mul_dvd_mul_iff_left hpe_ne).mp hdiff_sq
        have hnotp_sum : ¬ (p : ℤ) ∣ (a : ℤ) + (b : ℤ) := by
          intro hsum
          have hp_ab : (p : ℤ) ∣ (a : ℤ) - (b : ℤ) := dvd_trans (dvd_pow_self (p : ℤ) (by omega : e + 1 ≠ 0)) ⟨t, ht⟩
          have hp_2a : (p : ℤ) ∣ 2 * (a : ℤ) := by
            have : 2 * (a : ℤ) = ((a : ℤ) + (b : ℤ)) + ((a : ℤ) - (b : ℤ)) := by ring
            rw [this]; exact dvd_add hsum hp_ab
          have hp_a : (p : ℤ) ∣ (a : ℤ) := by
            rcases (Int.prime_iff_natAbs_prime.mpr (by simpa using hp)).dvd_mul.mp hp_2a with h2 | ha
            · have : p ∣ 2 := Int.ofNat_dvd.mp h2
              have := Nat.le_of_dvd (by omega) this; omega
            · exact ha
          have hp_a21 : (p : ℤ) ∣ (a : ℤ) ^ 2 + 1 := dvd_trans (dvd_pow_self (p : ℤ) (by omega : e + 2 ≠ 0)) hsq_x
          have hp_1 : (p : ℤ) ∣ 1 := by
            have hp_a2 : (p : ℤ) ∣ (a : ℤ) ^ 2 := dvd_pow hp_a (by norm_num)
            have : (1 : ℤ) = ((a : ℤ) ^ 2 + 1) - (a : ℤ) ^ 2 := by ring
            rw [this]; exact dvd_sub hp_a21 hp_a2
          have := Int.le_of_dvd (by norm_num) hp_1
          omega
        have hpt' : (p : ℤ) ∣ t := by
          rcases (Int.prime_iff_natAbs_prime.mpr (by simpa using hp)).dvd_mul.mp hpt with h | h
          · exact h
          · exact absurd h hnotp_sum
        obtain ⟨u, hu⟩ := hpt'
        have hfull : (p ^ (e + 2) : ℤ) ∣ (a : ℤ) - (b : ℤ) := by
          rw [ht, hu]
          refine ⟨u, ?_⟩
          ring
        have hzero : (((a : ℤ) - (b : ℤ) : ℤ) : ZMod (p ^ (e + 2))) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast hfull)
        push_cast at hzero; rw [hxa, hyb] at hzero; exact sub_eq_zero.mp hzero
      · intro y hy; simp only [trapRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hy; set a := y.val
        have hya : (a : ZMod (p ^ (e + 1))) = y := ZMod.natCast_zmod_val y
        have hdiv : p ^ (e + 1) ∣ a ^ 2 + 1 := by
          have : ((a ^ 2 + 1 : ℕ) : ZMod (p ^ (e + 1))) = 0 := by push_cast; rw [hya]; exact hy
          exact (ZMod.natCast_eq_zero_iff _ _).mp this
        obtain ⟨q, hq⟩ := hdiv
        have h2a_ne : (2 : ZMod p) * (a : ZMod p) ≠ 0 := by
          intro h0; have hpd : p ∣ 2 * a := (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast; exact h0)
          rcases hp.dvd_mul.mp hpd with h2 | ha
          · have := Nat.le_of_dvd (by omega) h2; omega
          · have hp_a21 : p ∣ a ^ 2 + 1 := dvd_trans (dvd_pow_self p (by omega : e + 1 ≠ 0)) ⟨q, hq⟩
            have hp_a2 : p ∣ a ^ 2 := dvd_pow ha (by norm_num)
            have hp_1 : p ∣ 1 := (Nat.dvd_add_right hp_a2).mp hp_a21
            have := Nat.le_of_dvd (by omega) hp_1; omega
        let t_z : ZMod p := -((q : ZMod p) * ((2 : ZMod p) * (a : ZMod p))⁻¹)
        let t : ℕ := t_z.val
        let x : ZMod (p ^ (e + 2)) := ((a + t * p ^ (e + 1) : ℕ) : ZMod (p ^ (e + 2)))
        refine ⟨x, ?_, ?_⟩
        · simp only [trapRoots, Finset.mem_filter, Finset.mem_univ, true_and]
          have hmod_p : ((q + 2 * a * t : ℕ) : ZMod p) = 0 := by
            push_cast
            have ht : (t : ZMod p) = t_z := ZMod.natCast_zmod_val t_z
            rw [ht]; simp only [t_z]
            have hcancel : (2 : ZMod p) * (a : ZMod p) * (-((q : ZMod p) *
                ((2 : ZMod p) * (a : ZMod p))⁻¹)) = -(q : ZMod p) := by
              rw [mul_neg, ← mul_assoc, mul_comm ((2 : ZMod p) * (a : ZMod p)) (q : ZMod p),
                  mul_assoc, mul_inv_cancel₀ h2a_ne, mul_one]
            rw [hcancel, add_neg_cancel]
          have hp_qt : p ∣ q + 2 * a * t := (ZMod.natCast_eq_zero_iff _ _).mp hmod_p
          have hexp : (a + t * p ^ (e + 1)) ^ 2 + 1 =
              p ^ (e + 1) * (q + 2 * a * t + t ^ 2 * p ^ (e + 1)) := by
            calc (a + t * p ^ (e + 1)) ^ 2 + 1
                = (a ^ 2 + 1) + 2 * a * t * p ^ (e + 1) + t ^ 2 * (p ^ (e + 1)) ^ 2 := by ring
              _ = p ^ (e + 1) * q + 2 * a * t * p ^ (e + 1) + t ^ 2 * (p ^ (e + 1)) ^ 2 := by rw [hq]
              _ = p ^ (e + 1) * (q + 2 * a * t + t ^ 2 * p ^ (e + 1)) := by ring
          have hdvd_full : p ^ (e + 2) ∣ (a + t * p ^ (e + 1)) ^ 2 + 1 := by
            rw [hexp, show p ^ (e + 2) = p ^ (e + 1) * p by ring]
            refine Nat.mul_dvd_mul_left (p ^ (e + 1)) ?_
            exact dvd_add hp_qt (dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) _)
          have : (((a + t * p ^ (e + 1)) ^ 2 + 1 : ℕ) : ZMod (p ^ (e + 2))) = 0 :=
            (ZMod.natCast_eq_zero_iff _ _).mpr hdvd_full
          simpa [x] using this
        · have hpx : proj x = ((a + t * p ^ (e + 1) : ℕ) : ZMod (p ^ (e + 1))) :=
            map_natCast proj (a + t * p ^ (e + 1))
          rw [hpx]; push_cast
          have h0 : ((p : ZMod (p ^ (e + 1))) ^ (e + 1)) = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
          rw [h0, mul_zero, add_zero, hya]
/-- Multiplicativity of `|trapRoots b|` on coprime moduli via CRT. -/
lemma card_trapRoots_mul {m n : ℕ} [NeZero m] [NeZero n] (hcop : Nat.Coprime m n) :
    letI : NeZero (m * n) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
    (trapRoots (m * n)).card = (trapRoots m).card * (trapRoots n).card := by
  have : NeZero (m * n) := ⟨mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  let e := ZMod.chineseRemainder hcop; rw [← Finset.card_product]
  refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
  · intro x hx
    simp only [trapRoots, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product] at hx ⊢
    have h0 : e (x ^ 2 + 1) = 0 := by rw [hx, map_zero]
    constructor
    · have := congr_arg Prod.fst h0; simpa using this
    · have := congr_arg Prod.snd h0; simpa using this
  · intro x _ y _ hxy; exact e.injective hxy
  · intro p hp
    simp only [trapRoots, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
    simp only [trapRoots, Finset.mem_filter, Finset.mem_univ, true_and]; apply e.injective
    rw [map_add, map_pow, map_one, map_zero, e.apply_symm_apply]; exact Prod.ext hp.1 hp.2
/-- Theorem `thm:odd-trapdoor`(4a): If odd `b ≥ 3` has all prime factors `≡ 1 (mod 4)`, then `|S(b)| = 2^{ω(b)}` -/
theorem thm_odd_trapdoor_rooted {b : ℕ} (hb3 : 3 ≤ b) (_hb_odd : b % 2 = 1)
    (hprimes : ∀ p ∈ b.primeFactors, p % 4 = 1) :
    letI : NeZero b := ⟨by omega⟩
    (trapRoots b).card = 2 ^ b.primeFactors.card ∧
    (∀ n : ℕ, n % 2 = 1 → (n : ZMod b) ∈ trapRoots b → b ∣ f_b b n) := by
  have : NeZero b := ⟨by omega⟩
  have hstep : ∀ n : ℕ, n % 2 = 1 → (n : ZMod b) ∈ trapRoots b → b ∣ f_b b n := by
    intro n hn_odd hmem; simp only [trapRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [f_b_odd hn_odd]
    have h1 : ((n * n + 1 : ℕ) : ZMod b) = 0 := by push_cast; rw [← sq]; exact hmem
    have h2 : b ∣ n * n + 1 := (ZMod.natCast_eq_zero_iff _ _).mp h1
    have h3 : ((n % b) * n + 1) % b = (n * n + 1) % b := by simp [Nat.add_mod, Nat.mul_mod]
    exact Nat.dvd_of_mod_eq_zero (h3.trans (Nat.mod_eq_zero_of_dvd h2))
  refine ⟨?_, hstep⟩
  suffices hgen : ∀ k : ℕ, ∀ m : ℕ, 1 ≤ m → m.primeFactors.card = k →
      (∀ p ∈ m.primeFactors, p % 4 = 1) →
      ∀ [NeZero m], (trapRoots m).card = 2 ^ k by
    exact hgen b.primeFactors.card b (by omega) rfl hprimes
  intro k
  induction k with
  | zero =>
    intro m hm hcard _ _
    have hm1 : m = 1 := by
      by_contra hne
      have hex := Nat.exists_prime_and_dvd hne; obtain ⟨p, hp, hpm⟩ := hex
      have hmem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpm, by omega⟩
      have hpos : 0 < m.primeFactors.card := Finset.card_pos.mpr ⟨p, hmem⟩; omega
    subst hm1
    have hfilt : trapRoots 1 = Finset.univ := by
      ext x; simp only [trapRoots, Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_true_intro (Subsingleton.elim (x ^ 2 + 1) (0 : ZMod 1))
    rw [hfilt, Finset.card_univ, ZMod.card 1, pow_zero]
  | succ k ih =>
    intro m hm hcard hmp _; have hne_empty : m.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p, hp_mem⟩ := hne_empty; have hp : Nat.Prime p := (Nat.mem_primeFactors.mp hp_mem).1
    have hpm : p ∣ m := (Nat.mem_primeFactors.mp hp_mem).2.1; have hp1 : p % 4 = 1 := hmp p hp_mem
    let e := m.factorization p
    have he1 : 1 ≤ e := by
      have : p ^ 1 ∣ m := by simpa using hpm
      exact (hp.pow_dvd_iff_le_factorization (by omega)).mp this
    have hpe_dvd : p ^ e ∣ m := Nat.ordProj_dvd m p; let m' := m / p ^ e
    have hm_eq : m = p ^ e * m' := (Nat.mul_div_cancel' hpe_dvd).symm
    have hm'_pos : 1 ≤ m' := by
      have : p ^ e ≤ m := Nat.le_of_dvd (by omega) hpe_dvd
      exact Nat.div_pos this (pow_pos hp.pos e)
    have hnot_p : ¬ p ∣ m' := by
      intro hdiv
      have : p ^ (e + 1) ∣ m := by rw [hm_eq, pow_succ]; exact Nat.mul_dvd_mul_left (p ^ e) hdiv
      have hle := (hp.pow_dvd_iff_le_factorization (by omega)).mp this
      omega
    have hcop : Nat.Coprime (p ^ e) m' := (hp.coprime_iff_not_dvd.mpr hnot_p).pow_left e
    have : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
    have : NeZero m' := ⟨by omega⟩
    have hpf_eq : m.primeFactors = insert p m'.primeFactors := by
      ext q; simp only [Nat.mem_primeFactors, Finset.mem_insert]; constructor
      · rintro ⟨hq, hqm, _⟩; rw [hm_eq] at hqm
        rcases hq.dvd_mul.mp hqm with hqp | hqm'
        · left; exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqp)
        · right; exact ⟨hq, hqm', by omega⟩
      · rintro (rfl | ⟨hq, hqm', _⟩)
        · exact ⟨hp, hpm, by omega⟩
        · exact ⟨hq, by rw [hm_eq]; exact dvd_mul_of_dvd_right hqm' _, by omega⟩
    have hp_not_m' : p ∉ m'.primeFactors := by intro h; exact hnot_p (Nat.mem_primeFactors.mp h).2.1
    have hm'_card : m'.primeFactors.card = k := by
      rw [hpf_eq, Finset.card_insert_of_notMem hp_not_m'] at hcard; omega
    have hm'_primes : ∀ q ∈ m'.primeFactors, q % 4 = 1 := by
      intro q hq; apply hmp q
      rw [hpf_eq]; exact Finset.mem_insert_of_mem hq
    have h1 := card_trapRoots_prime_pow hp hp1 he1; have h2 := ih m' hm'_pos hm'_card hm'_primes
    have hmul := card_trapRoots_mul hcop
    have hsame : (trapRoots m).card = (trapRoots (p ^ e * m')).card := by
      have : ∀ (a c : ℕ) [NeZero a] [NeZero c], a = c → (trapRoots a).card = (trapRoots c).card := by
        rintro a _ _ _ rfl; rfl
      exact this m (p ^ e * m') hm_eq
    rw [hsame, hmul, h1, h2, pow_succ']
/-- Theorem `thm:odd-trapdoor`(4b): Exact count of starts in `[1, 2b]` with `b ∣ n ∨ b ∣ f_b b n` equals -/
theorem thm_odd_trapdoor_density_count {b : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (hprimes : ∀ p ∈ b.primeFactors, p % 4 = 1) :
    ((Finset.Icc 1 (2 * b)).filter (fun n => b ∣ n ∨ b ∣ f_b b n)).card =
      2 + 2 ^ b.primeFactors.card := by
  classical
  have : NeZero b := ⟨by omega⟩
  have hS := thm_odd_trapdoor_rooted hb3 hb_odd hprimes; let A := (Finset.Icc 1 (2 * b)).filter (fun n => b ∣ n)
  let B := (Finset.Icc 1 (2 * b)).filter (fun n => ¬ b ∣ n ∧ b ∣ f_b b n)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]; intro n hA hB
    simp only [A, B, Finset.mem_filter] at hA hB; exact hB.2.1 hA.2
  have hunion : (Finset.Icc 1 (2 * b)).filter (fun n => b ∣ n ∨ b ∣ f_b b n) = A ∪ B := by
    ext n; simp only [A, B, Finset.mem_filter, Finset.mem_union]; tauto
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  have hA_eq : A = {b, 2 * b} := by
    ext n; simp only [A, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; constructor
    · rintro ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩; have hk1 : 1 ≤ k := by nlinarith
      have hk2 : k ≤ 2 := by nlinarith
      have hk : k = 1 ∨ k = 2 := by omega
      rcases hk with rfl | rfl
      · left; ring
      · right; ring
    · rintro (h | h) <;> rw [h]
      · exact ⟨⟨by omega, by omega⟩, dvd_refl b⟩
      · exact ⟨⟨by omega, by omega⟩, dvd_mul_left b 2⟩
  have hA_card : A.card = 2 := by rw [hA_eq, Finset.card_pair (by omega)]
  have hB_card : B.card = (trapRoots b).card := by
    refine Finset.card_bij (fun n _ => (n : ZMod b)) ?_ ?_ ?_
    · intro n hn; simp only [B, Finset.mem_filter] at hn
      have ⟨_, hroot⟩ := thm_odd_trapdoor_entry hb_odd hn.2.1 hn.2.2
      simp only [trapRoots, Finset.mem_filter, Finset.mem_univ, true_and]
      have hd : b ∣ n * n + 1 := Nat.dvd_of_mod_eq_zero hroot
      have h0 : ((n * n + 1 : ℕ) : ZMod b) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
      push_cast at h0; rw [sq]; exact h0
    · intro x hx y hy hxy; simp only [B, Finset.mem_filter, Finset.mem_Icc] at hx hy
      have hx_odd := (thm_odd_trapdoor_entry hb_odd hx.2.1 hx.2.2).1
      have hy_odd := (thm_odd_trapdoor_entry hb_odd hy.2.1 hy.2.2).1
      have hmodb : x % b = y % b := (ZMod.natCast_eq_natCast_iff' x y b).mp hxy; have hx_div := Nat.div_add_mod x b
      have hy_div := Nat.div_add_mod y b
      have hxb_lt : x < 2 * b := by
        by_contra hge
        have : x = 2 * b := by omega
        exact hx.2.1 (this ▸ dvd_mul_left b 2)
      have hyb_lt : y < 2 * b := by
        by_contra hge
        have : y = 2 * b := by omega
        exact hy.2.1 (this ▸ dvd_mul_left b 2)
      have hx_q : x / b ≤ 1 := Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega))
      have hy_q : y / b ≤ 1 := Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega))
      have hxq_cases : x / b = 0 ∨ x / b = 1 := by
        cases h : x / b with
        | zero => left; rfl
        | succ k => right; rw [h] at hx_q; omega
      have hyq_cases : y / b = 0 ∨ y / b = 1 := by
        cases h : y / b with
        | zero => left; rfl
        | succ k => right; rw [h] at hy_q; omega
      rcases hxq_cases with hxq | hxq <;> rcases hyq_cases with hyq | hyq <;>
        (rw [hxq] at hx_div; rw [hyq] at hy_div; simp only [mul_zero, mul_one, zero_add] at hx_div hy_div; omega)
    · intro r hr; let v := r.val; have hv_lt : v < b := r.val_lt
      have hv_ne0 : v ≠ 0 := by
        intro h0; simp only [trapRoots, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        have hr0 : r = 0 := by
          have := ZMod.natCast_zmod_val r
          rw [show r.val = 0 from h0] at this; simpa using this.symm
        rw [hr0] at hr
        have h10 : (1 : ZMod b) = 0 := by simpa using hr
        have : b ∣ 1 := (ZMod.natCast_eq_zero_iff 1 b).mp (by simpa using h10)
        have := Nat.le_of_dvd (by omega) this; omega
      let n := if v % 2 = 1 then v else v + b; have hn_odd : n % 2 = 1 := by simp only [n]; split_ifs <;> omega
      have hn_range : 1 ≤ n ∧ n ≤ 2 * b := by simp only [n]; split_ifs <;> omega
      have hn_cast : (n : ZMod b) = r := by
        simp only [n]
        split_ifs
        · exact ZMod.natCast_zmod_val r
        · push_cast; rw [ZMod.natCast_self, add_zero]; exact ZMod.natCast_zmod_val r
      have hn_ndvd : ¬ b ∣ n := by
        intro hd
        have : (n : ZMod b) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
        rw [hn_cast] at this
        have : v = 0 := by have := congr_arg ZMod.val this; simpa [v] using this
        exact hv_ne0 this
      have hn_fdvd : b ∣ f_b b n := hS.2 n hn_odd (hn_cast.symm ▸ hr)
      refine ⟨n, ?_, hn_cast⟩
      simp only [B, Finset.mem_filter, Finset.mem_Icc]; exact ⟨hn_range, hn_ndvd, hn_fdvd⟩
  rw [hA_card, hB_card, hS.1]

/-! ## Lemma `lem:odd-cylinders`: Odd-base cylinders and pullbacks -/
/-- A cylinder `(x, c, j)` in odd base `b`: `{n ≥ 1 | n ≡ x (mod b) ∧ n ≡ c (mod 2^j)}`. -/
structure OddCyl where
  x : ℕ
  c : ℕ
  j : ℕ
  deriving DecidableEq, Repr

def MemOddCyl (b : ℕ) (C : OddCyl) (n : ℕ) : Prop := 1 ≤ n ∧ n % b = C.x % b ∧ n % 2 ^ C.j = C.c % 2 ^ C.j
/-- Deterministic one-step cylinder map for odd `b ≥ 3`, `1 ≤ x < b`, `j ≥ 1`. -/
noncomputable def cylStep (b : ℕ) (C : OddCyl) : OddCyl :=
  if C.c % 2 = 0 then
    ⟨(C.x * ((b + 1) / 2)) % b, (C.c / 2) % 2 ^ (C.j - 1), C.j - 1⟩
  else
    let a := padicValNat 2 C.x
    ⟨(C.x * C.x + 1) % b, (C.x * C.c + 1) % 2 ^ (C.j + a), C.j + a⟩
/-- Lemma `lem:odd-cylinders`(1a): Forward inclusion `n ∈ C → f_b b n ∈ cylStep b C`. -/
theorem lem_odd_cylinders_step {b : ℕ} (hb_odd : b % 2 = 1) {C : OddCyl}
    (_hx1 : 1 ≤ C.x) (hxb : C.x < b) (hj : 1 ≤ C.j) {n : ℕ} (hn : MemOddCyl b C n) :
    MemOddCyl b (cylStep b C) (f_b b n) := by
  obtain ⟨hn1, hnb, hn2⟩ := hn; have h2dvd : 2 ∣ 2 ^ C.j := dvd_pow_self 2 (by omega)
  have hpar : n % 2 = C.c % 2 := by
    have h1 := Nat.mod_mod_of_dvd n h2dvd; have h2 := Nat.mod_mod_of_dvd C.c h2dvd; rw [← h1, hn2, h2]
  have hnb' : n % b = C.x := by rw [hnb, Nat.mod_eq_of_lt hxb]
  unfold cylStep
  split_ifs with hev
  ·
    have hnev : n % 2 = 0 := by omega
    rw [f_b_even hnev]; have hge1 : 1 ≤ n / 2 := by omega
    refine ⟨hge1, ?_, ?_⟩
    ·
      have h2inv : (2 * ((b + 1) / 2)) % b = 1 % b := by
        have : 2 * ((b + 1) / 2) = b + 1 := by omega
        rw [this, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
      have hmul : (n / 2) % b = ((n / 2) * (2 * ((b + 1) / 2))) % b := by
        rw [Nat.mul_mod, h2inv, ← Nat.mul_mod, mul_one]
      have h2n : n / 2 * 2 = n := by omega
      rw [hmul, ← mul_assoc, h2n, Nat.mul_mod, hnb']; simp [Nat.mul_mod]
    ·
      have hj_eq : 2 ^ C.j = 2 * 2 ^ (C.j - 1) := by conv_lhs => rw [show C.j = (C.j - 1) + 1 by omega, pow_succ']
      rw [Nat.mod_mod, nat_div_mod_two n, nat_div_mod_two C.c, ← hj_eq, hn2]
  ·
    have hnodd : n % 2 = 1 := by omega
    rw [f_b_odd hnodd, hnb']
    refine ⟨by omega, ?_, ?_⟩
    · simp only [Nat.mod_mod]; simp [Nat.add_mod, Nat.mul_mod, hnb']
    · simp only [Nat.mod_mod]; set a := padicValNat 2 C.x; have h2a_dvd : 2 ^ a ∣ C.x := pow_padicValNat_dvd
      obtain ⟨u, hu⟩ := h2a_dvd
      have hcast_eq : (n : ZMod (2 ^ C.j)) = (C.c : ZMod (2 ^ C.j)) :=
        (ZMod.natCast_eq_natCast_iff' n C.c (2 ^ C.j)).mpr hn2
      have hdiff : (2 ^ C.j : ℤ) ∣ (n : ℤ) - (C.c : ℤ) := by
        have : (((n : ℤ) - (C.c : ℤ) : ℤ) : ZMod (2 ^ C.j)) = 0 := by push_cast; exact sub_eq_zero.mpr hcast_eq
        exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
      have hmul_dvd : (2 ^ (C.j + a) : ℤ) ∣ ((C.x * n + 1 : ℕ) : ℤ) - ((C.x * C.c + 1 : ℕ) : ℤ) := by
        have h1 : ((C.x * n + 1 : ℕ) : ℤ) - ((C.x * C.c + 1 : ℕ) : ℤ) =
            (C.x : ℤ) * ((n : ℤ) - (C.c : ℤ)) := by push_cast; ring
        rw [h1, hu, pow_add]; push_cast; obtain ⟨k, hk⟩ := hdiff
        refine ⟨(u : ℤ) * k, ?_⟩
        rw [hk]; ring
      have hzm : (((C.x * n + 1 : ℕ) : ZMod (2 ^ (C.j + a))) =
          ((C.x * C.c + 1 : ℕ) : ZMod (2 ^ (C.j + a)))) := by
        apply sub_eq_zero.mp
        have h0 : ((((C.x * n + 1 : ℕ) : ℤ) - ((C.x * C.c + 1 : ℕ) : ℤ)) :
            ZMod (2 ^ (C.j + a))) = 0 := by
          rw [← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hmul_dvd
        simpa [Int.cast_sub, Int.cast_natCast] using h0
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hzm
/-- Lemma `lem:odd-cylinders`(1b): Exact sub-cylinder pullback — for every sub-cylinder -/
theorem lem_odd_cylinders_pullback {b : ℕ} (hb_odd : b % 2 = 1) {C : OddCyl}
    (hx1 : 1 ≤ C.x) (hxb : C.x < b) (hj : 1 ≤ C.j) (e cStar : ℕ)
    (hsub : cStar % 2 ^ (cylStep b C).j = (cylStep b C).c % 2 ^ (cylStep b C).j) :
    ∃ c0 : ℕ, c0 < 2 ^ (C.j + e) ∧ c0 % 2 ^ C.j = C.c % 2 ^ C.j ∧
      ∀ n : ℕ, (MemOddCyl b C n ∧ MemOddCyl b ⟨(cylStep b C).x, cStar, (cylStep b C).j + e⟩ (f_b b n)) ↔
        MemOddCyl b ⟨C.x, c0, C.j + e⟩ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hev : C.c % 2 = 0
  ·
    have hstep_j : (cylStep b C).j = C.j - 1 := by simp [cylStep, hev]
    have hstep_c : (cylStep b C).c = (C.c / 2) % 2 ^ (C.j - 1) := by simp [cylStep, hev]
    let c0 := (2 * cStar) % 2 ^ (C.j + e)
    have hdiv_cc : C.c % (2 * 2 ^ (C.j - 1)) = 2 * ((C.c / 2) % 2 ^ (C.j - 1)) := by
      have hpar_c : C.c % (2 * 2 ^ (C.j - 1)) % 2 = 0 := by rw [Nat.mod_mod_of_dvd _ (dvd_mul_right 2 _)]; exact hev
      rw [nat_div_mod_two]; omega
    have h2dvd_e : 2 ^ C.j ∣ 2 ^ (C.j + e) := pow_dvd_pow 2 (by omega)
    have hc0_mod : c0 % 2 ^ C.j = C.c % 2 ^ C.j := by
      rw [Nat.mod_mod_of_dvd _ h2dvd_e]; rw [hstep_j, hstep_c, Nat.mod_mod] at hsub
      have hj_eq : 2 ^ C.j = 2 * 2 ^ (C.j - 1) := by conv_lhs => rw [show C.j = (C.j - 1) + 1 by omega, pow_succ']
      rw [hj_eq, Nat.mul_mod_mul_left, hsub, ← hdiv_cc]
    refine ⟨c0, Nat.mod_lt _ (by positivity), hc0_mod, fun n => ?_⟩
    have hje : 2 ^ (C.j + e) = 2 * 2 ^ ((C.j - 1) + e) := by
      rw [show C.j + e = ((C.j - 1) + e) + 1 by omega, pow_succ']
    constructor
    · rintro ⟨hnC, hfnD⟩
      have hpar : n % 2 = 0 := by
        have h2d : 2 ∣ 2 ^ C.j := dvd_pow_self 2 (by omega)
        have h1 := Nat.mod_mod_of_dvd n h2d; have h2 := Nat.mod_mod_of_dvd C.c h2d; rw [← h1, hnC.2.2, h2, hev]
      have hmod := hfnD.2.2; rw [f_b_even hpar, hstep_j] at hmod
      refine ⟨hnC.1, hnC.2.1, ?_⟩
      rw [Nat.mod_mod]
      have h1 : n % (2 * 2 ^ (C.j - 1 + e)) = 2 * ((n / 2) % 2 ^ (C.j - 1 + e)) := by
        have hpar_n : n % (2 * 2 ^ (C.j - 1 + e)) % 2 = 0 := by
          rw [Nat.mod_mod_of_dvd _ (dvd_mul_right 2 _)]; exact hpar
        rw [nat_div_mod_two]; omega
      rw [hje, h1, hmod, Nat.mul_mod_mul_left]
    · intro hn0
      have hnC : MemOddCyl b C n := by
        refine ⟨hn0.1, hn0.2.1, ?_⟩
        have h1 := Nat.mod_mod_of_dvd n h2dvd_e; have h2 := Nat.mod_mod_of_dvd c0 h2dvd_e
        rw [← h1, hn0.2.2, h2, hc0_mod]
      have hfnC' := lem_odd_cylinders_step hb_odd hx1 hxb hj hnC
      refine ⟨hnC, hfnC'.1, hfnC'.2.1, ?_⟩
      have hpar : n % 2 = 0 := by
        have h2d : 2 ∣ 2 ^ C.j := dvd_pow_self 2 (by omega)
        have h1 := Nat.mod_mod_of_dvd n h2d; have h2 := Nat.mod_mod_of_dvd C.c h2d; rw [← h1, hnC.2.2, h2, hev]
      rw [f_b_even hpar, hstep_j]; have hmod := hn0.2.2
      rw [Nat.mod_mod, hje, Nat.mul_mod_mul_left] at hmod
      rw [nat_div_mod_two, hmod, Nat.mul_div_cancel_left _ (by omega)]
  ·
    have hodd : C.c % 2 = 1 := by omega
    set a := padicValNat 2 C.x; have hstep_j : (cylStep b C).j = C.j + a := by simp [cylStep, hev, a]
    have hstep_c : (cylStep b C).c = (C.x * C.c + 1) % 2 ^ (C.j + a) := by simp [cylStep, hev, a]
    have h2a_dvd : 2 ^ a ∣ C.x := pow_padicValNat_dvd; set u := C.x / 2 ^ a
    have hCx_eq : C.x = 2 ^ a * u := (Nat.mul_div_cancel' h2a_dvd).symm
    have hu_odd : u % 2 = 1 := by
      by_contra hu_ev
      have h2u : 2 ∣ u := by omega
      have h2a1 : 2 ^ (a + 1) ∣ C.x := by rw [hCx_eq, pow_succ]; exact Nat.mul_dvd_mul_left (2 ^ a) h2u
      have hle := (padicValNat_dvd_iff_le (by omega : C.x ≠ 0)).mp h2a1
      omega
    have hcop_u : Nat.Coprime u (2 ^ (C.j + e)) :=
      (Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))).pow_right _
    let uUnit : (ZMod (2 ^ (C.j + e)))ˣ := ZMod.unitOfCoprime u hcop_u
    let cStar' := cStar + 2 ^ (C.j + a + e)
    have hsub' : cStar' % 2 ^ (C.j + a) = (C.x * C.c + 1) % 2 ^ (C.j + a) := by
      rw [hstep_j, hstep_c, Nat.mod_mod] at hsub
      have hdvd : 2 ^ (C.j + a) ∣ 2 ^ (C.j + a + e) := pow_dvd_pow 2 (by omega)
      simp only [cStar', Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, add_zero, Nat.mod_mod, hsub]
    have h2a_dvd_cs : 2 ^ a ∣ cStar' - 1 := by
      have hdvd_a : 2 ^ a ∣ 2 ^ (C.j + a) := pow_dvd_pow 2 (by omega)
      have hmod_a : cStar' % 2 ^ a = (C.x * C.c + 1) % 2 ^ a := by
        rw [← Nat.mod_mod_of_dvd cStar' hdvd_a, hsub', Nat.mod_mod_of_dvd _ hdvd_a]
      have hCx_mod : (C.x * C.c + 1) % 2 ^ a = 1 % 2 ^ a := by
        rw [hCx_eq, mul_assoc, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
      have h1le : 1 ≤ cStar' := by
        have : 1 ≤ 2 ^ (C.j + a + e) := Nat.one_le_pow _ _ (by omega)
        omega
      rw [hCx_mod] at hmod_a
      have hcast : ((cStar' : ℕ) : ZMod (2 ^ a)) = ((1 : ℕ) : ZMod (2 ^ a)) :=
        (ZMod.natCast_eq_natCast_iff' cStar' 1 (2 ^ a)).mpr hmod_a
      have hsub0 : ((cStar' - 1 : ℕ) : ZMod (2 ^ a)) = 0 := by rw [Nat.cast_sub h1le, hcast, sub_self]
      exact (ZMod.natCast_eq_zero_iff _ _).mp hsub0
    let rhs := (cStar' - 1) / 2 ^ a
    let c0_z : ZMod (2 ^ (C.j + e)) := (uUnit⁻¹ : (ZMod (2 ^ (C.j + e)))ˣ) * (rhs : ZMod (2 ^ (C.j + e)))
    let c0 := c0_z.val
    have hc0_eq : ((u * c0 : ℕ) : ZMod (2 ^ (C.j + e))) = (rhs : ZMod (2 ^ (C.j + e))) := by
      push_cast; rw [ZMod.natCast_zmod_val c0_z]
      have hu_coe : (u : ZMod (2 ^ (C.j + e))) = (uUnit : ZMod (2 ^ (C.j + e))) := by simp [uUnit]
      rw [hu_coe, ← mul_assoc, Units.mul_inv, one_mul]
    have h2a_rhs : 2 ^ a * rhs + 1 = cStar' := by
      have h1 : 2 ^ a * rhs = cStar' - 1 := Nat.mul_div_cancel' h2a_dvd_cs
      have h1le : 1 ≤ cStar' := by
        have : 1 ≤ 2 ^ (C.j + a + e) := Nat.one_le_pow _ _ (by omega)
        omega
      omega
    have huc0_eq_c : ∀ m : ℕ, (C.x * m + 1) % 2 ^ (C.j + a + e) = cStar % 2 ^ (C.j + a + e) ↔
        m % 2 ^ (C.j + e) = c0 % 2 ^ (C.j + e) := by
      intro m; have hcs_mod : cStar % 2 ^ (C.j + a + e) = cStar' % 2 ^ (C.j + a + e) := by simp [cStar']
      rw [hcs_mod, ← h2a_rhs]
      have hpow : 2 ^ (C.j + a + e) = 2 ^ a * 2 ^ (C.j + e) := by
        rw [← pow_add, show a + (C.j + e) = C.j + a + e by omega]
      constructor
      · intro h
        have hsub1 : (C.x * m) % (2 ^ a * 2 ^ (C.j + e)) = (2 ^ a * rhs) % (2 ^ a * 2 ^ (C.j + e)) := by
          rw [← hpow]
          have h1 : ((C.x * m + 1 : ℕ) : ZMod (2 ^ (C.j + a + e))) =
              ((2 ^ a * rhs + 1 : ℕ) : ZMod (2 ^ (C.j + a + e))) :=
            (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
          push_cast at h1
          have h2 : ((C.x * m : ℕ) : ZMod (2 ^ (C.j + a + e))) =
              ((2 ^ a * rhs : ℕ) : ZMod (2 ^ (C.j + a + e))) := by
            push_cast; exact add_right_cancel h1
          exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h2
        rw [hCx_eq, mul_assoc, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at hsub1
        have hzm : (u * m : ℕ) % 2 ^ (C.j + e) = rhs % 2 ^ (C.j + e) :=
          Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ a) hsub1
        have hzm' : ((uUnit : ZMod (2 ^ (C.j + e))) * (m : ZMod (2 ^ (C.j + e)))) =
            ((uUnit : ZMod (2 ^ (C.j + e))) * (c0 : ZMod (2 ^ (C.j + e)))) := by
          have hu_coe : (uUnit : ZMod (2 ^ (C.j + e))) = (u : ZMod (2 ^ (C.j + e))) := by simp [uUnit]
          rw [hu_coe, ← Nat.cast_mul, ← Nat.cast_mul, hc0_eq]; exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hzm
        have hm_eq : (m : ZMod (2 ^ (C.j + e))) = (c0 : ZMod (2 ^ (C.j + e))) := by
          have := congr_arg (((uUnit⁻¹ : (ZMod (2 ^ (C.j + e)))ˣ) : ZMod (2 ^ (C.j + e))) * ·) hzm'
          simpa [← mul_assoc] using this
        exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hm_eq
      · intro h
        have hzm : (m : ZMod (2 ^ (C.j + e))) = (c0 : ZMod (2 ^ (C.j + e))) :=
          (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
        have hmul : ((u * m : ℕ) : ZMod (2 ^ (C.j + e))) = (rhs : ZMod (2 ^ (C.j + e))) := by
          push_cast; rw [hzm]; simpa using hc0_eq
        have hmul_mod : (u * m) % 2 ^ (C.j + e) = rhs % 2 ^ (C.j + e) := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hmul
        have h2a_mod : (C.x * m) % 2 ^ (C.j + a + e) = (2 ^ a * rhs) % 2 ^ (C.j + a + e) := by
          rw [hpow, hCx_eq, mul_assoc, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hmul_mod]
        rw [Nat.add_mod, h2a_mod, ← Nat.add_mod]
    have hc0_mod_j : c0 % 2 ^ C.j = C.c % 2 ^ C.j := by
      have hpow_j : 2 ^ (C.j + a) = 2 ^ a * 2 ^ C.j := by rw [← pow_add, add_comm]
      have h1 : (C.x * c0 + 1) % 2 ^ (C.j + a) = (C.x * C.c + 1) % 2 ^ (C.j + a) := by
        have hcs := (huc0_eq_c c0).mpr rfl; have hdvd : 2 ^ (C.j + a) ∣ 2 ^ (C.j + a + e) := pow_dvd_pow 2 (by omega)
        have h2 : (C.x * c0 + 1) % 2 ^ (C.j + a) = cStar % 2 ^ (C.j + a) := by
          rw [← Nat.mod_mod_of_dvd _ hdvd, hcs, Nat.mod_mod_of_dvd _ hdvd]
        rw [hstep_j, hstep_c, Nat.mod_mod] at hsub; exact h2.trans hsub
      have hsub1 : (C.x * c0) % (2 ^ a * 2 ^ C.j) = (C.x * C.c) % (2 ^ a * 2 ^ C.j) := by
        rw [← hpow_j]
        have hz : ((C.x * c0 + 1 : ℕ) : ZMod (2 ^ (C.j + a))) =
            ((C.x * C.c + 1 : ℕ) : ZMod (2 ^ (C.j + a))) :=
          (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h1
        push_cast at hz
        have hz2 : ((C.x * c0 : ℕ) : ZMod (2 ^ (C.j + a))) =
            ((C.x * C.c : ℕ) : ZMod (2 ^ (C.j + a))) := by
          push_cast; exact add_right_cancel hz
        exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hz2
      rw [hCx_eq, mul_assoc, mul_assoc, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at hsub1
      have h2 := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ a) hsub1
      have hcop_j : Nat.Coprime u (2 ^ C.j) :=
        (Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))).pow_right _
      let uJ : (ZMod (2 ^ C.j))ˣ := ZMod.unitOfCoprime u hcop_j
      have hz : (uJ : ZMod (2 ^ C.j)) * (c0 : ZMod (2 ^ C.j)) =
          (uJ : ZMod (2 ^ C.j)) * (C.c : ZMod (2 ^ C.j)) := by
        have hcoe : (uJ : ZMod (2 ^ C.j)) = (u : ZMod (2 ^ C.j)) := by simp [uJ]
        rw [hcoe, ← Nat.cast_mul, ← Nat.cast_mul]; exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h2
      have hcancel : (c0 : ZMod (2 ^ C.j)) = (C.c : ZMod (2 ^ C.j)) := by
        have := congr_arg (((uJ⁻¹ : (ZMod (2 ^ C.j))ˣ) : ZMod (2 ^ C.j)) * ·) hz
        simpa [← mul_assoc] using this
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcancel
    refine ⟨c0, c0_z.val_lt, hc0_mod_j, fun n => ?_⟩
    have h2dvd_e : 2 ^ C.j ∣ 2 ^ (C.j + e) := pow_dvd_pow 2 (by omega)
    constructor
    · rintro ⟨hnC, hfnD⟩
      have hpar : n % 2 = 1 := by
        have h2d : 2 ∣ 2 ^ C.j := dvd_pow_self 2 (by omega)
        have h1 := Nat.mod_mod_of_dvd n h2d; have h2 := Nat.mod_mod_of_dvd C.c h2d; rw [← h1, hnC.2.2, h2, hodd]
      have hnb' : n % b = C.x := by rw [hnC.2.1, Nat.mod_eq_of_lt hxb]
      have hmod := hfnD.2.2; rw [f_b_odd hpar, hnb', hstep_j] at hmod; exact ⟨hnC.1, hnC.2.1, (huc0_eq_c n).mp hmod⟩
    · intro hn0
      have hnC : MemOddCyl b C n := by
        refine ⟨hn0.1, hn0.2.1, ?_⟩
        have h1 := Nat.mod_mod_of_dvd n h2dvd_e; have h2 := Nat.mod_mod_of_dvd c0 h2dvd_e
        rw [← h1, hn0.2.2, h2, hc0_mod_j]
      have hfnC' := lem_odd_cylinders_step hb_odd hx1 hxb hj hnC
      refine ⟨hnC, hfnC'.1, hfnC'.2.1, ?_⟩
      have hpar : n % 2 = 1 := by
        have h2d : 2 ∣ 2 ^ C.j := dvd_pow_self 2 (by omega)
        have h1 := Nat.mod_mod_of_dvd n h2d; have h2 := Nat.mod_mod_of_dvd C.c h2d; rw [← h1, hnC.2.2, h2, hodd]
      have hnb' : n % b = C.x := by rw [hnC.2.1, Nat.mod_eq_of_lt hxb]
      rw [f_b_odd hpar, hnb', hstep_j]; exact (huc0_eq_c n).mpr hn0.2.2
/-- Lemma `lem:odd-cylinders`(3): `Z_K(b)` is periodic modulo `b * 2^K` for every `K ≥ 0`, so `τ_K(b)` is -/
lemma f_b_step_mod_odd {b k n m : ℕ} (_hb_odd : b % 2 = 1) (_hb : 1 ≤ b)
    (hmod : n % (b * 2 ^ (k + 1)) = m % (b * 2 ^ (k + 1))) :
    f_b b n % (b * 2 ^ k) = f_b b m % (b * 2 ^ k) := by
  have h2dvd : 2 ∣ b * 2 ^ (k + 1) := dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega)) b
  have hpar : n % 2 = m % 2 := by rw [← Nat.mod_mod_of_dvd n h2dvd, hmod, Nat.mod_mod_of_dvd m h2dvd]
  have hbdvd : b ∣ b * 2 ^ (k + 1) := dvd_mul_right b _
  have hmb : n % b = m % b := by rw [← Nat.mod_mod_of_dvd n hbdvd, hmod, Nat.mod_mod_of_dvd m hbdvd]
  by_cases hev : n % 2 = 0
  · have hmev : m % 2 = 0 := by omega
    rw [f_b_even hev, f_b_even hmev]; have hmul : b * 2 ^ (k + 1) = 2 * (b * 2 ^ k) := by rw [pow_succ]; ring
    rw [nat_div_mod_two n, nat_div_mod_two m, ← hmul, hmod]
  · have hnodd : n % 2 = 1 := by omega
    have hmodd : m % 2 = 1 := by omega
    rw [f_b_odd hnodd, f_b_odd hmodd, hmb]
    have hkdvd : b * 2 ^ k ∣ b * 2 ^ (k + 1) := Nat.mul_dvd_mul_left b (pow_dvd_pow 2 (by omega))
    have hmk : n % (b * 2 ^ k) = m % (b * 2 ^ k) := by
      rw [← Nat.mod_mod_of_dvd n hkdvd, hmod, Nat.mod_mod_of_dvd m hkdvd]
    rw [Nat.add_mod, Nat.mul_mod, hmk, ← Nat.mul_mod, ← Nat.add_mod]
lemma f_b_iter_mod_odd {b K n m : ℕ} (hb_odd : b % 2 = 1) (hb : 1 ≤ b)
    (hmod : n % (b * 2 ^ K) = m % (b * 2 ^ K)) :
    ∀ i ≤ K, (f_b b)^[i] n % (b * 2 ^ (K - i)) = (f_b b)^[i] m % (b * 2 ^ (K - i)) := by
  intro i hi
  induction i with
  | zero => simpa using hmod
  | succ i ih =>
    have hprev := ih (by omega)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; have hsub : K - i = (K - (i + 1)) + 1 := by omega
    rw [hsub] at hprev; exact f_b_step_mod_odd hb_odd hb hprev
/-- `Z_K(b) = {n ≥ 1 | ∃ i ≤ K, b ∣ f_b^i(n)}` is invariant modulo `b * 2^K`. -/
theorem lem_odd_cylinders_ZK_periodic {b K n m : ℕ} (hb_odd : b % 2 = 1) (hb : 1 ≤ b)
    (hmod : n % (b * 2 ^ K) = m % (b * 2 ^ K)) :
    (∃ i ≤ K, b ∣ (f_b b)^[i] n) ↔ (∃ i ≤ K, b ∣ (f_b b)^[i] m) := by
  have hiff : ∀ i ≤ K, b ∣ (f_b b)^[i] n ↔ b ∣ (f_b b)^[i] m := by
    intro i hi; have h1 := f_b_iter_mod_odd hb_odd hb hmod i hi; have hdvd : b ∣ b * 2 ^ (K - i) := dvd_mul_right b _
    have h2 : (f_b b)^[i] n % b = (f_b b)^[i] m % b := by
      rw [← Nat.mod_mod_of_dvd _ hdvd, h1, Nat.mod_mod_of_dvd _ hdvd]
    simp only [Nat.dvd_iff_mod_eq_zero, h2]
  exact ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, (hiff i hi).mp h⟩,
         fun ⟨i, hi, h⟩ => ⟨i, hi, (hiff i hi).mpr h⟩⟩

/-! ## Lemma `lem:odd-runaway`: Self-returning stretches diverge strictly -/
/-- Cylinder inclusion: `C1 ⊆ C2` means same residue mod `b`, at least as many known bits, and matching low bits -/
def CylSubset (b : ℕ) (C1 C2 : OddCyl) : Prop := C1.x % b = C2.x % b ∧ C2.j ≤ C1.j ∧ C1.c % 2 ^ C2.j = C2.c % 2 ^ C2.j
lemma memOddCyl_of_subset {b : ℕ} {C1 C2 : OddCyl} (h : CylSubset b C1 C2) {n : ℕ}
    (hn : MemOddCyl b C1 n) : MemOddCyl b C2 n := by
  refine ⟨hn.1, hn.2.1.trans h.1, ?_⟩
  have hdvd : 2 ^ C2.j ∣ 2 ^ C1.j := pow_dvd_pow 2 h.2.1
  rw [← Nat.mod_mod_of_dvd n hdvd, hn.2.2, Nat.mod_mod_of_dvd C1.c hdvd, h.2.2]
/-- Tracking the affine map `(A, B, h)` along a `p`-step cylinder path: `2^h * f_b^p(m) = A * m + B`, with -/
noncomputable def stretchAffine (b : ℕ) : OddCyl → ℕ → (ℕ × ℕ × ℕ)
  | _, 0 => (1, 0, 0)
  | C, t + 1 =>
    let (A, B, h) := stretchAffine b (cylStep b C) t
    if C.c % 2 = 0 then
      (A, 2 * B, h + 1)
    else
      (A * C.x, A + B, h)
/-- Helper: affine formula along a cylinder stretch staying off residue `0` with `j ≥ 1`. -/
lemma stretchAffine_spec {b : ℕ} (hb_odd : b % 2 = 1) :
    ∀ (t : ℕ) (C : OddCyl),
      (∀ i < t, 1 ≤ ((cylStep b)^[i] C).x ∧ ((cylStep b)^[i] C).x < b ∧
                1 ≤ ((cylStep b)^[i] C).j) →
      let (A, B, h) := stretchAffine b C t
      (∀ m, MemOddCyl b C m → 2 ^ h * (f_b b)^[t] m = A * m + B) ∧
      ((cylStep b)^[t] C).j + h ≤ C.j + padicValNat 2 A ∧
      1 ≤ A ∧
      (h < t → 1 ≤ B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro t
  induction t with
  | zero => intro C _; simp [stretchAffine]
  | succ t ih =>
    intro C hvalid; have h0 := hvalid 0 (by omega)
    simp only [Function.iterate_zero, id_eq] at h0
    have hrest : ∀ i < t, 1 ≤ ((cylStep b)^[i] (cylStep b C)).x ∧
        ((cylStep b)^[i] (cylStep b C)).x < b ∧
        1 ≤ ((cylStep b)^[i] (cylStep b C)).j := by
      intro i hi
      have := hvalid (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    have hih := ih (cylStep b C) hrest
    rcases hres : stretchAffine b (cylStep b C) t with ⟨A, B, h⟩
    rw [hres] at hih; obtain ⟨heq, hbits, hA1, hB⟩ := hih
    have hstep_eq : stretchAffine b C (t + 1) =
        if C.c % 2 = 0 then (A, 2 * B, h + 1) else (A * C.x, A + B, h) := by
      simp [stretchAffine, hres]
    rw [hstep_eq]
    split_ifs with hev
    ·
      have hCj : (cylStep b C).j = C.j - 1 := by simp [cylStep, hev]
      refine ⟨fun m hm => ?_, ?_, hA1, fun hlt => by have := hB (by omega); omega⟩
      · have h2d : 2 ∣ 2 ^ C.j := dvd_pow_self 2 (by omega)
        have hpar : m % 2 = 0 := by rw [← Nat.mod_mod_of_dvd m h2d, hm.2.2, Nat.mod_mod_of_dvd C.c h2d, hev]
        have hm' := lem_odd_cylinders_step hb_odd h0.1 h0.2.1 h0.2.2 hm; have h2m : 2 * (m / 2) = m := by omega
        calc 2 ^ (h + 1) * (f_b b)^[t + 1] m
            = 2 * (2 ^ h * (f_b b)^[t] (f_b b m)) := by rw [Function.iterate_succ_apply, pow_succ']; ring
          _ = 2 * (A * (f_b b m) + B) := by rw [heq (f_b b m) hm']
          _ = A * (2 * (m / 2)) + 2 * B := by rw [f_b_even hpar]; ring
          _ = A * m + 2 * B := by rw [h2m]
      · rw [Function.iterate_succ_apply]; rw [hCj] at hbits; omega
    ·
      have hodd : C.c % 2 = 1 := by omega
      have hCj : (cylStep b C).j = C.j + padicValNat 2 C.x := by simp [cylStep, hev]
      refine ⟨fun m hm => ?_, ?_, by nlinarith [h0.1], fun _ => by omega⟩
      · have h2d : 2 ∣ 2 ^ C.j := dvd_pow_self 2 (by omega)
        have hpar : m % 2 = 1 := by rw [← Nat.mod_mod_of_dvd m h2d, hm.2.2, Nat.mod_mod_of_dvd C.c h2d, hodd]
        have hmb : m % b = C.x := by rw [hm.2.1, Nat.mod_eq_of_lt h0.2.1]
        have hm' := lem_odd_cylinders_step hb_odd h0.1 h0.2.1 h0.2.2 hm
        calc 2 ^ h * (f_b b)^[t + 1] m
            = 2 ^ h * (f_b b)^[t] (f_b b m) := by rw [Function.iterate_succ_apply]
          _ = A * (f_b b m) + B := heq (f_b b m) hm'
          _ = A * (C.x * m + 1) + B := by rw [f_b_odd hpar, hmb]
          _ = A * C.x * m + (A + B) := by ring
      · rw [Function.iterate_succ_apply]; rw [hCj] at hbits
        have hpad : padicValNat 2 (A * C.x) = padicValNat 2 A + padicValNat 2 C.x :=
          padicValNat.mul (by omega) (by omega)
        rw [hpad]; omega
/-- Lemma `lem:odd-runaway`: If a stretch `C_0 = (x, 1, 1), C_1, ..., C_k` stays off residue `0` with `j ≥ 1` and -/
theorem lem_odd_runaway {b x k p : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (hp1 : 1 ≤ p) (hpk : p ≤ k)
    (hvalid : ∀ i ≤ k, 1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).x ∧
                       ((cylStep b)^[i] ⟨x, 1, 1⟩).x < b ∧
                       1 ≤ ((cylStep b)^[i] ⟨x, 1, 1⟩).j)
    (hret : CylSubset b ((cylStep b)^[k] ⟨x, 1, 1⟩) ((cylStep b)^[k - p] ⟨x, 1, 1⟩))
    {n : ℕ} (hn1 : 1 ≤ n) (hn_odd : n % 2 = 1) (hnx : n % b = x) :
    (∀ i : ℕ, ¬ b ∣ (f_b b)^[i] n ∧ (f_b b)^[i] n ≠ 1) ∧
    (∀ i ≥ k - p, (f_b b)^[i] n < (f_b b)^[i + p] n) ∧
    Filter.Tendsto (fun i => (f_b b)^[i] n) Filter.atTop Filter.atTop := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C0 : OddCyl := ⟨x, 1, 1⟩
  have hnC0 : MemOddCyl b C0 n := by
    refine ⟨hn1, ?_, ?_⟩
    · have h0 := (hvalid 0 (by omega)).2.1
      simp only [Function.iterate_zero, id_eq] at h0
      rw [hnx]; exact (Nat.mod_eq_of_lt h0).symm
    · simpa [C0] using hn_odd
  have hmem_le : ∀ i ≤ k, MemOddCyl b ((cylStep b)^[i] C0) ((f_b b)^[i] n) := by
    intro i hi
    induction i with
    | zero => simpa using hnC0
    | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; have hv := hvalid i (by omega)
      exact lem_odd_cylinders_step hb_odd hv.1 hv.2.1 hv.2.2 (ih (by omega))
  set Cs := (cylStep b)^[k - p] C0
  have hCs_iter : ∀ r ≤ p, (cylStep b)^[r] Cs = (cylStep b)^[k - p + r] C0 := by
    intro r _; simp only [Cs, ← Function.iterate_add_apply, add_comm]
  have hret' : CylSubset b ((cylStep b)^[p] Cs) Cs := by
    rw [hCs_iter p (le_refl p), show k - p + p = k by omega]
    exact hret
  have hCs_valid : ∀ r < p, 1 ≤ ((cylStep b)^[r] Cs).x ∧
      ((cylStep b)^[r] Cs).x < b ∧ 1 ≤ ((cylStep b)^[r] Cs).j := by
    intro r hr; rw [hCs_iter r (by omega)]
    exact hvalid (k - p + r) (by omega)
  have hstep_Cs : ∀ m, MemOddCyl b Cs m →
      ∀ r ≤ p, MemOddCyl b ((cylStep b)^[r] Cs) ((f_b b)^[r] m) := by
    intro m hm r hr
    induction r with
    | zero => simpa using hm
    | succ r ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; have hv := hCs_valid r (by omega)
      exact lem_odd_cylinders_step hb_odd hv.1 hv.2.1 hv.2.2 (ih (by omega))
  have hclosed_Cs : ∀ m, MemOddCyl b Cs m → MemOddCyl b Cs ((f_b b)^[p] m) := by
    intro m hm; exact memOddCyl_of_subset hret' (hstep_Cs m hm p (le_refl p))
  have haff := stretchAffine_spec hb_odd p Cs hCs_valid
  rcases hres : stretchAffine b Cs p with ⟨A, B, h⟩
  rw [hres] at haff
  obtain ⟨haff_eq, haff_bits, hA1, hB_cond⟩ := haff; have hle_j : Cs.j ≤ ((cylStep b)^[p] Cs).j := hret'.2.1
  have hh_le_v2 : h ≤ padicValNat 2 A := by omega
  have h2h_le_A : 2 ^ h ≤ A := by
    have hdvd : 2 ^ h ∣ A := dvd_trans (pow_dvd_pow 2 hh_le_v2) pow_padicValNat_dvd
    exact Nat.le_of_dvd (by omega) hdvd
  have hh_lt_p : h < p := by
    by_contra hge
    have hA_one : ∀ (t : ℕ) (C : OddCyl), (stretchAffine b C t).2.2 ≤ t ∧
        ((stretchAffine b C t).2.2 = t → (stretchAffine b C t).1 = 1) := by
      intro t
      induction t with
      | zero => intro C; simp [stretchAffine]
      | succ t ih =>
        intro C; have hprev := ih (cylStep b C)
        rcases hsp : stretchAffine b (cylStep b C) t with ⟨A', B', h'⟩
        rw [hsp] at hprev
        have hst : stretchAffine b C (t + 1) =
            if C.c % 2 = 0 then (A', 2 * B', h' + 1) else (A' * C.x, A' + B', h') := by
          simp [stretchAffine, hsp]
        rw [hst]
        split_ifs
        · exact ⟨by dsimp at hprev ⊢; omega, fun heq => hprev.2 (by dsimp at heq ⊢; omega)⟩
        · exact ⟨by dsimp at hprev ⊢; omega, fun heq => by dsimp at hprev heq ⊢; omega⟩
    have hspec := hA_one p Cs; rw [hres] at hspec; dsimp only at hspec; have hhp : h = p := by omega
    have hAeq1 : A = 1 := hspec.2 hhp; rw [hAeq1] at hh_le_v2
    have hv1 : padicValNat 2 1 = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
    rw [hv1] at hh_le_v2; omega
  have hB1 : 1 ≤ B := hB_cond hh_lt_p
  have hgrow_Cs : ∀ m, MemOddCyl b Cs m → m < (f_b b)^[p] m := by
    intro m hm; have heq := haff_eq m hm
    have hmul : 2 ^ h * m < 2 ^ h * (f_b b)^[p] m := by
      rw [heq]
      have : 2 ^ h * m ≤ A * m := Nat.mul_le_mul_right m h2h_le_A
      omega
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hiter_Cs : ∀ q : ℕ, MemOddCyl b Cs ((f_b b)^[k - p + q * p] n) := by
    intro q
    induction q with
    | zero => simpa using hmem_le (k - p) (by omega)
    | succ q ih =>
      rw [show k - p + (q + 1) * p = p + (k - p + q * p) by ring, Function.iterate_add_apply]
      exact hclosed_Cs _ ih
  have hmem_all : ∀ i ≥ k - p,
      MemOddCyl b ((cylStep b)^[(i - (k - p)) % p] Cs) ((f_b b)^[i] n) := by
    intro i hi; set q := (i - (k - p)) / p; set r := (i - (k - p)) % p; have hr : r < p := Nat.mod_lt _ (by omega)
    have hdm : p * q + r = i - (k - p) := Nat.div_add_mod (i - (k - p)) p
    have hi_sub : (i - (k - p)) + (k - p) = i := Nat.sub_add_cancel hi
    have hi_eq : i = r + (k - p + q * p) := by linarith [mul_comm p q]
    rw [hi_eq, Function.iterate_add_apply]; exact hstep_Cs _ (hiter_Cs q) r (by omega)
  have hf_mono : ∀ (C : OddCyl), 1 ≤ C.x → C.x < b → 1 ≤ C.j →
      ∀ m₁ m₂, MemOddCyl b C m₁ → MemOddCyl b C m₂ → m₁ < m₂ → f_b b m₁ < f_b b m₂ := by
    intro C hx1 hxb hj m₁ m₂ hm₁ hm₂ hlt; have h2d : 2 ∣ 2 ^ C.j := dvd_pow_self 2 (by omega)
    have hp1 : m₁ % 2 = C.c % 2 := by rw [← Nat.mod_mod_of_dvd m₁ h2d, hm₁.2.2, Nat.mod_mod_of_dvd C.c h2d]
    have hp2 : m₂ % 2 = C.c % 2 := by rw [← Nat.mod_mod_of_dvd m₂ h2d, hm₂.2.2, Nat.mod_mod_of_dvd C.c h2d]
    by_cases hev : C.c % 2 = 0
    · rw [f_b_even (by omega), f_b_even (by omega)]; omega
    · have hmb1 : m₁ % b = C.x := by rw [hm₁.2.1, Nat.mod_eq_of_lt hxb]
      have hmb2 : m₂ % b = C.x := by rw [hm₂.2.1, Nat.mod_eq_of_lt hxb]
      rw [f_b_odd (by omega), f_b_odd (by omega), hmb1, hmb2]
      nlinarith
  have hf_iter_mono : ∀ r ≤ p, ∀ m₁ m₂,
      MemOddCyl b Cs m₁ → MemOddCyl b Cs m₂ → m₁ < m₂ →
      (f_b b)^[r] m₁ < (f_b b)^[r] m₂ := by
    intro r hr
    induction r with
    | zero => intro m₁ m₂ _ _ hlt; simpa using hlt
    | succ r ih =>
      intro m₁ m₂ hm₁ hm₂ hlt; rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hv := hCs_valid r (by omega)
      exact hf_mono _ hv.1 hv.2.1 hv.2.2 _ _
        (hstep_Cs m₁ hm₁ r (by omega)) (hstep_Cs m₂ hm₂ r (by omega))
        (ih (by omega) m₁ m₂ hm₁ hm₂ hlt)
  have hgrow_all : ∀ i ≥ k - p, (f_b b)^[i] n < (f_b b)^[i + p] n := by
    intro i hi; set q := (i - (k - p)) / p; set r := (i - (k - p)) % p; have hr : r < p := Nat.mod_lt _ (by omega)
    have hdm : p * q + r = i - (k - p) := Nat.div_add_mod (i - (k - p)) p
    have hi_sub : (i - (k - p)) + (k - p) = i := Nat.sub_add_cancel hi
    have hi_eq : i = r + (k - p + q * p) := by linarith [mul_comm p q]
    have hip_eq : i + p = r + (p + (k - p + q * p)) := by omega
    conv_lhs => rw [hi_eq, Function.iterate_add_apply]
    conv_rhs => rw [hip_eq, Function.iterate_add_apply, Function.iterate_add_apply]
    have hmq := hiter_Cs q; exact hf_iter_mono r (by omega) _ _ hmq (hclosed_Cs _ hmq) (hgrow_Cs _ hmq)
  have hstep_ge_half : ∀ m : ℕ, 1 ≤ m → ¬ b ∣ m → m ≤ 2 * f_b b m := by
    intro m hm1 hnd
    by_cases hev : m % 2 = 0
    · rw [f_b_even hev]; omega
    · rw [f_b_odd (by omega)]
      have hmb : 1 ≤ m % b := by by_contra h0; exact hnd (Nat.dvd_of_mod_eq_zero (by omega))
      nlinarith
  have hnot_dvd : ∀ i : ℕ, ¬ b ∣ (f_b b)^[i] n := by
    intro i hdvd; have h0 : (f_b b)^[i] n % b = 0 := Nat.mod_eq_zero_of_dvd hdvd
    by_cases hi : i ≤ k - p
    · have hm := hmem_le i (by omega)
      have hv := hvalid i (by omega)
      rw [hm.2.1, Nat.mod_eq_of_lt hv.2.1] at h0; omega
    · have hm := hmem_all i (by omega)
      have hv := hCs_valid ((i - (k - p)) % p) (Nat.mod_lt _ (by omega))
      rw [hm.2.1, Nat.mod_eq_of_lt hv.2.1] at h0; omega
  have hpos_all : ∀ i : ℕ, 1 ≤ (f_b b)^[i] n := by
    intro i
    by_cases hi : i ≤ k - p
    · exact (hmem_le i (by omega)).1
    · exact (hmem_all i (by omega)).1
  have hiter_ge_half : ∀ r i : ℕ, (f_b b)^[i] n ≤ 2 ^ r * (f_b b)^[r + i] n := by
    intro r
    induction r with
    | zero => intro i; simp
    | succ r ih =>
      intro i; have h1 := ih i; have h2 := hstep_ge_half ((f_b b)^[r + i] n) (hpos_all (r + i)) (hnot_dvd (r + i))
      have h3 : (f_b b)^[r + 1 + i] n = f_b b ((f_b b)^[r + i] n) := by
        rw [show r + 1 + i = (r + i) + 1 by omega, Function.iterate_succ_apply']
      rw [h3, pow_succ]
      calc (f_b b)^[i] n ≤ 2 ^ r * (f_b b)^[r + i] n := h1
        _ ≤ 2 ^ r * (2 * f_b b ((f_b b)^[r + i] n)) := Nat.mul_le_mul_left _ h2
        _ = 2 ^ r * 2 * f_b b ((f_b b)^[r + i] n) := by ring
  have ha_ge : ∀ q : ℕ, q ≤ (f_b b)^[k - p + q * p] n := by
    intro q
    induction q with
    | zero => omega
    | succ q ih =>
      have hlt := hgrow_all (k - p + q * p) (by omega)
      rw [show k - p + q * p + p = k - p + (q + 1) * p by ring] at hlt
      omega
  have htend : Filter.Tendsto (fun i => (f_b b)^[i] n) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]; intro M
    refine ⟨k - p + (M * 2 ^ p) * p, fun i hi => ?_⟩
    set q := (i - (k - p)) / p; set r := (i - (k - p)) % p; have hr : r < p := Nat.mod_lt _ (by omega)
    have hq_ge : M * 2 ^ p ≤ q := by
      have : (M * 2 ^ p) * p ≤ i - (k - p) := by omega
      exact (Nat.le_div_iff_mul_le (by omega)).mpr this
    have hdm : p * q + r = i - (k - p) := Nat.div_add_mod (i - (k - p)) p
    have hi_sub : (i - (k - p)) + (k - p) = i := Nat.sub_add_cancel (by omega)
    have hi_eq : i = r + (k - p + q * p) := by linarith [mul_comm p q]
    have h1 := hiter_ge_half r (k - p + q * p); rw [← hi_eq] at h1
    have h2 : M * 2 ^ p ≤ (f_b b)^[k - p + q * p] n := hq_ge.trans (ha_ge q)
    have hpow : 2 ^ r ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : M * 2 ^ p ≤ 2 ^ p * (f_b b)^[i] n := by
      calc M * 2 ^ p ≤ (f_b b)^[k - p + q * p] n := h2
        _ ≤ 2 ^ r * (f_b b)^[i] n := h1
        _ ≤ 2 ^ p * (f_b b)^[i] n := Nat.mul_le_mul_right _ hpow
    have h4 : 2 ^ p * M ≤ 2 ^ p * (f_b b)^[i] n := by linarith
    exact Nat.le_of_mul_le_mul_left h4 (by positivity)
  have hne1 : ∀ i : ℕ, (f_b b)^[i] n ≠ 1 := by
    intro i hi1
    have hcyc : ∀ t : ℕ, (f_b b)^[t] 1 ≤ 2 := by
      intro t
      have : (f_b b)^[t] 1 = 1 ∨ (f_b b)^[t] 1 = 2 := by
        induction t with
        | zero => left; rfl
        | succ t iht =>
          rw [Function.iterate_succ_apply']
          rcases iht with h | h <;> rw [h]
          · right; rw [f_b_odd (by decide), Nat.mod_eq_of_lt (by omega)]
          · left; rw [f_b_even (by decide)]
      omega
    obtain ⟨N, hN⟩ := (Filter.tendsto_atTop_atTop.mp htend) 3; have h3 := hN (max i N) (le_max_right i N)
    have hsplit : max i N = (max i N - i) + i := by omega
    rw [hsplit, Function.iterate_add_apply, hi1] at h3
    have := hcyc (max i N - i)
    omega
  exact ⟨fun i => ⟨hnot_dvd i, hne1 i⟩, hgrow_all, htend⟩
/-- Explicit base-17 runaway witness from Paper 1 (`lem:odd-runaway`): every odd `n ≡ 16 (mod 17)` repeats a -/
theorem lem_base17_runaway {n : ℕ} (hn1 : 1 ≤ n) (hn_odd : n % 2 = 1) (hn17 : n % 17 = 16) :
    (∀ i : ℕ, ¬ 17 ∣ (f_b 17)^[i] n ∧ (f_b 17)^[i] n ≠ 1) ∧
    (∀ i : ℕ, (f_b 17)^[i] n < (f_b 17)^[i + 10] n) ∧
    Filter.Tendsto (fun i => (f_b 17)^[i] n) Filter.atTop Filter.atTop := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv16 : padicValNat 2 16 = 4 := by rw [show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat.prime_pow]
  have hv2 : padicValNat 2 2 = 1 := padicValNat.self (by norm_num)
  have hv5 : padicValNat 2 5 = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  have hv8 : padicValNat 2 8 = 3 := by rw [show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  have hv14 : padicValNat 2 14 = 1 := by
    rw [show (14 : ℕ) = 2 * 7 by norm_num, padicValNat.mul (by omega) (by omega),
        hv2, padicValNat.eq_zero_of_not_dvd (by omega)]
  have hv10 : padicValNat 2 10 = 1 := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num, padicValNat.mul (by omega) (by omega),
        hv2, hv5]
  have hs0 : (cylStep 17)^[0] ⟨16, 1, 1⟩ = ⟨16, 1, 1⟩ := rfl
  have hs1 : (cylStep 17)^[1] ⟨16, 1, 1⟩ = ⟨2, 17, 5⟩ := by simp [cylStep, hv16]
  have hs2 : (cylStep 17)^[2] ⟨16, 1, 1⟩ = ⟨5, 35, 6⟩ := by rw [Function.iterate_succ_apply', hs1]; simp [cylStep]
  have hs3 : (cylStep 17)^[3] ⟨16, 1, 1⟩ = ⟨9, 48, 6⟩ := by
    rw [Function.iterate_succ_apply', hs2]; simp [cylStep, hv5]
  have hs4 : (cylStep 17)^[4] ⟨16, 1, 1⟩ = ⟨13, 24, 5⟩ := by rw [Function.iterate_succ_apply', hs3]; simp [cylStep]
  have hs5 : (cylStep 17)^[5] ⟨16, 1, 1⟩ = ⟨15, 12, 4⟩ := by rw [Function.iterate_succ_apply', hs4]; simp [cylStep]
  have hs6 : (cylStep 17)^[6] ⟨16, 1, 1⟩ = ⟨16, 6, 3⟩ := by rw [Function.iterate_succ_apply', hs5]; simp [cylStep]
  have hs7 : (cylStep 17)^[7] ⟨16, 1, 1⟩ = ⟨8, 3, 2⟩ := by rw [Function.iterate_succ_apply', hs6]; simp [cylStep]
  have hs8 : (cylStep 17)^[8] ⟨16, 1, 1⟩ = ⟨14, 25, 5⟩ := by
    rw [Function.iterate_succ_apply', hs7]; simp [cylStep, hv8]
  have hs9 : (cylStep 17)^[9] ⟨16, 1, 1⟩ = ⟨10, 31, 6⟩ := by
    rw [Function.iterate_succ_apply', hs8]; simp [cylStep, hv14]
  have hs10 : (cylStep 17)^[10] ⟨16, 1, 1⟩ = ⟨16, 55, 7⟩ := by
    rw [Function.iterate_succ_apply', hs9]; simp [cylStep, hv10]
  have hvalid : ∀ i ≤ 10, 1 ≤ ((cylStep 17)^[i] ⟨16, 1, 1⟩).x ∧
      ((cylStep 17)^[i] ⟨16, 1, 1⟩).x < 17 ∧ 1 ≤ ((cylStep 17)^[i] ⟨16, 1, 1⟩).j := by
    intro i hi
    interval_cases i
    · rw [hs0]; decide
    · rw [hs1]; decide
    · rw [hs2]; decide
    · rw [hs3]; decide
    · rw [hs4]; decide
    · rw [hs5]; decide
    · rw [hs6]; decide
    · rw [hs7]; decide
    · rw [hs8]; decide
    · rw [hs9]; decide
    · rw [hs10]; decide
  have hret : CylSubset 17 ((cylStep 17)^[10] ⟨16, 1, 1⟩) ((cylStep 17)^[0] ⟨16, 1, 1⟩) := by
    rw [hs10, hs0]; exact ⟨by decide, by decide, by decide⟩
  have hrun := lem_odd_runaway (b := 17) (x := 16) (k := 10) (p := 10)
    (by omega) (by decide) (by omega) (by omega) hvalid hret hn1 hn_odd hn17
  exact ⟨hrun.1, fun i => hrun.2.1 i (by omega), hrun.2.2⟩

/-! ## Theorem `thm:odd-densities`: Trapping and divergence densities -/
/-- Set of starts diverging to `∞` under `f_b`. -/
def DivSet (b : ℕ) : Set ℕ :=
  {n | 1 ≤ n ∧ Filter.Tendsto (fun i => (f_b b)^[i] n) Filter.atTop Filter.atTop}
/-- Theorem `thm:odd-densities`(1): `Z(b) ⊆ R(b)` and `DivSet(b) ∩ R(b) = ∅`. -/
theorem thm_odd_densities_disjoint {b : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1) :
    ZSet b ⊆ RSet b ∧ Disjoint (DivSet b) (RSet b) := by
  constructor
  · intro n ⟨hn1, j, hj⟩
    refine ⟨hn1, ?_⟩
    set y := (f_b b)^[j] n
    have hy_pos : 1 ≤ y := by
      have hstep_pos : ∀ m, 1 ≤ m → 1 ≤ f_b b m := by
        intro m hm
        by_cases hev : m % 2 = 0
        · rw [f_b_even hev]; omega
        · rw [f_b_odd (by omega)]; omega
      have : ∀ t, 1 ≤ (f_b b)^[t] n := by
        intro t; induction t with
        | zero => exact hn1
        | succ t iht => rw [Function.iterate_succ_apply']; exact hstep_pos _ iht
      exact this j
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let v := padicValNat 2 y; let m := y / 2 ^ v
    have hy_eq : y = 2 ^ v * m := (Nat.mul_div_cancel' pow_padicValNat_dvd).symm
    have hm_odd : m % 2 = 1 := by
      by_contra h
      have h2m : 2 ∣ m := by omega
      have h2v1 : 2 ^ (v + 1) ∣ y := by rw [hy_eq, pow_succ]; exact Nat.mul_dvd_mul_left (2 ^ v) h2m
      have := (padicValNat_dvd_iff_le (by omega : y ≠ 0)).mp h2v1
      omega
    have hcop : Nat.Coprime b (2 ^ v) := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).symm.pow_right v
    have hbm : b ∣ m := hcop.dvd_of_dvd_mul_left (hy_eq ▸ hj)
    have htrap := (thm_odd_trapdoor_multiple (v := v) hb3 hm_odd hbm).2.1; rw [← hy_eq] at htrap
    exact ⟨v + 1 + j, by rw [Function.iterate_add_apply]; exact htrap⟩
  · rw [Set.disjoint_left]; intro n hdiv hreach; obtain ⟨_, htend⟩ := hdiv; obtain ⟨_, k, hk⟩ := hreach
    have hcyc : ∀ t : ℕ, (f_b b)^[t] 1 ≤ 2 := by
      intro t
      have : (f_b b)^[t] 1 = 1 ∨ (f_b b)^[t] 1 = 2 := by
        induction t with
        | zero => left; rfl
        | succ t iht =>
          rw [Function.iterate_succ_apply']
          rcases iht with h | h <;> rw [h]
          · right; rw [f_b_odd (by decide), Nat.mod_eq_of_lt (by omega)]
          · left; rw [f_b_even (by decide)]
      omega
    obtain ⟨N, hN⟩ := (Filter.tendsto_atTop_atTop.mp htend) 3; have h3 := hN (max k N) (le_max_right k N)
    have hsplit : max k N = (max k N - k) + k := by omega
    rw [hsplit, Function.iterate_add_apply, hk] at h3
    have := hcyc (max k N - k)
    omega
/-- Counting function `|{n ∈ [1, N] | n ∈ S}| / N` as a real number. -/
noncomputable def countFrac (S : Set ℕ) (N : ℕ) : ℝ :=
  open Classical in (((Finset.Icc 1 N).filter (· ∈ S)).card : ℝ) / (N : ℝ)
/-- Theorem `thm:odd-densities`(3): Density squeeze — if `Z ⊆ R`, `D ⊆ Div`, `Div ∩ R = ∅`, `τ + ρ = 1`, and -/
theorem thm_odd_densities_squeeze {Z R D Div : Set ℕ} {τ ρ : ℝ}
    (hZR : Z ⊆ R) (hDDiv : D ⊆ Div) (hdisj : Disjoint Div R) (hsum : τ + ρ = 1)
    (hZ_low : ∀ ε > 0, ∀ᶠ N in atTop, τ - ε ≤ countFrac Z N)
    (hD_low : ∀ ε > 0, ∀ᶠ N in atTop, ρ - ε ≤ countFrac D N) :
    Tendsto (countFrac Z) atTop (𝓝 τ) ∧
    Tendsto (countFrac R) atTop (𝓝 τ) ∧
    Tendsto (countFrac Div) atTop (𝓝 ρ) := by
  classical
  have hmono : ∀ {A B : Set ℕ}, A ⊆ B → ∀ N, countFrac A N ≤ countFrac B N := by
    intro A B hAB N; unfold countFrac
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
    exact_mod_cast Finset.card_le_card fun n hn => by
      simp only [Finset.mem_filter] at hn ⊢; exact ⟨hn.1, hAB hn.2⟩
  have hdisj_sum : ∀ N, 1 ≤ N → countFrac Div N + countFrac R N ≤ 1 := by
    intro N hN; unfold countFrac; rw [← add_div, div_le_one (by exact_mod_cast (by omega : 0 < N))]
    have hdisjF : Disjoint ((Finset.Icc 1 N).filter (· ∈ Div))
        ((Finset.Icc 1 N).filter (· ∈ R)) := by
      rw [Finset.disjoint_left]; intro n h1 h2
      simp only [Finset.mem_filter] at h1 h2; exact Set.disjoint_left.mp hdisj h1.2 h2.2
    have hsub : ((Finset.Icc 1 N).filter (· ∈ Div)) ∪ ((Finset.Icc 1 N).filter (· ∈ R)) ⊆
        Finset.Icc 1 N := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hcard : ((Finset.Icc 1 N).filter (· ∈ Div)).card +
        ((Finset.Icc 1 N).filter (· ∈ R)).card ≤ (Finset.Icc 1 N).card := by
      rw [← Finset.card_union_of_disjoint hdisjF]; exact Finset.card_le_card hsub
    have hIcc : (Finset.Icc 1 N).card = N := by simp
    rw [hIcc] at hcard; exact_mod_cast hcard
  have hlim : ∀ (f : ℕ → ℝ) (L : ℝ),
      (∀ ε > 0, ∀ᶠ N in atTop, L - ε ≤ f N ∧ f N ≤ L + ε) → Tendsto f atTop (𝓝 L) := by
    intro f L h; rw [Metric.tendsto_atTop]; intro ε hε
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (h (ε / 2) (by linarith))
    refine ⟨N0, fun N hN => ?_⟩
    rw [Real.dist_eq, abs_lt]; have ⟨hlo, hhi⟩ := hN0 N hN
    constructor <;> linarith
  refine ⟨hlim _ τ fun ε hε => ?_, hlim _ τ fun ε hε => ?_, hlim _ ρ fun ε hε => ?_⟩
  · filter_upwards [hZ_low ε hε, hD_low ε hε, Filter.eventually_ge_atTop 1] with N hZ hD hN1
    have h1 := hmono hZR N; have h2 := hmono hDDiv N; have h3 := hdisj_sum N hN1; exact ⟨hZ, by linarith⟩
  · filter_upwards [hZ_low ε hε, hD_low ε hε, Filter.eventually_ge_atTop 1] with N hZ hD hN1
    have h1 := hmono hZR N; have h2 := hmono hDDiv N; have h3 := hdisj_sum N hN1; exact ⟨by linarith, by linarith⟩
  · filter_upwards [hZ_low ε hε, hD_low ε hε, Filter.eventually_ge_atTop 1] with N hZ hD hN1
    have h1 := hmono hZR N; have h2 := hmono hDDiv N; have h3 := hdisj_sum N hN1; exact ⟨by linarith, by linarith⟩
/-- Theorem `thm:odd-densities`(5): If odd `b ≥ 3` has a prime factor `p ≡ 3 (mod 4)` (rootless), then `Z(b)` has -/
theorem thm_odd_densities_rootless {b p : ℕ} (hb3 : 3 ≤ b) (hb_odd : b % 2 = 1)
    (hp : Nat.Prime p) (hp3 : p % 4 = 3) (hpb : p ∣ b) :
    Tendsto (countFrac (ZSet b)) atTop (𝓝 (1 / (b : ℝ))) := by
  classical
  have hZ := (thm_odd_trapdoor_rootless hb_odd hp hp3 hpb).2
  have hcard : ∀ N : ℕ, (((Finset.Icc 1 N).filter (· ∈ ZSet b)).card : ℝ) =
      ((N / b : ℕ) : ℝ) := by
    intro N
    classical
    have hbij : ((Finset.Icc 1 N).filter (· ∈ ZSet b)).card = (Finset.Icc 1 (N / b)).card := by
      refine Finset.card_bij (fun n _ => n / b) ?_ ?_ ?_
      · intro n hn; simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢; obtain ⟨hn1, hbn⟩ := (hZ n).mp hn.2
        exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hbn) (by omega),
               Nat.div_le_div_right hn.1.2⟩
      · intro n₁ hn₁ n₂ hn₂ hEq; simp only [Finset.mem_filter] at hn₁ hn₂
        have h1 := ((hZ n₁).mp hn₁.2).2; have h2 := ((hZ n₂).mp hn₂.2).2
        rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, hEq]
      · intro k hk; simp only [Finset.mem_Icc] at hk
        refine ⟨b * k, ?_, Nat.mul_div_cancel_left k (by omega)⟩
        simp only [Finset.mem_filter, Finset.mem_Icc]
        have hle : b * k ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hk.2 |> fun h => by linarith
        exact ⟨⟨by nlinarith, hle⟩, (hZ (b * k)).mpr ⟨by nlinarith, dvd_mul_right b k⟩⟩
    rw [hbij]; simp
  rw [Metric.tendsto_atTop]; intro ε hε; obtain ⟨N0, hN0⟩ := exists_nat_gt (1 / ε)
  refine ⟨max 1 N0, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_left hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  unfold countFrac; rw [hcard N, Real.dist_eq, abs_lt]
  have hdiv_le : ((N / b : ℕ) : ℝ) * (b : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.div_mul_le_self N b
  have hdiv_gt : (N : ℝ) - (b : ℝ) < ((N / b : ℕ) : ℝ) * (b : ℝ) := by
    have : N < (N / b) * b + b := by
      have h := Nat.div_add_mod N b; have hm := Nat.mod_lt N (by omega : 0 < b)
      nlinarith
    have hR : (N : ℝ) < ((N / b : ℕ) : ℝ) * (b : ℝ) + (b : ℝ) := by exact_mod_cast this
    linarith
  have hupper : ((N / b : ℕ) : ℝ) / (N : ℝ) ≤ 1 / (b : ℝ) := by rw [div_le_div_iff₀ hNpos hbpos]; linarith
  have hlower : 1 / (b : ℝ) - 1 / (N : ℝ) < ((N / b : ℕ) : ℝ) / (N : ℝ) := by
    have h1 : (N : ℝ) / (b : ℝ) - 1 < ((N / b : ℕ) : ℝ) := by rw [sub_lt_iff_lt_add, div_lt_iff₀ hbpos]; linarith
    have h2 : ((N : ℝ) / (b : ℝ) - 1) / (N : ℝ) < ((N / b : ℕ) : ℝ) / (N : ℝ) := div_lt_div_of_pos_right h1 hNpos
    have h3 : ((N : ℝ) / (b : ℝ) - 1) / (N : ℝ) = 1 / (b : ℝ) - 1 / (N : ℝ) := by field_simp
    linarith
  have h1N : 1 / (N : ℝ) < ε := by
    rw [div_lt_iff₀ hNpos]
    have hN0_le : (N0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_of_max_le_right hN
    have : 1 / ε < (N : ℝ) := lt_of_lt_of_le hN0 hN0_le
    exact (div_lt_iff₀ hε).mp this |> fun h => by linarith
  constructor <;> linarith

end Ouroboros
