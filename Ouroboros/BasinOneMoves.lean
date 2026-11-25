module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic
public import Ouroboros.Defs
public import Ouroboros.BasinFive
@[expose] public section

/-! # Section 5 (Part 3): Move classification on `A ∪ B ∪ C` and no-residue-size-bound -/

namespace Ouroboros
/-- Membership in `A ∪ B ∪ C`: odd integers with residue `1`, `0`, or `2 (mod 15)`. -/
def InABC15 (o : ℕ) : Prop := 0 < o ∧ o % 2 = 1 ∧ (o % 15 = 1 ∨ o % 15 = 0 ∨ o % 15 = 2)
/-- A single allowed backward move `(d, v)` from `o` to `m` inside `A ∪ B ∪ C`. -/
def IsABCMove (o d_mv v m : ℕ) : Prop := InABC15 o ∧ InABC15 m ∧ 1 ≤ v ∧ d m = d_mv ∧ d_mv * m + 1 = 2 ^ v * o
/-- Reachability by a finite sequence of backward moves in `A ∪ B ∪ C` (empty path included). -/
inductive ABCReach : ℕ → ℕ → Prop
  | refl (o : ℕ) (ho : InABC15 o) : ABCReach o o
  | step {o d_mv v m n : ℕ} (hmv : IsABCMove o d_mv v m) (hrest : ABCReach m n) : ABCReach o n
private lemma two_pow_mod_3 (v : ℕ) : (v % 2 = 0 → 2 ^ v % 3 = 1) ∧ (v % 2 = 1 → 2 ^ v % 3 = 2) := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [pow_succ, Nat.mul_mod]
    constructor <;> intro h
    · have := ih.2 (by omega); rw [this]
    · have := ih.1 (by omega); rw [this]
private lemma two_pow_mod_5 (v : ℕ) :
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
/-- Lemma (`lem:basin1-moves`, part 1): exact 4-case move classification on `A ∪ B ∪ C` (no odd predecessor ends -/
theorem lem_basin1_moves_classify {o v m : ℕ} (ho : InABC15 o) (hv : 1 ≤ v)
    (hm_odd : m % 2 = 1) (heq : d m * m + 1 = 2 ^ v * o) :
    d m ≠ 3 ∧ d m ≠ 9 ∧ InABC15 m ∧
    ((o % 15 = 1 ∧ d m = 1 ∧ v % 4 = 1 ∧ m % 15 = 1) ∨
     (o % 15 = 2 ∧ d m = 1 ∧ v % 4 = 0 ∧ m % 15 = 1) ∨
     ((o % 15 = 1 ∨ o % 15 = 2) ∧ d m = 5 ∧ (2 ^ v * o) % 25 = 1 ∧ m % 15 = 0) ∨
     (o % 15 = 0 ∧ d m = 7 ∧ (2 ^ v * o) % 7 = 1 ∧ m % 15 = 2)) := by
  obtain ⟨ho_pos, ho_odd, ho15⟩ := ho
  have hd_cases : d m = 1 ∨ d m = 3 ∨ d m = 5 ∨ d m = 7 ∨ d m = 9 := by unfold d; omega
  have hm_pos : 0 < m := by
    have : 2 ≤ 2 ^ v * o := by
      have h2v : 2 ≤ 2 ^ v := calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv
      nlinarith
    rcases hd_cases with h | h | h | h | h <;> (rw [h] at heq; omega)
  have h2_3 := two_pow_mod_3 v; have h2_5 := two_pow_mod_5 v
  have hmod3 : (2 ^ v * o) % 3 = ((2 ^ v % 3) * (o % 3)) % 3 := Nat.mul_mod _ _ 3
  have hmod5 : (2 ^ v * o) % 5 = ((2 ^ v % 5) * (o % 5)) % 5 := Nat.mul_mod _ _ 5
  have hv4 : v % 4 = 0 ∨ v % 4 = 1 ∨ v % 4 = 2 ∨ v % 4 = 3 := by omega
  rcases hd_cases with hd | hd | hd | hd | hd
  ·
    have hcond : (2 ^ v * o) % 5 = 2 := by
      have := (lemma_odd_predecessors ho_pos ho_odd hv 0).mp ⟨hm_odd, hd, heq⟩
      exact this.1
    rw [hd, one_mul] at heq
    rcases ho15 with h15 | h15 | h15
    ·
      have hv1 : v % 4 = 1 := by
        rcases hv4 with h | h | h | h
        · rw [h2_5.1 h, show o % 5 = 1 by omega] at hmod5; omega
        · exact h
        · rw [h2_5.2.2.1 h, show o % 5 = 1 by omega] at hmod5; omega
        · rw [h2_5.2.2.2 h, show o % 5 = 1 by omega] at hmod5; omega
      have hm3 : m % 3 = 1 := by
        have h2v3 : 2 ^ v % 3 = 2 := h2_3.2 (by omega)
        rw [h2v3, show o % 3 = 1 by omega] at hmod3; omega
      have hm5 : m % 5 = 1 := by omega
      have hm15 : m % 15 = 1 := by omega
      exact ⟨by omega, by omega, ⟨hm_pos, hm_odd, Or.inl hm15⟩, Or.inl ⟨h15, hd, hv1, hm15⟩⟩
    ·
      rw [show o % 5 = 0 by omega] at hmod5; omega
    ·
      have hv0 : v % 4 = 0 := by
        rcases hv4 with h | h | h | h
        · exact h
        · rw [h2_5.2.1 h, show o % 5 = 2 by omega] at hmod5; omega
        · rw [h2_5.2.2.1 h, show o % 5 = 2 by omega] at hmod5; omega
        · rw [h2_5.2.2.2 h, show o % 5 = 2 by omega] at hmod5; omega
      have hm3 : m % 3 = 1 := by
        have h2v3 : 2 ^ v % 3 = 1 := h2_3.1 (by omega)
        rw [h2v3, show o % 3 = 2 by omega] at hmod3; omega
      have hm15 : m % 15 = 1 := by omega
      exact ⟨by omega, by omega, ⟨hm_pos, hm_odd, Or.inl hm15⟩, Or.inr (Or.inl ⟨h15, hd, hv0, hm15⟩)⟩
  ·
    have hcond := ((lemma_odd_predecessors ho_pos ho_odd hv 1).mp ⟨hm_odd, hd, heq⟩).1; simp only [predCond] at hcond
    obtain ⟨hc5, hc3⟩ := hcond
    rcases ho15 with h15 | h15 | h15
    · rcases hv4 with h | h | h | h
      · rw [h2_5.1 h, show o % 5 = 1 by omega] at hmod5; omega
      · rw [h2_5.2.1 h, show o % 5 = 1 by omega] at hmod5; omega
      · rw [h2_5.2.2.1 h, show o % 5 = 1 by omega] at hmod5; omega
      · rw [h2_5.2.2.2 h, show o % 5 = 1 by omega] at hmod5; omega
    · rw [show o % 3 = 0 by omega] at hmod3; omega
    · rcases hv4 with h | h | h | h
      · rw [h2_5.1 h, show o % 5 = 2 by omega] at hmod5; omega
      · rw [h2_5.2.1 h, show o % 5 = 2 by omega] at hmod5; omega
      · rw [h2_5.2.2.1 h, show o % 5 = 2 by omega] at hmod5; omega
      · rw [h2_5.2.2.2 h, show o % 5 = 2 by omega] at hmod5; omega
  ·
    have hcond : (2 ^ v * o) % 25 = 1 := ((lemma_odd_predecessors ho_pos ho_odd hv 2).mp ⟨hm_odd, hd, heq⟩).1
    have h5eq1 : (2 ^ v * o) % 5 = 1 := by omega
    rw [hd] at heq
    rcases ho15 with h15 | h15 | h15
    ·
      have hv0 : v % 4 = 0 := by
        rcases hv4 with h | h | h | h
        · exact h
        · rw [h2_5.2.1 h, show o % 5 = 1 by omega] at hmod5; omega
        · rw [h2_5.2.2.1 h, show o % 5 = 1 by omega] at hmod5; omega
        · rw [h2_5.2.2.2 h, show o % 5 = 1 by omega] at hmod5; omega
      have h2v3 : 2 ^ v % 3 = 1 := h2_3.1 (by omega)
      rw [h2v3, show o % 3 = 1 by omega] at hmod3
      have hm5 : m % 5 = 0 := by unfold d at hd; omega
      have hm15 : m % 15 = 0 := by omega
      exact ⟨by omega, by omega, ⟨hm_pos, hm_odd, Or.inr (Or.inl hm15)⟩,
             Or.inr (Or.inr (Or.inl ⟨Or.inl h15, hd, hcond, hm15⟩))⟩
    · rw [show o % 5 = 0 by omega] at hmod5; omega
    ·
      have hv3 : v % 4 = 3 := by
        rcases hv4 with h | h | h | h
        · rw [h2_5.1 h, show o % 5 = 2 by omega] at hmod5; omega
        · rw [h2_5.2.1 h, show o % 5 = 2 by omega] at hmod5; omega
        · rw [h2_5.2.2.1 h, show o % 5 = 2 by omega] at hmod5; omega
        · exact h
      have h2v3 : 2 ^ v % 3 = 2 := h2_3.2 (by omega)
      rw [h2v3, show o % 3 = 2 by omega] at hmod3
      have hm5 : m % 5 = 0 := by unfold d at hd; omega
      have hm15 : m % 15 = 0 := by omega
      exact ⟨by omega, by omega, ⟨hm_pos, hm_odd, Or.inr (Or.inl hm15)⟩,
             Or.inr (Or.inr (Or.inl ⟨Or.inr h15, hd, hcond, hm15⟩))⟩
  ·
    have hcond := ((lemma_odd_predecessors ho_pos ho_odd hv 3).mp ⟨hm_odd, hd, heq⟩).1; simp only [predCond] at hcond
    obtain ⟨hc5, hc7⟩ := hcond; rw [hd] at heq
    rcases ho15 with h15 | h15 | h15
    · rcases hv4 with h | h | h | h
      · rw [h2_5.1 h, show o % 5 = 1 by omega] at hmod5; omega
      · rw [h2_5.2.1 h, show o % 5 = 1 by omega] at hmod5; omega
      · rw [h2_5.2.2.1 h, show o % 5 = 1 by omega] at hmod5; omega
      · rw [h2_5.2.2.2 h, show o % 5 = 1 by omega] at hmod5; omega
    · rw [show o % 3 = 0 by omega] at hmod3
      have hm5 : m % 5 = 2 := by unfold d at hd; omega
      have hm15 : m % 15 = 2 := by omega
      exact ⟨by omega, by omega, ⟨hm_pos, hm_odd, Or.inr (Or.inr hm15)⟩,
             Or.inr (Or.inr (Or.inr ⟨h15, hd, hc7, hm15⟩))⟩
    · rcases hv4 with h | h | h | h
      · rw [h2_5.1 h, show o % 5 = 2 by omega] at hmod5; omega
      · rw [h2_5.2.1 h, show o % 5 = 2 by omega] at hmod5; omega
      · rw [h2_5.2.2.1 h, show o % 5 = 2 by omega] at hmod5; omega
      · rw [h2_5.2.2.2 h, show o % 5 = 2 by omega] at hmod5; omega
  ·
    have hcond := ((lemma_odd_predecessors ho_pos ho_odd hv 4).mp ⟨hm_odd, hd, heq⟩).1; simp only [predCond] at hcond
    obtain ⟨hc5, hc9⟩ := hcond
    rcases ho15 with h15 | h15 | h15
    ·
      have hv1 : v % 4 = 1 := by
        rcases hv4 with h | h | h | h
        · rw [h2_5.1 h, show o % 5 = 1 by omega] at hmod5; omega
        · exact h
        · rw [h2_5.2.2.1 h, show o % 5 = 1 by omega] at hmod5; omega
        · rw [h2_5.2.2.2 h, show o % 5 = 1 by omega] at hmod5; omega
      have h2v3 : 2 ^ v % 3 = 2 := h2_3.2 (by omega)
      rw [h2v3, show o % 3 = 1 by omega] at hmod3; omega
    · rw [show o % 3 = 0 by omega] at hmod3; omega
    ·
      have hv0 : v % 4 = 0 := by
        rcases hv4 with h | h | h | h
        · exact h
        · rw [h2_5.2.1 h, show o % 5 = 2 by omega] at hmod5; omega
        · rw [h2_5.2.2.1 h, show o % 5 = 2 by omega] at hmod5; omega
        · rw [h2_5.2.2.2 h, show o % 5 = 2 by omega] at hmod5; omega
      have h2v3 : 2 ^ v % 3 = 1 := h2_3.1 (by omega)
      rw [h2v3, show o % 3 = 2 by omega] at hmod3; omega

/-! ## Proposition `prop:no-residue-size-bound` -/
/-- One contracting double move `(7, 1)` then `(5, 3)` on `B`: if `o % 30 = 15` and `175 ∣ 19 * o + 15`, then -/
private lemma double_move_B {o : ℕ} (ho30 : o % 30 = 15) (hdvd : 175 ∣ 19 * o + 15) :
    ∃ o' : ℕ, o' % 30 = 15 ∧ ABCReach o o' ∧ 35 * (19 * o' + 15) = 16 * (19 * o + 15) := by
  have ho_pos : 0 < o := by omega
  have ho_abc : InABC15 o := ⟨ho_pos, by omega, Or.inr (Or.inl (by omega))⟩
  obtain ⟨k, hk⟩ := hdvd; have h7dvd : 7 ∣ 2 * o - 1 := by exact ⟨3 * o + 2 - 25 * k, by omega⟩
  have h25_rhs : 25 ∣ 16 * o - 15 := by
    have h25_o : 25 ∣ o - 15 := ⟨28 * k - (3 * o + 3), by omega⟩
    obtain ⟨q, hq⟩ := h25_o; exact ⟨16 * q + 9, by omega⟩
  clear hk; obtain ⟨m1, hm1_def⟩ := h7dvd; have hm1_eq : 7 * m1 + 1 = 2 * o := by omega
  have hm1_abc : InABC15 m1 := ⟨by omega, by omega, Or.inr (Or.inr (by omega))⟩
  have hmv1 : IsABCMove o 7 1 m1 := ⟨ho_abc, hm1_abc, by omega, by unfold d; omega, by simpa using hm1_eq⟩
  have h25dvd : 25 ∣ 8 * m1 - 1 := by
    have h7mul : 7 * (8 * m1 - 1) = 16 * o - 15 := by omega
    rw [← h7mul] at h25_rhs; exact (by decide : Nat.Coprime 25 7).dvd_of_dvd_mul_left h25_rhs
  have h5dvd : 5 ∣ 8 * m1 - 1 := dvd_trans (by decide : 5 ∣ 25) h25dvd
  obtain ⟨o', ho'_def⟩ := h5dvd; have ho'_eq : 5 * o' + 1 = 8 * m1 := by omega
  have ho'_mod30 : o' % 30 = 15 := by
    have h5o' : 5 ∣ o' := by obtain ⟨t, ht⟩ := h25dvd; exact ⟨t, by omega⟩
    omega
  have ho'_abc : InABC15 o' := ⟨by omega, by omega, Or.inr (Or.inl (by omega))⟩
  have hmv2 : IsABCMove m1 5 3 o' := ⟨hm1_abc, ho'_abc, by omega, by unfold d; omega, by simpa using ho'_eq⟩
  refine ⟨o', ho'_mod30, ABCReach.step hmv1 (ABCReach.step hmv2 (ABCReach.refl o' ho'_abc)), ?_⟩
  omega
/-- Iterating the contracting double move `r` times on `B`. -/
private lemma iter_double_move_B :
    ∀ (r o : ℕ), o % 30 = 15 → 5 * 35 ^ r ∣ 19 * o + 15 →
      ∃ n : ℕ, 1 ≤ n ∧ ABCReach o n ∧ 35 ^ r * (19 * n + 15) = 16 ^ r * (19 * o + 15) := by
  intro r
  induction r with
  | zero =>
    intro o ho30 _; exact ⟨o, by omega, ABCReach.refl o ⟨by omega, by omega, Or.inr (Or.inl (by omega))⟩, by simp⟩
  | succ r ih =>
    intro o ho30 hdvd
    have h175 : 175 ∣ 19 * o + 15 := by
      have : 175 ∣ 5 * 35 ^ (r + 1) := by rw [pow_succ']; exact ⟨35 ^ r, by ring⟩
      exact dvd_trans this hdvd
    obtain ⟨o', ho'30, hreach1, heq1⟩ := double_move_B ho30 h175
    have hdvd' : 5 * 35 ^ r ∣ 19 * o' + 15 := by
      obtain ⟨k, hk⟩ := hdvd
      have hmul : 35 * (19 * o' + 15) = 35 * (16 * (5 * 35 ^ r * k)) := by rw [heq1, hk, pow_succ']; ring
      have hdiv : 19 * o' + 15 = 16 * (5 * 35 ^ r * k) := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 35) hmul
      exact ⟨16 * k, by linarith⟩
    obtain ⟨n, hn1, hreach2, heq2⟩ := ih o' ho'30 hdvd'
    have htrans : ∀ {a b c : ℕ}, ABCReach a b → ABCReach b c → ABCReach a c := by
      intro a b c hab hbc
      induction hab with
      | refl _ _ => exact hbc
      | step hmv _ ihab => exact ABCReach.step hmv (ihab hbc)
    refine ⟨n, hn1, htrans hreach1 hreach2, ?_⟩
    calc 35 ^ (r + 1) * (19 * n + 15)
        = 35 * (35 ^ r * (19 * n + 15)) := by rw [pow_succ']; ring
      _ = 35 * (16 ^ r * (19 * o' + 15)) := by rw [heq2]
      _ = 16 ^ r * (35 * (19 * o' + 15)) := by ring
      _ = 16 ^ r * (16 * (19 * o + 15)) := by rw [heq1]
      _ = 16 ^ (r + 1) * (19 * o + 15) := by rw [pow_succ']; ring
/-- Proposition (`prop:no-residue-size-bound`): for every modulus `Q ≥ 1`, exponent `c > 0`, and positive weight -/
theorem prop_no_residue_size_bound {Q : ℕ} (hQ : 1 ≤ Q) {c : ℝ} (hc : 0 < c)
    (w : Fin Q → ℝ) :
    ∃ (o n : ℕ), o % 30 = 15 ∧ 1 ≤ n ∧ ABCReach o n ∧
      w ⟨o % Q, Nat.mod_lt o (by omega)⟩ * ((n : ℝ) / (o : ℝ)) ^ c < 1 := by
  let M : ℝ := 1 + ∑ q : Fin Q, |w q|
  have hM_pos : 0 < M := by
    have : 0 ≤ ∑ q : Fin Q, |w q| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hw_le : ∀ q : Fin Q, w q ≤ M := fun q => by
    have h1 : w q ≤ |w q| := le_abs_self _
    have h2 : |w q| ≤ ∑ r : Fin Q, |w r| :=
      Finset.single_le_sum (f := fun r => |w r|) (fun _ _ => abs_nonneg _) (Finset.mem_univ q)
    linarith
  set lam : ℝ := ((16 / 35 : ℝ)) ^ c
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos (by norm_num) c
  have hlam_lt1 : lam < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hc
  have htend : Filter.Tendsto (fun r : ℕ => M * (2 : ℝ) ^ c * lam ^ r) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam_pos.le hlam_lt1).const_mul (M * (2 : ℝ) ^ c)
  obtain ⟨r, hsmall⟩ := (htend.eventually (gt_mem_nhds zero_lt_one)).exists; set K := 5 * 35 ^ r
  have hK_pos : 0 < K := by positivity
  have hcop19 : Nat.Coprime 19 K := by
    refine Nat.Coprime.mul_right (by decide) ?_
    exact (by decide : Nat.Coprime 19 35).pow_right r
  have hcop6 : Nat.Coprime 6 K := by
    refine Nat.Coprime.mul_right (by decide) ?_
    exact (by decide : Nat.Coprime 6 35).pow_right r
  let u19 : (ZMod K)ˣ := ZMod.unitOfCoprime 19 hcop19
  let a_z : ZMod K := -(15 : ZMod K) * (u19⁻¹ : (ZMod K)ˣ)
  let e := ZMod.chineseRemainder hcop6
  let o_z : ZMod (6 * K) := e.symm ((3 : ZMod 6), a_z)
  let o : ℕ := o_z.val + 6 * K
  have hcast : (o : ZMod (6 * K)) = o_z := by
    simp only [o, Nat.cast_add, ZMod.natCast_self, add_zero]; exact ZMod.natCast_zmod_val o_z
  have he_eq : ((o : ZMod 6), (o : ZMod K)) = ((3 : ZMod 6), a_z) := by
    have h1 : e (o : ZMod (6 * K)) = ((o : ZMod 6), (o : ZMod K)) := map_natCast e o
    rw [← h1, hcast]; exact e.apply_symm_apply ((3 : ZMod 6), a_z)
  have ho_mod6 : o % 6 = 3 := by
    have h1 : (o : ZMod 6) = (3 : ZMod 6) := congr_arg Prod.fst he_eq
    have h2 : o % 6 = 3 % 6 := (ZMod.natCast_eq_natCast_iff' o 3 6).mp h1; simpa using h2
  have ho_modK : K ∣ 19 * o + 15 := by
    have h1 : (o : ZMod K) = a_z := congr_arg Prod.snd he_eq
    have hzero : ((19 * o + 15 : ℕ) : ZMod K) = 0 := by
      push_cast; rw [h1]
      have hcoe : (19 : ZMod K) = (u19 : ZMod K) := by simp [u19]
      rw [hcoe]; dsimp only [a_z]
      have hinv : (u19 : ZMod K) * (-(15 : ZMod K) * (u19⁻¹ : (ZMod K)ˣ)) = -(15 : ZMod K) := by
        rw [mul_left_comm, Units.mul_inv, mul_one]
      rw [hinv, neg_add_cancel]
    exact (ZMod.natCast_eq_zero_iff _ _).mp hzero
  have ho_mod5 : o % 5 = 0 := by
    have h5K : 5 ∣ K := dvd_mul_right 5 _; have h5 : 5 ∣ 19 * o + 15 := dvd_trans h5K ho_modK; omega
  have ho30 : o % 30 = 15 := by omega
  obtain ⟨n, hn1, hreach, heq⟩ := iter_double_move_B r o ho30 ho_modK
  refine ⟨o, n, ho30, hn1, hreach, ?_⟩
  have hratio : (n : ℝ) / (o : ℝ) ≤ 2 * (16 / 35 : ℝ) ^ r := by
    have ho_pos : (0 : ℝ) < (o : ℝ) := by exact_mod_cast (by omega : 0 < o)
    have h15_le : 15 ≤ 19 * o := by omega
    have hnat_le : 35 ^ r * (19 * n) ≤ 16 ^ r * (38 * o) := by
      have h1 : 35 ^ r * (19 * n) ≤ 35 ^ r * (19 * n + 15) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      have h2 : 16 ^ r * (19 * o + 15) ≤ 16 ^ r * (38 * o) := Nat.mul_le_mul_left _ (by omega)
      omega
    have hR : (35 : ℝ) ^ r * (19 * (n : ℝ)) ≤ (16 : ℝ) ^ r * (38 * (o : ℝ)) := by exact_mod_cast hnat_le
    rw [div_le_iff₀ ho_pos, div_pow]
    have h35 : (0 : ℝ) < (35 : ℝ) ^ r := by positivity
    have hgoal : (n : ℝ) * (35 : ℝ) ^ r ≤ 2 * (16 : ℝ) ^ r * (o : ℝ) := by linarith
    calc (n : ℝ) = (n : ℝ) * (35 : ℝ) ^ r / (35 : ℝ) ^ r := by field_simp
      _ ≤ 2 * (16 : ℝ) ^ r * (o : ℝ) / (35 : ℝ) ^ r := div_le_div_of_nonneg_right hgoal h35.le
      _ = 2 * ((16 : ℝ) ^ r / (35 : ℝ) ^ r) * (o : ℝ) := by ring
  have hpow : ((n : ℝ) / (o : ℝ)) ^ c ≤ (2 : ℝ) ^ c * lam ^ r := by
    calc ((n : ℝ) / (o : ℝ)) ^ c
        ≤ (2 * (16 / 35 : ℝ) ^ r) ^ c := Real.rpow_le_rpow (by positivity) hratio hc.le
      _ = (2 : ℝ) ^ c * ((16 / 35 : ℝ) ^ r) ^ c := Real.mul_rpow (by norm_num) (by positivity)
      _ = (2 : ℝ) ^ c * lam ^ r := by
          congr 1
          rw [← Real.rpow_natCast ((16 / 35 : ℝ)) r, ← Real.rpow_mul (by norm_num),
              mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  calc w ⟨o % Q, Nat.mod_lt o (by omega)⟩ * ((n : ℝ) / (o : ℝ)) ^ c
      ≤ M * ((n : ℝ) / (o : ℝ)) ^ c := mul_le_mul_of_nonneg_right (hw_le _) (by positivity)
    _ ≤ M * ((2 : ℝ) ^ c * lam ^ r) := mul_le_mul_of_nonneg_left hpow hM_pos.le
    _ = M * (2 : ℝ) ^ c * lam ^ r := by ring
    _ < 1 := hsmall

end Ouroboros
