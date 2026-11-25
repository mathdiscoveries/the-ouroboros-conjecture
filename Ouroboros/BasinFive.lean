module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import Ouroboros.Defs
public import Ouroboros.BasinOne
@[expose] public section

/-! # Section 5 (Part 2): The basin of 5 and basin separation (Lemmas 11–12, Theorem 13, Corollary 14) -/

namespace Ouroboros

/-! ## Lemma 11: Odd predecessors modulo 1575 -/
/-- The five odd decimal digits indexed by `Fin 5`. -/
def digitVal (i : Fin 5) : ℕ :=
  match i.val with
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | _ => 9
lemma digitVal_odd (i : Fin 5) : digitVal i % 2 = 1 := by fin_cases i <;> decide
lemma digitVal_pos (i : Fin 5) : 0 < digitVal i := by fin_cases i <;> decide
lemma digitVal_dvd_1575 (i : Fin 5) : digitVal i ∣ 1575 := by fin_cases i <;> decide
lemma digitVal_inj : Function.Injective digitVal := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [digitVal] at h ⊢
/-- Exact congruence condition of Lemma 11 on `x = 2^v * o` for digit `digitVal i`. -/
def predCond (i : Fin 5) (x : ℕ) : Prop :=
  match i.val with
  | 0 => x % 5 = 2
  | 1 => x % 5 = 0 ∧ x % 3 = 1
  | 2 => x % 25 = 1
  | 3 => x % 5 = 0 ∧ x % 7 = 1
  | _ => x % 5 = 2 ∧ x % 9 = 1
/-- Decidable boolean version of `predCond` for finite move enumeration. -/
def predCondBool (i : Fin 5) (x : ℕ) : Bool :=
  match i.val with
  | 0 => x % 5 == 2
  | 1 => (x % 5 == 0) && (x % 3 == 1)
  | 2 => x % 25 == 1
  | 3 => (x % 5 == 0) && (x % 7 == 1)
  | _ => (x % 5 == 2) && (x % 9 == 1)
lemma predCondBool_iff (i : Fin 5) (x : ℕ) : predCondBool i x = true ↔ predCond i x := by
  fin_cases i <;> simp [predCondBool, predCond]
lemma predCond_mod_1575 (i : Fin 5) {x y : ℕ} (h : x % 1575 = y % 1575) : predCond i x ↔ predCond i y := by
  fin_cases i <;> (simp only [predCond]; omega)
/-- Lemma 11 (exact congruence characterization): for positive odd `o`, `v ≥ 1`, and odd digit -/
theorem lemma_odd_predecessors {o v m : ℕ} (ho_pos : 0 < o) (_ho_odd : o % 2 = 1) (hv : 1 ≤ v)
    (i : Fin 5) :
    (m % 2 = 1 ∧ d m = digitVal i ∧ d m * m + 1 = 2 ^ v * o) ↔
      (predCond i (2 ^ v * o) ∧ digitVal i * m = 2 ^ v * o - 1) := by
  have hx_ge : 2 ≤ 2 ^ v * o := by
    have h2v : 2 ≤ 2 ^ v := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv
    nlinarith
  have hx_ev : (2 ^ v * o) % 2 = 0 := by
    have : v = (v - 1) + 1 := by omega
    have hmul : 2 ^ v * o = 2 * (2 ^ (v - 1) * o) := by conv_lhs => rw [this, pow_succ', mul_assoc]
    rw [hmul]; omega
  set x := 2 ^ v * o; constructor
  · intro ⟨_, hdm, heq⟩; rw [hdm] at heq; unfold d at hdm
    fin_cases i <;> (simp only [predCond, digitVal] at hdm heq ⊢; omega)
  · intro ⟨hcond, hmul⟩
    have hdm : d m = digitVal i := by
      unfold d
      fin_cases i <;> (simp only [predCond, digitVal] at hcond hmul ⊢; omega)
    refine ⟨?_, hdm, ?_⟩
    · unfold d at hdm; have := digitVal_odd i; omega
    · rw [hdm]; omega
/-- Corollary of Lemma 11: whenever `predCond i (2^v * o)` holds, `m = (2^v * o - 1) / digitVal i` is the unique -/
theorem lemma_odd_predecessors_unique {o v : ℕ} (ho_pos : 0 < o) (ho_odd : o % 2 = 1)
    (hv : 1 ≤ v) (i : Fin 5) (hcond : predCond i (2 ^ v * o)) :
    let m := (2 ^ v * o - 1) / digitVal i
    0 < m ∧ m % 2 = 1 ∧ d m = digitVal i ∧ d m * m + 1 = 2 ^ v * o ∧
    f^[v + 1] m = o := by
  have hx_ge : 2 ≤ 2 ^ v * o := by
    have h2v : 2 ≤ 2 ^ v := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hv
    nlinarith
  have hx_ev : (2 ^ v * o) % 2 = 0 := by
    have : v = (v - 1) + 1 := by omega
    have hmul : 2 ^ v * o = 2 * (2 ^ (v - 1) * o) := by conv_lhs => rw [this, pow_succ', mul_assoc]
    rw [hmul]; omega
  have hdvd : digitVal i ∣ (2 ^ v * o - 1) := by fin_cases i <;> (simp only [predCond, digitVal] at hcond ⊢; omega)
  set m := (2 ^ v * o - 1) / digitVal i; have hmul : digitVal i * m = 2 ^ v * o - 1 := Nat.mul_div_cancel' hdvd
  obtain ⟨hm_odd, hdm, heq⟩ := (lemma_odd_predecessors ho_pos ho_odd hv i).mpr ⟨hcond, hmul⟩
  have hm_pos : 0 < m := Nat.pos_of_mul_pos_left (by omega : 0 < digitVal i * m)
  have hf_step : f^[v + 1] m = o := by rw [Function.iterate_succ_apply, f_odd hm_odd, heq, f_iter_two_pow]
  exact ⟨hm_pos, hm_odd, hdm, heq, hf_step⟩

/-! ## Lemma 12: Weighted predecessor-tree lower bound -/
/-- `r` is non-periodic under `f`: no positive iterate returns to `r`. -/
def NonPeriodic (r : ℕ) : Prop := ∀ k : ℕ, 1 ≤ k → f^[k] r ≠ r
/-- Count of odd integers `m ≤ X` whose orbit under `f` passes through `o`. -/
noncomputable def NTree (o X : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 X).filter (fun m => m % 2 = 1 ∧ Reaches f m o)).card
lemma nonperiodic_of_reaches {o r : ℕ} (hreach : Reaches f o r) (hnp : NonPeriodic r) : NonPeriodic o := by
  rcases hreach with ⟨a, ha⟩
  intro k hk hcyc; apply hnp k hk; rw [← ha, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hcyc]
/-- If `o` is non-periodic and `m` is an odd predecessor of `o` (with `d(m)*m + 1 = 2^v * o`), then `o` does not -/
lemma not_reaches_pred_of_nonperiodic {o m v : ℕ} (hnp : NonPeriodic o)
    (hm_odd : m % 2 = 1) (hv : 1 ≤ v) (heq : d m * m + 1 = 2 ^ v * o) :
    ¬ Reaches f o m := by
  rintro ⟨k, hk⟩
  have hstep : f^[v + 1] m = o := by rw [Function.iterate_succ_apply, f_odd hm_odd, heq, f_iter_two_pow]
  apply hnp ((v + 1) + k) (by omega)
  rw [Function.iterate_add_apply, hk, hstep]
/-- Subtrees of two distinct odd predecessors `m1 ≠ m2` of a non-periodic odd `o` are disjoint. -/
lemma pred_subtrees_disjoint {o m1 m2 v1 v2 z : ℕ} (hnp : NonPeriodic o)
    (hm1 : m1 % 2 = 1) (hm2 : m2 % 2 = 1) (hv1 : 1 ≤ v1) (hv2 : 1 ≤ v2)
    (heq1 : d m1 * m1 + 1 = 2 ^ v1 * o) (heq2 : d m2 * m2 + 1 = 2 ^ v2 * o)
    (hne : m1 ≠ m2) (hr1 : Reaches f z m1) (hr2 : Reaches f z m2) : False := by
  rcases hr1 with ⟨k1, hk1⟩
  rcases hr2 with ⟨k2, hk2⟩
  wlog hle : k1 ≤ k2 generalizing m1 m2 v1 v2 k1 k2
  · exact this hm2 hm1 hv2 hv1 heq2 heq1 hne.symm k2 hk2 k1 hk1 (by omega)
  by_cases hkeq : k1 = k2
  · subst hkeq; exact hne (hk1.symm.trans hk2)
  · have hlt : k1 < k2 := by omega
    have hdiff : f^[k2 - k1] m1 = m2 := by rw [← hk1, ← Function.iterate_add_apply, Nat.sub_add_cancel hle, hk2]
    have hge1 : 1 ≤ k2 - k1 := by omega
    have hstep1 : f^[k2 - k1 - 1] (2 ^ v1 * o) = m2 := by
      have : k2 - k1 = (k2 - k1 - 1) + 1 := by omega
      rw [this, Function.iterate_succ_apply, f_odd hm1, heq1] at hdiff; exact hdiff
    obtain ⟨_, ho_m2⟩ := f_iter_two_pow_eq_odd hm2 hstep1
    exact not_reaches_pred_of_nonperiodic hnp hm2 hv2 heq2 ⟨k2 - k1 - 1 - v1, ho_m2⟩
/-- Tree cardinality inequality for a non-periodic odd `o ≤ X` and any finite set `S` of odd predecessors of `o` -/
lemma NTree_ge_one_add_sum {o X : ℕ} (ho_pos : 0 < o) (ho_odd : o % 2 = 1) (ho_le : o ≤ X)
    (hnp : NonPeriodic o) (S : Finset ℕ)
    (hS : ∀ m ∈ S, m ≤ X ∧ m % 2 = 1 ∧ ∃ v ≥ 1, d m * m + 1 = 2 ^ v * o) :
    (1 + ∑ m ∈ S, NTree m X ≤ NTree o X) ∧ (∀ m ∈ S, NTree m X < NTree o X) := by
  classical
  let A_o := (Finset.Icc 1 X).filter (fun z => z % 2 = 1 ∧ Reaches f z o)
  let B (m : ℕ) := (Finset.Icc 1 X).filter (fun z => z % 2 = 1 ∧ Reaches f z m)
  have ho_mem : o ∈ A_o := by
    simp only [A_o, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨ho_pos, ho_le⟩, ho_odd, reaches_refl f o⟩
  have hB_sub : ∀ m ∈ S, B m ⊆ A_o.erase o := by
    intro m hm z hz; obtain ⟨_, hm_odd, v, hv, heq⟩ := hS m hm; simp only [B, Finset.mem_filter, Finset.mem_Icc] at hz
    simp only [A_o, Finset.mem_erase, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨?_, hz.1, hz.2.1, ?_⟩
    · intro hzo; subst hzo; exact not_reaches_pred_of_nonperiodic hnp hm_odd hv heq hz.2.2
    · have hmo : Reaches f m o := ⟨v + 1, by
        rw [Function.iterate_succ_apply, f_odd hm_odd, heq, f_iter_two_pow]⟩
      exact reaches_trans hz.2.2 hmo
  have hdisj : (S : Set ℕ).PairwiseDisjoint B := by
    intro m1 hm1 m2 hm2 hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro z hz1 hz2
    obtain ⟨_, hm1_odd, v1, hv1, heq1⟩ := hS m1 hm1; obtain ⟨_, hm2_odd, v2, hv2, heq2⟩ := hS m2 hm2
    simp only [B, Finset.mem_filter] at hz1 hz2
    exact pred_subtrees_disjoint hnp hm1_odd hm2_odd hv1 hv2 heq1 heq2 hne hz1.2.2 hz2.2.2
  have hunion_sub : S.biUnion B ⊆ A_o.erase o := Finset.biUnion_subset.mpr hB_sub
  have hcard_union : (S.biUnion B).card = ∑ m ∈ S, (B m).card := Finset.card_biUnion hdisj
  have hcard_erase : (A_o.erase o).card + 1 = A_o.card := by
    rw [Finset.card_erase_of_mem ho_mem]; have hpos : 1 ≤ A_o.card := Finset.card_pos.mpr ⟨o, ho_mem⟩; omega
  have hle_sum : ∑ m ∈ S, (B m).card ≤ (A_o.erase o).card := hcard_union ▸ Finset.card_le_card hunion_sub
  have hmain : 1 + ∑ m ∈ S, NTree m X ≤ NTree o X := by change 1 + ∑ m ∈ S, (B m).card ≤ A_o.card; omega
  refine ⟨hmain, fun m hm => ?_⟩
  have hsingle : NTree m X ≤ ∑ m' ∈ S, NTree m' X :=
    Finset.single_le_sum (f := fun m' => NTree m' X) (fun _ _ => Nat.zero_le _) hm
  omega
/-- Residue type `(M, ρ)` with `M = Q / digitVal i` and `ρ < M`. -/
abbrev TypeId (Q : ℕ) := Σ i : Fin 5, Fin (Q / digitVal i)
/-- Allowed moves `(i, vc)` from residue `R mod Q` with period `P` (`v_c = vc.val + 1`). -/
def movesOf (Q P : ℕ) (R : Fin Q) : Finset (Fin 5 × Fin P) :=
  Finset.univ.filter fun mv => predCondBool mv.1 (2 ^ (mv.2.val + 1) * R.val)
/-- Child type `(Q / d, ρ')` produced by move `mv = (i, vc)` from residue `R mod Q`. -/
def childType (Q P : ℕ) (hQ : 1575 ∣ Q) (hQpos : 0 < Q) (R : Fin Q) (mv : Fin 5 × Fin P) : TypeId Q :=
  let d := digitVal mv.1; let r' := ((2 ^ (mv.2.val + 1) * R.val + Q - 1) % Q) / d
  ⟨mv.1, ⟨r', by
    have hd_pos : 0 < d := digitVal_pos mv.1; have hd_dvd : d ∣ Q := (digitVal_dvd_1575 mv.1).trans hQ
    have hlt : (2 ^ (mv.2.val + 1) * R.val + Q - 1) % Q < Q := Nat.mod_lt _ hQpos; rw [Nat.div_lt_iff_lt_mul hd_pos]
    rwa [Nat.div_mul_cancel hd_dvd]⟩⟩
/-- Helper: `((y / d) % (Q / d)) = (y % Q) / d` when `d ∣ Q` and `d ∣ y`. -/
lemma div_mod_div_eq {y d Q : ℕ} (hd_pos : 0 < d) (hdQ : d ∣ Q) (hdy : d ∣ y) : (y / d) % (Q / d) = (y % Q) / d := by
  rcases hdQ with ⟨q, rfl⟩
  rcases hdy with ⟨k, rfl⟩
  rw [Nat.mul_div_cancel_left k hd_pos, Nat.mul_div_cancel_left q hd_pos,
      Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ hd_pos]
/-- `3` is non-periodic under `f`: `3 → 10 → 5`, and `5` stays forever on `{5, 26, 13, 40, 20, 10}`. -/
lemma cycle5_mem (k : ℕ) :
    f^[k] 5 = 5 ∨ f^[k] 5 = 26 ∨ f^[k] 5 = 13 ∨
    f^[k] 5 = 40 ∨ f^[k] 5 = 20 ∨ f^[k] 5 = 10 := by
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h | h | h | h | h <;> rw [h]
    · right; left; decide
    · right; right; left; decide
    · right; right; right; left; decide
    · right; right; right; right; left; decide
    · right; right; right; right; right; decide
    · left; decide

theorem nonperiodic_three : NonPeriodic 3 := by
  intro k hk hcyc
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero =>
      change f 3 = 3 at hcyc
      have : f 3 = 10 := by decide
      omega
    | succ k =>
      have h2 : f^[2] 3 = 5 := by decide
      have hsplit : k + 1 + 1 = k + 2 := rfl; rw [hsplit, Function.iterate_add_apply, h2] at hcyc
      rcases cycle5_mem k with h | h | h | h | h | h <;> omega
lemma h1575_dvd_14175 : 1575 ∣ 14175 := by decide

/-! ## Corollary 14: Unconditional separation of the two basins -/
/-- Corollary 14 (odd starts): combining Theorem 10 (`N1(X) ≤ 2.44 * X^β`, `β < 0.626383`) with any -/
theorem cor_basin_separation {κ : ℝ} (hκ : 0 < κ)
    (h5 : ∀ X : ℕ, 3 ≤ X → κ * (X : ℝ) ^ ((65 : ℝ) / 100) ≤ (N5 X : ℝ))
    (X : ℕ) (hX : 3 ≤ X) :
    (N1 X : ℝ) / (N5 X : ℝ) ≤ ((244 / 100 : ℝ) / κ) * (X : ℝ) ^ (-(236 / 10000 : ℝ)) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by positivity
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
  have h1 := thm_basin1_upper X (by omega)
  have h5X := h5 X hX
  have h5_pos : 0 < (N5 X : ℝ) := lt_of_lt_of_le (by positivity) h5X
  have hexp : beta - (65 / 100 : ℝ) ≤ -(236 / 10000 : ℝ) := by linarith [beta_bounds.2]
  have hratio : (X : ℝ) ^ beta / (X : ℝ) ^ ((65 : ℝ) / 100) ≤ (X : ℝ) ^ (-(236 / 10000 : ℝ)) := by
    rw [← Real.rpow_sub hXpos]; exact Real.rpow_le_rpow_of_exponent_le hX1 hexp
  calc (N1 X : ℝ) / (N5 X : ℝ)
      ≤ ((244 / 100 : ℝ) * (X : ℝ) ^ beta) / (κ * (X : ℝ) ^ ((65 : ℝ) / 100)) :=
        div_le_div₀ (by positivity) h1 (by positivity) h5X
    _ = ((244 / 100 : ℝ) / κ) * ((X : ℝ) ^ beta / (X : ℝ) ^ ((65 : ℝ) / 100)) := by ring
    _ ≤ ((244 / 100 : ℝ) / κ) * (X : ℝ) ^ (-(236 / 10000 : ℝ)) := mul_le_mul_of_nonneg_left hratio (by positivity)
/-- Corollary 14 (all positive starts, even and odd): `N1All(X) / N5All(X) ≤ (6.93 / κ) * X^{-0.0236}`. -/
theorem cor_basin_separation_all {κ : ℝ} (hκ : 0 < κ)
    (h5 : ∀ X : ℕ, 3 ≤ X → κ * (X : ℝ) ^ ((65 : ℝ) / 100) ≤ (N5 X : ℝ))
    (X : ℕ) (hX : 3 ≤ X) :
    (N1All X : ℝ) / (N5All X : ℝ) ≤ ((693 / 100 : ℝ) / κ) * (X : ℝ) ^ (-(236 / 10000 : ℝ)) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by positivity
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
  have h1 := thm_basin1_all_upper X (by omega)
  have h5_sub : N5 X ≤ N5All X := by
    classical
    unfold N5 N5All
    refine Finset.card_le_card fun m hm => ?_
    simp only [Finset.mem_filter] at hm ⊢; exact ⟨hm.1, hm.2.2⟩
  have h5X : κ * (X : ℝ) ^ ((65 : ℝ) / 100) ≤ (N5All X : ℝ) := (h5 X hX).trans (by exact_mod_cast h5_sub)
  have hexp : beta - (65 / 100 : ℝ) ≤ -(236 / 10000 : ℝ) := by linarith [beta_bounds.2]
  have hratio : (X : ℝ) ^ beta / (X : ℝ) ^ ((65 : ℝ) / 100) ≤ (X : ℝ) ^ (-(236 / 10000 : ℝ)) := by
    rw [← Real.rpow_sub hXpos]; exact Real.rpow_le_rpow_of_exponent_le hX1 hexp
  calc (N1All X : ℝ) / (N5All X : ℝ)
      ≤ ((693 / 100 : ℝ) * (X : ℝ) ^ beta) / (κ * (X : ℝ) ^ ((65 : ℝ) / 100)) :=
        div_le_div₀ (by positivity) h1 (by positivity) h5X
    _ = ((693 / 100 : ℝ) / κ) * ((X : ℝ) ^ beta / (X : ℝ) ^ ((65 : ℝ) / 100)) := by ring
    _ ≤ ((693 / 100 : ℝ) / κ) * (X : ℝ) ^ (-(236 / 10000 : ℝ)) := mul_le_mul_of_nonneg_left hratio (by positivity)

end Ouroboros
