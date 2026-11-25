module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import Ouroboros.Defs
public import Ouroboros.BasinOne
public import Ouroboros.BasinFive
public import Ouroboros.BasinFiveCert
public import Ouroboros.BasinFiveUncond

@[expose] public section

/-!
# Individual Child-Weight Charging (`lem:weighted`) and Sharp Basin-of-5 Bound (`thm:basin-sharp` Part 2)

Formalizes:
- **Lemma 20 (`lem:weighted`)**: `lem_weighted` and `lem_weighted_tree3` — under the expansion
  inequality `∑_{(d,v) ∈ M(R)} (d / 2^v)^s * w_{t'} ≥ w_t` and per-residue row-sum budget
  `∑_{(d,v) ∈ M(R)} w_{t'} ≤ L` (`L > 0`), every odd vertex `o` in the inverse tree of `3`
  (more generally any non-periodic odd `o`) and every integer `X ≥ o` satisfies
  `L * H(o, X) ≥ (X / o)^s * w_t`, where `H(o, X) = NTree o X`.
- **Pure-kernel row-sum cap (`L = 2,269,527`)**: `checkRowCap_all` and `certW_row_sum_le`
  discharge all `14,175` raw child-weight row sums for the `Q = 14,175`, `Vmax = 16`
  `QuadTree` certificate via pure-kernel `rfl` across 14 binary-split shards.
- **Theorem `thm:basin-sharp` (Part 2, pure-kernel Lean 4)**:
  `thm_basin5_sharp` (`N5(X) ≥ (98959 / (2269527 * 3^(13/20))) * X^(13/20)` for all `X ≥ 3`)
  and `thm_basin5_sharp_gt` (`N5(X) > 0.02134 * X^(13/20)` for all `X ≥ 3`).
-/

namespace Ouroboros

open BasinFiveCert

lemma div_two_pow_rpow_eq (d : ℝ) (hd : 0 ≤ d) (v : ℕ) (s : ℝ) :
    (d / (2 : ℝ) ^ v) ^ s = d ^ s * (2 : ℝ) ^ (-(s * (v : ℝ))) := by
  rw [Real.div_rpow hd (by positivity), div_eq_mul_inv,
      ← Real.rpow_natCast (2 : ℝ) v, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_neg (by norm_num)]
  congr 2; ring

/-- **Lemma 20 (`lem:weighted`, general non-periodic odd root)**:
    If the expansion inequality `(eq:b5-expand)` and per-residue row-sum budget `(eq:b5-budget)`
    hold with `L > 0` for a nonnegative weight vector `w`, then for every non-periodic odd `o`,
    every integer `X ≥ o`, and every compatible type `t` of `o`,
    `((X : ℝ) / (o : ℝ)) ^ s * w t ≤ L * (NTree o X : ℝ)`. -/
theorem lem_weighted
    {Q Vmax : ℕ} (hQ1575 : 1575 ∣ Q) (hQpos : 0 < Q)
    {s L : ℝ} (hs : 0 < s) (hL : 0 < L)
    (w : TypeId Q → ℝ) (hw_nn : ∀ t, 0 ≤ w t)
    (hexpand : ∀ (t : TypeId Q) (R : Fin Q),
      R.val % (Q / digitVal t.1) = t.2.val →
      w t ≤ ∑ mv ∈ movesOf Q Vmax R,
        ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) ^ s *
          w (childType Q Vmax hQ1575 hQpos R mv))
    (hbudget : ∀ R : Fin Q,
      ∑ mv ∈ movesOf Q Vmax R, w (childType Q Vmax hQ1575 hQpos R mv) ≤ L) :
    ∀ (o X : ℕ), 0 < o → o % 2 = 1 → o ≤ X → NonPeriodic o →
      ∀ (t : TypeId Q), o % (Q / digitVal t.1) = t.2.val →
        ((X : ℝ) / (o : ℝ)) ^ s * w t ≤ L * (NTree o X : ℝ) := by
  suffices hstrong : ∀ N : ℕ, ∀ (o X : ℕ), NTree o X = N →
      0 < o → o % 2 = 1 → o ≤ X → NonPeriodic o →
      ∀ (t : TypeId Q), o % (Q / digitVal t.1) = t.2.val →
        ((X : ℝ) / (o : ℝ)) ^ s * w t ≤ L * (NTree o X : ℝ) by
    intro o X ho_pos ho_odd ho_le hnp t ht
    exact hstrong (NTree o X) o X rfl ho_pos ho_odd ho_le hnp t ht
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro o X hN_eq ho_pos ho_odd ho_le hnp t ht
    let R : Fin Q := ⟨o % Q, Nat.mod_lt o hQpos⟩
    have hR_comp : R.val % (Q / digitVal t.1) = t.2.val := by
      have hdvd : Q / digitVal t.1 ∣ Q :=
        Nat.div_dvd_of_dvd ((digitVal_dvd_1575 t.1).trans hQ1575)
      rw [Nat.mod_mod_of_dvd o hdvd]
      exact ht
    let predOf (mv : Fin 5 × Fin Vmax) : ℕ :=
      (2 ^ (mv.2.val + 1) * o - 1) / digitVal mv.1
    have hpred_props : ∀ mv ∈ movesOf Q Vmax R,
        let m := predOf mv
        0 < m ∧ m % 2 = 1 ∧ d m = digitVal mv.1 ∧
        d m * m + 1 = 2 ^ (mv.2.val + 1) * o ∧
        f^[mv.2.val + 2] m = o ∧
        m % (Q / digitVal mv.1) = (childType Q Vmax hQ1575 hQpos R mv).2.val := by
      intro mv hmv
      have hcondR : predCond mv.1 (2 ^ (mv.2.val + 1) * R.val) := by
        simp only [movesOf, Finset.mem_filter, Finset.mem_univ, true_and] at hmv
        exact (predCondBool_iff _ _).mp hmv
      have hmodQ : (2 ^ (mv.2.val + 1) * o) % Q = (2 ^ (mv.2.val + 1) * R.val) % Q := by
        simp [R, Nat.mul_mod]
      have hmod1575 : (2 ^ (mv.2.val + 1) * o) % 1575 =
          (2 ^ (mv.2.val + 1) * R.val) % 1575 := by
        rw [← Nat.mod_mod_of_dvd (2 ^ (mv.2.val + 1) * o) hQ1575,
            ← Nat.mod_mod_of_dvd (2 ^ (mv.2.val + 1) * R.val) hQ1575, hmodQ]
      have hcond : predCond mv.1 (2 ^ (mv.2.val + 1) * o) :=
        (predCond_mod_1575 mv.1 hmod1575).mpr hcondR
      obtain ⟨hm_pos, hm_odd, hdm, heq, hstep⟩ :=
        lemma_odd_predecessors_unique ho_pos ho_odd (by omega) mv.1 hcond
      refine ⟨hm_pos, hm_odd, hdm, heq, hstep, ?_⟩
      have hd_pos : 0 < digitVal mv.1 := digitVal_pos mv.1
      have hdQ : digitVal mv.1 ∣ Q := (digitVal_dvd_1575 mv.1).trans hQ1575
      have hx_pos : 1 ≤ 2 ^ (mv.2.val + 1) * o := by
        have : 1 ≤ 2 ^ (mv.2.val + 1) := Nat.one_le_pow _ _ (by norm_num)
        nlinarith
      have hdy : digitVal mv.1 ∣ (2 ^ (mv.2.val + 1) * o - 1) := by
        have h1 : digitVal mv.1 * predOf mv + 1 = 2 ^ (mv.2.val + 1) * o := by
          rw [← hdm]; exact heq
        exact ⟨predOf mv, by omega⟩
      rw [show predOf mv % (Q / digitVal mv.1) =
            ((2 ^ (mv.2.val + 1) * o - 1) % Q) / digitVal mv.1 from
          div_mod_div_eq hd_pos hdQ hdy]
      have hsub_mod : (2 ^ (mv.2.val + 1) * o - 1) % Q =
          (2 ^ (mv.2.val + 1) * R.val + Q - 1) % Q := by
        have h1 : (2 ^ (mv.2.val + 1) * o - 1 + Q) % Q =
            (2 ^ (mv.2.val + 1) * o - 1) % Q := Nat.add_mod_right _ _
        rw [← h1]
        have h2 : 2 ^ (mv.2.val + 1) * o - 1 + Q =
            2 ^ (mv.2.val + 1) * o + (Q - 1) := by omega
        have h3 : 2 ^ (mv.2.val + 1) * R.val + Q - 1 =
            2 ^ (mv.2.val + 1) * R.val + (Q - 1) := by omega
        rw [h2, h3, Nat.add_mod, hmodQ, ← Nat.add_mod]
      rw [hsub_mod]
      rfl
    classical
    let active : Finset (Fin 5 × Fin Vmax) :=
      (movesOf Q Vmax R).filter fun mv => 2 ^ (mv.2.val + 1) * o ≤ digitVal mv.1 * X
    have hpred_inj : Set.InjOn predOf (active : Set _) := by
      intro mv1 h1 mv2 h2 hEq
      simp only [Finset.mem_coe, active, Finset.mem_filter] at h1 h2
      obtain ⟨_, _, hd1, heq1, _, _⟩ := hpred_props mv1 h1.1
      obtain ⟨_, _, hd2, heq2, _, _⟩ := hpred_props mv2 h2.1
      have hi : mv1.1 = mv2.1 := digitVal_inj (by rw [← hd1, ← hd2, hEq])
      have hpow : 2 ^ (mv1.2.val + 1) * o = 2 ^ (mv2.2.val + 1) * o := by
        rw [← heq1, ← heq2, hEq]
      have hexp := (two_pow_mul_odd_inj ho_odd ho_odd hpow).1
      exact Prod.ext hi (Fin.ext (by omega))
    let S : Finset ℕ := active.image predOf
    have hS_valid : ∀ m ∈ S, m ≤ X ∧ m % 2 = 1 ∧ ∃ v ≥ 1, d m * m + 1 = 2 ^ v * o := by
      intro m hm
      simp only [S, Finset.mem_image] at hm
      obtain ⟨mv, hmv, rfl⟩ := hm
      simp only [active, Finset.mem_filter] at hmv
      obtain ⟨_, hm_odd, hdm, heq, _, _⟩ := hpred_props mv hmv.1
      have hleX : predOf mv ≤ X := by
        have hdm_pos : 0 < digitVal mv.1 := digitVal_pos mv.1
        have h1 : digitVal mv.1 * predOf mv ≤ digitVal mv.1 * X := by
          conv_lhs => rw [← hdm]
          omega
        exact Nat.le_of_mul_le_mul_left h1 hdm_pos
      exact ⟨hleX, hm_odd, mv.2.val + 1, by omega, heq⟩
    obtain ⟨hN_sum, hN_lt⟩ := NTree_ge_one_add_sum ho_pos ho_odd ho_le hnp S hS_valid
    let contrib (mv : Fin 5 × Fin Vmax) : ℝ :=
      if 2 ^ (mv.2.val + 1) * o ≤ digitVal mv.1 * X then L * (NTree (predOf mv) X : ℝ) else 0
    have hsum_eq : L * ∑ m ∈ S, (NTree m X : ℝ) = ∑ mv ∈ movesOf Q Vmax R, contrib mv := by
      rw [Finset.mul_sum]
      unfold S
      rw [Finset.sum_image (fun a ha b hb h => hpred_inj ha hb h)]
      unfold active contrib
      rw [Finset.sum_filter]
    -- Key per-child charging inequality: each discarded child loses at most its OWN weight `w(t')`.
    have hmove_ge : ∀ mv ∈ movesOf Q Vmax R,
        ((X : ℝ) / (o : ℝ)) ^ s * (((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) ^ s *
          w (childType Q Vmax hQ1575 hQpos R mv)) -
        w (childType Q Vmax hQ1575 hQpos R mv) ≤ contrib mv := by
      intro mv hmv
      have hw_nn_c := hw_nn (childType Q Vmax hQ1575 hQpos R mv)
      have ho_posR : (0 : ℝ) < (o : ℝ) := by exact_mod_cast ho_pos
      have hd_posR : (0 : ℝ) < (digitVal mv.1 : ℝ) := by exact_mod_cast digitVal_pos mv.1
      have h2_posR : (0 : ℝ) < (2 : ℝ) ^ (mv.2.val + 1) := by positivity
      unfold contrib
      split_ifs with hle
      · have hmv_act : mv ∈ active := Finset.mem_filter.mpr ⟨hmv, hle⟩
        have hm_in_S : predOf mv ∈ S := Finset.mem_image.mpr ⟨mv, hmv_act, rfl⟩
        have hlt_N : NTree (predOf mv) X < N := by rw [← hN_eq]; exact hN_lt _ hm_in_S
        obtain ⟨hm_pos, hm_odd, hdm, heq, hstep, htype⟩ := hpred_props mv hmv
        have hm_le : predOf mv ≤ X := (hS_valid _ hm_in_S).1
        have hm_np : NonPeriodic (predOf mv) :=
          nonperiodic_of_reaches ⟨mv.2.val + 2, hstep⟩ hnp
        have hih := ih (NTree (predOf mv) X) hlt_N (predOf mv) X rfl
          hm_pos hm_odd hm_le hm_np (childType Q Vmax hQ1575 hQpos R mv) htype
        have hm_posR : (0 : ℝ) < (predOf mv : ℝ) := by exact_mod_cast hm_pos
        have hratio : ((X : ℝ) / (o : ℝ)) * ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) ≤
            (X : ℝ) / (predOf mv : ℝ) := by
          have hnat : predOf mv * digitVal mv.1 < 2 ^ (mv.2.val + 1) * o := by
            rw [mul_comm, ← hdm]; omega
          have hR : (predOf mv : ℝ) * (digitVal mv.1 : ℝ) ≤
              (2 : ℝ) ^ (mv.2.val + 1) * (o : ℝ) := by exact_mod_cast hnat.le
          rw [le_div_iff₀ hm_posR]
          have heq_f : ((X : ℝ) / (o : ℝ)) * ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) *
              (predOf mv : ℝ) =
              (X : ℝ) * ((predOf mv : ℝ) * (digitVal mv.1 : ℝ)) /
                ((2 : ℝ) ^ (mv.2.val + 1) * (o : ℝ)) := by ring
          rw [heq_f, div_le_iff₀ (mul_pos h2_posR ho_posR)]
          nlinarith [show (0 : ℝ) ≤ (X : ℝ) by positivity]
        have hpow_ge : ((X : ℝ) / (o : ℝ)) ^ s *
            ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) ^ s ≤
            ((X : ℝ) / (predOf mv : ℝ)) ^ s := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          exact Real.rpow_le_rpow (by positivity) hratio hs.le
        have hmain : ((X : ℝ) / (o : ℝ)) ^ s *
            (((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) ^ s *
              w (childType Q Vmax hQ1575 hQpos R mv)) ≤ L * (NTree (predOf mv) X : ℝ) := by
          calc ((X : ℝ) / (o : ℝ)) ^ s *
                (((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) ^ s *
                  w (childType Q Vmax hQ1575 hQpos R mv))
              = (((X : ℝ) / (o : ℝ)) ^ s *
                  ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) ^ s) *
                  w (childType Q Vmax hQ1575 hQpos R mv) := by ring
            _ ≤ ((X : ℝ) / (predOf mv : ℝ)) ^ s *
                  w (childType Q Vmax hQ1575 hQpos R mv) :=
                  mul_le_mul_of_nonneg_right hpow_ge hw_nn_c
            _ ≤ L * (NTree (predOf mv) X : ℝ) := hih
        linarith
      · have hgt_nat : digitVal mv.1 * X < 2 ^ (mv.2.val + 1) * o := by omega
        have hgt_R : (digitVal mv.1 : ℝ) * (X : ℝ) < (2 : ℝ) ^ (mv.2.val + 1) * (o : ℝ) := by
          exact_mod_cast hgt_nat
        have hfrac_le1 : ((X : ℝ) / (o : ℝ)) * ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) ≤
            1 := by
          have : ((X : ℝ) / (o : ℝ)) * ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) =
              ((digitVal mv.1 : ℝ) * (X : ℝ)) / ((2 : ℝ) ^ (mv.2.val + 1) * (o : ℝ)) := by ring
          rw [this, div_le_one (mul_pos h2_posR ho_posR)]
          exact hgt_R.le
        have hpow_le1 : ((X : ℝ) / (o : ℝ)) ^ s *
            ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) ^ s ≤ 1 := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          calc (((X : ℝ) / (o : ℝ)) * ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1))) ^ s
              ≤ (1 : ℝ) ^ s := Real.rpow_le_rpow (by positivity) hfrac_le1 hs.le
            _ = 1 := Real.one_rpow s
        have hprod_le : ((X : ℝ) / (o : ℝ)) ^ s *
            (((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) ^ s *
              w (childType Q Vmax hQ1575 hQpos R mv)) ≤
            w (childType Q Vmax hQ1575 hQpos R mv) := by
          calc ((X : ℝ) / (o : ℝ)) ^ s *
                (((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) ^ s *
                  w (childType Q Vmax hQ1575 hQpos R mv))
              = (((X : ℝ) / (o : ℝ)) ^ s *
                  ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) ^ s) *
                  w (childType Q Vmax hQ1575 hQpos R mv) := by ring
            _ ≤ 1 * w (childType Q Vmax hQ1575 hQpos R mv) :=
                  mul_le_mul_of_nonneg_right hpow_le1 hw_nn_c
            _ = w (childType Q Vmax hQ1575 hQpos R mv) := one_mul _
        linarith
    have htotal : ((X : ℝ) / (o : ℝ)) ^ s *
        (∑ mv ∈ movesOf Q Vmax R,
          ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) ^ s *
            w (childType Q Vmax hQ1575 hQpos R mv)) -
        (∑ mv ∈ movesOf Q Vmax R, w (childType Q Vmax hQ1575 hQpos R mv)) ≤
        ∑ mv ∈ movesOf Q Vmax R, contrib mv := by
      have h1 := Finset.sum_le_sum fun mv hmv => hmove_ge mv hmv
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h1
      exact h1
    have hL_budget := hbudget R
    have hN_cast : (1 : ℝ) + ∑ m ∈ S, (NTree m X : ℝ) ≤ (NTree o X : ℝ) := by
      exact_mod_cast hN_sum
    have hL_cast : L + L * ∑ m ∈ S, (NTree m X : ℝ) ≤ L * (NTree o X : ℝ) := by
      nlinarith
    have hT_ge := hexpand t R hR_comp
    have hmul_T : ((X : ℝ) / (o : ℝ)) ^ s * w t ≤
        ((X : ℝ) / (o : ℝ)) ^ s *
          (∑ mv ∈ movesOf Q Vmax R,
            ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) ^ s *
              w (childType Q Vmax hQ1575 hQpos R mv)) :=
      mul_le_mul_of_nonneg_left hT_ge (by positivity)
    linarith

/-- **Lemma 20 (`lem:weighted`, literal statement on the inverse tree of `3`)**:
    For any odd vertex `o` whose forward orbit visits `3`, any integer `X ≥ o`, and any
    compatible type `t` of `o`, `((X : ℝ) / (o : ℝ)) ^ s * w t ≤ L * (NTree o X : ℝ)`. -/
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
    ((X : ℝ) / (o : ℝ)) ^ s * w t ≤ L * (NTree o X : ℝ) :=
  lem_weighted hQ1575 hQpos hs hL w hw_nn hexpand hbudget
    o X ho_pos ho_odd ho_le (nonperiodic_of_reaches ho_tree nonperiodic_three) t ht

/-! ## Pure-kernel row-sum cap `L = 2,269,527` and unconditional `thm:basin-sharp` (Part 2) -/

/-- One halving-level unscaled child-weight contribution at `x1 = (2^v * R) % 14175`. -/
def stepRawWeight (x1 : Nat) : Nat :=
  let r5 := x1 % 5
  match Nat.beq r5 0 with
  | true =>
    let xm1 := match Nat.beq x1 0 with | true => 14174 | false => x1 - 1
    let s3 := match Nat.beq (x1 % 3) 1 with
      | true => getW (14175 + xm1 / 3)
      | false => 0
    let s7 := match Nat.beq (x1 % 7) 1 with
      | true => getW (21735 + xm1 / 7)
      | false => 0
    s3 + s7
  | false =>
    match Nat.beq r5 1 with
    | true =>
      match Nat.beq (x1 % 25) 1 with
      | true => getW (18900 + (x1 - 1) / 5)
      | false => 0
    | false =>
      match Nat.beq r5 2 with
      | true =>
        let xm1 := x1 - 1
        let s1 := getW xm1
        let s9 := match Nat.beq (x1 % 9) 1 with
          | true => getW (23760 + xm1 / 9)
          | false => 0
        s1 + s9
      | false => 0

/-- Accumulate `stepRawWeight ((2^(vi+1) * R) % 14175)` for `rem` steps. -/
def sumRawAux : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | rem + 1, x, acc =>
    let x1 := (2 * x) % 14175
    sumRawAux rem x1 (acc + stepRawWeight x1)

/-- Check the exact raw row-sum budget `sumRawAux 16 R 0 ≤ 2269527` at residue `R`. -/
def checkRowCap (R : Nat) : Bool :=
  Nat.ble (sumRawAux 16 R 0) 2269527

/-- Binary-splitting pure-kernel range checker for `checkRowCap` over `[lo, lo + 2^d) ∩ [0, 14175)`. -/
def checkRowCapPow2 (lo : Nat) : Nat → Bool
  | 0 => match Nat.ble 14175 lo with | true => true | false => checkRowCap lo
  | d + 1 => checkRowCapPow2 lo d && checkRowCapPow2 (lo + 2 ^ d) d

private theorem checkRowCapPow2_sound (lo d : Nat) (h : checkRowCapPow2 lo d = true) :
    ∀ R, lo ≤ R → R < lo + 2 ^ d → R < 14175 → checkRowCap R = true := by
  induction d generalizing lo with
  | zero =>
    intro R hlo hhi hlt
    have hReq : R = lo := by omega
    subst hReq
    simp only [checkRowCapPow2] at h
    have hble : Nat.ble 14175 R = false := by
      cases hb : Nat.ble 14175 R with
      | false => rfl
      | true => exact absurd (Nat.ble_eq.mp hb) (by omega)
    rw [hble] at h
    exact h
  | succ d ih =>
    simp only [checkRowCapPow2, Bool.and_eq_true] at h
    intro R hlo hhi hlt
    by_cases hmid : R < lo + 2 ^ d
    · exact ih lo h.1 R hlo hmid hlt
    · have h2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ, Nat.mul_two]
      exact ih (lo + 2 ^ d) h.2 R (by omega) (by omega) hlt

private theorem rawShard_00 : checkRowCapPow2 0 10 = true := rfl
private theorem rawShard_01 : checkRowCapPow2 1024 10 = true := rfl
private theorem rawShard_02 : checkRowCapPow2 2048 10 = true := rfl
private theorem rawShard_03 : checkRowCapPow2 3072 10 = true := rfl
private theorem rawShard_04 : checkRowCapPow2 4096 10 = true := rfl
private theorem rawShard_05 : checkRowCapPow2 5120 10 = true := rfl
private theorem rawShard_06 : checkRowCapPow2 6144 10 = true := rfl
private theorem rawShard_07 : checkRowCapPow2 7168 10 = true := rfl
private theorem rawShard_08 : checkRowCapPow2 8192 10 = true := rfl
private theorem rawShard_09 : checkRowCapPow2 9216 10 = true := rfl
private theorem rawShard_10 : checkRowCapPow2 10240 10 = true := rfl
private theorem rawShard_11 : checkRowCapPow2 11264 10 = true := rfl
private theorem rawShard_12 : checkRowCapPow2 12288 10 = true := rfl
private theorem rawShard_13 : checkRowCapPow2 13312 10 = true := rfl

/-- Pure-kernel proof that every residue `R < 14175` has unscaled child-weight row sum
    at most `L = 2,269,527`. -/
theorem checkRowCap_all (R : Nat) (hR : R < 14175) : sumRawAux 16 R 0 ≤ 2269527 := by
  have h : checkRowCap R = true := by
    by_cases h0 : R < 1024
    · exact checkRowCapPow2_sound 0 10 rawShard_00 R (by omega) (by omega) hR
    by_cases h1 : R < 2048
    · exact checkRowCapPow2_sound 1024 10 rawShard_01 R (by omega) (by omega) hR
    by_cases h2 : R < 3072
    · exact checkRowCapPow2_sound 2048 10 rawShard_02 R (by omega) (by omega) hR
    by_cases h3 : R < 4096
    · exact checkRowCapPow2_sound 3072 10 rawShard_03 R (by omega) (by omega) hR
    by_cases h4 : R < 5120
    · exact checkRowCapPow2_sound 4096 10 rawShard_04 R (by omega) (by omega) hR
    by_cases h5 : R < 6144
    · exact checkRowCapPow2_sound 5120 10 rawShard_05 R (by omega) (by omega) hR
    by_cases h6 : R < 7168
    · exact checkRowCapPow2_sound 6144 10 rawShard_06 R (by omega) (by omega) hR
    by_cases h7 : R < 8192
    · exact checkRowCapPow2_sound 7168 10 rawShard_07 R (by omega) (by omega) hR
    by_cases h8 : R < 9216
    · exact checkRowCapPow2_sound 8192 10 rawShard_08 R (by omega) (by omega) hR
    by_cases h9 : R < 10240
    · exact checkRowCapPow2_sound 9216 10 rawShard_09 R (by omega) (by omega) hR
    by_cases h10 : R < 11264
    · exact checkRowCapPow2_sound 10240 10 rawShard_10 R (by omega) (by omega) hR
    by_cases h11 : R < 12288
    · exact checkRowCapPow2_sound 11264 10 rawShard_11 R (by omega) (by omega) hR
    by_cases h12 : R < 13312
    · exact checkRowCapPow2_sound 12288 10 rawShard_12 R (by omega) (by omega) hR
    · exact checkRowCapPow2_sound 13312 10 rawShard_13 R (by omega) (by omega) hR
  exact Nat.ble_eq.mp h

private lemma predCondBool_mod_14175' (i : Fin 5) (x : ℕ) :
    predCondBool i (x % 14175) = predCondBool i x := by
  have h1 : (x % 14175) % 1575 = x % 1575 := Nat.mod_mod_of_dvd x h1575_dvd_14175
  have hiff := predCond_mod_1575 i h1
  cases hb1 : predCondBool i (x % 14175) <;> cases hb2 : predCondBool i x
  · rfl
  · exfalso
    have h2 := (predCondBool_iff i x).mp hb2
    have h3 := (predCondBool_iff i (x % 14175)).mpr (hiff.mpr h2)
    rw [hb1] at h3; exact Bool.false_ne_true h3
  · exfalso
    have h2 := (predCondBool_iff i (x % 14175)).mp hb1
    have h3 := (predCondBool_iff i x).mpr (hiff.mp h2)
    rw [hb2] at h3; exact Bool.false_ne_true h3
  · rfl

private lemma beq_false_of_ne' {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

private lemma stepRawWeight_eq_sum (R : Fin 14175) (vi : Fin 16) :
    stepRawWeight ((2 ^ (vi.val + 1) * R.val) % 14175) =
      ∑ i : Fin 5,
        if predCondBool i (2 ^ (vi.val + 1) * R.val) then
          getW (typeOff i.val + (childType 14175 16 h1575_dvd_14175 (by omega) R (i, vi)).2.val)
        else 0 := by
  set x := 2 ^ (vi.val + 1) * R.val
  set x1 := x % 14175
  have hx1_lt : x1 < 14175 := Nat.mod_lt x (by omega)
  have hxm1_eq : (x + 14175 - 1) % 14175 = if x1 = 0 then 14174 else x1 - 1 := by
    have h1 : (x + 14175 - 1) % 14175 = (x1 + 14174) % 14175 := by
      have : x + 14175 - 1 = x + 14174 := by omega
      rw [this, Nat.add_mod, Nat.mod_eq_of_lt (by omega : 14174 < 14175)]
    rw [h1]
    split_ifs with h0
    · rw [h0]
    · have : x1 + 14174 = (x1 - 1) + 14175 := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hchild : ∀ i : Fin 5,
      (childType 14175 16 h1575_dvd_14175 (by omega) R (i, vi)).2.val =
        (if x1 = 0 then 14174 else x1 - 1) / digitVal i := by
    intro i
    change ((x + 14175 - 1) % 14175) / digitVal i = _
    rw [hxm1_eq]
  have hpc : ∀ i : Fin 5, predCondBool i x = predCondBool i x1 := fun i =>
    (predCondBool_mod_14175' i x).symm
  rw [Fin.sum_univ_five]
  simp only [hpc, hchild]
  change stepRawWeight x1 = _
  unfold stepRawWeight
  simp only [predCondBool, typeOff, digitVal, Bool.and_eq_true, beq_iff_eq]
  have h5_cases : x1 % 5 = 0 ∨ x1 % 5 = 1 ∨ x1 % 5 = 2 ∨ x1 % 5 = 3 ∨ x1 % 5 = 4 := by omega
  rcases h5_cases with h5 | h5 | h5 | h5 | h5
  · have h25 : x1 % 25 ≠ 1 := by omega
    by_cases h0 : x1 = 0 <;> by_cases h3 : x1 % 3 = 1 <;> by_cases h7 : x1 % 7 = 1 <;>
      simp [h5, h25, h0, h3, h7, beq_false_of_ne']
  · have hne0 : x1 ≠ 0 := by omega
    by_cases h25 : x1 % 25 = 1 <;>
      simp [h5, hne0, h25, beq_false_of_ne']
  · have hne0 : x1 ≠ 0 := by omega
    have h25 : x1 % 25 ≠ 1 := by omega
    by_cases h9 : x1 % 9 = 1 <;>
      simp [h5, hne0, h25, h9, beq_false_of_ne']
  · have h25 : x1 % 25 ≠ 1 := by omega
    simp [h5, h25]
  · have h25 : x1 % 25 ≠ 1 := by omega
    simp [h5, h25]

private lemma sumRawAux_spec (R : Fin 14175) :
    ∀ (rem vi x acc : ℕ), x = (2 ^ vi * R.val) % 14175 →
      sumRawAux rem x acc =
        acc + ∑ k ∈ Finset.range rem, stepRawWeight ((2 ^ (vi + k + 1) * R.val) % 14175) := by
  intro rem
  induction rem with
  | zero => intro vi x acc _; simp [sumRawAux]
  | succ rem ih =>
    intro vi x acc hx
    have hx1 : (2 * x) % 14175 = (2 ^ (vi + 1) * R.val) % 14175 := by
      rw [hx, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, ← pow_succ']
    simp only [sumRawAux]
    rw [ih (vi + 1) ((2 * x) % 14175) (acc + stepRawWeight ((2 * x) % 14175)) hx1]
    rw [Finset.sum_range_succ']
    simp only [add_zero, hx1]
    have hshift : ∀ k, vi + 1 + k = vi + (k + 1) := fun k => by omega
    simp only [hshift]
    omega

/-- Pure-kernel row-sum budget `(eq:b5-budget)` for `certW` with `L = 2269527 / 1000000`. -/
theorem certW_row_sum_le (R : Fin 14175) :
    ∑ mv ∈ movesOf 14175 16 R, certW (childType 14175 16 h1575_dvd_14175 (by omega) R mv) ≤
      (2269527 : ℝ) / 1000000 := by
  have hsum : sumRawAux 16 R.val 0 =
      ∑ mv ∈ movesOf 14175 16 R,
        getW (typeOff mv.1.val + (childType 14175 16 h1575_dvd_14175 (by omega) R mv).2.val) := by
    have h1 := sumRawAux_spec R 16 0 R.val 0 (by simp [Nat.mod_eq_of_lt R.isLt])
    simp only [zero_add] at h1
    rw [h1, ← Fin.sum_univ_eq_sum_range]
    have h2 : ∑ vi : Fin 16, stepRawWeight ((2 ^ (vi.val + 1) * R.val) % 14175) =
        ∑ vi : Fin 16, ∑ i : Fin 5,
          if predCondBool i (2 ^ (vi.val + 1) * R.val) then
            getW (typeOff i.val + (childType 14175 16 h1575_dvd_14175 (by omega) R (i, vi)).2.val)
          else 0 :=
      Finset.sum_congr rfl fun vi _ => stepRawWeight_eq_sum R vi
    rw [h2, Finset.sum_comm, ← Fintype.sum_prod_type']
    unfold movesOf
    rw [Finset.sum_filter]
  have hnat : (∑ mv ∈ movesOf 14175 16 R,
      getW (typeOff mv.1.val + (childType 14175 16 h1575_dvd_14175 (by omega) R mv).2.val)) ≤
      2269527 := by
    rw [← hsum]
    exact checkRowCap_all R.val R.isLt
  have hR : (∑ mv ∈ movesOf 14175 16 R,
      (getW (typeOff mv.1.val + (childType 14175 16 h1575_dvd_14175 (by omega) R mv).2.val) : ℝ)) ≤
      (2269527 : ℝ) := by exact_mod_cast hnat
  unfold certW
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right hR (by norm_num)

/-- **Theorem `thm:basin-sharp` (Part 2, exact constant form, pure-kernel Lean 4)**:
    for every integer `X ≥ 3`,
    `N5(X) ≥ (98959 / (2269527 * 3^(13/20))) * X^(13/20)`. -/
theorem thm_basin5_sharp (X : ℕ) (hX : 3 ≤ X) :
    ((98959 : ℝ) / ((2269527 : ℝ) * (3 : ℝ) ^ ((13 : ℝ) / 20))) * (X : ℝ) ^ ((13 : ℝ) / 20) ≤
      (N5 X : ℝ) := by
  have hexpand : ∀ (t : TypeId 14175) (R : Fin 14175),
      R.val % (14175 / digitVal t.1) = t.2.val →
      certW t ≤ ∑ mv ∈ movesOf 14175 16 R,
        ((digitVal mv.1 : ℝ) / (2 : ℝ) ^ (mv.2.val + 1)) ^ ((13 : ℝ) / 20) *
          certW (childType 14175 16 h1575_dvd_14175 (by omega) R mv) := by
    intro t R hcomp
    have h0 := certW_sub_eig t R hcomp
    have hs_eq : (65 : ℝ) / 100 = (13 : ℝ) / 20 := by norm_num
    rw [hs_eq] at h0
    refine h0.trans_eq (Finset.sum_congr rfl fun mv _ => ?_)
    rw [div_two_pow_rpow_eq (digitVal mv.1 : ℝ) (by positivity) (mv.2.val + 1) ((13 : ℝ) / 20)]
  have htree := lem_weighted_tree3
    h1575_dvd_14175 (by omega)
    (by norm_num : (0 : ℝ) < (13 : ℝ) / 20) (by norm_num : (0 : ℝ) < (2269527 : ℝ) / 1000000)
    certW certW_nonneg hexpand certW_row_sum_le
    (o := 3) (X := X) (by omega) (by decide) (reaches_refl f 3) hX
    ⟨0, ⟨3, by decide⟩⟩ (by decide)
  rw [certW_root] at htree
  have hsub : NTree 3 X ≤ N5 X := by
    classical
    unfold NTree N5
    refine Finset.card_le_card fun m hm => ?_
    simp only [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, hm.2.1, reaches_trans hm.2.2 ⟨2, by decide⟩⟩
  have hdiv : ((X : ℝ) / (3 : ℝ)) ^ ((13 : ℝ) / 20) =
      (X : ℝ) ^ ((13 : ℝ) / 20) / (3 : ℝ) ^ ((13 : ℝ) / 20) :=
    Real.div_rpow (by positivity) (by norm_num) ((13 : ℝ) / 20)
  push_cast at htree
  rw [hdiv] at htree
  have hNTree : ((98959 : ℝ) / ((2269527 : ℝ) * (3 : ℝ) ^ ((13 : ℝ) / 20))) *
      (X : ℝ) ^ ((13 : ℝ) / 20) ≤ (NTree 3 X : ℝ) := by
    have hLpos : (0 : ℝ) < (2269527 : ℝ) / 1000000 := by norm_num
    have h3pos : (0 : ℝ) < (3 : ℝ) ^ ((13 : ℝ) / 20) := by positivity
    have h1 : ((X : ℝ) ^ ((13 : ℝ) / 20) / (3 : ℝ) ^ ((13 : ℝ) / 20) * (98959 / 1000000 : ℝ)) /
        ((2269527 : ℝ) / 1000000) ≤ (NTree 3 X : ℝ) :=
      (div_le_iff₀ hLpos).mpr (by linarith)
    refine (le_of_eq ?_).trans h1
    field_simp
  exact hNTree.trans (by exact_mod_cast hsub)

/-- **Theorem `thm:basin-sharp` (Part 2, decimal lower bound)**:
    for every integer `X ≥ 3`, `N5(X) > 0.02134 * X^(13/20)`. -/
theorem thm_basin5_sharp_gt (X : ℕ) (hX : 3 ≤ X) :
    (2134 / 100000 : ℝ) * (X : ℝ) ^ ((13 : ℝ) / 20) < (N5 X : ℝ) := by
  have hconst : (2134 / 100000 : ℝ) <
      (98959 : ℝ) / ((2269527 : ℝ) * (3 : ℝ) ^ ((13 : ℝ) / 20)) := by
    have h3pos : (0 : ℝ) < (3 : ℝ) ^ ((13 : ℝ) / 20) := by positivity
    rw [lt_div_iff₀ (mul_pos (by norm_num) h3pos)]
    have h20 : ((2134 / 100000 : ℝ) * ((2269527 : ℝ) * (3 : ℝ) ^ ((13 : ℝ) / 20))) ^ (20 : ℕ) <
        (98959 : ℝ) ^ (20 : ℕ) := by
      rw [mul_pow, mul_pow,
          ← Real.rpow_natCast ((3 : ℝ) ^ ((13 : ℝ) / 20)) 20, ← Real.rpow_mul (by norm_num)]
      have hexp : ((13 : ℝ) / 20) * (20 : ℕ) = (13 : ℕ) := by norm_num
      rw [hexp, Real.rpow_natCast]
      norm_num
    exact lt_of_pow_lt_pow_left₀ 20 (by norm_num) h20
  have hXpos : (0 : ℝ) < (X : ℝ) ^ ((13 : ℝ) / 20) := by
    have : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
    positivity
  exact (mul_lt_mul_of_pos_right hconst hXpos).trans_le (thm_basin5_sharp X hX)

end Ouroboros
