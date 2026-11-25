module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import Ouroboros.Defs
public import Ouroboros.BasinOne
public import Ouroboros.BasinFive
public import Ouroboros.BasinFiveCert
@[expose] public section

/-! # Pure-kernel unconditional Theorem 13 (basin of 5) and Corollary 14 (basin separation) -/

namespace Ouroboros
open BasinFiveCert
/-- Finite-halving-horizon weighted predecessor-tree lower bound (`1 ≤ v ≤ Vmax`): dropping all moves with -/
theorem lemma_tree_weights_trunc
    {Q Vmax K : ℕ} (hQ1575 : 1575 ∣ Q) (hQpos : 0 < Q)
    (hKpos : 1 ≤ K) (hK : ∀ R : Fin Q, (movesOf Q Vmax R).card ≤ K)
    {c M_w : ℝ} (hc : 0 < c) (hMw : 0 < M_w)
    (w : TypeId Q → ℝ) (hw_nn : ∀ t, 0 ≤ w t) (hw_le : ∀ t, w t ≤ M_w)
    (hsub : ∀ (t : TypeId Q) (R : Fin Q),
      R.val % (Q / digitVal t.1) = t.2.val →
      w t ≤ ∑ mv ∈ movesOf Q Vmax R,
        ((digitVal mv.1 : ℝ) ^ c * (2 : ℝ) ^ (-(c * ((mv.2.val + 1 : ℕ) : ℝ)))) *
          w (childType Q Vmax hQ1575 hQpos R mv)) :
    ∀ (o X : ℕ), 0 < o → o % 2 = 1 → o ≤ X → NonPeriodic o →
      ∀ (t : TypeId Q), o % (Q / digitVal t.1) = t.2.val →
        (1 / ((K : ℝ) * M_w)) * w t * ((X : ℝ) / (o : ℝ)) ^ c ≤ (NTree o X : ℝ) := by
  set eps : ℝ := 1 / ((K : ℝ) * M_w)
  have heps_pos : 0 < eps := by
    have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
    positivity
  suffices hstrong : ∀ N : ℕ, ∀ (o X : ℕ), NTree o X = N →
      0 < o → o % 2 = 1 → o ≤ X → NonPeriodic o →
      ∀ (t : TypeId Q), o % (Q / digitVal t.1) = t.2.val →
        eps * w t * ((X : ℝ) / (o : ℝ)) ^ c ≤ (NTree o X : ℝ) by
    intro o X ho_pos ho_odd ho_le hnp t ht; exact hstrong (NTree o X) o X rfl ho_pos ho_odd ho_le hnp t ht
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro o X hN_eq ho_pos ho_odd ho_le hnp t ht
    let R : Fin Q := ⟨o % Q, Nat.mod_lt o hQpos⟩
    have hR_comp : R.val % (Q / digitVal t.1) = t.2.val := by
      have hdvd : Q / digitVal t.1 ∣ Q := Nat.div_dvd_of_dvd ((digitVal_dvd_1575 t.1).trans hQ1575)
      rw [Nat.mod_mod_of_dvd o hdvd]; exact ht
    let predOf (mv : Fin 5 × Fin Vmax) : ℕ := (2 ^ (mv.2.val + 1) * o - 1) / digitVal mv.1
    have hpred_props : ∀ mv ∈ movesOf Q Vmax R,
        let m := predOf mv
        0 < m ∧ m % 2 = 1 ∧ d m = digitVal mv.1 ∧
        d m * m + 1 = 2 ^ (mv.2.val + 1) * o ∧
        f^[mv.2.val + 2] m = o ∧
        m % (Q / digitVal mv.1) = (childType Q Vmax hQ1575 hQpos R mv).2.val := by
      intro mv hmv
      have hcondR : predCond mv.1 (2 ^ (mv.2.val + 1) * R.val) := by
        simp only [movesOf, Finset.mem_filter, Finset.mem_univ, true_and] at hmv; exact (predCondBool_iff _ _).mp hmv
      have hmodQ : (2 ^ (mv.2.val + 1) * o) % Q = (2 ^ (mv.2.val + 1) * R.val) % Q := by simp [R, Nat.mul_mod]
      have hmod1575 : (2 ^ (mv.2.val + 1) * o) % 1575 =
          (2 ^ (mv.2.val + 1) * R.val) % 1575 := by
        rw [← Nat.mod_mod_of_dvd (2 ^ (mv.2.val + 1) * o) hQ1575,
            ← Nat.mod_mod_of_dvd (2 ^ (mv.2.val + 1) * R.val) hQ1575, hmodQ]
      have hcond : predCond mv.1 (2 ^ (mv.2.val + 1) * o) := (predCond_mod_1575 mv.1 hmod1575).mpr hcondR
      obtain ⟨hm_pos, hm_odd, hdm, heq, hstep⟩ := lemma_odd_predecessors_unique ho_pos ho_odd (by omega) mv.1 hcond
      refine ⟨hm_pos, hm_odd, hdm, heq, hstep, ?_⟩
      have hd_pos : 0 < digitVal mv.1 := digitVal_pos mv.1
      have hdQ : digitVal mv.1 ∣ Q := (digitVal_dvd_1575 mv.1).trans hQ1575
      have hx_pos : 1 ≤ 2 ^ (mv.2.val + 1) * o := by
        have : 1 ≤ 2 ^ (mv.2.val + 1) := Nat.one_le_pow _ _ (by norm_num)
        nlinarith
      have hdy : digitVal mv.1 ∣ (2 ^ (mv.2.val + 1) * o - 1) := by
        have h1 : digitVal mv.1 * predOf mv + 1 = 2 ^ (mv.2.val + 1) * o := by rw [← hdm]; exact heq
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
      rw [hsub_mod]; rfl
    classical
    let active : Finset (Fin 5 × Fin Vmax) :=
      (movesOf Q Vmax R).filter fun mv => 2 ^ (mv.2.val + 1) * o ≤ digitVal mv.1 * X
    have hpred_inj : Set.InjOn predOf (active : Set _) := by
      intro mv1 h1 mv2 h2 hEq; simp only [Finset.mem_coe, active, Finset.mem_filter] at h1 h2
      obtain ⟨_, _, hd1, heq1, _, _⟩ := hpred_props mv1 h1.1; obtain ⟨_, _, hd2, heq2, _, _⟩ := hpred_props mv2 h2.1
      have hi : mv1.1 = mv2.1 := digitVal_inj (by rw [← hd1, ← hd2, hEq])
      have hpow : 2 ^ (mv1.2.val + 1) * o = 2 ^ (mv2.2.val + 1) * o := by rw [← heq1, ← heq2, hEq]
      have hexp := (two_pow_mul_odd_inj ho_odd ho_odd hpow).1; exact Prod.ext hi (Fin.ext (by omega))
    let S : Finset ℕ := active.image predOf
    have hS_valid : ∀ m ∈ S, m ≤ X ∧ m % 2 = 1 ∧ ∃ v ≥ 1, d m * m + 1 = 2 ^ v * o := by
      intro m hm; simp only [S, Finset.mem_image] at hm; obtain ⟨mv, hmv, rfl⟩ := hm
      simp only [active, Finset.mem_filter] at hmv; obtain ⟨_, hm_odd, hdm, heq, _, _⟩ := hpred_props mv hmv.1
      have hleX : predOf mv ≤ X := by
        have hdm_pos : 0 < digitVal mv.1 := digitVal_pos mv.1
        have h1 : digitVal mv.1 * predOf mv ≤ digitVal mv.1 * X := by
          conv_lhs => rw [← hdm]
          omega
        exact Nat.le_of_mul_le_mul_left h1 hdm_pos
      exact ⟨hleX, hm_odd, mv.2.val + 1, by omega, heq⟩
    obtain ⟨hN_sum, hN_lt⟩ := NTree_ge_one_add_sum ho_pos ho_odd ho_le hnp S hS_valid
    let contrib (mv : Fin 5 × Fin Vmax) : ℝ :=
      if 2 ^ (mv.2.val + 1) * o ≤ digitVal mv.1 * X then (NTree (predOf mv) X : ℝ) else 0
    have hsum_eq : ∑ m ∈ S, (NTree m X : ℝ) = ∑ mv ∈ movesOf Q Vmax R, contrib mv := by
      unfold S; rw [Finset.sum_image (fun a ha b hb h => hpred_inj ha hb h)]; unfold active contrib
      rw [Finset.sum_filter]
    have hmove_ge : ∀ mv ∈ movesOf Q Vmax R,
        eps * ((X : ℝ) / (o : ℝ)) ^ c *
          (((digitVal mv.1 : ℝ) ^ c * (2 : ℝ) ^ (-(c * ((mv.2.val + 1 : ℕ) : ℝ)))) *
            w (childType Q Vmax hQ1575 hQpos R mv)) - eps * M_w ≤ contrib mv := by
      intro mv hmv; have hw_nn_c := hw_nn (childType Q Vmax hQ1575 hQpos R mv)
      have hw_le_M := hw_le (childType Q Vmax hQ1575 hQpos R mv); unfold contrib
      split_ifs with hle
      · have hmv_act : mv ∈ active := Finset.mem_filter.mpr ⟨hmv, hle⟩
        have hm_in_S : predOf mv ∈ S := Finset.mem_image.mpr ⟨mv, hmv_act, rfl⟩
        have hlt_N : NTree (predOf mv) X < N := by rw [← hN_eq]; exact hN_lt _ hm_in_S
        obtain ⟨hm_pos, hm_odd, hdm, heq, hstep, htype⟩ := hpred_props mv hmv
        have hm_le : predOf mv ≤ X := (hS_valid _ hm_in_S).1
        have hm_np : NonPeriodic (predOf mv) := nonperiodic_of_reaches ⟨mv.2.val + 2, hstep⟩ hnp
        have hih := ih (NTree (predOf mv) X) hlt_N (predOf mv) X rfl
          hm_pos hm_odd hm_le hm_np (childType Q Vmax hQ1575 hQpos R mv) htype
        have hm_lt : (predOf mv : ℝ) <
            (2 : ℝ) ^ (mv.2.val + 1) * (o : ℝ) / (digitVal mv.1 : ℝ) := by
          have hd_pos : (0 : ℝ) < (digitVal mv.1 : ℝ) := by exact_mod_cast digitVal_pos mv.1
          rw [lt_div_iff₀ hd_pos]
          have hnat : predOf mv * digitVal mv.1 < 2 ^ (mv.2.val + 1) * o := by rw [mul_comm, ← hdm]; omega
          exact_mod_cast hnat
        have hratio : ((X : ℝ) / (o : ℝ)) * (digitVal mv.1 : ℝ) *
            ((2 : ℝ) ^ (mv.2.val + 1))⁻¹ ≤ (X : ℝ) / (predOf mv : ℝ) := by
          have hm_posR : (0 : ℝ) < (predOf mv : ℝ) := by exact_mod_cast hm_pos
          have ho_posR : (0 : ℝ) < (o : ℝ) := by exact_mod_cast ho_pos
          have hd_posR : (0 : ℝ) < (digitVal mv.1 : ℝ) := by exact_mod_cast digitVal_pos mv.1
          have h2_posR : (0 : ℝ) < (2 : ℝ) ^ (mv.2.val + 1) := by positivity
          rw [le_div_iff₀ hm_posR]
          have h1 : (predOf mv : ℝ) * (digitVal mv.1 : ℝ) ≤
              (2 : ℝ) ^ (mv.2.val + 1) * (o : ℝ) := by
            have := (lt_div_iff₀ hd_posR).mp hm_lt; linarith
          have h2 : ((X : ℝ) / (o : ℝ)) * (digitVal mv.1 : ℝ) *
              ((2 : ℝ) ^ (mv.2.val + 1))⁻¹ * (predOf mv : ℝ) =
              (X : ℝ) * ((predOf mv : ℝ) * (digitVal mv.1 : ℝ)) /
                ((2 : ℝ) ^ (mv.2.val + 1) * (o : ℝ)) := by ring
          rw [h2, div_le_iff₀ (mul_pos h2_posR ho_posR)]; nlinarith [show (0 : ℝ) ≤ (X : ℝ) by positivity]
        have h2r : (((2 : ℝ) ^ (mv.2.val + 1))⁻¹) ^ c =
            (2 : ℝ) ^ (-(c * ((mv.2.val + 1 : ℕ) : ℝ))) := by
          rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast 2,
              ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
          congr 1; ring
        have hpow_ge : ((X : ℝ) / (o : ℝ)) ^ c * (digitVal mv.1 : ℝ) ^ c *
            (2 : ℝ) ^ (-(c * ((mv.2.val + 1 : ℕ) : ℝ))) ≤
            ((X : ℝ) / (predOf mv : ℝ)) ^ c := by
          calc ((X : ℝ) / (o : ℝ)) ^ c * (digitVal mv.1 : ℝ) ^ c *
                (2 : ℝ) ^ (-(c * ((mv.2.val + 1 : ℕ) : ℝ)))
              = (((X : ℝ) / (o : ℝ)) * (digitVal mv.1 : ℝ) *
                  ((2 : ℝ) ^ (mv.2.val + 1))⁻¹) ^ c := by
                  rw [Real.mul_rpow (by positivity) (by positivity),
                      Real.mul_rpow (by positivity) (by positivity), h2r]
            _ ≤ ((X : ℝ) / (predOf mv : ℝ)) ^ c := Real.rpow_le_rpow (by positivity) hratio hc.le
        have hmain : eps * ((X : ℝ) / (o : ℝ)) ^ c *
            (((digitVal mv.1 : ℝ) ^ c * (2 : ℝ) ^ (-(c * ((mv.2.val + 1 : ℕ) : ℝ)))) *
              w (childType Q Vmax hQ1575 hQpos R mv)) ≤ (NTree (predOf mv) X : ℝ) := by
          calc eps * ((X : ℝ) / (o : ℝ)) ^ c *
                (((digitVal mv.1 : ℝ) ^ c * (2 : ℝ) ^ (-(c * ((mv.2.val + 1 : ℕ) : ℝ)))) *
                  w (childType Q Vmax hQ1575 hQpos R mv))
              = eps * w (childType Q Vmax hQ1575 hQpos R mv) *
                  (((X : ℝ) / (o : ℝ)) ^ c * (digitVal mv.1 : ℝ) ^ c *
                    (2 : ℝ) ^ (-(c * ((mv.2.val + 1 : ℕ) : ℝ)))) := by ring
            _ ≤ eps * w (childType Q Vmax hQ1575 hQpos R mv) *
                  ((X : ℝ) / (predOf mv : ℝ)) ^ c :=
                  mul_le_mul_of_nonneg_left hpow_ge (mul_nonneg heps_pos.le hw_nn_c)
            _ ≤ (NTree (predOf mv) X : ℝ) := hih
        have : 0 ≤ eps * M_w := by positivity
        linarith
      · have hgt_nat : digitVal mv.1 * X < 2 ^ (mv.2.val + 1) * o := by omega
        have hgt_R : (digitVal mv.1 : ℝ) * (X : ℝ) < (2 : ℝ) ^ (mv.2.val + 1) * (o : ℝ) := by exact_mod_cast hgt_nat
        have hfrac_le1 : ((X : ℝ) / (o : ℝ)) * (digitVal mv.1 : ℝ) *
            ((2 : ℝ) ^ (mv.2.val + 1))⁻¹ ≤ 1 := by
          have ho_posR : (0 : ℝ) < (o : ℝ) := by exact_mod_cast ho_pos
          have h2_posR : (0 : ℝ) < (2 : ℝ) ^ (mv.2.val + 1) := by positivity
          have : ((X : ℝ) / (o : ℝ)) * (digitVal mv.1 : ℝ) *
              ((2 : ℝ) ^ (mv.2.val + 1))⁻¹ =
              ((digitVal mv.1 : ℝ) * (X : ℝ)) / ((2 : ℝ) ^ (mv.2.val + 1) * (o : ℝ)) := by ring
          rw [this, div_le_one (mul_pos h2_posR ho_posR)]; exact hgt_R.le
        have h2r : (((2 : ℝ) ^ (mv.2.val + 1))⁻¹) ^ c =
            (2 : ℝ) ^ (-(c * ((mv.2.val + 1 : ℕ) : ℝ))) := by
          rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast 2,
              ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
          congr 1; ring
        have hpow_le1 : ((X : ℝ) / (o : ℝ)) ^ c * (digitVal mv.1 : ℝ) ^ c *
            (2 : ℝ) ^ (-(c * ((mv.2.val + 1 : ℕ) : ℝ))) ≤ 1 := by
          calc ((X : ℝ) / (o : ℝ)) ^ c * (digitVal mv.1 : ℝ) ^ c *
                (2 : ℝ) ^ (-(c * ((mv.2.val + 1 : ℕ) : ℝ)))
              = (((X : ℝ) / (o : ℝ)) * (digitVal mv.1 : ℝ) *
                  ((2 : ℝ) ^ (mv.2.val + 1))⁻¹) ^ c := by
                  rw [Real.mul_rpow (by positivity) (by positivity),
                      Real.mul_rpow (by positivity) (by positivity), h2r]
            _ ≤ (1 : ℝ) ^ c := Real.rpow_le_rpow (by positivity) hfrac_le1 hc.le
            _ = 1 := Real.one_rpow c
        have hprod_le : ((X : ℝ) / (o : ℝ)) ^ c * (digitVal mv.1 : ℝ) ^ c *
            (2 : ℝ) ^ (-(c * ((mv.2.val + 1 : ℕ) : ℝ))) *
            w (childType Q Vmax hQ1575 hQpos R mv) ≤ M_w := by
          calc _ ≤ 1 * M_w := mul_le_mul hpow_le1 hw_le_M hw_nn_c zero_le_one
            _ = M_w := one_mul M_w
        have hterm : eps * ((X : ℝ) / (o : ℝ)) ^ c *
            (((digitVal mv.1 : ℝ) ^ c * (2 : ℝ) ^ (-(c * ((mv.2.val + 1 : ℕ) : ℝ)))) *
              w (childType Q Vmax hQ1575 hQpos R mv)) ≤ eps * M_w := by
          have : eps * ((X : ℝ) / (o : ℝ)) ^ c *
              (((digitVal mv.1 : ℝ) ^ c * (2 : ℝ) ^ (-(c * ((mv.2.val + 1 : ℕ) : ℝ)))) *
                w (childType Q Vmax hQ1575 hQpos R mv)) =
              eps * (((X : ℝ) / (o : ℝ)) ^ c * (digitVal mv.1 : ℝ) ^ c *
                (2 : ℝ) ^ (-(c * ((mv.2.val + 1 : ℕ) : ℝ))) *
                w (childType Q Vmax hQ1575 hQpos R mv)) := by ring
          rw [this]; exact mul_le_mul_of_nonneg_left hprod_le heps_pos.le
        linarith
    have htotal : eps * ((X : ℝ) / (o : ℝ)) ^ c *
        (∑ mv ∈ movesOf Q Vmax R,
          ((digitVal mv.1 : ℝ) ^ c * (2 : ℝ) ^ (-(c * ((mv.2.val + 1 : ℕ) : ℝ)))) *
            w (childType Q Vmax hQ1575 hQpos R mv)) -
        ((movesOf Q Vmax R).card : ℝ) * (eps * M_w) ≤
        ∑ mv ∈ movesOf Q Vmax R, contrib mv := by
      have h1 := Finset.sum_le_sum fun mv hmv => hmove_ge mv hmv
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at h1; exact h1
    have hsub_le1 : ((movesOf Q Vmax R).card : ℝ) * (eps * M_w) ≤ 1 := by
      have hcard_le : ((movesOf Q Vmax R).card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK R
      have hK_eq : (K : ℝ) * (eps * M_w) = 1 := by
        unfold eps
        have hK_ne : (K : ℝ) ≠ 0 := by
          have : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
          exact ne_of_gt this
        have hMw_ne : M_w ≠ 0 := ne_of_gt hMw; field_simp
      calc ((movesOf Q Vmax R).card : ℝ) * (eps * M_w)
          ≤ (K : ℝ) * (eps * M_w) := mul_le_mul_of_nonneg_right hcard_le (by positivity)
        _ = 1 := hK_eq
    have hN_cast : (1 : ℝ) + ∑ m ∈ S, (NTree m X : ℝ) ≤ (NTree o X : ℝ) := by exact_mod_cast hN_sum
    have hT_ge := hsub t R hR_comp
    have hmul_T : eps * w t * ((X : ℝ) / (o : ℝ)) ^ c ≤
        eps * ((X : ℝ) / (o : ℝ)) ^ c *
          (∑ mv ∈ movesOf Q Vmax R,
            ((digitVal mv.1 : ℝ) ^ c * (2 : ℝ) ^ (-(c * ((mv.2.val + 1 : ℕ) : ℝ)))) *
              w (childType Q Vmax hQ1575 hQpos R mv)) := by
      have : eps * w t * ((X : ℝ) / (o : ℝ)) ^ c = eps * ((X : ℝ) / (o : ℝ)) ^ c * w t := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left hT_ge (by positivity)
    linarith

/-! ## Bridge from the pure-kernel `BasinFiveCert` to `lemma_tree_weights_trunc` -/
/-- Real weight vector on `TypeId 14175` backed by the pure-kernel `QuadTree` `wTree`. -/
noncomputable def certW (t : TypeId 14175) : ℝ := (getW (typeOff t.1.val + t.2.val) : ℝ) / 1000000
lemma certW_nonneg (t : TypeId 14175) : 0 ≤ certW t := by unfold certW; positivity
lemma certW_le_one (t : TypeId 14175) : certW t ≤ 1 := by
  unfold certW
  have h : (getW (typeOff t.1.val + t.2.val) : ℝ) ≤ 1000000 := by exact_mod_cast getW_le_scale _
  linarith
lemma certW_root : certW ⟨0, ⟨3, by decide⟩⟩ = 98959 / 1000000 := by
  unfold certW; change (getW 3 : ℝ) / 1000000 = 98959 / 1000000; rw [getW_root]; norm_num
lemma K_bound_80 (R : Fin 14175) : (movesOf 14175 16 R).card ≤ 80 := by
  calc (movesOf 14175 16 R).card
      ≤ (Finset.univ : Finset (Fin 5 × Fin 16)).card := Finset.card_filter_le _ _
    _ = 80 := by decide
lemma typeMod_eq (i : Fin 5) : typeMod i.val = 14175 / digitVal i := by fin_cases i <;> decide
lemma coeff_le_rpow (i : Fin 5) (vi : Fin 16) :
    (getC i.val vi.val : ℝ) / 1000000 ≤
      (digitVal i : ℝ) ^ ((65 : ℝ) / 100) *
        (2 : ℝ) ^ (-(((65 : ℝ) / 100) * ((vi.val + 1 : ℕ) : ℝ))) := by
  have hnat := checkCoeff_sound i.val vi.val i.isLt vi.isLt
  have hdig : certDigit i.val = digitVal i := by fin_cases i <;> rfl
  rw [hdig] at hnat
  have hR : (getC i.val vi.val : ℝ) ^ (20 : ℕ) * (2 : ℝ) ^ (13 * (vi.val + 1)) ≤
      (1000000 : ℝ) ^ (20 : ℕ) * (digitVal i : ℝ) ^ (13 : ℕ) := by
    exact_mod_cast hnat
  have hd_pos : (0 : ℝ) < (digitVal i : ℝ) := by exact_mod_cast digitVal_pos i
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ (13 * (vi.val + 1)) := by positivity
  have hpow20 : ((getC i.val vi.val : ℝ) / 1000000) ^ (20 : ℕ) ≤
      ((digitVal i : ℝ) ^ ((65 : ℝ) / 100) *
        (2 : ℝ) ^ (-(((65 : ℝ) / 100) * ((vi.val + 1 : ℕ) : ℝ)))) ^ (20 : ℕ) := by
    rw [div_pow, mul_pow]; rw [← Real.rpow_natCast ((digitVal i : ℝ) ^ _) 20, ← Real.rpow_mul hd_pos.le]
    rw [← Real.rpow_natCast ((2 : ℝ) ^ _) 20, ← Real.rpow_mul (by norm_num)]
    have hexp1 : ((65 : ℝ) / 100) * (20 : ℕ) = (13 : ℕ) := by norm_num
    have hexp2 : -(((65 : ℝ) / 100) * ((vi.val + 1 : ℕ) : ℝ)) * (20 : ℕ) =
        -((13 * (vi.val + 1) : ℕ) : ℝ) := by push_cast; ring
    rw [hexp1, hexp2, Real.rpow_natCast, Real.rpow_neg (by norm_num), Real.rpow_natCast,
        ← div_eq_mul_inv]
    rw [div_le_div_iff₀ (by positivity) h2_pos]
    linarith
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hpow20
private lemma predCondBool_mod_14175 (i : Fin 5) (x : ℕ) : predCondBool i (x % 14175) = predCondBool i x := by
  have h1 : (x % 14175) % 1575 = x % 1575 := Nat.mod_mod_of_dvd x h1575_dvd_14175; have hiff := predCond_mod_1575 i h1
  cases hb1 : predCondBool i (x % 14175) <;> cases hb2 : predCondBool i x
  · rfl
  · exfalso; have h2 := (predCondBool_iff i x).mp hb2; have h3 := (predCondBool_iff i (x % 14175)).mpr (hiff.mpr h2)
    rw [hb1] at h3; exact Bool.false_ne_true h3
  · exfalso; have h2 := (predCondBool_iff i (x % 14175)).mp hb1; have h3 := (predCondBool_iff i x).mpr (hiff.mp h2)
    rw [hb2] at h3; exact Bool.false_ne_true h3
  · rfl
private lemma beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h
private lemma stepSum_eq_sum (R : Fin 14175) (vi : Fin 16) :
    stepSum vi.val ((2 ^ (vi.val + 1) * R.val) % 14175) =
      ∑ i : Fin 5,
        if predCondBool i (2 ^ (vi.val + 1) * R.val) then
          getC i.val vi.val *
            getW (typeOff i.val + (childType 14175 16 h1575_dvd_14175 (by omega) R (i, vi)).2.val)
        else 0 := by
  set x := 2 ^ (vi.val + 1) * R.val; set x1 := x % 14175; have hx1_lt : x1 < 14175 := Nat.mod_lt x (by omega)
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
    intro i; change ((x + 14175 - 1) % 14175) / digitVal i = _; rw [hxm1_eq]
  have hpc : ∀ i : Fin 5, predCondBool i x = predCondBool i x1 := fun i => (predCondBool_mod_14175 i x).symm
  rw [Fin.sum_univ_five]; simp only [hpc, hchild]; change stepSum vi.val x1 = _; unfold stepSum
  simp only [predCondBool, getC, typeOff, digitVal, Bool.and_eq_true, beq_iff_eq]
  have h5_cases : x1 % 5 = 0 ∨ x1 % 5 = 1 ∨ x1 % 5 = 2 ∨ x1 % 5 = 3 ∨ x1 % 5 = 4 := by omega
  rcases h5_cases with h5 | h5 | h5 | h5 | h5
  · have h25 : x1 % 25 ≠ 1 := by omega
    by_cases h0 : x1 = 0 <;> by_cases h3 : x1 % 3 = 1 <;> by_cases h7 : x1 % 7 = 1 <;>
      simp [h5, h25, h0, h3, h7, beq_false_of_ne]
  · have hne0 : x1 ≠ 0 := by omega
    by_cases h25 : x1 % 25 = 1 <;>
      simp [h5, hne0, h25, beq_false_of_ne]
  · have hne0 : x1 ≠ 0 := by omega
    have h25 : x1 % 25 ≠ 1 := by omega
    by_cases h9 : x1 % 9 = 1 <;>
      simp [h5, hne0, h25, h9, beq_false_of_ne]
  · have h25 : x1 % 25 ≠ 1 := by omega
    simp [h5, h25]
  · have h25 : x1 % 25 ≠ 1 := by omega
    simp [h5, h25]
private lemma sumMovesAux_spec (R : Fin 14175) :
    ∀ (rem vi x acc : ℕ), x = (2 ^ vi * R.val) % 14175 →
      sumMovesAux rem vi x acc =
        acc + ∑ k ∈ Finset.range rem, stepSum (vi + k) ((2 ^ (vi + k + 1) * R.val) % 14175) := by
  intro rem
  induction rem with
  | zero => intro vi x acc _; simp [sumMovesAux]
  | succ rem ih =>
    intro vi x acc hx
    have hx1 : (2 * x) % 14175 = (2 ^ (vi + 1) * R.val) % 14175 := by
      rw [hx, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, ← pow_succ']
    simp only [sumMovesAux]; rw [ih (vi + 1) ((2 * x) % 14175) (acc + stepSum vi ((2 * x) % 14175)) hx1]
    rw [Finset.sum_range_succ']; simp only [add_zero, hx1]
    have hshift : ∀ k, vi + 1 + k = vi + (k + 1) := fun k => by omega
    simp only [hshift]; omega
private lemma sumMovesAux_eq_fin_sum (R : Fin 14175) :
    sumMovesAux 16 0 R.val 0 =
      ∑ mv ∈ movesOf 14175 16 R,
        getC mv.1.val mv.2.val *
          getW (typeOff mv.1.val + (childType 14175 16 h1575_dvd_14175 (by omega) R mv).2.val) := by
  have h1 := sumMovesAux_spec R 16 0 R.val 0 (by simp [Nat.mod_eq_of_lt R.isLt])
  simp only [zero_add] at h1; rw [h1, ← Fin.sum_univ_eq_sum_range]
  have h2 : ∑ vi : Fin 16, stepSum vi.val ((2 ^ (vi.val + 1) * R.val) % 14175) =
      ∑ vi : Fin 16, ∑ i : Fin 5,
        if predCondBool i (2 ^ (vi.val + 1) * R.val) then
          getC i.val vi.val *
            getW (typeOff i.val + (childType 14175 16 h1575_dvd_14175 (by omega) R (i, vi)).2.val)
        else 0 := by
    refine Finset.sum_congr rfl fun vi _ => stepSum_eq_sum R vi
  rw [h2, Finset.sum_comm, ← Fintype.sum_prod_type']; unfold movesOf; rw [Finset.sum_filter]
lemma certW_sub_eig (t : TypeId 14175) (R : Fin 14175)
    (hcomp : R.val % (14175 / digitVal t.1) = t.2.val) :
    certW t ≤ ∑ mv ∈ movesOf 14175 16 R,
      ((digitVal mv.1 : ℝ) ^ ((65 : ℝ) / 100) *
        (2 : ℝ) ^ (-(((65 : ℝ) / 100) * ((mv.2.val + 1 : ℕ) : ℝ)))) *
        certW (childType 14175 16 h1575_dvd_14175 (by omega) R mv) := by
  have hnat := checkR_type_le R.val t.1.val R.isLt t.1.isLt
  rw [typeMod_eq t.1, hcomp, sumMovesAux_eq_fin_sum R] at hnat
  have hR : (getW (typeOff t.1.val + t.2.val) : ℝ) * 1000000 ≤
      ∑ mv ∈ movesOf 14175 16 R,
        (getC mv.1.val mv.2.val : ℝ) *
          (getW (typeOff mv.1.val +
            (childType 14175 16 h1575_dvd_14175 (by omega) R mv).2.val) : ℝ) := by
    exact_mod_cast hnat
  have hdiv : certW t ≤
      ∑ mv ∈ movesOf 14175 16 R,
        ((getC mv.1.val mv.2.val : ℝ) / 1000000) *
          certW (childType 14175 16 h1575_dvd_14175 (by omega) R mv) := by
    unfold certW
    have hscale : (0 : ℝ) < (1000000 : ℝ) * 1000000 := by norm_num
    have h1 := div_le_div_of_nonneg_right hR hscale.le
    have hlhs : (getW (typeOff t.1.val + t.2.val) : ℝ) * 1000000 / (1000000 * 1000000) =
        (getW (typeOff t.1.val + t.2.val) : ℝ) / 1000000 := by ring
    have hrhs : (∑ mv ∈ movesOf 14175 16 R,
        (getC mv.1.val mv.2.val : ℝ) *
          (getW (typeOff mv.1.val +
            (childType 14175 16 h1575_dvd_14175 (by omega) R mv).2.val) : ℝ)) /
        (1000000 * 1000000) =
        ∑ mv ∈ movesOf 14175 16 R,
          ((getC mv.1.val mv.2.val : ℝ) / 1000000) *
            ((getW (typeOff mv.1.val +
              (childType 14175 16 h1575_dvd_14175 (by omega) R mv).2.val) : ℝ) / 1000000) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun mv _ => ?_
      ring
    rw [hlhs, hrhs] at h1; exact h1
  refine hdiv.trans (Finset.sum_le_sum fun mv _ => ?_)
  exact mul_le_mul_of_nonneg_right (coeff_le_rpow mv.1 mv.2) (certW_nonneg _)

/-! ## Unconditional Theorem 13 and Corollary 14 -/
private lemma basin5_uncond_const_ge :
    (605 / 1000000 : ℝ) ≤
      (1 / ((80 : ℕ) : ℝ)) * (98959 / 1000000 : ℝ) * ((3 : ℝ) ^ ((65 : ℝ) / 100))⁻¹ := by
  have h3pow : (3 : ℝ) ^ ((65 : ℝ) / 100) ≤ 204248 / 100000 := by
    have h20 : ((3 : ℝ) ^ ((65 : ℝ) / 100)) ^ (20 : ℕ) ≤ (204248 / 100000 : ℝ) ^ (20 : ℕ) := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ ((65 : ℝ) / 100)) 20, ← Real.rpow_mul (by norm_num)]
      have hexp : ((65 : ℝ) / 100) * (20 : ℕ) = (13 : ℕ) := by norm_num
      rw [hexp, Real.rpow_natCast]; norm_num
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h20
  have hinv3 : (100000 / 204248 : ℝ) ≤ ((3 : ℝ) ^ ((65 : ℝ) / 100))⁻¹ := by
    have : (100000 / 204248 : ℝ) = (204248 / 100000 : ℝ)⁻¹ := by norm_num
    rw [this]; exact inv_anti₀ (by positivity) h3pow
  have hmul := mul_le_mul_of_nonneg_left hinv3
    (show (0 : ℝ) ≤ (1 / ((80 : ℕ) : ℝ)) * (98959 / 1000000 : ℝ) by norm_num)
  have hnum : (605 / 1000000 : ℝ) ≤
      (1 / ((80 : ℕ) : ℝ)) * (98959 / 1000000 : ℝ) * (100000 / 204248 : ℝ) := by norm_num
  linarith
/-- Unconditional sharper Theorem 13 (`N5(X) ≥ 6.05e-4 * X^{0.65}` for all `X ≥ 3`), verified 100% in Lean 4's -/
theorem thm_basin5_tight (X : ℕ) (hX : 3 ≤ X) : (605 / 1000000 : ℝ) * (X : ℝ) ^ ((65 : ℝ) / 100) ≤ (N5 X : ℝ) := by
  have htree := lemma_tree_weights_trunc
    h1575_dvd_14175 (by omega) (by omega) K_bound_80
    (by norm_num : (0 : ℝ) < 65 / 100) (by norm_num : (0 : ℝ) < 1)
    certW certW_nonneg certW_le_one certW_sub_eig
    3 X (by omega) (by decide) hX nonperiodic_three ⟨0, ⟨3, by decide⟩⟩ (by decide)
  have hsub : NTree 3 X ≤ N5 X := by
    classical
    unfold NTree N5
    refine Finset.card_le_card fun m hm => ?_
    simp only [Finset.mem_filter] at hm ⊢; exact ⟨hm.1, hm.2.1, reaches_trans hm.2.2 ⟨2, by decide⟩⟩
  have hdiv : ((X : ℝ) / (3 : ℝ)) ^ ((65 : ℝ) / 100) =
      ((3 : ℝ) ^ ((65 : ℝ) / 100))⁻¹ * (X : ℝ) ^ ((65 : ℝ) / 100) := by
    rw [Real.div_rpow (by positivity) (by norm_num), div_eq_inv_mul]
  rw [certW_root, mul_one] at htree; push_cast at htree; rw [hdiv] at htree
  have hstep : (605 / 1000000 : ℝ) * (X : ℝ) ^ ((65 : ℝ) / 100) ≤
      (1 / ((80 : ℕ) : ℝ)) * (98959 / 1000000 : ℝ) *
        (((3 : ℝ) ^ ((65 : ℝ) / 100))⁻¹ * (X : ℝ) ^ ((65 : ℝ) / 100)) := by
    have h1 := mul_le_mul_of_nonneg_right basin5_uncond_const_ge
      (show 0 ≤ (X : ℝ) ^ ((65 : ℝ) / 100) by positivity)
    linarith
  have htree' : (1 / ((80 : ℕ) : ℝ)) * (98959 / 1000000 : ℝ) *
      (((3 : ℝ) ^ ((65 : ℝ) / 100))⁻¹ * (X : ℝ) ^ ((65 : ℝ) / 100)) ≤ (NTree 3 X : ℝ) := by
    push_cast; exact htree
  exact (hstep.trans htree').trans (by exact_mod_cast hsub)
/-- Theorem 13 (Paper 1, completely unconditional in pure Lean 4 kernel): for every `X ≥ 3`, -/
theorem thm_basin5 (X : ℕ) (hX : 3 ≤ X) : (10766 / 100000000 : ℝ) * (X : ℝ) ^ ((65 : ℝ) / 100) ≤ (N5 X : ℝ) := by
  have h1 : (10766 / 100000000 : ℝ) * (X : ℝ) ^ ((65 : ℝ) / 100) ≤
      (605 / 1000000 : ℝ) * (X : ℝ) ^ ((65 : ℝ) / 100) :=
    mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  exact h1.trans (thm_basin5_tight X hX)
/-- Corollary 14 (odd starts, completely unconditional): `N1(X) / N5(X) ≤ (2.44 / 1.0766e-4) * X^{-0.0236}` for -/
theorem cor_basin_separation_unconditional (X : ℕ) (hX : 3 ≤ X) :
    (N1 X : ℝ) / (N5 X : ℝ) ≤
      ((244 / 100 : ℝ) / (10766 / 100000000 : ℝ)) * (X : ℝ) ^ (-(236 / 10000 : ℝ)) :=
  cor_basin_separation (by norm_num) thm_basin5 X hX
/-- Corollary 14 (all positive starts, completely unconditional): -/
theorem cor_basin_separation_all_unconditional (X : ℕ) (hX : 3 ≤ X) :
    (N1All X : ℝ) / (N5All X : ℝ) ≤
      ((693 / 100 : ℝ) / (10766 / 100000000 : ℝ)) * (X : ℝ) ^ (-(236 / 10000 : ℝ)) :=
  cor_basin_separation_all (by norm_num) thm_basin5 X hX
/-- Corollary 14 (completely unconditional decay to `0`): both `N1(X) / N5(X)` and `N1All(X) / N5All(X)` tend to -/
theorem cor_basin_separation_tendsto_zero_unconditional (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (N1 X : ℝ) / (N5 X : ℝ) ≤ ε ∧ (N1All X : ℝ) / (N5All X : ℝ) ≤ ε := by
  let κ : ℝ := 10766 / 100000000
  have hκ : 0 < κ := by norm_num
  let C : ℝ := (693 / 100 : ℝ) / κ
  have hC_pos : 0 < C := by positivity
  obtain ⟨X₀, hX₀⟩ := exists_nat_gt ((C / ε) ^ (50 : ℕ))
  refine ⟨max 3 X₀, fun X hX => ?_⟩
  have hX3 : 3 ≤ X := le_of_max_le_left hX
  have hXpos : (0 : ℝ) < (X : ℝ) := by positivity
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
  have hbound_odd := cor_basin_separation_unconditional X hX3
  have hbound_all := cor_basin_separation_all_unconditional X hX3
  have hpow : (X : ℝ) ^ (-(236 / 10000 : ℝ)) ≤ (X : ℝ) ^ (-(1 / 50 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hX50 : (C / ε) ^ (50 : ℕ) ≤ (X : ℝ) := le_trans hX₀.le (by exact_mod_cast le_of_max_le_right hX)
  have hq : C / ε ≤ (X : ℝ) ^ ((1 / 50 : ℝ)) := by
    have h50 : (C / ε) ^ (50 : ℕ) ≤ ((X : ℝ) ^ ((1 / 50 : ℝ))) ^ (50 : ℕ) := by
      rw [← Real.rpow_natCast ((X : ℝ) ^ ((1 / 50 : ℝ))) 50, ← Real.rpow_mul hXpos.le]
      have : ((1 / 50 : ℝ) * (50 : ℕ)) = 1 := by norm_num
      rw [this, Real.rpow_one]; exact hX50
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h50
  have hfinal : C * (X : ℝ) ^ (-(1 / 50 : ℝ)) ≤ ε := by
    rw [Real.rpow_neg hXpos.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have := (div_le_iff₀ hε).mp hq
    linarith
  have hodd_le_all : ((244 / 100 : ℝ) / κ) * (X : ℝ) ^ (-(236 / 10000 : ℝ)) ≤
      C * (X : ℝ) ^ (-(236 / 10000 : ℝ)) := by
    have : (244 / 100 : ℝ) / κ ≤ C := by unfold C; exact div_le_div_of_nonneg_right (by norm_num) hκ.le
    exact mul_le_mul_of_nonneg_right this (by positivity)
  exact ⟨hbound_odd.trans (hodd_le_all.trans ((mul_le_mul_of_nonneg_left hpow hC_pos.le).trans hfinal)),
         hbound_all.trans ((mul_le_mul_of_nonneg_left hpow hC_pos.le).trans hfinal)⟩

end Ouroboros
