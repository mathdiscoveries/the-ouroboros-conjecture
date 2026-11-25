module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Tactic
public import Ouroboros.Defs
public import Ouroboros.DensityDescent
public import Ouroboros.EvenBases
public import Ouroboros.EvenCoding

@[expose] public section

/-!
# Theorem 11 (`thm:even-stopping`): All-Even-Base Non-Descent Dichotomy

Formalizes Theorem 11 (`thm:even-stopping`) of the Ouroboros paper in pure-kernel Lean 4:
1. For every even base `b ≥ 2` and every horizon `k ≥ 1`, the finite-horizon non-descent set
   `D_k(b) = {n ≥ 1 : (T_b b)^[j] n ≥ n for 1 ≤ j ≤ k}` has an exact natural density `p_k(b)`
   (`p_k_density`), and `p_infty(b) = lim_{k → ∞} p_k(b)` exists (`p_k_tendsto_p_infty`).
2. `p_infty(b) = 0 ↔ b ∈ {2, 4, 6, 10}` (`p_infty_eq_zero_iff`).
3. For `b ∈ {2, 4, 6, 10}`, the set of positive integers eventually descending below their
   starting value under `f_b` has natural density `1` (`descent_density_one_of_mem`).
4. For every other even base `b ≥ 2` (`b ∉ {2, 4, 6, 10}`), there exists `η_b > 0` such that
   `p_k(b) ≥ η_b` for all `k ≥ 1` (`p_k_pos_lower_bound`).
5. Combined Theorem 11 (`thm_even_stopping`).
-/

namespace Ouroboros

open EvenBasesCert

/-! ## Section 1: Finite-horizon sets `D_k(b)`, exact densities `p_k(b)`, and `p_infty(b)` -/

/-- Finite-horizon non-descent set `D_k(b) = {n ≥ 1 : ∀ 1 ≤ j ≤ k, T_b^j(n) ≥ n}`. -/
def D_k (b k : ℕ) : Set ℕ :=
  {n | 1 ≤ n ∧ ∀ j, 1 ≤ j → j ≤ k → n ≤ (T_b b)^[j] n}

/-- Positive integers eventually descending strictly below their starting value under `f_b`. -/
def DescentSet (b : ℕ) : Set ℕ :=
  {n | 1 ≤ n ∧ ∃ m : ℕ, 1 ≤ m ∧ (f_b b)^[m] n < n}

/-- Positive integers never descending strictly below their starting value under `f_b`. -/
def NoDescentSet (b : ℕ) : Set ℕ :=
  {n | 1 ≤ n ∧ ∀ m : ℕ, 1 ≤ m → n ≤ (f_b b)^[m] n}

/-- Natural density `d(S) = lim_{N → ∞} |S ∩ [1, N]| / N`. -/
def HasNaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun N : ℕ => (countUpTo S N : ℝ) / (N : ℝ)) Filter.atTop (nhds d)

/-- Surviving residue classes modulo `N_k = b * 2^(k - 1)` for horizon `k ≥ 1`. -/
def SurvRes (b k : ℕ) : Finset (Fin (b * 2 ^ (k - 1))) :=
  Finset.univ.filter fun r => ∀ j : Fin k, 2 ^ (j.val + 1) < (affAB b r.val (j.val + 1)).1

/-- Exact finite-horizon non-descent density `p_k(b)`. -/
noncomputable def p_k (b k : ℕ) : ℝ :=
  ((SurvRes b k).card : ℝ) / ((b * 2 ^ (k - 1) : ℕ) : ℝ)

/-- Limiting non-descent density `p_infty(b) = lim_{k → ∞} p_k(b) = inf_{k ≥ 1} p_k(b)`. -/
noncomputable def p_infty (b : ℕ) : ℝ :=
  ⨅ k : ℕ, p_k b (k + 1)

private lemma countUpTo_eq_card (S : Set ℕ) (N : ℕ) [DecidablePred (· ∈ S)] :
    countUpTo S N = ((Finset.Icc 1 N).filter (fun n => n ∈ S)).card := by
  unfold countUpTo
  congr 1; ext n; simp

lemma p_k_nonneg (b k : ℕ) : 0 ≤ p_k b k := by
  unfold p_k; positivity

lemma p_k_le_one (b k : ℕ) : p_k b k ≤ 1 := by
  unfold p_k
  by_cases h0 : b * 2 ^ (k - 1) = 0
  · simp [h0]
  · have hpos : (0 : ℝ) < ((b * 2 ^ (k - 1) : ℕ) : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero h0)
    rw [div_le_one hpos]
    have hcard : (SurvRes b k).card ≤ b * 2 ^ (k - 1) := by
      simpa using Finset.card_le_univ (SurvRes b k)
    exact_mod_cast hcard

/-- Counting an eventually periodic set modulo `M ≥ 1` gives exact natural density `card / M`. -/
private lemma eventually_periodic_density {M B : ℕ} (hM : 0 < M) (R : Finset (Fin M))
    (S : Set ℕ) (hagree : ∀ n : ℕ, B < n → (n ∈ S ↔ ⟨n % M, Nat.mod_lt n hM⟩ ∈ R)) :
    HasNaturalDensity S ((R.card : ℝ) / (M : ℝ)) := by
  classical
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  let P : Set ℕ := {n | ⟨n % M, Nat.mod_lt n hM⟩ ∈ R}
  have hP_count : ∀ N : ℕ,
      R.card * (N / M) ≤ countUpTo P N ∧ countUpTo P N ≤ R.card * (N / M + 1) := by
    intro N
    rw [countUpTo_eq_card P N]
    set fP := (Finset.Icc 1 N).filter (fun n => n ∈ P)
    constructor
    · rw [← Finset.card_range (N / M), ← Finset.card_product]
      refine Finset.card_le_card_of_injOn
        (fun p : Fin M × ℕ => if p.1.val = 0 then (p.2 + 1) * M else p.2 * M + p.1.val) ?_ ?_
      · intro ⟨r, q⟩ hp
        simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp
        have hqM : (q + 1) * M ≤ N := by
          have : q + 1 ≤ N / M := hp.2
          exact (Nat.mul_le_mul_right M this).trans (Nat.div_mul_le_self N M)
        simp only [Finset.mem_coe, fP, Finset.mem_filter, Finset.mem_Icc, P, Set.mem_ofPred_eq]
        split_ifs with hr0
        · refine ⟨⟨by nlinarith, hqM⟩, ?_⟩
          have hmod : ((q + 1) * M) % M = 0 := Nat.mul_mod_left _ _
          have hfin : (⟨((q + 1) * M) % M, Nat.mod_lt _ hM⟩ : Fin M) = r :=
            Fin.ext (hmod.trans hr0.symm)
          rw [hfin]; exact hp.1
        · refine ⟨⟨by omega, by nlinarith [r.isLt]⟩, ?_⟩
          have hmod : (q * M + r.val) % M = r.val := by
            rw [Nat.mul_comm q M, Nat.mul_add_mod, Nat.mod_eq_of_lt r.isLt]
          have hfin : (⟨(q * M + r.val) % M, Nat.mod_lt _ hM⟩ : Fin M) = r := Fin.ext hmod
          rw [hfin]; exact hp.1
      · intro ⟨r1, q1⟩ _ ⟨r2, q2⟩ _ hEq
        dsimp only at hEq
        have hmod1 : (if r1.val = 0 then (q1 + 1) * M else q1 * M + r1.val) % M = r1.val := by
          split_ifs with h0
          · rw [Nat.mul_mod_left, h0]
          · rw [Nat.mul_comm q1 M, Nat.mul_add_mod, Nat.mod_eq_of_lt r1.isLt]
        have hmod2 : (if r2.val = 0 then (q2 + 1) * M else q2 * M + r2.val) % M = r2.val := by
          split_ifs with h0
          · rw [Nat.mul_mod_left, h0]
          · rw [Nat.mul_comm q2 M, Nat.mul_add_mod, Nat.mod_eq_of_lt r2.isLt]
        have hr_eq : r1 = r2 := Fin.ext (by rw [← hmod1, hEq, hmod2])
        subst hr_eq
        split_ifs at hEq with h0
        · have := Nat.eq_of_mul_eq_mul_right hM hEq
          exact Prod.ext rfl (by omega)
        · have : q1 * M = q2 * M := by omega
          exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_right hM this)
    · rw [← Finset.card_range (N / M + 1), ← Finset.card_product]
      refine Finset.card_le_card_of_injOn (fun n => (⟨n % M, Nat.mod_lt n hM⟩, n / M)) ?_ ?_
      · intro n hn
        simp only [Finset.mem_coe, fP, Finset.mem_filter, Finset.mem_Icc, P, Set.mem_ofPred_eq] at hn
        exact Finset.mem_coe.mpr (Finset.mem_product.mpr
          ⟨hn.2, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.2))⟩)
      · intro a _ b _ hEq
        have h1 : a % M = b % M := congr_arg (fun p => p.1.val) hEq
        have h2 : a / M = b / M := congr_arg Prod.snd hEq
        rw [← Nat.div_add_mod a M, ← Nat.div_add_mod b M, h1, h2]
  have hdiff : ∀ N : ℕ,
      countUpTo S N ≤ countUpTo P N + B ∧ countUpTo P N ≤ countUpTo S N + B := by
    intro N
    rw [countUpTo_eq_card S N, countUpTo_eq_card P N]
    set fS := (Finset.Icc 1 N).filter (fun n => n ∈ S)
    set fP := (Finset.Icc 1 N).filter (fun n => n ∈ P)
    have hsub1 : fS \ fP ⊆ Finset.Icc 1 B := by
      intro n hn
      simp only [Finset.mem_sdiff, fS, fP, Finset.mem_filter, Finset.mem_Icc, P,
        Set.mem_ofPred_eq] at hn
      refine Finset.mem_Icc.mpr ⟨hn.1.1.1, ?_⟩
      by_contra hgt
      have := (hagree n (by omega)).mp hn.1.2
      exact hn.2 ⟨hn.1.1, this⟩
    have hsub2 : fP \ fS ⊆ Finset.Icc 1 B := by
      intro n hn
      simp only [Finset.mem_sdiff, fS, fP, Finset.mem_filter, Finset.mem_Icc, P,
        Set.mem_ofPred_eq] at hn
      refine Finset.mem_Icc.mpr ⟨hn.1.1.1, ?_⟩
      by_contra hgt
      have := (hagree n (by omega)).mpr hn.1.2
      exact hn.2 ⟨hn.1.1, this⟩
    have hc1 : (fS \ fP).card ≤ B := (Finset.card_le_card hsub1).trans (by simp)
    have hc2 : (fP \ fS).card ≤ B := (Finset.card_le_card hsub2).trans (by simp)
    have h1 : fS.card ≤ fP.card + (fS \ fP).card := by
      have : fS ⊆ fP ∪ (fS \ fP) := fun x hx => by
        by_cases h : x ∈ fP <;> simp [hx, h]
      exact (Finset.card_le_card this).trans (Finset.card_union_le _ _)
    have h2 : fP.card ≤ fS.card + (fP \ fS).card := by
      have : fP ⊆ fS ∪ (fP \ fS) := fun x hx => by
        by_cases h : x ∈ fS <;> simp [hx, h]
      exact (Finset.card_le_card this).trans (Finset.card_union_le _ _)
    omega
  rw [HasNaturalDensity, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N0, hN0⟩ := exists_nat_gt (((R.card + B : ℕ) : ℝ) / ε)
  refine ⟨max 1 N0, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_left hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNgt : ((R.card + B : ℕ) : ℝ) / ε < (N : ℝ) :=
    lt_of_lt_of_le hN0 (by exact_mod_cast le_of_max_le_right hN)
  have herr : ((R.card + B : ℕ) : ℝ) / (N : ℝ) < ε := by
    rwa [div_lt_iff₀ hNpos, ← div_lt_iff₀' hε]
  obtain ⟨hPlo, hPhi⟩ := hP_count N
  obtain ⟨hSP, hPS⟩ := hdiff N
  have hdiv_le : ((N / M : ℕ) : ℝ) ≤ (N : ℝ) / (M : ℝ) := Nat.cast_div_le
  have hdiv_ge : (N : ℝ) / (M : ℝ) - 1 ≤ ((N / M : ℕ) : ℝ) := by
    have hnat : N < (N / M + 1) * M := by
      have := Nat.div_add_mod N M
      have := Nat.mod_lt N hM
      nlinarith
    have hR : (N : ℝ) < (((N / M : ℕ) : ℝ) + 1) * (M : ℝ) := by exact_mod_cast hnat
    rw [sub_le_iff_le_add, div_le_iff₀ hMpos]
    linarith
  have hS_hi : (countUpTo S N : ℝ) ≤ (R.card : ℝ) * ((N : ℝ) / (M : ℝ)) + ((R.card + B : ℕ) : ℝ) := by
    have h1 : (countUpTo S N : ℝ) ≤ (R.card : ℝ) * (((N / M : ℕ) : ℝ) + 1) + (B : ℝ) := by
      exact_mod_cast (hSP.trans (Nat.add_le_add_right hPhi B))
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) R.card]
  have hS_lo : (R.card : ℝ) * ((N : ℝ) / (M : ℝ)) - ((R.card + B : ℕ) : ℝ) ≤ (countUpTo S N : ℝ) := by
    have h1 : (R.card : ℝ) * ((N / M : ℕ) : ℝ) ≤ (countUpTo S N : ℝ) + (B : ℝ) := by
      exact_mod_cast (hPlo.trans hPS)
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) R.card]
  rw [Real.dist_eq, abs_lt]
  constructor
  · have h1 : (R.card : ℝ) / (M : ℝ) - ((R.card + B : ℕ) : ℝ) / (N : ℝ) ≤
        (countUpTo S N : ℝ) / (N : ℝ) := by
      rw [le_div_iff₀ hNpos, sub_mul, div_mul_cancel₀ _ (ne_of_gt hNpos)]
      have : (R.card : ℝ) / (M : ℝ) * (N : ℝ) = (R.card : ℝ) * ((N : ℝ) / (M : ℝ)) := by ring
      linarith
    linarith
  · have h1 : (countUpTo S N : ℝ) / (N : ℝ) ≤
        (R.card : ℝ) / (M : ℝ) + ((R.card + B : ℕ) : ℝ) / (N : ℝ) := by
      rw [div_le_iff₀ hNpos, add_mul, div_mul_cancel₀ _ (ne_of_gt hNpos)]
      have : (R.card : ℝ) / (M : ℝ) * (N : ℝ) = (R.card : ℝ) * ((N : ℝ) / (M : ℝ)) := by ring
      linarith
    linarith

/-- **Existence of `p_k(b)`**: for every even `b ≥ 2` and every `k ≥ 1`, `D_k(b)` has exact
    natural density `p_k b k`. -/
theorem p_k_density {b k : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) (hk : 1 ≤ k) :
    HasNaturalDensity (D_k b k) (p_k b k) := by
  have hMpos : 0 < b * 2 ^ (k - 1) := by positivity
  refine eventually_periodic_density (M := b * 2 ^ (k - 1)) (B := k * b ^ k) hMpos
    (SurvRes b k) (D_k b k) fun n hn => ?_
  have hmod : n % (b * 2 ^ (k - 1)) = (n % (b * 2 ^ (k - 1))) % (b * 2 ^ (k - 1)) :=
    (Nat.mod_mod _ _).symm
  have hcod := (lem_even_coding_mod hb2 hbeven hk hmod).1
  have hdich := lem_even_coding_class_dichotomy (b := b) (k := k) (n := n) hb2 hbeven hk
  simp only [D_k, Set.mem_ofPred_eq, SurvRes, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ⟨_, hstay⟩ j
    have hj1 : 1 ≤ j.val + 1 := by omega
    have hjk : j.val + 1 ≤ k := by omega
    rw [← hcod (j.val + 1) hjk]
    have haff := lem_even_affine hb2 hbeven n (j.val + 1)
    rcases hres : affAB b n (j.val + 1) with ⟨A, B⟩
    rw [hres] at haff
    have hne : A ≠ 2 ^ (j.val + 1) := haff.2.2.2 hj1
    by_contra hle
    have hlt : A < 2 ^ (j.val + 1) := by omega
    have hBle : B ≤ k * b ^ k := by
      have h1 : (j.val + 1) * b ^ (j.val + 1) ≤ k * b ^ k :=
        Nat.mul_le_mul hjk (Nat.pow_le_pow_right (by omega) hjk)
      exact haff.2.2.1.trans h1
    have hdrop : (T_b b)^[j.val + 1] n < n := by
      have hmul : 2 ^ (j.val + 1) * (T_b b)^[j.val + 1] n < 2 ^ (j.val + 1) * n := by
        rw [haff.1]
        have : A + 1 ≤ 2 ^ (j.val + 1) := by omega
        nlinarith
      exact Nat.lt_of_mul_lt_mul_left hmul
    exact absurd (hstay (j.val + 1) hj1 hjk) (not_le_of_gt hdrop)
  · intro hsurv
    refine ⟨by omega, hdich.1 fun j hj1 hjk => ?_⟩
    rw [hcod j hjk]
    have := hsurv ⟨j - 1, by omega⟩
    rwa [show j - 1 + 1 = j by omega] at this

/-- `p_k b` is antitone in `k ≥ 1`. -/
lemma p_k_antitone {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) :
    Antitone (fun k : ℕ => p_k b (k + 1)) := by
  refine antitone_nat_of_succ_le fun k => ?_
  have hd1 := p_k_density hb2 hbeven (k := k + 1) (by omega)
  have hd2 := p_k_density hb2 hbeven (k := k + 2) (by omega)
  have hle : ∀ N : ℕ, (countUpTo (D_k b (k + 2)) N : ℝ) / (N : ℝ) ≤
      (countUpTo (D_k b (k + 1)) N : ℝ) / (N : ℝ) := by
    intro N
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hsub : countUpTo (D_k b (k + 2)) N ≤ countUpTo (D_k b (k + 1)) N := by
      classical
      rw [countUpTo_eq_card, countUpTo_eq_card]
      refine Finset.card_le_card (Finset.subset_iff.mpr fun n hn => ?_)
      simp only [Finset.mem_filter] at hn ⊢
      simp only [D_k, Set.mem_ofPred_eq] at hn ⊢
      exact ⟨hn.1, hn.2.1, fun j hj1 hjk => hn.2.2 j hj1 (by omega)⟩
    exact_mod_cast hsub
  exact le_of_tendsto_of_tendsto hd2 hd1 (Filter.Eventually.of_forall hle)

/-- **Existence of `p_infty(b)`**: `p_k(b) → p_infty(b)` as `k → ∞`. -/
theorem p_k_tendsto_p_infty {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) :
    Filter.Tendsto (fun k : ℕ => p_k b (k + 1)) Filter.atTop (nhds (p_infty b)) := by
  apply tendsto_atTop_ciInf (p_k_antitone hb2 hbeven)
  exact ⟨0, by rintro _ ⟨k, rfl⟩; exact p_k_nonneg b (k + 1)⟩

lemma p_infty_le_p_k {b : ℕ} (_hb2 : 2 ≤ b) (_hbeven : b % 2 = 0) (k : ℕ) (hk : 1 ≤ k) :
    p_infty b ≤ p_k b k := by
  have hbdd : BddBelow (Set.range fun j : ℕ => p_k b (j + 1)) :=
    ⟨0, by rintro _ ⟨j, rfl⟩; exact p_k_nonneg b (j + 1)⟩
  have h1 := ciInf_le hbdd (k - 1)
  rwa [show k - 1 + 1 = k by omega] at h1

lemma p_infty_nonneg (b : ℕ) : 0 ≤ p_infty b := by
  unfold p_infty
  exact le_ciInf fun k => p_k_nonneg b (k + 1)

lemma T_b_eq_f_b_or_ff {b : ℕ} (hbeven : b % 2 = 0) (n : ℕ) :
    T_b b n = if n % 2 = 0 then f_b b n else f_b b (f_b b n) := by
  by_cases h : n % 2 = 0
  · simp [T_b, f_b, h]
  · have hodd : n % 2 = 1 := by omega
    have h2dvd : 2 ∣ b := Nat.dvd_of_mod_eq_zero hbeven
    have hdodd : (n % b) % 2 = 1 := by rw [Nat.mod_mod_of_dvd n h2dvd]; exact hodd
    have hfev : ((n % b) * n + 1) % 2 = 0 := by
      rw [Nat.add_mod, Nat.mul_mod, hdodd, hodd]
    simp only [T_b, f_b, h, ↓reduceIte, hfev]

lemma T_b_iter_is_f_b_iter {b : ℕ} (hbeven : b % 2 = 0) (j n : ℕ) :
    ∃ m : ℕ, j ≤ m ∧ (T_b b)^[j] n = (f_b b)^[m] n := by
  induction j generalizing n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨m, hjm, hm⟩ := ih (T_b b n)
    have hT := T_b_eq_f_b_or_ff hbeven n
    split_ifs at hT with h
    · refine ⟨m + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply, ← hT, hm]
    · refine ⟨m + 2, by omega, ?_⟩
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← hT, hm]

/-- If `p_infty(b) = 0`, then `DescentSet b` has natural density `1`. -/
lemma descent_density_one_of_p_infty_zero {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0)
    (h0 : p_infty b = 0) : HasNaturalDensity (DescentSet b) 1 := by
  have hNoZero : HasNaturalDensity (NoDescentSet b) 0 := by
    rw [HasNaturalDensity, Metric.tendsto_atTop]
    intro ε hε
    have htend := p_k_tendsto_p_infty hb2 hbeven
    rw [h0, Metric.tendsto_atTop] at htend
    obtain ⟨k0, hk0⟩ := htend (ε / 2) (by linarith)
    have hpk_lt : p_k b (k0 + 1) < ε / 2 := by
      have h := hk0 k0 le_rfl
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (p_k_nonneg b (k0 + 1))] at h
      exact h
    have hd := p_k_density hb2 hbeven (k := k0 + 1) (by omega)
    rw [HasNaturalDensity, Metric.tendsto_atTop] at hd
    obtain ⟨N0, hN0⟩ := hd (ε / 2) (by linarith)
    refine ⟨max 1 N0, fun N hN => ?_⟩
    have hN1 : 1 ≤ N := le_of_max_le_left hN
    have hsub : countUpTo (NoDescentSet b) N ≤ countUpTo (D_k b (k0 + 1)) N := by
      classical
      rw [countUpTo_eq_card, countUpTo_eq_card]
      refine Finset.card_le_card (Finset.subset_iff.mpr fun n hn => ?_)
      simp only [Finset.mem_filter] at hn ⊢
      simp only [NoDescentSet, D_k, Set.mem_ofPred_eq] at hn ⊢
      refine ⟨hn.1, hn.2.1, fun j hj1 _ => ?_⟩
      obtain ⟨m, hjm, hm⟩ := T_b_iter_is_f_b_iter hbeven j n
      rw [hm]
      exact hn.2.2 m (by omega)
    have hdiv : (countUpTo (NoDescentSet b) N : ℝ) / (N : ℝ) ≤
        (countUpTo (D_k b (k0 + 1)) N : ℝ) / (N : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hsub) (by positivity)
    have hclose := hN0 N (le_of_max_le_right hN)
    rw [Real.dist_eq, abs_lt] at hclose
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    linarith
  have hpart : ∀ N : ℕ, countUpTo (DescentSet b) N + countUpTo (NoDescentSet b) N = N := by
    intro N
    classical
    rw [countUpTo_eq_card, countUpTo_eq_card]
    have hcompl : (Finset.Icc 1 N).filter (fun n => n ∈ NoDescentSet b) =
        (Finset.Icc 1 N).filter (fun n => ¬ n ∈ DescentSet b) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc]
      simp only [NoDescentSet, DescentSet, Set.mem_ofPred_eq]
      constructor
      · intro ⟨hI, _, hall⟩
        refine ⟨hI, fun ⟨_, m, hm, hlt⟩ => absurd (hall m hm) (not_le_of_gt hlt)⟩
      · intro ⟨hI, hnot⟩
        refine ⟨hI, hI.1, fun m hm => ?_⟩
        by_contra hlt
        exact hnot ⟨hI.1, m, hm, by omega⟩
    rw [hcompl, Finset.card_filter_add_card_filter_not]
    simp
  rw [HasNaturalDensity, Metric.tendsto_atTop] at hNoZero ⊢
  intro ε hε
  obtain ⟨N0, hN0⟩ := hNoZero ε hε
  refine ⟨max 1 N0, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_left hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsum : (countUpTo (DescentSet b) N : ℝ) / (N : ℝ) +
      (countUpTo (NoDescentSet b) N : ℝ) / (N : ℝ) = 1 := by
    rw [← add_div, show (countUpTo (DescentSet b) N : ℝ) + (countUpTo (NoDescentSet b) N : ℝ) =
      (N : ℝ) by exact_mod_cast hpart N, div_self (ne_of_gt hNpos)]
  have hclose := hN0 N (le_of_max_le_right hN)
  rw [Real.dist_eq, sub_zero] at hclose
  rw [Real.dist_eq]
  have : (countUpTo (DescentSet b) N : ℝ) / (N : ℝ) - 1 =
      -((countUpTo (NoDescentSet b) N : ℝ) / (N : ℝ)) := by linarith
  rw [this, abs_neg]
  exact hclose

/-! ## Section 2: Exact Markov coding bridges for `b = 2M` and `b = 4k` -/

lemma affAB_succ_fst (b n j : ℕ) :
    (affAB b n (j + 1)).1 = (if n % 2 = 0 then 1 else n % b) * (affAB b (T_b b n) j).1 := by
  induction j with
  | zero =>
    change (if n % 2 = 0 then (1, 0) else ((n % b) * 1, (n % b) * 0 + 1)).1 =
      (if n % 2 = 0 then 1 else n % b) * 1
    split_ifs <;> simp
  | succ j ih =>
    have hstep : affAB b n (j + 2) =
        let prev := affAB b n (j + 1)
        let cur := (T_b b)^[j + 1] n
        if cur % 2 = 0 then (prev.1, prev.2)
        else ((cur % b) * prev.1, (cur % b) * prev.2 + 2 ^ (j + 1)) := rfl
    have hstep' : affAB b (T_b b n) (j + 1) =
        let prev := affAB b (T_b b n) j
        let cur := (T_b b)^[j] (T_b b n)
        if cur % 2 = 0 then (prev.1, prev.2)
        else ((cur % b) * prev.1, (cur % b) * prev.2 + 2 ^ j) := rfl
    rw [hstep, hstep']
    dsimp only
    rw [Function.iterate_succ_apply]
    by_cases hc : ((T_b b)^[j] (T_b b n)) % 2 = 0
    · simp only [hc, ↓reduceIte]; exact ih
    · simp only [hc, ↓reduceIte]; rw [ih]; ring

/-- Finite-horizon survival probability for the 2-branch shortcut chain `K_M` (`b = 2M`, `M` odd). -/
noncomputable def surviveProb2M (M : ℕ) (hM : 1 ≤ M) : ℕ → Fin M → ℝ → ℝ
  | 0, _, _ => 1
  | n + 1, y, prod =>
    (1 / 2 : ℝ) * (if 1 < prod * (1 / 2 : ℝ) then
        surviveProb2M M hM n (hStep2M M hM y) (prod * (1 / 2 : ℝ)) else 0) +
    (1 / 2 : ℝ) * (if 1 < prod * ((oddDigit2M M y : ℝ) / 2) then
        surviveProb2M M hM n (qStep2M M hM y) (prod * ((oddDigit2M M y : ℝ) / 2)) else 0)

/-- Finite-horizon ruin probability for the 2-branch shortcut chain `K_M` (`b = 2M`, `M` odd). -/
noncomputable def ruinProb2M (M : ℕ) (hM : 1 ≤ M) : ℕ → Fin M → ℝ → ℝ
  | 0, _, _ => 0
  | n + 1, y, rho =>
    (1 / 2 : ℝ) * (if (1 / 2 : ℝ) ≤ rho then 1 else
        ruinProb2M M hM n (hStep2M M hM y) (2 * rho)) +
    (1 / 2 : ℝ) * (if ((oddDigit2M M y : ℝ) / 2) ≤ rho then 1 else
        ruinProb2M M hM n (qStep2M M hM y) (2 * rho / (oddDigit2M M y : ℝ)))

lemma surviveProb2M_nonneg {M : ℕ} (hM : 1 ≤ M) :
    ∀ n y prod, 0 ≤ surviveProb2M M hM n y prod := by
  intro n
  induction n with
  | zero => intro _ _; simp [surviveProb2M]
  | succ n ih =>
    intro y prod
    unfold surviveProb2M
    apply add_nonneg <;> apply mul_nonneg (by norm_num) <;> split_ifs
    all_goals first | exact ih _ _ | exact le_rfl

lemma surviveProb2M_add_ruinProb2M {M : ℕ} (hM : 1 ≤ M) (hModd : M % 2 = 1) :
    ∀ n y (prod : ℝ), 0 < prod →
      surviveProb2M M hM n y prod + ruinProb2M M hM n y (1 / prod) = 1 := by
  intro n
  induction n with
  | zero => intro _ _ _; simp [surviveProb2M, ruinProb2M]
  | succ n ih =>
    intro y prod hprod
    unfold surviveProb2M ruinProb2M
    have hdpos : (0 : ℝ) < (oddDigit2M M y : ℝ) := by
      have : 1 ≤ oddDigit2M M y := by
        unfold oddDigit2M oddDigitNat
        by_cases h1 : y.val % 2 = 1
        · simp [h1]; omega
        · have hbeq : Nat.beq (y.val % 2) 1 = false := by
            cases hb : Nat.beq (y.val % 2) 1 with
            | false => rfl
            | true => exact absurd (Nat.eq_of_beq_eq_true hb) h1
          simp [hbeq]; omega
      exact_mod_cast this
    have h1 : (1 / 2 : ℝ) * (if 1 < prod * (1 / 2 : ℝ) then
        surviveProb2M M hM n (hStep2M M hM y) (prod * (1 / 2 : ℝ)) else 0) +
      (1 / 2 : ℝ) * (if (1 / 2 : ℝ) ≤ 1 / prod then 1 else
        ruinProb2M M hM n (hStep2M M hM y) (2 * (1 / prod))) = 1 / 2 := by
      have hiff : 1 < prod * (1 / 2 : ℝ) ↔ ¬ (1 / 2 : ℝ) ≤ 1 / prod := by
        rw [le_div_iff₀ hprod, mul_comm]; exact not_le.symm
      by_cases hgt : 1 < prod * (1 / 2 : ℝ)
      · have hnot : ¬ (1 / 2 : ℝ) ≤ 1 / prod := hiff.mp hgt
        simp only [hgt, hnot, ↓reduceIte]
        have harg : 2 * (1 / prod) = 1 / (prod * (1 / 2 : ℝ)) := by field_simp
        rw [harg, ← mul_add, ih _ _ (by positivity), mul_one]
      · have hle : (1 / 2 : ℝ) ≤ 1 / prod := not_not.mp (mt hiff.mpr hgt)
        simp only [hgt, hle, ↓reduceIte]; ring
    have h2 : (1 / 2 : ℝ) * (if 1 < prod * ((oddDigit2M M y : ℝ) / 2) then
        surviveProb2M M hM n (qStep2M M hM y) (prod * ((oddDigit2M M y : ℝ) / 2)) else 0) +
      (1 / 2 : ℝ) * (if ((oddDigit2M M y : ℝ) / 2) ≤ 1 / prod then 1 else
        ruinProb2M M hM n (qStep2M M hM y) (2 * (1 / prod) / (oddDigit2M M y : ℝ))) = 1 / 2 := by
      have hiff : 1 < prod * ((oddDigit2M M y : ℝ) / 2) ↔ ¬ ((oddDigit2M M y : ℝ) / 2) ≤ 1 / prod := by
        rw [le_div_iff₀ hprod, mul_comm]; exact not_le.symm
      by_cases hgt : 1 < prod * ((oddDigit2M M y : ℝ) / 2)
      · have hnot : ¬ ((oddDigit2M M y : ℝ) / 2) ≤ 1 / prod := hiff.mp hgt
        simp only [hgt, hnot, ↓reduceIte]
        have harg : 2 * (1 / prod) / (oddDigit2M M y : ℝ) =
            1 / (prod * ((oddDigit2M M y : ℝ) / 2)) := by field_simp
        rw [harg, ← mul_add, ih _ _ (by positivity), mul_one]
      · have hle : ((oddDigit2M M y : ℝ) / 2) ≤ 1 / prod := not_not.mp (mt hiff.mpr hgt)
        simp only [hgt, hle, ↓reduceIte]; ring
    linarith

/-- Decay certificate for `K_M`: if `2^(-t-1) * (w(H y) + d(y)^t * w(Q y)) ≤ λ * w(y)` with
    `w ≥ wmin > 0`, `t > 0`, `λ > 0`, then `surviveProb2M n y 1 ≤ (w y / wmin) * λ^n`. -/
lemma prop_decay_2M {M : ℕ} (hM : 1 ≤ M) {t lam wmin : ℝ} (ht : 0 < t) (hlam : 0 < lam)
    (hwmin : 0 < wmin) {w : Fin M → ℝ} (hw : ∀ y, wmin ≤ w y)
    (hsub : ∀ y : Fin M,
      (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ t * w (hStep2M M hM y) +
        ((oddDigit2M M y : ℝ) / 2) ^ t * w (qStep2M M hM y)) ≤ lam * w y) :
    ∀ n y (prod : ℝ), 1 ≤ prod →
      surviveProb2M M hM n y prod * wmin ≤ prod ^ t * lam ^ n * w y := by
  intro n
  induction n with
  | zero =>
    intro y prod hprod
    simp only [surviveProb2M, one_mul, pow_zero, mul_one]
    have h1 : 1 ≤ prod ^ t := Real.one_le_rpow hprod ht.le
    have hw_nn : 0 ≤ w y := by linarith [hw y]
    calc wmin ≤ 1 * w y := by linarith [hw y]
      _ ≤ prod ^ t * w y := mul_le_mul_of_nonneg_right h1 hw_nn
  | succ n ih =>
    intro y prod hprod
    unfold surviveProb2M
    have hprod_nn : 0 ≤ prod := by linarith
    have hd_nn : (0 : ℝ) ≤ (oddDigit2M M y : ℝ) / 2 := by positivity
    have hbr1 : (if 1 < prod * (1 / 2 : ℝ) then
        surviveProb2M M hM n (hStep2M M hM y) (prod * (1 / 2 : ℝ)) else 0) * wmin ≤
        prod ^ t * lam ^ n * ((1 / 2 : ℝ) ^ t * w (hStep2M M hM y)) := by
      split_ifs with hgt
      · calc surviveProb2M M hM n (hStep2M M hM y) (prod * (1 / 2 : ℝ)) * wmin
            ≤ (prod * (1 / 2 : ℝ)) ^ t * lam ^ n * w (hStep2M M hM y) := ih _ _ hgt.le
          _ = prod ^ t * lam ^ n * ((1 / 2 : ℝ) ^ t * w (hStep2M M hM y)) := by
              rw [Real.mul_rpow hprod_nn (by norm_num)]; ring
      · rw [zero_mul]
        have : 0 ≤ w (hStep2M M hM y) := by linarith [hw (hStep2M M hM y)]
        positivity
    have hbr2 : (if 1 < prod * ((oddDigit2M M y : ℝ) / 2) then
        surviveProb2M M hM n (qStep2M M hM y) (prod * ((oddDigit2M M y : ℝ) / 2)) else 0) * wmin ≤
        prod ^ t * lam ^ n * (((oddDigit2M M y : ℝ) / 2) ^ t * w (qStep2M M hM y)) := by
      split_ifs with hgt
      · calc surviveProb2M M hM n (qStep2M M hM y) (prod * ((oddDigit2M M y : ℝ) / 2)) * wmin
            ≤ (prod * ((oddDigit2M M y : ℝ) / 2)) ^ t * lam ^ n * w (qStep2M M hM y) :=
              ih _ _ hgt.le
          _ = prod ^ t * lam ^ n * (((oddDigit2M M y : ℝ) / 2) ^ t * w (qStep2M M hM y)) := by
              rw [Real.mul_rpow hprod_nn hd_nn]; ring
      · rw [zero_mul]
        have : 0 ≤ w (qStep2M M hM y) := by linarith [hw (qStep2M M hM y)]
        positivity
    calc ((1 / 2 : ℝ) * (if 1 < prod * (1 / 2 : ℝ) then
            surviveProb2M M hM n (hStep2M M hM y) (prod * (1 / 2 : ℝ)) else 0) +
          (1 / 2 : ℝ) * (if 1 < prod * ((oddDigit2M M y : ℝ) / 2) then
            surviveProb2M M hM n (qStep2M M hM y) (prod * ((oddDigit2M M y : ℝ) / 2)) else 0)) * wmin
        ≤ prod ^ t * lam ^ n * ((1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ t * w (hStep2M M hM y) +
            ((oddDigit2M M y : ℝ) / 2) ^ t * w (qStep2M M hM y))) := by linarith
      _ ≤ prod ^ t * lam ^ n * (lam * w y) :=
          mul_le_mul_of_nonneg_left (hsub y) (by positivity)
      _ = prod ^ t * lam ^ (n + 1) * w y := by rw [pow_succ]; ring

/-- Supermartingale ruin bound for `K_M`: if `2^(t - 1) * (w(H y) + d(y)^(-t) * w(Q y)) ≤ w y`
    with `w ≥ wmin > 0` and `t > 0`, then `ruinProb2M n y rho ≤ rho^t * w y / wmin`. -/
lemma prop_survival_2M {M : ℕ} (hM : 1 ≤ M) (hModd : M % 2 = 1) {t wmin : ℝ}
    (ht : 0 < t) (hwmin : 0 < wmin) {w : Fin M → ℝ} (hw : ∀ y, wmin ≤ w y)
    (hsub : ∀ y : Fin M,
      (2 : ℝ) ^ (t - 1) * (w (hStep2M M hM y) +
        (oddDigit2M M y : ℝ) ^ (-t) * w (qStep2M M hM y)) ≤ w y) :
    ∀ n y (rho : ℝ), 0 < rho → ruinProb2M M hM n y rho ≤ rho ^ t * w y / wmin := by
  have hdpos : ∀ y : Fin M, (0 : ℝ) < (oddDigit2M M y : ℝ) := fun y => by
    have : 1 ≤ oddDigit2M M y := by
      unfold oddDigit2M oddDigitNat
      by_cases h1 : y.val % 2 = 1
      · simp [h1]; omega
      · have hbeq : Nat.beq (y.val % 2) 1 = false := by
          cases hb : Nat.beq (y.val % 2) 1 with
          | false => rfl
          | true => exact absurd (Nat.eq_of_beq_eq_true hb) h1
        simp [hbeq]; omega
    exact_mod_cast this
  intro n
  induction n with
  | zero =>
    intro y rho hrho
    simp only [ruinProb2M]
    have : 0 ≤ w y := by linarith [hw y]
    positivity
  | succ n ih =>
    intro y rho hrho
    unfold ruinProb2M
    have h2t : (1 / 2 : ℝ) * (2 : ℝ) ^ t = (2 : ℝ) ^ (t - 1) := by
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_neg_one]; ring
    have hbr1 : (if (1 / 2 : ℝ) ≤ rho then (1 : ℝ) else
        ruinProb2M M hM n (hStep2M M hM y) (2 * rho)) ≤
        (2 : ℝ) ^ t * rho ^ t * w (hStep2M M hM y) / wmin := by
      split_ifs with hle
      · rw [le_div_iff₀ hwmin, one_mul]
        have h2r : 1 ≤ 2 * rho := by linarith
        have hpow : 1 ≤ (2 * rho) ^ t := Real.one_le_rpow h2r ht.le
        rw [Real.mul_rpow (by norm_num) hrho.le] at hpow
        have hwH : wmin ≤ w (hStep2M M hM y) := hw _
        have : 0 ≤ w (hStep2M M hM y) := by linarith
        nlinarith
      · calc ruinProb2M M hM n (hStep2M M hM y) (2 * rho)
            ≤ (2 * rho) ^ t * w (hStep2M M hM y) / wmin := ih _ _ (by positivity)
          _ = (2 : ℝ) ^ t * rho ^ t * w (hStep2M M hM y) / wmin := by
              rw [Real.mul_rpow (by norm_num) hrho.le]
    have hbr2 : (if ((oddDigit2M M y : ℝ) / 2) ≤ rho then (1 : ℝ) else
        ruinProb2M M hM n (qStep2M M hM y) (2 * rho / (oddDigit2M M y : ℝ))) ≤
        (2 : ℝ) ^ t * rho ^ t * ((oddDigit2M M y : ℝ) ^ (-t) * w (qStep2M M hM y)) / wmin := by
      have hd := hdpos y
      split_ifs with hle
      · rw [le_div_iff₀ hwmin, one_mul]
        have hge1 : 1 ≤ 2 * rho / (oddDigit2M M y : ℝ) := by
          rw [one_le_div hd]; linarith
        have hpow : 1 ≤ (2 * rho / (oddDigit2M M y : ℝ)) ^ t := Real.one_le_rpow hge1 ht.le
        rw [Real.div_rpow (by positivity) hd.le, Real.mul_rpow (by norm_num) hrho.le,
            div_eq_mul_inv, ← Real.rpow_neg hd.le] at hpow
        have hwQ : wmin ≤ w (qStep2M M hM y) := hw _
        have : 0 ≤ w (qStep2M M hM y) := by linarith
        calc wmin ≤ 1 * w (qStep2M M hM y) := by linarith
          _ ≤ ((2 : ℝ) ^ t * rho ^ t * (oddDigit2M M y : ℝ) ^ (-t)) * w (qStep2M M hM y) :=
              mul_le_mul_of_nonneg_right hpow this
          _ = (2 : ℝ) ^ t * rho ^ t * ((oddDigit2M M y : ℝ) ^ (-t) * w (qStep2M M hM y)) := by ring
      · calc ruinProb2M M hM n (qStep2M M hM y) (2 * rho / (oddDigit2M M y : ℝ))
            ≤ (2 * rho / (oddDigit2M M y : ℝ)) ^ t * w (qStep2M M hM y) / wmin :=
              ih _ _ (by positivity)
          _ = (2 : ℝ) ^ t * rho ^ t * ((oddDigit2M M y : ℝ) ^ (-t) * w (qStep2M M hM y)) / wmin := by
              rw [Real.div_rpow (by positivity) hd.le, Real.mul_rpow (by norm_num) hrho.le,
                  Real.rpow_neg hd.le]
              field_simp
    calc (1 / 2 : ℝ) * (if (1 / 2 : ℝ) ≤ rho then 1 else
            ruinProb2M M hM n (hStep2M M hM y) (2 * rho)) +
          (1 / 2 : ℝ) * (if ((oddDigit2M M y : ℝ) / 2) ≤ rho then 1 else
            ruinProb2M M hM n (qStep2M M hM y) (2 * rho / (oddDigit2M M y : ℝ)))
        ≤ (1 / 2 : ℝ) * ((2 : ℝ) ^ t * rho ^ t * w (hStep2M M hM y) / wmin) +
          (1 / 2 : ℝ) * ((2 : ℝ) ^ t * rho ^ t *
            ((oddDigit2M M y : ℝ) ^ (-t) * w (qStep2M M hM y)) / wmin) := by linarith
      _ = rho ^ t * ((2 : ℝ) ^ (t - 1) * (w (hStep2M M hM y) +
            (oddDigit2M M y : ℝ) ^ (-t) * w (qStep2M M hM y))) / wmin := by
          rw [← h2t]; ring
      _ ≤ rho ^ t * w y / wmin :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hsub y) (by positivity)) hwmin.le

/-- Path-level survival indicator for `K_M`. -/
private noncomputable def path2MSurv (M : ℕ) (hM : 1 ≤ M) :
    ∀ k : ℕ, Fin M → (Fin k → Bool) → ℝ → Bool
  | 0, _, _, _ => true
  | k + 1, y, e, prod =>
    let mult : ℝ := if e 0 then (oddDigit2M M y : ℝ) / 2 else 1 / 2
    let y' : Fin M := if e 0 then qStep2M M hM y else hStep2M M hM y
    by classical exact decide (1 < prod * mult) && path2MSurv M hM k y' (fun j => e j.succ) (prod * mult)

private lemma surviveProb2M_eq_path_sum {M : ℕ} (hM : 1 ≤ M) :
    ∀ k y prod, surviveProb2M M hM k y prod =
      (1 / (2 : ℝ) ^ k) * ∑ e : Fin k → Bool, if path2MSurv M hM k y e prod then (1 : ℝ) else 0 := by
  intro k
  induction k with
  | zero =>
    intro y prod
    simp [surviveProb2M, path2MSurv]
  | succ k ih =>
    intro y prod
    let eqv : (Fin (k + 1) → Bool) ≃ Bool × (Fin k → Bool) :=
      { toFun := fun e => (e 0, fun j => e j.succ)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := fun e => by funext j; refine Fin.cases rfl (fun i => rfl) j
        right_inv := fun ⟨b, f⟩ => by ext <;> simp }
    have hsum : (∑ e : Fin (k + 1) → Bool, if path2MSurv M hM (k + 1) y e prod then (1 : ℝ) else 0) =
        (∑ e : Fin k → Bool, if path2MSurv M hM (k + 1) y (Fin.cons false e) prod then (1 : ℝ) else 0) +
        (∑ e : Fin k → Bool, if path2MSurv M hM (k + 1) y (Fin.cons true e) prod then (1 : ℝ) else 0) := by
      rw [← Equiv.sum_comp eqv.symm, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
      rfl
    rw [hsum]
    unfold surviveProb2M
    have hfalse : (1 / (2 : ℝ) ^ k) *
        (∑ e : Fin k → Bool, if path2MSurv M hM (k + 1) y (Fin.cons false e) prod then (1 : ℝ) else 0) =
        if 1 < prod * (1 / 2 : ℝ) then
          surviveProb2M M hM k (hStep2M M hM y) (prod * (1 / 2 : ℝ)) else 0 := by
      simp only [path2MSurv, Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ↓reduceIte]
      by_cases hgt : 1 < prod * (1 / 2 : ℝ)
      · simp only [hgt, decide_true, Bool.true_and, ↓reduceIte]
        exact (ih (hStep2M M hM y) (prod * (1 / 2 : ℝ))).symm
      · simp only [hgt, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          Finset.sum_const_zero, mul_zero]
    have htrue : (1 / (2 : ℝ) ^ k) *
        (∑ e : Fin k → Bool, if path2MSurv M hM (k + 1) y (Fin.cons true e) prod then (1 : ℝ) else 0) =
        if 1 < prod * ((oddDigit2M M y : ℝ) / 2) then
          surviveProb2M M hM k (qStep2M M hM y) (prod * ((oddDigit2M M y : ℝ) / 2)) else 0 := by
      simp only [path2MSurv, Fin.cons_zero, Fin.cons_succ, ↓reduceIte]
      by_cases hgt : 1 < prod * ((oddDigit2M M y : ℝ) / 2)
      · simp only [hgt, decide_true, Bool.true_and, ↓reduceIte]
        exact (ih (qStep2M M hM y) (prod * ((oddDigit2M M y : ℝ) / 2))).symm
      · simp only [hgt, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          Finset.sum_const_zero, mul_zero]
    rw [← hfalse, ← htrue, pow_succ]
    ring

private lemma mod_two_mul_eq_oddDigit2M {M : ℕ} (hM : 1 ≤ M) (hModd : M % 2 = 1) {n : ℕ}
    (hodd : n % 2 = 1) :
    n % (2 * M) = oddDigit2M M ⟨n % M, Nat.mod_lt n (by omega)⟩ := by
  unfold oddDigit2M oddDigitNat
  set r := n % (2 * M)
  have hrlt : r < 2 * M := Nat.mod_lt n (by omega)
  have hrodd : r % 2 = 1 := by
    have : r % 2 = n % 2 := Nat.mod_mod_of_dvd n (dvd_mul_right 2 M)
    omega
  have hrmodM : r % M = n % M := Nat.mod_mod_of_dvd n (dvd_mul_left M 2)
  have hrdiv := Nat.div_add_mod r M
  have hqle : r / M ≤ 1 := by
    have hmul : M * (r / M) ≤ r := Nat.mul_div_le r M
    nlinarith
  have hrcases : r = n % M ∨ r = n % M + M := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hqle with h0 | h1
    · left; rw [h0, mul_zero, zero_add] at hrdiv; omega
    · right; rw [h1, mul_one] at hrdiv; omega
  by_cases h1 : (n % M) % 2 = 1
  · simp [h1]
    rcases hrcases with heq | heq
    · exact heq
    · omega
  · have hbeq : Nat.beq (n % M % 2) 1 = false := by
      cases hb : Nat.beq (n % M % 2) 1 with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true hb) h1
    simp only [hbeq]
    rcases hrcases with heq | heq
    · omega
    · exact heq

private lemma T_2M_mod_M {M : ℕ} (hM : 1 ≤ M) (hModd : M % 2 = 1) (n : ℕ) :
    (⟨T_b (2 * M) n % M, Nat.mod_lt _ (by omega)⟩ : Fin M) =
      if n % 2 = 1 then qStep2M M hM ⟨n % M, Nat.mod_lt n (by omega)⟩
      else hStep2M M hM ⟨n % M, Nat.mod_lt n (by omega)⟩ := by
  ext
  by_cases hodd : n % 2 = 1
  · simp only [hodd, ↓reduceIte, qStep2M, qStepNat, oddDigitNat]
    have hd_eq : n % (2 * M) = oddDigit2M M ⟨n % M, Nat.mod_lt n (by omega)⟩ :=
      mod_two_mul_eq_oddDigit2M hM hModd hodd
    rw [T_b_odd hodd, hd_eq]
    set d0 := oddDigit2M M ⟨n % M, Nat.mod_lt n (by omega)⟩
    have h2M : n % (2 * M) = d0 := hd_eq
    have hd_odd : d0 % 2 = 1 := by
      rw [← h2M, Nat.mod_mod_of_dvd n (dvd_mul_right 2 M)]; exact hodd
    have hdiff : 2 * M ∣ (d0 * n + 1) - (d0 * d0 + 1) := by
      have hdiv := Nat.div_add_mod n (2 * M)
      refine ⟨d0 * (n / (2 * M)), ?_⟩
      have hle : d0 ≤ n := by rw [← h2M]; exact Nat.mod_le n (2 * M)
      have : d0 * n = d0 * (2 * M * (n / (2 * M)) + d0) := by rw [← h2M, hdiv]
      have : d0 * n - d0 * d0 = 2 * M * (d0 * (n / (2 * M))) := by
        rw [this]; ring_nf; omega
      omega
    obtain ⟨q, hq⟩ := hdiff
    have hle : d0 * d0 + 1 ≤ d0 * n + 1 := by
      have : d0 ≤ n := by rw [← h2M]; exact Nat.mod_le n (2 * M)
      nlinarith
    have heq : (d0 * n + 1) / 2 = (d0 * d0 + 1) / 2 + M * q := by
      have hq' : (d0 * n + 1) - (d0 * d0 + 1) = 2 * (M * q) := by rw [hq]; ring
      have h1 : d0 * n + 1 = (d0 * d0 + 1) + 2 * (M * q) := by omega
      rw [h1, Nat.add_mul_div_left _ _ zero_lt_two]
    rw [heq, Nat.add_mul_mod_self_left]
    rfl
  · have hev : n % 2 = 0 := by omega
    simp only [hodd, ↓reduceIte, hStep2M, hStepNat]
    rw [T_b_even hev]
    have h2mul : (2 * ((M + 1) / 2)) % M = 1 % M := by
      have : 2 * ((M + 1) / 2) = M + 1 := by omega
      rw [this, Nat.add_mod_left]
    have h1 : (n / 2) % M = ((n / 2) * (2 * ((M + 1) / 2))) % M := by
      rw [Nat.mul_mod, h2mul, ← Nat.mul_mod, mul_one]
    rw [h1]
    have h2 : (n / 2) * (2 * ((M + 1) / 2)) = n * ((M + 1) / 2) := by
      rw [← mul_assoc, mul_comm (n / 2) 2, show 2 * (n / 2) = n by omega]
    rw [h2]
    exact (Nat.mod_mul_mod n ((M + 1) / 2) M).symm

private lemma path2MSurv_iff_affAB {M : ℕ} (hM : 1 ≤ M) (hModd : M % 2 = 1) :
    ∀ (k n : ℕ) (prod : ℝ), 0 < prod →
      (path2MSurv M hM k ⟨n % M, Nat.mod_lt n (by omega)⟩
        (fun j : Fin k => ((T_b (2 * M))^[j.val] n % 2 == 1)) prod = true ↔
        ∀ j, 1 ≤ j → j ≤ k → 1 < prod * ((affAB (2 * M) n j).1 : ℝ) / (2 : ℝ) ^ j) := by
  intro k
  induction k with
  | zero =>
    intro n prod _
    simp only [path2MSurv, true_iff]
    intro j hj1 hj0; omega
  | succ k ih =>
    intro n prod hprod
    have hodd_d : n % 2 = 1 → n % (2 * M) = oddDigit2M M ⟨n % M, Nat.mod_lt n (by omega)⟩ :=
      mod_two_mul_eq_oddDigit2M hM hModd
    unfold path2MSurv
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    change (1 < prod * (if ((n % 2 == 1) = true) then
        (oddDigit2M M ⟨n % M, Nat.mod_lt n (by omega)⟩ : ℝ) / 2 else (1 / 2 : ℝ))) ∧
      path2MSurv M hM k
        (if ((n % 2 == 1) = true) then qStep2M M hM ⟨n % M, Nat.mod_lt n (by omega)⟩
         else hStep2M M hM ⟨n % M, Nat.mod_lt n (by omega)⟩)
        (fun j : Fin k => ((T_b (2 * M))^[j.succ.val] n % 2 == 1))
        (prod * (if ((n % 2 == 1) = true) then
          (oddDigit2M M ⟨n % M, Nat.mod_lt n (by omega)⟩ : ℝ) / 2 else (1 / 2 : ℝ))) = true ↔ _
    have hmult_eq : (if ((n % 2 == 1) = true) then (oddDigit2M M ⟨n % M, Nat.mod_lt n (by omega)⟩ : ℝ) / 2
        else (1 / 2 : ℝ)) = ((if n % 2 = 0 then 1 else n % (2 * M) : ℕ) : ℝ) / 2 := by
      by_cases hodd : n % 2 = 1
      · simp [hodd, hodd_d hodd]
      · have hev : n % 2 = 0 := by omega
        simp [hev]
    have hy'_eq : (if ((n % 2 == 1) = true) then qStep2M M hM ⟨n % M, Nat.mod_lt n (by omega)⟩
        else hStep2M M hM ⟨n % M, Nat.mod_lt n (by omega)⟩) =
        ⟨T_b (2 * M) n % M, Nat.mod_lt _ (by omega)⟩ := by
      rw [T_2M_mod_M hM hModd n]
      by_cases hodd : n % 2 = 1 <;> simp [hodd]
    have hshift : (fun j : Fin k => ((T_b (2 * M))^[j.succ.val] n % 2 == 1)) =
        (fun j : Fin k => ((T_b (2 * M))^[j.val] (T_b (2 * M) n) % 2 == 1)) := by
      funext j; simp [Function.iterate_succ_apply]
    have hmult_pos : 0 < ((if n % 2 = 0 then 1 else n % (2 * M) : ℕ) : ℝ) / 2 := by
      by_cases hodd : n % 2 = 1
      · have hne : n % 2 ≠ 0 := by omega
        have hdpos : 1 ≤ n % (2 * M) := by
          have : (n % (2 * M)) % 2 = 1 := by
            rw [Nat.mod_mod_of_dvd n (dvd_mul_right 2 M)]; exact hodd
          omega
        simp only [hne, ↓reduceIte]
        have hdp : (0 : ℝ) < ((n % (2 * M) : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
        positivity
      · have hev : n % 2 = 0 := by omega
        simp [hev]
    rw [hmult_eq, hy'_eq, hshift, ih (T_b (2 * M) n) _ (mul_pos hprod hmult_pos)]
    constructor
    · rintro ⟨h1, hrest⟩ j hj1 hjk
      cases j with
      | zero => omega
      | succ j =>
        rw [affAB_succ_fst]
        cases j with
        | zero =>
          simp only [affAB, mul_one]
          linarith [show prod * (((if n % 2 = 0 then 1 else n % (2 * M) : ℕ) : ℝ) / 2) =
            prod * ((if n % 2 = 0 then 1 else n % (2 * M) : ℕ) : ℝ) / 2 by ring]
        | succ j =>
          have hr := hrest (j + 1) (by omega) (by omega)
          rw [Nat.cast_mul, pow_succ']
          have heq : prod * (((if n % 2 = 0 then 1 else n % (2 * M) : ℕ) : ℝ) / 2) *
              ((affAB (2 * M) (T_b (2 * M) n) (j + 1)).1 : ℝ) / (2 : ℝ) ^ (j + 1) =
              prod * (((if n % 2 = 0 then 1 else n % (2 * M) : ℕ) : ℝ) *
                ((affAB (2 * M) (T_b (2 * M) n) (j + 1)).1 : ℝ)) /
                (2 * (2 : ℝ) ^ (j + 1)) := by ring
          linarith
    · intro hall
      refine ⟨?_, fun j hj1 hjk => ?_⟩
      · have h1 := hall 1 le_rfl (by omega)
        rw [affAB_succ_fst] at h1
        simp only [affAB, mul_one, pow_one] at h1
        linarith [show prod * (((if n % 2 = 0 then 1 else n % (2 * M) : ℕ) : ℝ) / 2) =
          prod * ((if n % 2 = 0 then 1 else n % (2 * M) : ℕ) : ℝ) / 2 by ring]
      · have hr := hall (j + 1) (by omega) (by omega)
        rw [affAB_succ_fst] at hr
        rw [Nat.cast_mul, pow_succ'] at hr
        have heq : prod * (((if n % 2 = 0 then 1 else n % (2 * M) : ℕ) : ℝ) / 2) *
            ((affAB (2 * M) (T_b (2 * M) n) j).1 : ℝ) / (2 : ℝ) ^ j =
            prod * (((if n % 2 = 0 then 1 else n % (2 * M) : ℕ) : ℝ) *
              ((affAB (2 * M) (T_b (2 * M) n) j).1 : ℝ)) / (2 * (2 : ℝ) ^ j) := by ring
        linarith

/-- **Exact bridge for `b = 2M` (`M` odd)**: `p_k (2*M) k = (1/M) * ∑ y, surviveProb2M M hM k y 1`. -/
theorem p_k_2M_eq_surviveProb {M k : ℕ} (hM : 1 ≤ M) (hModd : M % 2 = 1) (hk : 1 ≤ k) :
    p_k (2 * M) k = (1 / (M : ℝ)) * ∑ y : Fin M, surviveProb2M M hM k y 1 := by
  have hNk : 2 * M * 2 ^ (k - 1) = M * 2 ^ k := by
    have : 2 ^ k = 2 * 2 ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
    rw [this]; ring
  let eqv1 : Fin (2 * M * 2 ^ (k - 1)) ≃ Fin (M * 2 ^ k) := finCongr hNk
  let eqv2 : Fin (M * 2 ^ k) ≃ Fin M × (Fin k → Bool) :=
    Equiv.ofBijective (code2M M k hM) (lem_even_coding_bij_2M hM hModd hk)
  let eqv : Fin (2 * M * 2 ^ (k - 1)) ≃ Fin M × (Fin k → Bool) := eqv1.trans eqv2
  have hcard : ((SurvRes (2 * M) k).card : ℝ) =
      ∑ p : Fin M × (Fin k → Bool), if path2MSurv M hM k p.1 p.2 1 then (1 : ℝ) else 0 := by
    rw [← Equiv.sum_comp eqv]
    unfold SurvRes
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hiff := path2MSurv_iff_affAB hM hModd k r.val 1 zero_lt_one
    have hval : eqv r = (⟨r.val % M, Nat.mod_lt r.val (by omega)⟩,
        fun j : Fin k => ((T_b (2 * M))^[j.val] r.val % 2 == 1)) := rfl
    rw [hval]
    have hcond : (∀ j : Fin k, 2 ^ (j.val + 1) < (affAB (2 * M) r.val (j.val + 1)).1) ↔
        path2MSurv M hM k ⟨r.val % M, Nat.mod_lt r.val (by omega)⟩
          (fun j : Fin k => ((T_b (2 * M))^[j.val] r.val % 2 == 1)) 1 = true := by
      rw [hiff]
      constructor
      · intro h j hj1 hjk
        have hnat : 2 ^ j < (affAB (2 * M) r.val j).1 := by
          have := h ⟨j - 1, by omega⟩
          rwa [show j - 1 + 1 = j by omega] at this
        have hR : (2 : ℝ) ^ j < ((affAB (2 * M) r.val j).1 : ℝ) := by exact_mod_cast hnat
        rw [one_mul, one_lt_div (by positivity)]; exact hR
      · intro h j
        have hR := h (j.val + 1) (by omega) (by omega)
        rw [one_mul, one_lt_div (by positivity)] at hR
        exact_mod_cast hR
    by_cases hp : ∀ j : Fin k, 2 ^ (j.val + 1) < (affAB (2 * M) r.val (j.val + 1)).1
    · have hp' := hcond.mp hp; simp [hp, hp']
    · have hp' : path2MSurv M hM k ⟨r.val % M, Nat.mod_lt r.val (by omega)⟩
          (fun j : Fin k => ((T_b (2 * M))^[j.val] r.val % 2 == 1)) 1 = false := by
        cases hb : path2MSurv M hM k ⟨r.val % M, Nat.mod_lt r.val (by omega)⟩
            (fun j : Fin k => ((T_b (2 * M))^[j.val] r.val % 2 == 1)) 1 with
        | false => rfl
        | true => exact absurd (hcond.mpr hb) hp
      simp [hp, hp']
  unfold p_k
  rw [hcard, hNk, Fintype.sum_prod_type]
  simp_rw [surviveProb2M_eq_path_sum hM k]
  rw [← Finset.mul_sum]
  push_cast
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have h20 : (2 : ℝ) ^ k ≠ 0 := by positivity
  field_simp

/-- Odd-class bijection `code4k` for `b = 4k` (`k ≥ 1`, `n ≥ 1`): maps odd index
    `m < 2*k * 2^(n - 1)` (representing `r = 2*m + 1`) to `(r mod 4k, choice bits 0..n-2)`. -/
def code4k (k n : ℕ) (hk : 1 ≤ k) (m : Fin (2 * k * 2 ^ (n - 1))) :
    Fin (2 * k) × (Fin (n - 1) → Bool) :=
  let r := 2 * m.val + 1
  (⟨(r % (4 * k)) / 2, by have := Nat.mod_lt r (by omega : 0 < 4 * k); omega⟩,
   fun j => (((T_b (4 * k))^[j.val] r / (4 * k)) % 2 == 1))

/-- Bijectivity of `code4k` on odd residues modulo `4k * 2^(n - 1)`. -/
theorem lem_even_coding_bij_4k {k n : ℕ} (hk : 1 ≤ k) (_hn : 1 ≤ n) :
    Function.Bijective (code4k k n hk) := by
  have hcard : Fintype.card (Fin (2 * k * 2 ^ (n - 1))) =
      Fintype.card (Fin (2 * k) × (Fin (n - 1) → Bool)) := by
    simp [Fintype.card_fin, Fintype.card_prod, Fintype.card_bool]
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, hcard⟩
  intro m m' hEq
  let r := 2 * m.val + 1
  let r' := 2 * m'.val + 1
  have hr_mod : r % (4 * k) = r' % (4 * k) := by
    have h0 := congr_arg (fun p => p.1.val) hEq
    change r % (4 * k) / 2 = r' % (4 * k) / 2 at h0
    have hro : (r % (4 * k)) % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd r ⟨2 * k, by ring⟩]; omega
    have hro' : (r' % (4 * k)) % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd r' ⟨2 * k, by ring⟩]; omega
    omega
  have hbits : ∀ j : Fin (n - 1),
      ((T_b (4 * k))^[j.val] r / (4 * k)) % 2 = ((T_b (4 * k))^[j.val] r' / (4 * k)) % 2 := by
    intro j
    have h0 := congr_fun (congr_arg Prod.snd hEq) j
    change (((T_b (4 * k))^[j.val] r / (4 * k)) % 2 == 1) =
      (((T_b (4 * k))^[j.val] r' / (4 * k)) % 2 == 1) at h0
    by_cases h1 : ((T_b (4 * k))^[j.val] r / (4 * k)) % 2 = 1
    · have h2 : ((T_b (4 * k))^[j.val] r' / (4 * k)) % 2 = 1 := by
        simpa [h1] using h0.symm
      omega
    · have h2 : ((T_b (4 * k))^[j.val] r' / (4 * k)) % 2 ≠ 1 := by
        intro hc; have : ((T_b (4 * k))^[j.val] r / (4 * k)) % 2 = 1 := by
          simpa [hc] using h0
        exact h1 this
      omega
  have hmod_all : ∀ j ≤ n - 1, r % (4 * k * 2 ^ j) = r' % (4 * k * 2 ^ j) := by
    intro j hj
    induction j with
    | zero => simpa using hr_mod
    | succ j ih =>
      have hprev := ih (by omega)
      have hcod := lem_even_coding_mod (b := 4 * k) (k := j + 1) (by omega) (by omega) (by omega)
        (by simpa using hprev)
      have hAB := hcod.1 j (by omega)
      have hxmod := (hcod.2 j (by omega)).1
      have hqbit := hbits ⟨j, by omega⟩
      set x := (T_b (4 * k))^[j] r
      set x' := (T_b (4 * k))^[j] r'
      have hx8k : x % (8 * k) = x' % (8 * k) := by
        have hx1 := Nat.div_add_mod x (4 * k)
        have hx2 := Nat.div_add_mod x' (4 * k)
        have hd1 := Nat.div_add_mod (x / (4 * k)) 2
        have hd2 := Nat.div_add_mod (x' / (4 * k)) 2
        have he1 : x = 8 * k * (x / (4 * k) / 2) + (4 * k * ((x / (4 * k)) % 2) + x % (4 * k)) := by
          calc x = 4 * k * (x / (4 * k)) + x % (4 * k) := hx1.symm
            _ = 4 * k * (2 * (x / (4 * k) / 2) + (x / (4 * k)) % 2) + x % (4 * k) := by rw [hd1]
            _ = 8 * k * (x / (4 * k) / 2) + (4 * k * ((x / (4 * k)) % 2) + x % (4 * k)) := by ring
        have he2 : x' = 8 * k * (x' / (4 * k) / 2) + (4 * k * ((x' / (4 * k)) % 2) + x' % (4 * k)) := by
          calc x' = 4 * k * (x' / (4 * k)) + x' % (4 * k) := hx2.symm
            _ = 4 * k * (2 * (x' / (4 * k) / 2) + (x' / (4 * k)) % 2) + x' % (4 * k) := by rw [hd2]
            _ = 8 * k * (x' / (4 * k) / 2) + (4 * k * ((x' / (4 * k)) % 2) + x' % (4 * k)) := by ring
        have hlt1 : 4 * k * ((x / (4 * k)) % 2) + x % (4 * k) < 8 * k := by
          have := Nat.mod_lt x (by omega : 0 < 4 * k)
          have := Nat.mod_lt (x / (4 * k)) (by omega : 0 < 2)
          nlinarith
        have hlt2 : 4 * k * ((x' / (4 * k)) % 2) + x' % (4 * k) < 8 * k := by
          have := Nat.mod_lt x' (by omega : 0 < 4 * k)
          have := Nat.mod_lt (x' / (4 * k)) (by omega : 0 < 2)
          nlinarith
        rw [he1, he2, Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt1,
            Nat.mod_eq_of_lt hlt2, hqbit, hxmod]
      rcases hres : affAB (4 * k) r j with ⟨A, B⟩
      have haff1 := lem_even_affine (b := 4 * k) (by omega) (by omega) r j
      have haff2 := lem_even_affine (b := 4 * k) (by omega) (by omega) r' j
      rw [hres] at haff1
      rw [← hAB, hres] at haff2
      have hAodd : A % 2 = 1 := haff1.2.1
      have hmul8 : (A * r + B) % (4 * k * 2 ^ (j + 1)) = (A * r' + B) % (4 * k * 2 ^ (j + 1)) := by
        rw [← haff1.1, ← haff2.1]
        have hmod_eq : 4 * k * 2 ^ (j + 1) = 2 ^ j * (8 * k) := by rw [pow_succ]; ring
        rw [hmod_eq, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hx8k]
      have hQr : r = 4 * k * (r / (4 * k)) + r % (4 * k) := (Nat.div_add_mod r (4 * k)).symm
      have hQr' : r' = 4 * k * (r' / (4 * k)) + r % (4 * k) := by
        rw [hr_mod]; exact (Nat.div_add_mod r' (4 * k)).symm
      have hAr_mod : (A * (r / (4 * k))) % 2 ^ (j + 1) = (A * (r' / (4 * k))) % 2 ^ (j + 1) := by
        have hzm : ((A * r + B : ℕ) : ZMod (4 * k * 2 ^ (j + 1))) =
            ((A * r' + B : ℕ) : ZMod (4 * k * 2 ^ (j + 1))) :=
          (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hmul8
        push_cast at hzm
        have hzm2 : (A : ZMod (4 * k * 2 ^ (j + 1))) * (r : ZMod (4 * k * 2 ^ (j + 1))) =
            (A : ZMod (4 * k * 2 ^ (j + 1))) * (r' : ZMod (4 * k * 2 ^ (j + 1))) :=
          add_right_cancel hzm
        have hmodA : (A * r) % (4 * k * 2 ^ (j + 1)) = (A * r') % (4 * k * 2 ^ (j + 1)) :=
          (ZMod.natCast_eq_natCast_iff' _ _ _).mp (by push_cast; exact hzm2)
        have h1 : A * r = 4 * k * (A * (r / (4 * k))) + A * (r % (4 * k)) := by
          calc A * r = A * (4 * k * (r / (4 * k)) + r % (4 * k)) := by rw [← hQr]
            _ = 4 * k * (A * (r / (4 * k))) + A * (r % (4 * k)) := by ring
        have h2 : A * r' = 4 * k * (A * (r' / (4 * k))) + A * (r % (4 * k)) := by
          calc A * r' = A * (4 * k * (r' / (4 * k)) + r % (4 * k)) := by rw [← hQr']
            _ = 4 * k * (A * (r' / (4 * k))) + A * (r % (4 * k)) := by ring
        have hz2 : ((4 * k * (A * (r / (4 * k))) : ℕ) : ZMod (4 * k * 2 ^ (j + 1))) =
            ((4 * k * (A * (r' / (4 * k))) : ℕ) : ZMod (4 * k * 2 ^ (j + 1))) := by
          have hz0 : ((A * r : ℕ) : ZMod (4 * k * 2 ^ (j + 1))) =
              ((A * r' : ℕ) : ZMod (4 * k * 2 ^ (j + 1))) :=
            (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hmodA
          rw [h1, h2] at hz0
          push_cast at hz0 ⊢
          exact add_right_cancel hz0
        have hm0 : (4 * k * (A * (r / (4 * k)))) % (4 * k * 2 ^ (j + 1)) =
            (4 * k * (A * (r' / (4 * k)))) % (4 * k * 2 ^ (j + 1)) :=
          (ZMod.natCast_eq_natCast_iff' _ _ _).mp hz2
        rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at hm0
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4 * k) hm0
      have hq_mod : (r / (4 * k)) % 2 ^ (j + 1) = (r' / (4 * k)) % 2 ^ (j + 1) := by
        have hcopA : Nat.Coprime A (2 ^ (j + 1)) :=
          (Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))).pow_right _
        let uA : (ZMod (2 ^ (j + 1)))ˣ := ZMod.unitOfCoprime A hcopA
        have hz : (uA : ZMod (2 ^ (j + 1))) * ((r / (4 * k) : ℕ) : ZMod (2 ^ (j + 1))) =
            (uA : ZMod (2 ^ (j + 1))) * ((r' / (4 * k) : ℕ) : ZMod (2 ^ (j + 1))) := by
          have h0 : ((A * (r / (4 * k)) : ℕ) : ZMod (2 ^ (j + 1))) =
              ((A * (r' / (4 * k)) : ℕ) : ZMod (2 ^ (j + 1))) :=
            (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hAr_mod
          push_cast at h0
          simpa [uA] using h0
        have hc : ((r / (4 * k) : ℕ) : ZMod (2 ^ (j + 1))) =
            ((r' / (4 * k) : ℕ) : ZMod (2 ^ (j + 1))) := by
          have := congr_arg (((uA⁻¹ : (ZMod (2 ^ (j + 1)))ˣ) : ZMod (2 ^ (j + 1))) * ·) hz
          simpa [← mul_assoc] using this
        exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hc
      have hdiv1 : r = 4 * k * 2 ^ (j + 1) * ((r / (4 * k)) / 2 ^ (j + 1)) +
          (4 * k * ((r / (4 * k)) % 2 ^ (j + 1)) + r % (4 * k)) := by
        calc r = 4 * k * (r / (4 * k)) + r % (4 * k) := hQr
          _ = 4 * k * (2 ^ (j + 1) * ((r / (4 * k)) / 2 ^ (j + 1)) +
                (r / (4 * k)) % 2 ^ (j + 1)) + r % (4 * k) := by
              rw [Nat.div_add_mod (r / (4 * k)) (2 ^ (j + 1))]
          _ = 4 * k * 2 ^ (j + 1) * ((r / (4 * k)) / 2 ^ (j + 1)) +
                (4 * k * ((r / (4 * k)) % 2 ^ (j + 1)) + r % (4 * k)) := by ring
      have hdiv2 : r' = 4 * k * 2 ^ (j + 1) * ((r' / (4 * k)) / 2 ^ (j + 1)) +
          (4 * k * ((r' / (4 * k)) % 2 ^ (j + 1)) + r % (4 * k)) := by
        calc r' = 4 * k * (r' / (4 * k)) + r % (4 * k) := hQr'
          _ = 4 * k * (2 ^ (j + 1) * ((r' / (4 * k)) / 2 ^ (j + 1)) +
                (r' / (4 * k)) % 2 ^ (j + 1)) + r % (4 * k) := by
              rw [Nat.div_add_mod (r' / (4 * k)) (2 ^ (j + 1))]
          _ = 4 * k * 2 ^ (j + 1) * ((r' / (4 * k)) / 2 ^ (j + 1)) +
                (4 * k * ((r' / (4 * k)) % 2 ^ (j + 1)) + r % (4 * k)) := by ring
      have hlt1 : 4 * k * ((r / (4 * k)) % 2 ^ (j + 1)) + r % (4 * k) < 4 * k * 2 ^ (j + 1) := by
        have h1 : (r / (4 * k)) % 2 ^ (j + 1) + 1 ≤ 2 ^ (j + 1) :=
          Nat.mod_lt (r / (4 * k)) (by positivity : 0 < 2 ^ (j + 1))
        have h2 := Nat.mod_lt r (by omega : 0 < 4 * k)
        calc 4 * k * ((r / (4 * k)) % 2 ^ (j + 1)) + r % (4 * k)
            < 4 * k * ((r / (4 * k)) % 2 ^ (j + 1)) + 4 * k := by omega
          _ = 4 * k * ((r / (4 * k)) % 2 ^ (j + 1) + 1) := by ring
          _ ≤ 4 * k * 2 ^ (j + 1) := Nat.mul_le_mul_left _ h1
      have hlt2 : 4 * k * ((r' / (4 * k)) % 2 ^ (j + 1)) + r % (4 * k) < 4 * k * 2 ^ (j + 1) := by
        have h1 : (r' / (4 * k)) % 2 ^ (j + 1) + 1 ≤ 2 ^ (j + 1) :=
          Nat.mod_lt (r' / (4 * k)) (by positivity : 0 < 2 ^ (j + 1))
        have h2 := Nat.mod_lt r (by omega : 0 < 4 * k)
        calc 4 * k * ((r' / (4 * k)) % 2 ^ (j + 1)) + r % (4 * k)
            < 4 * k * ((r' / (4 * k)) % 2 ^ (j + 1)) + 4 * k := by omega
          _ = 4 * k * ((r' / (4 * k)) % 2 ^ (j + 1) + 1) := by ring
          _ ≤ 4 * k * 2 ^ (j + 1) := Nat.mul_le_mul_left _ h1
      rw [hdiv1, hdiv2, Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt1,
          Nat.mod_eq_of_lt hlt2, hq_mod]
  have hfull := hmod_all (n - 1) le_rfl
  have hmul2 : 4 * k * 2 ^ (n - 1) = 2 * (2 * k * 2 ^ (n - 1)) := by ring
  have hrlt : r < 4 * k * 2 ^ (n - 1) := by have := m.isLt; dsimp only [r]; omega
  have hrlt' : r' < 4 * k * 2 ^ (n - 1) := by have := m'.isLt; dsimp only [r']; omega
  rw [Nat.mod_eq_of_lt hrlt, Nat.mod_eq_of_lt hrlt'] at hfull
  exact Fin.ext (by dsimp only [r, r'] at hfull; omega)

private lemma T_4k_state_step {k : ℕ} (hk : 1 ≤ k) {r : ℕ} (hr : r % 2 = 1) :
    let i : Fin (2 * k) := ⟨(r % (4 * k)) / 2, by have := Nat.mod_lt r (by omega : 0 < 4 * k); omega⟩
    (⟨(T_b (4 * k) r % (4 * k)) / 2,
      by have := Nat.mod_lt (T_b (4 * k) r) (by omega : 0 < 4 * k); omega⟩ : Fin (2 * k)) =
      if (r / (4 * k)) % 2 = 1 then next4kB k hk i else next4kA k hk i := by
  intro i
  ext
  have hdodd0 : (r % (4 * k)) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd r ⟨2 * k, by ring⟩]; exact hr
  have hd_eq : digit4k i = r % (4 * k) := by
    unfold digit4k
    dsimp only [i]; omega
  set d := r % (4 * k)
  set q := r / (4 * k)
  have hdiv : 4 * k * q + d = r := Nat.div_add_mod r (4 * k)
  have hdodd : d % 2 = 1 := hdodd0
  have hT_eq : T_b (4 * k) r = (d * d + 1) / 2 + 2 * k * (d * q) := by
    rw [T_b_odd hr]
    have hnum : d * r + 1 = (d * d + 1) + 2 * (2 * k * (d * q)) := by rw [← hdiv]; ring
    rw [hnum, Nat.add_mul_div_left _ _ zero_lt_two]
  have hpar : (d * q) % 2 = q % 2 := by rw [Nat.mul_mod, hdodd, one_mul, Nat.mod_mod]
  by_cases hq : q % 2 = 1
  · simp only [hq, ↓reduceIte, next4kB, hd_eq]
    have h1 : (d * q) % 2 = 1 := hpar.trans hq
    have hsplit : 2 * k * (d * q) = 4 * k * ((d * q) / 2) + 2 * k := by
      have : d * q = 2 * ((d * q) / 2) + 1 := by omega
      calc 2 * k * (d * q) = 2 * k * (2 * ((d * q) / 2) + 1) := by conv_lhs => rw [this]
        _ = 4 * k * ((d * q) / 2) + 2 * k := by ring
    rw [hT_eq, hsplit, show (d * d + 1) / 2 + (4 * k * (d * q / 2) + 2 * k) =
        4 * k * (d * q / 2) + ((d * d + 1) / 2 + 2 * k) by ring, Nat.mul_add_mod]
  · simp only [hq, ↓reduceIte, next4kA, hd_eq]
    have h0 : (d * q) % 2 = 0 := by omega
    have hsplit : 2 * k * (d * q) = 4 * k * ((d * q) / 2) := by
      have : d * q = 2 * ((d * q) / 2) := by omega
      calc 2 * k * (d * q) = 2 * k * (2 * ((d * q) / 2)) := by conv_lhs => rw [this]
        _ = 4 * k * ((d * q) / 2) := by ring
    rw [hT_eq, hsplit, add_comm, Nat.mul_add_mod]

/-- Path-level survival indicator for `P_{4k}` (horizon `m + 1`). -/
private noncomputable def path4kSurv (k : ℕ) (hk : 1 ≤ k) :
    ∀ m : ℕ, Fin (2 * k) → (Fin m → Bool) → ℝ → Bool
  | 0, i, _, prod => by classical exact decide (1 < prod * mult4k i)
  | m + 1, i, b, prod =>
    let i' := if b 0 then next4kB k hk i else next4kA k hk i
    by
      classical
      exact decide (1 < prod * mult4k i) &&
        path4kSurv k hk m i' (fun j => b j.succ) (prod * mult4k i)

private lemma surviveProb4k_eq_path_sum {k : ℕ} (hk : 1 ≤ k) :
    ∀ m i prod, surviveProb (P4kMat k hk) mult4k (m + 1) i prod =
      (1 / (2 : ℝ) ^ m) * ∑ b : Fin m → Bool, if path4kSurv k hk m i b prod then (1 : ℝ) else 0 := by
  intro m
  induction m with
  | zero =>
    intro i prod
    unfold surviveProb path4kSurv
    simp only [pow_zero, div_one, one_mul, Fintype.sum_unique]
    by_cases hgt : 1 < prod * mult4k i
    · simp only [hgt, ↓reduceIte, decide_true]
      simp only [surviveProb, mul_one]
      exact P4kMat_sum_one hk i
    · simp only [hgt, ↓reduceIte, decide_false, Bool.false_eq_true]
  | succ m ih =>
    intro i prod
    let eqv : (Fin (m + 1) → Bool) ≃ Bool × (Fin m → Bool) :=
      { toFun := fun b => (b 0, fun j => b j.succ)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := fun b => by funext j; refine Fin.cases rfl (fun l => rfl) j
        right_inv := fun ⟨c, f⟩ => by ext <;> simp }
    rw [← Equiv.sum_comp eqv.symm, Fintype.sum_prod_type]
    unfold surviveProb
    by_cases hgt : 1 < prod * mult4k i
    · simp only [hgt, ↓reduceIte]
      rw [P4kMat_sum_mul hk]
      simp only [eqv, Equiv.coe_fn_symm_mk, path4kSurv, Fin.cons_zero, Fin.cons_succ, hgt,
        decide_true, Bool.true_and, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
      rw [ih (next4kA k hk i), ih (next4kB k hk i), pow_succ]
      ring
    · simp only [hgt, ↓reduceIte, eqv, Equiv.coe_fn_symm_mk, path4kSurv, decide_false,
        Bool.false_and, Bool.false_eq_true, Finset.sum_const_zero, mul_zero]

private lemma path4kSurv_iff_affAB {k : ℕ} (hk : 1 ≤ k) :
    ∀ (m r : ℕ) (hr : r % 2 = 1) (prod : ℝ), 0 < prod →
      (path4kSurv k hk m
          ⟨(r % (4 * k)) / 2, by have := Nat.mod_lt r (by omega : 0 < 4 * k); omega⟩
          (fun j : Fin m => (((T_b (4 * k))^[j.val] r / (4 * k)) % 2 == 1)) prod = true ↔
        ∀ j, 1 ≤ j → j ≤ m + 1 → 1 < prod * ((affAB (4 * k) r j).1 : ℝ) / (2 : ℝ) ^ j) := by
  intro m
  induction m with
  | zero =>
    intro r hr prod _
    unfold path4kSurv mult4k digit4k
    simp only [decide_eq_true_eq]
    have hrmod2 : (r % (4 * k)) % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd r ⟨2 * k, by ring⟩]; exact hr
    have hd_eq : 2 * (r % (4 * k) / 2) + 1 = r % (4 * k) := by omega
    rw [hd_eq]
    constructor
    · intro h j hj1 hjk
      have hj : j = 1 := by omega
      subst hj
      simp only [affAB, Function.iterate_zero, id_eq, show r % 2 ≠ 0 by omega, ↓reduceIte,
        mul_one, pow_one]
      linarith [show prod * (((r % (4 * k) : ℕ) : ℝ) / 2) =
        prod * ((r % (4 * k) : ℕ) : ℝ) / 2 by ring]
    · intro h
      have h1 := h 1 le_rfl le_rfl
      simp only [affAB, Function.iterate_zero, id_eq, show r % 2 ≠ 0 by omega, ↓reduceIte,
        mul_one, pow_one] at h1
      linarith [show prod * (((r % (4 * k) : ℕ) : ℝ) / 2) =
        prod * ((r % (4 * k) : ℕ) : ℝ) / 2 by ring]
  | succ m ih =>
    intro r hr prod hprod
    unfold path4kSurv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Fin.val_zero, Function.iterate_zero, id_eq]
    have hrmod2 : (r % (4 * k)) % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd r ⟨2 * k, by ring⟩]; exact hr
    set i0 : Fin (2 * k) := ⟨(r % (4 * k)) / 2, by have := Nat.mod_lt r (by omega : 0 < 4 * k); omega⟩
    have hd_eq : digit4k i0 = r % (4 * k) := by
      unfold digit4k; dsimp only [i0]; omega
    have hmult_eq : mult4k i0 = ((r % (4 * k) : ℕ) : ℝ) / 2 := by unfold mult4k; rw [hd_eq]
    have hmult_pos : 0 < ((r % (4 * k) : ℕ) : ℝ) / 2 := by
      have : 1 ≤ r % (4 * k) := by omega
      have hdp : (0 : ℝ) < ((r % (4 * k) : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      positivity
    have hi'_eq : (if (((r / (4 * k)) % 2 == 1) = true) then next4kB k hk i0 else next4kA k hk i0) =
        ⟨(T_b (4 * k) r % (4 * k)) / 2,
          by have := Nat.mod_lt (T_b (4 * k) r) (by omega : 0 < 4 * k); omega⟩ := by
      rw [T_4k_state_step hk hr]
      by_cases hq : (r / (4 * k)) % 2 = 1 <;> simp [hq, i0]
    have hshift : (fun j : Fin m => (((T_b (4 * k))^[j.succ.val] r / (4 * k)) % 2 == 1)) =
        (fun j : Fin m => (((T_b (4 * k))^[j.val] (T_b (4 * k) r) / (4 * k)) % 2 == 1)) := by
      funext j; simp [Function.iterate_succ_apply]
    have hTr_odd : T_b (4 * k) r % 2 = 1 := (lem_even_coding_4k_step hk hr).1
    change (1 < prod * mult4k i0 ∧
      path4kSurv k hk m (if (((r / (4 * k)) % 2 == 1) = true) then next4kB k hk i0 else next4kA k hk i0)
        (fun j : Fin m => (((T_b (4 * k))^[j.succ.val] r / (4 * k)) % 2 == 1))
        (prod * mult4k i0) = true) ↔ _
    rw [hmult_eq, hi'_eq, hshift, ih (T_b (4 * k) r) hTr_odd _ (mul_pos hprod hmult_pos)]
    constructor
    · rintro ⟨h1, hrest⟩ j hj1 hjk
      cases j with
      | zero => omega
      | succ j =>
        rw [affAB_succ_fst]
        simp only [show r % 2 ≠ 0 by omega, ↓reduceIte]
        cases j with
        | zero =>
          simp only [affAB, mul_one]
          linarith [show prod * (((r % (4 * k) : ℕ) : ℝ) / 2) =
            prod * ((r % (4 * k) : ℕ) : ℝ) / 2 by ring]
        | succ j =>
          have hr' := hrest (j + 1) (by omega) (by omega)
          push_cast
          rw [pow_succ']
          have heq : prod * (((r % (4 * k) : ℕ) : ℝ) / 2) *
              ((affAB (4 * k) (T_b (4 * k) r) (j + 1)).1 : ℝ) / (2 : ℝ) ^ (j + 1) =
              prod * (((r % (4 * k) : ℕ) : ℝ) * ((affAB (4 * k) (T_b (4 * k) r) (j + 1)).1 : ℝ)) /
                (2 * (2 : ℝ) ^ (j + 1)) := by ring
          linarith
    · intro hall
      refine ⟨?_, fun j hj1 hjk => ?_⟩
      · have h1 := hall 1 le_rfl (by omega)
        simp only [affAB, Function.iterate_zero, id_eq, show r % 2 ≠ 0 by omega, ↓reduceIte,
          mul_one, pow_one] at h1
        linarith [show prod * (((r % (4 * k) : ℕ) : ℝ) / 2) =
          prod * ((r % (4 * k) : ℕ) : ℝ) / 2 by ring]
      · have hr' := hall (j + 1) (by omega) (by omega)
        rw [affAB_succ_fst] at hr'
        simp only [show r % 2 ≠ 0 by omega, ↓reduceIte] at hr'
        push_cast at hr'
        rw [pow_succ'] at hr'
        have heq : prod * (((r % (4 * k) : ℕ) : ℝ) / 2) * ((affAB (4 * k) (T_b (4 * k) r) j).1 : ℝ) /
              (2 : ℝ) ^ j =
            prod * (((r % (4 * k) : ℕ) : ℝ) * ((affAB (4 * k) (T_b (4 * k) r) j).1 : ℝ)) /
              (2 * (2 : ℝ) ^ j) := by ring
        linarith

/-- **Exact bridge for `b = 4k` (`k ≥ 1`, `n ≥ 1`)**:
    `p_k (4*k) n = (1 / (2 * (2*k))) * ∑ i : Fin (2*k), surviveProb (P4kMat k hk) mult4k n i 1`. -/
theorem p_k_4k_eq_surviveProb {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    p_k (4 * k) n =
      (1 / (2 * ((2 * k : ℕ) : ℝ))) *
        ∑ i : Fin (2 * k), surviveProb (P4kMat k hk) mult4k n i 1 := by
  have hmul2 : 4 * k * 2 ^ (n - 1) = 2 * (2 * k * 2 ^ (n - 1)) := by ring
  let oddEmb : Fin (2 * k * 2 ^ (n - 1)) ↪ Fin (4 * k * 2 ^ (n - 1)) :=
    ⟨fun m => ⟨2 * m.val + 1, by have := m.isLt; omega⟩,
     fun a b h => Fin.ext (by have := congr_arg Fin.val h; dsimp at this; omega)⟩
  let SurvOdd : Finset (Fin (2 * k * 2 ^ (n - 1))) :=
    Finset.univ.filter fun m => ∀ j : Fin n, 2 ^ (j.val + 1) < (affAB (4 * k) (2 * m.val + 1) (j.val + 1)).1
  have hcard_odd : (SurvRes (4 * k) n).card = SurvOdd.card := by
    symm
    refine Finset.card_bij (fun m _ => oddEmb m) ?_ ?_ ?_
    · intro m hm
      simp only [SurvOdd, SurvRes, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
      exact hm
    · intro a _ b _ h; exact oddEmb.injective h
    · intro r hr
      simp only [SurvRes, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      have hrodd : r.val % 2 = 1 := by
        by_contra h
        have hev : r.val % 2 = 0 := by omega
        have h1 := hr ⟨0, by omega⟩
        simp [affAB, hev] at h1
      refine ⟨⟨r.val / 2, by have hrlt : r.val < 2 * (2 * k * 2 ^ (n - 1)) := hmul2 ▸ r.isLt; omega⟩, ?_, ?_⟩
      · simp only [SurvOdd, Finset.mem_filter, Finset.mem_univ, true_and]
        have heq : 2 * (r.val / 2) + 1 = r.val := by omega
        rwa [heq]
      · ext; change 2 * (r.val / 2) + 1 = r.val; omega
  let eqv : Fin (2 * k * 2 ^ (n - 1)) ≃ Fin (2 * k) × (Fin (n - 1) → Bool) :=
    Equiv.ofBijective (code4k k n hk) (lem_even_coding_bij_4k hk hn)
  have hcard_sum : (SurvOdd.card : ℝ) =
      ∑ p : Fin (2 * k) × (Fin (n - 1) → Bool),
        if path4kSurv k hk (n - 1) p.1 p.2 1 then (1 : ℝ) else 0 := by
    rw [← Equiv.sum_comp eqv]
    unfold SurvOdd
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hiff := path4kSurv_iff_affAB hk (n - 1) (2 * m.val + 1) (by omega) 1 zero_lt_one
    rw [show n - 1 + 1 = n by omega] at hiff
    have hcond : (∀ j : Fin n, 2 ^ (j.val + 1) < (affAB (4 * k) (2 * m.val + 1) (j.val + 1)).1) ↔
        path4kSurv k hk (n - 1) (eqv m).1 (eqv m).2 1 = true := by
      change _ ↔ path4kSurv k hk (n - 1) (code4k k n hk m).1 (code4k k n hk m).2 1 = true
      rw [code4k, hiff]
      constructor
      · intro h j hj1 hjn
        have hnat : 2 ^ j < (affAB (4 * k) (2 * m.val + 1) j).1 := by
          have := h ⟨j - 1, by omega⟩
          rwa [show j - 1 + 1 = j by omega] at this
        have hR : (2 : ℝ) ^ j < ((affAB (4 * k) (2 * m.val + 1) j).1 : ℝ) := by exact_mod_cast hnat
        rw [one_mul, one_lt_div (by positivity)]; exact hR
      · intro h j
        have hR := h (j.val + 1) (by omega) (by omega)
        rw [one_mul, one_lt_div (by positivity)] at hR
        exact_mod_cast hR
    by_cases hp : ∀ j : Fin n, 2 ^ (j.val + 1) < (affAB (4 * k) (2 * m.val + 1) (j.val + 1)).1
    · have hp' := hcond.mp hp; simp [hp, hp']
    · have hp' : path4kSurv k hk (n - 1) (eqv m).1 (eqv m).2 1 = false := by
        cases hb : path4kSurv k hk (n - 1) (eqv m).1 (eqv m).2 1 with
        | false => rfl
        | true => exact absurd (hcond.mpr hb) hp
      simp [hp, hp']
  unfold p_k
  rw [hcard_odd, hcard_sum, Fintype.sum_prod_type]
  have hn_eq : n = (n - 1) + 1 := by omega
  conv_rhs => rw [hn_eq]
  simp_rw [surviveProb4k_eq_path_sum hk (n - 1)]
  rw [← Finset.mul_sum]
  push_cast
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have h20 : (2 : ℝ) ^ (n - 1) ≠ 0 := by positivity
  field_simp
  ring

/-! ## Section 3: Negative-drift bases `b ∈ {2, 4, 6, 10}` (`p_infty(b) = 0`) -/

lemma p_infty_eq_zero_of_decay {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0)
    {C lam : ℝ} (_hC : 0 ≤ C) (hlam_nn : 0 ≤ lam) (hlam_lt : lam < 1)
    (hbound : ∀ k : ℕ, 1 ≤ k → p_k b k ≤ C * lam ^ k) : p_infty b = 0 := by
  have hle : p_infty b ≤ 0 := by
    have htend : Filter.Tendsto (fun k : ℕ => C * lam ^ (k + 1)) Filter.atTop (nhds 0) := by
      have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hlam_nn hlam_lt).comp
        (Filter.tendsto_add_atTop_nat 1)
      simpa using h1.const_mul C
    exact le_of_tendsto_of_tendsto (p_k_tendsto_p_infty hb2 hbeven) htend
      (Filter.Eventually.of_forall fun k => hbound (k + 1) (by omega))
  exact le_antisymm hle (p_infty_nonneg b)

theorem p_infty_base2 : p_infty 2 = 0 := by
  refine p_infty_eq_zero_of_decay (by omega) (by decide) (C := 0) (lam := 0)
    le_rfl le_rfl (by norm_num) fun k hk => ?_
  rw [zero_mul]
  have hempty : SurvRes 2 k = ∅ := by
    ext r
    simp only [SurvRes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    intro h
    have h1 := h ⟨0, by omega⟩
    simp only [affAB] at h1
    by_cases hev : r.val % 2 = 0
    · simp [hev] at h1
    · have : r.val % 2 = 1 := by omega
      simp [this] at h1
  simp [p_k, hempty]

theorem p_infty_base4 : p_infty 4 = 0 := by
  let w : Fin (2 * 1) → ℝ := fun i => Real.sqrt (mult4k i)
  let lam : ℝ := (Real.sqrt (1 / 2 : ℝ) + Real.sqrt (3 / 2 : ℝ)) / 2
  have hlam_pos : 0 < lam := by positivity
  have hlam_lt : lam < 1 := by
    have hsq : Real.sqrt (1 / 2 : ℝ) + Real.sqrt (3 / 2 : ℝ) < 2 := by
      have hprod : Real.sqrt (1 / 2 : ℝ) * Real.sqrt (3 / 2 : ℝ) < 1 := by
        rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_one]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have hsq2 : (Real.sqrt (1 / 2 : ℝ) + Real.sqrt (3 / 2 : ℝ)) ^ 2 < 2 ^ 2 := by
        calc (Real.sqrt (1 / 2 : ℝ) + Real.sqrt (3 / 2 : ℝ)) ^ 2
            = (Real.sqrt (1 / 2 : ℝ)) ^ 2 + (Real.sqrt (3 / 2 : ℝ)) ^ 2 +
              2 * (Real.sqrt (1 / 2 : ℝ) * Real.sqrt (3 / 2 : ℝ)) := by ring
          _ = 1 / 2 + 3 / 2 + 2 * (Real.sqrt (1 / 2 : ℝ) * Real.sqrt (3 / 2 : ℝ)) := by
              rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
          _ < 2 ^ 2 := by linarith
      nlinarith [Real.sqrt_nonneg (1 / 2 : ℝ), Real.sqrt_nonneg (3 / 2 : ℝ)]
    dsimp only [lam]; linarith
  have hwmin : 0 < Real.sqrt (1 / 2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hw_ge : ∀ i : Fin (2 * 1), Real.sqrt (1 / 2 : ℝ) ≤ w i := by
    intro i; fin_cases i
    · apply Real.sqrt_le_sqrt; unfold mult4k digit4k; norm_num
    · apply Real.sqrt_le_sqrt; unfold mult4k digit4k; norm_num
  have hsub : ∀ i : Fin (2 * 1),
      Mplus (P4kMat 1 le_rfl) mult4k (1 / 2 : ℝ) w i ≤ lam * w i := by
    intro i
    unfold Mplus
    rw [P4kMat_sum_mul le_rfl, ← Real.sqrt_eq_rpow]
    have hpair : w (next4kA 1 le_rfl i) + w (next4kB 1 le_rfl i) =
        Real.sqrt (1 / 2 : ℝ) + Real.sqrt (3 / 2 : ℝ) := by
      fin_cases i <;> (simp only [w, mult4k, digit4k, next4kA, next4kB]; norm_num)
    rw [hpair]
    dsimp only [w, lam]
    linarith
  let μ : Fin (2 * 1) → ℝ := fun _ => 1 / 4
  have hC : 0 ≤ (∑ i : Fin (2 * 1), μ i * w i) / Real.sqrt (1 / 2 : ℝ) := by
    apply div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      hwmin.le
  refine p_infty_eq_zero_of_decay (by omega) (by decide) hC hlam_pos.le hlam_lt fun k hk => ?_
  have hpk := p_k_4k_eq_surviveProb (k := 1) (n := k) le_rfl hk
  have hdec := prop_stopping_certs_decay (P4kMat_nonneg le_rfl)
    (fun i => by unfold mult4k digit4k; positivity)
    (by norm_num : (0 : ℝ) < 1 / 2) hlam_pos hwmin hw_ge hsub
    (μ := μ) (fun _ => by norm_num) k
  have hEq : p_k 4 k = ∑ i : Fin (2 * 1), μ i * surviveProb (P4kMat 1 le_rfl) mult4k k i 1 := by
    change p_k (4 * 1) k = _
    rw [hpk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only [μ]; norm_num
  rw [hEq]
  exact hdec

theorem p_infty_base6 : p_infty 6 = 0 := by
  let w : Fin 3 → ℝ := fun y => match y.val with | 0 => 1 | 1 => 7 / 10 | _ => 9 / 10
  have hw_ge : ∀ y : Fin 3, (7 / 10 : ℝ) ≤ w y := by
    intro y; fin_cases y <;> norm_num [w]
  have hsub : ∀ y : Fin 3,
      (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ (1 / 2 : ℝ) * w (hStep2M 3 (by omega) y) +
        ((oddDigit2M 3 y : ℝ) / 2) ^ (1 / 2 : ℝ) * w (qStep2M 3 (by omega) y)) ≤
        (19 / 20 : ℝ) * w y := by
    have hs12 : Real.sqrt (1 / 2 : ℝ) ≤ 71 / 100 := by
      have : (Real.sqrt (1 / 2 : ℝ)) ^ 2 ≤ (71 / 100 : ℝ) ^ 2 := by
        rw [Real.sq_sqrt (by norm_num)]; norm_num
      nlinarith [Real.sqrt_nonneg (1 / 2 : ℝ)]
    have hs32 : Real.sqrt (3 / 2 : ℝ) ≤ 123 / 100 := by
      have : (Real.sqrt (3 / 2 : ℝ)) ^ 2 ≤ (123 / 100 : ℝ) ^ 2 := by
        rw [Real.sq_sqrt (by norm_num)]; norm_num
      nlinarith [Real.sqrt_nonneg (3 / 2 : ℝ)]
    have hs52 : Real.sqrt (5 / 2 : ℝ) ≤ 159 / 100 := by
      have : (Real.sqrt (5 / 2 : ℝ)) ^ 2 ≤ (159 / 100 : ℝ) ^ 2 := by
        rw [Real.sq_sqrt (by norm_num)]; norm_num
      nlinarith [Real.sqrt_nonneg (5 / 2 : ℝ)]
    intro y
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    fin_cases y
    · have hd0 : (oddDigit2M 3 ⟨0, by omega⟩ : ℝ) = 3 := by
        unfold oddDigit2M oddDigitNat; norm_num
      have hH0 : w (hStep2M 3 (by omega) ⟨0, by omega⟩) = 1 := rfl
      have hQ0 : w (qStep2M 3 (by omega) ⟨0, by omega⟩) = 9 / 10 := rfl
      have hw0 : w ⟨0, by omega⟩ = 1 := rfl
      rw [hd0, hH0, hQ0, hw0]; linarith
    · have hd1 : (oddDigit2M 3 ⟨1, by omega⟩ : ℝ) = 1 := by
        unfold oddDigit2M oddDigitNat; norm_num
      have hH1 : w (hStep2M 3 (by omega) ⟨1, by omega⟩) = 9 / 10 := rfl
      have hQ1 : w (qStep2M 3 (by omega) ⟨1, by omega⟩) = 7 / 10 := rfl
      have hw1 : w ⟨1, by omega⟩ = 7 / 10 := rfl
      rw [hd1, hH1, hQ1, hw1]; linarith
    · have hd2 : (oddDigit2M 3 ⟨2, by omega⟩ : ℝ) = 5 := by
        unfold oddDigit2M oddDigitNat; norm_num
      have hH2 : w (hStep2M 3 (by omega) ⟨2, by omega⟩) = 7 / 10 := rfl
      have hQ2 : w (qStep2M 3 (by omega) ⟨2, by omega⟩) = 7 / 10 := rfl
      have hw2 : w ⟨2, by omega⟩ = 9 / 10 := rfl
      rw [hd2, hH2, hQ2, hw2]; linarith
  have hdec := prop_decay_2M (M := 3) (by omega) (t := 1 / 2) (lam := 19 / 20) (wmin := 7 / 10)
    (by norm_num) (by norm_num) (by norm_num) hw_ge hsub
  refine p_infty_eq_zero_of_decay (by omega) (by decide) (C := 10 / 7) (lam := 19 / 20)
    (by norm_num) (by norm_num) (by norm_num) fun k hk => ?_
  have hpk := p_k_2M_eq_surviveProb (M := 3) (k := k) (by omega) (by decide) hk
  change p_k (2 * 3) k ≤ _
  rw [hpk]
  have hle_y : ∀ y : Fin 3, surviveProb2M 3 (by omega) k y 1 ≤ (10 / 7 : ℝ) * (19 / 20 : ℝ) ^ k := by
    intro y
    have h1 := hdec k y 1 le_rfl
    rw [Real.one_rpow, one_mul] at h1
    have hwy : w y ≤ 1 := by fin_cases y <;> norm_num [w]
    have h2 : (19 / 20 : ℝ) ^ k * w y ≤ (19 / 20 : ℝ) ^ k * 1 :=
      mul_le_mul_of_nonneg_left hwy (by positivity)
    linarith
  calc (1 / (3 : ℝ)) * ∑ y : Fin 3, surviveProb2M 3 (by omega) k y 1
      ≤ (1 / (3 : ℝ)) * ∑ _y : Fin 3, ((10 / 7 : ℝ) * (19 / 20 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hle_y y) (by norm_num)
    _ = (10 / 7 : ℝ) * (19 / 20 : ℝ) ^ k := by simp

theorem p_infty_base10 : p_infty 10 = 0 := by
  have hT10 : T_b 10 = T := by
    funext n; unfold T_b T d; rfl
  refine p_infty_eq_zero_of_decay (by omega) (by decide)
    (C := 1124953 / 1000000) (lam := 996423 / 1000000)
    (by norm_num) (by norm_num) (by norm_num) fun k hk => ?_
  have hle_eps : ∀ ε : ℝ, 0 < ε →
      p_k 10 k ≤ (1124953 / 1000000 : ℝ) * (996423 / 1000000 : ℝ) ^ k + ε := by
    intro ε hε
    obtain ⟨N1, hN1⟩ := thm_terras_bound k hk (ε / 3) (by linarith)
    have hd := p_k_density (b := 10) (k := k) (by omega) (by decide) hk
    rw [HasNaturalDensity, Metric.tendsto_atTop] at hd
    obtain ⟨N2, hN2⟩ := hd (ε / 3) (by linarith)
    obtain ⟨N3, hN3⟩ := exists_nat_gt ((3 : ℝ) / ε)
    let N := max (max N1 N2) (max 1 N3)
    have hN1_le : N1 ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
    have hN2_le : N2 ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
    have hN_pos : (0 : ℝ) < (N : ℝ) := by
      have : 1 ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
      exact_mod_cast (by omega : 0 < N)
    have h1N : (1 : ℝ) / (N : ℝ) < ε / 3 := by
      have hgt : (3 : ℝ) / ε < (N : ℝ) :=
        lt_of_lt_of_le hN3 (by exact_mod_cast le_trans (le_max_right _ _) (le_max_right _ _))
      rw [div_lt_iff₀ hN_pos]
      have := (div_lt_iff₀ hε).mp hgt
      linarith
    have hcnt : countUpTo (D_k 10 k) N ≤ countUpTo (E_k k) N + 1 := by
      classical
      rw [countUpTo_eq_card, countUpTo_eq_card]
      have hsub : (Finset.Icc 1 N).filter (fun n => n ∈ D_k 10 k) ⊆
          (Finset.Icc 1 N).filter (fun n => n ∈ E_k k) ∪ {1} := by
        intro n hn
        simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter,
          Finset.mem_Icc] at hn ⊢
        simp only [D_k, E_k, Set.mem_ofPred_eq, hT10] at hn ⊢
        by_cases hn1 : n = 1
        · right; exact hn1
        · left; exact ⟨hn.1, by omega, hn.2.2⟩
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hdiv : (countUpTo (D_k 10 k) N : ℝ) / (N : ℝ) ≤
        (countUpTo (E_k k) N : ℝ) / (N : ℝ) + (1 : ℝ) / (N : ℝ) := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcnt) hN_pos.le
    have hclose := hN2 N hN2_le
    rw [Real.dist_eq, abs_lt] at hclose
    linarith [hN1 N hN1_le]
  by_contra hgt
  push Not at hgt
  have hε : 0 < p_k 10 k - (1124953 / 1000000 : ℝ) * (996423 / 1000000 : ℝ) ^ k := by linarith
  linarith [hle_eps ((p_k 10 k - (1124953 / 1000000 : ℝ) * (996423 / 1000000 : ℝ) ^ k) / 2)
    (by linarith)]

/-! ## Section 4: Positive lower bounds for all `b = 4k` (`k ≥ 2`) -/

/-- Exact `b = 8` (`k = 2`) positive survival bound via closed-form eigenvector `w(i) = r^(-1/4)`. -/
private lemma pos_base8 : ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ, 1 ≤ n → η ≤ p_k 8 n := by
  let w : Fin (2 * 2) → ℝ := fun i => (digit4k i : ℝ) ^ (-(1 / 4 : ℝ))
  have hwmin_pos : 0 < (7 : ℝ) ^ (-(1 / 4 : ℝ)) := by positivity
  have hw_ge : ∀ i : Fin (2 * 2), (7 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ w i := by
    intro i
    dsimp only [w]
    have hdpos : (0 : ℝ) < (digit4k i : ℝ) := by exact_mod_cast digit4k_pos i
    rw [Real.rpow_neg hdpos.le, Real.rpow_neg (by norm_num)]
    apply inv_anti₀ (by positivity)
    apply Real.rpow_le_rpow hdpos.le _ (by norm_num)
    have : digit4k i ≤ 7 := by fin_cases i <;> decide
    exact_mod_cast this
  have h5_bound : (5 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 27 / 40 := by
    rw [Real.rpow_neg (by norm_num), inv_le_comm₀ (by positivity) (by norm_num),
        show (27 / 40 : ℝ)⁻¹ = 40 / 27 by norm_num]
    have h4 : (40 / 27 : ℝ) ^ (4 : ℕ) ≤ ((5 : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast ((5 : ℝ) ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul (by norm_num)]
      have : (1 / 4 : ℝ) * (4 : ℕ) = 1 := by norm_num
      rw [this, Real.rpow_one]; norm_num
    exact le_of_pow_le_pow_left₀ (by norm_num : 4 ≠ 0) (by positivity) h4
  have h2_bound : (2 : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 40 / 67 := by
    rw [Real.rpow_neg (by norm_num), inv_le_comm₀ (by positivity) (by norm_num),
        show (40 / 67 : ℝ)⁻¹ = 67 / 40 by norm_num]
    have h4 : (67 / 40 : ℝ) ^ (4 : ℕ) ≤ ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (3 / 4 : ℝ)) 4, ← Real.rpow_mul (by norm_num)]
      have : (3 / 4 : ℝ) * (4 : ℕ) = (3 : ℕ) := by norm_num
      rw [this, Real.rpow_natCast]; norm_num
    exact le_of_pow_le_pow_left₀ (by norm_num : 4 ≠ 0) (by positivity) h4
  have hsub : ∀ i : Fin (2 * 2),
      Mminus (P4kMat 2 (by omega)) mult4k (1 / 4 : ℝ) w i ≤ w i := by
    intro i
    unfold Mminus
    rw [P4kMat_sum_mul (by omega)]
    have hpair : w (next4kA 2 (by omega) i) + w (next4kB 2 (by omega) i) =
        1 + (5 : ℝ) ^ (-(1 / 4 : ℝ)) := by
      fin_cases i <;>
        (simp only [w, next4kA, next4kB, digit4k]; norm_num; try ring)
    rw [hpair]
    have hmult_split : (mult4k i) ^ (-(1 / 4 : ℝ)) * (1 / 2 : ℝ) =
        (2 : ℝ) ^ (-(3 / 4 : ℝ)) * w i := by
      unfold mult4k w
      have hdpos : (0 : ℝ) < (digit4k i : ℝ) := by exact_mod_cast digit4k_pos i
      rw [Real.div_rpow hdpos.le (by norm_num), div_eq_mul_inv,
          ← Real.rpow_neg (by norm_num), neg_neg]
      have h2eq : (2 : ℝ) ^ (1 / 4 : ℝ) * (1 / 2 : ℝ) = (2 : ℝ) ^ (-(3 / 4 : ℝ)) := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num,
            ← Real.rpow_add (by norm_num)]
        congr 1; norm_num
      calc (digit4k i : ℝ) ^ (-(1 / 4 : ℝ)) * (2 : ℝ) ^ (1 / 4 : ℝ) * (1 / 2 : ℝ)
          = ((2 : ℝ) ^ (1 / 4 : ℝ) * (1 / 2 : ℝ)) * (digit4k i : ℝ) ^ (-(1 / 4 : ℝ)) := by ring
        _ = (2 : ℝ) ^ (-(3 / 4 : ℝ)) * (digit4k i : ℝ) ^ (-(1 / 4 : ℝ)) := by rw [h2eq]
    calc (mult4k i) ^ (-(1 / 4 : ℝ)) * ((1 / 2 : ℝ) * (1 + (5 : ℝ) ^ (-(1 / 4 : ℝ))))
        = ((mult4k i) ^ (-(1 / 4 : ℝ)) * (1 / 2 : ℝ)) * (1 + (5 : ℝ) ^ (-(1 / 4 : ℝ))) := by ring
      _ = ((2 : ℝ) ^ (-(3 / 4 : ℝ)) * (1 + (5 : ℝ) ^ (-(1 / 4 : ℝ)))) * w i := by
          rw [hmult_split]; ring
      _ ≤ 1 * w i := by
          apply mul_le_mul_of_nonneg_right _ (by dsimp [w]; positivity)
          calc (2 : ℝ) ^ (-(3 / 4 : ℝ)) * (1 + (5 : ℝ) ^ (-(1 / 4 : ℝ)))
              ≤ (40 / 67 : ℝ) * (1 + 27 / 40) :=
                mul_le_mul h2_bound (by linarith) (by positivity) (by norm_num)
            _ = 1 := by norm_num
      _ = w i := one_mul _
  have hmult_pos : ∀ i : Fin (2 * 2), 0 < mult4k i := fun i => by
    unfold mult4k
    have hdp : (0 : ℝ) < (digit4k i : ℝ) := by exact_mod_cast digit4k_pos i
    exact div_pos hdp zero_lt_two
  have hruin := prop_stopping_certs_survival (P4kMat_nonneg (k := 2) (by omega))
    (P4kMat_sum_one (k := 2) (by omega))
    hmult_pos (by norm_num : (0 : ℝ) < 1 / 4) hwmin_pos hw_ge hsub
  let η : ℝ := (1 / 16 : ℝ) * (1 - (2 / 5 : ℝ) ^ (1 / 4 : ℝ))
  have hη_pos : 0 < η := by
    have hlt : (2 / 5 : ℝ) ^ (1 / 4 : ℝ) < 1 := by
      conv_rhs => rw [← Real.one_rpow (1 / 4 : ℝ)]
      exact Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 2 / 5) (by norm_num) (by norm_num)
    dsimp only [η]; linarith
  refine ⟨η, hη_pos, fun n hn => ?_⟩
  cases n with
  | zero => omega
  | succ n =>
    have hpk := p_k_4k_eq_surviveProb (k := 2) (n := n + 1) (by omega) (by omega)
    change η ≤ p_k (4 * 2) (n + 1)
    rw [hpk]
    let i3 : Fin (2 * 2) := ⟨3, by omega⟩
    have hterm_ge : (1 / 2 : ℝ) * (1 - (2 / 5 : ℝ) ^ (1 / 4 : ℝ)) ≤
        surviveProb (P4kMat 2 (by omega)) mult4k (n + 1) i3 1 := by
      unfold surviveProb
      have hm3 : mult4k i3 = 7 / 2 := by unfold mult4k digit4k i3; norm_num
      have hgt1 : 1 < mult4k i3 := by rw [hm3]; norm_num
      simp only [one_mul, hgt1, ↓reduceIte]
      rw [P4kMat_sum_mul (by omega)]
      have hB : next4kB 2 (by omega) i3 = ⟨2, by omega⟩ := by
        apply Fin.ext
        change (((2 * 3 + 1) * (2 * 3 + 1) + 1) / 2 + 2 * 2) % (4 * 2) / 2 = 2
        decide
      have hnnA := surviveProb_nonneg (P4kMat_nonneg (k := 2) (by omega)) mult4k n
        (next4kA 2 (by omega) i3) (mult4k i3)
      have hadd := surviveProb_add_ruinProb (P := P4kMat 2 (by omega)) (mult := mult4k)
        (P4kMat_sum_one (k := 2) (by omega)) hmult_pos
        n ⟨2, by omega⟩ (mult4k i3) (by rw [hm3]; norm_num)
      have hr := hruin n ⟨2, by omega⟩ (1 / mult4k i3) (by rw [hm3]; norm_num)
      have hval : (1 / mult4k i3) ^ (1 / 4 : ℝ) * w ⟨2, by omega⟩ / (7 : ℝ) ^ (-(1 / 4 : ℝ)) =
          (2 / 5 : ℝ) ^ (1 / 4 : ℝ) := by
        rw [hm3]
        dsimp only [w, digit4k]
        norm_num
        rw [Real.div_rpow (by norm_num) (by norm_num), Real.div_rpow (by norm_num) (by norm_num),
            Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)]
        have h7 : (7 : ℝ) ^ (1 / 4 : ℝ) ≠ 0 := by positivity
        have h5 : (5 : ℝ) ^ (1 / 4 : ℝ) ≠ 0 := by positivity
        field_simp
      rw [hval] at hr
      rw [hB]
      linarith
    have hsum_ge : surviveProb (P4kMat 2 (by omega)) mult4k (n + 1) i3 1 ≤
        ∑ i : Fin (2 * 2), surviveProb (P4kMat 2 (by omega)) mult4k (n + 1) i 1 :=
      Finset.single_le_sum (fun i _ => surviveProb_nonneg (P4kMat_nonneg (k := 2) (by omega))
        mult4k (n + 1) i 1) (Finset.mem_univ i3)
    have hcoef : (1 / (2 * ((2 * 2 : ℕ) : ℝ))) = (1 / 8 : ℝ) := by norm_num
    rw [hcoef]
    dsimp only [η]
    linarith

/-- Reusable pure-kernel certificate helper for `b = 4k` at `t = 1/2` (used for `b = 12, 24`). -/
private lemma pos_4k_of_sq_cert {k : ℕ} (hk : 1 ≤ k) (w : Fin (2 * k) → ℕ) (wmin : ℕ)
    (hwmin : 1 ≤ wmin) (hw_ge : ∀ i, wmin ≤ w i)
    (hsq : ∀ i : Fin (2 * k),
      (w (next4kA k hk i) + w (next4kB k hk i)) ^ 2 ≤ 2 * digit4k i * (w i) ^ 2)
    (i0 : Fin (2 * k)) (hi0 : 3 ≤ digit4k i0)
    (hwit : 2 * (w (next4kA k hk i0)) ^ 2 < digit4k i0 * wmin ^ 2 ∨
            2 * (w (next4kB k hk i0)) ^ 2 < digit4k i0 * wmin ^ 2) :
    ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ, 1 ≤ n → η ≤ p_k (4 * k) n := by
  let wR : Fin (2 * k) → ℝ := fun i => (w i : ℝ)
  have hwminR : (0 : ℝ) < (wmin : ℝ) := by exact_mod_cast (by omega : 0 < wmin)
  have hwR_ge : ∀ i, (wmin : ℝ) ≤ wR i := fun i => by dsimp only [wR]; exact_mod_cast hw_ge i
  have hmult_pos : ∀ i : Fin (2 * k), 0 < mult4k i := fun i => by
    unfold mult4k
    have hdp : (0 : ℝ) < (digit4k i : ℝ) := by exact_mod_cast digit4k_pos i
    exact div_pos hdp zero_lt_two
  have hsub : ∀ i : Fin (2 * k),
      Mminus (P4kMat k hk) mult4k (1 / 2 : ℝ) wR i ≤ wR i := by
    intro i
    unfold Mminus
    rw [P4kMat_sum_mul hk, Real.rpow_neg (hmult_pos i).le, ← Real.sqrt_eq_rpow, ← Real.sqrt_inv]
    have hinv : (mult4k i)⁻¹ = 2 / (digit4k i : ℝ) := by unfold mult4k; field_simp
    rw [hinv]
    have hsqR : ((w (next4kA k hk i) : ℝ) + (w (next4kB k hk i) : ℝ)) ^ 2 ≤
        2 * (digit4k i : ℝ) * (w i : ℝ) ^ 2 := by exact_mod_cast hsq i
    have hdpos : (0 : ℝ) < (digit4k i : ℝ) := by exact_mod_cast digit4k_pos i
    have h2 : (Real.sqrt (2 / (digit4k i : ℝ)) *
        ((1 / 2 : ℝ) * (wR (next4kA k hk i) + wR (next4kB k hk i)))) ^ 2 ≤ (wR i) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      dsimp only [wR]
      have : (2 / (digit4k i : ℝ)) * ((1 / 2 : ℝ) * ((w (next4kA k hk i) : ℝ) +
          (w (next4kB k hk i) : ℝ))) ^ 2 =
          ((w (next4kA k hk i) : ℝ) + (w (next4kB k hk i) : ℝ)) ^ 2 / (2 * (digit4k i : ℝ)) := by
        ring
      rw [this, div_le_iff₀ (by positivity)]
      linarith
    have hnn1 : 0 ≤ Real.sqrt (2 / (digit4k i : ℝ)) *
        ((1 / 2 : ℝ) * (wR (next4kA k hk i) + wR (next4kB k hk i))) := by
      dsimp only [wR]; positivity
    have hnn2 : 0 ≤ wR i := by dsimp only [wR]; positivity
    nlinarith
  have hruin := prop_stopping_certs_survival (P4kMat_nonneg hk) (P4kMat_sum_one hk)
    hmult_pos (by norm_num : (0 : ℝ) < 1 / 2) hwminR hwR_ge hsub
  have hstep_wit : ∀ j : Fin (2 * k), 2 * (w j) ^ 2 < digit4k i0 * wmin ^ 2 →
      0 < 1 - Real.sqrt (2 / (digit4k i0 : ℝ)) * wR j / (wmin : ℝ) := by
    intro j hj
    have hdpos : (0 : ℝ) < (digit4k i0 : ℝ) := by exact_mod_cast digit4k_pos i0
    have hjR : 2 * (w j : ℝ) ^ 2 < (digit4k i0 : ℝ) * (wmin : ℝ) ^ 2 := by exact_mod_cast hj
    have hsq1 : (Real.sqrt (2 / (digit4k i0 : ℝ)) * wR j / (wmin : ℝ)) ^ 2 < 1 ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), one_pow, div_lt_one (by positivity)]
      dsimp only [wR]
      rw [show 2 / (digit4k i0 : ℝ) * (w j : ℝ) ^ 2 = 2 * (w j : ℝ) ^ 2 / (digit4k i0 : ℝ) by ring,
          div_lt_iff₀ hdpos]
      linarith
    have hnn : 0 ≤ Real.sqrt (2 / (digit4k i0 : ℝ)) * wR j / (wmin : ℝ) := by
      dsimp only [wR]; positivity
    nlinarith
  have hcommon : ∀ (j : Fin (2 * k)) (hj : j = next4kA k hk i0 ∨ j = next4kB k hk i0),
      2 * (w j) ^ 2 < digit4k i0 * wmin ^ 2 →
      ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ, 1 ≤ n → η ≤ p_k (4 * k) n := by
    intro j hj hlt
    let δ := 1 - Real.sqrt (2 / (digit4k i0 : ℝ)) * wR j / (wmin : ℝ)
    have hδ : 0 < δ := hstep_wit j hlt
    refine ⟨(1 / (2 * ((2 * k : ℕ) : ℝ))) * ((1 / 2 : ℝ) * δ), by positivity, fun n hn => ?_⟩
    cases n with
    | zero => omega
    | succ n =>
      rw [p_k_4k_eq_surviveProb hk (by omega)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hsum := Finset.single_le_sum (fun i _ => surviveProb_nonneg (P4kMat_nonneg hk)
        mult4k (n + 1) i 1) (Finset.mem_univ i0)
      refine le_trans ?_ hsum
      unfold surviveProb
      have hgt1 : 1 < mult4k i0 := by
        unfold mult4k; have : (3 : ℝ) ≤ (digit4k i0 : ℝ) := by exact_mod_cast hi0
        linarith
      simp only [one_mul, hgt1, ↓reduceIte]
      rw [P4kMat_sum_mul hk]
      have hsurv_j : δ ≤ surviveProb (P4kMat k hk) mult4k n j (mult4k i0) := by
        have hadd := surviveProb_add_ruinProb (P := P4kMat k hk) (mult := mult4k)
          (P4kMat_sum_one hk) hmult_pos n j (mult4k i0) (hmult_pos i0)
        have hr := hruin n j (1 / mult4k i0) (div_pos zero_lt_one (hmult_pos i0))
        have hpow : (1 / mult4k i0) ^ (1 / 2 : ℝ) = Real.sqrt (2 / (digit4k i0 : ℝ)) := by
          rw [← Real.sqrt_eq_rpow]; congr 1; unfold mult4k; field_simp
        rw [hpow] at hr
        dsimp only [δ]; linarith
      have hnnA := surviveProb_nonneg (P4kMat_nonneg hk) mult4k n (next4kA k hk i0) (mult4k i0)
      have hnnB := surviveProb_nonneg (P4kMat_nonneg hk) mult4k n (next4kB k hk i0) (mult4k i0)
      rcases hj with rfl | rfl <;> linarith
  rcases hwit with hA | hB
  · exact hcommon _ (Or.inl rfl) hA
  · exact hcommon _ (Or.inr rfl) hB

private lemma pos_base12 : ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ, 1 ≤ n → η ≤ p_k 12 n := by
  let w : Fin (2 * 3) → ℕ := fun i => [1000, 314, 447, 378, 181, 302].getD i.val 181
  exact pos_4k_of_sq_cert (k := 3) (by omega) w 181 (by omega)
    (by decide) (by decide) ⟨4, by omega⟩ (by decide) (by decide)

private lemma pos_base24 : ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ, 1 ≤ n → η ≤ p_k 24 n := by
  let w : Fin (2 * 6) → ℕ :=
    fun i => [1000, 312, 447, 378, 180, 302, 277, 139, 243, 229, 118, 209].getD i.val 118
  exact pos_4k_of_sq_cert (k := 6) (by omega) w 118 (by omega)
    (by decide) (by decide) ⟨4, by omega⟩ (by decide) (by decide)

/-- Positive uniform stopping-density lower bound for EVERY `b = 4k` with `k ≥ 2`. -/
theorem pos_all_4k {k : ℕ} (hk : 2 ≤ k) :
    ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ, 1 ≤ n → η ≤ p_k (4 * k) n := by
  by_cases h2 : k = 2
  · subst h2; exact pos_base8
  by_cases h3 : k = 3
  · subst h3; exact pos_base12
  by_cases h6 : k = 6
  · subst h6; exact pos_base24
  · obtain ⟨_, hsurv, hpos⟩ := prop_stopping_certs_4k_uniform (k := k) (by omega) h6
    refine ⟨_, hpos, fun n hn => ?_⟩
    rw [p_k_4k_eq_surviveProb (by omega) hn]
    exact hsurv n hn

/-! ## Section 5: Positive lower bounds for all `b = 2M` (`M ≥ 7` odd) -/

/-- Generic 1-step survival lower bound for `b = 2M` from a `M_t^- w ≤ w` supermartingale
    with a 1-step witness at `y = 0` (`d(0) = M`, `Q(0) = (M + 1)/2`). -/
private lemma pos_2M_of_supermartingale {M : ℕ} (hM7 : 7 ≤ M) (hModd : M % 2 = 1)
    {t wmin : ℝ} (ht : 0 < t) (hwmin : 0 < wmin)
    (w : Fin M → ℝ) (hw_ge : ∀ y, wmin ≤ w y)
    (hsub : ∀ y : Fin M,
      (2 : ℝ) ^ (t - 1) * (w (hStep2M M (by omega) y) +
        (oddDigit2M M y : ℝ) ^ (-t) * w (qStep2M M (by omega) y)) ≤ w y)
    (hwit0 : (2 / (M : ℝ)) ^ t * w (qStep2M M (by omega) ⟨0, by omega⟩) / wmin < 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ, 1 ≤ n → η ≤ p_k (2 * M) n := by
  have hruin := prop_survival_2M (M := M) (by omega) hModd ht hwmin hw_ge hsub
  let y0 : Fin M := ⟨0, by omega⟩
  have hd0 : oddDigit2M M y0 = M := by
    simp [oddDigit2M, oddDigitNat, y0]
  let δ : ℝ := 1 - (2 / (M : ℝ)) ^ t * w (qStep2M M (by omega) y0) / wmin
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  refine ⟨(1 / (M : ℝ)) * ((1 / 2 : ℝ) * δ), by positivity, fun n hn => ?_⟩
  cases n with
  | zero => omega
  | succ n =>
    rw [p_k_2M_eq_surviveProb (by omega) hModd (by omega)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine le_trans ?_ (Finset.single_le_sum (fun y _ => surviveProb2M_nonneg (by omega) (n + 1) y 1)
      (Finset.mem_univ y0))
    unfold surviveProb2M
    rw [hd0]
    have hgt1 : 1 < (M : ℝ) / 2 := by
      have : (7 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM7
      linarith
    simp only [one_mul, hgt1, ↓reduceIte]
    have hnn1 : 0 ≤ (if 1 < (1 / 2 : ℝ) then
        surviveProb2M M (by omega) n (hStep2M M (by omega) y0) (1 / 2 : ℝ) else 0) := by
      split_ifs <;> [exact surviveProb2M_nonneg (by omega) _ _ _; exact le_rfl]
    have hadd := surviveProb2M_add_ruinProb2M (by omega) hModd n (qStep2M M (by omega) y0)
      ((M : ℝ) / 2) (by positivity)
    have hr := hruin n (qStep2M M (by omega) y0) (1 / ((M : ℝ) / 2)) (by positivity)
    have hinv : 1 / ((M : ℝ) / 2) = 2 / (M : ℝ) := by field_simp
    rw [hinv] at hadd hr
    dsimp only [δ]
    linarith

/-- Helper: integer `q`-th power bound `S^q ≤ a^e * c^q` implies `a^(-e/q) ≤ c / S`. -/
private lemma rpow_neg_le_of_pow_le {a e q c S : ℕ} (ha : 0 < a) (hq : 0 < q) (hS : 0 < S)
    (h : S ^ q ≤ a ^ e * c ^ q) :
    (a : ℝ) ^ (-((e : ℝ) / (q : ℝ))) ≤ (c : ℝ) / (S : ℝ) := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hSR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hR : (S : ℝ) ^ q ≤ (a : ℝ) ^ e * (c : ℝ) ^ q := by exact_mod_cast h
  have hpow : ((a : ℝ) ^ (-((e : ℝ) / (q : ℝ)))) ^ q ≤ ((c : ℝ) / (S : ℝ)) ^ q := by
    rw [div_pow, ← Real.rpow_natCast ((a : ℝ) ^ _) q, ← Real.rpow_mul haR.le]
    have hexp : -((e : ℝ) / (q : ℝ)) * (q : ℝ) = -((e : ℕ) : ℝ) := by field_simp
    rw [hexp, Real.rpow_neg haR.le, Real.rpow_natCast, inv_eq_one_div,
        div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    linarith
  exact le_of_pow_le_pow_left₀ (by omega) (by positivity) hpow

private lemma two_mul_mod_eq {M x c : ℕ} (hx : x < M) (h : (2 * x) % M = c) :
    2 * x = c ∨ 2 * x = c + M := by
  have hdiv := Nat.div_add_mod (2 * x) M
  have hq : (2 * x) / M < 2 := by
    have : M * ((2 * x) / M) ≤ 2 * x := Nat.mul_div_le (2 * x) M
    nlinarith
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hq) with h0 | h1
  · left; rw [h0, h] at hdiv; omega
  · right; rw [h1, h] at hdiv; omega

/-- Analytic universal survival proof for ALL odd `M ≥ 267` using the 3-exception vector
    `w(1) = 1, w(2) = 4/5, w(3) = 3/4, w(y) = 2/3` at `t = 1/4`. -/
private lemma pos_2M_ge_267 {M : ℕ} (hM : 267 ≤ M) (hModd : M % 2 = 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ, 1 ≤ n → η ≤ p_k (2 * M) n := by
  let w : Fin M → ℝ := fun y =>
    if y.val = 1 then 1 else if y.val = 2 then 4 / 5 else if y.val = 3 then 3 / 4 else 2 / 3
  have hw_ge : ∀ y : Fin M, (2 / 3 : ℝ) ≤ w y := by
    intro y; dsimp only [w]; split_ifs <;> norm_num
  have hw_le1 : ∀ y : Fin M, w y ≤ 1 := by
    intro y; dsimp only [w]; split_ifs <;> norm_num
  have h2_34 : (2 : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 40 / 67 := by
    have := rpow_neg_le_of_pow_le (a := 2) (e := 3) (q := 4) (c := 40) (S := 67)
      (by omega) (by omega) (by omega) (by decide)
    norm_num at this ⊢; exact this
  have h2_34_tight : (2 : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 3 / 5 := by
    have := rpow_neg_le_of_pow_le (a := 2) (e := 3) (q := 4) (c := 3) (S := 5)
      (by omega) (by omega) (by omega) (by decide)
    norm_num at this ⊢; exact this
  have h3_14 : (3 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 4 / 5 := by
    have := rpow_neg_le_of_pow_le (a := 3) (e := 1) (q := 4) (c := 4) (S := 5)
      (by omega) (by omega) (by omega) (by decide)
    norm_num at this ⊢; exact this
  have h5_14 : (5 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 27 / 40 := by
    have := rpow_neg_le_of_pow_le (a := 5) (e := 1) (q := 4) (c := 27) (S := 40)
      (by omega) (by omega) (by omega) (by decide)
    norm_num at this ⊢; exact this
  have h25_14 : (25 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 9 / 20 := by
    have := rpow_neg_le_of_pow_le (a := 25) (e := 1) (q := 4) (c := 9) (S := 20)
      (by omega) (by omega) (by omega) (by decide)
    norm_num at this ⊢; exact this
  have h256_14 : (256 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 1 / 4 := by
    have := rpow_neg_le_of_pow_le (a := 256) (e := 1) (q := 4) (c := 1) (S := 4)
      (by omega) (by omega) (by omega) (by decide)
    norm_num at this ⊢
  have hpow_anti : ∀ a b : ℕ, 0 < a → a ≤ b → (b : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (a : ℝ) ^ (-(1 / 4 : ℝ)) := by
    intro a b ha hab
    have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    have hbR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    rw [Real.rpow_neg (by linarith), Real.rpow_neg haR.le]
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow haR.le hbR (by norm_num))
  have hH_val : ∀ y : Fin M, (2 * (hStep2M M (by omega) y).val) % M = y.val := by
    intro y
    change (2 * ((y.val * ((M + 1) / 2)) % M)) % M = y.val
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
        show 2 * (y.val * ((M + 1) / 2)) = y.val * (2 * ((M + 1) / 2)) by ring,
        show 2 * ((M + 1) / 2) = M + 1 by omega,
        Nat.mul_add, mul_one, Nat.mul_comm y.val M, Nat.mul_add_mod, Nat.mod_eq_of_lt y.isLt]
  have hsub : ∀ y : Fin M,
      (2 : ℝ) ^ ((1 / 4 : ℝ) - 1) * (w (hStep2M M (by omega) y) +
        (oddDigit2M M y : ℝ) ^ (-(1 / 4 : ℝ)) * w (qStep2M M (by omega) y)) ≤ w y := by
    intro y
    rw [show (1 / 4 : ℝ) - 1 = -(3 / 4 : ℝ) by norm_num]
    set d := oddDigit2M M y
    have hd_val : d = if y.val % 2 = 1 then y.val else y.val + M := by
      unfold d oddDigit2M oddDigitNat
      by_cases h1 : y.val % 2 = 1
      · simp [h1]
      · have hbeq : Nat.beq (y.val % 2) 1 = false := by
          cases hb : Nat.beq (y.val % 2) 1 with
          | false => rfl
          | true => exact absurd (Nat.eq_of_beq_eq_true hb) h1
        simp [h1, hbeq]
    by_cases hy1 : y.val = 1
    · have hwy : w y = 1 := by simp [w, hy1]
      have hH_ge : 4 ≤ (hStep2M M (by omega) y).val := by
        have h1 := hH_val y; rw [hy1] at h1
        rcases two_mul_mod_eq (hStep2M M (by omega) y).isLt h1 with h | h <;> omega
      have hwH : w (hStep2M M (by omega) y) = 2 / 3 := by dsimp [w]; split_ifs <;> first | rfl | omega
      have hd1 : d = 1 := by rw [hd_val, hy1]; norm_num
      rw [hwy, hwH, hd1]; norm_num
      have hQ1 : w (qStep2M M (by omega) y) ≤ 1 := hw_le1 _
      calc (2 : ℝ) ^ (-(3 / 4 : ℝ)) * (2 / 3 + w (qStep2M M (by omega) y))
          ≤ (3 / 5 : ℝ) * (2 / 3 + 1) := mul_le_mul h2_34_tight (by linarith) (by positivity) (by norm_num)
        _ = 1 := by norm_num
    by_cases hy2 : y.val = 2
    · have hwy : w y = 4 / 5 := by simp [w, hy2]
      have hd_ge : 256 ≤ d := by rw [hd_val, hy2]; norm_num; omega
      have hd_le : (d : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 1 / 4 := (hpow_anti 256 d (by omega) hd_ge).trans h256_14
      rw [hwy]
      have h1 : w (hStep2M M (by omega) y) ≤ 1 := hw_le1 _
      have h2 : w (qStep2M M (by omega) y) ≤ 1 := hw_le1 _
      have h2_nn : 0 ≤ w (qStep2M M (by omega) y) := by linarith [hw_ge (qStep2M M (by omega) y)]
      calc (2 : ℝ) ^ (-(3 / 4 : ℝ)) * (w (hStep2M M (by omega) y) +
            (d : ℝ) ^ (-(1 / 4 : ℝ)) * w (qStep2M M (by omega) y))
          ≤ (3 / 5 : ℝ) * (1 + (1 / 4 : ℝ) * 1) :=
            mul_le_mul h2_34_tight (add_le_add h1 (mul_le_mul hd_le h2 h2_nn (by norm_num)))
              (by positivity) (by norm_num)
        _ ≤ 4 / 5 := by norm_num
    by_cases hy3 : y.val = 3
    · have hwy : w y = 3 / 4 := by simp [w, hy3]
      have hH_ge : 4 ≤ (hStep2M M (by omega) y).val := by
        have h1 := hH_val y; rw [hy3] at h1
        rcases two_mul_mod_eq (hStep2M M (by omega) y).isLt h1 with h | h <;> omega
      have hwH : w (hStep2M M (by omega) y) = 2 / 3 := by dsimp [w]; split_ifs <;> first | rfl | omega
      have hd3 : d = 3 := by rw [hd_val, hy3]; norm_num
      have hQ5 : (qStep2M M (by omega) y).val = 5 := by
        change ((oddDigit2M M y * oddDigit2M M y + 1) / 2) % M = 5
        change ((d * d + 1) / 2) % M = 5
        rw [hd3]; exact Nat.mod_eq_of_lt (by omega)
      have hwQ : w (qStep2M M (by omega) y) = 2 / 3 := by dsimp [w]; rw [hQ5]; norm_num
      rw [hwy, hwH, hwQ, hd3]
      calc (2 : ℝ) ^ (-(3 / 4 : ℝ)) * (2 / 3 + (3 : ℝ) ^ (-(1 / 4 : ℝ)) * (2 / 3))
          ≤ (3 / 5 : ℝ) * (2 / 3 + (4 / 5 : ℝ) * (2 / 3)) :=
            mul_le_mul h2_34_tight (by linarith) (by positivity) (by norm_num)
        _ ≤ 3 / 4 := by norm_num
    by_cases hy4 : y.val = 4
    · have hwy : w y = 2 / 3 := by simp [w, hy4]
      have hH2 : (hStep2M M (by omega) y).val = 2 := by
        have h1 := hH_val y; rw [hy4] at h1
        rcases two_mul_mod_eq (hStep2M M (by omega) y).isLt h1 with h | h <;> omega
      have hwH : w (hStep2M M (by omega) y) = 4 / 5 := by dsimp [w]; rw [hH2]; norm_num
      have hd_ge : 256 ≤ d := by rw [hd_val, hy4]; norm_num; omega
      have hd_le : (d : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 1 / 4 := (hpow_anti 256 d (by omega) hd_ge).trans h256_14
      have h2 : w (qStep2M M (by omega) y) ≤ 1 := hw_le1 _
      have h2_nn : 0 ≤ w (qStep2M M (by omega) y) := by linarith [hw_ge (qStep2M M (by omega) y)]
      rw [hwy, hwH]
      calc (2 : ℝ) ^ (-(3 / 4 : ℝ)) * (4 / 5 + (d : ℝ) ^ (-(1 / 4 : ℝ)) * w (qStep2M M (by omega) y))
          ≤ (3 / 5 : ℝ) * (4 / 5 + (1 / 4 : ℝ) * 1) :=
            mul_le_mul h2_34_tight (add_le_add le_rfl (mul_le_mul hd_le h2 h2_nn (by norm_num)))
              (by positivity) (by norm_num)
        _ ≤ 2 / 3 := by norm_num
    by_cases hy6 : y.val = 6
    · have hwy : w y = 2 / 3 := by simp [w, hy6]
      have hH3 : (hStep2M M (by omega) y).val = 3 := by
        have h1 := hH_val y; rw [hy6] at h1
        rcases two_mul_mod_eq (hStep2M M (by omega) y).isLt h1 with h | h <;> omega
      have hwH : w (hStep2M M (by omega) y) = 3 / 4 := by dsimp [w]; rw [hH3]; norm_num
      have hd_ge : 256 ≤ d := by rw [hd_val, hy6]; norm_num; omega
      have hd_le : (d : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 1 / 4 := (hpow_anti 256 d (by omega) hd_ge).trans h256_14
      have h2 : w (qStep2M M (by omega) y) ≤ 1 := hw_le1 _
      have h2_nn : 0 ≤ w (qStep2M M (by omega) y) := by linarith [hw_ge (qStep2M M (by omega) y)]
      rw [hwy, hwH]
      calc (2 : ℝ) ^ (-(3 / 4 : ℝ)) * (3 / 4 + (d : ℝ) ^ (-(1 / 4 : ℝ)) * w (qStep2M M (by omega) y))
          ≤ (3 / 5 : ℝ) * (3 / 4 + (1 / 4 : ℝ) * 1) :=
            mul_le_mul h2_34_tight (add_le_add le_rfl (mul_le_mul hd_le h2 h2_nn (by norm_num)))
              (by positivity) (by norm_num)
        _ ≤ 2 / 3 := by norm_num
    · have hwy : w y = 2 / 3 := by simp [w, hy1, hy2, hy3]
      have hH_not : (hStep2M M (by omega) y).val ≠ 1 ∧
                    (hStep2M M (by omega) y).val ≠ 2 ∧
                    (hStep2M M (by omega) y).val ≠ 3 := by
        have h1 := hH_val y
        refine ⟨?_, ?_, ?_⟩ <;> intro heq <;> rw [heq] at h1
        · rw [Nat.mod_eq_of_lt (by omega)] at h1; exact hy2 h1.symm
        · rw [Nat.mod_eq_of_lt (by omega)] at h1; exact hy4 h1.symm
        · rw [Nat.mod_eq_of_lt (by omega)] at h1; exact hy6 h1.symm
      have hwH : w (hStep2M M (by omega) y) = 2 / 3 := by
        dsimp [w]; split_ifs <;> tauto
      have hd_ge5 : 5 ≤ d := by
        rw [hd_val]
        by_cases hpar : y.val % 2 = 1
        · simp only [hpar, ↓reduceIte]; omega
        · simp only [hpar, ↓reduceIte]; omega
      rw [hwy, hwH]
      by_cases hd25 : 25 ≤ d
      · have hd_le : (d : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 9 / 20 := (hpow_anti 25 d (by omega) hd25).trans h25_14
        have h2 : w (qStep2M M (by omega) y) ≤ 1 := hw_le1 _
        have h2_nn : 0 ≤ w (qStep2M M (by omega) y) := by linarith [hw_ge (qStep2M M (by omega) y)]
        calc (2 : ℝ) ^ (-(3 / 4 : ℝ)) * (2 / 3 + (d : ℝ) ^ (-(1 / 4 : ℝ)) * w (qStep2M M (by omega) y))
            ≤ (40 / 67 : ℝ) * (2 / 3 + (9 / 20 : ℝ) * 1) :=
              mul_le_mul h2_34 (add_le_add le_rfl (mul_le_mul hd_le h2 h2_nn (by norm_num)))
                (by positivity) (by norm_num)
          _ ≤ 2 / 3 := by norm_num
      · have hd_odd : d % 2 = 1 := by rw [hd_val]; split_ifs <;> omega
        have hd_le23 : d ≤ 23 := by omega
        have hdd_ev : d * d + 1 = 2 * ((d * d + 1) / 2) := by
          have : (d * d + 1) % 2 = 0 := by rw [Nat.add_mod, Nat.mul_mod, hd_odd]
          omega
        have hQ_ge : 13 ≤ (d * d + 1) / 2 := by nlinarith
        have hQ_lt : (d * d + 1) / 2 < M := by nlinarith
        have hQ_val : (qStep2M M (by omega) y).val = (d * d + 1) / 2 := by
          change ((d * d + 1) / 2) % M = (d * d + 1) / 2
          exact Nat.mod_eq_of_lt hQ_lt
        have hwQ : w (qStep2M M (by omega) y) = 2 / 3 := by
          dsimp [w]; rw [hQ_val]; split_ifs <;> first | rfl | omega
        have hd_le : (d : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 27 / 40 := (hpow_anti 5 d (by omega) hd_ge5).trans h5_14
        rw [hwQ]
        calc (2 : ℝ) ^ (-(3 / 4 : ℝ)) * (2 / 3 + (d : ℝ) ^ (-(1 / 4 : ℝ)) * (2 / 3))
            ≤ (40 / 67 : ℝ) * (2 / 3 + (27 / 40 : ℝ) * (2 / 3)) :=
              mul_le_mul h2_34 (by linarith) (by positivity) (by norm_num)
          _ = 2 / 3 := by norm_num
  have hQ0 : (qStep2M M (by omega) ⟨0, by omega⟩).val = (M + 1) / 2 := by
    simp only [qStep2M, qStepNat, oddDigitNat, Nat.zero_mod, zero_add]
    have hsplit : (M * M + 1) / 2 = M * ((M - 1) / 2) + (M + 1) / 2 := by
      set q0 := (M - 1) / 2
      have hM1 : M = 2 * q0 + 1 := by omega
      have hM2 : (M + 1) / 2 = q0 + 1 := by omega
      have : M * M + 1 = 2 * (M * q0 + (M + 1) / 2) := by
        rw [hM2, hM1]; ring
      omega
    rw [hsplit, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hwQ0 : w (qStep2M M (by omega) ⟨0, by omega⟩) = 2 / 3 := by
    dsimp [w]; rw [hQ0]; split_ifs <;> first | rfl | omega
  refine pos_2M_of_supermartingale (by omega) hModd (t := 1 / 4) (wmin := 2 / 3)
    (by norm_num) (by norm_num) w hw_ge hsub ?_
  rw [hwQ0, mul_div_cancel_right₀ _ (by norm_num : (2 / 3 : ℝ) ≠ 0)]
  conv_rhs => rw [← Real.one_rpow (1 / 4 : ℝ)]
  apply Real.rpow_lt_rpow (by positivity) _ (by norm_num)
  rw [div_lt_one (by exact_mod_cast (by omega : 0 < M))]
  exact_mod_cast (by omega : 2 < M)

/-- Generic pure-kernel `q`-th root supermartingale soundness theorem for finite odd `M ≥ 7`. -/
private lemma pos_2M_of_cert {M q S c2 wmin : ℕ} (hM7 : 7 ≤ M) (hModd : M % 2 = 1)
    (hq : 1 ≤ q) (hS : 1 ≤ S) (hwmin : 1 ≤ wmin)
    (cdFn : ℕ → ℕ) (wFn : ℕ → ℕ)
    (hc2 : S ^ q ≤ 2 ^ (q - 1) * c2 ^ q)
    (hcd : ∀ y < M, S ^ q ≤ oddDigitNat M y * (cdFn (oddDigitNat M y)) ^ q)
    (hw_ge : ∀ y < M, wmin ≤ wFn y)
    (hstep : ∀ y < M,
      c2 * (S * wFn (hStepNat M y) + cdFn (oddDigitNat M y) * wFn (qStepNat M y)) ≤
        S * S * wFn y)
    (hwit0 : 2 * (wFn ((M + 1) / 2)) ^ q < M * wmin ^ q) :
    ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ, 1 ≤ n → η ≤ p_k (2 * M) n := by
  let t : ℝ := 1 / (q : ℝ)
  have ht : 0 < t := by dsimp only [t]; positivity
  let w : Fin M → ℝ := fun y => (wFn y.val : ℝ)
  have hwminR : (0 : ℝ) < (wmin : ℝ) := by exact_mod_cast (by omega : 0 < wmin)
  have hwR_ge : ∀ y : Fin M, (wmin : ℝ) ≤ w y := fun y => by
    dsimp only [w]; exact_mod_cast hw_ge y.val y.isLt
  have hSR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast (by omega : 0 < S)
  have hc2_le : (2 : ℝ) ^ (t - 1) ≤ (c2 : ℝ) / (S : ℝ) := by
    have h1 := rpow_neg_le_of_pow_le (a := 2) (e := q - 1) (q := q) (c := c2) (S := S)
      (by omega) (by omega) (by omega) hc2
    have hexp : t - 1 = -(((q - 1 : ℕ) : ℝ) / (q : ℝ)) := by
      dsimp only [t]
      rw [Nat.cast_sub hq, Nat.cast_one]
      have : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
      field_simp; ring
    rwa [hexp]
  have hsub : ∀ y : Fin M,
      (2 : ℝ) ^ (t - 1) * (w (hStep2M M (by omega) y) +
        (oddDigit2M M y : ℝ) ^ (-t) * w (qStep2M M (by omega) y)) ≤ w y := by
    intro y
    have hd_pos : 0 < oddDigitNat M y.val := by
      unfold oddDigitNat
      by_cases h1 : y.val % 2 = 1
      · simp [h1]; omega
      · have hbeq : Nat.beq (y.val % 2) 1 = false := by
          cases hb : Nat.beq (y.val % 2) 1 with
          | false => rfl
          | true => exact absurd (Nat.eq_of_beq_eq_true hb) h1
        simp [hbeq]; omega
    have hcd_le : (oddDigit2M M y : ℝ) ^ (-t) ≤ (cdFn (oddDigitNat M y.val) : ℝ) / (S : ℝ) := by
      have h1 := rpow_neg_le_of_pow_le (a := oddDigitNat M y.val) (e := 1) (q := q)
        (c := cdFn (oddDigitNat M y.val)) (S := S) hd_pos (by omega) (by omega)
        (by simpa using hcd y.val y.isLt)
      simpa [t, oddDigit2M] using h1
    have hstR : (c2 : ℝ) * ((S : ℝ) * (wFn (hStepNat M y.val) : ℝ) +
        (cdFn (oddDigitNat M y.val) : ℝ) * (wFn (qStepNat M y.val) : ℝ)) ≤
        (S : ℝ) * (S : ℝ) * (wFn y.val : ℝ) := by exact_mod_cast hstep y.val y.isLt
    have hQ_nn : 0 ≤ w (qStep2M M (by omega) y) := by dsimp [w]; positivity
    calc (2 : ℝ) ^ (t - 1) * (w (hStep2M M (by omega) y) +
            (oddDigit2M M y : ℝ) ^ (-t) * w (qStep2M M (by omega) y))
        ≤ ((c2 : ℝ) / (S : ℝ)) * (w (hStep2M M (by omega) y) +
            ((cdFn (oddDigitNat M y.val) : ℝ) / (S : ℝ)) * w (qStep2M M (by omega) y)) :=
          mul_le_mul hc2_le
            (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcd_le hQ_nn))
            (by positivity) (by positivity)
      _ = ((c2 : ℝ) * ((S : ℝ) * (wFn (hStepNat M y.val) : ℝ) +
            (cdFn (oddDigitNat M y.val) : ℝ) * (wFn (qStepNat M y.val) : ℝ))) /
            ((S : ℝ) * (S : ℝ)) := by dsimp only [w, hStep2M, qStep2M]; field_simp
      _ ≤ ((S : ℝ) * (S : ℝ) * (wFn y.val : ℝ)) / ((S : ℝ) * (S : ℝ)) :=
          div_le_div_of_nonneg_right hstR (by positivity)
      _ = w y := by dsimp only [w]; field_simp
  have hQ0 : (qStep2M M (by omega) ⟨0, by omega⟩).val = (M + 1) / 2 := by
    simp only [qStep2M, qStepNat, oddDigitNat, Nat.zero_mod, zero_add]
    have hsplit : (M * M + 1) / 2 = M * ((M - 1) / 2) + (M + 1) / 2 := by
      set q0 := (M - 1) / 2
      have hM1 : M = 2 * q0 + 1 := by omega
      have hM2 : (M + 1) / 2 = q0 + 1 := by omega
      have : M * M + 1 = 2 * (M * q0 + (M + 1) / 2) := by
        rw [hM2, hM1]; ring
      omega
    rw [hsplit, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  refine pos_2M_of_supermartingale hM7 hModd ht hwminR w hwR_ge hsub ?_
  have hwQ0 : w (qStep2M M (by omega) ⟨0, by omega⟩) = (wFn ((M + 1) / 2) : ℝ) := by
    dsimp only [w]; rw [hQ0]
  rw [hwQ0]
  have hwitR : 2 * (wFn ((M + 1) / 2) : ℝ) ^ q < (M : ℝ) * (wmin : ℝ) ^ q := by exact_mod_cast hwit0
  have hpow : ((2 / (M : ℝ)) ^ t * (wFn ((M + 1) / 2) : ℝ) / (wmin : ℝ)) ^ q < (1 : ℝ) ^ q := by
    rw [one_pow, div_pow, mul_pow, ← Real.rpow_natCast ((2 / (M : ℝ)) ^ t) q,
        ← Real.rpow_mul (by positivity)]
    have htq : t * (q : ℝ) = 1 := by
      dsimp only [t]; exact one_div_mul_cancel (by exact_mod_cast (by omega : q ≠ 0))
    rw [htq, Real.rpow_one, div_lt_one (by positivity),
        show 2 / (M : ℝ) * (wFn ((M + 1) / 2) : ℝ) ^ q =
          (2 * (wFn ((M + 1) / 2) : ℝ) ^ q) / (M : ℝ) by ring,
        div_lt_iff₀ (by exact_mod_cast (by omega : 0 < M))]
    linarith
  exact lt_of_pow_lt_pow_left₀ q (by norm_num) hpow

/-- Fast 15-branch piecewise upper bound on `10000 * d^(-1/4)` for all `d ≥ 1`. -/
private def cd4Bound (d : ℕ) : ℕ :=
  if 256 ≤ d then 2500
  else if 160 ≤ d then 2812
  else if 100 ≤ d then 3163
  else if 64 ≤ d then 3536
  else if 45 ≤ d then 3861
  else if 33 ≤ d then 4173
  else if 25 ≤ d then 4473
  else if 19 ≤ d then 4790
  else if 15 ≤ d then 5082
  else if 11 ≤ d then 5492
  else if 9 ≤ d then 5774
  else if 7 ≤ d then 6148
  else if 5 ≤ d then 6688
  else if 3 ≤ d then 7599
  else 10000

private lemma cd4Bound_sound (d : ℕ) (hd : 1 ≤ d) : 10000 ^ 4 ≤ d * (cd4Bound d) ^ 4 := by
  unfold cd4Bound
  by_cases h1 : 256 ≤ d; · simp only [h1, ↓reduceIte]; nlinarith
  simp only [h1, ↓reduceIte]
  by_cases h2 : 160 ≤ d; · simp only [h2, ↓reduceIte]; nlinarith
  simp only [h2, ↓reduceIte]
  by_cases h3 : 100 ≤ d; · simp only [h3, ↓reduceIte]; nlinarith
  simp only [h3, ↓reduceIte]
  by_cases h4 : 64 ≤ d; · simp only [h4, ↓reduceIte]; nlinarith
  simp only [h4, ↓reduceIte]
  by_cases h5 : 45 ≤ d; · simp only [h5, ↓reduceIte]; nlinarith
  simp only [h5, ↓reduceIte]
  by_cases h6 : 33 ≤ d; · simp only [h6, ↓reduceIte]; nlinarith
  simp only [h6, ↓reduceIte]
  by_cases h7 : 25 ≤ d; · simp only [h7, ↓reduceIte]; nlinarith
  simp only [h7, ↓reduceIte]
  by_cases h8 : 19 ≤ d; · simp only [h8, ↓reduceIte]; nlinarith
  simp only [h8, ↓reduceIte]
  by_cases h9 : 15 ≤ d; · simp only [h9, ↓reduceIte]; nlinarith
  simp only [h9, ↓reduceIte]
  by_cases h10 : 11 ≤ d; · simp only [h10, ↓reduceIte]; nlinarith
  simp only [h10, ↓reduceIte]
  by_cases h11 : 9 ≤ d; · simp only [h11, ↓reduceIte]; nlinarith
  simp only [h11, ↓reduceIte]
  by_cases h12 : 7 ≤ d; · simp only [h12, ↓reduceIte]; nlinarith
  simp only [h12, ↓reduceIte]
  by_cases h13 : 5 ≤ d; · simp only [h13, ↓reduceIte]; nlinarith
  simp only [h13, ↓reduceIte]
  by_cases h14 : 3 ≤ d; · simp only [h14, ↓reduceIte]; nlinarith
  simp only [h14, ↓reduceIte]; nlinarith

/-- Single-state check for `(M, wmin, wFn)` at state `y < M` (`q = 4, S = 10000, c2 = 5947`). -/
private def check2M4At (M wmin : ℕ) (wFn : ℕ → ℕ) (y : ℕ) : Bool :=
  if M ≤ y then true
  else
    let d := oddDigitNat M y
    Nat.ble wmin (wFn y) &&
    Nat.ble (5947 * (10000 * wFn (hStepNat M y) + cd4Bound d * wFn (qStepNat M y)))
      (100000000 * wFn y)

/-- Binary-tree range checker `check2M4Pow2 M wmin wFn lo d` covering `[lo, lo + 2^d)`.
    Recursion depth is `d` (`≤ 9`), avoiding linear recursion depth limits in the kernel. -/
private def check2M4Pow2 (M wmin : ℕ) (wFn : ℕ → ℕ) : ℕ → ℕ → Bool
  | lo, 0 => check2M4At M wmin wFn lo
  | lo, d + 1 => check2M4Pow2 M wmin wFn lo d && check2M4Pow2 M wmin wFn (lo + 2 ^ d) d

private lemma check2M4Pow2_sound (M wmin : ℕ) (wFn : ℕ → ℕ) :
    ∀ d lo, check2M4Pow2 M wmin wFn lo d = true →
      ∀ y, lo ≤ y → y < lo + 2 ^ d → y < M →
        wmin ≤ wFn y ∧
          5947 * (10000 * wFn (hStepNat M y) + cd4Bound (oddDigitNat M y) * wFn (qStepNat M y)) ≤
            10000 * 10000 * wFn y := by
  intro d
  induction d with
  | zero =>
    intro lo h y hlo hhi hyM
    have heq : y = lo := by omega
    subst heq
    unfold check2M4Pow2 check2M4At at h
    have hnot : ¬ (M ≤ y) := by omega
    simp only [hnot, ↓reduceIte, Bool.and_eq_true, Nat.ble_eq] at h
    exact ⟨h.1, by simpa using h.2⟩
  | succ d ih =>
    intro lo h y hlo hhi hyM
    simp only [check2M4Pow2, Bool.and_eq_true] at h
    by_cases hlt : y < lo + 2 ^ d
    · exact ih lo h.1 y hlo hlt hyM
    · exact ih (lo + 2 ^ d) h.2 y (by omega) (by rw [pow_succ] at hhi; omega) hyM

private def check2M4 (M wmin : ℕ) (wFn : ℕ → ℕ) : Bool :=
  Nat.ble 1 wmin &&
  Nat.ble (2 * (wFn ((M + 1) / 2)) ^ 4 + 1) (M * wmin ^ 4) &&
  check2M4Pow2 M wmin wFn 0 9

private lemma pos_2M_of_check2M4 {M wmin : ℕ} (hM7 : 7 ≤ M) (hMlt : M ≤ 512) (hModd : M % 2 = 1)
    (wFn : ℕ → ℕ) (h : check2M4 M wmin wFn = true) :
    ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ, 1 ≤ n → η ≤ p_k (2 * M) n := by
  simp only [check2M4, Bool.and_eq_true, Nat.ble_eq] at h
  have hloop := check2M4Pow2_sound M wmin wFn 9 0 h.2
  refine pos_2M_of_cert hM7 hModd (q := 4) (S := 10000) (c2 := 5947) (wmin := wmin)
    (by omega) (by omega) h.1.1 cd4Bound wFn (by decide)
    (fun y hy => cd4Bound_sound _ (by
      unfold oddDigitNat
      by_cases h1 : y % 2 = 1
      · simp [h1]; omega
      · have hbeq : Nat.beq (y % 2) 1 = false := by
          cases hb : Nat.beq (y % 2) 1 with
          | false => rfl
          | true => exact absurd (Nat.eq_of_beq_eq_true hb) h1
        simp [hbeq]; omega))
    (fun y hy => (hloop y (Nat.zero_le _) (by omega) hy).1)
    (fun y hy => (hloop y (Nat.zero_le _) (by omega) hy).2)
    (by omega)

/-- 3-exception weight function `w3` scaled by `60` (`60, 48, 45, 40`). -/
private def w3Nat (y : ℕ) : ℕ :=
  match y with
  | 1 => 60
  | 2 => 48
  | 3 => 45
  | _ => 40

/-- List of the 12 odd moduli `M ∈ [7, 265]` requiring dedicated supermartingale vectors. -/
private def specialMs : List ℕ := [7, 9, 11, 13, 15, 21, 23, 33, 35, 39, 45, 55]

private def checkW3At (i : ℕ) : Bool :=
  if 130 ≤ i then true
  else
    let M := 2 * i + 7
    if specialMs.contains M then true else check2M4 M 40 w3Nat

/-- Binary-tree batch checker covering `i ∈ [lo, lo + 2^d)` for `7 ≤ M = 2*i + 7 ≤ 265`. -/
private def checkW3Pow2 : ℕ → ℕ → Bool
  | lo, 0 => checkW3At lo
  | lo, d + 1 => checkW3Pow2 lo d && checkW3Pow2 (lo + 2 ^ d) d

private theorem checkW3Shard_0 : checkW3Pow2 0 5 = true := rfl
private theorem checkW3Shard_1 : checkW3Pow2 32 5 = true := rfl
private theorem checkW3Shard_2 : checkW3Pow2 64 5 = true := rfl
private theorem checkW3Shard_3 : checkW3Pow2 96 5 = true := rfl
private theorem checkW3Shard_4 : checkW3Pow2 128 2 = true := rfl

private lemma checkW3Pow2_sound :
    ∀ d lo, checkW3Pow2 lo d = true →
      ∀ i, lo ≤ i → i < lo + 2 ^ d → i < 130 →
        specialMs.contains (2 * i + 7) = false → check2M4 (2 * i + 7) 40 w3Nat = true := by
  intro d
  induction d with
  | zero =>
    intro lo h i hlo hhi hi hnot
    have heq : i = lo := by omega
    subst heq
    unfold checkW3Pow2 checkW3At at h
    have hlt : ¬ (130 ≤ i) := by omega
    simp only [hlt, ↓reduceIte, hnot, Bool.false_eq_true] at h
    exact h
  | succ d ih =>
    intro lo h i hlo hhi hi hnot
    simp only [checkW3Pow2, Bool.and_eq_true] at h
    by_cases hlt : i < lo + 2 ^ d
    · exact ih lo h.1 i hlo hlt hi hnot
    · exact ih (lo + 2 ^ d) h.2 i (by omega) (by rw [pow_succ] at hhi; omega) hi hnot

private lemma checkW3Range_all (i : ℕ) (hi : i < 130)
    (hnot : specialMs.contains (2 * i + 7) = false) :
    check2M4 (2 * i + 7) 40 w3Nat = true := by
  by_cases h0 : i < 32
  · exact checkW3Pow2_sound 5 0 checkW3Shard_0 i (by omega) (by omega) hi hnot
  by_cases h1 : i < 64
  · exact checkW3Pow2_sound 5 32 checkW3Shard_1 i (by omega) (by omega) hi hnot
  by_cases h2 : i < 96
  · exact checkW3Pow2_sound 5 64 checkW3Shard_2 i (by omega) (by omega) hi hnot
  by_cases h3 : i < 128
  · exact checkW3Pow2_sound 5 96 checkW3Shard_3 i (by omega) (by omega) hi hnot
  · exact checkW3Pow2_sound 2 128 checkW3Shard_4 i (by omega) (by omega) hi hnot

private def wVec11 : List ℕ := [549, 1000, 798, 705, 696, 694, 661, 644, 619, 636, 699]
private def wVec13 : List ℕ := [527, 1000, 839, 697, 775, 652, 628, 617, 632, 702, 588, 650, 665]
private def wVec15 : List ℕ := [508, 1000, 766, 589, 772, 528, 563, 607, 614, 550, 481, 684, 492, 555, 643]
private def wVec21 : List ℕ :=
  [467, 1000, 824, 693, 686, 717, 628, 620, 701, 585, 610, 593, 560, 685, 566, 567, 614, 564,
   547, 602, 631]
private def wVec23 : List ℕ :=
  [457, 1000, 816, 652, 677, 608, 612, 671, 596, 584, 557, 547, 539, 542, 573, 531, 600, 550,
   519, 529, 516, 568, 606]
private def wVec33 : List ℕ :=
  [417, 1000, 799, 640, 659, 591, 636, 563, 575, 590, 650, 445, 580, 584, 507, 518, 528, 508,
   517, 500, 554, 557, 411, 617, 523, 479, 502, 552, 474, 486, 482, 527, 583]
private def wVec35 : List ℕ :=
  [411, 1000, 786, 599, 651, 516, 661, 463, 557, 566, 470, 533, 553, 489, 442, 477, 535, 490,
   504, 509, 448, 429, 470, 537, 484, 434, 482, 448, 396, 603, 432, 465, 475, 494, 556]
private def wVec39 : List ℕ :=
  [400, 1000, 811, 639, 684, 595, 572, 569, 590, 632, 519, 615, 539, 523, 628, 510, 513, 544,
   540, 508, 497, 504, 541, 469, 479, 623, 483, 510, 546, 461, 529, 482, 486, 489, 483, 500,
   496, 524, 565]
private def wVec45 : List ℕ :=
  [386, 1000, 799, 571, 685, 512, 514, 566, 589, 495, 469, 522, 481, 471, 519, 440, 536, 518,
   465, 646, 439, 452, 456, 457, 443, 431, 560, 448, 466, 472, 408, 524, 463, 436, 479, 411,
   428, 456, 542, 422, 408, 474, 425, 484, 537]
private def wVec55 : List ℕ :=
  [367, 1000, 820, 673, 679, 607, 568, 500, 621, 499, 531, 528, 501, 565, 474, 573, 528, 470,
   462, 467, 515, 624, 475, 448, 449, 486, 494, 449, 440, 509, 496, 421, 467, 449, 552, 483,
   439, 419, 432, 445, 507, 435, 543, 422, 455, 440, 407, 478, 418, 436, 460, 457, 474, 493, 527]

private theorem checkM11_ok : check2M4 11 549 (fun y => wVec11.getD y 0) = true := rfl
private theorem checkM13_ok : check2M4 13 527 (fun y => wVec13.getD y 0) = true := rfl
private theorem checkM15_ok : check2M4 15 481 (fun y => wVec15.getD y 0) = true := rfl
private theorem checkM21_ok : check2M4 21 467 (fun y => wVec21.getD y 0) = true := rfl
private theorem checkM23_ok : check2M4 23 457 (fun y => wVec23.getD y 0) = true := rfl
private theorem checkM33_ok : check2M4 33 411 (fun y => wVec33.getD y 0) = true := rfl
private theorem checkM35_ok : check2M4 35 396 (fun y => wVec35.getD y 0) = true := rfl
private theorem checkM39_ok : check2M4 39 400 (fun y => wVec39.getD y 0) = true := rfl
private theorem checkM45_ok : check2M4 45 386 (fun y => wVec45.getD y 0) = true := rfl
private theorem checkM55_ok : check2M4 55 367 (fun y => wVec55.getD y 0) = true := rfl

private def wVec9 : List ℕ := [760, 1000, 883, 815, 812, 813, 769, 811, 835]
private def cdVec9 : List ℕ := [10000, 8717, 8178, 7841, 7599, 7411, 7257, 7129, 7018]

private lemma pos_base18 : ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ, 1 ≤ n → η ≤ p_k (2 * 9) n := by
  refine pos_2M_of_cert (M := 9) (q := 8) (S := 10000) (c2 := 5453) (wmin := 760)
    (by omega) (by decide) (by omega) (by omega) (by omega)
    (fun d => cdVec9.getD (d / 2) 10000) (fun y => wVec9.getD y 0)
    (by decide) ?_ ?_ ?_ (by decide)
  · intro y hy; interval_cases y <;> decide
  · intro y hy; interval_cases y <;> decide
  · intro y hy; interval_cases y <;> decide

private def wVec7 : List ℕ := [8855, 10000, 9487, 9408, 9144, 9315, 9364]
private def cdVec7 : List ℕ := [100000, 93365, 90431, 88549, 87169, 86083, 85189]

private lemma pos_base14 : ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ, 1 ≤ n → η ≤ p_k (2 * 7) n := by
  refine pos_2M_of_cert (M := 7) (q := 16) (S := 100000) (c2 := 52214) (wmin := 8855)
    (by omega) (by decide) (by omega) (by omega) (by omega)
    (fun d => cdVec7.getD (d / 2) 100000) (fun y => wVec7.getD y 0)
    (by decide) ?_ ?_ ?_ (by decide)
  · intro y hy; interval_cases y <;> decide
  · intro y hy; interval_cases y <;> decide
  · intro y hy; interval_cases y <;> decide

/-- Positive uniform stopping-density lower bound for EVERY `b = 2M` with `M ≥ 7` odd. -/
theorem pos_all_2M {M : ℕ} (hM7 : 7 ≤ M) (hModd : M % 2 = 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ n : ℕ, 1 ≤ n → η ≤ p_k (2 * M) n := by
  by_cases hge : 267 ≤ M
  · exact pos_2M_ge_267 hge hModd
  by_cases h7 : M = 7
  · subst h7; exact pos_base14
  by_cases h9 : M = 9
  · subst h9; exact pos_base18
  by_cases h11 : M = 11
  · subst h11; exact pos_2M_of_check2M4 (by omega) (by omega) (by decide) _ checkM11_ok
  by_cases h13 : M = 13
  · subst h13; exact pos_2M_of_check2M4 (by omega) (by omega) (by decide) _ checkM13_ok
  by_cases h15 : M = 15
  · subst h15; exact pos_2M_of_check2M4 (by omega) (by omega) (by decide) _ checkM15_ok
  by_cases h21 : M = 21
  · subst h21; exact pos_2M_of_check2M4 (by omega) (by omega) (by decide) _ checkM21_ok
  by_cases h23 : M = 23
  · subst h23; exact pos_2M_of_check2M4 (by omega) (by omega) (by decide) _ checkM23_ok
  by_cases h33 : M = 33
  · subst h33; exact pos_2M_of_check2M4 (by omega) (by omega) (by decide) _ checkM33_ok
  by_cases h35 : M = 35
  · subst h35; exact pos_2M_of_check2M4 (by omega) (by omega) (by decide) _ checkM35_ok
  by_cases h39 : M = 39
  · subst h39; exact pos_2M_of_check2M4 (by omega) (by omega) (by decide) _ checkM39_ok
  by_cases h45 : M = 45
  · subst h45; exact pos_2M_of_check2M4 (by omega) (by omega) (by decide) _ checkM45_ok
  by_cases h55 : M = 55
  · subst h55; exact pos_2M_of_check2M4 (by omega) (by omega) (by decide) _ checkM55_ok
  · let i := (M - 7) / 2
    have hMeq : 2 * i + 7 = M := by dsimp only [i]; omega
    have hi : i < 130 := by dsimp only [i]; omega
    have hnot : specialMs.contains M = false := by
      simp [specialMs, h7, h9, h11, h13, h15, h21, h23, h33, h35, h39, h45, h55]
    have hok := checkW3Range_all i hi (by rwa [hMeq])
    rw [hMeq] at hok
    exact pos_2M_of_check2M4 hM7 (by omega) hModd w3Nat hok

/-! ## Section 6: Main Theorem 11 (`thm:even-stopping`) -/

/-- **Positive uniform lower bound (`thm:even-stopping`, positive-drift direction)**:
    for every even base `b ≥ 2` with `b ∉ {2, 4, 6, 10}`, there exists `η > 0` such that
    `p_k(b) ≥ η` for all `k ≥ 1`. -/
theorem p_k_pos_lower_bound {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0)
    (hne2 : b ≠ 2) (hne4 : b ≠ 4) (hne6 : b ≠ 6) (hne10 : b ≠ 10) :
    ∃ η : ℝ, 0 < η ∧ ∀ k : ℕ, 1 ≤ k → η ≤ p_k b k := by
  by_cases h4 : 4 ∣ b
  · obtain ⟨k, rfl⟩ := h4
    exact pos_all_4k (by omega)
  · have hM_odd : (b / 2) % 2 = 1 := by omega
    have hM7 : 7 ≤ b / 2 := by omega
    have hb_eq : 2 * (b / 2) = b := by omega
    simpa [hb_eq] using pos_all_2M hM7 hM_odd

/-- **Non-descent dichotomy (`thm:even-stopping`)**:
    for every even base `b ≥ 2`, `p_infty(b) = 0 ↔ b ∈ {2, 4, 6, 10}`. -/
theorem p_infty_eq_zero_iff {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) :
    p_infty b = 0 ↔ b = 2 ∨ b = 4 ∨ b = 6 ∨ b = 10 := by
  constructor
  · intro h0
    by_contra hnot
    push Not at hnot
    obtain ⟨hne2, hne4, hne6, hne10⟩ := hnot
    obtain ⟨η, hη, hlb⟩ := p_k_pos_lower_bound hb2 hbeven hne2 hne4 hne6 hne10
    have hle : η ≤ p_infty b := le_ciInf fun k => hlb (k + 1) (by omega)
    linarith
  · rintro (rfl | rfl | rfl | rfl)
    · exact p_infty_base2
    · exact p_infty_base4
    · exact p_infty_base6
    · exact p_infty_base10

/-- **Density-one descent in bases `{2, 4, 6, 10}` (`thm:even-stopping`)**. -/
theorem descent_density_one_of_mem {b : ℕ} (hb : b = 2 ∨ b = 4 ∨ b = 6 ∨ b = 10) :
    HasNaturalDensity (DescentSet b) 1 := by
  rcases hb with rfl | rfl | rfl | rfl
  · exact descent_density_one_of_p_infty_zero (by omega) (by decide) p_infty_base2
  · exact descent_density_one_of_p_infty_zero (by omega) (by decide) p_infty_base4
  · exact descent_density_one_of_p_infty_zero (by omega) (by decide) p_infty_base6
  · exact descent_density_one_of_p_infty_zero (by omega) (by decide) p_infty_base10

/-- **Theorem 11 (`thm:even-stopping`, complete statement)**:
    For every even base `b ≥ 2`:
    1. Every finite-horizon non-descent density `p_k(b) = d(D_k(b))` (`k ≥ 1`) exists.
    2. `p_k(b) → p_infty(b)` as `k → ∞`.
    3. `p_infty(b) = 0 ↔ b ∈ {2, 4, 6, 10}`.
    4. If `b ∈ {2, 4, 6, 10}`, then `DescentSet b` has natural density `1`.
    5. If `b ∉ {2, 4, 6, 10}`, then `∃ η > 0, ∀ k ≥ 1, η ≤ p_k(b)`. -/
theorem thm_even_stopping {b : ℕ} (hb2 : 2 ≤ b) (hbeven : b % 2 = 0) :
    (∀ k : ℕ, 1 ≤ k → HasNaturalDensity (D_k b k) (p_k b k)) ∧
    Filter.Tendsto (fun k : ℕ => p_k b (k + 1)) Filter.atTop (nhds (p_infty b)) ∧
    (p_infty b = 0 ↔ b = 2 ∨ b = 4 ∨ b = 6 ∨ b = 10) ∧
    ((b = 2 ∨ b = 4 ∨ b = 6 ∨ b = 10) → HasNaturalDensity (DescentSet b) 1) ∧
    ((b ≠ 2 ∧ b ≠ 4 ∧ b ≠ 6 ∧ b ≠ 10) → ∃ η : ℝ, 0 < η ∧ ∀ k : ℕ, 1 ≤ k → η ≤ p_k b k) :=
  ⟨fun _ hk => p_k_density hb2 hbeven hk,
   p_k_tendsto_p_infty hb2 hbeven,
   p_infty_eq_zero_iff hb2 hbeven,
   descent_density_one_of_mem,
   fun ⟨h2, h4, h6, h10⟩ => p_k_pos_lower_bound hb2 hbeven h2 h4 h6 h10⟩

end Ouroboros
