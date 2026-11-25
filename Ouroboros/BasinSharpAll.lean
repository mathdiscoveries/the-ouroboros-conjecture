module
public import Ouroboros.CantorClosure
public import Ouroboros.BasinOneSharp
public import Ouroboros.BasinOneUpperSharp
public import Ouroboros.WeightedCharging

@[expose] public section

/-!
# Complete Theorem 8 (`thm:basin-sharp`) Master Bundle

Composes the three independently audited pure-kernel components of Theorem 8 (`thm:basin-sharp`)
together with `Ouroboros.CantorClosure` into a single self-contained master declaration
`Ouroboros.thm_basin_sharp` (closing YELLOW-1 and YELLOW-2 of Blind Referee #8):

1. **Part 1a (`Ouroboros.BasinOneSharp`)**: for every real `X ≥ 1`,
   `0.0806 * (X / 31)^{399/800} ≤ N_1(⌊X⌋)` and `0.0145 * X^{399/800} ≤ N_1(⌊X⌋)`.
2. **Part 1b (`Ouroboros.BasinOneUpperSharp`)**: there exists `C > 0` such that for every
   real `X ≥ 1`, `N_1(⌊X⌋) ≤ C * X^{0.6245}`.
3. **2-adic / Archimedean strict separation (`Ouroboros.CantorClosure` + `BasinOneUpperSharp`)**:
   real-variable `limsup_{X → ∞} (log N_1(⌊X⌋) / log X) ≤ 0.6245 < β`,
   `0.626382135 < β < 0.626382145`, `dimH (closure B1Padic) = ENNReal.ofReal β`,
   and `ENNReal.ofReal 0.6245 < dimH (closure B1Padic)`.
4. **Part 2 (`Ouroboros.WeightedCharging`)**: for every integer `X ≥ 3`,
   `(98959 / (2269527 * 3^{13/20})) * X^{13/20} ≤ N_5(X)` and
   `0.02134 * X^{13/20} < N_5(X)`.
5. **Sharpened basin separation (`Ouroboros.BasinOneUpperSharp`)**: there exists `C > 0` such that
   for every integer `X ≥ 3`, `N_1(X) / N_5(X) ≤ C * X^{-0.0255}`.
-/

namespace Ouroboros

/-- Real-variable Archimedean upper exponent bound:
    `limsup_{X → ∞} (log N_1(⌊X⌋) / log X) ≤ betaPrime (= 0.6245)`. -/
theorem cor_basin1_archimedean_limsup_real :
    Filter.limsup (fun X : ℝ => Real.log (N1 ⌊X⌋₊ : ℝ) / Real.log X) Filter.atTop ≤ betaPrime := by
  classical
  obtain ⟨C, hC, hbound⟩ := thm_basin1_upper_sharp_real
  have hN1_ge1 : ∀ X : ℝ, 2 ≤ X → (1 : ℝ) ≤ (N1 ⌊X⌋₊ : ℝ) := by
    intro X hX
    have hfl1 : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by push_cast; linarith)
    have h1_mem : 1 ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n => n % 2 = 1 ∧ Reaches f n 1) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨le_rfl, hfl1⟩, by decide, reaches_refl f 1⟩
    have hcard : 1 ≤ N1 ⌊X⌋₊ := Finset.card_pos.mpr ⟨1, h1_mem⟩
    exact_mod_cast hcard
  have hev_le : ∀ᶠ X : ℝ in Filter.atTop,
      Real.log (N1 ⌊X⌋₊ : ℝ) / Real.log X ≤ Real.log C / Real.log X + betaPrime := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with X hX
    have hX_pos : (0 : ℝ) < X := by linarith
    have hlogX_pos : 0 < Real.log X := Real.log_pos (by linarith)
    have hN1_pos : (0 : ℝ) < (N1 ⌊X⌋₊ : ℝ) := lt_of_lt_of_le zero_lt_one (hN1_ge1 X hX)
    have hup := hbound X (by linarith)
    have hlog_le : Real.log (N1 ⌊X⌋₊ : ℝ) ≤ Real.log (C * X ^ betaPrime) :=
      Real.log_le_log hN1_pos hup
    rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hX_pos _).ne',
        Real.log_rpow hX_pos] at hlog_le
    rw [div_le_iff₀ hlogX_pos]
    have hrew : (Real.log C / Real.log X + betaPrime) * Real.log X =
        Real.log C + betaPrime * Real.log X := by
      have hne : Real.log X ≠ 0 := hlogX_pos.ne'
      field_simp
    linarith
  have hev_ge0 : ∀ᶠ X : ℝ in Filter.atTop,
      (0 : ℝ) ≤ Real.log (N1 ⌊X⌋₊ : ℝ) / Real.log X := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with X hX
    have hlogX_pos : 0 < Real.log X := Real.log_pos (by linarith)
    exact div_nonneg (Real.log_nonneg (hN1_ge1 X hX)) hlogX_pos.le
  have htend_rhs : Filter.Tendsto
      (fun X : ℝ => Real.log C / Real.log X + betaPrime)
      Filter.atTop (nhds betaPrime) := by
    have hdiv0 : Filter.Tendsto (fun X : ℝ => Real.log C / Real.log X) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    simpa using hdiv0.add tendsto_const_nhds
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun X : ℝ => Real.log (N1 ⌊X⌋₊ : ℝ) / Real.log X) :=
    Filter.isCoboundedUnder_le_of_eventually_le Filter.atTop hev_ge0
  have hbdd_rhs : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun X : ℝ => Real.log C / Real.log X + betaPrime) :=
    htend_rhs.isBoundedUnder_le
  calc Filter.limsup (fun X : ℝ => Real.log (N1 ⌊X⌋₊ : ℝ) / Real.log X) Filter.atTop
      ≤ Filter.limsup (fun X : ℝ => Real.log C / Real.log X + betaPrime) Filter.atTop :=
        Filter.limsup_le_limsup hev_le hcobdd hbdd_rhs
    _ = betaPrime := htend_rhs.limsup_eq

/-- Strict Hausdorff-dimension separation in `ℝ≥0∞`:
    `ENNReal.ofReal betaPrime < dimH (closure B1Padic)`. -/
theorem cor_basin1_dimH_lt :
    ENNReal.ofReal betaPrime < dimH (closure B1Padic) := by
  rw [dimH_closure_B1Padic]
  have hbeta_pos : 0 < beta := by linarith [beta_bounds.1]
  exact (ENNReal.ofReal_lt_ofReal_iff hbeta_pos).mpr cor_basin1_archimedean_lt_2adic.2

/-- Complete Theorem 8 (`thm:basin-sharp`): sharpened Archimedean lower and upper bounds on
    `N_1(X)`, strict separation from the 2-adic Hausdorff dimension `dimH (closure B1Padic)`,
    sharpened weighted-charging lower bound on `N_5(X)`, and ratio bound `N_1(X)/N_5(X) = O(X^{-0.0255})`. -/
theorem thm_basin_sharp :
    (∀ X : ℝ, 1 ≤ X →
      (806 / 10000 : ℝ) * (X / 31) ^ ((399 : ℝ) / 800) ≤ (N1 ⌊X⌋₊ : ℝ) ∧
      (145 / 10000 : ℝ) * X ^ ((399 : ℝ) / 800) ≤ (N1 ⌊X⌋₊ : ℝ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → (N1 ⌊X⌋₊ : ℝ) ≤ C * X ^ betaPrime) ∧
    (Filter.limsup (fun X : ℝ => Real.log (N1 ⌊X⌋₊ : ℝ) / Real.log X) Filter.atTop ≤ betaPrime ∧
      betaPrime < beta ∧
      (626382135 / 1000000000 : ℝ) < beta ∧ beta < (626382145 / 1000000000 : ℝ) ∧
      dimH (closure B1Padic) = ENNReal.ofReal beta ∧
      ENNReal.ofReal betaPrime < dimH (closure B1Padic)) ∧
    (∀ X : ℕ, 3 ≤ X →
      ((98959 : ℝ) / ((2269527 : ℝ) * (3 : ℝ) ^ ((13 : ℝ) / 20))) * (X : ℝ) ^ ((13 : ℝ) / 20) ≤
        (N5 X : ℝ) ∧
      (2134 / 100000 : ℝ) * (X : ℝ) ^ ((13 : ℝ) / 20) < (N5 X : ℝ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 3 ≤ X →
      (N1 X : ℝ) / (N5 X : ℝ) ≤ C * (X : ℝ) ^ (-(255 : ℝ) / 10000)) :=
  ⟨thm_basin1_sharp_lower_real,
   thm_basin1_upper_sharp_real,
   ⟨cor_basin1_archimedean_limsup_real, cor_basin1_archimedean_lt_2adic.2,
    beta_bounds_8.1, beta_bounds_8.2, dimH_closure_B1Padic, cor_basin1_dimH_lt⟩,
   fun X hX => ⟨thm_basin5_sharp X hX, thm_basin5_sharp_gt X hX⟩,
   cor_basin_separation_sharp⟩

end Ouroboros
