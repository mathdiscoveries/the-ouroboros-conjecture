module
@[expose] public section

/-! # Pure-kernel finite-case certificate for `thm:even-bases` and `prop:near-zero` -/

namespace Ouroboros.EvenBasesCert
/-- Binary-squaring power with fuel `f`, avoiding Lean's `256`-exponent literal threshold. -/
def powBin (a : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | f + 1, n =>
    match Nat.beq n 0 with
    | true => 1
    | false =>
      let h := powBin a f (n / 2)
      match Nat.beq (n % 2) 0 with
      | true => h * h
      | false => a * (h * h)

theorem powBin_eq_pow (a : Nat) : ∀ f n, n < 2 ^ f → powBin a f n = a ^ n := by
  intro f
  induction f with
  | zero =>
    intro n hn; have hn0 : n = 0 := by omega
    subst hn0; rfl
  | succ f ih =>
    intro n hn; unfold powBin
    cases hb : Nat.beq n 0 with
    | true =>
      have hn0 : n = 0 := Nat.eq_of_beq_eq_true hb
      subst hn0; rfl
    | false =>
      have hn_half : n / 2 < 2 ^ f := by
        have : 2 ^ (f + 1) = 2 * 2 ^ f := by rw [Nat.pow_succ, Nat.mul_comm]
        omega
      have hrec := ih (n / 2) hn_half
      dsimp only
      rw [hrec]
      cases hp : Nat.beq (n % 2) 0 with
      | true =>
        have hpar : n % 2 = 0 := Nat.eq_of_beq_eq_true hp; have heq : n = n / 2 + n / 2 := by omega
        rw [← Nat.pow_add, ← heq]
      | false =>
        have hne : n % 2 ≠ 0 := by intro h0; rw [h0] at hp; exact Bool.false_ne_true (hp.symm.trans (Nat.beq_refl 0))
        have heq : n = (n / 2 + n / 2) + 1 := by omega
        dsimp only
        rw [← Nat.pow_add, Nat.mul_comm a, ← Nat.pow_succ]; rw [show (n / 2 + n / 2).succ = n by omega]
/-- Integer table `k_i = ⌊100 * ln(2*i + 1) / (100 * ln(100/99))⌋` for `0 ≤ i < 103`. -/
def kTable : List Nat :=
  [0, 109, 160, 193, 218, 238, 255, 269, 281, 292, 302, 311, 320, 327, 335, 341, 347, 353, 359,
   364, 369, 374, 378, 383, 387, 391, 395, 398, 402, 405, 409, 412, 415, 418, 421, 424, 426, 429,
   432, 434, 437, 439, 442, 444, 446, 448, 450, 453, 455, 457, 459, 461, 463, 464, 466, 468, 470,
   472, 473, 475, 477, 478, 480, 481, 483, 485, 486, 488, 489, 490, 492, 493, 495, 496, 497, 499,
   500, 501, 503, 504, 505, 506, 508, 509, 510, 511, 512, 513, 515, 516, 517, 518, 519, 520, 521,
   522, 523, 524, 525, 526, 527, 528, 529]

def kVal (i : Nat) : Nat := kTable.getD i 0
def checkKTable : Nat → List Nat → Bool
  | _, [] => true
  | i, k :: ks =>
    Nat.ble k 1023 && Nat.ble (powBin 100 10 k) ((2 * i + 1) * powBin 99 10 k) &&
      checkKTable (i + 1) ks

theorem checkKTable_true : checkKTable 0 kTable = true := rfl
theorem checkKTable_sound :
    ∀ (l : List Nat) (off i : Nat),
      checkKTable off l = true → i < l.length →
        100 ^ (l.getD i 0) ≤ (2 * (off + i) + 1) * 99 ^ (l.getD i 0) := by
  intro l
  induction l with
  | nil => intro _ i _ hi; simp at hi
  | cons k ks ih =>
    intro off i h hi
    simp only [checkKTable, Bool.and_eq_true, Nat.ble_eq] at h
    cases i with
    | zero =>
      have hk_lt : k < 2 ^ 10 := by omega
      have h100 := powBin_eq_pow 100 10 k hk_lt; have h99 := powBin_eq_pow 99 10 k hk_lt; have hle := h.1.2
      rw [h100, h99] at hle
      simpa [List.getD] using hle
    | succ i =>
      have hi' : i < ks.length := by simp at hi; omega
      have hrec := ih (off + 1) i h.2 hi'
      have hidx : (k :: ks).getD (i + 1) 0 = ks.getD i 0 := rfl
      rw [hidx, show off + (i + 1) = off + 1 + i by omega]
      exact hrec

theorem kVal_sound (i : Nat) (hi : i < 103) : 100 ^ kVal i ≤ (2 * i + 1) * 99 ^ kVal i := by
  have h := checkKTable_sound kTable 0 i checkKTable_true hi
  simpa [kVal] using h
/-- Unique odd digit in `[1, 2M)` congruent to `y (mod M)` for odd `M`. -/
def oddDigitNat (M y : Nat) : Nat :=
  match Nat.beq (y % 2) 1 with
  | true => y
  | false => y + M
/-- Multiplication by `2⁻¹ (mod M)` for odd `M`. -/
def hStepNat (M y : Nat) : Nat := (y * ((M + 1) / 2)) % M
/-- Odd-step transition `(d(y)^2 + 1) / 2 (mod M)` for odd `M`. -/
def qStepNat (M y : Nat) : Nat :=
  let d := oddDigitNat M y
  ((d * d + 1) / 2) % M
/-- Unscaled integer iterate `uIter M i y = 2^i * (K_M^i u_0)(y)`. -/
def uIter (M : Nat) : Nat → Nat → Nat
  | 0, y => kVal (oddDigitNat M y / 2)
  | i + 1, y => uIter M i (hStepNat M y) + uIter M i (qStepNat M y)
/-- List-based fast pure-kernel evaluation of `uIter` and the scaled path sum -/
def initU (M : Nat) : List Nat := (List.range M).map fun y => kVal (oddDigitNat M y / 2)

def stepU (M : Nat) (u : List Nat) : List Nat :=
  (List.range M).map fun y => u.getD (hStepNat M y) 0 + u.getD (qStepNat M y) 0

def stepAcc (acc u : List Nat) : List Nat := List.zipWith (fun a v => 2 * a + v) acc u

def runK (M : Nat) : Nat → List Nat → List Nat → List Nat
  | 0, _, acc => acc
  | n + 1, u, acc =>
    let u' := stepU M u
    runK M n u' (stepAcc acc u')

def allGt (bound : Nat) : List Nat → Bool
  | [] => true
  | x :: xs => Nat.ble (bound + 1) x && allGt bound xs

def checkOneM (M L rhsMult : Nat) : Bool :=
  let u0 := initU M
  allGt (rhsMult * L * 2 ^ (L - 1)) (runK M (L - 1) u0 u0)
/-- Pure-kernel check at `M = 7` (`b = 14`, `L = 29`, `rhs = 139`): drift `> 0`. -/
theorem checkM7_pos : checkOneM 7 29 139 = true := rfl
theorem checkM9 : checkOneM 9 24 164 = true := rfl
theorem checkM11 : checkOneM 11 13 164 = true := rfl
theorem checkM13 : checkOneM 13 9 164 = true := rfl
theorem checkM15 : checkOneM 15 6 164 = true := rfl
theorem checkM17 : checkOneM 17 6 164 = true := rfl
theorem checkM19 : checkOneM 19 6 164 = true := rfl
theorem checkM21 : checkOneM 21 6 164 = true := rfl
theorem checkM23 : checkOneM 23 5 164 = true := rfl
theorem checkM25 : checkOneM 25 5 164 = true := rfl
theorem checkM27 : checkOneM 27 4 164 = true := rfl
theorem checkM29 : checkOneM 29 5 164 = true := rfl
theorem checkM31 : checkOneM 31 4 164 = true := rfl
theorem checkM33 : checkOneM 33 5 164 = true := rfl
theorem checkM35 : checkOneM 35 4 164 = true := rfl
theorem checkM37 : checkOneM 37 4 164 = true := rfl
theorem checkM39 : checkOneM 39 4 164 = true := rfl
theorem checkM41 : checkOneM 41 4 164 = true := rfl
theorem checkM43 : checkOneM 43 4 164 = true := rfl
theorem checkM45 : checkOneM 45 4 164 = true := rfl
theorem checkM47 : checkOneM 47 3 164 = true := rfl
theorem checkM49 : checkOneM 49 4 164 = true := rfl
theorem checkM51 : checkOneM 51 4 164 = true := rfl
theorem checkM53 : checkOneM 53 4 164 = true := rfl
theorem checkM55 : checkOneM 55 3 164 = true := rfl
theorem checkM57 : checkOneM 57 4 164 = true := rfl
theorem checkM59 : checkOneM 59 3 164 = true := rfl
theorem checkM61 : checkOneM 61 4 164 = true := rfl
theorem checkM63 : checkOneM 63 3 164 = true := rfl
theorem checkM65 : checkOneM 65 4 164 = true := rfl
theorem checkM67 : checkOneM 67 4 164 = true := rfl
theorem checkM69 : checkOneM 69 4 164 = true := rfl
theorem checkM71 : checkOneM 71 3 164 = true := rfl
theorem checkM73 : checkOneM 73 4 164 = true := rfl
theorem checkM75 : checkOneM 75 3 164 = true := rfl
theorem checkM77 : checkOneM 77 3 164 = true := rfl
theorem checkM79 : checkOneM 79 3 164 = true := rfl
theorem checkM81 : checkOneM 81 4 164 = true := rfl
theorem checkM83 : checkOneM 83 3 164 = true := rfl
theorem checkM85 : checkOneM 85 3 164 = true := rfl
theorem checkM87 : checkOneM 87 3 164 = true := rfl
theorem checkM89 : checkOneM 89 3 164 = true := rfl
theorem checkM91 : checkOneM 91 3 164 = true := rfl
theorem checkM93 : checkOneM 93 3 164 = true := rfl
theorem checkM95 : checkOneM 95 3 164 = true := rfl
theorem checkM97 : checkOneM 97 4 164 = true := rfl
set_option maxRecDepth 1024 in

theorem checkM99 : checkOneM 99 3 164 = true := rfl
set_option maxRecDepth 1024 in

theorem checkM101 : checkOneM 101 3 164 = true := rfl
set_option maxRecDepth 1024 in

theorem checkM103 : checkOneM 103 3 164 = true := rfl
theorem allGt_sound (bound : Nat) :
    ∀ (l : List Nat) (y : Nat), allGt bound l = true → y < l.length →
      bound < l.getD y 0 := by
  intro l
  induction l with
  | nil => intro y _ hy; simp at hy
  | cons x xs ih =>
    intro y h hy
    simp only [allGt, Bool.and_eq_true, Nat.ble_eq] at h
    cases y with
    | zero => exact Nat.lt_of_succ_le h.1
    | succ y =>
      have hy' : y < xs.length := by simp at hy; omega
      exact ih y h.2 hy'

theorem getD_map_range (M : Nat) (f : Nat → Nat) (y : Nat) (hy : y < M) : ((List.range M).map f).getD y 0 = f y := by
  simp [List.getD, List.getElem?_map, List.getElem?_range hy]

theorem length_stepU (M : Nat) (u : List Nat) : (stepU M u).length = M := by simp [stepU]

theorem length_initU (M : Nat) : (initU M).length = M := by simp [initU]

theorem length_stepAcc (acc u : List Nat) : (stepAcc acc u).length = min acc.length u.length := by simp [stepAcc]
/-- Scaled cumulative sum `accIter M k y = ∑_{i=0}^{k} 2^(k - i) * uIter M i y`. -/
def accIter (M : Nat) : Nat → Nat → Nat
  | 0, y => uIter M 0 y
  | k + 1, y => 2 * accIter M k y + uIter M (k + 1) y

theorem runK_spec (M : Nat) (hM : 1 ≤ M) :
    ∀ (n k : Nat) (u acc : List Nat),
      u.length = M → acc.length = M →
      (∀ y < M, u.getD y 0 = uIter M k y) →
      (∀ y < M, acc.getD y 0 = accIter M k y) →
      (runK M n u acc).length = M ∧
      (∀ y < M, (runK M n u acc).getD y 0 = accIter M (k + n) y) := by
  intro n
  induction n with
  | zero => intro k u acc _ ha _ hacc; exact ⟨ha, hacc⟩
  | succ n ih =>
    intro k u acc hu ha huf hacc; have hstep_len : (stepU M u).length = M := length_stepU M u
    have hstep_get : ∀ y < M, (stepU M u).getD y 0 = uIter M (k + 1) y := by
      intro y hy; rw [stepU, getD_map_range M _ y hy]; have hh : hStepNat M y < M := Nat.mod_lt _ (by omega)
      have hq : qStepNat M y < M := Nat.mod_lt _ (by omega)
      rw [huf _ hh, huf _ hq]; rfl
    have hnew_acc_len : (stepAcc acc (stepU M u)).length = M := by rw [length_stepAcc, ha, hstep_len, Nat.min_self]
    have hnew_acc_get : ∀ y < M, (stepAcc acc (stepU M u)).getD y 0 = accIter M (k + 1) y := by
      intro y hy; have hy_acc : y < acc.length := by omega
      have hy_u : y < (stepU M u).length := by omega
      simp only [stepAcc, List.getD, List.getElem?_zipWith,
        List.getElem?_eq_getElem hy_acc, List.getElem?_eq_getElem hy_u, Option.getD_some]
      have h1 : acc[y] = acc.getD y 0 := by simp [List.getD, List.getElem?_eq_getElem hy_acc]
      have h2 : (stepU M u)[y] = (stepU M u).getD y 0 := by simp [List.getD, List.getElem?_eq_getElem hy_u]
      rw [h1, h2, hacc y hy, hstep_get y hy]; rfl
    have hres := ih (k + 1) (stepU M u) (stepAcc acc (stepU M u))
      hstep_len hnew_acc_len hstep_get hnew_acc_get
    simpa [runK, show k + 1 + n = k + (n + 1) by omega] using hres
/-- Soundness of `checkOneM M L rhsMult = true`: for every `y < M`, -/
theorem checkOneM_sound {M L rhsMult : Nat} (hM : 1 ≤ M) (_hL : 1 ≤ L)
    (h : checkOneM M L rhsMult = true) :
    ∀ y < M, rhsMult * L * 2 ^ (L - 1) < accIter M (L - 1) y := by
  have hu0_len : (initU M).length = M := length_initU M
  have hu0_get : ∀ y < M, (initU M).getD y 0 = uIter M 0 y := by intro y hy; rw [initU, getD_map_range M _ y hy]; rfl
  have hrun := runK_spec M hM (L - 1) 0 (initU M) (initU M) hu0_len hu0_len hu0_get hu0_get; intro y hy
  have hgt := allGt_sound (rhsMult * L * 2 ^ (L - 1)) _ y h (by rw [hrun.1]; exact hy)
  rw [hrun.2 y hy] at hgt
  simpa using hgt
/-- Every odd `M` with `9 ≤ M ≤ 103` has a certified `L ≥ 1` with `checkOneM M L 164 = true`. -/
theorem checkOneM_9_to_103 (M : Nat) (hodd : M % 2 = 1) (hlo : 9 ≤ M) (hhi : M ≤ 103) :
    ∃ L, 1 ≤ L ∧ checkOneM M L 164 = true := by
  have hcases : M = 9 ∨ M = 11 ∨ M = 13 ∨ M = 15 ∨ M = 17 ∨ M = 19 ∨ M = 21 ∨ M = 23 ∨
      M = 25 ∨ M = 27 ∨ M = 29 ∨ M = 31 ∨ M = 33 ∨ M = 35 ∨ M = 37 ∨ M = 39 ∨
      M = 41 ∨ M = 43 ∨ M = 45 ∨ M = 47 ∨ M = 49 ∨ M = 51 ∨ M = 53 ∨ M = 55 ∨
      M = 57 ∨ M = 59 ∨ M = 61 ∨ M = 63 ∨ M = 65 ∨ M = 67 ∨ M = 69 ∨ M = 71 ∨
      M = 73 ∨ M = 75 ∨ M = 77 ∨ M = 79 ∨ M = 81 ∨ M = 83 ∨ M = 85 ∨ M = 87 ∨
      M = 89 ∨ M = 91 ∨ M = 93 ∨ M = 95 ∨ M = 97 ∨ M = 99 ∨ M = 101 ∨ M = 103 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨24, by omega, checkM9⟩
  · exact ⟨13, by omega, checkM11⟩
  · exact ⟨9, by omega, checkM13⟩
  · exact ⟨6, by omega, checkM15⟩
  · exact ⟨6, by omega, checkM17⟩
  · exact ⟨6, by omega, checkM19⟩
  · exact ⟨6, by omega, checkM21⟩
  · exact ⟨5, by omega, checkM23⟩
  · exact ⟨5, by omega, checkM25⟩
  · exact ⟨4, by omega, checkM27⟩
  · exact ⟨5, by omega, checkM29⟩
  · exact ⟨4, by omega, checkM31⟩
  · exact ⟨5, by omega, checkM33⟩
  · exact ⟨4, by omega, checkM35⟩
  · exact ⟨4, by omega, checkM37⟩
  · exact ⟨4, by omega, checkM39⟩
  · exact ⟨4, by omega, checkM41⟩
  · exact ⟨4, by omega, checkM43⟩
  · exact ⟨4, by omega, checkM45⟩
  · exact ⟨3, by omega, checkM47⟩
  · exact ⟨4, by omega, checkM49⟩
  · exact ⟨4, by omega, checkM51⟩
  · exact ⟨4, by omega, checkM53⟩
  · exact ⟨3, by omega, checkM55⟩
  · exact ⟨4, by omega, checkM57⟩
  · exact ⟨3, by omega, checkM59⟩
  · exact ⟨4, by omega, checkM61⟩
  · exact ⟨3, by omega, checkM63⟩
  · exact ⟨4, by omega, checkM65⟩
  · exact ⟨4, by omega, checkM67⟩
  · exact ⟨4, by omega, checkM69⟩
  · exact ⟨3, by omega, checkM71⟩
  · exact ⟨4, by omega, checkM73⟩
  · exact ⟨3, by omega, checkM75⟩
  · exact ⟨3, by omega, checkM77⟩
  · exact ⟨3, by omega, checkM79⟩
  · exact ⟨4, by omega, checkM81⟩
  · exact ⟨3, by omega, checkM83⟩
  · exact ⟨3, by omega, checkM85⟩
  · exact ⟨3, by omega, checkM87⟩
  · exact ⟨3, by omega, checkM89⟩
  · exact ⟨3, by omega, checkM91⟩
  · exact ⟨3, by omega, checkM93⟩
  · exact ⟨3, by omega, checkM95⟩
  · exact ⟨4, by omega, checkM97⟩
  · exact ⟨3, by omega, checkM99⟩
  · exact ⟨3, by omega, checkM101⟩
  · exact ⟨3, by omega, checkM103⟩

end Ouroboros.EvenBasesCert
