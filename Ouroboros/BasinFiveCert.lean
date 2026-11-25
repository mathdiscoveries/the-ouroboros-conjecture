module
public import Ouroboros.BasinFiveCertData
public import Ouroboros.BasinFiveCert00
public import Ouroboros.BasinFiveCert01
public import Ouroboros.BasinFiveCert02
public import Ouroboros.BasinFiveCert03
public import Ouroboros.BasinFiveCert04
public import Ouroboros.BasinFiveCert05
public import Ouroboros.BasinFiveCert06
public import Ouroboros.BasinFiveCert07
public import Ouroboros.BasinFiveCert08
public import Ouroboros.BasinFiveCert09
public import Ouroboros.BasinFiveCert10
public import Ouroboros.BasinFiveCert11
public import Ouroboros.BasinFiveCert12
public import Ouroboros.BasinFiveCert13
@[expose] public section

/-! # Pure-kernel basin-of-5 certificate combiner (`Q = 14175`, `Vmax = 16`, `c = 0.65`) -/

namespace Ouroboros.BasinFiveCert
/-- Pure-kernel proof of `checkR R = true` for every residue `R < 14175`. -/
theorem checkR_all (R : Nat) (hR : R < 14175) : checkR R = true := by
  by_cases h0 : R < 1024
  · exact checkPow2_sound 0 10 shard_00 R (by omega) (by omega) hR
  by_cases h1 : R < 2048
  · exact checkPow2_sound 1024 10 shard_01 R (by omega) (by omega) hR
  by_cases h2 : R < 3072
  · exact checkPow2_sound 2048 10 shard_02 R (by omega) (by omega) hR
  by_cases h3 : R < 4096
  · exact checkPow2_sound 3072 10 shard_03 R (by omega) (by omega) hR
  by_cases h4 : R < 5120
  · exact checkPow2_sound 4096 10 shard_04 R (by omega) (by omega) hR
  by_cases h5 : R < 6144
  · exact checkPow2_sound 5120 10 shard_05 R (by omega) (by omega) hR
  by_cases h6 : R < 7168
  · exact checkPow2_sound 6144 10 shard_06 R (by omega) (by omega) hR
  by_cases h7 : R < 8192
  · exact checkPow2_sound 7168 10 shard_07 R (by omega) (by omega) hR
  by_cases h8 : R < 9216
  · exact checkPow2_sound 8192 10 shard_08 R (by omega) (by omega) hR
  by_cases h9 : R < 10240
  · exact checkPow2_sound 9216 10 shard_09 R (by omega) (by omega) hR
  by_cases h10 : R < 11264
  · exact checkPow2_sound 10240 10 shard_10 R (by omega) (by omega) hR
  by_cases h11 : R < 12288
  · exact checkPow2_sound 11264 10 shard_11 R (by omega) (by omega) hR
  by_cases h12 : R < 13312
  · exact checkPow2_sound 12288 10 shard_12 R (by omega) (by omega) hR
  · exact checkPow2_sound 13312 10 shard_13 R (by omega) (by omega) hR
/-- Type offset in the flat `[0, 25335)` weight table for odd digit index `di ∈ 0..4`. -/
def typeOff (di : Nat) : Nat :=
  match di with
  | 0 => 0
  | 1 => 14175
  | 2 => 18900
  | 3 => 21735
  | _ => 23760
/-- Type modulus `14175 / digitVal di` for odd digit index `di ∈ 0..4`. -/
def typeMod (di : Nat) : Nat :=
  match di with
  | 0 => 14175
  | 1 => 4725
  | 2 => 2835
  | 3 => 2025
  | _ => 1575
/-- Every type `(di, R % typeMod di)` at every `R < 14175` satisfies the exact integer super-eigenvector -/
theorem checkR_type_le (R di : Nat) (hR : R < 14175) (hdi : di < 5) :
    getW (typeOff di + R % typeMod di) * 1000000 ≤ sumMovesAux 16 0 R 0 := by
  have h := checkR_all R hR
  simp only [checkR, Bool.and_eq_true, Nat.ble_eq] at h
  match di with
  | 0 => simp only [typeOff, typeMod, Nat.zero_add, Nat.mod_eq_of_lt hR]; exact h.1.1.1.1
  | 1 => exact h.1.1.1.2
  | 2 => exact h.1.1.2
  | 3 => exact h.1.2
  | 4 => exact h.2
  | _ + 5 => omega
private theorem checkCoeffDigit_sound (di : Nat) :
    ∀ n, checkCoeffDigit di n = true → ∀ vi < n, checkCoeffOne di vi = true := by
  intro n
  induction n with
  | zero => intro _ vi hvi; omega
  | succ n ih =>
    intro h vi hvi
    simp only [checkCoeffDigit, Bool.and_eq_true] at h
    by_cases heq : vi = n
    · subst heq; exact h.1
    · exact ih h.2 vi (by omega)
/-- Odd digit `1, 3, 5, 7, 9` for digit index `di < 5`. -/
def certDigit (di : Nat) : Nat :=
  match di with
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | _ => 9
/-- Every `(di, vi)` with `di < 5` and `vi < 16` satisfies the exact integer 20th-power bound -/
theorem checkCoeff_sound (di vi : Nat) (hdi : di < 5) (hvi : vi < 16) :
    getC di vi ^ 20 * 2 ^ (13 * (vi + 1)) ≤ 1000000 ^ 20 * certDigit di ^ 13 := by
  have hall := checkCoeffAll_true
  simp only [checkCoeffAll, Bool.and_eq_true] at hall
  have hone : checkCoeffOne di vi = true := by
    match di with
    | 0 => exact checkCoeffDigit_sound 0 16 hall.1.1.1.1 vi hvi
    | 1 => exact checkCoeffDigit_sound 1 16 hall.1.1.1.2 vi hvi
    | 2 => exact checkCoeffDigit_sound 2 16 hall.1.1.2 vi hvi
    | 3 => exact checkCoeffDigit_sound 3 16 hall.1.2 vi hvi
    | 4 => exact checkCoeffDigit_sound 4 16 hall.2 vi hvi
    | _ + 5 => omega
  simp only [checkCoeffOne, Nat.ble_eq] at hone
  exact hone

end Ouroboros.BasinFiveCert
