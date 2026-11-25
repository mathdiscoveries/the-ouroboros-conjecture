module
public import Ouroboros.BasinOneLowerCertData
public import Ouroboros.BasinOneLowerCertA00
public import Ouroboros.BasinOneLowerCertA01
public import Ouroboros.BasinOneLowerCertA02
public import Ouroboros.BasinOneLowerCertA03
public import Ouroboros.BasinOneLowerCertA04
public import Ouroboros.BasinOneLowerCertA05
public import Ouroboros.BasinOneLowerCertA06
public import Ouroboros.BasinOneLowerCertA07
public import Ouroboros.BasinOneLowerCertA08
public import Ouroboros.BasinOneLowerCertA09
public import Ouroboros.BasinOneLowerCertA10
public import Ouroboros.BasinOneLowerCertC00
public import Ouroboros.BasinOneLowerCertC01
public import Ouroboros.BasinOneLowerCertC02
public import Ouroboros.BasinOneLowerCertC03
public import Ouroboros.BasinOneLowerCertC04
public import Ouroboros.BasinOneLowerCertC05
public import Ouroboros.BasinOneLowerCertC06
public import Ouroboros.BasinOneLowerCertC07
public import Ouroboros.BasinOneLowerCertC08
public import Ouroboros.BasinOneLowerCertC09
public import Ouroboros.BasinOneLowerCertC10
public import Ouroboros.BasinOneLowerCertB00
public import Ouroboros.BasinOneLowerCertB01
public import Ouroboros.BasinOneLowerCertB02
public import Ouroboros.BasinOneLowerCertB03
public import Ouroboros.BasinOneLowerCertB04
public import Ouroboros.BasinOneLowerCertB05

@[expose] public section

/-!
# Pure-kernel basin-of-1 lower-bound certificate combiner (`Q₁ = 643,125`)

Combines the 28 parallel pure-kernel `rfl` shards (`A00..A10`, `C00..C10`, `B00..B05`)
into `checkA_all`, `checkC_all`, and `checkB_all` across all `128,625` residues.
Uses ONLY Lean `Init` — zero Mathlib, zero `native_decide`, zero `sorry`, zero axioms.
-/

namespace Ouroboros.BasinOneLowerCert

private theorem checkRowA_all (k : Nat) (hk : k < 42875) : checkRowA k = true := by
  by_cases h0 : k < 4096
  · exact checkPow2A_sound 0 12 shard_A00 k (by omega) (by omega) hk
  by_cases h1 : k < 8192
  · exact checkPow2A_sound 4096 12 shard_A01 k (by omega) (by omega) hk
  by_cases h2 : k < 12288
  · exact checkPow2A_sound 8192 12 shard_A02 k (by omega) (by omega) hk
  by_cases h3 : k < 16384
  · exact checkPow2A_sound 12288 12 shard_A03 k (by omega) (by omega) hk
  by_cases h4 : k < 20480
  · exact checkPow2A_sound 16384 12 shard_A04 k (by omega) (by omega) hk
  by_cases h5 : k < 24576
  · exact checkPow2A_sound 20480 12 shard_A05 k (by omega) (by omega) hk
  by_cases h6 : k < 28672
  · exact checkPow2A_sound 24576 12 shard_A06 k (by omega) (by omega) hk
  by_cases h7 : k < 32768
  · exact checkPow2A_sound 28672 12 shard_A07 k (by omega) (by omega) hk
  by_cases h8 : k < 36864
  · exact checkPow2A_sound 32768 12 shard_A08 k (by omega) (by omega) hk
  by_cases h9 : k < 40960
  · exact checkPow2A_sound 36864 12 shard_A09 k (by omega) (by omega) hk
  · exact checkPow2A_sound 40960 12 shard_A10 k (by omega) (by omega) hk

theorem checkA_all (k : Nat) (hk : k < 42875) : getWA k * 1048576 ≤ sumA k := by
  have h := checkRowA_all k hk
  simp only [checkRowA, Nat.ble_eq] at h
  exact h

private theorem checkRowC_all (k : Nat) (hk : k < 42875) : checkRowC k = true := by
  by_cases h0 : k < 4096
  · exact checkPow2C_sound 0 12 shard_C00 k (by omega) (by omega) hk
  by_cases h1 : k < 8192
  · exact checkPow2C_sound 4096 12 shard_C01 k (by omega) (by omega) hk
  by_cases h2 : k < 12288
  · exact checkPow2C_sound 8192 12 shard_C02 k (by omega) (by omega) hk
  by_cases h3 : k < 16384
  · exact checkPow2C_sound 12288 12 shard_C03 k (by omega) (by omega) hk
  by_cases h4 : k < 20480
  · exact checkPow2C_sound 16384 12 shard_C04 k (by omega) (by omega) hk
  by_cases h5 : k < 24576
  · exact checkPow2C_sound 20480 12 shard_C05 k (by omega) (by omega) hk
  by_cases h6 : k < 28672
  · exact checkPow2C_sound 24576 12 shard_C06 k (by omega) (by omega) hk
  by_cases h7 : k < 32768
  · exact checkPow2C_sound 28672 12 shard_C07 k (by omega) (by omega) hk
  by_cases h8 : k < 36864
  · exact checkPow2C_sound 32768 12 shard_C08 k (by omega) (by omega) hk
  by_cases h9 : k < 40960
  · exact checkPow2C_sound 36864 12 shard_C09 k (by omega) (by omega) hk
  · exact checkPow2C_sound 40960 12 shard_C10 k (by omega) (by omega) hk

theorem checkC_all (k : Nat) (hk : k < 42875) : getWC (k % 6125) * 1048576 ≤ sumC k := by
  have h := checkRowC_all k hk
  simp only [checkRowC, Nat.ble_eq] at h
  exact h

private theorem checkRowB_all (k : Nat) (hk : k < 42875) : checkRowB k = true := by
  by_cases h0 : k < 8192
  · exact checkPow2B_sound 0 13 shard_B00 k (by omega) (by omega) hk
  by_cases h1 : k < 16384
  · exact checkPow2B_sound 8192 13 shard_B01 k (by omega) (by omega) hk
  by_cases h2 : k < 24576
  · exact checkPow2B_sound 16384 13 shard_B02 k (by omega) (by omega) hk
  by_cases h3 : k < 32768
  · exact checkPow2B_sound 24576 13 shard_B03 k (by omega) (by omega) hk
  by_cases h4 : k < 40960
  · exact checkPow2B_sound 32768 13 shard_B04 k (by omega) (by omega) hk
  · exact checkPow2B_sound 40960 13 shard_B05 k (by omega) (by omega) hk

theorem checkB_all (k : Nat) (hk : k < 42875) : getWB (k % 8575) * 1048576 ≤ sumB k := by
  have h := checkRowB_all k hk
  simp only [checkRowB] at h
  cases h0 : Nat.beq (getWB (k % 8575)) 0 with
  | true =>
    have hz : getWB (k % 8575) = 0 := Nat.eq_of_beq_eq_true h0
    rw [hz]; exact Nat.zero_le _
  | false =>
    rw [h0] at h
    exact Nat.ble_eq.mp h

end Ouroboros.BasinOneLowerCert
