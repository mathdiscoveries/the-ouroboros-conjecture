module
public import Ouroboros.BasinOneUpperCertData
public import Ouroboros.BasinOneUpperCert00
public import Ouroboros.BasinOneUpperCert01
public import Ouroboros.BasinOneUpperCert02
public import Ouroboros.BasinOneUpperCert03
public import Ouroboros.BasinOneUpperCert04
public import Ouroboros.BasinOneUpperCert05
public import Ouroboros.BasinOneUpperCert06
public import Ouroboros.BasinOneUpperCert07
public import Ouroboros.BasinOneUpperCert08
public import Ouroboros.BasinOneUpperCert09
public import Ouroboros.BasinOneUpperCert10
public import Ouroboros.BasinOneUpperCert11
public import Ouroboros.BasinOneUpperCert12
public import Ouroboros.BasinOneUpperCert13
public import Ouroboros.BasinOneUpperCert14
public import Ouroboros.BasinOneUpperCert15
public import Ouroboros.BasinOneUpperCert16
public import Ouroboros.BasinOneUpperCert17
public import Ouroboros.BasinOneUpperCert18
public import Ouroboros.BasinOneUpperCert19
public import Ouroboros.BasinOneUpperCert20

@[expose] public section

/-!
# Pure-kernel pair certificate combiner (`Q1 = 643,125`, `Vmax = 36`, `a_P = 0.7116`, `s_P = 9/25`)

Combines the 21 parallel pure-kernel `rfl` shards (`BasinOneUpperCert00`..`BasinOneUpperCert20`)
into `checkQ_all : ∀ q < 42875, checkQ q = true`, verifying all `128,625` residue classes
modulo `Q1 = 643,125` with ZERO `native_decide`, ZERO `sorry`, and ZERO custom axioms.
-/

namespace Ouroboros.BasinOneUpperCert

/-- Pure-kernel proof of `checkQ q = true` for every quotient `q < 42875` (all `128,625` rows). -/
theorem checkQ_all (q : Nat) (hq : q < 42875) : checkQ q = true := by
  by_cases h0 : q < 2048
  · exact checkPow2_sound 0 11 shard_00 q (by omega) (by omega) hq
  by_cases h1 : q < 4096
  · exact checkPow2_sound 2048 11 shard_01 q (by omega) (by omega) hq
  by_cases h2 : q < 6144
  · exact checkPow2_sound 4096 11 shard_02 q (by omega) (by omega) hq
  by_cases h3 : q < 8192
  · exact checkPow2_sound 6144 11 shard_03 q (by omega) (by omega) hq
  by_cases h4 : q < 10240
  · exact checkPow2_sound 8192 11 shard_04 q (by omega) (by omega) hq
  by_cases h5 : q < 12288
  · exact checkPow2_sound 10240 11 shard_05 q (by omega) (by omega) hq
  by_cases h6 : q < 14336
  · exact checkPow2_sound 12288 11 shard_06 q (by omega) (by omega) hq
  by_cases h7 : q < 16384
  · exact checkPow2_sound 14336 11 shard_07 q (by omega) (by omega) hq
  by_cases h8 : q < 18432
  · exact checkPow2_sound 16384 11 shard_08 q (by omega) (by omega) hq
  by_cases h9 : q < 20480
  · exact checkPow2_sound 18432 11 shard_09 q (by omega) (by omega) hq
  by_cases h10 : q < 22528
  · exact checkPow2_sound 20480 11 shard_10 q (by omega) (by omega) hq
  by_cases h11 : q < 24576
  · exact checkPow2_sound 22528 11 shard_11 q (by omega) (by omega) hq
  by_cases h12 : q < 26624
  · exact checkPow2_sound 24576 11 shard_12 q (by omega) (by omega) hq
  by_cases h13 : q < 28672
  · exact checkPow2_sound 26624 11 shard_13 q (by omega) (by omega) hq
  by_cases h14 : q < 30720
  · exact checkPow2_sound 28672 11 shard_14 q (by omega) (by omega) hq
  by_cases h15 : q < 32768
  · exact checkPow2_sound 30720 11 shard_15 q (by omega) (by omega) hq
  by_cases h16 : q < 34816
  · exact checkPow2_sound 32768 11 shard_16 q (by omega) (by omega) hq
  by_cases h17 : q < 36864
  · exact checkPow2_sound 34816 11 shard_17 q (by omega) (by omega) hq
  by_cases h18 : q < 38912
  · exact checkPow2_sound 36864 11 shard_18 q (by omega) (by omega) hq
  by_cases h19 : q < 40960
  · exact checkPow2_sound 38912 11 shard_19 q (by omega) (by omega) hq
  · exact checkPow2_sound 40960 11 shard_20 q (by omega) (by omega) hq

end Ouroboros.BasinOneUpperCert
