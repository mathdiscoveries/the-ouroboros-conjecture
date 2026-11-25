module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_16_0 : checkPow2 32768 8 = true := rfl
theorem shard_16_1 : checkPow2 33024 8 = true := rfl
theorem shard_16_2 : checkPow2 33280 8 = true := rfl
theorem shard_16_3 : checkPow2 33536 8 = true := rfl
theorem shard_16_4 : checkPow2 33792 8 = true := rfl
theorem shard_16_5 : checkPow2 34048 8 = true := rfl
theorem shard_16_6 : checkPow2 34304 8 = true := rfl
theorem shard_16_7 : checkPow2 34560 8 = true := rfl

theorem shard_16 : checkPow2 32768 11 = true :=
  checkPow2_succ 32768 10
    (checkPow2_succ 32768 9 (checkPow2_succ 32768 8 shard_16_0 shard_16_1) (checkPow2_succ 33280 8 shard_16_2 shard_16_3))
    (checkPow2_succ 33792 9 (checkPow2_succ 33792 8 shard_16_4 shard_16_5) (checkPow2_succ 34304 8 shard_16_6 shard_16_7))

end Ouroboros.BasinOneUpperCert
