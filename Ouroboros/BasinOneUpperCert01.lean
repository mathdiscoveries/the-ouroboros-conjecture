module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_01_0 : checkPow2 2048 8 = true := rfl
theorem shard_01_1 : checkPow2 2304 8 = true := rfl
theorem shard_01_2 : checkPow2 2560 8 = true := rfl
theorem shard_01_3 : checkPow2 2816 8 = true := rfl
theorem shard_01_4 : checkPow2 3072 8 = true := rfl
theorem shard_01_5 : checkPow2 3328 8 = true := rfl
theorem shard_01_6 : checkPow2 3584 8 = true := rfl
theorem shard_01_7 : checkPow2 3840 8 = true := rfl

theorem shard_01 : checkPow2 2048 11 = true :=
  checkPow2_succ 2048 10
    (checkPow2_succ 2048 9 (checkPow2_succ 2048 8 shard_01_0 shard_01_1) (checkPow2_succ 2560 8 shard_01_2 shard_01_3))
    (checkPow2_succ 3072 9 (checkPow2_succ 3072 8 shard_01_4 shard_01_5) (checkPow2_succ 3584 8 shard_01_6 shard_01_7))

end Ouroboros.BasinOneUpperCert
