module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_15_0 : checkPow2 30720 8 = true := rfl
theorem shard_15_1 : checkPow2 30976 8 = true := rfl
theorem shard_15_2 : checkPow2 31232 8 = true := rfl
theorem shard_15_3 : checkPow2 31488 8 = true := rfl
theorem shard_15_4 : checkPow2 31744 8 = true := rfl
theorem shard_15_5 : checkPow2 32000 8 = true := rfl
theorem shard_15_6 : checkPow2 32256 8 = true := rfl
theorem shard_15_7 : checkPow2 32512 8 = true := rfl

theorem shard_15 : checkPow2 30720 11 = true :=
  checkPow2_succ 30720 10
    (checkPow2_succ 30720 9 (checkPow2_succ 30720 8 shard_15_0 shard_15_1) (checkPow2_succ 31232 8 shard_15_2 shard_15_3))
    (checkPow2_succ 31744 9 (checkPow2_succ 31744 8 shard_15_4 shard_15_5) (checkPow2_succ 32256 8 shard_15_6 shard_15_7))

end Ouroboros.BasinOneUpperCert
