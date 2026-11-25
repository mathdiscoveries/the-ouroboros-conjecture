module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_12_0 : checkPow2 24576 8 = true := rfl
theorem shard_12_1 : checkPow2 24832 8 = true := rfl
theorem shard_12_2 : checkPow2 25088 8 = true := rfl
theorem shard_12_3 : checkPow2 25344 8 = true := rfl
theorem shard_12_4 : checkPow2 25600 8 = true := rfl
theorem shard_12_5 : checkPow2 25856 8 = true := rfl
theorem shard_12_6 : checkPow2 26112 8 = true := rfl
theorem shard_12_7 : checkPow2 26368 8 = true := rfl

theorem shard_12 : checkPow2 24576 11 = true :=
  checkPow2_succ 24576 10
    (checkPow2_succ 24576 9 (checkPow2_succ 24576 8 shard_12_0 shard_12_1) (checkPow2_succ 25088 8 shard_12_2 shard_12_3))
    (checkPow2_succ 25600 9 (checkPow2_succ 25600 8 shard_12_4 shard_12_5) (checkPow2_succ 26112 8 shard_12_6 shard_12_7))

end Ouroboros.BasinOneUpperCert
