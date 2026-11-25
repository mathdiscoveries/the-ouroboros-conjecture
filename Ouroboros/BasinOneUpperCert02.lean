module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_02_0 : checkPow2 4096 8 = true := rfl
theorem shard_02_1 : checkPow2 4352 8 = true := rfl
theorem shard_02_2 : checkPow2 4608 8 = true := rfl
theorem shard_02_3 : checkPow2 4864 8 = true := rfl
theorem shard_02_4 : checkPow2 5120 8 = true := rfl
theorem shard_02_5 : checkPow2 5376 8 = true := rfl
theorem shard_02_6 : checkPow2 5632 8 = true := rfl
theorem shard_02_7 : checkPow2 5888 8 = true := rfl

theorem shard_02 : checkPow2 4096 11 = true :=
  checkPow2_succ 4096 10
    (checkPow2_succ 4096 9 (checkPow2_succ 4096 8 shard_02_0 shard_02_1) (checkPow2_succ 4608 8 shard_02_2 shard_02_3))
    (checkPow2_succ 5120 9 (checkPow2_succ 5120 8 shard_02_4 shard_02_5) (checkPow2_succ 5632 8 shard_02_6 shard_02_7))

end Ouroboros.BasinOneUpperCert
