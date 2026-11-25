module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_10_0 : checkPow2 20480 8 = true := rfl
theorem shard_10_1 : checkPow2 20736 8 = true := rfl
theorem shard_10_2 : checkPow2 20992 8 = true := rfl
theorem shard_10_3 : checkPow2 21248 8 = true := rfl
theorem shard_10_4 : checkPow2 21504 8 = true := rfl
theorem shard_10_5 : checkPow2 21760 8 = true := rfl
theorem shard_10_6 : checkPow2 22016 8 = true := rfl
theorem shard_10_7 : checkPow2 22272 8 = true := rfl

theorem shard_10 : checkPow2 20480 11 = true :=
  checkPow2_succ 20480 10
    (checkPow2_succ 20480 9 (checkPow2_succ 20480 8 shard_10_0 shard_10_1) (checkPow2_succ 20992 8 shard_10_2 shard_10_3))
    (checkPow2_succ 21504 9 (checkPow2_succ 21504 8 shard_10_4 shard_10_5) (checkPow2_succ 22016 8 shard_10_6 shard_10_7))

end Ouroboros.BasinOneUpperCert
