module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_18_0 : checkPow2 36864 8 = true := rfl
theorem shard_18_1 : checkPow2 37120 8 = true := rfl
theorem shard_18_2 : checkPow2 37376 8 = true := rfl
theorem shard_18_3 : checkPow2 37632 8 = true := rfl
theorem shard_18_4 : checkPow2 37888 8 = true := rfl
theorem shard_18_5 : checkPow2 38144 8 = true := rfl
theorem shard_18_6 : checkPow2 38400 8 = true := rfl
theorem shard_18_7 : checkPow2 38656 8 = true := rfl

theorem shard_18 : checkPow2 36864 11 = true :=
  checkPow2_succ 36864 10
    (checkPow2_succ 36864 9 (checkPow2_succ 36864 8 shard_18_0 shard_18_1) (checkPow2_succ 37376 8 shard_18_2 shard_18_3))
    (checkPow2_succ 37888 9 (checkPow2_succ 37888 8 shard_18_4 shard_18_5) (checkPow2_succ 38400 8 shard_18_6 shard_18_7))

end Ouroboros.BasinOneUpperCert
