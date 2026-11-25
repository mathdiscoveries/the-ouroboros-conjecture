module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_14_0 : checkPow2 28672 8 = true := rfl
theorem shard_14_1 : checkPow2 28928 8 = true := rfl
theorem shard_14_2 : checkPow2 29184 8 = true := rfl
theorem shard_14_3 : checkPow2 29440 8 = true := rfl
theorem shard_14_4 : checkPow2 29696 8 = true := rfl
theorem shard_14_5 : checkPow2 29952 8 = true := rfl
theorem shard_14_6 : checkPow2 30208 8 = true := rfl
theorem shard_14_7 : checkPow2 30464 8 = true := rfl

theorem shard_14 : checkPow2 28672 11 = true :=
  checkPow2_succ 28672 10
    (checkPow2_succ 28672 9 (checkPow2_succ 28672 8 shard_14_0 shard_14_1) (checkPow2_succ 29184 8 shard_14_2 shard_14_3))
    (checkPow2_succ 29696 9 (checkPow2_succ 29696 8 shard_14_4 shard_14_5) (checkPow2_succ 30208 8 shard_14_6 shard_14_7))

end Ouroboros.BasinOneUpperCert
