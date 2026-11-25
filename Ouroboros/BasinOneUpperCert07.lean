module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_07_0 : checkPow2 14336 8 = true := rfl
theorem shard_07_1 : checkPow2 14592 8 = true := rfl
theorem shard_07_2 : checkPow2 14848 8 = true := rfl
theorem shard_07_3 : checkPow2 15104 8 = true := rfl
theorem shard_07_4 : checkPow2 15360 8 = true := rfl
theorem shard_07_5 : checkPow2 15616 8 = true := rfl
theorem shard_07_6 : checkPow2 15872 8 = true := rfl
theorem shard_07_7 : checkPow2 16128 8 = true := rfl

theorem shard_07 : checkPow2 14336 11 = true :=
  checkPow2_succ 14336 10
    (checkPow2_succ 14336 9 (checkPow2_succ 14336 8 shard_07_0 shard_07_1) (checkPow2_succ 14848 8 shard_07_2 shard_07_3))
    (checkPow2_succ 15360 9 (checkPow2_succ 15360 8 shard_07_4 shard_07_5) (checkPow2_succ 15872 8 shard_07_6 shard_07_7))

end Ouroboros.BasinOneUpperCert
