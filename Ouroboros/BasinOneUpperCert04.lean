module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_04_0 : checkPow2 8192 8 = true := rfl
theorem shard_04_1 : checkPow2 8448 8 = true := rfl
theorem shard_04_2 : checkPow2 8704 8 = true := rfl
theorem shard_04_3 : checkPow2 8960 8 = true := rfl
theorem shard_04_4 : checkPow2 9216 8 = true := rfl
theorem shard_04_5 : checkPow2 9472 8 = true := rfl
theorem shard_04_6 : checkPow2 9728 8 = true := rfl
theorem shard_04_7 : checkPow2 9984 8 = true := rfl

theorem shard_04 : checkPow2 8192 11 = true :=
  checkPow2_succ 8192 10
    (checkPow2_succ 8192 9 (checkPow2_succ 8192 8 shard_04_0 shard_04_1) (checkPow2_succ 8704 8 shard_04_2 shard_04_3))
    (checkPow2_succ 9216 9 (checkPow2_succ 9216 8 shard_04_4 shard_04_5) (checkPow2_succ 9728 8 shard_04_6 shard_04_7))

end Ouroboros.BasinOneUpperCert
