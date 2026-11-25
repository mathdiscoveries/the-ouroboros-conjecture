module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_08_0 : checkPow2 16384 8 = true := rfl
theorem shard_08_1 : checkPow2 16640 8 = true := rfl
theorem shard_08_2 : checkPow2 16896 8 = true := rfl
theorem shard_08_3 : checkPow2 17152 8 = true := rfl
theorem shard_08_4 : checkPow2 17408 8 = true := rfl
theorem shard_08_5 : checkPow2 17664 8 = true := rfl
theorem shard_08_6 : checkPow2 17920 8 = true := rfl
theorem shard_08_7 : checkPow2 18176 8 = true := rfl

theorem shard_08 : checkPow2 16384 11 = true :=
  checkPow2_succ 16384 10
    (checkPow2_succ 16384 9 (checkPow2_succ 16384 8 shard_08_0 shard_08_1) (checkPow2_succ 16896 8 shard_08_2 shard_08_3))
    (checkPow2_succ 17408 9 (checkPow2_succ 17408 8 shard_08_4 shard_08_5) (checkPow2_succ 17920 8 shard_08_6 shard_08_7))

end Ouroboros.BasinOneUpperCert
