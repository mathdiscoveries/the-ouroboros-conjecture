module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_00_0 : checkPow2 0 8 = true := rfl
theorem shard_00_1 : checkPow2 256 8 = true := rfl
theorem shard_00_2 : checkPow2 512 8 = true := rfl
theorem shard_00_3 : checkPow2 768 8 = true := rfl
theorem shard_00_4 : checkPow2 1024 8 = true := rfl
theorem shard_00_5 : checkPow2 1280 8 = true := rfl
theorem shard_00_6 : checkPow2 1536 8 = true := rfl
theorem shard_00_7 : checkPow2 1792 8 = true := rfl

theorem shard_00 : checkPow2 0 11 = true :=
  checkPow2_succ 0 10
    (checkPow2_succ 0 9 (checkPow2_succ 0 8 shard_00_0 shard_00_1) (checkPow2_succ 512 8 shard_00_2 shard_00_3))
    (checkPow2_succ 1024 9 (checkPow2_succ 1024 8 shard_00_4 shard_00_5) (checkPow2_succ 1536 8 shard_00_6 shard_00_7))

end Ouroboros.BasinOneUpperCert
