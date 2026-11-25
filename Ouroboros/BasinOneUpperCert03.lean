module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_03_0 : checkPow2 6144 8 = true := rfl
theorem shard_03_1 : checkPow2 6400 8 = true := rfl
theorem shard_03_2 : checkPow2 6656 8 = true := rfl
theorem shard_03_3 : checkPow2 6912 8 = true := rfl
theorem shard_03_4 : checkPow2 7168 8 = true := rfl
theorem shard_03_5 : checkPow2 7424 8 = true := rfl
theorem shard_03_6 : checkPow2 7680 8 = true := rfl
theorem shard_03_7 : checkPow2 7936 8 = true := rfl

theorem shard_03 : checkPow2 6144 11 = true :=
  checkPow2_succ 6144 10
    (checkPow2_succ 6144 9 (checkPow2_succ 6144 8 shard_03_0 shard_03_1) (checkPow2_succ 6656 8 shard_03_2 shard_03_3))
    (checkPow2_succ 7168 9 (checkPow2_succ 7168 8 shard_03_4 shard_03_5) (checkPow2_succ 7680 8 shard_03_6 shard_03_7))

end Ouroboros.BasinOneUpperCert
