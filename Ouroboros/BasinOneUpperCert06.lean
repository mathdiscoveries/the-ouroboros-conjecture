module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_06_0 : checkPow2 12288 8 = true := rfl
theorem shard_06_1 : checkPow2 12544 8 = true := rfl
theorem shard_06_2 : checkPow2 12800 8 = true := rfl
theorem shard_06_3 : checkPow2 13056 8 = true := rfl
theorem shard_06_4 : checkPow2 13312 8 = true := rfl
theorem shard_06_5 : checkPow2 13568 8 = true := rfl
theorem shard_06_6 : checkPow2 13824 8 = true := rfl
theorem shard_06_7 : checkPow2 14080 8 = true := rfl

theorem shard_06 : checkPow2 12288 11 = true :=
  checkPow2_succ 12288 10
    (checkPow2_succ 12288 9 (checkPow2_succ 12288 8 shard_06_0 shard_06_1) (checkPow2_succ 12800 8 shard_06_2 shard_06_3))
    (checkPow2_succ 13312 9 (checkPow2_succ 13312 8 shard_06_4 shard_06_5) (checkPow2_succ 13824 8 shard_06_6 shard_06_7))

end Ouroboros.BasinOneUpperCert
