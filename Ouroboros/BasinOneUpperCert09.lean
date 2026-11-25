module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_09_0 : checkPow2 18432 8 = true := rfl
theorem shard_09_1 : checkPow2 18688 8 = true := rfl
theorem shard_09_2 : checkPow2 18944 8 = true := rfl
theorem shard_09_3 : checkPow2 19200 8 = true := rfl
theorem shard_09_4 : checkPow2 19456 8 = true := rfl
theorem shard_09_5 : checkPow2 19712 8 = true := rfl
theorem shard_09_6 : checkPow2 19968 8 = true := rfl
theorem shard_09_7 : checkPow2 20224 8 = true := rfl

theorem shard_09 : checkPow2 18432 11 = true :=
  checkPow2_succ 18432 10
    (checkPow2_succ 18432 9 (checkPow2_succ 18432 8 shard_09_0 shard_09_1) (checkPow2_succ 18944 8 shard_09_2 shard_09_3))
    (checkPow2_succ 19456 9 (checkPow2_succ 19456 8 shard_09_4 shard_09_5) (checkPow2_succ 19968 8 shard_09_6 shard_09_7))

end Ouroboros.BasinOneUpperCert
