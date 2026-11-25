module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_05_0 : checkPow2 10240 8 = true := rfl
theorem shard_05_1 : checkPow2 10496 8 = true := rfl
theorem shard_05_2 : checkPow2 10752 8 = true := rfl
theorem shard_05_3 : checkPow2 11008 8 = true := rfl
theorem shard_05_4 : checkPow2 11264 8 = true := rfl
theorem shard_05_5 : checkPow2 11520 8 = true := rfl
theorem shard_05_6 : checkPow2 11776 8 = true := rfl
theorem shard_05_7 : checkPow2 12032 8 = true := rfl

theorem shard_05 : checkPow2 10240 11 = true :=
  checkPow2_succ 10240 10
    (checkPow2_succ 10240 9 (checkPow2_succ 10240 8 shard_05_0 shard_05_1) (checkPow2_succ 10752 8 shard_05_2 shard_05_3))
    (checkPow2_succ 11264 9 (checkPow2_succ 11264 8 shard_05_4 shard_05_5) (checkPow2_succ 11776 8 shard_05_6 shard_05_7))

end Ouroboros.BasinOneUpperCert
