module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_19_0 : checkPow2 38912 8 = true := rfl
theorem shard_19_1 : checkPow2 39168 8 = true := rfl
theorem shard_19_2 : checkPow2 39424 8 = true := rfl
theorem shard_19_3 : checkPow2 39680 8 = true := rfl
theorem shard_19_4 : checkPow2 39936 8 = true := rfl
theorem shard_19_5 : checkPow2 40192 8 = true := rfl
theorem shard_19_6 : checkPow2 40448 8 = true := rfl
theorem shard_19_7 : checkPow2 40704 8 = true := rfl

theorem shard_19 : checkPow2 38912 11 = true :=
  checkPow2_succ 38912 10
    (checkPow2_succ 38912 9 (checkPow2_succ 38912 8 shard_19_0 shard_19_1) (checkPow2_succ 39424 8 shard_19_2 shard_19_3))
    (checkPow2_succ 39936 9 (checkPow2_succ 39936 8 shard_19_4 shard_19_5) (checkPow2_succ 40448 8 shard_19_6 shard_19_7))

end Ouroboros.BasinOneUpperCert
