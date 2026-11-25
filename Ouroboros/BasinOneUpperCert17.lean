module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_17_0 : checkPow2 34816 8 = true := rfl
theorem shard_17_1 : checkPow2 35072 8 = true := rfl
theorem shard_17_2 : checkPow2 35328 8 = true := rfl
theorem shard_17_3 : checkPow2 35584 8 = true := rfl
theorem shard_17_4 : checkPow2 35840 8 = true := rfl
theorem shard_17_5 : checkPow2 36096 8 = true := rfl
theorem shard_17_6 : checkPow2 36352 8 = true := rfl
theorem shard_17_7 : checkPow2 36608 8 = true := rfl

theorem shard_17 : checkPow2 34816 11 = true :=
  checkPow2_succ 34816 10
    (checkPow2_succ 34816 9 (checkPow2_succ 34816 8 shard_17_0 shard_17_1) (checkPow2_succ 35328 8 shard_17_2 shard_17_3))
    (checkPow2_succ 35840 9 (checkPow2_succ 35840 8 shard_17_4 shard_17_5) (checkPow2_succ 36352 8 shard_17_6 shard_17_7))

end Ouroboros.BasinOneUpperCert
