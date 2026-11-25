module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_13_0 : checkPow2 26624 8 = true := rfl
theorem shard_13_1 : checkPow2 26880 8 = true := rfl
theorem shard_13_2 : checkPow2 27136 8 = true := rfl
theorem shard_13_3 : checkPow2 27392 8 = true := rfl
theorem shard_13_4 : checkPow2 27648 8 = true := rfl
theorem shard_13_5 : checkPow2 27904 8 = true := rfl
theorem shard_13_6 : checkPow2 28160 8 = true := rfl
theorem shard_13_7 : checkPow2 28416 8 = true := rfl

theorem shard_13 : checkPow2 26624 11 = true :=
  checkPow2_succ 26624 10
    (checkPow2_succ 26624 9 (checkPow2_succ 26624 8 shard_13_0 shard_13_1) (checkPow2_succ 27136 8 shard_13_2 shard_13_3))
    (checkPow2_succ 27648 9 (checkPow2_succ 27648 8 shard_13_4 shard_13_5) (checkPow2_succ 28160 8 shard_13_6 shard_13_7))

end Ouroboros.BasinOneUpperCert
