module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_11_0 : checkPow2 22528 8 = true := rfl
theorem shard_11_1 : checkPow2 22784 8 = true := rfl
theorem shard_11_2 : checkPow2 23040 8 = true := rfl
theorem shard_11_3 : checkPow2 23296 8 = true := rfl
theorem shard_11_4 : checkPow2 23552 8 = true := rfl
theorem shard_11_5 : checkPow2 23808 8 = true := rfl
theorem shard_11_6 : checkPow2 24064 8 = true := rfl
theorem shard_11_7 : checkPow2 24320 8 = true := rfl

theorem shard_11 : checkPow2 22528 11 = true :=
  checkPow2_succ 22528 10
    (checkPow2_succ 22528 9 (checkPow2_succ 22528 8 shard_11_0 shard_11_1) (checkPow2_succ 23040 8 shard_11_2 shard_11_3))
    (checkPow2_succ 23552 9 (checkPow2_succ 23552 8 shard_11_4 shard_11_5) (checkPow2_succ 24064 8 shard_11_6 shard_11_7))

end Ouroboros.BasinOneUpperCert
