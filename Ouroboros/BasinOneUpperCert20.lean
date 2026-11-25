module
public import Ouroboros.BasinOneUpperCertData

@[expose] public section

namespace Ouroboros.BasinOneUpperCert

theorem shard_20_0 : checkPow2 40960 8 = true := rfl
theorem shard_20_1 : checkPow2 41216 8 = true := rfl
theorem shard_20_2 : checkPow2 41472 8 = true := rfl
theorem shard_20_3 : checkPow2 41728 8 = true := rfl
theorem shard_20_4 : checkPow2 41984 8 = true := rfl
theorem shard_20_5 : checkPow2 42240 8 = true := rfl
theorem shard_20_6 : checkPow2 42496 8 = true := rfl
theorem shard_20_7 : checkPow2 42752 8 = true := rfl

theorem shard_20 : checkPow2 40960 11 = true :=
  checkPow2_succ 40960 10
    (checkPow2_succ 40960 9 (checkPow2_succ 40960 8 shard_20_0 shard_20_1) (checkPow2_succ 41472 8 shard_20_2 shard_20_3))
    (checkPow2_succ 41984 9 (checkPow2_succ 41984 8 shard_20_4 shard_20_5) (checkPow2_succ 42496 8 shard_20_6 shard_20_7))

end Ouroboros.BasinOneUpperCert
