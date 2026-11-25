module
public import Ouroboros.BasinFiveCertData
@[expose] public section
namespace Ouroboros.BasinFiveCert
theorem shard_04_0 : checkPow2 4096 8 = true := rfl
theorem shard_04_1 : checkPow2 4352 8 = true := rfl
theorem shard_04_2 : checkPow2 4608 8 = true := rfl
theorem shard_04_3 : checkPow2 4864 8 = true := rfl
theorem shard_04 : checkPow2 4096 10 = true := checkPow2_succ 4096 9 (checkPow2_succ 4096 8 shard_04_0 shard_04_1) (checkPow2_succ 4608 8 shard_04_2 shard_04_3)
end Ouroboros.BasinFiveCert
