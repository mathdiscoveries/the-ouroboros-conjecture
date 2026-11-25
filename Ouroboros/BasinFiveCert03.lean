module
public import Ouroboros.BasinFiveCertData
@[expose] public section
namespace Ouroboros.BasinFiveCert
theorem shard_03_0 : checkPow2 3072 8 = true := rfl
theorem shard_03_1 : checkPow2 3328 8 = true := rfl
theorem shard_03_2 : checkPow2 3584 8 = true := rfl
theorem shard_03_3 : checkPow2 3840 8 = true := rfl
theorem shard_03 : checkPow2 3072 10 = true := checkPow2_succ 3072 9 (checkPow2_succ 3072 8 shard_03_0 shard_03_1) (checkPow2_succ 3584 8 shard_03_2 shard_03_3)
end Ouroboros.BasinFiveCert
