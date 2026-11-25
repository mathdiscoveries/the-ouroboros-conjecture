module
public import Ouroboros.BasinFiveCertData
@[expose] public section
namespace Ouroboros.BasinFiveCert
theorem shard_07_0 : checkPow2 7168 8 = true := rfl
theorem shard_07_1 : checkPow2 7424 8 = true := rfl
theorem shard_07_2 : checkPow2 7680 8 = true := rfl
theorem shard_07_3 : checkPow2 7936 8 = true := rfl
theorem shard_07 : checkPow2 7168 10 = true := checkPow2_succ 7168 9 (checkPow2_succ 7168 8 shard_07_0 shard_07_1) (checkPow2_succ 7680 8 shard_07_2 shard_07_3)
end Ouroboros.BasinFiveCert
