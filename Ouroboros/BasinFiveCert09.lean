module
public import Ouroboros.BasinFiveCertData
@[expose] public section
namespace Ouroboros.BasinFiveCert
theorem shard_09_0 : checkPow2 9216 8 = true := rfl
theorem shard_09_1 : checkPow2 9472 8 = true := rfl
theorem shard_09_2 : checkPow2 9728 8 = true := rfl
theorem shard_09_3 : checkPow2 9984 8 = true := rfl
theorem shard_09 : checkPow2 9216 10 = true := checkPow2_succ 9216 9 (checkPow2_succ 9216 8 shard_09_0 shard_09_1) (checkPow2_succ 9728 8 shard_09_2 shard_09_3)
end Ouroboros.BasinFiveCert
