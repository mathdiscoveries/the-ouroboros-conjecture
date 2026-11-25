module
public import Ouroboros.BasinFiveCertData
@[expose] public section
namespace Ouroboros.BasinFiveCert
theorem shard_12_0 : checkPow2 12288 8 = true := rfl
theorem shard_12_1 : checkPow2 12544 8 = true := rfl
theorem shard_12_2 : checkPow2 12800 8 = true := rfl
theorem shard_12_3 : checkPow2 13056 8 = true := rfl
theorem shard_12 : checkPow2 12288 10 = true := checkPow2_succ 12288 9 (checkPow2_succ 12288 8 shard_12_0 shard_12_1) (checkPow2_succ 12800 8 shard_12_2 shard_12_3)
end Ouroboros.BasinFiveCert
