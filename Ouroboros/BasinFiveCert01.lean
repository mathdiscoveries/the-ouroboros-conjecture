module
public import Ouroboros.BasinFiveCertData
@[expose] public section
namespace Ouroboros.BasinFiveCert
theorem shard_01_0 : checkPow2 1024 8 = true := rfl
theorem shard_01_1 : checkPow2 1280 8 = true := rfl
theorem shard_01_2 : checkPow2 1536 8 = true := rfl
theorem shard_01_3 : checkPow2 1792 8 = true := rfl
theorem shard_01 : checkPow2 1024 10 = true := checkPow2_succ 1024 9 (checkPow2_succ 1024 8 shard_01_0 shard_01_1) (checkPow2_succ 1536 8 shard_01_2 shard_01_3)
end Ouroboros.BasinFiveCert
