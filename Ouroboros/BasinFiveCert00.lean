module
public import Ouroboros.BasinFiveCertData
@[expose] public section
namespace Ouroboros.BasinFiveCert
theorem shard_00_0 : checkPow2 0 8 = true := rfl
theorem shard_00_1 : checkPow2 256 8 = true := rfl
theorem shard_00_2 : checkPow2 512 8 = true := rfl
theorem shard_00_3 : checkPow2 768 8 = true := rfl
theorem shard_00 : checkPow2 0 10 = true := checkPow2_succ 0 9 (checkPow2_succ 0 8 shard_00_0 shard_00_1) (checkPow2_succ 512 8 shard_00_2 shard_00_3)
end Ouroboros.BasinFiveCert
