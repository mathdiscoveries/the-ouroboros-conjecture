module
public import Ouroboros.BasinFiveCertData
@[expose] public section
namespace Ouroboros.BasinFiveCert
theorem shard_02_0 : checkPow2 2048 8 = true := rfl
theorem shard_02_1 : checkPow2 2304 8 = true := rfl
theorem shard_02_2 : checkPow2 2560 8 = true := rfl
theorem shard_02_3 : checkPow2 2816 8 = true := rfl
theorem shard_02 : checkPow2 2048 10 = true := checkPow2_succ 2048 9 (checkPow2_succ 2048 8 shard_02_0 shard_02_1) (checkPow2_succ 2560 8 shard_02_2 shard_02_3)
end Ouroboros.BasinFiveCert
