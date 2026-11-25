module
public import Ouroboros.BasinFiveCertData
@[expose] public section
namespace Ouroboros.BasinFiveCert
theorem shard_05_0 : checkPow2 5120 8 = true := rfl
theorem shard_05_1 : checkPow2 5376 8 = true := rfl
theorem shard_05_2 : checkPow2 5632 8 = true := rfl
theorem shard_05_3 : checkPow2 5888 8 = true := rfl
theorem shard_05 : checkPow2 5120 10 = true := checkPow2_succ 5120 9 (checkPow2_succ 5120 8 shard_05_0 shard_05_1) (checkPow2_succ 5632 8 shard_05_2 shard_05_3)
end Ouroboros.BasinFiveCert
