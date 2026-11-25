module
public import Ouroboros.BasinFiveCertData
@[expose] public section
namespace Ouroboros.BasinFiveCert
theorem shard_06_0 : checkPow2 6144 8 = true := rfl
theorem shard_06_1 : checkPow2 6400 8 = true := rfl
theorem shard_06_2 : checkPow2 6656 8 = true := rfl
theorem shard_06_3 : checkPow2 6912 8 = true := rfl
theorem shard_06 : checkPow2 6144 10 = true := checkPow2_succ 6144 9 (checkPow2_succ 6144 8 shard_06_0 shard_06_1) (checkPow2_succ 6656 8 shard_06_2 shard_06_3)
end Ouroboros.BasinFiveCert
