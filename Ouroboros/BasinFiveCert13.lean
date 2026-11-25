module
public import Ouroboros.BasinFiveCertData
@[expose] public section
namespace Ouroboros.BasinFiveCert
theorem shard_13_0 : checkPow2 13312 8 = true := rfl
theorem shard_13_1 : checkPow2 13568 8 = true := rfl
theorem shard_13_2 : checkPow2 13824 8 = true := rfl
theorem shard_13_3 : checkPow2 14080 8 = true := rfl
theorem shard_13 : checkPow2 13312 10 = true := checkPow2_succ 13312 9 (checkPow2_succ 13312 8 shard_13_0 shard_13_1) (checkPow2_succ 13824 8 shard_13_2 shard_13_3)
end Ouroboros.BasinFiveCert
