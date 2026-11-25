module
public import Ouroboros.BasinFiveCertData
@[expose] public section
namespace Ouroboros.BasinFiveCert
theorem shard_10_0 : checkPow2 10240 8 = true := rfl
theorem shard_10_1 : checkPow2 10496 8 = true := rfl
theorem shard_10_2 : checkPow2 10752 8 = true := rfl
theorem shard_10_3 : checkPow2 11008 8 = true := rfl
theorem shard_10 : checkPow2 10240 10 = true := checkPow2_succ 10240 9 (checkPow2_succ 10240 8 shard_10_0 shard_10_1) (checkPow2_succ 10752 8 shard_10_2 shard_10_3)
end Ouroboros.BasinFiveCert
