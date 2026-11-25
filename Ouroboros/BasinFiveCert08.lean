module
public import Ouroboros.BasinFiveCertData
@[expose] public section
namespace Ouroboros.BasinFiveCert
theorem shard_08_0 : checkPow2 8192 8 = true := rfl
theorem shard_08_1 : checkPow2 8448 8 = true := rfl
theorem shard_08_2 : checkPow2 8704 8 = true := rfl
theorem shard_08_3 : checkPow2 8960 8 = true := rfl
theorem shard_08 : checkPow2 8192 10 = true := checkPow2_succ 8192 9 (checkPow2_succ 8192 8 shard_08_0 shard_08_1) (checkPow2_succ 8704 8 shard_08_2 shard_08_3)
end Ouroboros.BasinFiveCert
