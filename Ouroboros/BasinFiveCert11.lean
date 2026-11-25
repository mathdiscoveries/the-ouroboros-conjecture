module
public import Ouroboros.BasinFiveCertData
@[expose] public section
namespace Ouroboros.BasinFiveCert
theorem shard_11_0 : checkPow2 11264 8 = true := rfl
theorem shard_11_1 : checkPow2 11520 8 = true := rfl
theorem shard_11_2 : checkPow2 11776 8 = true := rfl
theorem shard_11_3 : checkPow2 12032 8 = true := rfl
theorem shard_11 : checkPow2 11264 10 = true := checkPow2_succ 11264 9 (checkPow2_succ 11264 8 shard_11_0 shard_11_1) (checkPow2_succ 11776 8 shard_11_2 shard_11_3)
end Ouroboros.BasinFiveCert
