module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2C 12288 8 = true := rfl
private theorem sub_01 : checkPow2C 12544 8 = true := rfl
private theorem sub_02 : checkPow2C 12800 8 = true := rfl
private theorem sub_03 : checkPow2C 13056 8 = true := rfl
private theorem sub_04 : checkPow2C 13312 8 = true := rfl
private theorem sub_05 : checkPow2C 13568 8 = true := rfl
private theorem sub_06 : checkPow2C 13824 8 = true := rfl
private theorem sub_07 : checkPow2C 14080 8 = true := rfl
private theorem sub_08 : checkPow2C 14336 8 = true := rfl
private theorem sub_09 : checkPow2C 14592 8 = true := rfl
private theorem sub_10 : checkPow2C 14848 8 = true := rfl
private theorem sub_11 : checkPow2C 15104 8 = true := rfl
private theorem sub_12 : checkPow2C 15360 8 = true := rfl
private theorem sub_13 : checkPow2C 15616 8 = true := rfl
private theorem sub_14 : checkPow2C 15872 8 = true := rfl
private theorem sub_15 : checkPow2C 16128 8 = true := rfl

theorem shard_C03 : checkPow2C 12288 12 = true :=
  (checkPow2C_succ 12288 11 (checkPow2C_succ 12288 10 (checkPow2C_succ 12288 9 (checkPow2C_succ 12288 8 sub_00 sub_01) (checkPow2C_succ 12800 8 sub_02 sub_03)) (checkPow2C_succ 13312 9 (checkPow2C_succ 13312 8 sub_04 sub_05) (checkPow2C_succ 13824 8 sub_06 sub_07))) (checkPow2C_succ 14336 10 (checkPow2C_succ 14336 9 (checkPow2C_succ 14336 8 sub_08 sub_09) (checkPow2C_succ 14848 8 sub_10 sub_11)) (checkPow2C_succ 15360 9 (checkPow2C_succ 15360 8 sub_12 sub_13) (checkPow2C_succ 15872 8 sub_14 sub_15))))

end Ouroboros.BasinOneLowerCert
