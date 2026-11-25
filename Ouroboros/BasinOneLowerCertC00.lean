module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2C 0 8 = true := rfl
private theorem sub_01 : checkPow2C 256 8 = true := rfl
private theorem sub_02 : checkPow2C 512 8 = true := rfl
private theorem sub_03 : checkPow2C 768 8 = true := rfl
private theorem sub_04 : checkPow2C 1024 8 = true := rfl
private theorem sub_05 : checkPow2C 1280 8 = true := rfl
private theorem sub_06 : checkPow2C 1536 8 = true := rfl
private theorem sub_07 : checkPow2C 1792 8 = true := rfl
private theorem sub_08 : checkPow2C 2048 8 = true := rfl
private theorem sub_09 : checkPow2C 2304 8 = true := rfl
private theorem sub_10 : checkPow2C 2560 8 = true := rfl
private theorem sub_11 : checkPow2C 2816 8 = true := rfl
private theorem sub_12 : checkPow2C 3072 8 = true := rfl
private theorem sub_13 : checkPow2C 3328 8 = true := rfl
private theorem sub_14 : checkPow2C 3584 8 = true := rfl
private theorem sub_15 : checkPow2C 3840 8 = true := rfl

theorem shard_C00 : checkPow2C 0 12 = true :=
  (checkPow2C_succ 0 11 (checkPow2C_succ 0 10 (checkPow2C_succ 0 9 (checkPow2C_succ 0 8 sub_00 sub_01) (checkPow2C_succ 512 8 sub_02 sub_03)) (checkPow2C_succ 1024 9 (checkPow2C_succ 1024 8 sub_04 sub_05) (checkPow2C_succ 1536 8 sub_06 sub_07))) (checkPow2C_succ 2048 10 (checkPow2C_succ 2048 9 (checkPow2C_succ 2048 8 sub_08 sub_09) (checkPow2C_succ 2560 8 sub_10 sub_11)) (checkPow2C_succ 3072 9 (checkPow2C_succ 3072 8 sub_12 sub_13) (checkPow2C_succ 3584 8 sub_14 sub_15))))

end Ouroboros.BasinOneLowerCert
