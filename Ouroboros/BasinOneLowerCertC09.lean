module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2C 36864 8 = true := rfl
private theorem sub_01 : checkPow2C 37120 8 = true := rfl
private theorem sub_02 : checkPow2C 37376 8 = true := rfl
private theorem sub_03 : checkPow2C 37632 8 = true := rfl
private theorem sub_04 : checkPow2C 37888 8 = true := rfl
private theorem sub_05 : checkPow2C 38144 8 = true := rfl
private theorem sub_06 : checkPow2C 38400 8 = true := rfl
private theorem sub_07 : checkPow2C 38656 8 = true := rfl
private theorem sub_08 : checkPow2C 38912 8 = true := rfl
private theorem sub_09 : checkPow2C 39168 8 = true := rfl
private theorem sub_10 : checkPow2C 39424 8 = true := rfl
private theorem sub_11 : checkPow2C 39680 8 = true := rfl
private theorem sub_12 : checkPow2C 39936 8 = true := rfl
private theorem sub_13 : checkPow2C 40192 8 = true := rfl
private theorem sub_14 : checkPow2C 40448 8 = true := rfl
private theorem sub_15 : checkPow2C 40704 8 = true := rfl

theorem shard_C09 : checkPow2C 36864 12 = true :=
  (checkPow2C_succ 36864 11 (checkPow2C_succ 36864 10 (checkPow2C_succ 36864 9 (checkPow2C_succ 36864 8 sub_00 sub_01) (checkPow2C_succ 37376 8 sub_02 sub_03)) (checkPow2C_succ 37888 9 (checkPow2C_succ 37888 8 sub_04 sub_05) (checkPow2C_succ 38400 8 sub_06 sub_07))) (checkPow2C_succ 38912 10 (checkPow2C_succ 38912 9 (checkPow2C_succ 38912 8 sub_08 sub_09) (checkPow2C_succ 39424 8 sub_10 sub_11)) (checkPow2C_succ 39936 9 (checkPow2C_succ 39936 8 sub_12 sub_13) (checkPow2C_succ 40448 8 sub_14 sub_15))))

end Ouroboros.BasinOneLowerCert
