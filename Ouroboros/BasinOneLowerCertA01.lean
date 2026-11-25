module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2A 4096 8 = true := rfl
private theorem sub_01 : checkPow2A 4352 8 = true := rfl
private theorem sub_02 : checkPow2A 4608 8 = true := rfl
private theorem sub_03 : checkPow2A 4864 8 = true := rfl
private theorem sub_04 : checkPow2A 5120 8 = true := rfl
private theorem sub_05 : checkPow2A 5376 8 = true := rfl
private theorem sub_06 : checkPow2A 5632 8 = true := rfl
private theorem sub_07 : checkPow2A 5888 8 = true := rfl
private theorem sub_08 : checkPow2A 6144 8 = true := rfl
private theorem sub_09 : checkPow2A 6400 8 = true := rfl
private theorem sub_10 : checkPow2A 6656 8 = true := rfl
private theorem sub_11 : checkPow2A 6912 8 = true := rfl
private theorem sub_12 : checkPow2A 7168 8 = true := rfl
private theorem sub_13 : checkPow2A 7424 8 = true := rfl
private theorem sub_14 : checkPow2A 7680 8 = true := rfl
private theorem sub_15 : checkPow2A 7936 8 = true := rfl

theorem shard_A01 : checkPow2A 4096 12 = true :=
  (checkPow2A_succ 4096 11 (checkPow2A_succ 4096 10 (checkPow2A_succ 4096 9 (checkPow2A_succ 4096 8 sub_00 sub_01) (checkPow2A_succ 4608 8 sub_02 sub_03)) (checkPow2A_succ 5120 9 (checkPow2A_succ 5120 8 sub_04 sub_05) (checkPow2A_succ 5632 8 sub_06 sub_07))) (checkPow2A_succ 6144 10 (checkPow2A_succ 6144 9 (checkPow2A_succ 6144 8 sub_08 sub_09) (checkPow2A_succ 6656 8 sub_10 sub_11)) (checkPow2A_succ 7168 9 (checkPow2A_succ 7168 8 sub_12 sub_13) (checkPow2A_succ 7680 8 sub_14 sub_15))))

end Ouroboros.BasinOneLowerCert
