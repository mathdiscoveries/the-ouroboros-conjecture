module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2B 0 8 = true := rfl
private theorem sub_01 : checkPow2B 256 8 = true := rfl
private theorem sub_02 : checkPow2B 512 8 = true := rfl
private theorem sub_03 : checkPow2B 768 8 = true := rfl
private theorem sub_04 : checkPow2B 1024 8 = true := rfl
private theorem sub_05 : checkPow2B 1280 8 = true := rfl
private theorem sub_06 : checkPow2B 1536 8 = true := rfl
private theorem sub_07 : checkPow2B 1792 8 = true := rfl
private theorem sub_08 : checkPow2B 2048 8 = true := rfl
private theorem sub_09 : checkPow2B 2304 8 = true := rfl
private theorem sub_10 : checkPow2B 2560 8 = true := rfl
private theorem sub_11 : checkPow2B 2816 8 = true := rfl
private theorem sub_12 : checkPow2B 3072 8 = true := rfl
private theorem sub_13 : checkPow2B 3328 8 = true := rfl
private theorem sub_14 : checkPow2B 3584 8 = true := rfl
private theorem sub_15 : checkPow2B 3840 8 = true := rfl
private theorem sub_16 : checkPow2B 4096 8 = true := rfl
private theorem sub_17 : checkPow2B 4352 8 = true := rfl
private theorem sub_18 : checkPow2B 4608 8 = true := rfl
private theorem sub_19 : checkPow2B 4864 8 = true := rfl
private theorem sub_20 : checkPow2B 5120 8 = true := rfl
private theorem sub_21 : checkPow2B 5376 8 = true := rfl
private theorem sub_22 : checkPow2B 5632 8 = true := rfl
private theorem sub_23 : checkPow2B 5888 8 = true := rfl
private theorem sub_24 : checkPow2B 6144 8 = true := rfl
private theorem sub_25 : checkPow2B 6400 8 = true := rfl
private theorem sub_26 : checkPow2B 6656 8 = true := rfl
private theorem sub_27 : checkPow2B 6912 8 = true := rfl
private theorem sub_28 : checkPow2B 7168 8 = true := rfl
private theorem sub_29 : checkPow2B 7424 8 = true := rfl
private theorem sub_30 : checkPow2B 7680 8 = true := rfl
private theorem sub_31 : checkPow2B 7936 8 = true := rfl

theorem shard_B00 : checkPow2B 0 13 = true :=
  (checkPow2B_succ 0 12 (checkPow2B_succ 0 11 (checkPow2B_succ 0 10 (checkPow2B_succ 0 9 (checkPow2B_succ 0 8 sub_00 sub_01) (checkPow2B_succ 512 8 sub_02 sub_03)) (checkPow2B_succ 1024 9 (checkPow2B_succ 1024 8 sub_04 sub_05) (checkPow2B_succ 1536 8 sub_06 sub_07))) (checkPow2B_succ 2048 10 (checkPow2B_succ 2048 9 (checkPow2B_succ 2048 8 sub_08 sub_09) (checkPow2B_succ 2560 8 sub_10 sub_11)) (checkPow2B_succ 3072 9 (checkPow2B_succ 3072 8 sub_12 sub_13) (checkPow2B_succ 3584 8 sub_14 sub_15)))) (checkPow2B_succ 4096 11 (checkPow2B_succ 4096 10 (checkPow2B_succ 4096 9 (checkPow2B_succ 4096 8 sub_16 sub_17) (checkPow2B_succ 4608 8 sub_18 sub_19)) (checkPow2B_succ 5120 9 (checkPow2B_succ 5120 8 sub_20 sub_21) (checkPow2B_succ 5632 8 sub_22 sub_23))) (checkPow2B_succ 6144 10 (checkPow2B_succ 6144 9 (checkPow2B_succ 6144 8 sub_24 sub_25) (checkPow2B_succ 6656 8 sub_26 sub_27)) (checkPow2B_succ 7168 9 (checkPow2B_succ 7168 8 sub_28 sub_29) (checkPow2B_succ 7680 8 sub_30 sub_31)))))

end Ouroboros.BasinOneLowerCert
