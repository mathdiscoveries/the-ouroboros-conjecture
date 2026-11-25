module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2B 32768 8 = true := rfl
private theorem sub_01 : checkPow2B 33024 8 = true := rfl
private theorem sub_02 : checkPow2B 33280 8 = true := rfl
private theorem sub_03 : checkPow2B 33536 8 = true := rfl
private theorem sub_04 : checkPow2B 33792 8 = true := rfl
private theorem sub_05 : checkPow2B 34048 8 = true := rfl
private theorem sub_06 : checkPow2B 34304 8 = true := rfl
private theorem sub_07 : checkPow2B 34560 8 = true := rfl
private theorem sub_08 : checkPow2B 34816 8 = true := rfl
private theorem sub_09 : checkPow2B 35072 8 = true := rfl
private theorem sub_10 : checkPow2B 35328 8 = true := rfl
private theorem sub_11 : checkPow2B 35584 8 = true := rfl
private theorem sub_12 : checkPow2B 35840 8 = true := rfl
private theorem sub_13 : checkPow2B 36096 8 = true := rfl
private theorem sub_14 : checkPow2B 36352 8 = true := rfl
private theorem sub_15 : checkPow2B 36608 8 = true := rfl
private theorem sub_16 : checkPow2B 36864 8 = true := rfl
private theorem sub_17 : checkPow2B 37120 8 = true := rfl
private theorem sub_18 : checkPow2B 37376 8 = true := rfl
private theorem sub_19 : checkPow2B 37632 8 = true := rfl
private theorem sub_20 : checkPow2B 37888 8 = true := rfl
private theorem sub_21 : checkPow2B 38144 8 = true := rfl
private theorem sub_22 : checkPow2B 38400 8 = true := rfl
private theorem sub_23 : checkPow2B 38656 8 = true := rfl
private theorem sub_24 : checkPow2B 38912 8 = true := rfl
private theorem sub_25 : checkPow2B 39168 8 = true := rfl
private theorem sub_26 : checkPow2B 39424 8 = true := rfl
private theorem sub_27 : checkPow2B 39680 8 = true := rfl
private theorem sub_28 : checkPow2B 39936 8 = true := rfl
private theorem sub_29 : checkPow2B 40192 8 = true := rfl
private theorem sub_30 : checkPow2B 40448 8 = true := rfl
private theorem sub_31 : checkPow2B 40704 8 = true := rfl

theorem shard_B04 : checkPow2B 32768 13 = true :=
  (checkPow2B_succ 32768 12 (checkPow2B_succ 32768 11 (checkPow2B_succ 32768 10 (checkPow2B_succ 32768 9 (checkPow2B_succ 32768 8 sub_00 sub_01) (checkPow2B_succ 33280 8 sub_02 sub_03)) (checkPow2B_succ 33792 9 (checkPow2B_succ 33792 8 sub_04 sub_05) (checkPow2B_succ 34304 8 sub_06 sub_07))) (checkPow2B_succ 34816 10 (checkPow2B_succ 34816 9 (checkPow2B_succ 34816 8 sub_08 sub_09) (checkPow2B_succ 35328 8 sub_10 sub_11)) (checkPow2B_succ 35840 9 (checkPow2B_succ 35840 8 sub_12 sub_13) (checkPow2B_succ 36352 8 sub_14 sub_15)))) (checkPow2B_succ 36864 11 (checkPow2B_succ 36864 10 (checkPow2B_succ 36864 9 (checkPow2B_succ 36864 8 sub_16 sub_17) (checkPow2B_succ 37376 8 sub_18 sub_19)) (checkPow2B_succ 37888 9 (checkPow2B_succ 37888 8 sub_20 sub_21) (checkPow2B_succ 38400 8 sub_22 sub_23))) (checkPow2B_succ 38912 10 (checkPow2B_succ 38912 9 (checkPow2B_succ 38912 8 sub_24 sub_25) (checkPow2B_succ 39424 8 sub_26 sub_27)) (checkPow2B_succ 39936 9 (checkPow2B_succ 39936 8 sub_28 sub_29) (checkPow2B_succ 40448 8 sub_30 sub_31)))))

end Ouroboros.BasinOneLowerCert
