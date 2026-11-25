module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2A 32768 8 = true := rfl
private theorem sub_01 : checkPow2A 33024 8 = true := rfl
private theorem sub_02 : checkPow2A 33280 8 = true := rfl
private theorem sub_03 : checkPow2A 33536 8 = true := rfl
private theorem sub_04 : checkPow2A 33792 8 = true := rfl
private theorem sub_05 : checkPow2A 34048 8 = true := rfl
private theorem sub_06 : checkPow2A 34304 8 = true := rfl
private theorem sub_07 : checkPow2A 34560 8 = true := rfl
private theorem sub_08 : checkPow2A 34816 8 = true := rfl
private theorem sub_09 : checkPow2A 35072 8 = true := rfl
private theorem sub_10 : checkPow2A 35328 8 = true := rfl
private theorem sub_11 : checkPow2A 35584 8 = true := rfl
private theorem sub_12 : checkPow2A 35840 8 = true := rfl
private theorem sub_13 : checkPow2A 36096 8 = true := rfl
private theorem sub_14 : checkPow2A 36352 8 = true := rfl
private theorem sub_15 : checkPow2A 36608 8 = true := rfl

theorem shard_A08 : checkPow2A 32768 12 = true :=
  (checkPow2A_succ 32768 11 (checkPow2A_succ 32768 10 (checkPow2A_succ 32768 9 (checkPow2A_succ 32768 8 sub_00 sub_01) (checkPow2A_succ 33280 8 sub_02 sub_03)) (checkPow2A_succ 33792 9 (checkPow2A_succ 33792 8 sub_04 sub_05) (checkPow2A_succ 34304 8 sub_06 sub_07))) (checkPow2A_succ 34816 10 (checkPow2A_succ 34816 9 (checkPow2A_succ 34816 8 sub_08 sub_09) (checkPow2A_succ 35328 8 sub_10 sub_11)) (checkPow2A_succ 35840 9 (checkPow2A_succ 35840 8 sub_12 sub_13) (checkPow2A_succ 36352 8 sub_14 sub_15))))

end Ouroboros.BasinOneLowerCert
