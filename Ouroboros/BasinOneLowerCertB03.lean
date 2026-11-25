module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2B 24576 8 = true := rfl
private theorem sub_01 : checkPow2B 24832 8 = true := rfl
private theorem sub_02 : checkPow2B 25088 8 = true := rfl
private theorem sub_03 : checkPow2B 25344 8 = true := rfl
private theorem sub_04 : checkPow2B 25600 8 = true := rfl
private theorem sub_05 : checkPow2B 25856 8 = true := rfl
private theorem sub_06 : checkPow2B 26112 8 = true := rfl
private theorem sub_07 : checkPow2B 26368 8 = true := rfl
private theorem sub_08 : checkPow2B 26624 8 = true := rfl
private theorem sub_09 : checkPow2B 26880 8 = true := rfl
private theorem sub_10 : checkPow2B 27136 8 = true := rfl
private theorem sub_11 : checkPow2B 27392 8 = true := rfl
private theorem sub_12 : checkPow2B 27648 8 = true := rfl
private theorem sub_13 : checkPow2B 27904 8 = true := rfl
private theorem sub_14 : checkPow2B 28160 8 = true := rfl
private theorem sub_15 : checkPow2B 28416 8 = true := rfl
private theorem sub_16 : checkPow2B 28672 8 = true := rfl
private theorem sub_17 : checkPow2B 28928 8 = true := rfl
private theorem sub_18 : checkPow2B 29184 8 = true := rfl
private theorem sub_19 : checkPow2B 29440 8 = true := rfl
private theorem sub_20 : checkPow2B 29696 8 = true := rfl
private theorem sub_21 : checkPow2B 29952 8 = true := rfl
private theorem sub_22 : checkPow2B 30208 8 = true := rfl
private theorem sub_23 : checkPow2B 30464 8 = true := rfl
private theorem sub_24 : checkPow2B 30720 8 = true := rfl
private theorem sub_25 : checkPow2B 30976 8 = true := rfl
private theorem sub_26 : checkPow2B 31232 8 = true := rfl
private theorem sub_27 : checkPow2B 31488 8 = true := rfl
private theorem sub_28 : checkPow2B 31744 8 = true := rfl
private theorem sub_29 : checkPow2B 32000 8 = true := rfl
private theorem sub_30 : checkPow2B 32256 8 = true := rfl
private theorem sub_31 : checkPow2B 32512 8 = true := rfl

theorem shard_B03 : checkPow2B 24576 13 = true :=
  (checkPow2B_succ 24576 12 (checkPow2B_succ 24576 11 (checkPow2B_succ 24576 10 (checkPow2B_succ 24576 9 (checkPow2B_succ 24576 8 sub_00 sub_01) (checkPow2B_succ 25088 8 sub_02 sub_03)) (checkPow2B_succ 25600 9 (checkPow2B_succ 25600 8 sub_04 sub_05) (checkPow2B_succ 26112 8 sub_06 sub_07))) (checkPow2B_succ 26624 10 (checkPow2B_succ 26624 9 (checkPow2B_succ 26624 8 sub_08 sub_09) (checkPow2B_succ 27136 8 sub_10 sub_11)) (checkPow2B_succ 27648 9 (checkPow2B_succ 27648 8 sub_12 sub_13) (checkPow2B_succ 28160 8 sub_14 sub_15)))) (checkPow2B_succ 28672 11 (checkPow2B_succ 28672 10 (checkPow2B_succ 28672 9 (checkPow2B_succ 28672 8 sub_16 sub_17) (checkPow2B_succ 29184 8 sub_18 sub_19)) (checkPow2B_succ 29696 9 (checkPow2B_succ 29696 8 sub_20 sub_21) (checkPow2B_succ 30208 8 sub_22 sub_23))) (checkPow2B_succ 30720 10 (checkPow2B_succ 30720 9 (checkPow2B_succ 30720 8 sub_24 sub_25) (checkPow2B_succ 31232 8 sub_26 sub_27)) (checkPow2B_succ 31744 9 (checkPow2B_succ 31744 8 sub_28 sub_29) (checkPow2B_succ 32256 8 sub_30 sub_31)))))

end Ouroboros.BasinOneLowerCert
