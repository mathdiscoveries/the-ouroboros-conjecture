module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2A 28672 8 = true := rfl
private theorem sub_01 : checkPow2A 28928 8 = true := rfl
private theorem sub_02 : checkPow2A 29184 8 = true := rfl
private theorem sub_03 : checkPow2A 29440 8 = true := rfl
private theorem sub_04 : checkPow2A 29696 8 = true := rfl
private theorem sub_05 : checkPow2A 29952 8 = true := rfl
private theorem sub_06 : checkPow2A 30208 8 = true := rfl
private theorem sub_07 : checkPow2A 30464 8 = true := rfl
private theorem sub_08 : checkPow2A 30720 8 = true := rfl
private theorem sub_09 : checkPow2A 30976 8 = true := rfl
private theorem sub_10 : checkPow2A 31232 8 = true := rfl
private theorem sub_11 : checkPow2A 31488 8 = true := rfl
private theorem sub_12 : checkPow2A 31744 8 = true := rfl
private theorem sub_13 : checkPow2A 32000 8 = true := rfl
private theorem sub_14 : checkPow2A 32256 8 = true := rfl
private theorem sub_15 : checkPow2A 32512 8 = true := rfl

theorem shard_A07 : checkPow2A 28672 12 = true :=
  (checkPow2A_succ 28672 11 (checkPow2A_succ 28672 10 (checkPow2A_succ 28672 9 (checkPow2A_succ 28672 8 sub_00 sub_01) (checkPow2A_succ 29184 8 sub_02 sub_03)) (checkPow2A_succ 29696 9 (checkPow2A_succ 29696 8 sub_04 sub_05) (checkPow2A_succ 30208 8 sub_06 sub_07))) (checkPow2A_succ 30720 10 (checkPow2A_succ 30720 9 (checkPow2A_succ 30720 8 sub_08 sub_09) (checkPow2A_succ 31232 8 sub_10 sub_11)) (checkPow2A_succ 31744 9 (checkPow2A_succ 31744 8 sub_12 sub_13) (checkPow2A_succ 32256 8 sub_14 sub_15))))

end Ouroboros.BasinOneLowerCert
