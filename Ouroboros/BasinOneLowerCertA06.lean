module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2A 24576 8 = true := rfl
private theorem sub_01 : checkPow2A 24832 8 = true := rfl
private theorem sub_02 : checkPow2A 25088 8 = true := rfl
private theorem sub_03 : checkPow2A 25344 8 = true := rfl
private theorem sub_04 : checkPow2A 25600 8 = true := rfl
private theorem sub_05 : checkPow2A 25856 8 = true := rfl
private theorem sub_06 : checkPow2A 26112 8 = true := rfl
private theorem sub_07 : checkPow2A 26368 8 = true := rfl
private theorem sub_08 : checkPow2A 26624 8 = true := rfl
private theorem sub_09 : checkPow2A 26880 8 = true := rfl
private theorem sub_10 : checkPow2A 27136 8 = true := rfl
private theorem sub_11 : checkPow2A 27392 8 = true := rfl
private theorem sub_12 : checkPow2A 27648 8 = true := rfl
private theorem sub_13 : checkPow2A 27904 8 = true := rfl
private theorem sub_14 : checkPow2A 28160 8 = true := rfl
private theorem sub_15 : checkPow2A 28416 8 = true := rfl

theorem shard_A06 : checkPow2A 24576 12 = true :=
  (checkPow2A_succ 24576 11 (checkPow2A_succ 24576 10 (checkPow2A_succ 24576 9 (checkPow2A_succ 24576 8 sub_00 sub_01) (checkPow2A_succ 25088 8 sub_02 sub_03)) (checkPow2A_succ 25600 9 (checkPow2A_succ 25600 8 sub_04 sub_05) (checkPow2A_succ 26112 8 sub_06 sub_07))) (checkPow2A_succ 26624 10 (checkPow2A_succ 26624 9 (checkPow2A_succ 26624 8 sub_08 sub_09) (checkPow2A_succ 27136 8 sub_10 sub_11)) (checkPow2A_succ 27648 9 (checkPow2A_succ 27648 8 sub_12 sub_13) (checkPow2A_succ 28160 8 sub_14 sub_15))))

end Ouroboros.BasinOneLowerCert
