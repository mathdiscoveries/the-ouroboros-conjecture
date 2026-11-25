module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2C 24576 8 = true := rfl
private theorem sub_01 : checkPow2C 24832 8 = true := rfl
private theorem sub_02 : checkPow2C 25088 8 = true := rfl
private theorem sub_03 : checkPow2C 25344 8 = true := rfl
private theorem sub_04 : checkPow2C 25600 8 = true := rfl
private theorem sub_05 : checkPow2C 25856 8 = true := rfl
private theorem sub_06 : checkPow2C 26112 8 = true := rfl
private theorem sub_07 : checkPow2C 26368 8 = true := rfl
private theorem sub_08 : checkPow2C 26624 8 = true := rfl
private theorem sub_09 : checkPow2C 26880 8 = true := rfl
private theorem sub_10 : checkPow2C 27136 8 = true := rfl
private theorem sub_11 : checkPow2C 27392 8 = true := rfl
private theorem sub_12 : checkPow2C 27648 8 = true := rfl
private theorem sub_13 : checkPow2C 27904 8 = true := rfl
private theorem sub_14 : checkPow2C 28160 8 = true := rfl
private theorem sub_15 : checkPow2C 28416 8 = true := rfl

theorem shard_C06 : checkPow2C 24576 12 = true :=
  (checkPow2C_succ 24576 11 (checkPow2C_succ 24576 10 (checkPow2C_succ 24576 9 (checkPow2C_succ 24576 8 sub_00 sub_01) (checkPow2C_succ 25088 8 sub_02 sub_03)) (checkPow2C_succ 25600 9 (checkPow2C_succ 25600 8 sub_04 sub_05) (checkPow2C_succ 26112 8 sub_06 sub_07))) (checkPow2C_succ 26624 10 (checkPow2C_succ 26624 9 (checkPow2C_succ 26624 8 sub_08 sub_09) (checkPow2C_succ 27136 8 sub_10 sub_11)) (checkPow2C_succ 27648 9 (checkPow2C_succ 27648 8 sub_12 sub_13) (checkPow2C_succ 28160 8 sub_14 sub_15))))

end Ouroboros.BasinOneLowerCert
