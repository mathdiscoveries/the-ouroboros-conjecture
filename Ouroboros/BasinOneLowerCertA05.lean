module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2A 20480 8 = true := rfl
private theorem sub_01 : checkPow2A 20736 8 = true := rfl
private theorem sub_02 : checkPow2A 20992 8 = true := rfl
private theorem sub_03 : checkPow2A 21248 8 = true := rfl
private theorem sub_04 : checkPow2A 21504 8 = true := rfl
private theorem sub_05 : checkPow2A 21760 8 = true := rfl
private theorem sub_06 : checkPow2A 22016 8 = true := rfl
private theorem sub_07 : checkPow2A 22272 8 = true := rfl
private theorem sub_08 : checkPow2A 22528 8 = true := rfl
private theorem sub_09 : checkPow2A 22784 8 = true := rfl
private theorem sub_10 : checkPow2A 23040 8 = true := rfl
private theorem sub_11 : checkPow2A 23296 8 = true := rfl
private theorem sub_12 : checkPow2A 23552 8 = true := rfl
private theorem sub_13 : checkPow2A 23808 8 = true := rfl
private theorem sub_14 : checkPow2A 24064 8 = true := rfl
private theorem sub_15 : checkPow2A 24320 8 = true := rfl

theorem shard_A05 : checkPow2A 20480 12 = true :=
  (checkPow2A_succ 20480 11 (checkPow2A_succ 20480 10 (checkPow2A_succ 20480 9 (checkPow2A_succ 20480 8 sub_00 sub_01) (checkPow2A_succ 20992 8 sub_02 sub_03)) (checkPow2A_succ 21504 9 (checkPow2A_succ 21504 8 sub_04 sub_05) (checkPow2A_succ 22016 8 sub_06 sub_07))) (checkPow2A_succ 22528 10 (checkPow2A_succ 22528 9 (checkPow2A_succ 22528 8 sub_08 sub_09) (checkPow2A_succ 23040 8 sub_10 sub_11)) (checkPow2A_succ 23552 9 (checkPow2A_succ 23552 8 sub_12 sub_13) (checkPow2A_succ 24064 8 sub_14 sub_15))))

end Ouroboros.BasinOneLowerCert
