module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2A 12288 8 = true := rfl
private theorem sub_01 : checkPow2A 12544 8 = true := rfl
private theorem sub_02 : checkPow2A 12800 8 = true := rfl
private theorem sub_03 : checkPow2A 13056 8 = true := rfl
private theorem sub_04 : checkPow2A 13312 8 = true := rfl
private theorem sub_05 : checkPow2A 13568 8 = true := rfl
private theorem sub_06 : checkPow2A 13824 8 = true := rfl
private theorem sub_07 : checkPow2A 14080 8 = true := rfl
private theorem sub_08 : checkPow2A 14336 8 = true := rfl
private theorem sub_09 : checkPow2A 14592 8 = true := rfl
private theorem sub_10 : checkPow2A 14848 8 = true := rfl
private theorem sub_11 : checkPow2A 15104 8 = true := rfl
private theorem sub_12 : checkPow2A 15360 8 = true := rfl
private theorem sub_13 : checkPow2A 15616 8 = true := rfl
private theorem sub_14 : checkPow2A 15872 8 = true := rfl
private theorem sub_15 : checkPow2A 16128 8 = true := rfl

theorem shard_A03 : checkPow2A 12288 12 = true :=
  (checkPow2A_succ 12288 11 (checkPow2A_succ 12288 10 (checkPow2A_succ 12288 9 (checkPow2A_succ 12288 8 sub_00 sub_01) (checkPow2A_succ 12800 8 sub_02 sub_03)) (checkPow2A_succ 13312 9 (checkPow2A_succ 13312 8 sub_04 sub_05) (checkPow2A_succ 13824 8 sub_06 sub_07))) (checkPow2A_succ 14336 10 (checkPow2A_succ 14336 9 (checkPow2A_succ 14336 8 sub_08 sub_09) (checkPow2A_succ 14848 8 sub_10 sub_11)) (checkPow2A_succ 15360 9 (checkPow2A_succ 15360 8 sub_12 sub_13) (checkPow2A_succ 15872 8 sub_14 sub_15))))

end Ouroboros.BasinOneLowerCert
