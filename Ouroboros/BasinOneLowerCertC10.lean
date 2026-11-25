module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2C 40960 8 = true := rfl
private theorem sub_01 : checkPow2C 41216 8 = true := rfl
private theorem sub_02 : checkPow2C 41472 8 = true := rfl
private theorem sub_03 : checkPow2C 41728 8 = true := rfl
private theorem sub_04 : checkPow2C 41984 8 = true := rfl
private theorem sub_05 : checkPow2C 42240 8 = true := rfl
private theorem sub_06 : checkPow2C 42496 8 = true := rfl
private theorem sub_07 : checkPow2C 42752 8 = true := rfl
private theorem sub_08 : checkPow2C 43008 8 = true := rfl
private theorem sub_09 : checkPow2C 43264 8 = true := rfl
private theorem sub_10 : checkPow2C 43520 8 = true := rfl
private theorem sub_11 : checkPow2C 43776 8 = true := rfl
private theorem sub_12 : checkPow2C 44032 8 = true := rfl
private theorem sub_13 : checkPow2C 44288 8 = true := rfl
private theorem sub_14 : checkPow2C 44544 8 = true := rfl
private theorem sub_15 : checkPow2C 44800 8 = true := rfl

theorem shard_C10 : checkPow2C 40960 12 = true :=
  (checkPow2C_succ 40960 11 (checkPow2C_succ 40960 10 (checkPow2C_succ 40960 9 (checkPow2C_succ 40960 8 sub_00 sub_01) (checkPow2C_succ 41472 8 sub_02 sub_03)) (checkPow2C_succ 41984 9 (checkPow2C_succ 41984 8 sub_04 sub_05) (checkPow2C_succ 42496 8 sub_06 sub_07))) (checkPow2C_succ 43008 10 (checkPow2C_succ 43008 9 (checkPow2C_succ 43008 8 sub_08 sub_09) (checkPow2C_succ 43520 8 sub_10 sub_11)) (checkPow2C_succ 44032 9 (checkPow2C_succ 44032 8 sub_12 sub_13) (checkPow2C_succ 44544 8 sub_14 sub_15))))

end Ouroboros.BasinOneLowerCert
