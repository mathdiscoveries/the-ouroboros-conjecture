module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2A 16384 8 = true := rfl
private theorem sub_01 : checkPow2A 16640 8 = true := rfl
private theorem sub_02 : checkPow2A 16896 8 = true := rfl
private theorem sub_03 : checkPow2A 17152 8 = true := rfl
private theorem sub_04 : checkPow2A 17408 8 = true := rfl
private theorem sub_05 : checkPow2A 17664 8 = true := rfl
private theorem sub_06 : checkPow2A 17920 8 = true := rfl
private theorem sub_07 : checkPow2A 18176 8 = true := rfl
private theorem sub_08 : checkPow2A 18432 8 = true := rfl
private theorem sub_09 : checkPow2A 18688 8 = true := rfl
private theorem sub_10 : checkPow2A 18944 8 = true := rfl
private theorem sub_11 : checkPow2A 19200 8 = true := rfl
private theorem sub_12 : checkPow2A 19456 8 = true := rfl
private theorem sub_13 : checkPow2A 19712 8 = true := rfl
private theorem sub_14 : checkPow2A 19968 8 = true := rfl
private theorem sub_15 : checkPow2A 20224 8 = true := rfl

theorem shard_A04 : checkPow2A 16384 12 = true :=
  (checkPow2A_succ 16384 11 (checkPow2A_succ 16384 10 (checkPow2A_succ 16384 9 (checkPow2A_succ 16384 8 sub_00 sub_01) (checkPow2A_succ 16896 8 sub_02 sub_03)) (checkPow2A_succ 17408 9 (checkPow2A_succ 17408 8 sub_04 sub_05) (checkPow2A_succ 17920 8 sub_06 sub_07))) (checkPow2A_succ 18432 10 (checkPow2A_succ 18432 9 (checkPow2A_succ 18432 8 sub_08 sub_09) (checkPow2A_succ 18944 8 sub_10 sub_11)) (checkPow2A_succ 19456 9 (checkPow2A_succ 19456 8 sub_12 sub_13) (checkPow2A_succ 19968 8 sub_14 sub_15))))

end Ouroboros.BasinOneLowerCert
