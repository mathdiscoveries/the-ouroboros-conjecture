module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2B 16384 8 = true := rfl
private theorem sub_01 : checkPow2B 16640 8 = true := rfl
private theorem sub_02 : checkPow2B 16896 8 = true := rfl
private theorem sub_03 : checkPow2B 17152 8 = true := rfl
private theorem sub_04 : checkPow2B 17408 8 = true := rfl
private theorem sub_05 : checkPow2B 17664 8 = true := rfl
private theorem sub_06 : checkPow2B 17920 8 = true := rfl
private theorem sub_07 : checkPow2B 18176 8 = true := rfl
private theorem sub_08 : checkPow2B 18432 8 = true := rfl
private theorem sub_09 : checkPow2B 18688 8 = true := rfl
private theorem sub_10 : checkPow2B 18944 8 = true := rfl
private theorem sub_11 : checkPow2B 19200 8 = true := rfl
private theorem sub_12 : checkPow2B 19456 8 = true := rfl
private theorem sub_13 : checkPow2B 19712 8 = true := rfl
private theorem sub_14 : checkPow2B 19968 8 = true := rfl
private theorem sub_15 : checkPow2B 20224 8 = true := rfl
private theorem sub_16 : checkPow2B 20480 8 = true := rfl
private theorem sub_17 : checkPow2B 20736 8 = true := rfl
private theorem sub_18 : checkPow2B 20992 8 = true := rfl
private theorem sub_19 : checkPow2B 21248 8 = true := rfl
private theorem sub_20 : checkPow2B 21504 8 = true := rfl
private theorem sub_21 : checkPow2B 21760 8 = true := rfl
private theorem sub_22 : checkPow2B 22016 8 = true := rfl
private theorem sub_23 : checkPow2B 22272 8 = true := rfl
private theorem sub_24 : checkPow2B 22528 8 = true := rfl
private theorem sub_25 : checkPow2B 22784 8 = true := rfl
private theorem sub_26 : checkPow2B 23040 8 = true := rfl
private theorem sub_27 : checkPow2B 23296 8 = true := rfl
private theorem sub_28 : checkPow2B 23552 8 = true := rfl
private theorem sub_29 : checkPow2B 23808 8 = true := rfl
private theorem sub_30 : checkPow2B 24064 8 = true := rfl
private theorem sub_31 : checkPow2B 24320 8 = true := rfl

theorem shard_B02 : checkPow2B 16384 13 = true :=
  (checkPow2B_succ 16384 12 (checkPow2B_succ 16384 11 (checkPow2B_succ 16384 10 (checkPow2B_succ 16384 9 (checkPow2B_succ 16384 8 sub_00 sub_01) (checkPow2B_succ 16896 8 sub_02 sub_03)) (checkPow2B_succ 17408 9 (checkPow2B_succ 17408 8 sub_04 sub_05) (checkPow2B_succ 17920 8 sub_06 sub_07))) (checkPow2B_succ 18432 10 (checkPow2B_succ 18432 9 (checkPow2B_succ 18432 8 sub_08 sub_09) (checkPow2B_succ 18944 8 sub_10 sub_11)) (checkPow2B_succ 19456 9 (checkPow2B_succ 19456 8 sub_12 sub_13) (checkPow2B_succ 19968 8 sub_14 sub_15)))) (checkPow2B_succ 20480 11 (checkPow2B_succ 20480 10 (checkPow2B_succ 20480 9 (checkPow2B_succ 20480 8 sub_16 sub_17) (checkPow2B_succ 20992 8 sub_18 sub_19)) (checkPow2B_succ 21504 9 (checkPow2B_succ 21504 8 sub_20 sub_21) (checkPow2B_succ 22016 8 sub_22 sub_23))) (checkPow2B_succ 22528 10 (checkPow2B_succ 22528 9 (checkPow2B_succ 22528 8 sub_24 sub_25) (checkPow2B_succ 23040 8 sub_26 sub_27)) (checkPow2B_succ 23552 9 (checkPow2B_succ 23552 8 sub_28 sub_29) (checkPow2B_succ 24064 8 sub_30 sub_31)))))

end Ouroboros.BasinOneLowerCert
