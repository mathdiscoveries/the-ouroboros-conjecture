module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2B 40960 8 = true := rfl
private theorem sub_01 : checkPow2B 41216 8 = true := rfl
private theorem sub_02 : checkPow2B 41472 8 = true := rfl
private theorem sub_03 : checkPow2B 41728 8 = true := rfl
private theorem sub_04 : checkPow2B 41984 8 = true := rfl
private theorem sub_05 : checkPow2B 42240 8 = true := rfl
private theorem sub_06 : checkPow2B 42496 8 = true := rfl
private theorem sub_07 : checkPow2B 42752 8 = true := rfl
private theorem sub_08 : checkPow2B 43008 8 = true := rfl
private theorem sub_09 : checkPow2B 43264 8 = true := rfl
private theorem sub_10 : checkPow2B 43520 8 = true := rfl
private theorem sub_11 : checkPow2B 43776 8 = true := rfl
private theorem sub_12 : checkPow2B 44032 8 = true := rfl
private theorem sub_13 : checkPow2B 44288 8 = true := rfl
private theorem sub_14 : checkPow2B 44544 8 = true := rfl
private theorem sub_15 : checkPow2B 44800 8 = true := rfl
private theorem sub_16 : checkPow2B 45056 8 = true := rfl
private theorem sub_17 : checkPow2B 45312 8 = true := rfl
private theorem sub_18 : checkPow2B 45568 8 = true := rfl
private theorem sub_19 : checkPow2B 45824 8 = true := rfl
private theorem sub_20 : checkPow2B 46080 8 = true := rfl
private theorem sub_21 : checkPow2B 46336 8 = true := rfl
private theorem sub_22 : checkPow2B 46592 8 = true := rfl
private theorem sub_23 : checkPow2B 46848 8 = true := rfl
private theorem sub_24 : checkPow2B 47104 8 = true := rfl
private theorem sub_25 : checkPow2B 47360 8 = true := rfl
private theorem sub_26 : checkPow2B 47616 8 = true := rfl
private theorem sub_27 : checkPow2B 47872 8 = true := rfl
private theorem sub_28 : checkPow2B 48128 8 = true := rfl
private theorem sub_29 : checkPow2B 48384 8 = true := rfl
private theorem sub_30 : checkPow2B 48640 8 = true := rfl
private theorem sub_31 : checkPow2B 48896 8 = true := rfl

theorem shard_B05 : checkPow2B 40960 13 = true :=
  (checkPow2B_succ 40960 12 (checkPow2B_succ 40960 11 (checkPow2B_succ 40960 10 (checkPow2B_succ 40960 9 (checkPow2B_succ 40960 8 sub_00 sub_01) (checkPow2B_succ 41472 8 sub_02 sub_03)) (checkPow2B_succ 41984 9 (checkPow2B_succ 41984 8 sub_04 sub_05) (checkPow2B_succ 42496 8 sub_06 sub_07))) (checkPow2B_succ 43008 10 (checkPow2B_succ 43008 9 (checkPow2B_succ 43008 8 sub_08 sub_09) (checkPow2B_succ 43520 8 sub_10 sub_11)) (checkPow2B_succ 44032 9 (checkPow2B_succ 44032 8 sub_12 sub_13) (checkPow2B_succ 44544 8 sub_14 sub_15)))) (checkPow2B_succ 45056 11 (checkPow2B_succ 45056 10 (checkPow2B_succ 45056 9 (checkPow2B_succ 45056 8 sub_16 sub_17) (checkPow2B_succ 45568 8 sub_18 sub_19)) (checkPow2B_succ 46080 9 (checkPow2B_succ 46080 8 sub_20 sub_21) (checkPow2B_succ 46592 8 sub_22 sub_23))) (checkPow2B_succ 47104 10 (checkPow2B_succ 47104 9 (checkPow2B_succ 47104 8 sub_24 sub_25) (checkPow2B_succ 47616 8 sub_26 sub_27)) (checkPow2B_succ 48128 9 (checkPow2B_succ 48128 8 sub_28 sub_29) (checkPow2B_succ 48640 8 sub_30 sub_31)))))

end Ouroboros.BasinOneLowerCert
