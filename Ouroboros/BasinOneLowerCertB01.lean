module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2B 8192 8 = true := rfl
private theorem sub_01 : checkPow2B 8448 8 = true := rfl
private theorem sub_02 : checkPow2B 8704 8 = true := rfl
private theorem sub_03 : checkPow2B 8960 8 = true := rfl
private theorem sub_04 : checkPow2B 9216 8 = true := rfl
private theorem sub_05 : checkPow2B 9472 8 = true := rfl
private theorem sub_06 : checkPow2B 9728 8 = true := rfl
private theorem sub_07 : checkPow2B 9984 8 = true := rfl
private theorem sub_08 : checkPow2B 10240 8 = true := rfl
private theorem sub_09 : checkPow2B 10496 8 = true := rfl
private theorem sub_10 : checkPow2B 10752 8 = true := rfl
private theorem sub_11 : checkPow2B 11008 8 = true := rfl
private theorem sub_12 : checkPow2B 11264 8 = true := rfl
private theorem sub_13 : checkPow2B 11520 8 = true := rfl
private theorem sub_14 : checkPow2B 11776 8 = true := rfl
private theorem sub_15 : checkPow2B 12032 8 = true := rfl
private theorem sub_16 : checkPow2B 12288 8 = true := rfl
private theorem sub_17 : checkPow2B 12544 8 = true := rfl
private theorem sub_18 : checkPow2B 12800 8 = true := rfl
private theorem sub_19 : checkPow2B 13056 8 = true := rfl
private theorem sub_20 : checkPow2B 13312 8 = true := rfl
private theorem sub_21 : checkPow2B 13568 8 = true := rfl
private theorem sub_22 : checkPow2B 13824 8 = true := rfl
private theorem sub_23 : checkPow2B 14080 8 = true := rfl
private theorem sub_24 : checkPow2B 14336 8 = true := rfl
private theorem sub_25 : checkPow2B 14592 8 = true := rfl
private theorem sub_26 : checkPow2B 14848 8 = true := rfl
private theorem sub_27 : checkPow2B 15104 8 = true := rfl
private theorem sub_28 : checkPow2B 15360 8 = true := rfl
private theorem sub_29 : checkPow2B 15616 8 = true := rfl
private theorem sub_30 : checkPow2B 15872 8 = true := rfl
private theorem sub_31 : checkPow2B 16128 8 = true := rfl

theorem shard_B01 : checkPow2B 8192 13 = true :=
  (checkPow2B_succ 8192 12 (checkPow2B_succ 8192 11 (checkPow2B_succ 8192 10 (checkPow2B_succ 8192 9 (checkPow2B_succ 8192 8 sub_00 sub_01) (checkPow2B_succ 8704 8 sub_02 sub_03)) (checkPow2B_succ 9216 9 (checkPow2B_succ 9216 8 sub_04 sub_05) (checkPow2B_succ 9728 8 sub_06 sub_07))) (checkPow2B_succ 10240 10 (checkPow2B_succ 10240 9 (checkPow2B_succ 10240 8 sub_08 sub_09) (checkPow2B_succ 10752 8 sub_10 sub_11)) (checkPow2B_succ 11264 9 (checkPow2B_succ 11264 8 sub_12 sub_13) (checkPow2B_succ 11776 8 sub_14 sub_15)))) (checkPow2B_succ 12288 11 (checkPow2B_succ 12288 10 (checkPow2B_succ 12288 9 (checkPow2B_succ 12288 8 sub_16 sub_17) (checkPow2B_succ 12800 8 sub_18 sub_19)) (checkPow2B_succ 13312 9 (checkPow2B_succ 13312 8 sub_20 sub_21) (checkPow2B_succ 13824 8 sub_22 sub_23))) (checkPow2B_succ 14336 10 (checkPow2B_succ 14336 9 (checkPow2B_succ 14336 8 sub_24 sub_25) (checkPow2B_succ 14848 8 sub_26 sub_27)) (checkPow2B_succ 15360 9 (checkPow2B_succ 15360 8 sub_28 sub_29) (checkPow2B_succ 15872 8 sub_30 sub_31)))))

end Ouroboros.BasinOneLowerCert
