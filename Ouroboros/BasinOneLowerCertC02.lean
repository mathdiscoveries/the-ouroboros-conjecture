module
public import Ouroboros.BasinOneLowerCertData

@[expose] public section

namespace Ouroboros.BasinOneLowerCert

private theorem sub_00 : checkPow2C 8192 8 = true := rfl
private theorem sub_01 : checkPow2C 8448 8 = true := rfl
private theorem sub_02 : checkPow2C 8704 8 = true := rfl
private theorem sub_03 : checkPow2C 8960 8 = true := rfl
private theorem sub_04 : checkPow2C 9216 8 = true := rfl
private theorem sub_05 : checkPow2C 9472 8 = true := rfl
private theorem sub_06 : checkPow2C 9728 8 = true := rfl
private theorem sub_07 : checkPow2C 9984 8 = true := rfl
private theorem sub_08 : checkPow2C 10240 8 = true := rfl
private theorem sub_09 : checkPow2C 10496 8 = true := rfl
private theorem sub_10 : checkPow2C 10752 8 = true := rfl
private theorem sub_11 : checkPow2C 11008 8 = true := rfl
private theorem sub_12 : checkPow2C 11264 8 = true := rfl
private theorem sub_13 : checkPow2C 11520 8 = true := rfl
private theorem sub_14 : checkPow2C 11776 8 = true := rfl
private theorem sub_15 : checkPow2C 12032 8 = true := rfl

theorem shard_C02 : checkPow2C 8192 12 = true :=
  (checkPow2C_succ 8192 11 (checkPow2C_succ 8192 10 (checkPow2C_succ 8192 9 (checkPow2C_succ 8192 8 sub_00 sub_01) (checkPow2C_succ 8704 8 sub_02 sub_03)) (checkPow2C_succ 9216 9 (checkPow2C_succ 9216 8 sub_04 sub_05) (checkPow2C_succ 9728 8 sub_06 sub_07))) (checkPow2C_succ 10240 10 (checkPow2C_succ 10240 9 (checkPow2C_succ 10240 8 sub_08 sub_09) (checkPow2C_succ 10752 8 sub_10 sub_11)) (checkPow2C_succ 11264 9 (checkPow2C_succ 11264 8 sub_12 sub_13) (checkPow2C_succ 11776 8 sub_14 sub_15))))

end Ouroboros.BasinOneLowerCert
