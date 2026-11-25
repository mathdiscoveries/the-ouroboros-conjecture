module
public import Ouroboros.OddSurveyCertData
public import Ouroboros.OddSurveyCert00
public import Ouroboros.OddSurveyCert01
public import Ouroboros.OddSurveyCert02
public import Ouroboros.OddSurveyCert03
public import Ouroboros.OddSurveyCert04
public import Ouroboros.OddSurveyCert05
public import Ouroboros.OddSurveyCert06
public import Ouroboros.OddSurveyCert07
public import Ouroboros.OddSurveyCert08
public import Ouroboros.OddSurveyCert09
public import Ouroboros.OddSurveyCert10
public import Ouroboros.OddSurveyCert11
public import Ouroboros.OddSurveyCert12
public import Ouroboros.OddSurveyCert13
public import Ouroboros.OddSurveyCert14
public import Ouroboros.OddSurveyCert15
public import Ouroboros.OddSurveyCert16
public import Ouroboros.OddSurveyCert17
public import Ouroboros.OddSurveyCert18
public import Ouroboros.OddSurveyCert19
public import Ouroboros.OddSurveyCert20
public import Ouroboros.OddSurveyCert21
public import Ouroboros.OddSurveyCert22
public import Ouroboros.OddSurveyCert23
public import Ouroboros.OddSurveyCert24
public import Ouroboros.OddSurveyCert25
public import Ouroboros.OddSurveyCert26
public import Ouroboros.OddSurveyCert27
public import Ouroboros.OddSurveyCert28
public import Ouroboros.OddSurveyCert29
public import Ouroboros.OddSurveyCert30
public import Ouroboros.OddSurveyCert31

@[expose] public section

/-!
# Combined Pure-Kernel Odd-Base Survey Certificate (`905 / 999` odd bases `3 ≤ b ≤ 1,999`)

Combines all 32 parallel pure-kernel `rfl` shards (`OddSurveyCert00`..`OddSurveyCert31`) into:
- `trapOnlyList` (27 strictly increasing odd bases) with `trapOnly_cert_all`
- `splitList` (878 strictly increasing odd bases) with `split_cert_all`
- Pure-kernel proofs of strict sortedness, disjointness, lengths, and range `[3, 1999]`.
-/

namespace Ouroboros.OddSurveyCert

def isSortedStrict : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => Nat.ble (a + 1) b && isSortedStrict (b :: rest)

def allOddInRange : List Nat → Bool
  | [] => true
  | b :: rest => Nat.ble 3 b && Nat.ble b 1999 && Nat.beq (b % 2) 1 && allOddInRange rest

def memList (x : Nat) : List Nat → Bool
  | [] => false
  | h :: t => match Nat.beq x h with | true => true | false => memList x t

def allNotMem (l1 l2 : List Nat) : Bool :=
  l1.all (fun x => !memList x l2)

theorem all_cons {b : Nat} {bs : List Nat} {P : Nat → Prop}
    (hb : P b) (hbs : ∀ x ∈ bs, P x) : ∀ x ∈ b :: bs, P x := by
  intro x hx
  cases hx with
  | head => exact hb
  | tail _ h => exact hbs x h

theorem all_nil {P : Nat → Prop} : ∀ x ∈ ([] : List Nat), P x := by
  intro _ h; cases h

theorem all_append {l1 l2 : List Nat} {P : Nat → Prop}
    (h1 : ∀ x ∈ l1, P x) (h2 : ∀ x ∈ l2, P x) : ∀ x ∈ l1 ++ l2, P x := by
  intro x hx
  cases List.mem_append.mp hx with
  | inl h => exact h1 x h
  | inr h => exact h2 x h

theorem disj_append {l0 l1 l2 : List Nat}
    (h1 : ∀ x ∈ l0, x ∉ l1) (h2 : ∀ x ∈ l0, x ∉ l2) : ∀ x ∈ l0, x ∉ l1 ++ l2 := by
  intro x hx hm
  cases List.mem_append.mp hm with
  | inl h => exact h1 x hx h
  | inr h => exact h2 x hx h

theorem memList_false_of_not_mem (x : Nat) (l : List Nat) (h : memList x l = false) : x ∉ l := by
  induction l with
  | nil => intro hm; cases hm
  | cons y ys ih =>
    simp only [memList] at h
    cases hb : Nat.beq x y with
    | true => rw [hb] at h; cases h
    | false =>
      rw [hb] at h
      intro hm
      cases hm with
      | head => exact absurd (Nat.beq_refl x) (by rw [hb]; decide)
      | tail _ htail => exact ih h htail

theorem isSortedStrict_pairwise : ∀ l : List Nat, isSortedStrict l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ a
  | a :: b :: rest, h => by
    simp only [isSortedStrict, Bool.and_eq_true, Nat.ble_eq] at h
    have hp := isSortedStrict_pairwise (b :: rest) h.2
    refine List.pairwise_cons.mpr ⟨?_, hp⟩
    intro y hy
    cases hy with
    | head => omega
    | tail _ htail =>
      have hby := (List.pairwise_cons.mp hp).1 y htail
      omega

theorem pairwise_lt_append {l1 l2 : List Nat} {hi lo : Nat}
    (h1 : l1.Pairwise (· < ·)) (h2 : l2.Pairwise (· < ·))
    (hhi : ∀ x ∈ l1, x ≤ hi) (hlo : ∀ y ∈ l2, lo ≤ y) (hgap : hi < lo) :
    (l1 ++ l2).Pairwise (· < ·) := by
  rw [List.pairwise_append]
  refine ⟨h1, h2, fun x hx y hy => ?_⟩
  have := hhi x hx; have := hlo y hy; omega

theorem allLe_sound (bound : Nat) : ∀ l : List Nat, l.all (fun x => Nat.ble x bound) = true → ∀ x ∈ l, x ≤ bound
  | [], _, _, h => by cases h
  | a :: as, h, x, hx => by
    simp only [List.all_cons, Bool.and_eq_true, Nat.ble_eq] at h
    cases hx with
    | head => exact h.1
    | tail _ ht => exact allLe_sound bound as h.2 x ht

theorem allGe_sound (bound : Nat) : ∀ l : List Nat, l.all (fun x => Nat.ble bound x) = true → ∀ x ∈ l, bound ≤ x
  | [], _, _, h => by cases h
  | a :: as, h, x, hx => by
    simp only [List.all_cons, Bool.and_eq_true, Nat.ble_eq] at h
    cases hx with
    | head => exact h.1
    | tail _ ht => exact allGe_sound bound as h.2 x ht

theorem allOddInRange_sound : ∀ l : List Nat, allOddInRange l = true → ∀ b ∈ l, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1
  | [], _, _, h => by cases h
  | a :: as, h, x, hx => by
    simp only [allOddInRange, Bool.and_eq_true, Nat.ble_eq] at h
    cases hx with
    | head => exact ⟨h.1.1.1, h.1.1.2, Nat.eq_of_beq_eq_true h.1.2⟩
    | tail _ ht => exact allOddInRange_sound as h.2 x ht

theorem allNotMem_sound : ∀ l1 l2 : List Nat, allNotMem l1 l2 = true → ∀ x ∈ l1, x ∉ l2
  | [], _, _, _, h => by cases h
  | a :: as, l2, h, x, hx => by
    simp only [allNotMem, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    cases hx with
    | head => exact memList_false_of_not_mem a l2 h.1
    | tail _ ht => exact allNotMem_sound as l2 h.2 x ht

def trapOnlyList : List Nat := [5, 25, 29, 41, 89, 101, 173, 193, 221, 265, 281, 353, 365, 397, 533, 653, 793, 797, 877, 925, 1025, 1069, 1565, 1657, 1681, 1685, 1853]

theorem trapOnlyList_length : trapOnlyList.length = 27 := rfl
theorem trapOnlyList_pairwise_lt : trapOnlyList.Pairwise (· < ·) :=
  isSortedStrict_pairwise trapOnlyList rfl
theorem trapOnlyList_in_range : ∀ b ∈ trapOnlyList, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 :=
  allOddInRange_sound trapOnlyList rfl

theorem trapOnly_cert_all : ∀ b ∈ trapOnlyList, BaseCertified b false :=
  (all_cons cert_5 (all_cons cert_25 (all_cons cert_29 (all_cons cert_41 (all_cons cert_89 (all_cons cert_101 (all_cons cert_173 (all_cons cert_193 (all_cons cert_221 (all_cons cert_265 (all_cons cert_281 (all_cons cert_353 (all_cons cert_365 (all_cons cert_397 (all_cons cert_533 (all_cons cert_653 (all_cons cert_793 (all_cons cert_797 (all_cons cert_877 (all_cons cert_925 (all_cons cert_1025 (all_cons cert_1069 (all_cons cert_1565 (all_cons cert_1657 (all_cons cert_1681 (all_cons cert_1685 (all_cons cert_1853 all_nil)))))))))))))))))))))))))))

def splitCh_00 : List Nat := [3, 11, 13, 15, 17, 19, 31, 33, 37, 39, 43, 47, 49, 53, 55, 57, 59, 61, 65, 67, 69, 71, 73, 75, 77, 79, 81, 85, 87, 91, 93, 95]
theorem splitCh_00_len : splitCh_00.length = 32 := rfl
theorem splitCh_00_lt : splitCh_00.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_00 rfl
theorem splitCh_00_le : ∀ x ∈ splitCh_00, x ≤ 95 := allLe_sound 95 splitCh_00 rfl
theorem splitCh_00_ge : ∀ x ∈ splitCh_00, 3 ≤ x := allGe_sound 3 splitCh_00 rfl
theorem splitCh_00_rng : ∀ b ∈ splitCh_00, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_00 rfl
theorem splitCh_00_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_00 := allNotMem_sound trapOnlyList splitCh_00 rfl
theorem splitCh_00_cert : ∀ b ∈ splitCh_00, BaseCertified b true := (all_cons cert_3 (all_cons cert_11 (all_cons cert_13 (all_cons cert_15 (all_cons cert_17 (all_cons cert_19 (all_cons cert_31 (all_cons cert_33 (all_cons cert_37 (all_cons cert_39 (all_cons cert_43 (all_cons cert_47 (all_cons cert_49 (all_cons cert_53 (all_cons cert_55 (all_cons cert_57 (all_cons cert_59 (all_cons cert_61 (all_cons cert_65 (all_cons cert_67 (all_cons cert_69 (all_cons cert_71 (all_cons cert_73 (all_cons cert_75 (all_cons cert_77 (all_cons cert_79 (all_cons cert_81 (all_cons cert_85 (all_cons cert_87 (all_cons cert_91 (all_cons cert_93 (all_cons cert_95 all_nil))))))))))))))))))))))))))))))))

def splitCh_01 : List Nat := [97, 99, 103, 107, 109, 111, 113, 115, 117, 121, 123, 125, 127, 129, 131, 133, 135, 137, 139, 141, 145, 147, 149, 153, 155, 157, 159, 161, 163, 165, 169, 171]
theorem splitCh_01_len : splitCh_01.length = 32 := rfl
theorem splitCh_01_lt : splitCh_01.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_01 rfl
theorem splitCh_01_le : ∀ x ∈ splitCh_01, x ≤ 171 := allLe_sound 171 splitCh_01 rfl
theorem splitCh_01_ge : ∀ x ∈ splitCh_01, 97 ≤ x := allGe_sound 97 splitCh_01 rfl
theorem splitCh_01_rng : ∀ b ∈ splitCh_01, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_01 rfl
theorem splitCh_01_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_01 := allNotMem_sound trapOnlyList splitCh_01 rfl
theorem splitCh_01_cert : ∀ b ∈ splitCh_01, BaseCertified b true := (all_cons cert_97 (all_cons cert_99 (all_cons cert_103 (all_cons cert_107 (all_cons cert_109 (all_cons cert_111 (all_cons cert_113 (all_cons cert_115 (all_cons cert_117 (all_cons cert_121 (all_cons cert_123 (all_cons cert_125 (all_cons cert_127 (all_cons cert_129 (all_cons cert_131 (all_cons cert_133 (all_cons cert_135 (all_cons cert_137 (all_cons cert_139 (all_cons cert_141 (all_cons cert_145 (all_cons cert_147 (all_cons cert_149 (all_cons cert_153 (all_cons cert_155 (all_cons cert_157 (all_cons cert_159 (all_cons cert_161 (all_cons cert_163 (all_cons cert_165 (all_cons cert_169 (all_cons cert_171 all_nil))))))))))))))))))))))))))))))))

def splitCh_02 : List Nat := [181, 183, 185, 187, 191, 197, 199, 201, 203, 205, 207, 209, 211, 213, 215, 217, 223, 225, 229, 231, 233, 237, 239, 241, 243, 247, 249, 251, 257, 259, 261, 267]
theorem splitCh_02_len : splitCh_02.length = 32 := rfl
theorem splitCh_02_lt : splitCh_02.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_02 rfl
theorem splitCh_02_le : ∀ x ∈ splitCh_02, x ≤ 267 := allLe_sound 267 splitCh_02 rfl
theorem splitCh_02_ge : ∀ x ∈ splitCh_02, 181 ≤ x := allGe_sound 181 splitCh_02 rfl
theorem splitCh_02_rng : ∀ b ∈ splitCh_02, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_02 rfl
theorem splitCh_02_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_02 := allNotMem_sound trapOnlyList splitCh_02 rfl
theorem splitCh_02_cert : ∀ b ∈ splitCh_02, BaseCertified b true := (all_cons cert_181 (all_cons cert_183 (all_cons cert_185 (all_cons cert_187 (all_cons cert_191 (all_cons cert_197 (all_cons cert_199 (all_cons cert_201 (all_cons cert_203 (all_cons cert_205 (all_cons cert_207 (all_cons cert_209 (all_cons cert_211 (all_cons cert_213 (all_cons cert_215 (all_cons cert_217 (all_cons cert_223 (all_cons cert_225 (all_cons cert_229 (all_cons cert_231 (all_cons cert_233 (all_cons cert_237 (all_cons cert_239 (all_cons cert_241 (all_cons cert_243 (all_cons cert_247 (all_cons cert_249 (all_cons cert_251 (all_cons cert_257 (all_cons cert_259 (all_cons cert_261 (all_cons cert_267 all_nil))))))))))))))))))))))))))))))))

def splitCh_03 : List Nat := [269, 271, 273, 275, 277, 283, 285, 287, 289, 291, 293, 295, 297, 299, 301, 303, 305, 307, 309, 311, 313, 317, 319, 321, 323, 325, 327, 329, 331, 337, 339, 341]
theorem splitCh_03_len : splitCh_03.length = 32 := rfl
theorem splitCh_03_lt : splitCh_03.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_03 rfl
theorem splitCh_03_le : ∀ x ∈ splitCh_03, x ≤ 341 := allLe_sound 341 splitCh_03 rfl
theorem splitCh_03_ge : ∀ x ∈ splitCh_03, 269 ≤ x := allGe_sound 269 splitCh_03 rfl
theorem splitCh_03_rng : ∀ b ∈ splitCh_03, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_03 rfl
theorem splitCh_03_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_03 := allNotMem_sound trapOnlyList splitCh_03 rfl
theorem splitCh_03_cert : ∀ b ∈ splitCh_03, BaseCertified b true := (all_cons cert_269 (all_cons cert_271 (all_cons cert_273 (all_cons cert_275 (all_cons cert_277 (all_cons cert_283 (all_cons cert_285 (all_cons cert_287 (all_cons cert_289 (all_cons cert_291 (all_cons cert_293 (all_cons cert_295 (all_cons cert_297 (all_cons cert_299 (all_cons cert_301 (all_cons cert_303 (all_cons cert_305 (all_cons cert_307 (all_cons cert_309 (all_cons cert_311 (all_cons cert_313 (all_cons cert_317 (all_cons cert_319 (all_cons cert_321 (all_cons cert_323 (all_cons cert_325 (all_cons cert_327 (all_cons cert_329 (all_cons cert_331 (all_cons cert_337 (all_cons cert_339 (all_cons cert_341 all_nil))))))))))))))))))))))))))))))))

def splitCh_04 : List Nat := [343, 345, 347, 349, 351, 355, 357, 359, 361, 363, 367, 369, 371, 373, 375, 377, 379, 381, 383, 385, 389, 391, 393, 395, 399, 401, 403, 407, 409, 411, 413, 417]
theorem splitCh_04_len : splitCh_04.length = 32 := rfl
theorem splitCh_04_lt : splitCh_04.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_04 rfl
theorem splitCh_04_le : ∀ x ∈ splitCh_04, x ≤ 417 := allLe_sound 417 splitCh_04 rfl
theorem splitCh_04_ge : ∀ x ∈ splitCh_04, 343 ≤ x := allGe_sound 343 splitCh_04 rfl
theorem splitCh_04_rng : ∀ b ∈ splitCh_04, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_04 rfl
theorem splitCh_04_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_04 := allNotMem_sound trapOnlyList splitCh_04 rfl
theorem splitCh_04_cert : ∀ b ∈ splitCh_04, BaseCertified b true := (all_cons cert_343 (all_cons cert_345 (all_cons cert_347 (all_cons cert_349 (all_cons cert_351 (all_cons cert_355 (all_cons cert_357 (all_cons cert_359 (all_cons cert_361 (all_cons cert_363 (all_cons cert_367 (all_cons cert_369 (all_cons cert_371 (all_cons cert_373 (all_cons cert_375 (all_cons cert_377 (all_cons cert_379 (all_cons cert_381 (all_cons cert_383 (all_cons cert_385 (all_cons cert_389 (all_cons cert_391 (all_cons cert_393 (all_cons cert_395 (all_cons cert_399 (all_cons cert_401 (all_cons cert_403 (all_cons cert_407 (all_cons cert_409 (all_cons cert_411 (all_cons cert_413 (all_cons cert_417 all_nil))))))))))))))))))))))))))))))))

def splitCh_05 : List Nat := [419, 421, 423, 425, 427, 429, 431, 433, 435, 437, 439, 441, 443, 445, 447, 449, 451, 453, 457, 459, 461, 463, 467, 469, 471, 473, 475, 481, 483, 485, 487, 489]
theorem splitCh_05_len : splitCh_05.length = 32 := rfl
theorem splitCh_05_lt : splitCh_05.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_05 rfl
theorem splitCh_05_le : ∀ x ∈ splitCh_05, x ≤ 489 := allLe_sound 489 splitCh_05 rfl
theorem splitCh_05_ge : ∀ x ∈ splitCh_05, 419 ≤ x := allGe_sound 419 splitCh_05 rfl
theorem splitCh_05_rng : ∀ b ∈ splitCh_05, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_05 rfl
theorem splitCh_05_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_05 := allNotMem_sound trapOnlyList splitCh_05 rfl
theorem splitCh_05_cert : ∀ b ∈ splitCh_05, BaseCertified b true := (all_cons cert_419 (all_cons cert_421 (all_cons cert_423 (all_cons cert_425 (all_cons cert_427 (all_cons cert_429 (all_cons cert_431 (all_cons cert_433 (all_cons cert_435 (all_cons cert_437 (all_cons cert_439 (all_cons cert_441 (all_cons cert_443 (all_cons cert_445 (all_cons cert_447 (all_cons cert_449 (all_cons cert_451 (all_cons cert_453 (all_cons cert_457 (all_cons cert_459 (all_cons cert_461 (all_cons cert_463 (all_cons cert_467 (all_cons cert_469 (all_cons cert_471 (all_cons cert_473 (all_cons cert_475 (all_cons cert_481 (all_cons cert_483 (all_cons cert_485 (all_cons cert_487 (all_cons cert_489 all_nil))))))))))))))))))))))))))))))))

def splitCh_06 : List Nat := [491, 493, 495, 497, 499, 501, 503, 505, 507, 509, 511, 513, 515, 517, 521, 523, 525, 527, 529, 531, 537, 539, 541, 543, 545, 547, 549, 551, 553, 555, 557, 559]
theorem splitCh_06_len : splitCh_06.length = 32 := rfl
theorem splitCh_06_lt : splitCh_06.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_06 rfl
theorem splitCh_06_le : ∀ x ∈ splitCh_06, x ≤ 559 := allLe_sound 559 splitCh_06 rfl
theorem splitCh_06_ge : ∀ x ∈ splitCh_06, 491 ≤ x := allGe_sound 491 splitCh_06 rfl
theorem splitCh_06_rng : ∀ b ∈ splitCh_06, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_06 rfl
theorem splitCh_06_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_06 := allNotMem_sound trapOnlyList splitCh_06 rfl
theorem splitCh_06_cert : ∀ b ∈ splitCh_06, BaseCertified b true := (all_cons cert_491 (all_cons cert_493 (all_cons cert_495 (all_cons cert_497 (all_cons cert_499 (all_cons cert_501 (all_cons cert_503 (all_cons cert_505 (all_cons cert_507 (all_cons cert_509 (all_cons cert_511 (all_cons cert_513 (all_cons cert_515 (all_cons cert_517 (all_cons cert_521 (all_cons cert_523 (all_cons cert_525 (all_cons cert_527 (all_cons cert_529 (all_cons cert_531 (all_cons cert_537 (all_cons cert_539 (all_cons cert_541 (all_cons cert_543 (all_cons cert_545 (all_cons cert_547 (all_cons cert_549 (all_cons cert_551 (all_cons cert_553 (all_cons cert_555 (all_cons cert_557 (all_cons cert_559 all_nil))))))))))))))))))))))))))))))))

def splitCh_07 : List Nat := [561, 563, 565, 567, 569, 571, 573, 577, 579, 583, 585, 587, 589, 591, 593, 595, 597, 599, 601, 603, 605, 607, 609, 611, 613, 617, 619, 623, 625, 627, 629, 631]
theorem splitCh_07_len : splitCh_07.length = 32 := rfl
theorem splitCh_07_lt : splitCh_07.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_07 rfl
theorem splitCh_07_le : ∀ x ∈ splitCh_07, x ≤ 631 := allLe_sound 631 splitCh_07 rfl
theorem splitCh_07_ge : ∀ x ∈ splitCh_07, 561 ≤ x := allGe_sound 561 splitCh_07 rfl
theorem splitCh_07_rng : ∀ b ∈ splitCh_07, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_07 rfl
theorem splitCh_07_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_07 := allNotMem_sound trapOnlyList splitCh_07 rfl
theorem splitCh_07_cert : ∀ b ∈ splitCh_07, BaseCertified b true := (all_cons cert_561 (all_cons cert_563 (all_cons cert_565 (all_cons cert_567 (all_cons cert_569 (all_cons cert_571 (all_cons cert_573 (all_cons cert_577 (all_cons cert_579 (all_cons cert_583 (all_cons cert_585 (all_cons cert_587 (all_cons cert_589 (all_cons cert_591 (all_cons cert_593 (all_cons cert_595 (all_cons cert_597 (all_cons cert_599 (all_cons cert_601 (all_cons cert_603 (all_cons cert_605 (all_cons cert_607 (all_cons cert_609 (all_cons cert_611 (all_cons cert_613 (all_cons cert_617 (all_cons cert_619 (all_cons cert_623 (all_cons cert_625 (all_cons cert_627 (all_cons cert_629 (all_cons cert_631 all_nil))))))))))))))))))))))))))))))))

def splitCh_08 : List Nat := [633, 635, 637, 639, 641, 643, 645, 649, 651, 657, 661, 663, 665, 667, 671, 673, 675, 677, 679, 681, 683, 685, 687, 689, 691, 693, 695, 697, 699, 701, 703, 705]
theorem splitCh_08_len : splitCh_08.length = 32 := rfl
theorem splitCh_08_lt : splitCh_08.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_08 rfl
theorem splitCh_08_le : ∀ x ∈ splitCh_08, x ≤ 705 := allLe_sound 705 splitCh_08 rfl
theorem splitCh_08_ge : ∀ x ∈ splitCh_08, 633 ≤ x := allGe_sound 633 splitCh_08 rfl
theorem splitCh_08_rng : ∀ b ∈ splitCh_08, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_08 rfl
theorem splitCh_08_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_08 := allNotMem_sound trapOnlyList splitCh_08 rfl
theorem splitCh_08_cert : ∀ b ∈ splitCh_08, BaseCertified b true := (all_cons cert_633 (all_cons cert_635 (all_cons cert_637 (all_cons cert_639 (all_cons cert_641 (all_cons cert_643 (all_cons cert_645 (all_cons cert_649 (all_cons cert_651 (all_cons cert_657 (all_cons cert_661 (all_cons cert_663 (all_cons cert_665 (all_cons cert_667 (all_cons cert_671 (all_cons cert_673 (all_cons cert_675 (all_cons cert_677 (all_cons cert_679 (all_cons cert_681 (all_cons cert_683 (all_cons cert_685 (all_cons cert_687 (all_cons cert_689 (all_cons cert_691 (all_cons cert_693 (all_cons cert_695 (all_cons cert_697 (all_cons cert_699 (all_cons cert_701 (all_cons cert_703 (all_cons cert_705 all_nil))))))))))))))))))))))))))))))))

def splitCh_09 : List Nat := [707, 709, 711, 713, 715, 721, 723, 725, 727, 729, 731, 733, 735, 737, 739, 741, 743, 745, 747, 749, 753, 755, 757, 761, 763, 765, 767, 769, 771, 773, 775, 777]
theorem splitCh_09_len : splitCh_09.length = 32 := rfl
theorem splitCh_09_lt : splitCh_09.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_09 rfl
theorem splitCh_09_le : ∀ x ∈ splitCh_09, x ≤ 777 := allLe_sound 777 splitCh_09 rfl
theorem splitCh_09_ge : ∀ x ∈ splitCh_09, 707 ≤ x := allGe_sound 707 splitCh_09 rfl
theorem splitCh_09_rng : ∀ b ∈ splitCh_09, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_09 rfl
theorem splitCh_09_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_09 := allNotMem_sound trapOnlyList splitCh_09 rfl
theorem splitCh_09_cert : ∀ b ∈ splitCh_09, BaseCertified b true := (all_cons cert_707 (all_cons cert_709 (all_cons cert_711 (all_cons cert_713 (all_cons cert_715 (all_cons cert_721 (all_cons cert_723 (all_cons cert_725 (all_cons cert_727 (all_cons cert_729 (all_cons cert_731 (all_cons cert_733 (all_cons cert_735 (all_cons cert_737 (all_cons cert_739 (all_cons cert_741 (all_cons cert_743 (all_cons cert_745 (all_cons cert_747 (all_cons cert_749 (all_cons cert_753 (all_cons cert_755 (all_cons cert_757 (all_cons cert_761 (all_cons cert_763 (all_cons cert_765 (all_cons cert_767 (all_cons cert_769 (all_cons cert_771 (all_cons cert_773 (all_cons cert_775 (all_cons cert_777 all_nil))))))))))))))))))))))))))))))))

def splitCh_10 : List Nat := [781, 783, 785, 787, 789, 791, 795, 799, 801, 803, 805, 807, 809, 811, 813, 817, 819, 821, 823, 825, 827, 829, 831, 833, 835, 837, 841, 843, 845, 847, 849, 851]
theorem splitCh_10_len : splitCh_10.length = 32 := rfl
theorem splitCh_10_lt : splitCh_10.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_10 rfl
theorem splitCh_10_le : ∀ x ∈ splitCh_10, x ≤ 851 := allLe_sound 851 splitCh_10 rfl
theorem splitCh_10_ge : ∀ x ∈ splitCh_10, 781 ≤ x := allGe_sound 781 splitCh_10 rfl
theorem splitCh_10_rng : ∀ b ∈ splitCh_10, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_10 rfl
theorem splitCh_10_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_10 := allNotMem_sound trapOnlyList splitCh_10 rfl
theorem splitCh_10_cert : ∀ b ∈ splitCh_10, BaseCertified b true := (all_cons cert_781 (all_cons cert_783 (all_cons cert_785 (all_cons cert_787 (all_cons cert_789 (all_cons cert_791 (all_cons cert_795 (all_cons cert_799 (all_cons cert_801 (all_cons cert_803 (all_cons cert_805 (all_cons cert_807 (all_cons cert_809 (all_cons cert_811 (all_cons cert_813 (all_cons cert_817 (all_cons cert_819 (all_cons cert_821 (all_cons cert_823 (all_cons cert_825 (all_cons cert_827 (all_cons cert_829 (all_cons cert_831 (all_cons cert_833 (all_cons cert_835 (all_cons cert_837 (all_cons cert_841 (all_cons cert_843 (all_cons cert_845 (all_cons cert_847 (all_cons cert_849 (all_cons cert_851 all_nil))))))))))))))))))))))))))))))))

def splitCh_11 : List Nat := [853, 855, 857, 859, 861, 863, 865, 867, 869, 871, 875, 881, 883, 885, 887, 889, 891, 893, 895, 897, 901, 903, 905, 907, 909, 913, 915, 917, 919, 921, 923, 927]
theorem splitCh_11_len : splitCh_11.length = 32 := rfl
theorem splitCh_11_lt : splitCh_11.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_11 rfl
theorem splitCh_11_le : ∀ x ∈ splitCh_11, x ≤ 927 := allLe_sound 927 splitCh_11 rfl
theorem splitCh_11_ge : ∀ x ∈ splitCh_11, 853 ≤ x := allGe_sound 853 splitCh_11 rfl
theorem splitCh_11_rng : ∀ b ∈ splitCh_11, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_11 rfl
theorem splitCh_11_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_11 := allNotMem_sound trapOnlyList splitCh_11 rfl
theorem splitCh_11_cert : ∀ b ∈ splitCh_11, BaseCertified b true := (all_cons cert_853 (all_cons cert_855 (all_cons cert_857 (all_cons cert_859 (all_cons cert_861 (all_cons cert_863 (all_cons cert_865 (all_cons cert_867 (all_cons cert_869 (all_cons cert_871 (all_cons cert_875 (all_cons cert_881 (all_cons cert_883 (all_cons cert_885 (all_cons cert_887 (all_cons cert_889 (all_cons cert_891 (all_cons cert_893 (all_cons cert_895 (all_cons cert_897 (all_cons cert_901 (all_cons cert_903 (all_cons cert_905 (all_cons cert_907 (all_cons cert_909 (all_cons cert_913 (all_cons cert_915 (all_cons cert_917 (all_cons cert_919 (all_cons cert_921 (all_cons cert_923 (all_cons cert_927 all_nil))))))))))))))))))))))))))))))))

def splitCh_12 : List Nat := [929, 931, 933, 935, 937, 939, 941, 943, 945, 947, 949, 951, 953, 955, 957, 959, 961, 963, 965, 967, 969, 973, 975, 977, 979, 981, 983, 985, 987, 989, 991, 993]
theorem splitCh_12_len : splitCh_12.length = 32 := rfl
theorem splitCh_12_lt : splitCh_12.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_12 rfl
theorem splitCh_12_le : ∀ x ∈ splitCh_12, x ≤ 993 := allLe_sound 993 splitCh_12 rfl
theorem splitCh_12_ge : ∀ x ∈ splitCh_12, 929 ≤ x := allGe_sound 929 splitCh_12 rfl
theorem splitCh_12_rng : ∀ b ∈ splitCh_12, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_12 rfl
theorem splitCh_12_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_12 := allNotMem_sound trapOnlyList splitCh_12 rfl
theorem splitCh_12_cert : ∀ b ∈ splitCh_12, BaseCertified b true := (all_cons cert_929 (all_cons cert_931 (all_cons cert_933 (all_cons cert_935 (all_cons cert_937 (all_cons cert_939 (all_cons cert_941 (all_cons cert_943 (all_cons cert_945 (all_cons cert_947 (all_cons cert_949 (all_cons cert_951 (all_cons cert_953 (all_cons cert_955 (all_cons cert_957 (all_cons cert_959 (all_cons cert_961 (all_cons cert_963 (all_cons cert_965 (all_cons cert_967 (all_cons cert_969 (all_cons cert_973 (all_cons cert_975 (all_cons cert_977 (all_cons cert_979 (all_cons cert_981 (all_cons cert_983 (all_cons cert_985 (all_cons cert_987 (all_cons cert_989 (all_cons cert_991 (all_cons cert_993 all_nil))))))))))))))))))))))))))))))))

def splitCh_13 : List Nat := [995, 997, 999, 1001, 1003, 1005, 1007, 1009, 1011, 1013, 1015, 1017, 1019, 1021, 1023, 1027, 1029, 1031, 1033, 1035, 1037, 1039, 1041, 1043, 1045, 1047, 1049, 1051, 1053, 1055, 1057, 1061]
theorem splitCh_13_len : splitCh_13.length = 32 := rfl
theorem splitCh_13_lt : splitCh_13.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_13 rfl
theorem splitCh_13_le : ∀ x ∈ splitCh_13, x ≤ 1061 := allLe_sound 1061 splitCh_13 rfl
theorem splitCh_13_ge : ∀ x ∈ splitCh_13, 995 ≤ x := allGe_sound 995 splitCh_13 rfl
theorem splitCh_13_rng : ∀ b ∈ splitCh_13, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_13 rfl
theorem splitCh_13_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_13 := allNotMem_sound trapOnlyList splitCh_13 rfl
theorem splitCh_13_cert : ∀ b ∈ splitCh_13, BaseCertified b true := (all_cons cert_995 (all_cons cert_997 (all_cons cert_999 (all_cons cert_1001 (all_cons cert_1003 (all_cons cert_1005 (all_cons cert_1007 (all_cons cert_1009 (all_cons cert_1011 (all_cons cert_1013 (all_cons cert_1015 (all_cons cert_1017 (all_cons cert_1019 (all_cons cert_1021 (all_cons cert_1023 (all_cons cert_1027 (all_cons cert_1029 (all_cons cert_1031 (all_cons cert_1033 (all_cons cert_1035 (all_cons cert_1037 (all_cons cert_1039 (all_cons cert_1041 (all_cons cert_1043 (all_cons cert_1045 (all_cons cert_1047 (all_cons cert_1049 (all_cons cert_1051 (all_cons cert_1053 (all_cons cert_1055 (all_cons cert_1057 (all_cons cert_1061 all_nil))))))))))))))))))))))))))))))))

def splitCh_14 : List Nat := [1063, 1065, 1067, 1071, 1073, 1075, 1077, 1079, 1081, 1083, 1085, 1087, 1089, 1091, 1093, 1095, 1097, 1099, 1101, 1103, 1105, 1107, 1109, 1111, 1113, 1115, 1117, 1119, 1121, 1123, 1125, 1127]
theorem splitCh_14_len : splitCh_14.length = 32 := rfl
theorem splitCh_14_lt : splitCh_14.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_14 rfl
theorem splitCh_14_le : ∀ x ∈ splitCh_14, x ≤ 1127 := allLe_sound 1127 splitCh_14 rfl
theorem splitCh_14_ge : ∀ x ∈ splitCh_14, 1063 ≤ x := allGe_sound 1063 splitCh_14 rfl
theorem splitCh_14_rng : ∀ b ∈ splitCh_14, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_14 rfl
theorem splitCh_14_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_14 := allNotMem_sound trapOnlyList splitCh_14 rfl
theorem splitCh_14_cert : ∀ b ∈ splitCh_14, BaseCertified b true := (all_cons cert_1063 (all_cons cert_1065 (all_cons cert_1067 (all_cons cert_1071 (all_cons cert_1073 (all_cons cert_1075 (all_cons cert_1077 (all_cons cert_1079 (all_cons cert_1081 (all_cons cert_1083 (all_cons cert_1085 (all_cons cert_1087 (all_cons cert_1089 (all_cons cert_1091 (all_cons cert_1093 (all_cons cert_1095 (all_cons cert_1097 (all_cons cert_1099 (all_cons cert_1101 (all_cons cert_1103 (all_cons cert_1105 (all_cons cert_1107 (all_cons cert_1109 (all_cons cert_1111 (all_cons cert_1113 (all_cons cert_1115 (all_cons cert_1117 (all_cons cert_1119 (all_cons cert_1121 (all_cons cert_1123 (all_cons cert_1125 (all_cons cert_1127 all_nil))))))))))))))))))))))))))))))))

def splitCh_15 : List Nat := [1129, 1133, 1135, 1137, 1139, 1141, 1145, 1147, 1149, 1151, 1153, 1155, 1157, 1159, 1161, 1163, 1165, 1167, 1169, 1171, 1177, 1179, 1181, 1183, 1185, 1187, 1189, 1191, 1193, 1195, 1197, 1199]
theorem splitCh_15_len : splitCh_15.length = 32 := rfl
theorem splitCh_15_lt : splitCh_15.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_15 rfl
theorem splitCh_15_le : ∀ x ∈ splitCh_15, x ≤ 1199 := allLe_sound 1199 splitCh_15 rfl
theorem splitCh_15_ge : ∀ x ∈ splitCh_15, 1129 ≤ x := allGe_sound 1129 splitCh_15 rfl
theorem splitCh_15_rng : ∀ b ∈ splitCh_15, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_15 rfl
theorem splitCh_15_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_15 := allNotMem_sound trapOnlyList splitCh_15 rfl
theorem splitCh_15_cert : ∀ b ∈ splitCh_15, BaseCertified b true := (all_cons cert_1129 (all_cons cert_1133 (all_cons cert_1135 (all_cons cert_1137 (all_cons cert_1139 (all_cons cert_1141 (all_cons cert_1145 (all_cons cert_1147 (all_cons cert_1149 (all_cons cert_1151 (all_cons cert_1153 (all_cons cert_1155 (all_cons cert_1157 (all_cons cert_1159 (all_cons cert_1161 (all_cons cert_1163 (all_cons cert_1165 (all_cons cert_1167 (all_cons cert_1169 (all_cons cert_1171 (all_cons cert_1177 (all_cons cert_1179 (all_cons cert_1181 (all_cons cert_1183 (all_cons cert_1185 (all_cons cert_1187 (all_cons cert_1189 (all_cons cert_1191 (all_cons cert_1193 (all_cons cert_1195 (all_cons cert_1197 (all_cons cert_1199 all_nil))))))))))))))))))))))))))))))))

def splitCh_16 : List Nat := [1201, 1203, 1205, 1207, 1209, 1211, 1213, 1215, 1217, 1219, 1221, 1223, 1225, 1227, 1229, 1231, 1233, 1237, 1239, 1241, 1243, 1245, 1247, 1249, 1251, 1253, 1255, 1257, 1259, 1261, 1263, 1265]
theorem splitCh_16_len : splitCh_16.length = 32 := rfl
theorem splitCh_16_lt : splitCh_16.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_16 rfl
theorem splitCh_16_le : ∀ x ∈ splitCh_16, x ≤ 1265 := allLe_sound 1265 splitCh_16 rfl
theorem splitCh_16_ge : ∀ x ∈ splitCh_16, 1201 ≤ x := allGe_sound 1201 splitCh_16 rfl
theorem splitCh_16_rng : ∀ b ∈ splitCh_16, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_16 rfl
theorem splitCh_16_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_16 := allNotMem_sound trapOnlyList splitCh_16 rfl
theorem splitCh_16_cert : ∀ b ∈ splitCh_16, BaseCertified b true := (all_cons cert_1201 (all_cons cert_1203 (all_cons cert_1205 (all_cons cert_1207 (all_cons cert_1209 (all_cons cert_1211 (all_cons cert_1213 (all_cons cert_1215 (all_cons cert_1217 (all_cons cert_1219 (all_cons cert_1221 (all_cons cert_1223 (all_cons cert_1225 (all_cons cert_1227 (all_cons cert_1229 (all_cons cert_1231 (all_cons cert_1233 (all_cons cert_1237 (all_cons cert_1239 (all_cons cert_1241 (all_cons cert_1243 (all_cons cert_1245 (all_cons cert_1247 (all_cons cert_1249 (all_cons cert_1251 (all_cons cert_1253 (all_cons cert_1255 (all_cons cert_1257 (all_cons cert_1259 (all_cons cert_1261 (all_cons cert_1263 (all_cons cert_1265 all_nil))))))))))))))))))))))))))))))))

def splitCh_17 : List Nat := [1267, 1269, 1271, 1273, 1275, 1277, 1281, 1283, 1285, 1287, 1289, 1293, 1295, 1297, 1299, 1301, 1303, 1305, 1307, 1309, 1311, 1313, 1315, 1317, 1319, 1321, 1323, 1325, 1327, 1329, 1331, 1333]
theorem splitCh_17_len : splitCh_17.length = 32 := rfl
theorem splitCh_17_lt : splitCh_17.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_17 rfl
theorem splitCh_17_le : ∀ x ∈ splitCh_17, x ≤ 1333 := allLe_sound 1333 splitCh_17 rfl
theorem splitCh_17_ge : ∀ x ∈ splitCh_17, 1267 ≤ x := allGe_sound 1267 splitCh_17 rfl
theorem splitCh_17_rng : ∀ b ∈ splitCh_17, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_17 rfl
theorem splitCh_17_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_17 := allNotMem_sound trapOnlyList splitCh_17 rfl
theorem splitCh_17_cert : ∀ b ∈ splitCh_17, BaseCertified b true := (all_cons cert_1267 (all_cons cert_1269 (all_cons cert_1271 (all_cons cert_1273 (all_cons cert_1275 (all_cons cert_1277 (all_cons cert_1281 (all_cons cert_1283 (all_cons cert_1285 (all_cons cert_1287 (all_cons cert_1289 (all_cons cert_1293 (all_cons cert_1295 (all_cons cert_1297 (all_cons cert_1299 (all_cons cert_1301 (all_cons cert_1303 (all_cons cert_1305 (all_cons cert_1307 (all_cons cert_1309 (all_cons cert_1311 (all_cons cert_1313 (all_cons cert_1315 (all_cons cert_1317 (all_cons cert_1319 (all_cons cert_1321 (all_cons cert_1323 (all_cons cert_1325 (all_cons cert_1327 (all_cons cert_1329 (all_cons cert_1331 (all_cons cert_1333 all_nil))))))))))))))))))))))))))))))))

def splitCh_18 : List Nat := [1339, 1341, 1343, 1345, 1347, 1349, 1351, 1353, 1355, 1357, 1359, 1361, 1363, 1367, 1369, 1371, 1373, 1375, 1377, 1379, 1381, 1383, 1385, 1387, 1389, 1391, 1393, 1395, 1397, 1399, 1401, 1403]
theorem splitCh_18_len : splitCh_18.length = 32 := rfl
theorem splitCh_18_lt : splitCh_18.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_18 rfl
theorem splitCh_18_le : ∀ x ∈ splitCh_18, x ≤ 1403 := allLe_sound 1403 splitCh_18 rfl
theorem splitCh_18_ge : ∀ x ∈ splitCh_18, 1339 ≤ x := allGe_sound 1339 splitCh_18 rfl
theorem splitCh_18_rng : ∀ b ∈ splitCh_18, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_18 rfl
theorem splitCh_18_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_18 := allNotMem_sound trapOnlyList splitCh_18 rfl
theorem splitCh_18_cert : ∀ b ∈ splitCh_18, BaseCertified b true := (all_cons cert_1339 (all_cons cert_1341 (all_cons cert_1343 (all_cons cert_1345 (all_cons cert_1347 (all_cons cert_1349 (all_cons cert_1351 (all_cons cert_1353 (all_cons cert_1355 (all_cons cert_1357 (all_cons cert_1359 (all_cons cert_1361 (all_cons cert_1363 (all_cons cert_1367 (all_cons cert_1369 (all_cons cert_1371 (all_cons cert_1373 (all_cons cert_1375 (all_cons cert_1377 (all_cons cert_1379 (all_cons cert_1381 (all_cons cert_1383 (all_cons cert_1385 (all_cons cert_1387 (all_cons cert_1389 (all_cons cert_1391 (all_cons cert_1393 (all_cons cert_1395 (all_cons cert_1397 (all_cons cert_1399 (all_cons cert_1401 (all_cons cert_1403 all_nil))))))))))))))))))))))))))))))))

def splitCh_19 : List Nat := [1405, 1407, 1409, 1411, 1413, 1415, 1417, 1419, 1421, 1423, 1425, 1427, 1429, 1431, 1433, 1437, 1441, 1443, 1445, 1447, 1449, 1451, 1453, 1455, 1457, 1459, 1463, 1465, 1467, 1469, 1471, 1473]
theorem splitCh_19_len : splitCh_19.length = 32 := rfl
theorem splitCh_19_lt : splitCh_19.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_19 rfl
theorem splitCh_19_le : ∀ x ∈ splitCh_19, x ≤ 1473 := allLe_sound 1473 splitCh_19 rfl
theorem splitCh_19_ge : ∀ x ∈ splitCh_19, 1405 ≤ x := allGe_sound 1405 splitCh_19 rfl
theorem splitCh_19_rng : ∀ b ∈ splitCh_19, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_19 rfl
theorem splitCh_19_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_19 := allNotMem_sound trapOnlyList splitCh_19 rfl
theorem splitCh_19_cert : ∀ b ∈ splitCh_19, BaseCertified b true := (all_cons cert_1405 (all_cons cert_1407 (all_cons cert_1409 (all_cons cert_1411 (all_cons cert_1413 (all_cons cert_1415 (all_cons cert_1417 (all_cons cert_1419 (all_cons cert_1421 (all_cons cert_1423 (all_cons cert_1425 (all_cons cert_1427 (all_cons cert_1429 (all_cons cert_1431 (all_cons cert_1433 (all_cons cert_1437 (all_cons cert_1441 (all_cons cert_1443 (all_cons cert_1445 (all_cons cert_1447 (all_cons cert_1449 (all_cons cert_1451 (all_cons cert_1453 (all_cons cert_1455 (all_cons cert_1457 (all_cons cert_1459 (all_cons cert_1463 (all_cons cert_1465 (all_cons cert_1467 (all_cons cert_1469 (all_cons cert_1471 (all_cons cert_1473 all_nil))))))))))))))))))))))))))))))))

def splitCh_20 : List Nat := [1475, 1477, 1479, 1481, 1483, 1485, 1487, 1489, 1491, 1493, 1497, 1499, 1501, 1503, 1505, 1507, 1509, 1511, 1513, 1515, 1517, 1519, 1523, 1525, 1527, 1529, 1531, 1533, 1535, 1537, 1539, 1541]
theorem splitCh_20_len : splitCh_20.length = 32 := rfl
theorem splitCh_20_lt : splitCh_20.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_20 rfl
theorem splitCh_20_le : ∀ x ∈ splitCh_20, x ≤ 1541 := allLe_sound 1541 splitCh_20 rfl
theorem splitCh_20_ge : ∀ x ∈ splitCh_20, 1475 ≤ x := allGe_sound 1475 splitCh_20 rfl
theorem splitCh_20_rng : ∀ b ∈ splitCh_20, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_20 rfl
theorem splitCh_20_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_20 := allNotMem_sound trapOnlyList splitCh_20 rfl
theorem splitCh_20_cert : ∀ b ∈ splitCh_20, BaseCertified b true := (all_cons cert_1475 (all_cons cert_1477 (all_cons cert_1479 (all_cons cert_1481 (all_cons cert_1483 (all_cons cert_1485 (all_cons cert_1487 (all_cons cert_1489 (all_cons cert_1491 (all_cons cert_1493 (all_cons cert_1497 (all_cons cert_1499 (all_cons cert_1501 (all_cons cert_1503 (all_cons cert_1505 (all_cons cert_1507 (all_cons cert_1509 (all_cons cert_1511 (all_cons cert_1513 (all_cons cert_1515 (all_cons cert_1517 (all_cons cert_1519 (all_cons cert_1523 (all_cons cert_1525 (all_cons cert_1527 (all_cons cert_1529 (all_cons cert_1531 (all_cons cert_1533 (all_cons cert_1535 (all_cons cert_1537 (all_cons cert_1539 (all_cons cert_1541 all_nil))))))))))))))))))))))))))))))))

def splitCh_21 : List Nat := [1543, 1545, 1547, 1549, 1551, 1553, 1555, 1557, 1559, 1561, 1563, 1567, 1569, 1571, 1575, 1577, 1579, 1583, 1585, 1587, 1589, 1591, 1593, 1597, 1599, 1601, 1603, 1605, 1607, 1609, 1611, 1613]
theorem splitCh_21_len : splitCh_21.length = 32 := rfl
theorem splitCh_21_lt : splitCh_21.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_21 rfl
theorem splitCh_21_le : ∀ x ∈ splitCh_21, x ≤ 1613 := allLe_sound 1613 splitCh_21 rfl
theorem splitCh_21_ge : ∀ x ∈ splitCh_21, 1543 ≤ x := allGe_sound 1543 splitCh_21 rfl
theorem splitCh_21_rng : ∀ b ∈ splitCh_21, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_21 rfl
theorem splitCh_21_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_21 := allNotMem_sound trapOnlyList splitCh_21 rfl
theorem splitCh_21_cert : ∀ b ∈ splitCh_21, BaseCertified b true := (all_cons cert_1543 (all_cons cert_1545 (all_cons cert_1547 (all_cons cert_1549 (all_cons cert_1551 (all_cons cert_1553 (all_cons cert_1555 (all_cons cert_1557 (all_cons cert_1559 (all_cons cert_1561 (all_cons cert_1563 (all_cons cert_1567 (all_cons cert_1569 (all_cons cert_1571 (all_cons cert_1575 (all_cons cert_1577 (all_cons cert_1579 (all_cons cert_1583 (all_cons cert_1585 (all_cons cert_1587 (all_cons cert_1589 (all_cons cert_1591 (all_cons cert_1593 (all_cons cert_1597 (all_cons cert_1599 (all_cons cert_1601 (all_cons cert_1603 (all_cons cert_1605 (all_cons cert_1607 (all_cons cert_1609 (all_cons cert_1611 (all_cons cert_1613 all_nil))))))))))))))))))))))))))))))))

def splitCh_22 : List Nat := [1615, 1617, 1619, 1621, 1623, 1625, 1627, 1629, 1631, 1633, 1635, 1637, 1639, 1643, 1645, 1647, 1649, 1651, 1653, 1655, 1659, 1661, 1663, 1665, 1667, 1669, 1671, 1673, 1675, 1677, 1679, 1683]
theorem splitCh_22_len : splitCh_22.length = 32 := rfl
theorem splitCh_22_lt : splitCh_22.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_22 rfl
theorem splitCh_22_le : ∀ x ∈ splitCh_22, x ≤ 1683 := allLe_sound 1683 splitCh_22 rfl
theorem splitCh_22_ge : ∀ x ∈ splitCh_22, 1615 ≤ x := allGe_sound 1615 splitCh_22 rfl
theorem splitCh_22_rng : ∀ b ∈ splitCh_22, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_22 rfl
theorem splitCh_22_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_22 := allNotMem_sound trapOnlyList splitCh_22 rfl
theorem splitCh_22_cert : ∀ b ∈ splitCh_22, BaseCertified b true := (all_cons cert_1615 (all_cons cert_1617 (all_cons cert_1619 (all_cons cert_1621 (all_cons cert_1623 (all_cons cert_1625 (all_cons cert_1627 (all_cons cert_1629 (all_cons cert_1631 (all_cons cert_1633 (all_cons cert_1635 (all_cons cert_1637 (all_cons cert_1639 (all_cons cert_1643 (all_cons cert_1645 (all_cons cert_1647 (all_cons cert_1649 (all_cons cert_1651 (all_cons cert_1653 (all_cons cert_1655 (all_cons cert_1659 (all_cons cert_1661 (all_cons cert_1663 (all_cons cert_1665 (all_cons cert_1667 (all_cons cert_1669 (all_cons cert_1671 (all_cons cert_1673 (all_cons cert_1675 (all_cons cert_1677 (all_cons cert_1679 (all_cons cert_1683 all_nil))))))))))))))))))))))))))))))))

def splitCh_23 : List Nat := [1687, 1689, 1691, 1693, 1695, 1697, 1699, 1701, 1705, 1707, 1709, 1711, 1713, 1715, 1717, 1719, 1721, 1723, 1725, 1729, 1731, 1733, 1737, 1739, 1741, 1743, 1745, 1747, 1749, 1751, 1753, 1755]
theorem splitCh_23_len : splitCh_23.length = 32 := rfl
theorem splitCh_23_lt : splitCh_23.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_23 rfl
theorem splitCh_23_le : ∀ x ∈ splitCh_23, x ≤ 1755 := allLe_sound 1755 splitCh_23 rfl
theorem splitCh_23_ge : ∀ x ∈ splitCh_23, 1687 ≤ x := allGe_sound 1687 splitCh_23 rfl
theorem splitCh_23_rng : ∀ b ∈ splitCh_23, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_23 rfl
theorem splitCh_23_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_23 := allNotMem_sound trapOnlyList splitCh_23 rfl
theorem splitCh_23_cert : ∀ b ∈ splitCh_23, BaseCertified b true := (all_cons cert_1687 (all_cons cert_1689 (all_cons cert_1691 (all_cons cert_1693 (all_cons cert_1695 (all_cons cert_1697 (all_cons cert_1699 (all_cons cert_1701 (all_cons cert_1705 (all_cons cert_1707 (all_cons cert_1709 (all_cons cert_1711 (all_cons cert_1713 (all_cons cert_1715 (all_cons cert_1717 (all_cons cert_1719 (all_cons cert_1721 (all_cons cert_1723 (all_cons cert_1725 (all_cons cert_1729 (all_cons cert_1731 (all_cons cert_1733 (all_cons cert_1737 (all_cons cert_1739 (all_cons cert_1741 (all_cons cert_1743 (all_cons cert_1745 (all_cons cert_1747 (all_cons cert_1749 (all_cons cert_1751 (all_cons cert_1753 (all_cons cert_1755 all_nil))))))))))))))))))))))))))))))))

def splitCh_24 : List Nat := [1757, 1759, 1761, 1763, 1765, 1767, 1769, 1771, 1773, 1777, 1779, 1781, 1783, 1785, 1789, 1791, 1793, 1795, 1797, 1799, 1801, 1803, 1805, 1807, 1809, 1811, 1813, 1815, 1817, 1819, 1821, 1825]
theorem splitCh_24_len : splitCh_24.length = 32 := rfl
theorem splitCh_24_lt : splitCh_24.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_24 rfl
theorem splitCh_24_le : ∀ x ∈ splitCh_24, x ≤ 1825 := allLe_sound 1825 splitCh_24 rfl
theorem splitCh_24_ge : ∀ x ∈ splitCh_24, 1757 ≤ x := allGe_sound 1757 splitCh_24 rfl
theorem splitCh_24_rng : ∀ b ∈ splitCh_24, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_24 rfl
theorem splitCh_24_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_24 := allNotMem_sound trapOnlyList splitCh_24 rfl
theorem splitCh_24_cert : ∀ b ∈ splitCh_24, BaseCertified b true := (all_cons cert_1757 (all_cons cert_1759 (all_cons cert_1761 (all_cons cert_1763 (all_cons cert_1765 (all_cons cert_1767 (all_cons cert_1769 (all_cons cert_1771 (all_cons cert_1773 (all_cons cert_1777 (all_cons cert_1779 (all_cons cert_1781 (all_cons cert_1783 (all_cons cert_1785 (all_cons cert_1789 (all_cons cert_1791 (all_cons cert_1793 (all_cons cert_1795 (all_cons cert_1797 (all_cons cert_1799 (all_cons cert_1801 (all_cons cert_1803 (all_cons cert_1805 (all_cons cert_1807 (all_cons cert_1809 (all_cons cert_1811 (all_cons cert_1813 (all_cons cert_1815 (all_cons cert_1817 (all_cons cert_1819 (all_cons cert_1821 (all_cons cert_1825 all_nil))))))))))))))))))))))))))))))))

def splitCh_25 : List Nat := [1827, 1829, 1831, 1835, 1837, 1839, 1841, 1843, 1847, 1849, 1851, 1855, 1857, 1859, 1861, 1863, 1865, 1867, 1869, 1871, 1873, 1875, 1877, 1879, 1881, 1883, 1885, 1887, 1889, 1891, 1893, 1895]
theorem splitCh_25_len : splitCh_25.length = 32 := rfl
theorem splitCh_25_lt : splitCh_25.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_25 rfl
theorem splitCh_25_le : ∀ x ∈ splitCh_25, x ≤ 1895 := allLe_sound 1895 splitCh_25 rfl
theorem splitCh_25_ge : ∀ x ∈ splitCh_25, 1827 ≤ x := allGe_sound 1827 splitCh_25 rfl
theorem splitCh_25_rng : ∀ b ∈ splitCh_25, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_25 rfl
theorem splitCh_25_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_25 := allNotMem_sound trapOnlyList splitCh_25 rfl
theorem splitCh_25_cert : ∀ b ∈ splitCh_25, BaseCertified b true := (all_cons cert_1827 (all_cons cert_1829 (all_cons cert_1831 (all_cons cert_1835 (all_cons cert_1837 (all_cons cert_1839 (all_cons cert_1841 (all_cons cert_1843 (all_cons cert_1847 (all_cons cert_1849 (all_cons cert_1851 (all_cons cert_1855 (all_cons cert_1857 (all_cons cert_1859 (all_cons cert_1861 (all_cons cert_1863 (all_cons cert_1865 (all_cons cert_1867 (all_cons cert_1869 (all_cons cert_1871 (all_cons cert_1873 (all_cons cert_1875 (all_cons cert_1877 (all_cons cert_1879 (all_cons cert_1881 (all_cons cert_1883 (all_cons cert_1885 (all_cons cert_1887 (all_cons cert_1889 (all_cons cert_1891 (all_cons cert_1893 (all_cons cert_1895 all_nil))))))))))))))))))))))))))))))))

def splitCh_26 : List Nat := [1897, 1899, 1901, 1903, 1905, 1907, 1911, 1913, 1915, 1917, 1919, 1921, 1923, 1925, 1927, 1931, 1933, 1935, 1937, 1939, 1941, 1943, 1945, 1947, 1949, 1951, 1953, 1957, 1959, 1961, 1963, 1965]
theorem splitCh_26_len : splitCh_26.length = 32 := rfl
theorem splitCh_26_lt : splitCh_26.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_26 rfl
theorem splitCh_26_le : ∀ x ∈ splitCh_26, x ≤ 1965 := allLe_sound 1965 splitCh_26 rfl
theorem splitCh_26_ge : ∀ x ∈ splitCh_26, 1897 ≤ x := allGe_sound 1897 splitCh_26 rfl
theorem splitCh_26_rng : ∀ b ∈ splitCh_26, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_26 rfl
theorem splitCh_26_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_26 := allNotMem_sound trapOnlyList splitCh_26 rfl
theorem splitCh_26_cert : ∀ b ∈ splitCh_26, BaseCertified b true := (all_cons cert_1897 (all_cons cert_1899 (all_cons cert_1901 (all_cons cert_1903 (all_cons cert_1905 (all_cons cert_1907 (all_cons cert_1911 (all_cons cert_1913 (all_cons cert_1915 (all_cons cert_1917 (all_cons cert_1919 (all_cons cert_1921 (all_cons cert_1923 (all_cons cert_1925 (all_cons cert_1927 (all_cons cert_1931 (all_cons cert_1933 (all_cons cert_1935 (all_cons cert_1937 (all_cons cert_1939 (all_cons cert_1941 (all_cons cert_1943 (all_cons cert_1945 (all_cons cert_1947 (all_cons cert_1949 (all_cons cert_1951 (all_cons cert_1953 (all_cons cert_1957 (all_cons cert_1959 (all_cons cert_1961 (all_cons cert_1963 (all_cons cert_1965 all_nil))))))))))))))))))))))))))))))))

def splitCh_27 : List Nat := [1967, 1969, 1971, 1973, 1977, 1981, 1985, 1987, 1989, 1991, 1993, 1995, 1997, 1999]
theorem splitCh_27_len : splitCh_27.length = 14 := rfl
theorem splitCh_27_lt : splitCh_27.Pairwise (· < ·) := isSortedStrict_pairwise splitCh_27 rfl
theorem splitCh_27_le : ∀ x ∈ splitCh_27, x ≤ 1999 := allLe_sound 1999 splitCh_27 rfl
theorem splitCh_27_ge : ∀ x ∈ splitCh_27, 1967 ≤ x := allGe_sound 1967 splitCh_27 rfl
theorem splitCh_27_rng : ∀ b ∈ splitCh_27, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 := allOddInRange_sound splitCh_27 rfl
theorem splitCh_27_disj : ∀ x ∈ trapOnlyList, x ∉ splitCh_27 := allNotMem_sound trapOnlyList splitCh_27 rfl
theorem splitCh_27_cert : ∀ b ∈ splitCh_27, BaseCertified b true := (all_cons cert_1967 (all_cons cert_1969 (all_cons cert_1971 (all_cons cert_1973 (all_cons cert_1977 (all_cons cert_1981 (all_cons cert_1985 (all_cons cert_1987 (all_cons cert_1989 (all_cons cert_1991 (all_cons cert_1993 (all_cons cert_1995 (all_cons cert_1997 (all_cons cert_1999 all_nil))))))))))))))

def splitList : List Nat := ((((splitCh_00 ++ (splitCh_01 ++ splitCh_02)) ++ ((splitCh_03 ++ splitCh_04) ++ (splitCh_05 ++ splitCh_06))) ++ ((splitCh_07 ++ (splitCh_08 ++ splitCh_09)) ++ ((splitCh_10 ++ splitCh_11) ++ (splitCh_12 ++ splitCh_13)))) ++ (((splitCh_14 ++ (splitCh_15 ++ splitCh_16)) ++ ((splitCh_17 ++ splitCh_18) ++ (splitCh_19 ++ splitCh_20))) ++ ((splitCh_21 ++ (splitCh_22 ++ splitCh_23)) ++ ((splitCh_24 ++ splitCh_25) ++ (splitCh_26 ++ splitCh_27)))))

theorem splitList_length : splitList.length = 878 := by
  unfold splitList
  simp only [List.length_append, splitCh_00_len, splitCh_01_len, splitCh_02_len, splitCh_03_len, splitCh_04_len, splitCh_05_len, splitCh_06_len, splitCh_07_len, splitCh_08_len, splitCh_09_len, splitCh_10_len, splitCh_11_len, splitCh_12_len, splitCh_13_len, splitCh_14_len, splitCh_15_len, splitCh_16_len, splitCh_17_len, splitCh_18_len, splitCh_19_len, splitCh_20_len, splitCh_21_len, splitCh_22_len, splitCh_23_len, splitCh_24_len, splitCh_25_len, splitCh_26_len, splitCh_27_len]

theorem splitList_pairwise_lt : splitList.Pairwise (· < ·) :=
  (pairwise_lt_append (pairwise_lt_append (pairwise_lt_append (pairwise_lt_append splitCh_00_lt (pairwise_lt_append splitCh_01_lt splitCh_02_lt splitCh_01_le splitCh_02_ge (by decide : 171 < 181)) splitCh_00_le (all_append splitCh_01_ge (fun x hx => Nat.le_trans (by decide : 97 ≤ 181) (splitCh_02_ge x hx))) (by decide : 95 < 97)) (pairwise_lt_append (pairwise_lt_append splitCh_03_lt splitCh_04_lt splitCh_03_le splitCh_04_ge (by decide : 341 < 343)) (pairwise_lt_append splitCh_05_lt splitCh_06_lt splitCh_05_le splitCh_06_ge (by decide : 489 < 491)) (all_append (fun x hx => Nat.le_trans (splitCh_03_le x hx) (by decide : 341 ≤ 417)) splitCh_04_le) (all_append splitCh_05_ge (fun x hx => Nat.le_trans (by decide : 419 ≤ 491) (splitCh_06_ge x hx))) (by decide : 417 < 419)) (all_append (fun x hx => Nat.le_trans (splitCh_00_le x hx) (by decide : 95 ≤ 267)) (all_append (fun x hx => Nat.le_trans (splitCh_01_le x hx) (by decide : 171 ≤ 267)) splitCh_02_le)) (all_append (all_append splitCh_03_ge (fun x hx => Nat.le_trans (by decide : 269 ≤ 343) (splitCh_04_ge x hx))) (all_append (fun x hx => Nat.le_trans (by decide : 269 ≤ 419) (splitCh_05_ge x hx)) (fun x hx => Nat.le_trans (by decide : 269 ≤ 491) (splitCh_06_ge x hx)))) (by decide : 267 < 269)) (pairwise_lt_append (pairwise_lt_append splitCh_07_lt (pairwise_lt_append splitCh_08_lt splitCh_09_lt splitCh_08_le splitCh_09_ge (by decide : 705 < 707)) splitCh_07_le (all_append splitCh_08_ge (fun x hx => Nat.le_trans (by decide : 633 ≤ 707) (splitCh_09_ge x hx))) (by decide : 631 < 633)) (pairwise_lt_append (pairwise_lt_append splitCh_10_lt splitCh_11_lt splitCh_10_le splitCh_11_ge (by decide : 851 < 853)) (pairwise_lt_append splitCh_12_lt splitCh_13_lt splitCh_12_le splitCh_13_ge (by decide : 993 < 995)) (all_append (fun x hx => Nat.le_trans (splitCh_10_le x hx) (by decide : 851 ≤ 927)) splitCh_11_le) (all_append splitCh_12_ge (fun x hx => Nat.le_trans (by decide : 929 ≤ 995) (splitCh_13_ge x hx))) (by decide : 927 < 929)) (all_append (fun x hx => Nat.le_trans (splitCh_07_le x hx) (by decide : 631 ≤ 777)) (all_append (fun x hx => Nat.le_trans (splitCh_08_le x hx) (by decide : 705 ≤ 777)) splitCh_09_le)) (all_append (all_append splitCh_10_ge (fun x hx => Nat.le_trans (by decide : 781 ≤ 853) (splitCh_11_ge x hx))) (all_append (fun x hx => Nat.le_trans (by decide : 781 ≤ 929) (splitCh_12_ge x hx)) (fun x hx => Nat.le_trans (by decide : 781 ≤ 995) (splitCh_13_ge x hx)))) (by decide : 777 < 781)) (all_append (all_append (fun x hx => Nat.le_trans (splitCh_00_le x hx) (by decide : 95 ≤ 559)) (all_append (fun x hx => Nat.le_trans (splitCh_01_le x hx) (by decide : 171 ≤ 559)) (fun x hx => Nat.le_trans (splitCh_02_le x hx) (by decide : 267 ≤ 559)))) (all_append (all_append (fun x hx => Nat.le_trans (splitCh_03_le x hx) (by decide : 341 ≤ 559)) (fun x hx => Nat.le_trans (splitCh_04_le x hx) (by decide : 417 ≤ 559))) (all_append (fun x hx => Nat.le_trans (splitCh_05_le x hx) (by decide : 489 ≤ 559)) splitCh_06_le))) (all_append (all_append splitCh_07_ge (all_append (fun x hx => Nat.le_trans (by decide : 561 ≤ 633) (splitCh_08_ge x hx)) (fun x hx => Nat.le_trans (by decide : 561 ≤ 707) (splitCh_09_ge x hx)))) (all_append (all_append (fun x hx => Nat.le_trans (by decide : 561 ≤ 781) (splitCh_10_ge x hx)) (fun x hx => Nat.le_trans (by decide : 561 ≤ 853) (splitCh_11_ge x hx))) (all_append (fun x hx => Nat.le_trans (by decide : 561 ≤ 929) (splitCh_12_ge x hx)) (fun x hx => Nat.le_trans (by decide : 561 ≤ 995) (splitCh_13_ge x hx))))) (by decide : 559 < 561)) (pairwise_lt_append (pairwise_lt_append (pairwise_lt_append splitCh_14_lt (pairwise_lt_append splitCh_15_lt splitCh_16_lt splitCh_15_le splitCh_16_ge (by decide : 1199 < 1201)) splitCh_14_le (all_append splitCh_15_ge (fun x hx => Nat.le_trans (by decide : 1129 ≤ 1201) (splitCh_16_ge x hx))) (by decide : 1127 < 1129)) (pairwise_lt_append (pairwise_lt_append splitCh_17_lt splitCh_18_lt splitCh_17_le splitCh_18_ge (by decide : 1333 < 1339)) (pairwise_lt_append splitCh_19_lt splitCh_20_lt splitCh_19_le splitCh_20_ge (by decide : 1473 < 1475)) (all_append (fun x hx => Nat.le_trans (splitCh_17_le x hx) (by decide : 1333 ≤ 1403)) splitCh_18_le) (all_append splitCh_19_ge (fun x hx => Nat.le_trans (by decide : 1405 ≤ 1475) (splitCh_20_ge x hx))) (by decide : 1403 < 1405)) (all_append (fun x hx => Nat.le_trans (splitCh_14_le x hx) (by decide : 1127 ≤ 1265)) (all_append (fun x hx => Nat.le_trans (splitCh_15_le x hx) (by decide : 1199 ≤ 1265)) splitCh_16_le)) (all_append (all_append splitCh_17_ge (fun x hx => Nat.le_trans (by decide : 1267 ≤ 1339) (splitCh_18_ge x hx))) (all_append (fun x hx => Nat.le_trans (by decide : 1267 ≤ 1405) (splitCh_19_ge x hx)) (fun x hx => Nat.le_trans (by decide : 1267 ≤ 1475) (splitCh_20_ge x hx)))) (by decide : 1265 < 1267)) (pairwise_lt_append (pairwise_lt_append splitCh_21_lt (pairwise_lt_append splitCh_22_lt splitCh_23_lt splitCh_22_le splitCh_23_ge (by decide : 1683 < 1687)) splitCh_21_le (all_append splitCh_22_ge (fun x hx => Nat.le_trans (by decide : 1615 ≤ 1687) (splitCh_23_ge x hx))) (by decide : 1613 < 1615)) (pairwise_lt_append (pairwise_lt_append splitCh_24_lt splitCh_25_lt splitCh_24_le splitCh_25_ge (by decide : 1825 < 1827)) (pairwise_lt_append splitCh_26_lt splitCh_27_lt splitCh_26_le splitCh_27_ge (by decide : 1965 < 1967)) (all_append (fun x hx => Nat.le_trans (splitCh_24_le x hx) (by decide : 1825 ≤ 1895)) splitCh_25_le) (all_append splitCh_26_ge (fun x hx => Nat.le_trans (by decide : 1897 ≤ 1967) (splitCh_27_ge x hx))) (by decide : 1895 < 1897)) (all_append (fun x hx => Nat.le_trans (splitCh_21_le x hx) (by decide : 1613 ≤ 1755)) (all_append (fun x hx => Nat.le_trans (splitCh_22_le x hx) (by decide : 1683 ≤ 1755)) splitCh_23_le)) (all_append (all_append splitCh_24_ge (fun x hx => Nat.le_trans (by decide : 1757 ≤ 1827) (splitCh_25_ge x hx))) (all_append (fun x hx => Nat.le_trans (by decide : 1757 ≤ 1897) (splitCh_26_ge x hx)) (fun x hx => Nat.le_trans (by decide : 1757 ≤ 1967) (splitCh_27_ge x hx)))) (by decide : 1755 < 1757)) (all_append (all_append (fun x hx => Nat.le_trans (splitCh_14_le x hx) (by decide : 1127 ≤ 1541)) (all_append (fun x hx => Nat.le_trans (splitCh_15_le x hx) (by decide : 1199 ≤ 1541)) (fun x hx => Nat.le_trans (splitCh_16_le x hx) (by decide : 1265 ≤ 1541)))) (all_append (all_append (fun x hx => Nat.le_trans (splitCh_17_le x hx) (by decide : 1333 ≤ 1541)) (fun x hx => Nat.le_trans (splitCh_18_le x hx) (by decide : 1403 ≤ 1541))) (all_append (fun x hx => Nat.le_trans (splitCh_19_le x hx) (by decide : 1473 ≤ 1541)) splitCh_20_le))) (all_append (all_append splitCh_21_ge (all_append (fun x hx => Nat.le_trans (by decide : 1543 ≤ 1615) (splitCh_22_ge x hx)) (fun x hx => Nat.le_trans (by decide : 1543 ≤ 1687) (splitCh_23_ge x hx)))) (all_append (all_append (fun x hx => Nat.le_trans (by decide : 1543 ≤ 1757) (splitCh_24_ge x hx)) (fun x hx => Nat.le_trans (by decide : 1543 ≤ 1827) (splitCh_25_ge x hx))) (all_append (fun x hx => Nat.le_trans (by decide : 1543 ≤ 1897) (splitCh_26_ge x hx)) (fun x hx => Nat.le_trans (by decide : 1543 ≤ 1967) (splitCh_27_ge x hx))))) (by decide : 1541 < 1543)) (all_append (all_append (all_append (fun x hx => Nat.le_trans (splitCh_00_le x hx) (by decide : 95 ≤ 1061)) (all_append (fun x hx => Nat.le_trans (splitCh_01_le x hx) (by decide : 171 ≤ 1061)) (fun x hx => Nat.le_trans (splitCh_02_le x hx) (by decide : 267 ≤ 1061)))) (all_append (all_append (fun x hx => Nat.le_trans (splitCh_03_le x hx) (by decide : 341 ≤ 1061)) (fun x hx => Nat.le_trans (splitCh_04_le x hx) (by decide : 417 ≤ 1061))) (all_append (fun x hx => Nat.le_trans (splitCh_05_le x hx) (by decide : 489 ≤ 1061)) (fun x hx => Nat.le_trans (splitCh_06_le x hx) (by decide : 559 ≤ 1061))))) (all_append (all_append (fun x hx => Nat.le_trans (splitCh_07_le x hx) (by decide : 631 ≤ 1061)) (all_append (fun x hx => Nat.le_trans (splitCh_08_le x hx) (by decide : 705 ≤ 1061)) (fun x hx => Nat.le_trans (splitCh_09_le x hx) (by decide : 777 ≤ 1061)))) (all_append (all_append (fun x hx => Nat.le_trans (splitCh_10_le x hx) (by decide : 851 ≤ 1061)) (fun x hx => Nat.le_trans (splitCh_11_le x hx) (by decide : 927 ≤ 1061))) (all_append (fun x hx => Nat.le_trans (splitCh_12_le x hx) (by decide : 993 ≤ 1061)) splitCh_13_le)))) (all_append (all_append (all_append splitCh_14_ge (all_append (fun x hx => Nat.le_trans (by decide : 1063 ≤ 1129) (splitCh_15_ge x hx)) (fun x hx => Nat.le_trans (by decide : 1063 ≤ 1201) (splitCh_16_ge x hx)))) (all_append (all_append (fun x hx => Nat.le_trans (by decide : 1063 ≤ 1267) (splitCh_17_ge x hx)) (fun x hx => Nat.le_trans (by decide : 1063 ≤ 1339) (splitCh_18_ge x hx))) (all_append (fun x hx => Nat.le_trans (by decide : 1063 ≤ 1405) (splitCh_19_ge x hx)) (fun x hx => Nat.le_trans (by decide : 1063 ≤ 1475) (splitCh_20_ge x hx))))) (all_append (all_append (fun x hx => Nat.le_trans (by decide : 1063 ≤ 1543) (splitCh_21_ge x hx)) (all_append (fun x hx => Nat.le_trans (by decide : 1063 ≤ 1615) (splitCh_22_ge x hx)) (fun x hx => Nat.le_trans (by decide : 1063 ≤ 1687) (splitCh_23_ge x hx)))) (all_append (all_append (fun x hx => Nat.le_trans (by decide : 1063 ≤ 1757) (splitCh_24_ge x hx)) (fun x hx => Nat.le_trans (by decide : 1063 ≤ 1827) (splitCh_25_ge x hx))) (all_append (fun x hx => Nat.le_trans (by decide : 1063 ≤ 1897) (splitCh_26_ge x hx)) (fun x hx => Nat.le_trans (by decide : 1063 ≤ 1967) (splitCh_27_ge x hx)))))) (by decide : 1061 < 1063))

theorem splitList_in_range : ∀ b ∈ splitList, 3 ≤ b ∧ b ≤ 1999 ∧ b % 2 = 1 :=
  (all_append (all_append (all_append (all_append splitCh_00_rng (all_append splitCh_01_rng splitCh_02_rng)) (all_append (all_append splitCh_03_rng splitCh_04_rng) (all_append splitCh_05_rng splitCh_06_rng))) (all_append (all_append splitCh_07_rng (all_append splitCh_08_rng splitCh_09_rng)) (all_append (all_append splitCh_10_rng splitCh_11_rng) (all_append splitCh_12_rng splitCh_13_rng)))) (all_append (all_append (all_append splitCh_14_rng (all_append splitCh_15_rng splitCh_16_rng)) (all_append (all_append splitCh_17_rng splitCh_18_rng) (all_append splitCh_19_rng splitCh_20_rng))) (all_append (all_append splitCh_21_rng (all_append splitCh_22_rng splitCh_23_rng)) (all_append (all_append splitCh_24_rng splitCh_25_rng) (all_append splitCh_26_rng splitCh_27_rng)))))

theorem trapOnly_split_disjoint : ∀ x ∈ trapOnlyList, x ∉ splitList :=
  (disj_append (disj_append (disj_append (disj_append splitCh_00_disj (disj_append splitCh_01_disj splitCh_02_disj)) (disj_append (disj_append splitCh_03_disj splitCh_04_disj) (disj_append splitCh_05_disj splitCh_06_disj))) (disj_append (disj_append splitCh_07_disj (disj_append splitCh_08_disj splitCh_09_disj)) (disj_append (disj_append splitCh_10_disj splitCh_11_disj) (disj_append splitCh_12_disj splitCh_13_disj)))) (disj_append (disj_append (disj_append splitCh_14_disj (disj_append splitCh_15_disj splitCh_16_disj)) (disj_append (disj_append splitCh_17_disj splitCh_18_disj) (disj_append splitCh_19_disj splitCh_20_disj))) (disj_append (disj_append splitCh_21_disj (disj_append splitCh_22_disj splitCh_23_disj)) (disj_append (disj_append splitCh_24_disj splitCh_25_disj) (disj_append splitCh_26_disj splitCh_27_disj)))))

theorem split_cert_all : ∀ b ∈ splitList, BaseCertified b true :=
  (all_append (all_append (all_append (all_append splitCh_00_cert (all_append splitCh_01_cert splitCh_02_cert)) (all_append (all_append splitCh_03_cert splitCh_04_cert) (all_append splitCh_05_cert splitCh_06_cert))) (all_append (all_append splitCh_07_cert (all_append splitCh_08_cert splitCh_09_cert)) (all_append (all_append splitCh_10_cert splitCh_11_cert) (all_append splitCh_12_cert splitCh_13_cert)))) (all_append (all_append (all_append splitCh_14_cert (all_append splitCh_15_cert splitCh_16_cert)) (all_append (all_append splitCh_17_cert splitCh_18_cert) (all_append splitCh_19_cert splitCh_20_cert))) (all_append (all_append splitCh_21_cert (all_append splitCh_22_cert splitCh_23_cert)) (all_append (all_append splitCh_24_cert splitCh_25_cert) (all_append splitCh_26_cert splitCh_27_cert)))))

end Ouroboros.OddSurveyCert
