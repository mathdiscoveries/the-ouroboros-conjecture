module
@[expose] public section

/-!
# Pure-Kernel Certificate Checker for `thm:odd-survey` (905 Resolved Odd Bases `3 ≤ b ≤ 1,999`)

Uses ONLY Lean `Init` (zero Mathlib, zero `native_decide`, zero `sorry`, zero `set_option`,
zero custom axioms) so that all 32 parallel certificate shards compile quickly and independently.

For each resolved odd base `b ∈ [3, 1999]`:
- `seeds : List (Nat × Nat × Nat)` gives the direct self-returning runaway cylinders `(x, kStart, p)`
  (`[]` for the 27 trap-only bases; nonempty for the 878 split bases).
- `dt : QT` is a depth-4 4-way radix tree packing 16 4-bit tags per `Nat` word for `x ∈ [0, b)`:
  - tag `0`: `TRAP` (odd cylinder `⟨x, 1, 1⟩` hits `0 mod b`),
  - tag `1`: `RUN` (odd cylinder `⟨x, 1, 1⟩` is a direct seed or enters another tag-`1` odd cylinder),
  - tag `d + 2` (`d ≤ 13`): `ZERO y` with BFS distance `d + 1` to `{TRAP, RUN}` along `half(x)` or `y`.

Soundness connecting `checkBaseCert b isSplit seeds dt = true` to exact natural densities
`d(Z_b) = d(R_b) = τ_b` and `d(E_b) = ρ_b` (`τ_b + ρ_b = 1`) is proved in `Ouroboros/OddSurvey.lean`.
-/

namespace Ouroboros.OddSurveyCert

/-- 4-way LSB-first radix tree storing packed 64-bit `Nat` words (16 4-bit tags per leaf). -/
inductive QT where
  | Z : QT
  | L : Nat → QT
  | Q : QT → QT → QT → QT → QT

/-- Pure-kernel depth-`d` lookup in `QT` using only `Nat.beq`. -/
def QT.get : Nat → QT → Nat → Nat
  | _, .Z, _ => 0
  | _, .L v, _ => v
  | 0, .Q _ _ _ _, _ => 0
  | d + 1, .Q t0 t1 t2 t3, i =>
    let r := i % 4
    let q := i / 4
    match Nat.beq r 0 with
    | true => t0.get d q
    | false =>
      match Nat.beq r 1 with
      | true => t1.get d q
      | false =>
        match Nat.beq r 2 with
        | true => t2.get d q
        | false => t3.get d q

/-- Read 4-bit tag in `[0, 15]` for residue `x < 4096` from depth-4 `QT`. -/
def getTag (dt : QT) (x : Nat) : Nat :=
  let w := dt.get 4 (x / 16)
  (w / (16 ^ (x % 16))) % 16

/-- BFS distance to `{TRAP, RUN}` encoded by tag `tg`: `0, 1 ↦ 0`; `d + 2 ↦ d + 1`. -/
def tagDist (tg : Nat) : Nat :=
  match tg with
  | 0 => 0
  | 1 => 0
  | d + 2 => d + 1

/-- Unrolled `2^(v_2(x))` for `1 ≤ x < 2048` (zero recursion, pure `Nat.mod` + `Nat.beq`). -/
def p2v2 (x : Nat) : Nat :=
  match Nat.beq (x % 2) 0 with
  | false => 1
  | true =>
    match Nat.beq (x % 4) 0 with
    | false => 2
    | true =>
      match Nat.beq (x % 8) 0 with
      | false => 4
      | true =>
        match Nat.beq (x % 16) 0 with
        | false => 8
        | true =>
          match Nat.beq (x % 32) 0 with
          | false => 16
          | true =>
            match Nat.beq (x % 64) 0 with
            | false => 32
            | true =>
              match Nat.beq (x % 128) 0 with
              | false => 64
              | true =>
                match Nat.beq (x % 256) 0 with
                | false => 128
                | true =>
                  match Nat.beq (x % 512) 0 with
                  | false => 256
                  | true =>
                    match Nat.beq (x % 1024) 0 with
                    | false => 512
                    | true => 1024

/-- One cylinder step tracking `(x, c, m)` with `m = 2^j`. -/
def cylStepM (b inv2 x c m : Nat) : Nat × Nat × Nat :=
  match Nat.beq (c % 2) 0 with
  | true => ((x * inv2) % b, c / 2, m / 2)
  | false =>
    let m' := m * p2v2 x
    ((x * x + 1) % b, (x * c + 1) % m', m')

/-- Run `n` validated cylinder steps (`1 ≤ x < b` and `2 ≤ m` at every intermediate state);
    returns `(0, 0, 0)` on any invalid intermediate state. -/
def runSeedSteps (b inv2 : Nat) : Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | 0, x, c, m => (x, c, m)
  | fuel + 1, x, c, m =>
    match Nat.beq x 0 with
    | true => (0, 0, 0)
    | false =>
      match Nat.ble m 1 with
      | true => (0, 0, 0)
      | false =>
        match Nat.beq (c % 2) 0 with
        | true => runSeedSteps b inv2 fuel ((x * inv2) % b) (c / 2) (m / 2)
        | false =>
          let m' := m * p2v2 x
          runSeedSteps b inv2 fuel ((x * x + 1) % b) ((x * c + 1) % m') m'

/-- Bounded-recursion chunked wrapper for `runSeedSteps` (supports `n ≤ chunks * 180`). -/
def runSeedChunks (b inv2 : Nat) : Nat → Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | 0, _, x, c, m => (x, c, m)
  | chunks + 1, n, x, c, m =>
    match Nat.ble n 180 with
    | true => runSeedSteps b inv2 n x c m
    | false =>
      match runSeedSteps b inv2 180 x c m with
      | (x1, c1, m1) => runSeedChunks b inv2 chunks (n - 180) x1 c1 m1

/-- Verify one direct runaway seed `(x, kStart, p)` satisfies `lem_odd_runaway` hypotheses. -/
def checkSeed (b inv2 : Nat) (s : Nat × Nat × Nat) : Bool :=
  let (x, kStart, p) := s
  Nat.ble 1 x && Nat.ble (x + 1) b && Nat.ble 1 p &&
  Nat.ble kStart 1440 && Nat.ble p 1440 &&
  match runSeedChunks b inv2 8 kStart x 1 2 with
  | (x1, c1, m1) =>
    Nat.ble 1 x1 && Nat.ble 2 m1 &&
    match runSeedChunks b inv2 8 p x1 c1 m1 with
    | (x2, c2, m2) =>
      Nat.ble 1 x2 && Nat.ble 2 m2 &&
      Nat.beq x2 x1 && Nat.ble m1 m2 && Nat.beq (c2 % m1) (c1 % m1)

/-- Verify every seed in `seeds`. -/
def checkSeeds (b inv2 : Nat) : List (Nat × Nat × Nat) → Bool
  | [] => true
  | s :: rest => checkSeed b inv2 s && checkSeeds b inv2 rest

/-- Membership test `x ∈ seeds.map (·.1)`. -/
def memSeeds (x : Nat) : List (Nat × Nat × Nat) → Bool
  | [] => false
  | (sx, _, _) :: rest =>
    match Nat.beq x sx with
    | true => true
    | false => memSeeds x rest

/-- Pure `TRAP`/`ZERO` tracer chunk (up to `fuel` steps, zero seed lookups):
    returns `(0, x', c', m')` if still running, `(1, 0, 0, 0)` on `TRAP`,
    or `(3 + y, 0, 0, 0)` on `ZERO y`. -/
def tracePureChunk (b inv2 : Nat) : Nat → Nat → Nat → Nat → Nat × Nat × Nat × Nat
  | 0, x, c, m => (0, x, c, m)
  | fuel + 1, x, c, m =>
    match Nat.beq (c % 2) 0 with
    | true =>
      let m' := m / 2
      let x' := (x * inv2) % b
      match Nat.beq m' 1 with
      | true => (3 + x', 0, 0, 0)
      | false => tracePureChunk b inv2 fuel x' (c / 2) m'
    | false =>
      let x' := (x * x + 1) % b
      match Nat.beq x' 0 with
      | true => (1, 0, 0, 0)
      | false =>
        let m' := m * p2v2 x
        tracePureChunk b inv2 fuel x' ((x * c + 1) % m') m'

/-- Bounded-recursion chunked pure tracer (`chunks * 180` max steps; `12 * 180 = 2160 > 1840`). -/
def tracePureLoop (b inv2 : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | k + 1, x, c, m =>
    match tracePureChunk b inv2 180 x c m with
    | (0, x', c', m') => tracePureLoop b inv2 k x' c' m'
    | (res, _, _, _) => res

/-- Runaway-closure tracer chunk: starting after step 1, checks if the stretch hits any
    odd cylinder `⟨y, c, m⟩` (`c % 2 = 1`, `2 ≤ m`) with `getTag dt y = 1`.
    Returns `(2, 0, 0, 0)` on success, `(1, 0, 0, 0)` on failure (`TRAP`/`ZERO`),
    or `(0, x', c', m')` if still running. -/
def traceRunChunk (b inv2 : Nat) (dt : QT) : Nat → Nat → Nat → Nat → Nat × Nat × Nat × Nat
  | 0, x, c, m => (0, x, c, m)
  | fuel + 1, x, c, m =>
    match Nat.beq (c % 2) 0 with
    | true =>
      let m' := m / 2
      match Nat.beq m' 1 with
      | true => (1, 0, 0, 0)
      | false => traceRunChunk b inv2 dt fuel ((x * inv2) % b) (c / 2) m'
    | false =>
      match Nat.beq (getTag dt x) 1 with
      | true => (2, 0, 0, 0)
      | false =>
        let x' := (x * x + 1) % b
        match Nat.beq x' 0 with
        | true => (1, 0, 0, 0)
        | false =>
          let m' := m * p2v2 x
          traceRunChunk b inv2 dt fuel x' ((x * c + 1) % m') m'

/-- Bounded-recursion chunked runaway-closure tracer (`8 * 180 = 1440 > 1153`). -/
def traceRunLoop (b inv2 : Nat) (dt : QT) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => false
  | k + 1, x, c, m =>
    match traceRunChunk b inv2 dt 180 x c m with
    | (2, _, _, _) => true
    | (0, x', c', m') => traceRunLoop b inv2 dt k x' c' m'
    | (_, _, _, _) => false

/-- Check `ZERO y` result and strict BFS distance decrease via `half(x)` or `y`. -/
def checkZeroDist (b inv2 : Nat) (dt : QT) (x dCur : Nat) (res : Nat) : Bool :=
  match res with
  | 0 => false
  | 1 => false
  | 2 => false
  | y + 3 =>
    match Nat.ble (tagDist (getTag dt ((x * inv2) % b)) + 1) dCur with
    | true => true
    | false => Nat.ble (tagDist (getTag dt y) + 1) dCur

/-- Verify residue `x ∈ [1, b)` against its tag in `dt`. -/
def checkRes (b inv2 : Nat) (isSplit : Bool) (seeds : List (Nat × Nat × Nat)) (dt : QT) (x : Nat) : Bool :=
  match getTag dt x with
  | 1 =>
    match isSplit with
    | false => false
    | true =>
      match memSeeds x seeds with
      | true => true
      | false =>
        let x1 := (x * x + 1) % b
        match Nat.beq x1 0 with
        | true => false
        | false =>
          let m1 := 2 * p2v2 x
          traceRunLoop b inv2 dt 8 x1 ((x + 1) % m1) m1
  | 0 =>
    match Nat.beq (x % 2) 1 with
    | true => Nat.beq ((x * x + 1) % b) 0
    | false =>
      let x1 := (x * x + 1) % b
      match Nat.beq x1 0 with
      | true => true
      | false =>
        let m1 := 2 * p2v2 x
        Nat.beq (tracePureLoop b inv2 12 x1 ((x + 1) % m1) m1) 1
  | d + 2 =>
    match Nat.beq (x % 2) 1 with
    | true =>
      let x1 := (x * x + 1) % b
      match Nat.beq x1 0 with
      | true => false
      | false => checkZeroDist b inv2 dt x (d + 1) (3 + ((x1 * inv2) % b))
    | false =>
      let x1 := (x * x + 1) % b
      match Nat.beq x1 0 with
      | true => false
      | false =>
        let m1 := 2 * p2v2 x
        checkZeroDist b inv2 dt x (d + 1) (tracePureLoop b inv2 12 x1 ((x + 1) % m1) m1)

/-- Binary-splitting pure-kernel range checker over `[lo, lo + 2^d) ∩ [1, b)`. -/
def checkRange (b inv2 : Nat) (isSplit : Bool) (seeds : List (Nat × Nat × Nat)) (dt : QT) : Nat → Nat → Bool
  | 0, lo =>
    match Nat.beq lo 0 with
    | true => true
    | false =>
      match Nat.ble b lo with
      | true => true
      | false => checkRes b inv2 isSplit seeds dt lo
  | d + 1, lo =>
    checkRange b inv2 isSplit seeds dt d lo &&
    checkRange b inv2 isSplit seeds dt d (lo + 2 ^ d)

theorem checkRange_succ (b inv2 : Nat) (isSplit : Bool) (seeds : List (Nat × Nat × Nat)) (dt : QT)
    (d lo : Nat)
    (h1 : checkRange b inv2 isSplit seeds dt d lo = true)
    (h2 : checkRange b inv2 isSplit seeds dt d (lo + 2 ^ d) = true) :
    checkRange b inv2 isSplit seeds dt (d + 1) lo = true := by
  simp only [checkRange, h1, h2, Bool.and_self]

theorem checkRange_sound (b inv2 : Nat) (isSplit : Bool) (seeds : List (Nat × Nat × Nat)) (dt : QT)
    (d lo : Nat) (h : checkRange b inv2 isSplit seeds dt d lo = true) :
    ∀ x, lo ≤ x → x < lo + 2 ^ d → 1 ≤ x → x < b → checkRes b inv2 isSplit seeds dt x = true := by
  induction d generalizing lo with
  | zero =>
    intro x hlo hhi hx1 hxb
    have hxeq : x = lo := by omega
    subst hxeq
    simp only [checkRange] at h
    have h0 : Nat.beq x 0 = false := by
      cases hb : Nat.beq x 0 with
      | false => rfl
      | true => have := Nat.eq_of_beq_eq_true hb; omega
    have hble : Nat.ble b x = false := by
      cases hb : Nat.ble b x with
      | false => rfl
      | true => have := Nat.ble_eq.mp hb; omega
    rw [h0, hble] at h
    exact h
  | succ d ih =>
    simp only [checkRange, Bool.and_eq_true] at h
    intro x hlo hhi hx1 hxb
    by_cases hmid : x < lo + 2 ^ d
    · exact ih lo h.1 x hlo hmid hx1 hxb
    · have h2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by
        rw [Nat.pow_succ, Nat.mul_two]
      exact ih (lo + 2 ^ d) h.2 x (by omega) (by omega) hx1 hxb

/-- Complete pure-kernel certificate predicate for one odd base `b ∈ [3, 1999]`. -/
def checkBaseCert (b : Nat) (isSplit : Bool) (seeds : List (Nat × Nat × Nat)) (dt : QT) : Bool :=
  Nat.ble 3 b && Nat.ble b 1999 && Nat.beq (b % 2) 1 &&
  (match isSplit, seeds with
   | false, [] => true
   | true, _ :: _ => true
   | _, _ => false) &&
  checkSeeds b ((b + 1) / 2) seeds &&
  checkRange b ((b + 1) / 2) isSplit seeds dt 11 0

/-- Header-only certificate predicate (used to combine split `checkRange` sub-range proofs cleanly). -/
def checkBaseHeader (b : Nat) (isSplit : Bool) (seeds : List (Nat × Nat × Nat)) : Bool :=
  Nat.ble 3 b && Nat.ble b 1999 && Nat.beq (b % 2) 1 &&
  (match isSplit, seeds with
   | false, [] => true
   | true, _ :: _ => true
   | _, _ => false) &&
  checkSeeds b ((b + 1) / 2) seeds

theorem checkBaseCert_mk (b : Nat) (isSplit : Bool) (seeds : List (Nat × Nat × Nat)) (dt : QT)
    (hHdr : checkBaseHeader b isSplit seeds = true)
    (hRng : checkRange b ((b + 1) / 2) isSplit seeds dt 11 0 = true) :
    checkBaseCert b isSplit seeds dt = true := by
  unfold checkBaseCert
  unfold checkBaseHeader at hHdr
  rw [hHdr, hRng]
  rfl

/-- Certificate existence predicate exported by shards (`Init`-only). -/
def BaseCertified (b : Nat) (isSplit : Bool) : Prop :=
  ∃ seeds dt, checkBaseCert b isSplit seeds dt = true

theorem baseCertified_of_cert (b : Nat) (isSplit : Bool) (seeds : List (Nat × Nat × Nat)) (dt : QT)
    (h : checkBaseCert b isSplit seeds dt = true) :
    BaseCertified b isSplit :=
  ⟨seeds, dt, h⟩

end Ouroboros.OddSurveyCert
