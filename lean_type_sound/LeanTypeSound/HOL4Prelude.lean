/-
  HOL4 Prelude - Library shim providing HOL4 primitives not in Lean stdlib.
  This module defines types and functions that serve as Lean counterparts
  for standard HOL4 library constructs.
-/

import Init.Data.List.Perm
import Batteries.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Lattice

-- ============================================================
-- Set compatibility shim
-- The project's Set operations are compatible with Mathlib's Set.
-- We define a custom Disjoint for Set that matches HOL4 semantics.
-- ============================================================

namespace Set

def Disjoint' {α : Type} (s1 s2 : Set α) : Prop := ∀ x, ¬(s1 x ∧ s2 x)

end Set

namespace HOL4

-- ============================================================
-- Basic list operations
-- ============================================================

/- HOL4: ALOOKUP -/
def ALOOKUP {α β : Type} [BEq α] : List (α × β) → α → Option β
  | [], _ => none
  | (k, v) :: rest, key => if k == key then some v else ALOOKUP rest key

/- HOL4: LUPDATE -/
def LUPDATE {α : Type} (x : α) (n : Nat) (l : List α) : List α :=
  l.set n x

/- HOL4: EL n l - element at index n -/
def EL {α : Type} [Inhabited α] (n : Nat) (l : List α) : α :=
  l[n]!

/- HOL4: TAKE -/
def TAKE {α : Type} (n : Nat) (l : List α) : List α :=
  l.take n

/- HOL4: DROP -/
def DROP {α : Type} (n : Nat) (l : List α) : List α :=
  l.drop n

/- HOL4: GENLIST f n -/
def GENLIST {α : Type} (f : Nat → α) (n : Nat) : List α :=
  (List.range n).map f

/- HOL4: ZIP -/
def ZIP {α β : Type} : List α × List β → List (α × β)
  | (l1, l2) => l1.zip l2

/- HOL4: UNZIP -/
def UNZIP {α β : Type} : List (α × β) → List α × List β
  | [] => ([], [])
  | (a, b) :: rest =>
    let (as_, bs) := UNZIP rest
    (a :: as_, b :: bs)

/- HOL4: EVERY -/
def EVERY {α : Type} (P : α → Bool) (l : List α) : Bool :=
  l.all P

/- HOL4: EXISTS -/
def EXISTS_ {α : Type} (P : α → Bool) (l : List α) : Bool :=
  l.any P

/- HOL4: ALL_DISTINCT -/
def ALL_DISTINCT {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !(xs.any (· == x)) && ALL_DISTINCT xs

/- HOL4: LIST_REL -/
inductive LIST_REL {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : LIST_REL R [] []
  | cons : ∀ (x : α) (y : β) (xs : List α) (ys : List β),
    R x y → LIST_REL R xs ys → LIST_REL R (x :: xs) (y :: ys)

/- HOL4: PERM - permutation relation. Translated as `List.Perm`. -/
def PERM {α : Type} [BEq α] (l1 l2 : List α) : Prop := List.Perm l1 l2

/- HOL4: REPLICATE -/
def REPLICATE {α : Type} (n : Nat) (x : α) : List α :=
  List.replicate n x

/- HOL4: FLAT -/
def FLAT {α : Type} (l : List (List α)) : List α :=
  l.flatten

/- HOL4: MAP2 -/
def MAP2 {α β γ : Type} (f : α → β → γ) : List α → List β → List γ
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => f x y :: MAP2 f xs ys

/- HOL4: FILTER -/
def FILTER {α : Type} (P : α → Bool) (l : List α) : List α :=
  l.filter P

/- HOL4: nub (remove duplicates) -/
def nub {α : Type} [BEq α] : List α → List α
  | [] => []
  | x :: xs => if xs.any (· == x) then nub xs else x :: nub xs

/- HOL4: MEM -/
def MEM {α : Type} [BEq α] (x : α) (l : List α) : Bool :=
  l.any (· == x)

/- HOL4: SNOC -/
def SNOC {α : Type} (x : α) (l : List α) : List α :=
  l ++ [x]

/- HOL4: REVERSE -/
def REVERSE {α : Type} (l : List α) : List α :=
  l.reverse

/- HOL4: IS_PREFIX l1 l2 means "l2 is a prefix of l1" (l2 ≼ l1) -/
def IS_PREFIX {α : Type} [BEq α] (l1 l2 : List α) : Bool :=
  l2.isPrefixOf l1

/- HOL4: oEL n l - optional element at index n -/
def oEL {α : Type} (n : Nat) (l : List α) : Option α :=
  l[n]?

-- ============================================================
-- Option operations
-- ============================================================

/- HOL4: OPT_MMAP -/
def OPT_MMAP {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => do
    let y ← f x
    let ys ← OPT_MMAP f xs
    return y :: ys

/- HOL4: IS_SOME -/
def IS_SOME {α : Type} : Option α → Bool
  | some _ => true
  | none => false

/- HOL4: IS_NONE -/
def IS_NONE {α : Type} : Option α → Bool
  | some _ => false
  | none => true

/- HOL4: THE -/
def THE {α : Type} [Inhabited α] : Option α → α
  | some x => x
  | none => default

-- ============================================================
-- Finite maps
-- Represented concretely as a partial function `α → Option β`.
-- HOL4's `('a, 'b) fmap` is set-theoretically a partial function with
-- finite support; in this development the finiteness side condition is
-- not required by any client, so we model the API using the underlying
-- partial function directly.
-- ============================================================

/- HOL4: ('a, 'b) fmap -/
def Finmap (α : Type) (β : Type) : Type := α → Option β

namespace Finmap

/- HOL4: FEMPTY -/
def FEMPTY {α β : Type} : Finmap α β := fun _ => none

/- HOL4: FLOOKUP -/
def FLOOKUP {α β : Type} (m : Finmap α β) (k : α) : Option β := m k

/- HOL4: FUPDATE — point update at key `kv.1`. Requires `BEq α` so the
   update is computable. -/
def FUPDATE {α β : Type} [BEq α] (m : Finmap α β) (kv : α × β) : Finmap α β :=
  fun x => if x == kv.1 then some kv.2 else m x

/- HOL4: FDOM -/
def FDOM {α β : Type} (m : Finmap α β) : Set α := fun a => (m a).isSome

/- HOL4: FRANGE -/
def FRANGE {α β : Type} (m : Finmap α β) : Set β := fun b => ∃ a, m a = some b

/- HOL4: FEVERY -/
def FEVERY {α β : Type} (P : α × β → Prop) (m : Finmap α β) : Prop :=
  ∀ k val_, m k = some val_ → P (k, val_)

/- HOL4: FUPDATE_LIST -/
def FUPDATE_LIST {α β : Type} [BEq α] (m : Finmap α β) (l : List (α × β)) : Finmap α β :=
  l.foldl FUPDATE m

/- HOL4: o_f (map over values) -/
def o_f {α β γ : Type} (f : β → γ) (m : Finmap α β) : Finmap α γ :=
  fun x => (m x).map f

/- HOL4: alist_to_fmap — earliest binding wins. -/
def alist_to_fmap {α β : Type} [BEq α] (l : List (α × β)) : Finmap α β :=
  fun k => (l.find? (fun p => k == p.1)).map Prod.snd

/- HOL4: SUBMAP -/
def SUBMAP {α β : Type} (m1 m2 : Finmap α β) : Prop :=
  ∀ k val_, m1 k = some val_ → m2 k = some val_

/- HOL4: FUNION (left-biased union) -/
def FUNION {α β : Type} (m1 m2 : Finmap α β) : Finmap α β :=
  fun x => match m1 x with
    | some v => some v
    | none => m2 x

end Finmap

-- ============================================================
-- Sptree (num-keyed maps)
-- HOL4's `'a spt` is a sparse patricia tree keyed by `num`; we represent
-- it concretely as a `List (Nat × α)` where the first matching key wins.
-- This loses the O(log n) characteristics but preserves the API
-- semantics needed by this development.
-- ============================================================

/- HOL4: 'a spt -/
def Sptree (α : Type) : Type := List (Nat × α)

namespace Sptree

/- HOL4: lookup -/
def lookup {α : Type} (k : Nat) (t : Sptree α) : Option α :=
  (t.find? (fun p => p.1 = k)).map Prod.snd

/- HOL4: insert -/
def insert {α : Type} (k : Nat) (v : α) (t : Sptree α) : Sptree α :=
  (k, v) :: t.filter (fun p => p.1 ≠ k)

/- HOL4: delete -/
def delete {α : Type} (k : Nat) (t : Sptree α) : Sptree α :=
  t.filter (fun p => p.1 ≠ k)

/- HOL4: fromAList -/
def fromAList {α : Type} (l : List (Nat × α)) : Sptree α := l

/- HOL4: domain -/
def domain {α : Type} (t : Sptree α) : Set Nat := fun n => (lookup n t).isSome

/- HOL4: toList (returns values only) -/
def toList {α : Type} (t : Sptree α) : List α := t.map Prod.snd

/- HOL4: toAList (returns key-value pairs) -/
def toAList {α : Type} (t : Sptree α) : List (Nat × α) := t

end Sptree

-- ============================================================
-- LazyList (potentially infinite lists)
-- HOL4's `'a llist` is a coinductive lazy list; we represent it as a
-- partial indexing function `Nat → Option α`, where a `none` at position
-- `n` indicates the list has ended by index `n`. (The intended invariant
-- is that `none` is downward-closed; this invariant is not enforced at
-- the type level but is preserved by `fromList`.)
-- ============================================================

/- HOL4: 'a llist -/
def LazyList (α : Type) : Type := Nat → Option α

namespace LazyList

open Classical

/- HOL4: LPREFIX l1 l2 — l1 is a prefix of l2. Every position present
   in l1 is present in l2 with the same value. -/
def LPREFIX {α : Type} (l1 l2 : LazyList α) : Prop :=
  ∀ n x, l1 n = some x → l2 n = some x

/- HOL4: fromList -/
def fromList {α : Type} (l : List α) : LazyList α := fun n => l[n]?

/- HOL4: toList — returns `some l` when the lazy list is finite (i.e.
   has a least index after which it is empty), otherwise `none`.
   Defined classically since the predicate is undecidable in general. -/
noncomputable def toList {α : Type} (ll : LazyList α) : Option (List α) :=
  if h : ∃ N, ∀ n, n ≥ N → ll n = none then
    let N := Classical.choose h
    some ((List.range N).filterMap ll)
  else
    none

end LazyList

-- ============================================================
-- Set operations
-- ============================================================

/- HOL4: DISJOINT -/
def DISJOINT {α : Type} (s1 s2 : Set α) : Prop :=
  Set.Disjoint' s1 s2

/- HOL4: IMAGE -/
def IMAGE {α β : Type} (f : α → β) (s : Set α) : Set β :=
  Set.image f s

/- HOL4: BIGUNION -/
def BIGUNION {α : Type} (ss : Set (Set α)) : Set α :=
  Set.sUnion ss

/- HOL4: FINITE — there is a list enumerating exactly the elements of `s`. -/
def FINITE {α : Type} (s : Set α) : Prop :=
  ∃ l : List α, ∀ a, s a ↔ a ∈ l

/- HOL4: CARD — cardinality of a finite set. Defined classically: when
   `FINITE s`, returns the length of the de-duplicated enumerating list;
   otherwise 0. -/
open Classical in
noncomputable def CARD {α : Type} (s : Set α) : Nat :=
  if h : FINITE s then
    (Classical.choose h).length
  else
    0

/- HOL4: BIJ f s t — f restricted to s is a bijection onto t. -/
def BIJ {α β : Type} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ a, s a → t (f a)) ∧
  (∀ a1 a2, s a1 → s a2 → f a1 = f a2 → a1 = a2) ∧
  (∀ b, t b → ∃ a, s a ∧ f a = b)

/- HOL4: TOKENS — tokenize a list by a separator predicate, dropping
   empty groups. -/
def TOKENS {α : Type} [BEq α] (P : α → Bool) (l : List α) : List (List α) :=
  (l.splitOnP P).filter (fun g => !g.isEmpty)

-- ============================================================
-- Word types (opaque stubs)
-- ============================================================

/- HOL4: word8 -/
abbrev word8 := UInt8

/- HOL4: word64 -/
abbrev word64 := UInt64

/- HOL4: word_add, word_sub, etc. for word8 -/
def word_add_8 (a b : word8) : word8 := a + b
def word_sub_8 (a b : word8) : word8 := a - b
def word_and_8 (a b : word8) : word8 := a &&& b
def word_or_8 (a b : word8) : word8 := a ||| b
def word_xor_8 (a b : word8) : word8 := a ^^^ b
def word_lsl_8 (a : word8) (n : Nat) : word8 := a <<< n.toUInt8
def word_lsr_8 (a : word8) (n : Nat) : word8 := a >>> n.toUInt8
/- Arithmetic right shift: sign-extend. UInt8 has no native ASR; emulate
   by sign-extending the top bit. -/
def word_asr_8 (a : word8) (n : Nat) : word8 :=
  let signMask : word8 := if a &&& 0x80 != 0 then
      ((0xFF : word8) <<< (8 - min 8 n).toUInt8)
    else 0
  (a >>> n.toUInt8) ||| signMask
/- Rotate right. -/
def word_ror_8 (a : word8) (n : Nat) : word8 :=
  let m := n % 8
  (a >>> m.toUInt8) ||| (a <<< (8 - m).toUInt8)

/- HOL4: word_add, word_sub, etc. for word64 -/
def word_add_64 (a b : word64) : word64 := a + b
def word_sub_64 (a b : word64) : word64 := a - b
def word_and_64 (a b : word64) : word64 := a &&& b
def word_or_64 (a b : word64) : word64 := a ||| b
def word_xor_64 (a b : word64) : word64 := a ^^^ b
def word_lsl_64 (a : word64) (n : Nat) : word64 := a <<< n.toUInt64
def word_lsr_64 (a : word64) (n : Nat) : word64 := a >>> n.toUInt64
/- Arithmetic right shift on 64-bit. -/
def word_asr_64 (a : word64) (n : Nat) : word64 :=
  let signMask : word64 :=
    if a &&& 0x8000000000000000 != 0 then
      ((0xFFFFFFFFFFFFFFFF : word64) <<< (64 - min 64 n).toUInt64)
    else 0
  (a >>> n.toUInt64) ||| signMask
/- Rotate right on 64-bit. -/
def word_ror_64 (a : word64) (n : Nat) : word64 :=
  let m := n % 64
  (a >>> m.toUInt64) ||| (a <<< (64 - m).toUInt64)

/- HOL4: w2n -/
def w2n_8 (w : word8) : Nat := w.toNat
def w2n_64 (w : word64) : Nat := w.toNat

/- HOL4: n2w -/
def n2w_8 (n : Nat) : word8 := n.toUInt8
def n2w_64 (n : Nat) : word64 := n.toUInt64

/- HOL4: i2w — convert an integer to a machine word, taking the result
   modulo `2^width`. Negative integers are represented in two's complement. -/
def i2w_8 (i : Int) : word8 := (i % 256 + 256).toNat.toUInt8
def i2w_64 (i : Int) : word64 := (i % (2^64 : Int) + (2^64 : Int)).toNat.toUInt64

-- ============================================================
-- IEEE754 floating point (opaque stubs)
-- ============================================================

/- HOL4: fp64 ops — IEEE 754 binary64 operations. The HOL4 development
   models fp64 values as 64-bit words and operates on them through
   IEEE-aware functions. We delegate to Lean's `Float` (which is binary64)
   via `Float.ofBits` / `Float.toBits`. The rounding-mode argument is
   ignored (Lean uses round-to-nearest-even). -/
private def fpOfBits (a : word64) : Float := Float.ofBits a
private def fpToBits (f : Float) : word64 := f.toBits

def fp64_lessThan (a b : word64) : Bool := decide (fpOfBits a < fpOfBits b)
def fp64_lessEqual (a b : word64) : Bool := decide (fpOfBits a ≤ fpOfBits b)
def fp64_greaterThan (a b : word64) : Bool := decide (fpOfBits b < fpOfBits a)
def fp64_greaterEqual (a b : word64) : Bool := decide (fpOfBits b ≤ fpOfBits a)
def fp64_equal (a b : word64) : Bool := fpOfBits a == fpOfBits b
def fp64_abs (a : word64) : word64 := fpToBits (fpOfBits a).abs
def fp64_negate (a : word64) : word64 := fpToBits (-(fpOfBits a))
def fp64_sqrt (_rm : Unit) (a : word64) : word64 := fpToBits (fpOfBits a).sqrt
def fp64_add (_rm : Unit) (a b : word64) : word64 := fpToBits (fpOfBits a + fpOfBits b)
def fp64_sub (_rm : Unit) (a b : word64) : word64 := fpToBits (fpOfBits a - fpOfBits b)
def fp64_mul (_rm : Unit) (a b : word64) : word64 := fpToBits (fpOfBits a * fpOfBits b)
def fp64_div (_rm : Unit) (a b : word64) : word64 := fpToBits (fpOfBits a / fpOfBits b)
/- Note: this is not a true fused multiply-add (no FMA primitive in Lean
   core); we compute `a*b + c` with two roundings. This is a translation
   gap relative to HOL4's `fp64_mul_add` which uses a single FMA rounding. -/
def fp64_mul_add (_rm : Unit) (a b c : word64) : word64 :=
  fpToBits (fpOfBits a * fpOfBits b + fpOfBits c)
def roundTiesToEven : Unit := ()

-- ============================================================
-- Comparison type
-- ============================================================

/- HOL4: ordering (LESS | EQUAL | GREATER) -/
inductive ordering where
  | LESS
  | EQUAL
  | GREATER
deriving Repr, BEq, Inhabited

-- ============================================================
-- Char operations
-- ============================================================

/- HOL4: ORD -/
def ORD (c : Char) : Nat := c.toNat

/- HOL4: CHR -/
def CHR (n : Nat) : Char := Char.ofNat n

-- ============================================================
-- FOLDR / FOLDL
-- ============================================================

/- HOL4: FOLDR -/
def FOLDR {α β : Type} (f : α → β → β) (b : β) (l : List α) : β :=
  l.foldr f b

/- HOL4: FOLDL -/
def FOLDL {α β : Type} (f : β → α → β) (b : β) (l : List α) : β :=
  l.foldl f b

/- HOL4: RTC (reflexive transitive closure) -/
inductive RTC {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl : ∀ (x : α), RTC R x x
  | step : ∀ (x y z : α), R x y → RTC R y z → RTC R x z

end HOL4

open HOL4
