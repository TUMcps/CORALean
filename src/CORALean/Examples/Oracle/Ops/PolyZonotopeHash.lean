import CORALean.Global.Sort

/-!
# CORA's order of the merged exponent columns

`removeRedundantExponents` of CORA hashes every exponent column with a fixed random vector,
`hashVec = rs.rand(1, p)` of `RandStream('mt19937ar', 'Seed', 0)` (MATLAB's `init_genrand(5489)`
and `genrand_res53`), sorts the columns stably by the hash and puts first those whose hash is not
shared with a neighbour, then the runs of equal columns. Only the order of the columns is taken
from here: which columns are equal is decided on the exponents, and every order is a sound one
(`PolyZonotope.compactGens` merges, a permutation of the columns moves no point).

## Inputs
* `extra` – columns that CORA has twice and the caller once (`enclose`'s new factor alone)
* `p` – the number of identifiers
* `cols` – the exponent columns

## Output
* the columns of the merged set in CORA's order, each by the index of its first column
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Oracle


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The 624 words of `init_genrand(seed)`. -/
private def aux_mtInit (seed : UInt32) : Array UInt32 := Id.run do
  let mut mt : Array UInt32 := Array.replicate 624 0
  mt := mt.set! 0 seed
  for i in [1:624] do
    let prev := mt[i - 1]!
    mt := mt.set! i ((1812433253 : UInt32) * (prev ^^^ (prev >>> 30)) + i.toUInt32)
  return mt

/-- The twisted state, all 624 words at once. -/
private def aux_mtTwist (mt : Array UInt32) : Array UInt32 := Id.run do
  let mut mt := mt
  for k in [0:624] do
    let y := (mt[k]! &&& 0x80000000) ||| (mt[(k + 1) % 624]! &&& 0x7fffffff)
    let v := mt[(k + 397) % 624]! ^^^ (y >>> 1) ^^^ (if y &&& 1 == 1 then 0x9908b0df else 0)
    mt := mt.set! k v
  return mt

/-- `genrand_int32`, tempered, the `k`-th word of the stream. -/
private def aux_mtWords (count : Nat) : Array UInt32 := Id.run do
  let mut out : Array UInt32 := #[]
  let mut mt := aux_mtInit 5489
  let mut idx := 624
  for _ in [0:count] do
    if idx ≥ 624 then
      mt := aux_mtTwist mt
      idx := 0
    let mut y := mt[idx]!
    idx := idx + 1
    y := y ^^^ (y >>> 11)
    y := y ^^^ ((y <<< 7) &&& 0x9d2c5680)
    y := y ^^^ ((y <<< 15) &&& 0xefc60000)
    y := y ^^^ (y >>> 18)
    out := out.push y
  return out

/-- `genrand_res53`: the first `p` doubles of the stream, two words each. -/
private def aux_hashVec (p : Nat) : Array Float :=
  let w := aux_mtWords (2 * p)
  Array.ofFn fun k : Fin p =>
    let a := (w[2 * k.val]! >>> 5).toNat.toFloat
    let b := (w[2 * k.val + 1]! >>> 6).toNat.toFloat
    (a * 67108864.0 + b) / 9007199254740992.0

/-- The hash of an exponent column, the products summed in the order of the identifiers. -/
private def aux_hash (hv : Array Float) (col : Array Nat) : Float := Id.run do
  let mut acc : Float := 0
  for k in [0:col.size] do
    let t := hv[k]! * col[k]!.toFloat
    acc := if k == 0 then t else acc + t
  return acc


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The index of the first column of every group of equal exponent columns, in CORA's order: the
groups of one column by their hash, then the groups of several by theirs. -/
def hashedColumnOrder (extra : Array (Array Nat)) (p : Nat) (cols : Array (Array Nat)) :
    Array Nat := Id.run do
  let hv := aux_hashVec p
  let hashes := cols.map (aux_hash hv)
  -- the first column of each group, and the size of the group
  let mut firsts : Array Nat := #[]
  let mut sizes : Array Nat := #[]
  for l in [0:cols.size] do
    match firsts.findIdx? fun f => cols[f]! == cols[l]! with
    | some g => sizes := sizes.modify g (· + 1)
    | none =>
      firsts := firsts.push l
      sizes := sizes.push 1
  -- the columns CORA merges before the order is taken but this pipeline carries once
  for e in extra do
    match firsts.findIdx? fun f => cols[f]! == e with
    | some g => sizes := sizes.modify g (· + 1)
    | none => pure ()
  -- no two columns equal: CORA returns the columns as they are
  if firsts.size == cols.size && extra.isEmpty then return firsts
  -- singles first, each class by its hash (a stable sort)
  let keyed := (Array.range firsts.size).map fun g =>
    (g, decide (sizes[g]! > 1), hashes[firsts[g]!]!)
  let sorted := keyed.toList.mergeSort fun a b =>
    if a.2.1 != b.2.1 then !a.2.1 else decide (a.2.2 ≤ b.2.2)
  return (sorted.map fun t => firsts[t.1]!).toArray

end CORALean.Oracle


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
