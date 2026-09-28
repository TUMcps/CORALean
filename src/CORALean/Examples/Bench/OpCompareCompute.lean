import CORALean.Global.Float.FloatOps
import CORALean.Global.Float.Instances.Binary64.API
import CORALean.Global.Float.Instances.IEEE.API

/-!
# `opcompare`: the sequential sum, dot product and matrix product

Every quantity is computed strictly left to right, one rounding per operation, matching
`experiments/matlab-ops/compare.py`'s own `seqsum`/`seqdot` exactly: the accumulator starts at
`zero`, and a dot product's product and sum are two separate rounded steps, never a fused
multiply-add. `seqSumFO`/`seqDotFO` are generic in `FloatOps`, so the very same code computes
`hardware_down`/`hardware_up` at `Float` and `ieee_down`/`ieee_up` at `IEEE .binary64`;
`seqSumNearest`/`seqDotNearest` are `hardware_nearest`'s own native round-to-nearest.

`mtimes500` is 1.25e8 multiply-adds per bound at `IEEE`'s big-integer arithmetic, so
`aux_parMatrix` spreads the `n` rows over `numChunks` `Task`s, each computing a contiguous
row range -- pure, since every entry is a function of `A`/`B` alone.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench

open CORALean.Float FloatOps


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `f i j` for every `(i, j)` in `n × n`, row-major, split into `numChunks` contiguous row
ranges and computed by one `Task` each -- `Task.get`, in chunk order, is what makes the result
row-major again. -/
def aux_parMatrix {α : Type} (numChunks n : Nat) (f : Nat → Nat → α) : Array α :=
  let chunkLen := (n + numChunks - 1) / max numChunks 1
  let ranges := (List.range numChunks).map fun c => (c * chunkLen, min n (c * chunkLen + chunkLen))
  let tasks := (ranges.filter fun (lo, hi) => lo < hi).map fun (lo, hi) =>
    Task.spawn fun _ => Id.run do
      let mut out := Array.mkEmpty ((hi - lo) * n)
      for i in [lo:hi] do
        for j in [0:n] do
          out := out.push (f i j)
      pure out
  (tasks.map Task.get).foldl (· ++ ·) #[]


-- =====================================  MAIN DEFINITION  ====================================== --

variable {𝕋 : Type} [FloatOps 𝕋]

/-- The sequential sum of `xs`, rounded down or up throughout: `compare.py`'s `seqsum`,
accumulator `zero` and all, at whichever direction `down` picks. -/
def seqSumFO (down : Bool) (xs : Array 𝕋) : 𝕋 :=
  xs.foldl (if down then addDown else addUp) zero

/-- The sequential dot product of `xs` and `ys`: `compare.py`'s `seqdot` -- one rounded multiply
then one rounded add per term, left to right, both in the direction `down` picks. -/
def seqDotFO (down : Bool) (xs ys : Array 𝕋) : 𝕋 :=
  let mul := if down then mulDown else mulUp
  let add := if down then addDown else addUp
  Id.run do
    let mut s : 𝕋 := zero
    for i in [0:xs.size] do
      s := add s (mul (xs.getD i zero) (ys.getD i zero))
    pure s

/-- `seqSumFO`'s own accumulator, native round-to-nearest: `hardware_nearest`. -/
def seqSumNearest (xs : Array Float) : Float := xs.foldl (· + ·) 0.0

/-- `seqDotFO`'s own multiply-then-add, native round-to-nearest. -/
def seqDotNearest (xs ys : Array Float) : Float := Id.run do
  let mut s : Float := 0.0
  for i in [0:xs.size] do
    s := s + xs[i]! * ys[i]!
  pure s

/-- `A * B`, `n × n`, row-major: entry `(i, j)` is `seqDotFO` of row `i` of `A` and column `j`
of `B`, over `numChunks` `Task`s. -/
def matMulFO (numChunks : Nat) (down : Bool) (n : Nat) (A B : Array 𝕋) : Array 𝕋 :=
  let rows := Array.ofFn fun i : Fin n => A.extract (i.val * n) (i.val * n + n)
  let cols := Array.ofFn fun j : Fin n =>
    Array.ofFn fun i : Fin n => B.getD (i.val * n + j.val) zero
  aux_parMatrix numChunks n fun i j => seqDotFO down (rows.getD i #[]) (cols.getD j #[])

/-- `matMulFO`'s own entry, native round-to-nearest. -/
def matMulNearest (numChunks n : Nat) (A B : Array Float) : Array Float :=
  let rows := Array.ofFn fun i : Fin n => A.extract (i.val * n) (i.val * n + n)
  let cols := Array.ofFn fun j : Fin n => Array.ofFn fun i : Fin n => B[i.val * n + j.val]!
  aux_parMatrix numChunks n fun i j => seqDotNearest rows[i]! cols[j]!

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
