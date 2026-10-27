module

public import CORALean.Global.Float.FloatOps
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Zonotope.basisInverse`

A candidate inverse of a square matrix, by Gauss-Jordan elimination without pivoting,
in the scalar's own arithmetic. It is not trusted: nothing about it is ever assumed, and what
makes it usable is the check `methCQ` runs on `H P`, which an elimination that met a zero
pivot, or rounded badly, simply fails. The rows are stored between steps, as the elimination would
otherwise be a closure nested once per step.

## Inputs
* `P` – basis matrix

## Output
* inverse reached by elimination
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- One elimination step: row `k` scaled to a unit pivot, and cleared from every other row. -/
@[step_of Zonotope.basisInverse]
def Zonotope.step_basisStep (k : Fin n) (A B : Vector (Vector 𝕋 n) n) :
    Vector (Vector 𝕋 n) n × Vector (Vector 𝕋 n) n :=
  let p := (A[k.val]'k.isLt)[k.val]'k.isLt
  let rowA : Fin n → 𝕋 := fun j => divDown ((A[k.val]'k.isLt)[j.val]'j.isLt) p
  let rowB : Fin n → 𝕋 := fun j => divDown ((B[k.val]'k.isLt)[j.val]'j.isLt) p
  let f : Fin n → 𝕋 := fun i => (A[i.val]'i.isLt)[k.val]'k.isLt
  (Vector.ofFn fun i => Vector.ofFn fun j =>
      if i = k then rowA j else subDown ((A[i.val]'i.isLt)[j.val]'j.isLt) (mulUp (f i) (rowA j)),
    Vector.ofFn fun i => Vector.ofFn fun j =>
      if i = k then rowB j else subDown ((B[i.val]'i.isLt)[j.val]'j.isLt) (mulUp (f i) (rowB j)))


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The inverse the elimination arrives at, or whatever it arrives at where it breaks down. -/
def Zonotope.basisInverse (P : Mat 𝕋 n n) : Mat 𝕋 n n :=
  let A₀ : Vector (Vector 𝕋 n) n := Vector.ofFn fun i => Vector.ofFn fun j => P i j
  let B₀ : Vector (Vector 𝕋 n) n :=
    Vector.ofFn fun i => Vector.ofFn fun j => if i = j then one else zero
  let B := ((List.finRange n).foldl (fun s k => Zonotope.step_basisStep k s.1 s.2) (A₀, B₀)).2
  fun i j => (B[i.val]'i.isLt)[j.val]'j.isLt

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
