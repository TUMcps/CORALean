module

public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `Interval.exactSquare`, over a floating-point scalar

CORA's `exactSquare` of an interval matrix, rounded outward: the range of `M * M` entry by entry.
Off the diagonal it is `A i j` times the sum `A i i + A j j` plus the products over `k` other than
`i` and `j`; on the diagonal the square of `A i i` plus the products over `k` other than `i`.
Every product is the corner hull `mulLo`/`mulHi`, the sums are `sumDown`/`sumUp`, and the lower
end of the square is `0` unless the interval is certified to be on one side of `0`.

## Inputs
* `A` – interval matrix

## Output
* interval matrix enclosing the squares of its members, rounded outward
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The least square over `[a, b]`: the smaller end square if the interval is certified to lie on
one side of `0`, else `0`. -/
@[step_of Interval.exactSquare]
def Interval.step_squareLo (a b : 𝕋) : 𝕋 :=
  if le zero a || le b zero then minimum (mulDown a a) (mulDown b b) else zero

/-- The greatest square over `[a, b]`, the larger end square rounded up. -/
@[step_of Interval.exactSquare]
def Interval.step_squareHi (a b : 𝕋) : 𝕋 := maximum (mulUp a a) (mulUp b b)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The entrywise range of `M * M` over the box. -/
def Interval.exactSquare (A : Interval (Mat 𝕋 n n)) : Interval (Mat 𝕋 n n) where
  -- the lower ends: squares and products rounded down
  inf := fun i j =>
    if i = j then
      addDown (Interval.step_squareLo (A.inf i i) (A.sup i i))
        (sumDown fun k => if k = i then zero
          else Interval.mulLo (A.inf i k) (A.sup i k) (A.inf k i) (A.sup k i))
    else
      addDown (Interval.mulLo (A.inf i j) (A.sup i j) (addDown (A.inf i i) (A.inf j j))
          (addUp (A.sup i i) (A.sup j j)))
        (sumDown fun k => if k = i ∨ k = j then zero
          else Interval.mulLo (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j))
  -- the upper ends: squares and products rounded up
  sup := fun i j =>
    if i = j then
      addUp (Interval.step_squareHi (A.inf i i) (A.sup i i))
        (sumUp fun k => if k = i then zero
          else Interval.mulHi (A.inf i k) (A.sup i k) (A.inf k i) (A.sup k i))
    else
      addUp (Interval.mulHi (A.inf i j) (A.sup i j) (addDown (A.inf i i) (A.inf j j))
          (addUp (A.sup i i) (A.sup j j)))
        (sumUp fun k => if k = i ∨ k = j then zero
          else Interval.mulHi (A.inf i k) (A.sup i k) (A.inf k j) (A.sup k j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
