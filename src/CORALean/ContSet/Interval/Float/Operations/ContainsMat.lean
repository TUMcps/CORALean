module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.containsMat`, over a floating-point scalar

CORA's `contains(intMat, M, 'exact', tol)` as a decision: column by column, every column of the
box nonempty and every entry of `M` below the upper bound and above the lower bound up to `tol`,
or within `tol` of it absolutely or relatively. Each comparison is made in the direction that
makes a `true` certain: sums round the way that tightens the test, the absolute difference is the
larger of the two rounded-up differences, and `ltStrict` and `le` only say `true` when the order
holds.

## Inputs
* `I` – interval matrix
* `M` – matrix
* `tol` – tolerance

## Output
* `true` only if `M` is in `I` up to the tolerance
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `true` only when every column is nonempty and every entry passes both tolerance tests. -/
def Interval.containsMat (I : Interval (Mat 𝕋 m n)) (M : Mat 𝕋 m n) (tol : 𝕋) : Bool :=
  let within : 𝕋 → 𝕋 → Bool := fun a b =>
    let d := maximum (subUp a b) (subUp b a)
    le d tol || le d (mulDown tol (minimum (absolute a) (absolute b)))
  (List.finRange n).all fun j =>
    (List.finRange m).all (fun i => le (I.inf i j) (I.sup i j)) &&
      (List.finRange m).all fun i =>
        (ltStrict (I.inf i j) (addDown (M i j) tol) || within (I.inf i j) (M i j)) &&
          (ltStrict (subUp (M i j) tol) (I.sup i j) || within (I.sup i j) (M i j))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
