module

public import CORALean.ContSet.HPolytope.Float.Operations.SetRhs
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `HPolytope.rescaleCols`: the rows read at `ξm + diag(ξr) δ`, for `δ` in the unit box

The substitution [1, Prop. 4] makes in a constrained zonotope's coefficients: a row `a` read at
`ξ = ξm + diag(ξr) δ` is the row `a diag(ξr)` read at `δ` plus the constant `a ξm`, so the rows
become `A diag(ξr)` and `Ae diag(ξr)` and the bounds `b - A ξm` and `be - Ae ξm`. Each entry of a
scaled row is rounded down, which names a slightly different halfspace; against `δ` in the unit
box it is off by at most the row's summed gaps (`abs_sum_mulDown_gap_le`). So `setRhs` stores the
lower end of a row's new bound and pays the width into the row's slack (#218): an equality stays
an equality. The slacks are carried, the error box is not read (a constrained zonotope's
constraint has none).

## Inputs
* `P` – H-polytope
* `ξm` – vector of length `n`
* `ξr` – vector of length `n`

## Output
* the rows at `ξm + diag(ξr) δ`, rounding against the unit box paid into the slacks

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes: A new
      tool for set-based estimation and fault detection". Automatica, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows at `ξm + diag(ξr) δ`: `A diag(ξr)` rounded down, the bounds `b - A ξm`, the rounding
of both against the unit box in the slacks. -/
def HPolytope.rescaleCols (P : HPolytope 𝕋 (Vec 𝕋 n)) (ξm ξr : Vec 𝕋 n) : HPolytope 𝕋 (Vec 𝕋 n) :=
  -- how far a row `a diag(ξr)`, rounded down, may be off against the unit box
  let gap : Vec 𝕋 n → 𝕋 := fun a =>
    sumUp fun j => subUp (mulUp (a j) (ξr j)) (mulDown (a j) (ξr j))
  -- the scaled rows, the slacks kept for `setRhs` to widen
  let Q : HPolytope 𝕋 (Vec 𝕋 n) :=
    { P with A := fun k j => mulDown (P.A k j) (ξr j), Ae := fun k j => mulDown (P.Ae k j) (ξr j),
             I_error := Interval.origin n }
  -- `b - A ξm` between its two roundings, and the gap either way
  Q.setRhs (fun k => subDown (subDown (P.b k) (dotUp (P.A k) ξm)) (gap (P.A k)))
    (fun k => addUp (subUp (P.b k) (dotDown (P.A k) ξm)) (gap (P.A k)))
    (fun k => subDown (subDown (P.be k) (dotUp (P.Ae k) ξm)) (gap (P.Ae k)))
    (fun k => addUp (subUp (P.be k) (dotDown (P.Ae k) ξm)) (gap (P.Ae k)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
