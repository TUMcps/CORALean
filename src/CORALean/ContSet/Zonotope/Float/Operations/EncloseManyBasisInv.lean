import CORALean.ContSet.Interval.Float.Operations.Mrdivide
import CORALean.ContSet.Zonotope.Float.Operations.EncloseManyBasis

/-!
# `Zonotope.encloseManyBasisInv`, over a floating-point scalar

An interval matrix holding `rotMatrix⁻¹`, in closed form. With `d` the dropped axis,
`R = [newGen | e_i, i ≠ d]` solves `R x = y` by `x₀ = y_d / g_d` and
`x_{j+1} = y_{i_j} - g_{i_j} y_d / g_d` (`i_j` the `j`-th axis but `d`), so the inverse has
`1` at `(j+1, i_j)`, the column `d` equal to `(1, -g_{i_j})_j / g_d`, and `0` elsewhere. The
quotients are the only inexact entries, rounded outward by `Interval.mrdivide`; the divisor
`g_d` must be provably nonzero, which `encloseMany` checks. This replaces the exact `R⁻¹` of the
exact layer by a box that holds it, so a product with it over-approximates the exact image.

Source: [1].

## References

* [1] `contSet/@zonotope/encloseMany.m`, CORA (Sep. 2025). No paper behind the
      rule was confirmed.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A box of matrices containing the inverse of `encloseManyBasis newGen`. -/
def Zonotope.encloseManyBasisInv (newGen : Vec 𝕋 (m + 1)) : Interval (Mat 𝕋 (m + 1) (m + 1)) :=
  let dropped := Zonotope.encloseManyDropped newGen
  let w : Vec 𝕋 (m + 1) := Fin.cons one fun j => neg (newGen (dropped.succAbove j))
  let col := Interval.mrdivide ⟨w, w⟩ (newGen dropped)               -- column `dropped`: w / g_d
  let axes : Mat 𝕋 (m + 1) (m + 1) := fun r k =>                     -- the exact unit entries
    Fin.cases zero (fun j => if k = dropped.succAbove j then one else zero) r
  { inf := fun r k => if k = dropped then col.inf r else axes r k
    sup := fun r k => if k = dropped then col.sup r else axes r k }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
