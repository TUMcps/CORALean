import CORALean.Global.Float.SinCos
import CORALean.ContSet.Interval.Float.Interval

/-!
# `rotMat`, as an interval matrix

The matrix of CORA's `@zonotope/rotate(Z, dims, angle)` at a float angle: the 2x2 rotation
`[cos -sin; sin cos]` on the coordinates `dims = (i, j)`, the identity elsewhere, with every
`cos`/`sin` entry the interval `cosDown`/`cosUp` (`sinDown`/`sinUp`) of `Global/Float/SinCos`, and
the exact entries `0` and `1` degenerate intervals. `p` is the number of halvings.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Each entry as a pair of bounds, laid out as the real `rotMat`. -/
def rotMat (p n : ℕ) (i j : Fin n) (angle : 𝕋) : Interval (Mat 𝕋 n n) :=
  let c := (cosDown p angle, cosUp p angle)                         -- cos(angle)
  let s := (sinDown p angle, sinUp p angle)                         -- sin(angle)
  let ms := (neg (sinUp p angle), neg (sinDown p angle))            -- -sin(angle)
  let o := ((zero : 𝕋), (zero : 𝕋))
  let e : Fin n → Fin n → 𝕋 × 𝕋 := fun a b =>
    if a = i then (if b = i then c else if b = j then ms else o)
    else if a = j then (if b = i then s else if b = j then c else o)
    else if a = b then (one, one) else o
  ⟨fun a b => (e a b).1, fun a b => (e a b).2⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
