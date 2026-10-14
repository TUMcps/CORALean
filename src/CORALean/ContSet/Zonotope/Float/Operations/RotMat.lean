module

public import CORALean.Global.Float.SinCos
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `rotMat`, as an interval matrix

The matrix of CORA's `@zonotope/rotate(Z, dims, angle)` at a float angle: the 2x2 rotation
`[cos -sin; sin cos]` on the coordinates `dims = (i, j)`, the identity elsewhere, with every
`cos`/`sin` entry the interval `cosDown`/`cosUp` (`sinDown`/`sinUp`) of `Global/Float/SinCos`, and
the exact entries `0` and `1` degenerate intervals. `p` is the number of halvings.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Each entry as a pair of bounds, laid out as the real `rotMat`. -/
def rotMat (p n : ℕ) (i j : Fin n) (angle : 𝕋) : Interval (Mat 𝕋 n n) :=
  let c : Interval 𝕋 := ⟨cosDown p angle, cosUp p angle⟩                         -- cos(angle)
  let s : Interval 𝕋 := ⟨sinDown p angle, sinUp p angle⟩                         -- sin(angle)
  let ms : Interval 𝕋 := ⟨neg (sinUp p angle), neg (sinDown p angle)⟩            -- -sin(angle)
  let o : Interval 𝕋 := ⟨(zero : 𝕋), (zero : 𝕋)⟩
  let e : Fin n → Fin n → Interval 𝕋 := fun a b =>
    if a = i then (if b = i then c else if b = j then ms else o)
    else if a = j then (if b = i then s else if b = j then c else o)
    else if a = b then ⟨one, one⟩ else o
  ⟨fun a b => (e a b).inf, fun a b => (e a b).sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
