import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.Global.Float.Sqrt

/-!
# `Zonotope.radius`

CORA's `@zonotope/radius`: the smaller of two radii of a ball about the centre, the sum of the
generator lengths and the Euclidean norm of the half-widths of `interval(Z)`. Here both are
radii about the stored centre and both pay for the error box by its largest magnitude `err`
per coordinate: `∑ⱼ ‖Gⱼ‖₂ + ‖err‖₂`, and `‖rowSum |G| + err‖₂`. The second is CORA's
half-width norm when the error box is zero and the centre is the midpoint, as it is for a
box with no error. The roots are `normUp` (`Global/Float/Sqrt`, `k` Newton steps), the sums
`addUp`, so the radius is rounded up.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.radius (k : ℕ) (Z : Zonotope 𝕋 n) : 𝕋 :=
  let err := fun i => maximum (absolute (Z.E.inf i)) (absolute (Z.E.sup i))
  let errLength := normUp k err
  let generatorSum := addUp (sumUp fun j => normUp k fun i => Z.G i j) errLength
  let boxLength := normUp k fun i => addUp (CORALean.Float.radius Z.G i) (err i)
  minimum generatorSum boxLength

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
