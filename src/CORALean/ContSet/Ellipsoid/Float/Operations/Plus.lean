import CORALean.ContSet.Ellipsoid.Float.Operations.GeneratorError
import CORALean.ContSet.Interval.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Residual

/-!
# `Ellipsoid.plus`

The Minkowski sum of two ellipsoids is not an ellipsoid, so this encloses it and
carries the free parameter every enclosure of it does. Over ℝ that parameter is
Kurzhanski and Varaiya's `l > 0` and the generator matrix is
`[√(1+1/l) G₁ | √(1+l) G₂]`.

Here the parameter is the *two scalings themselves*, `s₁` and `s₂`, and that is
not a workaround for a missing square root and a missing division: it is what
the exact layer already computes with. `l` never appears in `plus_outer` over ℝ
except through those two numbers, and the condition they have to satisfy is
`1/s₁² + 1/s₂² ≤ 1`, which `l`'s pair meets with equality. Taking the pair as
the parameter therefore *widens* the family rather than approximating it — every
sound enclosure of this shape is reachable, and the classical one is the case of
equality.

So the parameter is a real hypothesis the caller discharges, in the shape
`HPolytope.boundOfDual`'s dual feasibility has: an unverified routine proposes
the two scalings and the inequality is what makes them a bound.

Both blocks concatenate as over ℝ and the generator count adds. Only the centre
and the two scalings round, the first into a `residual` and the second into a
`generatorError`, `u` reaching `[-1,1]` in every coordinate.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- Storing the lower of the two directed roundings leaves this much to pay. -/
def Ellipsoid.centerResidual (a b : Vec 𝕋 n) : Interval 𝕋 n :=
  Interval.residual (fun i => addDown (a i) (b i)) (fun i => addUp (a i) (b i))
    (fun i => addDown (a i) (b i))

/-- The two scaled generator blocks side by side, each rounded down. -/
def Ellipsoid.plusG (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n) : Mat 𝕋 n (E₁.k + E₂.k) :=
  fun i => Fin.append (fun j => mulDown s₁ (E₁.G i j)) (fun j => mulDown s₂ (E₂.G i j))

/-- How far each stored generator can be from its exact scaling. -/
def Ellipsoid.plusGap (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n) : Mat 𝕋 n (E₁.k + E₂.k) :=
  fun i => Fin.append
    (fun j => subUp (mulUp s₁ (E₁.G i j)) (mulDown s₁ (E₁.G i j)))
    (fun j => subUp (mulUp s₂ (E₂.G i j)) (mulDown s₂ (E₂.G i j)))

def Ellipsoid.plus (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n) : Ellipsoid 𝕋 n where
  k := E₁.k + E₂.k
  q := fun i => addDown (E₁.q i) (E₂.q i)
  G := Ellipsoid.plusG s₁ s₂ E₁ E₂
  err := (E₁.err.plus E₂.err).plus
    ((Ellipsoid.centerResidual E₁.q E₂.q).plus
      (Ellipsoid.generatorError (Ellipsoid.plusGap s₁ s₂ E₁ E₂)))

end CORALean.Float
