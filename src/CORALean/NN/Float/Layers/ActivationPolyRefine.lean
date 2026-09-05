import CORALean.NN.Float.Layers.ActivationPoly
import CORALean.NN.RefinableLayer

/-!
# The refinable activation layer over a floating-point scalar

The exact refinable layer with `PolyRelaxation` replaced by the float one, and
cheap for the same reason the layer itself is: `sound` states an inequality
against `error`, so a level's coefficients are sound however they were computed
and only `error` pays. A schedule therefore changes nothing about correctness
here either, which is what `Theorems.PropagateAtOuter` says for both layers at
once — `RefinableLayer` is a structure over any `ContSet`, so nothing about the
loop is written twice.

Convergence is deliberately not stated here, and the reason is informative
rather than an omission: the representation's own rounding is charged to an
error box that no refinement level touches, so the propagated set does not
approach the exact image, however much order is spent. The limit is a statement
about ℝ, and the float layer's guarantee is the enclosure it composes with.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ} {n : ℕ}

/-- A float polynomial relaxation per refinement level, the order free to grow
with it. -/
structure PolyRelaxationFamily (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
    (σ : ℝ → ℝ) where
  deg : ℕ → ℕ
  rel : (o : ℕ) → PolyRelaxation 𝕋 σ (deg o)

/-- The activation layer of a float family: one `σ`, one enclosure per level. -/
def Layer.activationPolyRefinable (F : PolyRelaxationFamily 𝕋 σ) :
    Real.RefinableLayer (PolyZonotope 𝕋) n n where
  eval x := fun i => σ (x i)
  propagate o := (Layer.activationPoly (F.rel o)).propagate
  propagate_outer o := (Layer.activationPoly (F.rel o)).propagate_outer

end CORALean.Float
