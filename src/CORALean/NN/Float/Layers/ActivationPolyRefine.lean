import CORALean.NN.Float.Layers.PolyRelaxationPad
import CORALean.NN.RefinableLayer

/-!
# The refinable activation layer over a floating-point scalar

The exact refinable layer with `PolyRelaxation` replaced by the float one, and
cheap for the same reason the layer itself is: `sound` states an inequality
against `error`, so a level's coefficients are sound however they were computed
and only `error` pays. A schedule therefore changes nothing about correctness
here either, which is what `Theorems.EncloseAtOuter` says for both layers at
once — `RefinableLayer` is a structure over any `ContSet`, so nothing about the
loop is written twice, the order pattern [1, Eq. 23] included.

`atPattern` reads one level per neuron out of that pattern and pads the neurons'
fits to a common degree, which `PolyRelaxationPad` does exactly.

Convergence is deliberately not stated here, and the reason is informative
rather than an omission: the representation's own rounding is charged to an
error box that no refinement level touches, so the enclosed set does not
approach the exact image, however much order is spent. The limit is a statement
about ℝ, and the float layer's guarantee is the enclosure it composes with.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ} {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A float polynomial relaxation per refinement level, the order free to grow
with it. -/
structure PolyRelaxationFamily (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]
    (σ : ℝ → ℝ) where
  deg : ℕ → ℕ
  rel : (o : ℕ) → PolyRelaxation 𝕋 σ (deg o)

/-- The degree a whole layer is read at: the largest any of its neurons asks
for, which padding lifts the others to. -/
def PolyRelaxationFamily.degOf (F : PolyRelaxationFamily 𝕋 σ) (t : Real.OrderPattern n) : ℕ :=
  Finset.univ.sup fun i => F.deg (t i)

/-- Every neuron's own degree is under the layer's, which is what padding needs
and what makes the common degree no restriction. -/
theorem PolyRelaxationFamily.deg_le_degOf (F : PolyRelaxationFamily 𝕋 σ)
    (t : Real.OrderPattern n) (i : Fin n) : F.deg (t i) ≤ F.degOf t :=
  Finset.le_sup (f := fun j => F.deg (t j)) (Finset.mem_univ i)

/-- The layer's abstraction at an order pattern: each neuron's own fit at its
own level, padded to the common degree. -/
def PolyRelaxationFamily.atPattern (F : PolyRelaxationFamily 𝕋 σ) (t : Real.OrderPattern n) :
    LayerRelaxation 𝕋 σ n (F.degOf t) :=
  fun i => (F.rel (t i)).padTo (F.degOf t) (F.deg_le_degOf t i)

/-- The activation layer of a float family: one `σ`, one enclosure per pattern. -/
def Layer.activationPolyRefinable (F : PolyRelaxationFamily 𝕋 σ) :
    Real.RefinableLayer (PolyZonotope 𝕋) n n where
  eval x := fun i => σ (x i)
  enclose t := (Layer.activationPoly (F.atPattern t)).enclose
  enclose_outer t := (Layer.activationPoly_sound (F.atPattern t)).enclose_outer

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
