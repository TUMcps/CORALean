module

public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.ConZonotope.Float.Instances
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Theorems.MemPoint
public import CORALean.HybridDynamics.Definitions.Transition
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeConZonotopeContains

@[expose] public section

/-!
# The jump step at a float constrained zonotope, with nothing assumed

`JumpOuterConZonotope` over a floating-point scalar: the state set and the guard
are float constrained zonotopes, the guard cut is computed by the float
`ConZonotope.intersection`, and the reset `x ↦ W x + w` is `mtimes` for the matrix
and `plus` of the zero-width box at `w`, as `Transition.jumpFloat` does it for a
zonotope. `w` is stored floats, so that box is a float box and
`Interval.conZonotope` turns it into a constrained zonotope.

Where the exact theorem is lossless at the cut, this one is outer: the float
intersection widens its agreement rows by the rounding of `c₂ - c₁` and by the
two error boxes.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float ContSet Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {L : Type} {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The guard intersection computed rather than assumed, in floats. -/
theorem Transition.jumpFloat_outer_conZonotope
    (e : Transition (fun k => ConZonotope 𝕋 (Vec 𝕋 k)) L 𝕋 n)
    {R : ConZonotope 𝕋 (Vec 𝕋 n)} {z : Vec ℝ n} (hz : z ∈ construct R)
    (hguard : z ∈ construct e.guard) : -- --- STMT ---
    e.reset z ∈ construct (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => ConZonotope 𝕋 (Vec 𝕋 k)) e.W
    (R.intersection e.guard)
      ⊞ (Interval.point e.w).conZonotope) := by -- --- PROOF ---
  show Scalar.toRealMat e.W *ᵥ z + Scalar.toRealVec e.w ∈ _
  exact Plus.plus_outer _ _ (Set.add_mem_add
    (Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (S := fun k => ConZonotope 𝕋 (Vec 𝕋 k)) e.W
      (R.intersection e.guard)
      (Set.mem_biUnion rfl (Set.mem_image_of_mem _
        (ConZonotope.intersection_outer R e.guard ⟨hz, hguard⟩))))
    (Interval.conZonotope_contains _ (Interval.mem_point e.w)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
