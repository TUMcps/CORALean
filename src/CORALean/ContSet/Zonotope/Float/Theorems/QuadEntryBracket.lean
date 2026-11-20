module

public import CORALean.ContSet.Zonotope.Float.Operations.QuadEntryDown
public import CORALean.ContSet.Zonotope.Float.Operations.QuadEntryUp
public import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadDownLe
public import CORALean.ContSet.PolyZonotope.Float.Theorems.LeQuadUp
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `Zonotope.quadEntryDown` and `quadEntryUp` bracket `uᵀ Q v`

The row `Qᵀ u` lies between its two roundings; its dot product with `v`, bracketed by `quadDown`
and `quadUp`, is `uᵀ Q v`.

## Inputs
* `Q` – matrix of the quadratic form
* `u` – left vector
* `v` – right vector

## Hypotheses
* none

## Conclusion
* `quadEntryDown Q u v ≤ uᵀ Q v ≤ quadEntryUp Q u v`, over the reals
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.quadEntry_bracket (Q : Mat 𝕋 n n) (u v : Vec 𝕋 n) : -- --- CONCL ---
    toReal (Zonotope.quadEntryDown Q u v) ≤ toRealVec u ⬝ᵥ (toRealMat Q *ᵥ toRealVec v)
      ∧ toRealVec u ⬝ᵥ (toRealMat Q *ᵥ toRealVec v)
        ≤ toReal (Zonotope.quadEntryUp Q u v) := by -- --- PROOF ---
  -- the row `Qᵀ u`, bracketed
  have hw : ∀ r, toReal (mulVecDown (fun k j => Q j k) u r)
        ≤ (toRealMat (fun k j => Q j k) *ᵥ toRealVec u) r
      ∧ (toRealMat (fun k j => Q j k) *ᵥ toRealVec u) r
        ≤ toReal (mulVecUp (fun k j => Q j k) u r) :=
    fun r => ⟨dotDown_le (fun j => Q j r) u, le_dotUp (fun j => Q j r) u⟩
  -- its dot product with `v`, and that this is `uᵀ Q v`
  have hT : toRealVec v ⬝ᵥ (toRealMat (fun k j => Q j k) *ᵥ toRealVec u)
      = toRealVec u ⬝ᵥ (toRealMat Q *ᵥ toRealVec v) := by
    have : toRealMat (fun k j => Q j k) = (toRealMat Q)ᵀ := rfl
    rw [this, dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  rw [← hT]
  exact ⟨PolyZonotope.quadDown_le (g := v) hw, PolyZonotope.le_quadUp (g := v) hw⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
