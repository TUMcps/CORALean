module

public import CORALean.ContSet.Zonotope.Float.Operations.QuadMapTri
public import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadDownLe
public import CORALean.ContSet.PolyZonotope.Float.Theorems.LeQuadUp
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# The entries of `Zonotope.quadMapTri` bracket the exact bilinear forms

The entry `(a, b)` of `M = Zᵀ Q Z` is `z_aᵀ Q z_b`. `Zonotope.step_quadMapTriEntryDown` and `Up`
form the row `Qᵀ z_a` from below and above (`mulVecDown`, `mulVecUp`) and take its dot product with
`z_b` by `PolyZonotope.quadDown`, `quadUp`; the exact value lies between them. The center and the
generators are sums of such entries, so their roundings follow.

## Inputs
* `Q` – quadratic form
* `Zext` – the center and the generators of the operand, `[c G]`
* `a` – row of the entry
* `b` – column of the entry

## Hypotheses
* none

## Conclusion
* the exact `z_aᵀ Q z_b` lies between the entry rounded down and up
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `z_aᵀ Q z_b` is between `step_quadMapTriEntryDown` and `step_quadMapTriEntryUp`. -/
theorem Zonotope.quadMapTri_entry_bracket (Q : Mat 𝕋 n n) (Zext : Fin (N + 1) → Vec 𝕋 n)
    (a b : Fin (N + 1)) : -- --- CONCL ---
    toReal (Zonotope.step_quadMapTriEntryDown Q Zext a b)
        ≤ toRealVec (Zext a) ⬝ᵥ (toRealMat Q *ᵥ toRealVec (Zext b))
      ∧ toRealVec (Zext a) ⬝ᵥ (toRealMat Q *ᵥ toRealVec (Zext b))
        ≤ toReal (Zonotope.step_quadMapTriEntryUp Q Zext a b) := by -- --- PROOF ---
  -- the row `Qᵀ z_a`, bracketed
  have hw : ∀ r, toReal (mulVecDown (fun k j => Q j k) (Zext a) r)
        ≤ (toRealMat (fun k j => Q j k) *ᵥ toRealVec (Zext a)) r
      ∧ (toRealMat (fun k j => Q j k) *ᵥ toRealVec (Zext a)) r
        ≤ toReal (mulVecUp (fun k j => Q j k) (Zext a) r) :=
    fun r => ⟨dotDown_le (fun j => Q j r) (Zext a), le_dotUp (fun j => Q j r) (Zext a)⟩
  -- its dot product with `z_b`, and that this is `z_aᵀ Q z_b`
  have hT : toRealVec (Zext b) ⬝ᵥ (toRealMat (fun k j => Q j k) *ᵥ toRealVec (Zext a))
      = toRealVec (Zext a) ⬝ᵥ (toRealMat Q *ᵥ toRealVec (Zext b)) := by
    have : toRealMat (fun k j => Q j k) = (toRealMat Q)ᵀ := rfl
    rw [this, dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  rw [← hT]
  exact ⟨PolyZonotope.quadDown_le (g := Zext b) hw, PolyZonotope.le_quadUp (g := Zext b) hw⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
