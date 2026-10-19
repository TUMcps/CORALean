module

public import CORALean.ContSet.Zonotope.Float.Operations.CubContractUp
public import CORALean.ContSet.PolyZonotope.Float.Theorems.QuadDownLe
public import CORALean.ContSet.PolyZonotope.Float.Theorems.LeQuadUp

@[expose] public section

/-!
# `cubContractDown` and `cubContractUp` bracket the cubic contraction

Two applications of `quadDown_le` and `le_quadUp`: the middle vector is bracketed by `dotDown_le`
and `le_dotUp`, the quadratic form by the first application, the sum over `k` by the second.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.cubContract_bracket (T : Fin m → Fin n → Mat 𝕋 n n) (u v w : Vec 𝕋 n)
    (i : Fin m) : -- --- STMT ---
    toReal (Zonotope.cubContractDown T u v w i)
        ≤ ∑ k, toReal (u k) * (toRealVec v ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec w))
      ∧ ∑ k, toReal (u k) * (toRealVec v ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec w))
        ≤ toReal (Zonotope.cubContractUp T u v w i) := by -- --- PROOF ---
  -- the middle vector, bracketed
  have hw : ∀ k r, toReal (mulVecDown (T i k) w r)
        ≤ (toRealMat (T i k) *ᵥ toRealVec w) r
      ∧ (toRealMat (T i k) *ᵥ toRealVec w) r ≤ toReal (mulVecUp (T i k) w r) :=
    fun k r => ⟨dotDown_le (T i k r) w, le_dotUp (T i k r) w⟩
  -- the quadratic forms, bracketed
  have hq : ∀ k,
      toReal (PolyZonotope.quadDown v (mulVecDown (T i k) w) (mulVecUp (T i k) w))
          ≤ toRealVec v ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec w)
        ∧ toRealVec v ⬝ᵥ (toRealMat (T i k) *ᵥ toRealVec w)
          ≤ toReal (PolyZonotope.quadUp v (mulVecDown (T i k) w) (mulVecUp (T i k) w)) :=
    fun k => ⟨PolyZonotope.quadDown_le (g := v) (hw k), PolyZonotope.le_quadUp (g := v) (hw k)⟩
  exact ⟨PolyZonotope.quadDown_le (g := u) (w := fun k => toRealVec v ⬝ᵥ
      (toRealMat (T i k) *ᵥ toRealVec w)) hq,
    PolyZonotope.le_quadUp (g := u) (w := fun k => toRealVec v ⬝ᵥ
      (toRealMat (T i k) *ᵥ toRealVec w)) hq⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
