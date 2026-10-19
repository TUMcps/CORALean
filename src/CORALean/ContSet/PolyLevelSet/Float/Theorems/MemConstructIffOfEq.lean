module

public import CORALean.ContSet.PolyLevelSet.Float.PolyLevelSet

@[expose] public section

/-!
# A float polynomial level set of equations

Where every row is `=`, a point is in the set exactly when it solves each read-back row to within
its slack: `|(A μ_R(x))ᵢ - bᵢ| ≤ |b_errorᵢ|`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `=` in every row, membership is every row met to within its slack. -/
theorem PolyLevelSet.mem_construct_iff_of_eq {P : PolyLevelSet 𝕋 n} (h : ∀ i, P.op i = .eq)
    {x : Vec ℝ n} :
    x ∈ P.construct ↔ ∀ i, |(toRealMat P.A *ᵥ Real.PolyZonotope.monomial P.R x) i
      - toReal (P.b i)| ≤ |toReal (P.b_error i)| := by
  refine forall_congr' fun i => ?_
  rw [h i]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
