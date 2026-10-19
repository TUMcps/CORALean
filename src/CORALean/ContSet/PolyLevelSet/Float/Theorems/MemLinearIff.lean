module

public import CORALean.ContSet.PolyLevelSet.Float.Operations.Linear
public import CORALean.ContSet.PolyZonotope.Real.Operations.MonomialIdentE

@[expose] public section

/-!
# A point of `PolyLevelSet.linear`, over a floating-point scalar

A point of the linear level set meets every read-back row `(A x - b)ᵢ` within its slack.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A point of the linear level set is in the box and meets every row `(A x - b)ᵢ ⋈ᵢ 0` within its
slack. -/
theorem PolyLevelSet.mem_linear_iff {m : ℕ} (A : Mat 𝕋 m n) (b b_error : Vec 𝕋 m)
    (op : Fin m → Real.CompOp) (D : Interval (Vec 𝕋 n)) (x : Vec ℝ n) : -- --- STMT ---
    x ∈ (PolyLevelSet.linear A b b_error op D).construct
      ↔ x ∈ D.construct ∧ ∀ i, (op i).IsMetWithin ((toRealMat A *ᵥ x - toRealVec b) i)
        |toReal (b_error i)| := by -- --- PROOF ---
  have hμ : Real.PolyZonotope.monomial (Real.PolyZonotope.identE n) x = x :=
    funext fun k => Real.PolyZonotope.monomial_identE x k
  show (x ∈ D.construct ∧ ∀ i, (op i).IsMetWithin ((toRealMat A *ᵥ Real.PolyZonotope.monomial
    (Real.PolyZonotope.identE n) x - toRealVec b) i) |toReal (b_error i)|) ↔ _
  rw [hμ]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
