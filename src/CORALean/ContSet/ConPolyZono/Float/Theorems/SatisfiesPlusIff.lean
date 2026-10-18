module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
public import CORALean.ContSet.ConPolyZono.Float.Operations.PlusA
public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealVecPlusB
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatPlusA
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ForallAbsSubAppendIff
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MulVecPlusAPlusE

@[expose] public section

/-!
# Two constraint systems side by side hold exactly when each does

The rows split as the exact layer's do (`mulVec_plusA_plusE`, at the read-back matrix
`toRealMat_plusA`), and so do the right-hand sides and the slacks (`toRealVec_plusB`).
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Two constraint systems side by side hold exactly when each holds on the
factors it came with. -/
theorem ConPolyZono.satisfies_plus_iff (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (a : Fin (cPZ₁.p + cPZ₂.p) → ℝ) : -- --- STMT ---
    (cPZ₁.plus cPZ₂).satisfies a
      ↔ cPZ₁.satisfies (fun k => a (Fin.castAdd cPZ₂.p k))
        ∧ cPZ₂.satisfies (fun k => a (Fin.natAdd cPZ₁.p k)) := by -- --- PROOF ---
  have hb : ∀ {m₁ m₂ : ℕ} (u : Vec 𝕋 m₁) (v : Vec 𝕋 m₂) (i : Fin (m₁ + m₂)),
      toReal (ConPolyZono.plusB u v i) = Fin.append (toRealVec u) (toRealVec v) i :=
    fun u v i => congrFun (ConPolyZono.toRealVec_plusB u v) i
  show (∀ i, |(toRealMat (ConPolyZono.plusA cPZ₁.A cPZ₂.A) *ᵥ Real.PolyZonotope.monomial
      (Real.PolyZonotope.plusE cPZ₁.R cPZ₂.R) a) i - toReal (ConPolyZono.plusB cPZ₁.b cPZ₂.b i)|
      ≤ |toReal (ConPolyZono.plusB cPZ₁.b_error cPZ₂.b_error i)|) ↔ _
  simp only [ConPolyZono.toRealMat_plusA, Real.ConPolyZono.mulVec_plusA_plusE, hb]
  exact Real.ConPolyZono.forall_abs_sub_append_iff _ _ _ _ _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
