module

public import CORALean.ContSet.ConPolyZono.Float.Operations.LinComb
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealVecPlusB
public import CORALean.ContSet.ConPolyZono.Float.Theorems.ToRealMatPlusA
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ForallAbsSubAppendIff
public import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialPadE
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MulVecPlusAPlusE

@[expose] public section

/-!
# `ConPolyZono.linComb`'s constraint reads each side's own factors

As in the exact layer's `satisfies_linComb_iff`: `monomial_padE` drops the fresh segment factor,
which no constraint monomial reads, and `mulVec_plusA_plusE` splits what is left at
`toRealMat_plusA`, the right-hand sides and the slacks at `toRealVec_plusB`.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.satisfies_linComb_iff (cPZ₁ cPZ₂ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (a : Fin (cPZ₁.p + cPZ₂.p + 1) → ℝ) : -- --- STMT ---
    (cPZ₁.linComb cPZ₂).satisfies a
      ↔ cPZ₁.satisfies (fun k => a (Fin.castAdd 1 (Fin.castAdd cPZ₂.p k)))
        ∧ cPZ₂.satisfies (fun k => a (Fin.castAdd 1 (Fin.natAdd cPZ₁.p k))) := by -- --- PROOF ---
  have hb : ∀ {m₁ m₂ : ℕ} (u : Vec 𝕋 m₁) (v : Vec 𝕋 m₂) (i : Fin (m₁ + m₂)),
      toReal (ConPolyZono.plusB u v i) = Fin.append (toRealVec u) (toRealVec v) i :=
    fun u v i => congrFun (ConPolyZono.toRealVec_plusB u v) i
  have hm : Real.PolyZonotope.monomial
      (Real.ConPolyZono.padE (Real.PolyZonotope.plusE cPZ₁.R cPZ₂.R) 1) a
      = Real.PolyZonotope.monomial (Real.PolyZonotope.plusE cPZ₁.R cPZ₂.R)
          (fun k => a (Fin.castAdd 1 k)) :=
    funext fun l => Real.ConPolyZono.monomial_padE _ 1 a l
  show (∀ i, |(toRealMat (ConPolyZono.plusA cPZ₁.A cPZ₂.A) *ᵥ Real.PolyZonotope.monomial
      (Real.ConPolyZono.padE (Real.PolyZonotope.plusE cPZ₁.R cPZ₂.R) 1) a) i
      - toReal (ConPolyZono.plusB cPZ₁.b cPZ₂.b i)|
      ≤ |toReal (ConPolyZono.plusB cPZ₁.b_error cPZ₂.b_error i)|) ↔ _
  simp only [ConPolyZono.toRealMat_plusA, hm, Real.ConPolyZono.mulVec_plusA_plusE, hb]
  exact Real.ConPolyZono.forall_abs_sub_append_iff _ _ _ _ _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
