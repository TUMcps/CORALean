module

public import CORALean.ContSet.Zonotope.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.EntryDeviation
public import CORALean.ContSet.Zonotope.Float.Operations.MulResidual
public import CORALean.ContSet.Zonotope.Float.Operations.ErrBound

@[expose] public section

/-!
# `Zonotope.stLeftover`

What everything the coefficients leave over costs in one entry, rounded up.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Entry `i` of what the rounded `β` (`stBeta`) and `Γ` (`stGamma`) of the `'approx:st'` test
(`st`: Sadraddini-Tedrake) leave over, rounded up: the centre and generator residuals of
`c₂ - c₁ = G₂ β`, `G₁ = G₂ Γ`, plus `Z₁`'s error box. The box of `ballCert` must absorb it. -/
def Zonotope.stLeftover (Z₂ Z₁ : Zonotope (Vec 𝕋 n)) (H : Mat 𝕋 Z₂.h n) (i : Fin n) : 𝕋 :=
  addUp (addUp
    (Zonotope.entryDeviation Z₁.c Z₂.I_error.inf (Z₂.pointLo (Z₂.stBeta Z₁ H))
      (Z₂.pointHi (Z₂.stBeta Z₁ H)) i)
    (sumUp fun j => Zonotope.mulResidual (fun i j => Z₁.G j i) (fun i j => Z₂.G j i)
      (Z₂.stGamma Z₁ H) i j))
    (Zonotope.errBound Z₁.I_error i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
