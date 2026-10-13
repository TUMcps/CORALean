module

public import CORALean.ContSet.Zonotope.Float.Operations.MulResidual
public import Mathlib.Data.Matrix.Mul
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# `mulResidual` bounds `|A - G Γ|`

Each entry of `G Γ` lies between its two directed dot products, so the entry of `A - G Γ` lies
between the two differences, and `mulResidual` takes the larger magnitude of their bounds.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mulResidual_bound {m h : ℕ} (A : Mat 𝕋 n m) (G : Mat 𝕋 n h) (Γ : Mat 𝕋 h m)
    (i : Fin n) (j : Fin m) :
    |(toRealMat A - toRealMat G * toRealMat Γ) i j|
      ≤ toReal (Zonotope.mulResidual A G Γ i j) := by -- --- PROOF ---
  have hd := dotDown_le (fun l => G i l) fun l => Γ l j
  have hu := le_dotUp (fun l => G i l) fun l => Γ l j
  have hprod : (toRealMat G * toRealMat Γ) i j = ∑ l, toReal (G i l) * toReal (Γ l j) := rfl
  have h1 := subDown_le_sub (A i j) (dotUp (fun l => G i l) fun l => Γ l j)
  have h2 := sub_le_subUp (A i j) (dotDown (fun l => G i l) fun l => Γ l j)
  rw [Matrix.sub_apply, hprod]
  simp only [Zonotope.mulResidual, toReal_maximum, toReal_absolute]
  have hA : toRealMat A i j = toReal (A i j) := rfl
  rw [hA]
  exact abs_le_max_abs_abs (by linarith) (by linarith)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
