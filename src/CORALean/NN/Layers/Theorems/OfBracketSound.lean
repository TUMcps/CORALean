import CORALean.NN.Layers.Operations.PolyRelaxationOfBracket
import CORALean.NN.Layers.Theorems.AbsSubLeBracketError
import CORALean.NN.Layers.Theorems.EvalPolyShiftConst

/-!
# A recentred bracket is a sound relaxation

What the bracket buys, and the only place `σ` appears: the recentred fit encloses it wherever
the two ends did. The fit is free and the bracket owes everything.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ} {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyRelaxation.ofBracket_sound {c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋} {lo hi : 𝕋 → 𝕋 → 𝕋}
    (hb : ∀ (l u : 𝕋) (t : ℝ), toReal l ≤ t → t ≤ toReal u →
      toReal (lo l u) ≤ σ t - Real.evalPoly (fun k => toReal (c l u k)) t
        ∧ σ t - Real.evalPoly (fun k => toReal (c l u k)) t ≤ toReal (hi l u)) :
    (PolyRelaxation.ofBracket c lo hi).Sound σ := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  obtain ⟨h1, h2⟩ := hb l u t hl hu
  show |σ t - Real.evalPoly
      (fun k => toReal (shiftConst (c l u) (bracketShift (lo l u) (hi l u)) k)) t|
    ≤ toReal (bracketError (c l u 0) (lo l u) (hi l u))
  rw [evalPoly_shiftConst, sub_add_eq_sub_sub]
  exact abs_sub_le_bracketError h1 h2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
