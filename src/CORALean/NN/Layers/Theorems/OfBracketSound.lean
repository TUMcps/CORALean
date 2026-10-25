module

public import CORALean.NN.Layers.Operations.PolyRelaxationOfBracket
public import CORALean.NN.Layers.Operations.BracketError
public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.NN.Layers.Theorems.EvalPolyShiftConst

@[expose] public section

/-!
# A recentered bracket is a sound relaxation

What the bracket buys, and the only place `σ` appears: the recentered fit encloses it wherever
the two ends did. The fit is free and the bracket owes everything.

## Inputs
* `c` – fit coefficients for each box
* `lo` – lower end of the error bracket
* `hi` – upper end of the error bracket

## Hypotheses
* `hb` – the bracket contains the activation minus the fit

## Conclusion
* the recentered relaxation is sound for the activation
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {σ : ℝ → ℝ} {m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]

/-- A value in the bracket is within its radius of the shift. -/
theorem aux_abs_sub_le_bracketError {c0 lo hi : 𝕋} {y : ℝ}
    (h1 : toReal lo ≤ y) (h2 : y ≤ toReal hi) : -- --- CONCL ---
    |y - (toReal (addUp c0 (bracketShift lo hi)) - toReal c0)|
      ≤ toReal (bracketError c0 lo hi) := by -- --- PROOF ---
  have hlo := subDown_le_sub (addUp c0 (bracketShift lo hi)) c0
  have hhi := sub_le_subUp (addUp c0 (bracketShift lo hi)) c0
  have hA := sub_le_subUp hi (subDown (addUp c0 (bracketShift lo hi)) c0)
  have hB := sub_le_subUp (subUp (addUp c0 (bracketShift lo hi)) c0) lo
  -- each end of the max covers one end of the moved bracket
  have hmA := le_max_left (toReal (subUp hi (subDown (addUp c0 (bracketShift lo hi)) c0)))
    (toReal (subUp (subUp (addUp c0 (bracketShift lo hi)) c0) lo))
  have hmB := le_max_right (toReal (subUp hi (subDown (addUp c0 (bracketShift lo hi)) c0)))
    (toReal (subUp (subUp (addUp c0 (bracketShift lo hi)) c0) lo))
  rw [bracketError, toReal_maximum, abs_le]
  exact ⟨by linarith, by linarith⟩

end


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyRelaxation.ofBracket_sound {c : 𝕋 → 𝕋 → Fin (m + 1) → 𝕋} {lo hi : 𝕋 → 𝕋 → 𝕋}
    (hb : ∀ (l u : 𝕋) (t : ℝ), toReal l ≤ t → t ≤ toReal u →
      toReal (lo l u) ≤ σ t - Real.evalPoly (fun k => toReal (c l u k)) t
        ∧ σ t - Real.evalPoly (fun k => toReal (c l u k)) t ≤ toReal (hi l u)) : -- --- CONCL ---
    (PolyRelaxation.ofBracket c lo hi).IsSound σ := by -- --- PROOF ---
  refine ⟨fun {l u t} hl hu => ?_⟩
  obtain ⟨h1, h2⟩ := hb l u t hl hu
  show |σ t - Real.evalPoly
      (fun k => toReal (shiftConst (c l u) (bracketShift (lo l u) (hi l u)) k)) t|
    ≤ toReal (bracketError (c l u 0) (lo l u) (hi l u))
  rw [evalPoly_shiftConst, sub_add_eq_sub_sub]
  exact aux_abs_sub_le_bracketError h1 h2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
