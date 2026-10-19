module

public import CORALean.ContSet.StarSet.Float.Operations.Basic
public import CORALean.ContSet.StarSet.Float.StarSet
public import CORALean.ContSet.StarSet.Real.Operations.Basic

@[expose] public section

/-!
# The float factor added is the exact one, read as reals

`StarSet.LinPred.snoc` in floats pads every row with `zero` and appends the range's floats;
read through `toReal`, entry by entry, that is the exact layer's `snoc` at the range read as
reals, `zero` reading as `0`. So a float step that adds a factor is stated, and proved, through
the exact layer's membership (`Real.StarSet.LinPred.mem_snoc_iff`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The factor added in floats is the exact factor added, its range read as reals. -/
theorem StarSet.LinPred.nominal_snoc (p : StarSet.LinPred 𝕋 m) (lo hi : 𝕋) :
    (p.snoc lo hi).nominal = p.nominal.snoc (toReal lo) (toReal hi) := by -- --- PROOF ---
  -- a vector extended in floats reads as the vector read, extended
  have h : ∀ (v : Fin m → 𝕋) (a : 𝕋), (fun k => toReal (Fin.snoc (α := fun _ => 𝕋) v a k))
      = Fin.snoc (α := fun _ => ℝ) (fun k => toReal (v k)) (toReal a) := fun v a =>
    funext fun k => Fin.lastCases (by simp) (fun k => by simp) k
  simp only [StarSet.LinPred.snoc, StarSet.LinPred.nominal, CORALean.Real.StarSet.LinPred.snoc,
    List.map_map, Function.comp_def, h, toReal_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
