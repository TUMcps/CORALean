import CORALean.Global.Float.Instances.Real.Instances

/-!
# ℝ reads itself

`toReal` at the ℝ model is the identity. True by `rfl`, but a statement written once over the
scalar and read at `𝕋 := ℝ` mentions it, and a proof rewriting there needs it by name.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- =======================================  MAIN THEOREM  ======================================= --

@[simp] theorem toReal_real (a : ℝ) : SoundFloatArithmetic.toReal a = a := rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
