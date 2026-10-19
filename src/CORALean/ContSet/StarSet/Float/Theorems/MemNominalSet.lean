module

public import CORALean.ContSet.StarSet.Float.StarSet

@[expose] public section

/-!
# The points of the nominal part of a float star set

The nominal star set is the stored numbers read as reals, so its points are the `c + G α` over the
factors in the box `[l, u]` in the predicate's nominal part, each number read through `toReal`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Float.SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem StarSet.mem_nominalSet_iff (s : StarSet 𝕋 n) (x : Vec ℝ n) : -- --- CONCL ---
    x ∈ nominalSet s ↔ ∃ α : Fin s.m → ℝ,
      ((∀ k, toReal (s.dom.inf k) ≤ α k ∧ α k ≤ toReal (s.dom.sup k))
        ∧ α ∈ s.pred.nominal.construct) ∧
      ∀ i, x i = toReal (s.c i) + ∑ k, toReal (s.G i k) * α k :=
  Iff.rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
