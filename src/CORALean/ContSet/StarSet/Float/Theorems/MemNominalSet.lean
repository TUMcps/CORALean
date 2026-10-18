module

public import CORALean.ContSet.StarSet.Float.StarSet

@[expose] public section

/-!
# The points of the nominal part of a float star set

The nominal star set is the stored numbers read as reals, so its points are the `c + G α` over the
factors in the box `[l, u]` satisfying every row, each number read through `toReal`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Float.SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem StarSet.mem_nominalSet_iff (s : StarSet 𝕋 n) (x : Vec ℝ n) : -- --- STMT ---
    x ∈ nominalSet s ↔ ∃ α : Fin s.m → ℝ,
      ((∀ k, toReal (s.pred.l k) ≤ α k ∧ α k ≤ toReal (s.pred.u k)) ∧
      (∀ r ∈ s.pred.cons, ∑ k, toReal (r.1 k) * α k ≤ toReal r.2)) ∧
      ∀ i, x i = toReal (s.c i) + ∑ k, toReal (s.G i k) * α k := by -- --- PROOF ---
  change (∃ α : Fin s.m → ℝ, (_ ∧ (∀ r ∈ s.pred.cons.map _, _)) ∧ _) ↔ _
  simp only [List.forall_mem_map]
  exact Iff.rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
