module

public import CORALean.NN.Layers.Definitions.PolyDerivBound
public import CORALean.NN.Layers.Operations.PolyDerivCenter
public import CORALean.Global.Float.SoundFloatArithmetic

@[expose] public section

/-!
# A stored center reads back exactly

One index carries the linear term and every other contributes nothing.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_polyDerivCenter (c : Fin (n + 1) → 𝕋) :
    toReal (polyDerivCenter c)
      = Real.polyDerivCenter (fun k => toReal (c k)) := by -- --- PROOF ---
  show toReal (if h : 1 < n + 1 then c ⟨1, h⟩ else zero)
    = ∑ i : Fin (n + 1), if (i : ℕ) = 1 then toReal (c i) else 0
  by_cases h : 1 < n + 1
  · -- one index carries the linear term and every other contributes nothing
    have hsum : (∑ i : Fin (n + 1), if (i : ℕ) = 1 then toReal (c i) else 0)
        = toReal (c ⟨1, h⟩) := by
      rw [Finset.sum_eq_single (⟨1, h⟩ : Fin (n + 1))]
      · rw [if_pos rfl]
      · exact fun b _ hb => if_neg fun hb1 => hb (Fin.ext hb1)
      · exact fun hmem => absurd (Finset.mem_univ _) hmem
    rw [dif_pos h, hsum]
  · have hn : n = 0 := by omega
    subst hn
    rw [dif_neg h, toReal_zero, Fin.sum_univ_one, if_neg (by norm_num)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
