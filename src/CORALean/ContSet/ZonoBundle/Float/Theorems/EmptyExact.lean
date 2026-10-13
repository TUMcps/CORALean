import CORALean.ContSet.ZonoBundle.Float.Operations.Empty
import CORALean.ContSet.Zonotope.Float.Theorems.OriginExact

/-!
# `ZonoBundle.empty` denotes the empty set

The two members are the points `0` and `e₀`, which differ in the first coordinate.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.empty_exact (n : ℕ) (hn : 0 < n) :
    (ZonoBundle.empty n hn : ZonoBundle (Vec 𝕋 n)).construct = ∅ := by -- --- PROOF ---
  ext x
  simp only [ZonoBundle.construct, Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
  intro h
  have h0 : x ∈ (Zonotope.origin n : Zonotope (Vec 𝕋 n)).construct := h (0 : Fin 2)
  have h1 : x ∈ (Zonotope.point fun i : Fin n =>
      if i = ⟨0, hn⟩ then (one : 𝕋) else zero).construct := h (1 : Fin 2)
  rw [Zonotope.origin_exact, Set.mem_singleton_iff] at h0
  rw [Zonotope.construct_point, Set.mem_singleton_iff] at h1
  have := congrFun (h0.symm.trans h1) ⟨0, hn⟩
  simp [toRealVec, toReal_one] at this

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
