module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.ConstructEqIInter
public import CORALean.ContSet.ZonoBundle.Real.Operations.Empty
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMemIff
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# `ZonoBundle.empty` denotes the empty set


-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.empty_exact (n : ℕ) (hn : 0 < n) :
    (ZonoBundle.empty n hn).construct = ∅ := by -- --- PROOF ---
  ext x
  simp only [ZonoBundle.construct_eq_iInter, Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
  intro h
  have h0 := h (0 : Fin 2)
  have h1 := h (1 : Fin 2)
  have h0' : x ∈ (Zonotope.ofPoint (0 : Vec ℝ n)).construct := h0
  have h1' : x ∈ (Zonotope.ofPoint (Pi.single (⟨0, hn⟩ : Fin n) (1 : ℝ) : Vec ℝ n)).construct := h1
  rw [Zonotope.mem_ofPoint_iff] at h0' h1'
  have := congrFun (h0'.symm.trans h1') ⟨0, hn⟩
  simp at this

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
