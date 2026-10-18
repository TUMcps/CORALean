module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.ConstructEqIInter
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeConZonotopeExact
public import CORALean.ContSet.ConZonotope.Real.Theorems.ConstructFoldlIntersectionEq
public import CORALean.ContSet.Conversion.Real.Operations.ZonoBundle_to_ConZonotope

@[expose] public section

/-!
# A bundle's constrained zonotope, at one component
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Exact: the folded intersection denotes the bundle. -/
theorem ZonoBundle.conZonotopeAll_exact (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    (zB.conZonotopeAll hk).construct = zB.construct := by -- --- PROOF ---
  unfold ZonoBundle.conZonotopeAll
  rw [ConZonotope.construct_foldl_intersection_eq]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iInter, ← Zonotope.conZonotope_exact,
    ZonoBundle.construct_eq_iInter]
  constructor
  · rintro ⟨h0, hi⟩ ⟨j, hj⟩
    rcases j with _ | j
    · exact h0
    · exact hi ⟨j, by omega⟩
  · intro h
    exact ⟨h ⟨0, hk⟩, fun i => h ⟨i + 1, by omega⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
