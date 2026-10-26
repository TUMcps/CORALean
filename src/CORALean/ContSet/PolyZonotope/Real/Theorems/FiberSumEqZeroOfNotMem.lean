module

public import CORALean.ContSet.PolyZonotope.Real.Operations.CompactKeep

@[expose] public section

/-!
# A dropped column's fibre sums to zero

Split out of `Compact.lean` (issue #62): used again by `compactGens` below and
by `Theorems/CompactGensExact.lean`, both outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [Module ℝ α] in
/-- Membership through the classical instance `compactKeep` fixes, which
instance search cannot rediscover at a use site. File-local: only
`fiberSum_eq_zero_of_notMem` below needs it. -/
private theorem PolyZonotope.aux_mem_compactKeep_iff {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (G : Fin h → α) (j : Fin h) :
    j ∈ PolyZonotope.compactKeep E G ↔ PolyZonotope.fiberSum (PolyZonotope.rep E) G j ≠ 0 := by
  rw [PolyZonotope.compactKeep]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
theorem PolyZonotope.fiberSum_eq_zero_of_notMem {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (G : Fin h → α) {j : Fin h} (hj : j ∉ PolyZonotope.compactKeep E G) :
    PolyZonotope.fiberSum (PolyZonotope.rep E) G j = 0 :=
  not_not.mp fun hne => hj ((PolyZonotope.aux_mem_compactKeep_iff E G j).mpr hne)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
