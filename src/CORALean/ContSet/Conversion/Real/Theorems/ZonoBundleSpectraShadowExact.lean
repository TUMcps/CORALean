module

public import CORALean.ContSet.ZonoBundle.Real.Theorems.ToSetEqIInter
public import CORALean.ContSet.SpectraShadow.Real.Theorems.InfExact
public import CORALean.ContSet.SpectraShadow.Real.Theorems.InterExact
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeSpectraShadowExact
public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_SpectraShadow

@[expose] public section

/-!
# A zonotope bundle as a spectrahedral shadow

Exact. CORA converts every member (`Zonotope.spectraShadow`) and intersects the results with
`and_(·, ·, 'exact')`, in order: that is `SpectraShadow.inter`, the members' inequalities side by
side with the points forced equal. An empty family, which denotes the whole space here, is
`SpectraShadow.Inf`; CORA returns an empty `spectraShadow()` object there instead. The flags CORA
caches on the result (`bounded`, `emptySet`, `fullDim`, `center`) are not part of the denotation.

## Inputs
* `zB` – zonotope bundle

## Hypotheses
* none

## Conclusion
* bundle equals its spectrahedral shadow
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A left fold of `inter` is the intersection of what it starts from and what it folds in. -/
private theorem ZonoBundle.aux_foldl_inter (Ss : List (SpectraShadow (Vec ℝ n)))
    (S : SpectraShadow (Vec ℝ n)) : -- --- CONCL ---
    (Ss.foldl SpectraShadow.inter S).toSet
      = S.toSet ∩ {x | ∀ T ∈ Ss, x ∈ T.toSet} := by -- --- PROOF ---
  induction Ss generalizing S with
  | nil => simp
  | cons T Ts ih =>
    rw [List.foldl_cons, ih, ← SpectraShadow.inter_exact]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, List.mem_cons, forall_eq_or_imp]
    tauto


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.spectraShadow_exact (zB : ZonoBundle (Vec ℝ n)) : -- --- CONCL ---
    zB.toSet = zB.spectraShadow.toSet := by -- --- PROOF ---
  have hmem : ∀ x, x ∈ zB.toSet ↔ ∀ T ∈ List.ofFn (fun i => (zB.Z i).spectraShadow),
      x ∈ T.toSet := by
    intro x
    simp only [ZonoBundle.toSet_eq_iInter, Set.mem_iInter, List.mem_ofFn,
      forall_exists_index, forall_apply_eq_imp_iff, ← Zonotope.spectraShadow_exact]
  unfold ZonoBundle.spectraShadow
  generalize hL : List.ofFn (fun i => (zB.Z i).spectraShadow) = L at hmem
  cases L with
  | nil => rw [SpectraShadow.Inf_exact]; ext x; simp [hmem]
  | cons S Ss =>
    rw [ZonoBundle.aux_foldl_inter]
    ext x
    simp [hmem]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
