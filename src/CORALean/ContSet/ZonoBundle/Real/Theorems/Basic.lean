module

public import CORALean.ContSet.Conversion.Real.Theorems.ZonoBundleConZonotopeAllExact
public import CORALean.ContSet.ZonoBundle.Real.Operations.OfPoint
public import CORALean.ContSet.ZonoBundle.Real.Operations.ReduceCombined
public import CORALean.ContSet.ZonoBundle.Real.Operations.Volume
public import CORALean.ContSet.ZonoBundle.Real.Theorems.EnclosingParallelotopeOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.ConstructEqIInter
public import CORALean.ContSet.SetIntersection.Theorems.IsCompact
public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.Zonotope.Real.Theorems.Convex
public import CORALean.ContSet.Zonotope.Real.Theorems.OfPointMem
public import CORALean.ContSet.Conversion.Real.Operations.ZonoBundle_to_ConZonotope

@[expose] public section

/-!
# `ContSet/ZonoBundle/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

section

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =============================  `ZonoBundle.isBounded_construct`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `isBounded` is `true` for a bundle of a zonotope or more, the empty one being `univ`. -/
theorem ZonoBundle.isBounded_construct {zB : ZonoBundle α} (h : 0 < zB.k) :
    Bornology.IsBounded zB.construct :=
  (SetIntersection.isCompact_construct (I := zB.toSetIntersection)
    (List.ofFn_eq_nil_iff.not.mpr h.ne')).isBounded

end


section

variable {n : ℕ} {α : Type} [AddCommGroup α] [Module ℝ α]


-- =============================  `ZonoBundle.exists_conZonotope`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `representsa_(zB, 'conZonotope')` is `true`: with a first member, the folded intersection of the
members' constrained zonotopes (`conZonotopeAll`) denotes the bundle. -/
theorem ZonoBundle.exists_conZonotope (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    ∃ cZ : ConZonotope (Vec ℝ n), cZ.construct = zB.construct :=
  ⟨zB.conZonotopeAll hk, ZonoBundle.conZonotopeAll_exact zB hk⟩


-- =================================  `ZonoBundle.mem_ofPoint`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)

/-- `construct` is an intersection over `Fin 1`, so the sole conjunct is
`Zonotope.mem_ofPoint` at the family's one member. -/
theorem ZonoBundle.mem_ofPoint (v : α) : v ∈ (ZonoBundle.ofPoint v).construct := by
  simp only [ZonoBundle.construct_eq_iInter, ZonoBundle.ofPoint, Set.mem_iInter]
  exact fun _ => Zonotope.mem_ofPoint v


-- ============================  `ZonoBundle.reduceCombined_outer`  ============================= --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `enclosingParallelotope` encloses the bundle at any edges, so at whichever `n` generators the
filters select. -/
theorem ZonoBundle.reduceCombined_outer (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    zB.construct ⊆ (zB.reduceCombined hk).construct :=
  ZonoBundle.enclosingParallelotope_outer zB hk _


-- ============================  `ZonoBundle.representsa_convexSet`  ============================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `representsa_(zB, 'convexSet')` is `true`: an intersection of convex zonotopes is convex. -/
theorem ZonoBundle.representsa_convexSet (zB : ZonoBundle (Vec ℝ n)) :
    Convex ℝ zB.construct :=
  SetIntersection.convex_construct zB.toSetIntersection


-- ================================  `ZonoBundle.volume_lt_top`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The bundle is compact, so bounded, so of finite Lebesgue measure. -/
theorem ZonoBundle.volume_lt_top (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    zB.volume < ⊤ :=
  (ZonoBundle.isBounded_construct hk).measure_lt_top

end

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
