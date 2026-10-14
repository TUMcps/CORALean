module

public import CORALean.ContSet.Conversion.Real.Theorems.ZonoBundleConZonotopeAllExact
public import CORALean.ContSet.ZonoBundle.Real.Operations.OfPoint
public import CORALean.ContSet.ZonoBundle.Real.Operations.ReduceCombined
public import CORALean.ContSet.ZonoBundle.Real.Operations.Volume
public import CORALean.ContSet.ZonoBundle.Real.Theorems.EnclosingParallelotopeOuter
public import CORALean.ContSet.ZonoBundle.Real.Theorems.IsCompact
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

/-- CORA's `isBounded` is `true`, for a bundle of at least one zonotope; `isCompact_construct`
needs `0 < k` as the empty family denotes the whole space. -/
theorem ZonoBundle.isBounded_construct {zB : ZonoBundle α} (h : 0 < zB.k) :
    Bornology.IsBounded zB.construct :=
  (ZonoBundle.isCompact_construct h).isBounded

end


section

variable {n : ℕ} {α : Type} [AddCommGroup α] [Module ℝ α]


-- ==============================  `ZonoBundle.convex_construct`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An intersection of convex sets, `convex_iInter` applied to each component's own
convexity — which holds vacuously at `k = 0`, `univ` being convex too. -/
theorem ZonoBundle.convex_construct (zB : ZonoBundle α) : Convex ℝ zB.construct :=
  convex_iInter fun i => (zB.Z i).convex_construct


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
-- Reviewed:      ---

/-- `construct` is an intersection over `Fin 1`, so the sole conjunct is
`Zonotope.mem_ofPoint` at the family's one member. -/
theorem ZonoBundle.mem_ofPoint (v : α) : v ∈ (ZonoBundle.ofPoint v).construct := by
  simp only [ZonoBundle.construct, ZonoBundle.ofPoint, Set.mem_iInter]
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
  zB.convex_construct


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
