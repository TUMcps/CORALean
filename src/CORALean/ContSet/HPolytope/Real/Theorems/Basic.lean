module

public import CORALean.ContSet.HPolytope.Real.Definitions.PolyNorm
public import CORALean.ContSet.HPolytope.Real.Operations.Lift
public import CORALean.ContSet.HPolytope.Real.Operations.OfPoint
public import CORALean.ContSet.HPolytope.Real.Operations.Volume

@[expose] public section

/-!
# `ContSet/HPolytope/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open Matrix

variable {s n N : ℕ} {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =================================  `HPolytope.comap_exact`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)

/-- By `rfl`: precomposing every constraint with `f` is what asking the constraints
about `f x` means. -/
theorem HPolytope.comap_exact (f : β →ₗ[ℝ] α) (P : HPolytope α) :
    (HPolytope.comap f P).construct = f ⁻¹' P.construct := rfl


-- ==================================  `HPolytope.lift_exact`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A point of the higher-dimensional space is in the lifted polytope exactly when its coordinates
`dims` form a point of `P`; the other coordinates are free. -/
theorem HPolytope.lift_exact (P : HPolytope (Vec ℝ n)) (dims : Fin n → Fin N) :
    (P.lift_ dims).construct = {x : Vec ℝ N | (fun k => x (dims k)) ∈ P.construct} :=
  HPolytope.comap_exact (LinearMap.funLeft ℝ ℝ dims) P


-- =================================  `HPolytope.mem_ofPoint`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `ofPoint v` has no inequalities and reads coordinate `i` back through
`LinearMap.proj i`, so each equality row holds by `LinearMap.proj_apply`. -/
theorem HPolytope.mem_ofPoint (v : Vec ℝ n) : v ∈ (HPolytope.ofPoint v).construct :=
  ⟨fun i => i.elim0, fun i => LinearMap.proj_apply i v⟩


-- ===============================  `HPolytope.polyNorm_le_iff`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `S_P(x) ≤ t` iff `0 ≤ t` and every row's ratio is at most `t`: a fold of `max` is below `t`
exactly when its start and every term are. -/
theorem HPolytope.polyNorm_le_iff {H : Mat ℝ s n} {h : Vec ℝ s} {x : Vec ℝ n} {t : ℝ} :
    HPolytope.polyNorm H h x ≤ t ↔ 0 ≤ t ∧ ∀ i, (H *ᵥ x) i / h i ≤ t := by
  simp [HPolytope.polyNorm, Finset.fold_max_le]


-- ================================  `HPolytope.volume_lt_top`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The case where CORA's value is a number rather than `Inf`: a bounded set has finite Lebesgue
measure. -/
theorem HPolytope.volume_lt_top {P : HPolytope (Vec ℝ n)}
    (h : Bornology.IsBounded P.construct) : P.volume < ⊤ :=
  h.measure_lt_top

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
