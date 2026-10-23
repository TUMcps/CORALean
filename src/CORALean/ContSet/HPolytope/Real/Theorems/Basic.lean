module

public import CORALean.ContSet.HPolytope.Real.Definitions.PolyNorm
public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Real.Operations.Lift
public import CORALean.ContSet.HPolytope.Real.Operations.ToIneqs
public import CORALean.ContSet.HPolytope.Real.Theorems.MemIffRows
public import CORALean.ContSet.HPolytope.Real.Operations.OfPoint
public import CORALean.ContSet.HPolytope.Real.Operations.Volume
public import CORALean.ContSet.HPolytope.Real.Operations.Eqs
public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Real.Operations.OfBounds

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


-- ============================  `HPolytope.construct_eq_feasible`  ============================= --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- A halfspace description's own construct is `Feasible` -/
theorem HPolytope.construct_eq_feasible (P : HPolytope α) :
    P.construct = Feasible P.A P.b P.Ae P.be := rfl


-- ===========================  `HPolytope.construct_subset_dropEqs`  =========================== --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Dropping the equalities only widens the set. -/
theorem HPolytope.construct_subset_dropEqs (P : HPolytope α) : P.construct ⊆ P.dropEqs.construct :=
  fun _ hx => ⟨hx.1, fun i => i.elim0⟩


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


-- =================================  `HPolytope.mem_eqs_iff`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- Membership in `HPolytope.eqs` -/
theorem HPolytope.mem_eqs_iff {Ae : Mat ℝ s n} {be : Vec ℝ s} {x : Vec ℝ n} :
    x ∈ (HPolytope.eqs Ae be).construct ↔ ∀ i, (Ae *ᵥ x) i = be i :=
  ⟨fun h i => h.2 i, fun h => ⟨fun i => i.elim0, h⟩⟩


-- ================================  `HPolytope.mem_ineqs_iff`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)

/-- Membership in `HPolytope.ineqs` -/
theorem HPolytope.mem_ineqs_iff {A : Mat ℝ s n} {b : Vec ℝ s} {x : Vec ℝ n} :
    x ∈ (HPolytope.ineqs A b).construct ↔ ∀ i, (A *ᵥ x) i ≤ b i :=
  ⟨fun h i => h.1 i, fun h => ⟨h, fun i => i.elim0⟩⟩


-- =================================  `HPolytope.mem_ofPoint`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `ofPoint v` has no inequalities and reads coordinate `i` back through
`LinearMap.proj i`, so each equality row holds by `LinearMap.proj_apply`. -/
theorem HPolytope.mem_ofPoint (v : Vec ℝ n) : v ∈ (HPolytope.ofPoint v).construct :=
  ⟨fun i => i.elim0, fun i => LinearMap.proj_apply i v⟩


-- ================================  `HPolytope.mem_relax_iff`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A point of the relaxed polytope meets every inequality up to its added `rᵢ`. -/
theorem HPolytope.mem_relax_iff {P : HPolytope α} {r : Fin P.m → ℝ} {x : α} :
    x ∈ (P.relax r).construct ↔ (∀ i, P.A i x ≤ P.b i + r i) ∧ ∀ i, P.Ae i x = P.be i :=
  Iff.rfl


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


-- ===============================  `HPolytope.subset_ofBounds`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- Nothing here solves a linear program. It consumes the answers. -/
theorem HPolytope.subset_ofBounds {S : Set α} (Aq : Fin s → (α →ₗ[ℝ] ℝ))
    (u : ∀ i, SupportBound S (Aq i)) : S ⊆ (HPolytope.ofBounds Aq u).construct :=
  fun _ hx => ⟨fun i => (u i).le _ hx, fun i => i.elim0⟩


-- ================================  `HPolytope.toIneqs_exact`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Writing every equality as its two halves leaves the set unchanged. -/
theorem HPolytope.toIneqs_exact (P : HPolytope α) : P.toIneqs.construct = P.construct :=
  Set.ext fun _ => ⟨fun h => HPolytope.mem_construct_iff_rows.mpr h.1,
    fun h => ⟨HPolytope.mem_construct_iff_rows.mp h, fun i => i.elim0⟩⟩


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
