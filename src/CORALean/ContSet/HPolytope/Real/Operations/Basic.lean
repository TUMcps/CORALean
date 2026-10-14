module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.ContSet.HPolytope.Real.Operations.Eqs
public import CORALean.ContSet.HPolytope.Real.Operations.Fullspace
public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Real.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Real.Operations.Translate
public import CORALean.Global.LinProg.Duality

@[expose] public section

/-!
# `ContSet/HPolytope/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

open Matrix

-- there is no row index to discharge, in either block
variable {α : Type} [AddCommGroup α] [Module ℝ α] {q n : ℕ} {S : Set α}


-- ============================  `HPolytope.construct_eq_feasible`  ============================= --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- A halfspace description's own construct is `Feasible` -/
theorem HPolytope.construct_eq_feasible (P : HPolytope α) :
    P.construct = Feasible P.A P.b P.Ae P.be := rfl


-- =============================  `HPolytope.construct_fullspace`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- There is no row index to discharge, in either block, so the set it denotes is
one `ext` away. -/
theorem HPolytope.construct_fullspace : (HPolytope.fullspace α).construct = Set.univ := by
  ext x
  exact ⟨fun _ => trivial, fun _ => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩


-- =================================  `HPolytope.mem_eqs_iff`  ================================== --
-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- Membership in `HPolytope.eqs` -/
theorem HPolytope.mem_eqs_iff {Ae : Mat ℝ q n} {be : Vec ℝ q} {x : Vec ℝ n} :
    x ∈ (HPolytope.eqs Ae be).construct ↔ ∀ i, (Ae *ᵥ x) i = be i :=
  ⟨fun h i => h.2 i, fun h => ⟨fun i => i.elim0, h⟩⟩


-- ================================  `HPolytope.mem_ineqs_iff`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   05-September-2026
-- Reviewed:      14-October-2026 (Tobias Ladner)

/-- Membership in `HPolytope.ineqs` -/
theorem HPolytope.mem_ineqs_iff {A : Mat ℝ q n} {b : Vec ℝ q} {x : Vec ℝ n} :
    x ∈ (HPolytope.ineqs A b).construct ↔ ∀ i, (A *ᵥ x) i ≤ b i :=
  ⟨fun h i => h.1 i, fun h => ⟨h, fun i => i.elim0⟩⟩


-- ====================================  `HPolytope.minus`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- CORA's `polytope/minus.m` accepts a column vector as subtrahend and nothing else
(a set subtrahend is a Minkowski difference, a different method), so `minus P v`
is the translation by `-v`. -/
def HPolytope.minus (P : HPolytope α) (v : α) : HPolytope α :=
  HPolytope.translate (-v) P


-- ===============================  `HPolytope.subset_ofBounds`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- Nothing here solves a linear program. It consumes the answers. -/
theorem HPolytope.subset_ofBounds (Aq : Fin q → (α →ₗ[ℝ] ℝ))
    (u : ∀ i, SupportBound S (Aq i)) : S ⊆ (HPolytope.ofBounds Aq u).construct :=
  fun _ hx => ⟨fun i => (u i).le _ hx, fun i => i.elim0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
