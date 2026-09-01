import CORALean.ContSet.HPolytope.HPolytope

/-!
# `HPolytope` from constraint matrices

CORA's `polytope(A, b)` and `polytope([], [], Ae, be)`, which `and` combines into
the four-argument constructor. Only here does a constraint become a matrix row,
and only at `Vec` — the representation itself needs no coordinates.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {q n : ℕ}

/-- Row `i` of `M`, as the functional a constraint is. -/
def HPolytope.aux_rowLin (M : Mat ℝ q n) (i : Fin q) : Vec ℝ n →ₗ[ℝ] ℝ where
  toFun x := (M *ᵥ x) i
  map_add' x y := by rw [Matrix.mulVec_add]; rfl
  map_smul' c x := by rw [RingHom.id_apply, Matrix.mulVec_smul]; rfl

/-- CORA's `polytope(A, b)`: one inequality per row. -/
def HPolytope.ineqs (A : Mat ℝ q n) (b : Vec ℝ q) : HPolytope (Vec ℝ n) where
  m := q
  A := HPolytope.aux_rowLin A
  b := b
  me := 0
  Ae := Fin.elim0
  be := Fin.elim0

/-- CORA's `polytope([], [], Ae, be)`: one equality per row. -/
def HPolytope.eqs (Ae : Mat ℝ q n) (be : Vec ℝ q) : HPolytope (Vec ℝ n) where
  m := 0
  A := Fin.elim0
  b := Fin.elim0
  me := q
  Ae := HPolytope.aux_rowLin Ae
  be := be

theorem HPolytope.mem_ineqs_iff {A : Mat ℝ q n} {b : Vec ℝ q} {x : Vec ℝ n} :
    x ∈ (HPolytope.ineqs A b).construct ↔ ∀ i, (A *ᵥ x) i ≤ b i :=
  ⟨fun h i => h.1 i, fun h => ⟨h, fun i => i.elim0⟩⟩

theorem HPolytope.mem_eqs_iff {Ae : Mat ℝ q n} {be : Vec ℝ q} {x : Vec ℝ n} :
    x ∈ (HPolytope.eqs Ae be).construct ↔ ∀ i, (Ae *ᵥ x) i = be i :=
  ⟨fun h i => h.2 i, fun h => ⟨fun i => i.elim0, h⟩⟩

end CORALean.Real
