import CORALean.ContSet.HPolytope.Float.HPolytope

/-!
# The float `HPolytope` from constraint matrices

CORA's two constructors. The inequality one absorbs its rounding by raising `b`;
the equality one takes an interval right-hand side, which is where an equality's
rounding goes.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {q n : ℕ}

def HPolytope.ineqs (A : Mat 𝕋 q n) (b : Vec 𝕋 q) : HPolytope 𝕋 n where
  m := q
  A := A
  b := b
  me := 0
  Ae := fun i => i.elim0
  be := ⟨fun i => i.elim0, fun i => i.elim0⟩

def HPolytope.eqs (Ae : Mat 𝕋 q n) (be : Interval 𝕋 q) : HPolytope 𝕋 n where
  m := 0
  A := fun i => i.elim0
  b := fun i => i.elim0
  me := q
  Ae := Ae
  be := be

/-- No constraints, so every point qualifies: what a zonotope's coefficients
answer to beyond the unit box. -/
def HPolytope.fullspace (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) : HPolytope 𝕋 n where
  m := 0
  A := fun i => i.elim0
  b := fun i => i.elim0
  me := 0
  Ae := fun i => i.elim0
  be := ⟨fun i => i.elim0, fun i => i.elim0⟩

variable [SoundFloatArithmetic 𝕋]

theorem HPolytope.mem_fullspace (x : Vec ℝ n) :
    x ∈ (HPolytope.fullspace 𝕋 n).construct :=
  HPolytope.mem_construct_iff.mpr ⟨fun i => i.elim0, fun i => i.elim0⟩

-- membership at each shape, the block that is absent discharged by `Fin.elim0`
theorem HPolytope.mem_ineqs_iff {A : Mat 𝕋 q n} {b : Vec 𝕋 q} {x : Vec ℝ n} :
    x ∈ (HPolytope.ineqs A b).construct ↔ ∀ i, (toRealMat A *ᵥ x) i ≤ toReal (b i) :=
  ⟨fun h => (HPolytope.mem_construct_iff.mp h).1,
   fun h => HPolytope.mem_construct_iff.mpr ⟨h, fun i => i.elim0⟩⟩

theorem HPolytope.mem_eqs_iff {Ae : Mat 𝕋 q n} {be : Interval 𝕋 q} {x : Vec ℝ n} :
    x ∈ (HPolytope.eqs Ae be).construct ↔
      ∀ i, toReal (be.inf i) ≤ (toRealMat Ae *ᵥ x) i
           ∧ (toRealMat Ae *ᵥ x) i ≤ toReal (be.sup i) :=
  ⟨fun h => (HPolytope.mem_construct_iff.mp h).2,
   fun h => HPolytope.mem_construct_iff.mpr ⟨fun i => i.elim0, h⟩⟩

end CORALean.Float
