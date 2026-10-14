module

public import CORALean.ContSet.HPolytope.Float.Operations.EqScalar
public import CORALean.ContSet.HPolytope.Float.Operations.Fullspace
public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs
public import CORALean.ContSet.HPolytope.Float.Operations.MemIntersectionIff
public import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Float.Operations.Translate

@[expose] public section

/-!
# `ContSet/HPolytope/Float/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix

-- membership at each shape, the block that is absent discharged by `Fin.elim0`
variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ} {S : Set (Vec ℝ n)}


-- ==============================  `HPolytope.intersection_exact`  ============================== --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- The constraint lists concatenate. Nothing is computed, so nothing rounds. -/
theorem HPolytope.intersection_exact (P₁ P₂ : HPolytope 𝕋 (Vec 𝕋 n)) :
    P₁.construct ∩ P₂.construct = (P₁.intersection P₂).construct :=
  Set.ext fun _ => HPolytope.mem_intersection_iff.symm


-- ================================  `HPolytope.mem_fullspace`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- Every point is in `HPolytope.fullspace` -/
theorem HPolytope.mem_fullspace (x : Vec ℝ n) :
    x ∈ (HPolytope.fullspace 𝕋 n).construct :=
  HPolytope.mem_construct_iff.mpr ⟨fun i => i.elim0, fun i => i.elim0⟩


-- ================================  `HPolytope.mem_ineqs_iff`  ================================= --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- Membership at each shape, the block that is absent discharged by `Fin.elim0`. -/
theorem HPolytope.mem_ineqs_iff {A : Mat 𝕋 q n} {b : Vec 𝕋 q} {x : Vec ℝ n} :
    x ∈ (HPolytope.ineqs A b).construct ↔ ∀ i, (toRealMat A *ᵥ x) i ≤ toReal (b i) :=
  ⟨fun h => (HPolytope.mem_construct_iff.mp h).1,
   fun h => HPolytope.mem_construct_iff.mpr ⟨h, fun i => i.elim0⟩⟩


-- ===============================  `HPolytope.subset_ofBounds`  ================================ --
-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---

/-- The rounding has already been paid where each bound was combined, and nothing
rounds here. -/
theorem HPolytope.subset_ofBounds (Aq : Mat 𝕋 q n) (u : ∀ i, FloatBound 𝕋 S (rowLin Aq i)) :
    S ⊆ (HPolytope.ofBounds Aq u).construct :=
  fun x hx => HPolytope.mem_ineqs_iff.mpr fun i => (u i).le x hx

end CORALean.Float


namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ==================================  `HPolytope.isZeroVec`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- All entries `eqScalar` to `zero`.

Every entry certified equal to `zero`: CORA's `withinTol(row, 0)` at tolerance zero. -/
def HPolytope.isZeroVec (v : Vec 𝕋 n) : Bool :=
  (List.finRange n).all fun j => HPolytope.eqScalar (v j) zero


-- ====================================  `HPolytope.minus`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The translation by `-v`. Negation is exact, so the subtrahend costs no rounding
of its own; the shift rounds as `translate` does. -/
def HPolytope.minus (P : HPolytope 𝕋 (Vec 𝕋 n)) (v : Vec 𝕋 n) : HPolytope 𝕋 (Vec 𝕋 n) :=
  HPolytope.translate (fun i => neg (v i)) P

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
