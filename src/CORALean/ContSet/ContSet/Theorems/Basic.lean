module

public import CORALean.ContSet.ContSet.ContSet
public import CORALean.ContSet.ContSet.Definitions.Interfaces
public import CORALean.ContSet.ContSet.Operations.Basic
public import CORALean.ContSet.ContSet.Theorems.UnionSubsetSetLinComb

@[expose] public section

/-!
# `ContSet/ContSet/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

section

open ContSet ContSetLike

variable {S α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] [ContSetLike S α]


-- ===============================  `CompactSet.isBounded_toSet`  =============================== --
-- Authors:       Claude Sonnet 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `CompactSet.isBounded_toSet`: compactness over a normed space gives boundedness for free. -/
theorem CompactSet.isBounded_toSet [CompactSet S α] (s : S) :
    Bornology.IsBounded (toSet s) :=
  (CompactSet.isCompact_toSet s).isBounded


-- ===============================  `CompactSet.isClosed_toSet`  ================================ --
-- Authors:       Claude Sonnet 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `CompactSet.isClosed_toSet`: compactness over a normed space gives closedness for free. -/
theorem CompactSet.isClosed_toSet [CompactSet S α] (s : S) : IsClosed (toSet s) :=
  (CompactSet.isCompact_toSet s).isClosed

end


section

open ContSet ContSetLike

variable {S α : Type} [ContSetLike S α] [Isequal S]


-- ====================================  `ContSet.eq_toSet`  ==================================== --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- If `eq` holds the two representations denote one set. Sound, not exact: `eq` can fail on
two representations of one set. -/
theorem ContSet.eq_toSet {s t : S} (h : ContSet.eq s t) : toSet s = toSet t :=
  Isequal.isequal_toSet s t h


-- =================================  `ContSet.ne_of_toSet_ne`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- If the denoted sets differ, `ne` holds. Only this direction: `ne` can hold of two
representations of one set, since `isequal` is conservative. -/
theorem ContSet.ne_of_toSet_ne {s t : S} (h : toSet s ≠ toSet t) : ContSet.ne s t :=
  fun hi => h (Isequal.isequal_toSet s t hi)

end


section

open Matrix Pointwise
open ContSet ContSetLike


-- ====================================  `ContSet.mem_iff`  ===================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- Membership in a representation is membership in the set it denotes. -/
theorem ContSet.mem_iff {S α : Type} [ContSetLike S α] {s : S} {x : α} :
    x ∈ s ↔ x ∈ toSet s := Iff.rfl


-- ===================================  `ContSet.toSet_set`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- A set is its own `ContSetLike` representation. -/
@[simp] theorem ContSet.toSet_set {α : Type} (X : Set α) : toSet X = X := rfl

end


section

open Matrix Pointwise
open ContSet ContSetLike
open Scalar


-- ===================================  `ContSet.toSet_mat`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- A matrix is the set holding its real image, as a `ContSet`. -/
@[simp] theorem ContSet.toSet_mat {𝕋 : Type} [Scalar 𝕋] {m n : ℕ} (M : Mat 𝕋 m n) :
    toSet M = {toRealMat M} := rfl


-- ===================================  `matMulBilin_apply`  ==================================== --
-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   14-October-2026
-- Reviewed:      ---

/-- `matMulBilin` is the matrix product. -/
@[simp] theorem matMulBilin_apply {p q r : ℕ} (A : Mat ℝ p q) (B : Mat ℝ q r) :
    matMulBilin A B = A * B := rfl


-- ==================================  `reindexLin_bijective`  ================================== --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A relabelling is bijective: `reindexLin e.symm` undoes it on either side. -/
theorem reindexLin_bijective {n m : ℕ} (e : Fin m ≃ Fin n) : Function.Bijective (reindexLin e) :=
  Function.bijective_iff_has_inverse.mpr ⟨reindexLin e.symm,
    fun x => funext fun i => by simp [reindexLin], fun x => funext fun i => by simp [reindexLin]⟩

end


section

open ContSet ContSetLike Scalar

variable {S α : Type} [ContSetLike S α]


-- ==================================  `ContSet.uplus_exact`  =================================== --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `uplus` denotes the set it is given, so it is exact, not only an outer bound. -/
theorem ContSet.uplus_exact (s : S) : toSet (ContSet.uplus s) = toSet s := rfl

end


section

open ContSet ContSetLike

variable {α : Type} [AddCommGroup α] [Module ℝ α] {S : Type} [ContSetLike S α]


-- ==============================  `LinComb.union_subset_linComb`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `linComb_outer` and `union_subset_setLinComb`: an enclosure of CORA's `or`. -/
theorem LinComb.union_subset_linComb [LinComb S α] (s t : S) (hs : (toSet s).Nonempty)
    (ht : (toSet t).Nonempty) :
    toSet s ∪ toSet t ⊆ toSet (LinComb.linComb s t) :=
  (union_subset_setLinComb hs ht).trans (LinComb.linComb_outer s t)


-- ====================================  `setLinComb_mono`  ===================================== --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `Set.linComb` is monotone in both sets: the same points and weights still witness it. -/
theorem setLinComb_mono {X X' Y Y' : Set α} (hX : X ⊆ X') (hY : Y ⊆ Y') :
    Set.linComb X Y ⊆ Set.linComb X' Y' :=
  fun _ ⟨y₁, h₁, y₂, h₂, lam, hl, e⟩ => ⟨y₁, hX h₁, y₂, hY h₂, lam, hl, e⟩

end

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
