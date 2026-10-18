module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Capsule.Float.Operations.Reduce
public import CORALean.ContSet.Capsule.Real.Instances
public import CORALean.ContSet.Capsule.Real.Theorems.MemConstructIffNorm
public import CORALean.ContSet.Capsule.Float.Operations.Basic
public import CORALean.ContSet.InflatedContSet.Theorems.Convex
public import CORALean.ContSet.InflatedContSet.Theorems.IsCompact

@[expose] public section

/-!
# `ContSet/Capsule/Float/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Float

open CORALean FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ================================  `Capsule.convex_construct`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---

/-- A capsule plus a box: both convex, so the sum is. -/
theorem Capsule.convex_construct (C : Capsule 𝕋 n) : Convex ℝ C.construct :=
  InflatedContSet.convex_construct C


-- ==============================  `Capsule.exists_split_of_mem`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- A point of an exact capsule is a point of its segment plus a vector no longer than `r`. -/
theorem Capsule.exists_split_of_mem {K : Real.Capsule n} {y : Vec ℝ n} (hy : y ∈ K.construct) :
    ∃ t ∈ Set.Icc (-1 : ℝ) 1, ∃ w : Vec ℝ n, ‖w‖₂ ≤ K.r ∧ y = K.c + t • K.g + w :=
  let ⟨t, ht, hw⟩ := (Real.Capsule.mem_construct_iff_norm₂ K y).mp hy
  ⟨t, ht, _, hw, by abel⟩


-- ==============================  `Capsule.isCompact_construct`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---

/-- A capsule plus a box: both compact, so the sum is. -/
theorem Capsule.isCompact_construct (C : Capsule 𝕋 n) : IsCompact C.construct :=
  InflatedContSet.isCompact_construct C


-- ==================================  `Capsule.reduce_outer`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `reduce` is the identity, so it encloses trivially. -/
theorem Capsule.reduce_outer (C : Capsule 𝕋 n) (o : ℕ) :
    C.construct ⊆ (C.reduce o).construct :=
  subset_rfl


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
