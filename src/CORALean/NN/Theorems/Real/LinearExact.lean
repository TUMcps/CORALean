module

public import CORALean.ContSet.Interval.Real.Theorems.MemPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MtimesExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PlusExact
public import CORALean.NN.Layers.Operations.Linear
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_PolyZonotope
public import CORALean.ContSet.Conversion.Float.Theorems.ConZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopePolyZonotopeExact

@[expose] public section

/-!
# The linear layer loses nothing at a polynomial zonotope

ℝ-only: `mtimes` and `plus` are exact at the exact polynomial zonotope, where a machine scalar
pays its rounding into an error box.

`Layer.linear` encloses by `mtimes` and then `plus`, and a polynomial zonotope
is exact under both: a linear map of the ambient space cannot touch the
monomials, and `plus` keeps the two factor blocks apart rather than identifying
them.

The bias is a box of zero width, so the second half is a translation. That is
where the exactness of `plus` is actually needed — a singleton is what the
`OfInterval` conversion has to denote, and it does, both the zonotope's centre
and its generators collapsing onto the point.

This is what makes a linear layer convergent for nothing: the enclosed set
*is* the image, so it lies inside every inflation of it and no level is spent.
-/

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix Pointwise ContSet Plus Mtimes OfInterval

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A zero-width box denotes its point and nothing else, through both conversion
steps: every generator vanishes and the centre is the point. -/
theorem aux_construct_point_polyZonotope (b : Vec ℝ m) :
    ((Interval.point b).polyZonotope).construct = ({b} : Set (Vec ℝ m)) := by -- --- PROOF ---
  have hc : (Interval.point b).zonotope.c = b := by
    funext i
    show (b i + b i) / 2 = b i
    ring
  have hG : ∀ j, (Interval.point b).zonotope.G j = (0 : Vec ℝ m) := by
    intro j
    funext i
    show (if i = j then (b i - b i) / 2 else 0) = (0 : ℝ)
    rw [sub_self, zero_div, ite_self]
  have hpz : (Interval.point b).polyZonotope = (Interval.point b).zonotope.polyZonotope := rfl
  rw [hpz, ← Zonotope.polyZonotope_exact]
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨β, _, rfl⟩
    -- no generator reaches anywhere, so the centre is the only point
    have hzero : ∑ j, β j • (Interval.point b).zonotope.G j = (0 : Vec ℝ m) := by
      rw [Finset.sum_congr rfl fun j _ => by rw [hG j, smul_zero]]
      exact Finset.sum_const_zero
    rw [Set.mem_singleton_iff, hzero, add_zero, hc]
  · rw [Set.singleton_subset_iff]
    exact Interval.zonotope_contains _ (Interval.mem_point b)


-- =======================================  MAIN THEOREM  ======================================= --

/-- ℝ-only, a polynomial zonotope being exact under `mtimes` and `plus` only there. -/
theorem Layer.linear_exact (W : Mat ℝ m n) (b : Vec ℝ m) (s : PolyZonotope (Vec ℝ n)) :
    construct ((CORALean.Layer.linear (S := 𝒫𝒵) W b).enclose s)
      = (fun x => W *ᵥ x + b) '' construct s := by -- --- PROOF ---
  show ((PolyZonotope.mtimes W s).plus (Interval.point b).polyZonotope).construct
      = (fun x => W *ᵥ x + b) '' s.construct
  -- both operations read backwards, and the bias is then a translation
  rw [← PolyZonotope.plus_exact, ← PolyZonotope.mtimes_exact,
    aux_construct_point_polyZonotope, Set.add_singleton, Set.image_image]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
