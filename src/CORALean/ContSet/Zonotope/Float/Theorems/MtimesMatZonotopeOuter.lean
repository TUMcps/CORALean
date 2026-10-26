module

public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Operations.MtimesMatZonotope
public import CORALean.ContSet.Zonotope.Float.Theorems.OfEntryBoundsOuter
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesMatZonotopeOuter
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeMatIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# `Zonotope.mtimesMatZonotope` over-approximates every member's image

`(a + e)(z + f) = az + (af + e(z + f))`. The nominal image `az` lies in the exact
`mtimesMatZonotope` (`Real.Zonotope.mtimesMatZonotope_outer`), whose center and
generators `dotDown_le`/`le_dotUp` bracket; `af` and `e(z + f)` are
`Interval.mtimesIntervalMat_outer` at the boxes `matInterval_contains` and
`interval_contains` supply.

## Inputs
* `M` – matrix zonotope
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* images under every member matrix are contained in the result
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One exact matrix-vector product of stored values, between its directed roundings. -/
private theorem Zonotope.aux_mulVec_bounds (A : Mat 𝕋 m n) (v : Vec 𝕋 n) (i : Fin m) :
    toReal (mulVecDown A v i) ≤ Matrix.mulVecBilin ℝ ℝ (toRealMat A) (toRealVec v) i
      ∧ Matrix.mulVecBilin ℝ ℝ (toRealMat A) (toRealVec v) i ≤ toReal (mulVecUp A v i) := by
  rw [Matrix.mulVecBilin_apply]
  exact ⟨dotDown_le (A i) v, le_dotUp (A i) v⟩


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.mtimesMatZonotope_outer (M : Zonotope (Mat 𝕋 m n))
    (Z : Zonotope (Vec 𝕋 n)) : -- --- CONCL ---
    (⋃ A ∈ M.construct, (A *ᵥ ·) '' Z.construct)
      ⊆ (Zonotope.mtimesMatZonotope M Z).construct := by -- --- PROOF ---
  intro y hy
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
  obtain ⟨_, ⟨a, ha, e, he, rfl⟩, x, hx, rfl⟩ := hy
  obtain ⟨z, hz, f, hf, rfl⟩ := hx
  -- `nominal Z` spelled out, so that its generator count is `Z.h` to `simp` below
  let Zn : CORALean.Real.Zonotope (Vec ℝ n) := ⟨Z.h, toRealVec Z.c, fun j i => toReal (Z.G j i)⟩
  set R := CORALean.Real.Zonotope.mtimesMatZonotope M.nominal Zn
  -- `h` first, with no expected type, as `Real.Zonotope.mtimesMatZonotope_outer` itself does
  have h := CORALean.Real.Zonotope.mtimesMatZonotope_outer M.nominal Zn
  have haz : a *ᵥ z ∈ R.construct := h (Set.mem_biUnion ha ⟨z, hz, rfl⟩)
  -- the matrix zonotope's nominal part, boxed: its nominal part with a zero box
  have ha' : a ∈ ({ M with I_error := Interval.point fun _ _ => zero } :
      Zonotope (Mat 𝕋 m n)).matInterval.construct := by
    refine Zonotope.matInterval_contains _ ⟨a, ha, 0, ?_, add_zero a⟩
    refine Interval.mem_mat_iff.mpr fun i j => ?_
    show toReal (zero : 𝕋) ≤ 0 ∧ 0 ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_rfl, le_rfl⟩
  have hx : z + f ∈ Z.interval.construct := Zonotope.interval_contains Z ⟨z, hz, f, hf, rfl⟩
  have hE : a *ᵥ f + e *ᵥ (z + f) ∈ ((Interval.mtimesIntervalMat _ Z.I_error).plus
      (Interval.mtimesIntervalMat M.I_error Z.interval)).construct :=
    Interval.plus_outer _ _ ⟨_, Interval.mtimesIntervalMat_outer _ _
      (Set.mem_biUnion ha' ⟨f, hf, rfl⟩), _, Interval.mtimesIntervalMat_outer _ _
      (Set.mem_biUnion he ⟨z + f, hx, rfl⟩), rfl⟩
  -- each generator block of `bilin`, bracketed by the same directed products
  have hG : ∀ i k, toReal (Fin.append (Fin.append (fun l => mulVecDown (M.G l) Z.c)
        (fun j => mulVecDown M.c (Z.G j)))
        (fun k => mulVecDown (M.G (finProdFinEquiv.symm k).1)
          (Z.G (finProdFinEquiv.symm k).2)) k i) ≤ R.G k i
      ∧ R.G k i ≤ toReal (Fin.append (Fin.append (fun l => mulVecUp (M.G l) Z.c)
        (fun j => mulVecUp M.c (Z.G j)))
        (fun k => mulVecUp (M.G (finProdFinEquiv.symm k).1)
          (Z.G (finProdFinEquiv.symm k).2)) k i) := by
    intro i k
    refine Fin.addCases (fun k' => Fin.addCases (fun l => ?_) (fun l => ?_) k') (fun l => ?_) k
      <;> simp only [R, Zn, CORALean.Real.Zonotope.mtimesMatZonotope,
        CORALean.Real.Zonotope.bilin, Zonotope.nominal, realImage_mat, Fin.append_left,
        Fin.append_right]
      <;> exact Zonotope.aux_mulVec_bounds _ _ i
  -- the nominal image rounded, the two error terms in the box
  have hmem : a *ᵥ z + (a *ᵥ f + e *ᵥ (z + f)) ∈ (Zonotope.mtimesMatZonotope M Z).construct :=
    Zonotope.ofEntryBounds_outer R _ (fun i => Zonotope.aux_mulVec_bounds M.c Z.c i) hG
      ⟨a *ᵥ z, haz, _, hE, rfl⟩
  have heq : (a + e) *ᵥ (z + f) = a *ᵥ z + (a *ᵥ f + e *ᵥ (z + f)) := by
    rw [Matrix.add_mulVec, Matrix.mulVec_add a z f, add_assoc]
  show (a + e) *ᵥ (z + f) ∈ _
  rw [heq]
  exact hmem

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
