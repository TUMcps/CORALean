module

public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.PolyZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Interval.Float.Theorems.MtimesIntervalMatOuter
public import CORALean.ContSet.Interval.Float.Theorems.SubMemMatResidual
public import CORALean.ContSet.PolyZonotope.Float.Theorems.NominalPointEq
public import CORALean.ContSet.PolyZonotope.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.PolyZonotope.Float.Theorems.Basic
public import CORALean.ContSet.PolyZonotope.Float.Theorems.FiberMaterialise
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemFiberIff
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemFiberOfIndep
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemToSetIffFiber
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MtimesPoint
public import CORALean.ContSet.PolyZonotope.Float.Theorems.PlusFiber

@[expose] public section

/-!
# An interval matrix times a fiber point

`mid(M) pZ` keeps the factors: the stored product is the product's own point at the same `a` and
`β`, up to the residual. The box `(M - mid(M)) [pZ]` has none. So a product `M x` of a matrix of the
box and a point of `pZ` at `a` is a point of the result at `a`.

## Inputs
* `IM` – interval matrix
* `pZ` – polynomial zonotope
* `M` – matrix in the box
* `a` – factor values
* `x` – point

## Hypotheses
* `hM` – the matrix is in the box
* `ha` – the factors are in the unit box
* `hx` – the point is in the fiber at `a`

## Conclusion
* the product is in the fiber of the result at `a`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A stored matrix times a fiber point is a fiber point of `mtimes` at the same factors. -/
private theorem PolyZonotope.aux_mtimes_fiber (M : Mat 𝕋 m n) (pZ : PolyZonotope (Vec 𝕋 n))
    {a : Fin pZ.p → ℝ} (ha : ∀ k, |a k| ≤ 1) {x : Vec ℝ n} (hx : x ∈ pZ.fiber a) : -- --- CONCL ---
    toRealMat M *ᵥ x ∈ (PolyZonotope.mtimes M pZ).fiber a := by -- --- PROOF ---
  obtain ⟨β, hβ, e, he, rfl⟩ := (PolyZonotope.mem_fiber_iff _ _ _).mp hx
  set n0 : Vec ℝ n := pZ.nominal.point a + fun i => ∑ j, toReal (pZ.GI j i) * β j with hn0
  obtain ⟨r, hr, hxr⟩ := PolyZonotope.mtimes_point M pZ ha hβ (x := n0) fun i => by
    simp only [hn0, Pi.add_apply]
    repeat rw [PolyZonotope.nominal_point_eq]
  refine (PolyZonotope.mem_fiber_iff _ _ _).mpr ⟨β, hβ, toRealMat M *ᵥ e + r,
    Interval.plus_outer _ _ ⟨_, Interval.mtimes_outer M _ (Set.mem_image_of_mem _ he), r, hr, rfl⟩,
    ?_⟩
  funext i
  have hxr' : (toRealMat M *ᵥ n0) i = toReal ((PolyZonotope.mtimes M pZ).c i)
      + (∑ l : Fin (PolyZonotope.mtimes M pZ).h, toReal ((PolyZonotope.mtimes M pZ).G l i)
          * Real.PolyZonotope.monomial (PolyZonotope.mtimes M pZ).E a l)
      + (∑ j : Fin (PolyZonotope.mtimes M pZ).q, toReal ((PolyZonotope.mtimes M pZ).GI j i) * β j)
      + r i := hxr i
  rw [Matrix.mulVec_add, Pi.add_apply, hxr']
  repeat rw [PolyZonotope.nominal_point_eq]
  simp only [Pi.add_apply]
  ring


-- =======================================  MAIN THEOREM  ======================================= --

/-- A matrix of the box times a fiber point is a fiber point of the result at the same factors. -/
theorem PolyZonotope.mtimesIntervalMat_fiber (IM : Interval (Mat 𝕋 m n))
    (pZ : PolyZonotope (Vec 𝕋 n)) {M : Mat ℝ m n} (hM : M ∈ IM.toSet) {a : Fin pZ.p → ℝ}
    (ha : ∀ k, |a k| ≤ 1) {x : Vec ℝ n} (hx : x ∈ pZ.fiber a) : -- --- CONCL ---
    M *ᵥ x ∈ (PolyZonotope.mtimesIntervalMat IM pZ).fiber a := by -- --- PROOF ---
  set C := Interval.centerMat IM with hC
  set Rs := Interval.matResidual IM.inf IM.sup C with hRs
  -- the matrix is the stored center plus a matrix of the residual box
  have hD : (fun i j => M i j - toReal (C i j)) ∈ Rs.toSet :=
    Interval.sub_mem_matResidual fun i j => by
      have h := hM (i, j)
      simp only [Entrywise.entry_mat] at h
      exact h
  have hsplit : M *ᵥ x = toRealMat C *ᵥ x + (fun i j => M i j - toReal (C i j)) *ᵥ x := by
    rw [← Matrix.add_mulVec]
    congr 1
    funext i j
    simp [toRealMat]
  -- the second term is in the box of the product with the hull of the set
  have hxs : x ∈ pZ.toSet := (PolyZonotope.mem_toSet_iff_fiber pZ x).mpr ⟨a, ha, hx⟩
  have hxI : x ∈ pZ.zonotope.interval.toSet :=
    Zonotope.interval_contains _ (PolyZonotope.zonotope_contains pZ hxs)
  have hbox := Interval.mtimesIntervalMat_outer Rs pZ.zonotope.interval
    (Set.mem_biUnion hD (Set.mem_image_of_mem _ hxI))
  have hz := Interval.zonotope_contains _ hbox
  rw [hsplit]
  unfold PolyZonotope.mtimesIntervalMat
  have key := PolyZonotope.plus_fiber (PolyZonotope.mtimes C pZ)
    (Interval.mtimesIntervalMat Rs pZ.zonotope.interval).zonotope.ofIndep (a := a)
    (PolyZonotope.aux_mtimes_fiber C pZ ha hx) (Zonotope.mem_fiber_ofIndep _ hz _)
  exact (Set.ext_iff.mp (PolyZonotope.fiber_materialise ((PolyZonotope.mtimes C pZ).plus
    (Interval.mtimesIntervalMat Rs pZ.zonotope.interval).zonotope.ofIndep) a) _).mpr key

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
