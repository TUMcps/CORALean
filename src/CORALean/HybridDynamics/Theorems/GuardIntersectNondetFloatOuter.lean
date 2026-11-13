module

public import CORALean.HybridDynamics.Theorems.OrthDefectFloatMem
public import CORALean.HybridDynamics.Theorems.JoinedBoxFloatContains
public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.HybridDynamics.Operations.GuardIntersectNondetFloat
public import CORALean.ContSet.Interval.Float.Theorems.OrOuter
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.PolyZonotope_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_ConZonotope
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Float.Theorems.Basic
public import CORALean.ContSet.Conversion.Float.Theorems.ConZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeConZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.PolyZonotopeZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# `Location.guardIntersectNondetFloat` holds every state that meets the guard

A state of one of the reach sets that lies in the guard lies in every member of the bundle, so in
the bundle. Each member is a box in a basis, widened by the defect `(I - B Bᵀ) x`
(`Location.orthDefectFloat`), so the bases need not be orthogonal.
Outer only: every step over-approximates.

## Inputs
* `Bs` – bases
* `R₀` – initial set
* `Rs` – reach sets
* `guard` – constrained zonotope guard
* `R` – reach set
* `x` – trajectory of the stay

## Hypotheses
* `hR` – the reach set is among the given ones
* `hx` – state lies in the reach set
* `hg` – state lies on the guard

## Conclusion
* state lies in the bundle
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   12-November-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A state in a reach set and in the guard lies in the bundle, for any bases. -/
theorem Location.guardIntersectNondetFloat_outer (Bs : List (Mat 𝕋 n n)) (R₀ : Zonotope (Vec 𝕋 n))
    (Rs : List (Zonotope (Vec 𝕋 n))) (guard : ConZonotope 𝕋 (Vec 𝕋 n))
    {R : Zonotope (Vec 𝕋 n)} (hR : R ∈ R₀ :: Rs) {x : Vec ℝ n} (hx : x ∈ R.toSet)
    (hg : x ∈ guard.toSet) : -- --- CONCL ---
    x ∈ (Location.guardIntersectNondetFloat Bs R₀ Rs guard).toSet := by -- --- PROOF ---
  -- a point of the start or of any box folded in is a point of the hull
  have hfold : ∀ (Is : List (Interval (Vec 𝕋 n))) (J : Interval (Vec 𝕋 n)) (y : Vec ℝ n),
      (y ∈ J.toSet ∨ ∃ I ∈ Is, y ∈ I.toSet) → y ∈ (Is.foldl Interval.or J).toSet := by
    intro Is
    induction Is with
    | nil => exact fun J y h => h.resolve_right (by simp)
    | cons I Is ih =>
      intro J y h
      rw [List.foldl_cons]
      refine ih _ y ?_
      rcases h with hJ | ⟨I', hI', hy⟩
      · exact Or.inl (Interval.or_outer J I (Or.inl hJ))
      · rcases List.mem_cons.mp hI' with rfl | hI'
        · exact Or.inl (Interval.or_outer J I' (Or.inr hy))
        · exact Or.inr ⟨I', hI', hy⟩
  refine SetIntersection.mem_toSet_ofFn.mpr fun i => ?_
  unfold Location.guardIntersectNondetFloat
  dsimp only
  generalize Bs[i] = B
  -- the state boxed in the basis
  have h1 : Scalar.toRealMat Bᵀ *ᵥ x ∈
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) Bᵀ R).toSet :=
    Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) Bᵀ R
      (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx))
  have h2 := hfold (Rs.map
    fun R => (Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) Bᵀ R).interval)
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) Bᵀ R₀).interval
      (Scalar.toRealMat Bᵀ *ᵥ x) (by
      rcases List.mem_cons.mp hR with rfl | hR'
      · exact Or.inl (Zonotope.interval_contains _ h1)
      · exact Or.inr ⟨_, List.mem_map.mpr ⟨R, hR', rfl⟩, Zonotope.interval_contains _ h1⟩)
  generalize List.foldl Interval.or
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) Bᵀ R₀).interval
    (Rs.map fun R => (Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) Bᵀ
      R).interval) = box at h2 ⊢
  -- back through the basis, into the conZonotope and its cut
  have h3 := Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B box.zonotope
    (Set.mem_biUnion rfl (Set.mem_image_of_mem (fun v => Scalar.toRealMat B *ᵥ v)
      (Interval.zonotope_contains _ h2)))
  have h4 := Location.orthDefectFloat_mem B _ _ (Location.joinedBoxFloat_contains R₀ Rs hR hx) h3
  have h5 := ConZonotope.intersection_outer _ guard ⟨Zonotope.conZonotope_contains _ h4, hg⟩
  generalize ConZonotope.intersection
    (Zonotope.conZonotope (Location.orthDefectFloat B (Location.joinedBoxFloat R₀ Rs)
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B
    box.zonotope))) guard = cZ at h5 ⊢
  -- boxed again in the basis
  have h6 : Scalar.toRealMat Bᵀ *ᵥ x ∈
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := fun k => ConZonotope 𝕋 (Vec 𝕋 k)) Bᵀ cZ).toSet :=
    Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (ContSet := fun k => ConZonotope 𝕋 (Vec 𝕋 k)) Bᵀ cZ
      (Set.mem_biUnion rfl (Set.mem_image_of_mem _ h5))
  have h7 := Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (ContSet := fun k => ConZonotope 𝕋 (Vec 𝕋 k)) Bᵀ
      cZ).interval.zonotope
    (Set.mem_biUnion rfl (Set.mem_image_of_mem (fun v => Scalar.toRealMat B *ᵥ v)
      (Interval.zonotope_contains _ (ConZonotope.interval_contains _ h6))))
  exact Location.orthDefectFloat_mem B _ _ (Location.joinedBoxFloat_contains R₀ Rs hR hx) h7

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
