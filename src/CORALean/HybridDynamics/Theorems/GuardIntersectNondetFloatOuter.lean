module

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
the bundle. Each member is a box in an orthogonal basis, which is why the bases are required to
satisfy `B Bᵀ = 1` over ℝ: `B (Bᵀ x) = x` carries the state through the basis and back.
Outer only: every step over-approximates.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A state in a reach set and in the guard lies in the bundle, for orthogonal bases. -/
theorem Location.guardIntersectNondetFloat_outer (Bs : List (Mat 𝕋 n n)) (R₀ : Zonotope (Vec 𝕋 n))
    (Rs : List (Zonotope (Vec 𝕋 n))) (guard : ConZonotope 𝕋 (Vec 𝕋 n))
    (horth : ∀ B ∈ Bs, Scalar.toRealMat B * (Scalar.toRealMat B)ᵀ = 1)
    {R : Zonotope (Vec 𝕋 n)} (hR : R ∈ R₀ :: Rs) {x : Vec ℝ n} (hx : x ∈ R.construct)
    (hg : x ∈ guard.construct) : -- --- CONCL ---
    x ∈ (Location.guardIntersectNondetFloat Bs R₀ Rs guard).construct := by -- --- PROOF ---
  -- a point of the start or of any box folded in is a point of the hull
  have hfold : ∀ (Is : List (Interval (Vec 𝕋 n))) (J : Interval (Vec 𝕋 n)) (y : Vec ℝ n),
      (y ∈ J.construct ∨ ∃ I ∈ Is, y ∈ I.construct) → y ∈ (Is.foldl Interval.or J).construct := by
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
  refine SetIntersection.mem_construct_ofFn.mpr fun i => ?_
  have hB := horth Bs[i] (List.getElem_mem i.isLt)
  unfold Location.guardIntersectNondetFloat
  dsimp only
  generalize Bs[i] = B at hB
  -- the basis maps back: `B (Bᵀ y) = y`, and `Bᵀ` reads as the transpose
  have hT : Scalar.toRealMat Bᵀ = (Scalar.toRealMat B)ᵀ := by
    ext a b
    simp [Scalar.toRealMat_apply]
  have hBB : ∀ y : Vec ℝ n, Scalar.toRealMat B *ᵥ (Scalar.toRealMat Bᵀ *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hT, hB, Matrix.one_mulVec]
  -- the state boxed in the basis
  have h1 : Scalar.toRealMat Bᵀ *ᵥ x ∈
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) Bᵀ R).construct :=
    Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) Bᵀ R
      (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hx))
  have h2 := hfold (Rs.map
    fun R => (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) Bᵀ R).interval)
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) Bᵀ R₀).interval
      (Scalar.toRealMat Bᵀ *ᵥ x) (by
      rcases List.mem_cons.mp hR with rfl | hR'
      · exact Or.inl (Zonotope.interval_contains _ h1)
      · exact Or.inr ⟨_, List.mem_map.mpr ⟨R, hR', rfl⟩, Zonotope.interval_contains _ h1⟩)
  generalize List.foldl Interval.or
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) Bᵀ R₀).interval
    (Rs.map fun R => (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) Bᵀ
      R).interval) = box at h2 ⊢
  -- back through the basis, into the conZonotope and its cut
  have h3 := Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) B box.zonotope
    (Set.mem_biUnion rfl (Set.mem_image_of_mem (fun v => Scalar.toRealMat B *ᵥ v)
      (Interval.zonotope_contains _ h2)))
  rw [hBB] at h3
  have h5 := ConZonotope.intersection_outer _ guard ⟨Zonotope.conZonotope_contains _ h3, hg⟩
  generalize ConZonotope.intersection
    (Zonotope.conZonotope (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) B
    box.zonotope)) guard = cZ at h5 ⊢
  -- boxed again in the basis
  have h6 : Scalar.toRealMat Bᵀ *ᵥ x ∈
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => ConZonotope 𝕋 (Vec 𝕋 k)) Bᵀ cZ).construct :=
    Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (S := fun k => ConZonotope 𝕋 (Vec 𝕋 k)) Bᵀ cZ
      (Set.mem_biUnion rfl (Set.mem_image_of_mem _ h5))
  have h7 := Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) B
    (Mtimes.mtimes (𝕄 := Mat 𝕋) (S := fun k => ConZonotope 𝕋 (Vec 𝕋 k)) Bᵀ cZ).interval.zonotope
    (Set.mem_biUnion rfl (Set.mem_image_of_mem (fun v => Scalar.toRealMat B *ᵥ v)
      (Interval.zonotope_contains _ (ConZonotope.interval_contains _ h6))))
  rwa [hBB] at h7

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
