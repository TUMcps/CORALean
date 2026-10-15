module

public import CORALean.HybridDynamics.Operations.GuardIntersectZonoGirardFloat
public import CORALean.HybridDynamics.Theorems.ZonoGirardUpperFloatLe
public import CORALean.ContSet.Interval.Float.Theorems.OrOuter
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `Location.guardIntersectZonoGirardFloat` holds every state that meets the guard

A state `x` of a reach set on the hyperplane has `x·ℓ` between the ends of that set's cut along
each column `ℓ` of a basis (`zonoGirardUpperFloat_le` in the directions `ℓ` and `-ℓ`), so in the
joined interval, so in every member of the bundle: the basis, with `B Bᵀ = 1` over ℝ, carries
`x` through its coordinates `Bᵀ x` and back. Outer only.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps CORALean.Float.SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A state in a reach set and on the hyperplane lies in the bundle, for orthogonal bases. -/
theorem Location.guardIntersectZonoGirardFloat_outer (Bs : List (Mat 𝕋 n n))
    (R₀ : Zonotope (Vec 𝕋 n))
    (Rs : List (Zonotope (Vec 𝕋 n))) (nv : Vec 𝕋 n) (γ : 𝕋)
    (horth : ∀ B ∈ Bs, Scalar.toRealMat B * (Scalar.toRealMat B)ᵀ = 1)
    {R : Zonotope (Vec 𝕋 n)} (hR : R ∈ R₀ :: Rs) {x : Vec ℝ n} (hx : x ∈ R.construct)
    (hg : x ⬝ᵥ toRealVec nv = toReal γ) :
    x ∈ (Location.guardIntersectZonoGirardFloat Bs R₀ Rs nv γ).construct := by -- --- PROOF ---
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
  -- member `i` of the bundle, whose basis is orthogonal
  refine Set.mem_iInter.mpr fun i => ?_
  have hB : Scalar.toRealMat Bs[i] * (Scalar.toRealMat Bs[i])ᵀ = 1 :=
    horth _ (List.getElem_mem i.isLt)
  unfold Location.guardIntersectZonoGirardFloat
  dsimp only
  generalize Bs[i] = B at hB
  -- the basis maps back: `B (Bᵀ y) = y`
  have hT : Scalar.toRealMat Bᵀ = (Scalar.toRealMat B)ᵀ := by
    ext a b
    simp [Scalar.toRealMat_apply]
  have hBB : ∀ y : Vec ℝ n, Scalar.toRealMat B *ᵥ (Scalar.toRealMat Bᵀ *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hT, hB, Matrix.one_mulVec]
  -- the state's coordinates lie in the cut of a set holding it
  have hcut : ∀ R' : Zonotope (Vec 𝕋 n), x ∈ R'.construct →
      Scalar.toRealMat Bᵀ *ᵥ x ∈ (⟨fun k => neg (Location.zonoGirardUpperFloat R' nv γ
          (-(Bᵀ k))),
        fun k => Location.zonoGirardUpperFloat R' nv γ (Bᵀ k)⟩ : Interval (Vec 𝕋 n)).construct :=
    fun R' hx' => by
    -- the coordinate `k` of `Bᵀ x` is `x·ℓ` for the column `ℓ` of `B`
    intro k
    have hk : (Scalar.toRealMat Bᵀ *ᵥ x) k = x ⬝ᵥ toRealVec (Bᵀ k) := by
      rw [Matrix.mulVec, dotProduct_comm]
      rfl
    have hu := Location.zonoGirardUpperFloat_le R' nv γ (Bᵀ k) hx' hg
    have hl := Location.zonoGirardUpperFloat_le R' nv γ (-(Bᵀ k)) hx' hg
    have hneg : toRealVec (-(Bᵀ k)) = -toRealVec (Bᵀ k) := toRealVec_neg _
    -- the lower end is the upper end of `-ℓ`, negated
    rw [hneg, dotProduct_neg] at hl
    refine ⟨?_, ?_⟩
    · -- the lower end
      show toReal (neg (Location.zonoGirardUpperFloat R' nv γ (-(Bᵀ k)))) ≤
        (Scalar.toRealMat Bᵀ *ᵥ x) k
      rw [toReal_neg, hk]
      linarith
    · -- the upper end
      show (Scalar.toRealMat Bᵀ *ᵥ x) k ≤ toReal (Location.zonoGirardUpperFloat R' nv γ (Bᵀ k))
      rw [hk]
      exact hu
  -- the state is in the joined interval
  have h2 := hfold (Rs.map fun R' => (⟨fun k => neg (Location.zonoGirardUpperFloat R' nv γ
          (-(Bᵀ k))),
        fun k => Location.zonoGirardUpperFloat R' nv γ (Bᵀ k)⟩ : Interval (Vec 𝕋 n)))
    ⟨fun k => neg (Location.zonoGirardUpperFloat R₀ nv γ (-(Bᵀ k))),
        fun k => Location.zonoGirardUpperFloat R₀ nv γ (Bᵀ k)⟩
    (Scalar.toRealMat Bᵀ *ᵥ x) (by
      rcases List.mem_cons.mp hR with rfl | hR'
      · exact Or.inl (hcut _ hx)
      · exact Or.inr ⟨_, List.mem_map.mpr ⟨R, hR', rfl⟩, hcut _ hx⟩)
  generalize List.foldl Interval.or
    (⟨fun k => neg (Location.zonoGirardUpperFloat R₀ nv γ (-(Bᵀ k))),
        fun k => Location.zonoGirardUpperFloat R₀ nv γ (Bᵀ k)⟩ : Interval (Vec 𝕋 n))
    (Rs.map fun R' => (⟨fun k => neg (Location.zonoGirardUpperFloat R' nv γ
          (-(Bᵀ k))),
        fun k => Location.zonoGirardUpperFloat R' nv γ (Bᵀ k)⟩ : Interval (Vec 𝕋 n))) = box
    at h2 ⊢
  -- and back through the basis
  have h3 := Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (S := 𝒵[𝕋]) B box.zonotope
    (Set.mem_biUnion rfl (Set.mem_image_of_mem (fun v => Scalar.toRealMat B *ᵥ v)
      (Interval.zonotope_contains _ h2)))
  rwa [hBB] at h3

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
