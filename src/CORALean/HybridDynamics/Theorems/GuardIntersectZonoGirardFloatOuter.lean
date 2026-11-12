module

public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.HybridDynamics.Operations.GuardIntersectZonoGirardFloat
public import CORALean.HybridDynamics.Theorems.ZonoGirardBoxFloatMem
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

## Inputs
* `Bs` – bases
* `R₀` – initial set
* `Rs` – reach sets
* `nv` – guard normal
* `γ` – guard offset
* `R` – reach set
* `x` – trajectory of the stay

## Hypotheses
* `horth` – bases orthogonal
* `hR` – the reach set is among the given ones
* `hx` – state lies in the reach set
* `hg` – state lies on the guard

## Conclusion
* state lies in the bundle
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
    {R : Zonotope (Vec 𝕋 n)} (hR : R ∈ R₀ :: Rs) {x : Vec ℝ n} (hx : x ∈ R.toSet)
    (hg : x ⬝ᵥ toRealVec nv = toReal γ) : -- --- CONCL ---
    x ∈ (Location.guardIntersectZonoGirardFloat Bs R₀ Rs nv γ).toSet := by -- --- PROOF ---
  -- member `i` of the bundle, whose basis is orthogonal
  refine SetIntersection.mem_toSet_ofFn.mpr fun i => ?_
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
  -- the state's coordinates are in the joined box
  have h2 := Location.zonoGirardBoxFloat_mem B R₀ Rs nv γ hR hx hg
  generalize Location.zonoGirardBoxFloat B R₀ Rs nv γ = box at h2 ⊢
  -- and back through the basis
  have h3 := Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B box.zonotope
    (Set.mem_biUnion rfl (Set.mem_image_of_mem (fun v => Scalar.toRealMat B *ᵥ v)
      (Interval.zonotope_contains _ h2)))
  rwa [hBB] at h3

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
