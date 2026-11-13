module

public import CORALean.HybridDynamics.Operations.ZonoGirardMemberFloat
public import CORALean.HybridDynamics.Theorems.ZonoGirardBoxFloatMem
public import CORALean.HybridDynamics.Theorems.OrthDefectFloatMem
public import CORALean.HybridDynamics.Theorems.JoinedBoxFloatContains
public import CORALean.ContSet.Interval.Float.Theorems.Basic
public import CORALean.ContSet.Zonotope.Float.Theorems.PlusOuter
public import CORALean.ContSet.Zonotope.Float.Theorems.MtimesOuter
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Float.Theorems.ZonotopeIntervalContains
public import CORALean.ContSet.Interval.Float.Theorems.OrOuter

@[expose] public section

/-!
# `Location.zonoGirardMemberFloat` holds every state that meets the guard, for any basis

A state `x` of a reach set on the hyperplane is `B (Bᵀ x) + (I - B Bᵀ) x`, for any real matrix
`B`. The first term is in `B zonotope(I)` (`zonoGirardBoxFloat_mem`), the second in the box
`[-r, r]` (the defect box holds `I - B Bᵀ`, the joined boxes of the reach sets hold `x`). Where the
defect box is the zero matrix the second term is zero. No orthogonality is assumed.

## Inputs
* `B` – basis
* `R₀` – initial zonotope
* `Rs` – reach sets
* `nv` – guard normal
* `γ` – guard offset
* `R` – reach set
* `x` – state

## Hypotheses
* `hR` – the reach set is among the given ones
* `hx` – state lies in the reach set
* `hg` – state lies on the guard

## Conclusion
* state lies in the member
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float CORALean.Float.FloatOps CORALean.Float.SoundFloatArithmetic Matrix

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A state in a reach set and on the hyperplane lies in the member, for every basis. -/
theorem Location.zonoGirardMemberFloat_mem (B : Mat 𝕋 n n) (R₀ : Zonotope (Vec 𝕋 n))
    (Rs : List (Zonotope (Vec 𝕋 n))) (nv : Vec 𝕋 n) (γ : 𝕋)
    {R : Zonotope (Vec 𝕋 n)} (hR : R ∈ R₀ :: Rs) {x : Vec ℝ n} (hx : x ∈ R.toSet)
    (hg : x ⬝ᵥ toRealVec nv = toReal γ) : -- --- CONCL ---
    x ∈ (Location.zonoGirardMemberFloat B R₀ Rs nv γ).toSet := by -- --- PROOF ---
  -- `B (Bᵀ x)` is in `B zonotope(I)`
  have h2 := Location.zonoGirardBoxFloat_mem B R₀ Rs nv γ hR hx hg
  exact Location.orthDefectFloat_mem B _ _ (Location.joinedBoxFloat_contains R₀ Rs hR hx)
    (Mtimes.mtimes_outer (𝕄 := Mat 𝕋) (ContSet := 𝒵[𝕋]) B _
      (Set.mem_biUnion rfl (Set.mem_image_of_mem (fun v => Scalar.toRealMat B *ᵥ v)
        (Interval.zonotope_contains _ h2))))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
