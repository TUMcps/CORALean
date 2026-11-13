module

public import CORALean.ContSet.SetIntersection.Theorems.Basic
public import CORALean.HybridDynamics.Operations.GuardIntersectZonoGirardFloat
public import CORALean.HybridDynamics.Theorems.ZonoGirardMemberFloatMem
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Theorems.IntervalZonotopeContains
public import CORALean.ContSet.Conversion.Real.Theorems.IntervalZonotopeContains

@[expose] public section

/-!
# `Location.guardIntersectZonoGirardFloat` holds every state that meets the guard

A state `x` of a reach set on the hyperplane has `x·ℓ` between the ends of that set's cut along
each column `ℓ` of a basis (`zonoGirardUpperFloat_le` in the directions `ℓ` and `-ℓ`), so in the
joined interval, so in every member of the bundle: `zonoGirardMemberFloat_mem`, for any basis, not
only an orthogonal one. Outer only.

## Inputs
* `Bs` – bases
* `R₀` – initial set
* `Rs` – reach sets
* `nv` – guard normal
* `γ` – guard offset
* `R` – reach set
* `x` – trajectory of the stay

## Hypotheses
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

/-- A state in a reach set and on the hyperplane lies in the bundle, for any bases. -/
theorem Location.guardIntersectZonoGirardFloat_outer (Bs : List (Mat 𝕋 n n))
    (R₀ : Zonotope (Vec 𝕋 n))
    (Rs : List (Zonotope (Vec 𝕋 n))) (nv : Vec 𝕋 n) (γ : 𝕋)
    {R : Zonotope (Vec 𝕋 n)} (hR : R ∈ R₀ :: Rs) {x : Vec ℝ n} (hx : x ∈ R.toSet)
    (hg : x ⬝ᵥ toRealVec nv = toReal γ) : -- --- CONCL ---
    x ∈ (Location.guardIntersectZonoGirardFloat Bs R₀ Rs nv γ).toSet := by -- --- PROOF ---
  -- member `i` of the bundle
  refine SetIntersection.mem_toSet_ofFn.mpr fun i => ?_
  exact Location.zonoGirardMemberFloat_mem Bs[i] R₀ Rs nv γ hR hx hg

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
