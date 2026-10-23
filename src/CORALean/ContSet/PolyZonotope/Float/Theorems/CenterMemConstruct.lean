module

public import CORALean.ContSet.ConPolyZono.Real.Theorems.MonomialEqZeroOfNoZeroCol
public import CORALean.ContSet.ConPolyZono.Real.Operations.NoZeroCol
public import CORALean.ContSet.PolyZonotope.Float.Operations.Basic
public import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet

@[expose] public section

/-!
# The stored center is a point of the polynomial zonotope

CORA's `center` returns the field `c`. The stored center, read as reals, lies in the
nominal part at the zero factors and zero independent coefficients once no exponent column is
zero, so that every monomial vanishes there, and in the whole set once the error box holds
`0`, which a box built by the operations does and an arbitrary one need not.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* `hE` – no exponent column is zero
* `h0` – error box contains zero

## Conclusion
* the stored center lies in the set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.center_mem_construct (pZ : PolyZonotope (Vec 𝕋 n))
    (hE : Real.ConPolyZono.NoZeroCol pZ.E)
    (h0 : ∀ i, toReal (pZ.I_error.inf i) ≤ 0 ∧ 0 ≤ toReal (pZ.I_error.sup i)) :
    toRealVec pZ.center ∈ pZ.construct := by
  refine ⟨toRealVec pZ.center, PolyZonotope.mem_nominalSet_iff.mpr
    ⟨fun _ => 0, fun _ => 0, fun k => by simp, fun j => by simp, fun i => ?_⟩, 0, h0, add_zero _⟩
  simp [Real.ConPolyZono.monomial_eq_zero_of_noZeroCol hE (fun _ => rfl), toRealVec,
    PolyZonotope.center]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
