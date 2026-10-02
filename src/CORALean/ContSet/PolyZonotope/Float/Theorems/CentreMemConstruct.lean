import CORALean.ContSet.ConPolyZono.Real.Operations.MonomialEqZeroOfNoZeroCol
import CORALean.ContSet.ConPolyZono.Real.Operations.NoZeroCol
import CORALean.ContSet.PolyZonotope.Float.Operations.Centre
import CORALean.ContSet.PolyZonotope.Float.Theorems.MemNominalSet

/-!
# The stored centre is a point of the polynomial zonotope

CORA's `center` returns the field `c`. The stored centre, read as reals, lies in the
nominal part at the zero factors and zero independent coefficients once no exponent column is
zero, so that every monomial vanishes there, and in the whole set once the error box holds
`0`, which a box built by the operations does and an arbitrary one need not.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.centre_mem_construct (pZ : PolyZonotope 𝕋 n)
    (hE : Real.ConPolyZono.NoZeroCol pZ.E)
    (h0 : ∀ i, toReal (pZ.err.inf i) ≤ 0 ∧ 0 ≤ toReal (pZ.err.sup i)) :
    toRealVec pZ.centre ∈ pZ.construct := by
  refine ⟨toRealVec pZ.centre, PolyZonotope.mem_nominalSet_iff.mpr
    ⟨fun _ => 0, fun _ => 0, fun k => by simp, fun j => by simp, fun i => ?_⟩, 0, h0, add_zero _⟩
  simp [Real.ConPolyZono.monomial_eq_zero_of_noZeroCol hE (fun _ => rfl), toRealVec,
    PolyZonotope.centre]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
