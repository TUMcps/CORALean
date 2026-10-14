module

public import CORALean.ContSet.ConPolyZono.Real.Theorems.CentreMemConstruct
public import CORALean.ContSet.ConPolyZono.Float.Operations.Basic

@[expose] public section

/-!
# The stored centre is a point of the constrained polynomial zonotope

CORA's `center` returns the field `c` with no guarantee. Read as reals it is the nominal part's
centre, which the exact layer's `centre_mem_construct` places in the nominal set when no
exponent column of `E` or `EC` is zero and `0` lies in the constraint interval; it is then in
the whole set once the error box holds `0`, which a box built by the operations does and an
arbitrary one need not.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.centre_mem_construct (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n))
    (hE : Real.ConPolyZono.NoZeroCol cPZ.E) (hEC : Real.ConPolyZono.NoZeroCol cPZ.EC)
    (hb : ∀ i, toReal (cPZ.b.inf i) ≤ 0 ∧ 0 ≤ toReal (cPZ.b.sup i))
    (h0 : ∀ i, toReal (cPZ.I_error.inf i) ≤ 0 ∧ 0 ≤ toReal (cPZ.I_error.sup i)) :
    toRealVec cPZ.centre ∈ cPZ.construct := by
  -- the nominal part holds its own centre, which is the stored one read as reals
  have hN : toRealVec cPZ.centre ∈ InflatedContSet.nominalSet cPZ :=
    Real.ConPolyZono.centre_mem_construct (InflatedContSet.nominal cPZ) hE hEC hb
  exact ⟨_, hN, 0, h0, add_zero _⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
