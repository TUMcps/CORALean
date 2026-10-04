import CORALean.ContSet.PolyZonotope.Real.Operations.SubsPow
import CORALean.ContSet.PolyZonotope.Real.Operations.SubsPoly

/-!
# `PolyZonotope.subsXprod`

CORA's `Xprod` of generator `i`: what its monomial in the replaced factors becomes, the product over
the outputs `ii` of `Y{ii, e}`, the `e`-th power of output `ii`'s polynomial, `e` the exponent of
factor `idu ii` in the generator.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The terms generator `i`'s monomial in the replaced factors expands to. -/
noncomputable def PolyZonotope.subsXprod (pZ : PolyZonotope α) {nu : ℕ}
    (pZin : PolyZonotope (Vec ℝ nu)) (idu : Fin nu → Fin pZ.p) (i : Fin pZ.h) :
    List (ℝ × (Fin pZin.p → ℕ)) :=
  -- `Y`: the powers of the outputs
  let Y : Fin nu → ℕ → List (ℝ × (Fin pZin.p → ℕ)) :=
    fun ii d => PolyZonotope.subsPow (pZin.subsPoly ii) d
  -- the product over the outputs
  (List.finRange nu).foldl (fun acc ii => PolyZonotope.subsMul acc (Y ii (pZ.E (idu ii) i)))
    [(1, 0)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
