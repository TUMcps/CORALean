import CORALean.ContSet.Interval.Float.Interval

/-!
# `PolyZonotope.sliceBox`

The box `X_` with the coordinates `ind` replaced by the box `U`: CORA's
`X_modified = X_; X_modified(ind) = cartProd(U1_, U2_)` in `aux_InnerGeneral` and
`aux_containsInterval`, on which the Jacobian is re-evaluated after each domain inflation of
`U1_`. The coordinates not in `ind` keep `X_`'s bounds, which is `U2_` in CORA's split.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `X₀` with coordinate `ind i` replaced by `U`'s coordinate `i`. -/
def PolyZonotope.sliceBox (X₀ : Interval (Vec 𝕋 p)) (ind : Fin n → Fin p)
    (U : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 p) :=
  -- which coordinate of `U`, if any, sits at `k`
  let pick : Fin p → Option (Fin n) := fun k => (List.finRange n).find? fun i => decide (ind i = k)
  ⟨fun k => match pick k with | some i => U.inf i | none => X₀.inf k,
   fun k => match pick k with | some i => U.sup i | none => X₀.sup k⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
