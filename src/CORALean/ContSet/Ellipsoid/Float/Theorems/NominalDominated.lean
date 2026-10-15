module

public import CORALean.ContSet.Ellipsoid.Float.Theorems.NominalQEq

@[expose] public section

/-!
# The stored shape matrix dominates the nominal one

`Q - nominal Q` is `0` where `Q` is positive semi-definite, and the nominal shape is `0` where it
is not: the condition of `add_sub_mem_nominalSet` for an operation that keeps `Q`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A stored `Q` dominates its own nominal shape, or that shape is `0`: the condition of
`add_sub_mem_nominalSet` for an operation that keeps `Q`. -/
theorem Ellipsoid.nominal_dominated [SoundFloatArithmetic 𝕋] (E : Ellipsoid 𝕋 n) :
    (InflatedContSet.nominal E).ellipsoid.Q = 0
      ∨ (toRealMat E.Q - (InflatedContSet.nominal E).ellipsoid.Q).PosSemidef := by
  rw [Ellipsoid.nominal_Q_eq]
  split_ifs
  · exact Or.inr (by rw [sub_self]; exact .zero)
  · exact Or.inl rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
