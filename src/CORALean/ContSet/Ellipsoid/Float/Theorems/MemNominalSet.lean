import CORALean.ContSet.Ellipsoid.Float.Ellipsoid

/-!
# Membership in the nominal ellipsoid, in the stored fields

The form every enclosure proof at this layer reads the nominal half of a point
in: the ball coefficient `u` kept as it is, and the stored centre and generator
entries put through `toReal`, coordinate by coordinate.

Proofs use it rather than going through `nominal` because through it the count
is `E.k`, where the instance gives the equal-but-distinct `(nominal E).k` that
`rw` and `linarith` read apart.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.mem_nominalSet_iff [SoundFloatArithmetic 𝕋] {E : Ellipsoid 𝕋 n}
    {x : Vec ℝ n} :
    x ∈ InflatedContSet.nominalSet E ↔ ∃ u : Vec ℝ E.k, ‖u‖₂ ≤ 1 ∧
      ∀ i, x i = toReal (E.q i) + ∑ j, toReal (E.G i j) * u j := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, fun _ => rfl⟩
  -- back, the pointwise equalities collected into one by `funext`
  · rintro ⟨u, hu, hx⟩
    exact ⟨u, hu, funext hx⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
