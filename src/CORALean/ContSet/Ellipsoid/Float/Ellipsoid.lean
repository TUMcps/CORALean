import CORALean.ContSet.Ellipsoid.Real.Instances
import CORALean.ContSet.InflatedContSet.InflatedContSet

/-!
# Ellipsoids over a floating-point scalar: the representation

The exact layer's centre and generator matrix held in `𝕋`, plus the error box
that makes it an `InflatedContSet`. Storing the generator matrix rather than
CORA's shape matrix pays here as it does over ℝ, and more: a shape matrix would
have to come back through a matrix square root, and this layer has no square
root of any kind.

No generator transpose, unlike the zonotope and the polynomial zonotope: the
exact `Ellipsoid` already stores `G` as a matrix, so the nominal part is the two
stored arrays read entrywise as reals.

What ranges over the unit ball is `u`, not a free coefficient — which changes
nothing about the rounding. `‖u‖₂ ≤ 1` gives `|uⱼ| ≤ 1`, so a rounded generator
costs exactly what a zonotope's does; `Theorems/MemGeneratorError` says why the
tighter bound is the one worth not taking.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

structure Ellipsoid (𝕋 : Type) (n : ℕ) where
  /-- The generator count, as over ℝ: `G` is `n × k` and need not be square. -/
  k : ℕ
  q : Vec 𝕋 n
  G : Mat 𝕋 n k
  /-- The error box. Named `err` rather than `E`, which reads as an exponent
  matrix nowhere here but as the exact layer's ellipsoid everywhere. -/
  err : Interval 𝕋 n

instance [SoundFloatArithmetic 𝕋] :
    InflatedContSet (Ellipsoid 𝕋 n) (CORALean.Real.Ellipsoid n) 𝕋 n where
  nominal E := ⟨E.k, toRealVec E.q, toRealMat E.G⟩
  error E := E.err

/-! The nominal ellipsoid's fields, so proofs can see through the instance. -/

theorem Ellipsoid.nominal_k [SoundFloatArithmetic 𝕋] (E : Ellipsoid 𝕋 n) :
    (InflatedContSet.nominal E).k = E.k := rfl

theorem Ellipsoid.nominal_q [SoundFloatArithmetic 𝕋] (E : Ellipsoid 𝕋 n) :
    (InflatedContSet.nominal E).q = toRealVec E.q := rfl

theorem Ellipsoid.nominal_G [SoundFloatArithmetic 𝕋] (E : Ellipsoid 𝕋 n) :
    (InflatedContSet.nominal E).G = toRealMat E.G := rfl

/-- The nominal set spelt in this ellipsoid's own fields, coordinatewise.
Definitional, and the reason proofs never mention `nominal`: through it the
generator count is `(nominal E).k`, which `rw` and `linarith` read as a term
distinct from the equal `E.k`. -/
theorem Ellipsoid.mem_nominalSet_iff [SoundFloatArithmetic 𝕋] {E : Ellipsoid 𝕋 n}
    {x : Vec ℝ n} :
    x ∈ InflatedContSet.nominalSet E ↔ ∃ u : Vec ℝ E.k, ‖u‖₂ ≤ 1 ∧
      ∀ i, x i = toReal (E.q i) + ∑ j, toReal (E.G i j) * u j := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, fun _ => rfl⟩
  · rintro ⟨u, hu, hx⟩
    exact ⟨u, hu, funext hx⟩

/-- Inherited from `InflatedContSet`; named here so statements read locally. -/
abbrev Ellipsoid.construct [SoundFloatArithmetic 𝕋] (E : Ellipsoid 𝕋 n) : Set (Vec ℝ n) :=
  InflatedContSet.construct E

end CORALean.Float
