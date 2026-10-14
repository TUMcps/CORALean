module

public import CORALean.ContSet.Ellipsoid.Float.Theorems.MemNominalSet
public import CORALean.Global.Float.EuclideanNorm

@[expose] public section

/-!
# An ellipsoid as a box, over a floating-point scalar

The centre give or take a row length, each end rounded away from the ellipsoid,
plus what the error box already held.

The row length is where the square root would have been, and this is the
conversion that shows it costs nothing: in a *coordinate* direction the pulled
back direction is a stored row of `G` outright, exactly representable, so the
certificate is one proposed length per coordinate checked against
`sqSumUp (|Gᵢ·|)` and no rounding enters the pullback at all. The same length
serves both faces, `‖-Gᵢ·‖₂ = ‖Gᵢ·‖₂`, which is why `s` is a vector of `n` and
not of `2n`.

Not through `Interval.ofBounds` and `Ellipsoid.boundDot`, which would answer an
arbitrary direction and then have to be told that a coordinate projection is
one: at a coordinate the whole apparatus reduces to Cauchy–Schwarz against a row
already in hand. Tight only up to the certificate: over ℝ the box touches the
ellipsoid on every face, here it touches whatever `s` was worth.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The box, given one proposed length per coordinate. -/
def Ellipsoid.interval (E : Ellipsoid 𝕋 n) (s : Vec 𝕋 n) : Interval (Vec 𝕋 n) where
  inf := fun i => addDown (subDown (E.c i) (absolute (s i))) (E.I_error.inf i)
  sup := fun i => addUp (addUp (E.c i) (absolute (s i))) (E.I_error.sup i)

open SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What a certified length buys: the whole `i`-th row reaches no further over
the unit ball. -/
theorem Ellipsoid.aux_row_le (E : Ellipsoid 𝕋 n) (s : Vec 𝕋 n)
    (hs : ∀ i, toReal (sqSumUp fun j => absolute (E.G i j))
      ≤ toReal (mulDown (s i) (s i)))
    {u : Vec ℝ E.k} (hu : ‖u‖₂ ≤ 1) (i : Fin n) :
    |∑ j, toReal (E.G i j) * u j| ≤ toReal (absolute (s i)) := by -- --- PROOF ---
  have hrow : ‖(fun j => toReal (E.G i j) : Vec ℝ E.k)‖₂ ≤ toReal (absolute (s i)) :=
    norm₂_le_of_sq_le (fun j => le_of_eq (toReal_absolute (E.G i j)).symm) (hs i)
  have h0 : (0:ℝ) ≤ toReal (absolute (s i)) := le_trans (norm₂_nonneg _) hrow
  calc |∑ j, toReal (E.G i j) * u j|
      ≤ ‖(fun j => toReal (E.G i j) : Vec ℝ E.k)‖₂ * ‖u‖₂ :=
        abs_dotProduct_le_norm₂_mul_norm₂ _ _
    _ ≤ toReal (absolute (s i)) * 1 := mul_le_mul hrow hu (norm₂_nonneg u) h0
    _ = toReal (absolute (s i)) := mul_one _


-- =======================================  MAIN THEOREM  ======================================= --

-- the box is that reach around the centre, with the error box added on
theorem Ellipsoid.interval_contains (E : Ellipsoid 𝕋 n) (s : Vec 𝕋 n)
    (hs : ∀ i, toReal (sqSumUp fun j => absolute (E.G i j))
      ≤ toReal (mulDown (s i) (s i))) :
    E.construct ⊆ (E.interval s).construct := by -- --- PROOF ---
  rintro _ ⟨z, hzmem, e, he, rfl⟩ i
  obtain ⟨u, hu, hz⟩ := Ellipsoid.mem_nominalSet_iff.mp hzmem
  have hrow := E.aux_row_le s hs hu i
  have hlo : toReal (E.I_error.inf i) ≤ e i := (he i).1
  have hhi : e i ≤ toReal (E.I_error.sup i) := (he i).2
  have hzi : z i = toReal (E.c i) + ∑ j, toReal (E.G i j) * u j := hz i
  -- each face on its own, the two roundings going opposite ways
  constructor
  · have h1 := addDown_le_add (subDown (E.c i) (absolute (s i))) (E.I_error.inf i)
    have h2 := subDown_le_sub (E.c i) (absolute (s i))
    have h3 := neg_le_of_abs_le hrow
    show toReal (addDown (subDown (E.c i) (absolute (s i))) (E.I_error.inf i)) ≤ z i + e i
    rw [hzi]
    linarith
  · have h1 := add_le_addUp (addUp (E.c i) (absolute (s i))) (E.I_error.sup i)
    have h2 := add_le_addUp (E.c i) (absolute (s i))
    have h3 := le_of_abs_le hrow
    show z i + e i ≤ toReal (addUp (addUp (E.c i) (absolute (s i))) (E.I_error.sup i))
    rw [hzi]
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
