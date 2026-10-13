import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# `ϑ`-uniformly distributed random variables

`[1, Def. 4.1]`: a random variable `v ∈ K` is `ϑ`-uniformly distributed on `K` if
`|P(v ∈ S) - vol(S) / vol(K)| ≤ ϑ` for every measurable `S ⊆ K`. What the ball walk
delivers, and what `[1, Thm. 4.2]` assumes of its samples. `vol` is any measure on the
space; the theorem takes it to be a Haar measure.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open MeasureTheory


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `v` takes values in `K` and hits each measurable `S ⊆ K` with probability within `ϑ` of
its volume fraction, `[1, Def. 4.1]`. -/
def IsThetaUniform {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω)
    (v : Ω → E) (vol : Measure E) (K : Set E) (ϑ : ℝ) : Prop :=
  (∀ ω, v ω ∈ K) ∧ ∀ S ⊆ K, MeasurableSet S →
    |(P (v ⁻¹' S)).toReal - (vol S).toReal / (vol K).toReal| ≤ ϑ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
