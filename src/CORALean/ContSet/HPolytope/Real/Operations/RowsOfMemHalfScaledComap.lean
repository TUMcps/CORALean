module

public import CORALean.ContSet.HPolytope.Real.Operations.Comap
public import CORALean.ContSet.HPolytope.Real.Operations.MemHalfScaledIff

@[expose] public section

/-!
# The weighted rows a scaled membership gives back

The converse reading of `mem_halfScaled_comap`: a point of the weighted
preimage satisfies `P`'s own rows against the weight, which is where a proof
that the combination is *no larger* than the hull starts. It stops at the rows
rather than going on to a member of `P`, since at weight zero there is nothing
to divide by.

## Inputs
* `f` – `γ →ₗ[ℝ] α`
* `t` – `γ →ₗ[ℝ] ℝ`
* `P` – H-polytope
* `x` – `γ`
* `w` – real number

## Hypotheses
* `hw` – `w` is the weight `(t x + 1) / 2`
* `hx` – `x` lies in `((P.comap f).halfScaled t)`

## Conclusion
* the weighted rows a scaled membership gives back
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α γ : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup γ] [Module ℝ γ]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.rows_of_mem_halfScaled_comap {f : γ →ₗ[ℝ] α} {t : γ →ₗ[ℝ] ℝ}
    {P : HPolytope α} {x : γ} {w : ℝ} (hw : (t x + 1) / 2 = w)
    (hx : x ∈ ((P.comap f).halfScaled t).construct) :
    (∀ i, P.A i (f x) ≤ w * P.b i) ∧ ∀ i, P.Ae i (f x) = w * P.be i := by
  obtain ⟨hle, heq⟩ := HPolytope.mem_halfScaled_iff.mp hx
  rw [hw] at hle heq
  exact ⟨hle, heq⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
