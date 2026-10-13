import CORALean.ContSet.HPolytope.Real.Operations.MinkDiffOf
import Mathlib.Tactic.Linarith

/-!
# The certified halfspace difference is an inner approximation

`hker` says `T` lies in the kernel of every equality direction: the case a
caller actually has, a disturbance that does not move the state along a
constrained direction. It is not a hypothesis to weaken — without it no `x` at
all satisfies the difference along an equality row, so there is nothing weaker
to assume, and the right answer is not to silently return `∅`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.minkDiffOf_inner (P : HPolytope α) (T : Set α)
    (u : ∀ i, SupportBound T (P.A i)) (hker : ∀ i, ∀ y ∈ T, P.Ae i y = 0) :
    (P.minkDiffOf T u).construct ⊆ minkowskiDiff P.construct T := by -- --- PROOF ---
  intro x hx y hy
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h1 : P.A i x ≤ P.b i - (u i).val := hx.1 i
    have h2 : P.A i y ≤ (u i).val := (u i).le y hy
    rw [map_add]
    linarith
  · have h1 : P.Ae i x = P.be i := hx.2 i
    rw [map_add, h1, hker i y hy, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
