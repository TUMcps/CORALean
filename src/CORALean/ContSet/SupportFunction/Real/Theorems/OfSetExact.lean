module

public import CORALean.ContSet.SupportFunction.Real.Operations.OfSet
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A closed convex set is its support function

The support function of a closed convex set denotes the set: the set is contained in every halfspace
its support function names, and a point outside it is separated from it by a hyperplane
(Hahn–Banach), whose normal is a functional under which the point exceeds the support function.
Without closedness the support function sees only the closure; without convexity only the closed
convex hull.

## Inputs
* `S` – set

## Hypotheses
* `hconv` – `S` is convex
* `hcl` – `S` is closed

## Conclusion
* the support function of `S` denotes `S`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem SupportFunction.ofSet_exact {S : Set α} (hconv : Convex ℝ S)
    (hcl : IsClosed S) : -- --- CONCL ---
    (SupportFunction.ofSet S).construct = S := by -- --- PROOF ---
  ext x
  constructor
  · intro hx
    by_contra hxS
    -- a hyperplane separates `x` from `S`; its normal is a functional `ℓ`
    obtain ⟨f, u, hS, hu⟩ := geometric_hahn_banach_closed_point hconv hcl hxS
    -- `ℓ` bounds `S` by `u`, and `x` exceeds `u`
    have hle : supportFunc S (f : α →ₗ[ℝ] ℝ) ≤ (u : EReal) :=
      iSup₂_le fun y hy => EReal.coe_le_coe_iff.mpr (hS y hy).le
    have h2 : f x ≤ u := EReal.coe_le_coe_iff.mp ((hx (f : α →ₗ[ℝ] ℝ)).trans hle)
    linarith
  · intro hx ℓ
    exact le_iSup₂ (f := fun y _ => (ℓ y : EReal)) x hx

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
