module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Project
public import CORALean.ContSet.ConPolyZono.Real.Theorems.MapExact

@[expose] public section

/-!
# `ContSet/ConPolyZono/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean.Real

variable {n m : ℕ} {α : Type}


-- ===============================  `ConPolyZono.project_exact`  ================================ --
-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Reading the same coordinates of every member, no hypothesis on `dims`: a linear map is exact
without injectivity, so nothing is added and nothing lost. -/
theorem ConPolyZono.project_exact (cPZ : ConPolyZono (Vec ℝ n)) (dims : Fin m → Fin n) :
    (fun x k => x (dims k)) '' cPZ.construct = (cPZ.project dims).construct :=
  ConPolyZono.map_exact (LinearMap.funLeft ℝ ℝ dims) cPZ


-- ===========================  `ConPolyZono.satisfies_iff_mem_cons`  =========================== --
-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- The factor constraint is the polynomial level set `cons`: each row `A μ_R(α) = b` is the
`=` row `(A μ_R(α) - b)ᵢ = 0`. -/
theorem ConPolyZono.satisfies_iff_mem_cons (cPZ : ConPolyZono α) (a : Fin cPZ.p → ℝ) :
    cPZ.satisfies a ↔ a ∈ cPZ.cons.construct :=
  forall_congr' fun _ => sub_eq_zero.symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
