module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `Zonotope.reduceUnderApproxSadraddini`

CORA's `reduceUnderApprox(Z, 'sadraddini', order)`: a zonotope of lower order inside `Z`,
`[1, Cor. 6]`. The optimization (43) is bilinear and solved by alternation, outside the
trusted base: `opt` proposes generators `X_red` with a `Γ₀`, and what is kept is checked,
`X_red = X Γ₀` with `‖Γ₀‖∞ ≤ 1`, which is (43)'s containment row and `[1, Thm. 3]`'s
condition for `⟨x̄, X_red⟩ ⊆ ⟨x̄, X⟩`. A missing or failing proposal costs the reduction,
not soundness: the center alone is returned, which `Z` always contains.

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The solver's reduced generators if they pass (43)'s containment row, else the center. -/
noncomputable def Zonotope.reduceUnderApproxSadraddini
    (opt : (Z : Zonotope (Vec ℝ n)) → Option (Σ h : ℕ, (Fin h → Vec ℝ n) × Mat ℝ Z.h h))
    (Z : Zonotope (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  match opt Z with
  | none => ⟨0, Z.c, Fin.elim0⟩
  | some ⟨h, Gr, Γ₀⟩ =>
    if (∀ k, Gr k = ∑ j, Γ₀ j k • Z.G j) ∧ ∀ j, ∑ k, |Γ₀ j k| ≤ 1 then ⟨h, Z.c, Gr⟩
    else ⟨0, Z.c, Fin.elim0⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
