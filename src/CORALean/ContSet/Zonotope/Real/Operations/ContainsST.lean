module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `Zonotope.containsST`

CORA's `contains_(Z, S, 'approx:st')`: whether `[1, Thm. 3]` certifies `S ⊆ Z`. The
condition is a linear program in `(Γ, β)`, and the solver is an argument returning a
candidate or nothing; the candidate is checked here, so a wrong or missing one costs the
answer `true` and never soundness. `false` says only that this condition was not shown.

## Inputs
* `lp` – linear-program solver
* `Zy` – outer zonotope
* `Zx` – inner zonotope

## Output
* `true` iff the solver's certificate shows containment

## References

* [1] [S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". 2019 IEEE
      58th Conference on Decision and Control (CDC),
      2019.](../../../../../../references/2019/sadraddini-cdc-polytope-containment.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α] [DecidableEq α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `true` if the solver's `(Γ, β)` meets `[1, Thm. 3]` for `Zx ⊆ Zy`. -/
noncomputable def Zonotope.containsST
    (lp : (Zy Zx : Zonotope α) → Option (Mat ℝ Zy.h Zx.h × Vec ℝ Zy.h))
    (Zy Zx : Zonotope α) : Bool :=
  match lp Zy Zx with
  | none => false
  | some (Γ, β) =>
    if (∀ j, Zx.G j = ∑ k, Γ k j • Zy.G k) ∧ Zy.c - Zx.c = ∑ k, β k • Zy.G k ∧
      ∀ k, ∑ j, |Γ k j| + |β k| ≤ 1 then true else false

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
