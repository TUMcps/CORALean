import CORALean.ContSet.ConPolyZono.Real.Operations.RepVec
import CORALean.ContSet.ConPolyZono.Real.ConPolyZono

/-!
# `ConPolyZono.convHullG`

The generators of [1, Prop. 9]: `a` copies of the linear combination's centre,
one per weight factor, and then its generators twice over — plain, and again for
the weighted half of each copy.

The centre of the result is `a` times the combination's, so a copy contributes
`c + λ c` where the weight `1 + λ` asks for `(1 + λ) c`.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A copy of the centre per weight, then the generators plain and weighted. -/
noncomputable def ConPolyZono.convHullG {α : Type} [AddCommGroup α] [Module ℝ α] (a : ℕ) {h : ℕ}
    (c : α) (G : Fin h → α) : Fin (a + (a * h + a * h)) → α :=
  Fin.append (fun _ => c) (Fin.append (ConPolyZono.repVec a G) (ConPolyZono.repVec a G))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
