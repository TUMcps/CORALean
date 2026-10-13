module

public import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
public import CORALean.ContSet.ConPolyZono.Real.Operations.RepVec

@[expose] public section

/-!
# `ConPolyZono.convHullG`

The generators of [1, Prop. 9]: `a` copies of the centre, one per weight factor, then
the generators twice over, plain and weighted. All entries are copies, so nothing here
rounds.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A copy of the centre per weight, then the generators plain and weighted. -/
def ConPolyZono.convHullG (a : ℕ) {h : ℕ} (c : Vec 𝕋 n) (G : Fin h → Vec 𝕋 n) :
    Fin (a + (a * h + a * h)) → Vec 𝕋 n :=
  Fin.append (fun _ => c) (Fin.append (Real.ConPolyZono.repVec a G) (Real.ConPolyZono.repVec a G))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
