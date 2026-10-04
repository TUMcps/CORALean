import CORALean.ContSet.ConPolyZono.Float.ConPolyZono
import CORALean.ContSet.ConPolyZono.Real.Operations.RepVec

/-!
# `ConPolyZono.convHullG`

The generators of [1, Prop. 9]: `a` copies of the centre, one per weight factor, then
the generators twice over, plain and weighted. All entries are copies, so nothing here
rounds.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A copy of the centre per weight, then the generators plain and weighted. -/
def ConPolyZono.convHullG (a : ℕ) {h : ℕ} (c : Vec 𝕋 n) (G : Mat 𝕋 n h) :
    Mat 𝕋 n (a + (a * h + a * h)) :=
  fun i => Fin.append (fun _ => c i)
    (Fin.append (Real.ConPolyZono.repVec a (G i)) (Real.ConPolyZono.repVec a (G i)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
