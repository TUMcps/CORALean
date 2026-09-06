import CORALean.ContSet.HPolytope.Float.Operations.And
import CORALean.ContSet.HPolytope.Float.Operations.Ineqs

/-!
# `HPolytope.halfScaledRight`

The mirror of `halfScaledLeft`: `P` reads the second block, and the trailing
coefficient carries the complementary weight `(1 - t) / 2`, which is the other
side of the same convex combination. Only the sign of the weighting column
differs.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.halfScaledRight (n₁ : ℕ) (P : HPolytope 𝕋 n₂) : HPolytope 𝕋 (n₁ + n₂ + 1) :=
  (HPolytope.ineqs (fun i => Fin.append (Fin.append (fun _ : Fin n₁ => zero) (P.A i))
        fun _ : Fin 1 => half (P.b i))
      fun i => half (P.b i)).and
    ((HPolytope.ineqs (fun i => Fin.append (Fin.append (fun _ : Fin n₁ => zero) (P.Ae i))
          fun _ : Fin 1 => half (P.be.sup i))
        fun i => half (P.be.sup i)).and
      (HPolytope.ineqs (fun i => Fin.append (Fin.append (fun _ : Fin n₁ => zero)
            fun k => neg (P.Ae i k)) fun _ : Fin 1 => neg (half (P.be.inf i)))
        fun i => neg (half (P.be.inf i))))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
