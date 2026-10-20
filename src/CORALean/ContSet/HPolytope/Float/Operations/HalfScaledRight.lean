module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows
public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs

@[expose] public section

/-!
# `HPolytope.halfScaledRight`

The mirror of `halfScaledLeft`: `P` reads the second block, and the trailing
coefficient carries the complementary weight `(1 - t) / 2`, which is the other
side of the same convex combination. Only the sign of the weighting column
differs.

## Inputs
* `n₁` – natural number
* `P` – H-polytope

## Output
* the constraints of `P` at weight `(1 - t) / 2` on a coefficient space wider by `n₁ + 1`
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.halfScaledRight (n₁ : ℕ) (P : HPolytope 𝕋 (Vec 𝕋 n₂)) : HPolytope
    𝕋 (Vec 𝕋 (n₁ + n₂ + 1)) :=
  ({ HPolytope.ineqs (fun i => Fin.append (Fin.append (fun _ : Fin n₁ => zero) (P.A i))
        fun _ : Fin 1 => half (P.b i))
      (fun i => half (P.b i)) with b_error := P.b_error }).stackRows
    (({ HPolytope.ineqs (fun i => Fin.append (Fin.append (fun _ : Fin n₁ => zero) (P.Ae i))
          fun _ : Fin 1 => half (P.be i))
        (fun i => half (P.be i)) with b_error := P.be_error }).stackRows
      { HPolytope.ineqs (fun i => Fin.append (Fin.append (fun _ : Fin n₁ => zero)
            (-(P.Ae i))) fun _ : Fin 1 => half (neg (P.be i)))
        (fun i => half (neg (P.be i))) with b_error := P.be_error })

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
