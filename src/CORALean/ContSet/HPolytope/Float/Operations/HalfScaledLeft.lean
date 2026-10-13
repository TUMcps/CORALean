module

public import CORALean.ContSet.HPolytope.Float.Operations.Intersection
public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs

@[expose] public section

/-!
# `HPolytope.halfScaledLeft`

The constraints of `P` at the weight a trailing coefficient names, on a wider
coefficient space: `P` reads the first block, the middle block answers to
nothing, and the last coordinate `t` carries the weight `(t + 1) / 2` a
convex combination gives the first of its two sides.

Every right-hand side halves into the column that reads `t`, and halving is
exact, so this computes nothing that rounds — the polytope it returns is as
tight as the one it was given.

An equality cannot be weighted while its right-hand side is an interval, so an
interval row leaves as the two inequalities it stands for, each weighted on its
own. That is why the result carries no equalities at all.

Padding and weighting are one operation rather than two: the weight lives in the
new coordinate, which is not a block a `padLeft` could add.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.halfScaledLeft (P : HPolytope 𝕋 (Vec 𝕋 n₁)) (n₂ : ℕ) : HPolytope
    𝕋 (Vec 𝕋 (n₁ + n₂ + 1)) :=
  (HPolytope.ineqs (fun i => Fin.append (Fin.append (P.A i) fun _ : Fin n₂ => zero)
        fun _ : Fin 1 => neg (half (P.b i)))
      fun i => half (P.b i)).intersection
    ((HPolytope.ineqs (fun i => Fin.append (Fin.append (P.Ae i) fun _ : Fin n₂ => zero)
          fun _ : Fin 1 => neg (half (P.be.sup i)))
        fun i => half (P.be.sup i)).intersection
      (HPolytope.ineqs (fun i => Fin.append (Fin.append (fun k => neg (P.Ae i k))
            fun _ : Fin n₂ => zero) fun _ : Fin 1 => half (P.be.inf i))
        fun i => neg (half (P.be.inf i))))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
