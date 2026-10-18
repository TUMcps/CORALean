module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.StackRows
public import CORALean.ContSet.HPolytope.Float.Operations.Ineqs

@[expose] public section

/-!
# `HPolytope.halfScaledLeft`

The constraints of `P` at the weight a trailing coefficient names, on a wider
coefficient space: `P` reads the first block, the middle block answers to
nothing, and the last coordinate `t` carries the weight `(t + 1) / 2` a
convex combination gives the first of its two sides.

Every right-hand side halves into the column that reads `t`, and halving is exact, so this
computes nothing that rounds — the polytope it returns is as tight as the one it was given.

An equality cannot be weighted by an inequality's rule, so a row leaves as the two inequalities
it stands for, each weighted on its own. That is why the result carries no equalities at all.
The rows are the nominal part's: the error box is not read, and the result carries none. Each row
keeps its slack unweighted, which covers the weighted slack at a weight in `[0, 1]`, so the result
holds every weighted point, exactly so for a slack-free `P` (`smul_mem_halfScaledLeft`).

Padding and weighting are one operation rather than two: the weight lives in the new coordinate,
which is not a block a `padLeft` could add.
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.halfScaledLeft (P : HPolytope 𝕋 (Vec 𝕋 n₁)) (n₂ : ℕ) : HPolytope
    𝕋 (Vec 𝕋 (n₁ + n₂ + 1)) :=
  ({ HPolytope.ineqs (fun i => Fin.append (Fin.append (P.A i) fun _ : Fin n₂ => zero)
        fun _ : Fin 1 => neg (half (P.b i)))
      (fun i => half (P.b i)) with b_error := P.b_error }).stackRows
    (({ HPolytope.ineqs (fun i => Fin.append (Fin.append (P.Ae i) fun _ : Fin n₂ => zero)
          fun _ : Fin 1 => neg (half (P.be i)))
        (fun i => half (P.be i)) with b_error := P.be_error }).stackRows
      { HPolytope.ineqs (fun i => Fin.append (Fin.append (-(P.Ae i))
            fun _ : Fin n₂ => zero) fun _ : Fin 1 => neg (half (neg (P.be i))))
        (fun i => half (neg (P.be i))) with b_error := P.be_error })

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
