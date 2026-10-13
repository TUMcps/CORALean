module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Zonotope.Float.Operations.GeneratorLength
public import CORALean.Global.Sort

@[expose] public section

/-!
# `Zonotope.methCBasis`

The basis `reduce(Z, 'methC', ·)` boxes along, [1]: `n` of the generators of the zonotope.
CORA filters the generators by length and then chooses the `n` of largest spanned volume by an
exhaustive search; here the `n` longest are taken, ranked by `generatorLength`, which is
cheap and which `reduceMethC_outer` does not depend on: a poor basis costs precision alone. A
zonotope with fewer than `n` generators has no basis, and the column is then `zero`.

## References

* [1] `contSet/@zonotope/private/priv_reduceMethC.m`, CORA (Sep. 2025). No
      paper behind the rule was confirmed.
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

/-- The `n` longest generators, side by side. -/
def Zonotope.methCBasis (Z : Zonotope (Vec 𝕋 n)) : Mat 𝕋 n n := fun i k =>
  if hk : k.val < Z.h then
    Z.G (sortPerm (fun j₁ j₂ => le (Z.generatorLength 2 j₂) (Z.generatorLength 2 j₁))
      ⟨k.val, hk⟩) i
  else zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
