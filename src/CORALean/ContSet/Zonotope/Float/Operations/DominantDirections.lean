module

public import CORALean.ContSet.Zonotope.Float.Operations.DominantScore
public import CORALean.ContSet.Zonotope.Float.Operations.DominantShortlist
public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.dominantDirections`, over a floating-point scalar

CORA's `dominantDirections(Z, filterLength1, filterLength2)` [1] in rounded arithmetic: the
generators go through the length filter (`filterLength1 = n + 5` of the longest), the generator
volume filter (`filterLength2 = n + 3` subsets of largest `|det|`), and `priv_volumeFilter` picks
the subset of least `dominantScore`, the first on a tie. Both lengths are clamped to the number of
non-zero generators.

Every ranking runs on rounded numbers, so the subset picked need not be the one the exact layer
picks. What does not depend on the ranking is what is returned: columns that are stored
generators (`dominantDirections_mem`), whose parallelotope encloses the zonotope whenever they are
invertible (`dominantDirections_outer`). `none` where fewer than `n` generators are left.

## References

* [1] `contSet/@zonotope/dominantDirections.m` and its private helpers, CORA (Sep. 2025), by
      M. Althoff (2010). No paper behind the rule was confirmed.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The number of generators that are not provably zero. -/
def Zonotope.aux_nonzeroCount (Z : Zonotope (Vec 𝕋 n)) : ℕ :=
  ((List.finRange Z.h).filter fun j =>
    !(List.finRange n).all fun i => le (absolute (Z.G j i)) zero).length


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `dominantDirections`: the `n` generators, as columns, of least `dominantScore` among the
shortlist; `none` where there is none. -/
def Zonotope.dominantDirections (Z : Zonotope (Vec 𝕋 n))
    (filterLength₁ : ℕ := n + 5) (filterLength₂ : ℕ := n + 3) : Option (Mat 𝕋 n n) :=
  let nrOfGens :=
    Z.aux_nonzeroCount                                         -- size(nonzeroFilter(G),2)
  let L₁ := min filterLength₁ nrOfGens                                    -- clamp filterLength1
  let L₂ := min filterLength₂ nrOfGens                                    -- clamp filterLength2
  let Gcells := Z.dominantShortlist L₁ L₂                              -- priv_generatorVolumeFilter
  let better : Option 𝕋 → Option 𝕋 → Bool := fun a b =>                  -- a < b, `inf` last
    match a, b with
    | some x, some y => ltStrict x y
    | some _, none => true
    | none, _ => false
  (Gcells.map Z.generatorMatrix).foldl                                  -- priv_volumeFilter, 1 pick
    (fun best P => match best with
      | none => some P
      | some Q => if better (Z.dominantScore P) (Z.dominantScore Q) then some P else some Q)
    none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
