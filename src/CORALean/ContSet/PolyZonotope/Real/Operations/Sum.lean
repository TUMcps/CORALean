import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
import Mathlib.Algebra.BigOperators.Fin

/-!
# `PolyZonotope.sum`

CORA's `@polyZonotope/sum`: the sum of `pZ` and a list of sets, all written over one factor
list, so every factor shared by two of them stays shared. Centres add, the generator and
exponent blocks concatenate side by side: `exactPlus` many times over, as one definition so
that the factor count stays `pZ.p`. `hp` says every summand has that count, factor identity
being positional.

CORA then runs `removeRedundantExponents`, which merges equal exponent columns and denotes the
same set (`compact_exact`); it is left out. CORA's centre adds `pZlist{1}.c` on every pass of
its loop, not `pZlist{i}.c`: see `sumCora`.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `pZ` summed with the sets `L 0, ..., L (m-1)`, over `pZ`'s factors. -/
def PolyZonotope.sum {m : ℕ} (pZ : PolyZonotope α) (L : Fin m → PolyZonotope α)
    (hp : ∀ i, (L i).p = pZ.p) : PolyZonotope α where
  p := pZ.p
  h := pZ.h + ∑ i, (L i).h
  q := pZ.q + ∑ i, (L i).q
  c := pZ.c + ∑ i, (L i).c
  G := Fin.append pZ.G fun j =>
    (L (finSigmaFinEquiv.symm j).1).G (finSigmaFinEquiv.symm j).2
  E := fun k => Fin.append (pZ.E k) fun j =>
    (L (finSigmaFinEquiv.symm j).1).E (Fin.cast (hp _).symm k) (finSigmaFinEquiv.symm j).2
  GI := Fin.append pZ.GI fun j =>
    (L (finSigmaFinEquiv.symm j).1).GI (finSigmaFinEquiv.symm j).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
