module

public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.pick`

The generators `idx 0, …, idx (m-1)`, in that order: a permutation of the generators when `idx` is
a bijection, and the removal of zero generators when those outside its range are certified zero
(`le` answers `true` both ways). Where the index map fails either test the zonotope is returned
as it is.

## Inputs
* `Z` – zonotope
* `m` – number of generators picked
* `idx` – the index of the generator behind each

## Output
* zonotope of the picked generators
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The generators `idx`, one after the other; `Z` itself unless `idx` names generators, is
injective and every generator it leaves out is certified zero. -/
def Zonotope.pick (Z : Zonotope (Vec 𝕋 n)) (m : ℕ) (idx : Fin m → ℕ) : Zonotope (Vec 𝕋 n) :=
  if hv : (∀ t, idx t < Z.h) ∧ Function.Injective idx ∧ ∀ l : Fin Z.h, ¬ (∃ t, idx t = l.val) →
      ∀ i : Fin n, le (Z.G l i) zero = true ∧ le zero (Z.G l i) = true then
    { Z with h := m, G := fun t => Z.G ⟨idx t, hv.1 t⟩ }
  else Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
