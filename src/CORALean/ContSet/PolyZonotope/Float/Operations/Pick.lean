module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.pick`

The dependent generators `idx 0, …, idx (m-1)`, in that order, each with its exponent column. It is
a permutation of the columns when `idx` is a bijection, and the removal of zero generators when the
columns outside its range are certified zero (`le` answers `true` both ways, which `FloatOps`
constrains for `true` only). Where the index map fails either test, the set is returned as it is,
so that a ranking chosen outside Lean (CORA's hash) can never cost soundness.

## Inputs
* `pZ` – polynomial zonotope
* `m` – number of generators picked
* `idx` – the index of the generator behind each

## Output
* polynomial zonotope of the picked generators
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

/-- The generators `idx`, one after the other; `pZ` itself unless `idx` names generators, is
injective and every generator it leaves out is certified zero. -/
def PolyZonotope.pick (pZ : PolyZonotope (Vec 𝕋 n)) (m : ℕ) (idx : Fin m → ℕ) :
    PolyZonotope (Vec 𝕋 n) :=
  if hv : (∀ t, idx t < pZ.h) ∧ Function.Injective idx ∧ ∀ l : Fin pZ.h, ¬ (∃ t, idx t = l.val) →
      ∀ i : Fin n, le (pZ.G l i) zero = true ∧ le zero (pZ.G l i) = true then
    { pZ with h := m, G := fun t => pZ.G ⟨idx t, hv.1 t⟩, E := fun k t => pZ.E k ⟨idx t, hv.1 t⟩ }
  else pZ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
