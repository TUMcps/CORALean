import Mathlib.Data.Nat.Notation

/-!
# The weights of a polynomial sigmoid layer

The polynomial sigmoid layer as an `Enclose` kind, at a polynomial zonotope only: per neuron a
fit `c` of degree `deg`, a grid `p` of `N + 1` points and its spacing `dx`, and `k`, how many
terms enclose `exp`. The dimension is kept, so its weights carry `dim`, the proof that the two
dimensions agree, which `rfl` discharges where a layer is built.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

structure SigmoidPolyLayer (𝕋 : Type) (n m : ℕ) where
  k : ℕ
  deg : ℕ
  N : ℕ
  c : Fin n → 𝕋 → 𝕋 → Fin (deg + 1) → 𝕋
  dx : Fin n → 𝕋 → 𝕋 → 𝕋
  p : Fin n → 𝕋 → 𝕋 → Fin (N + 1) → 𝕋
  dim : n = m

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
