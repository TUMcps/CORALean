import Mathlib.Data.Rat.Defs

/-!
# `randverify`: a window's support along its candidate normals

For a window `Y` in output space, each candidate normal `n` (integer, primitive) with the numerator
of `ρ_Y(n) = max_{y ∈ Y} n · y` over `den`, exactly, and its length as a scale and a `Float`; and
the same normalised, approximately, to choose among the candidates fast. The candidates are the
facet normals of `Y` -- the perpendiculars `±(-g₂, g₁)` of its generators -- and `±e₁`, `±e₂`, which
are those of an unsafe box: together, the facet normals of `Y ⊕ (-S)` for every box `S`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Bench


-- ========================================  MAIN TYPE  ========================================= --

structure RandWindow where
  den : ℕ
  /-- `(n₁, n₂, den · ρ_Y(n), den · 2^k, ‖n‖₂ / 2^k)` per candidate normal, `2^k` near `‖n‖₂`:
  the last two only to report a distance, so that no `Float` overflows. -/
  normals : Array (ℤ × ℤ × ℤ × ℕ × Float)
  /-- `(n₁, n₂, ρ_Y(n)) / ‖n‖₂` per candidate normal, as `Float`s: to choose a normal fast, never
  to decide. -/
  approx : Array (Float × Float × Float)

end CORALean.Bench


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
