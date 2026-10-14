module

public import CORALean.ContSet.SpectraShadow.Real.SpectraShadow

@[expose] public section

/-!
# `ContSet/SpectraShadow/Real/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ==============================  `SpectraShadow.hyperplaneOne`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

/-- `spectraShadow(sparse(1,n+1), c_one, [speye(n); sparse(1,n)])` of `convHull_`: the hyperplane
`ℝⁿ × {1}` of `ℝⁿ⁺¹`, the trivial inequality `0 ⪰ 0` with the last coordinate fixed to `1`. -/
abbrev SpectraShadow.hyperplaneOne (n : ℕ) : SpectraShadow (Vec ℝ (n + 1)) :=
  ⟨1, n, 0, fun _ => 0, Fin.append (0 : Vec ℝ n) (fun _ : Fin 1 => 1),
    fun j => Fin.append (Pi.single j 1 : Vec ℝ n) (0 : Vec ℝ 1)⟩

end CORALean.Real


-- ===============================  `SpectraShadow.pointExample`  =============================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

open Matrix

/-- The point `{0}` of `ℝ¹` as `1 ⪰ 0` with `A₁ = 0` and `G = 0`, the counterexample set of
`SpectraShadow.supportFuncCoraAllZero_ne_supportFunc`. -/
def SpectraShadow.pointExample : SpectraShadow (Vec ℝ 1) :=
  ⟨1, 1, 1, fun _ => 0, 0, fun _ => 0⟩

end CORALean.Real


-- ================================  `SpectraShadow.translate`  ================================= --
-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- A shadow shifted by a vector: only the centre moves, the inequality is untouched. CORA's
`SpS - c` and `SpS + c` for a numeric `c` (`@spectraShadow/plus.m` with a point), as the
shift of the set by `v` is the centre `c + v`. -/
def SpectraShadow.translate (S : SpectraShadow α) (v : α) : SpectraShadow α :=
  { S with c := S.c + v }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
