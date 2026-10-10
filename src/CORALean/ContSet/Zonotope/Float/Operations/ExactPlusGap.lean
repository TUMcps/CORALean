import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.exactPlusGap`

What the rounding of `Zonotope.exactPlus`'s shared columns costs, laid out like its generators: on
a shared column the stored sum is rounded down, so the exact sum lies above it by at most the
sum rounded up minus the sum rounded down (`subUp`), and on the copied columns nothing rounds.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.exactPlusGap (Z₁ Z₂ : Zonotope 𝕋 n) (k : ℕ) :
    Mat 𝕋 n (min (min Z₁.h Z₂.h) k + (Z₁.h - min (min Z₁.h Z₂.h) k) +
      (Z₂.h - min (min Z₁.h Z₂.h) k)) :=
  let m := min (min Z₁.h Z₂.h) k
  have hm₁ : m ≤ Z₁.h := (min_le_left _ _).trans (min_le_left _ _)
  have hm₂ : m ≤ Z₂.h := (min_le_left _ _).trans (min_le_right _ _)
  -- the gap on each shared column, and nothing on the copied ones
  let gap : Mat 𝕋 n m := fun i j =>
    subUp (addUp (Z₁.G (Fin.castLE hm₁ j) i) (Z₂.G (Fin.castLE hm₂ j) i))
      (addDown (Z₁.G (Fin.castLE hm₁ j) i) (Z₂.G (Fin.castLE hm₂ j) i))
  fun i => Fin.append (Fin.append (gap i) fun _ : Fin (Z₁.h - m) => zero)
    fun _ : Fin (Z₂.h - m) => zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
