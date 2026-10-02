import CORALean.ContSet.Zonotope.Real.Zonotope

/-!
# `Zonotope.exactPlus`

CORA's `@zonotope/exactPlus`: the sum of two zonotopes whose first `m = min(h₁, h₂, k)` generators
share their coefficients. Centres add, the first `m` generator columns add pairwise, and the
remaining columns of each operand follow. That is *not* `plus`, which concatenates all generators
and so lets every coefficient move independently: here a coefficient that moves `Z₁`'s `j`-th
generator moves `Z₂`'s too, and the dependency survives. The result is a subset of `plus`'s, and a
smaller one whenever `m > 0`. CORA's optional third argument is `k`; leaving it out is `k = ∞`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `zonotope/exactPlus`: `G = [G₁(:,1:m) + G₂(:,1:m), G₁(:,m+1:end), G₂(:,m+1:end)]`. -/
def Zonotope.exactPlus (Z₁ Z₂ : Zonotope α) (k : ℕ) : Zonotope α :=
  let m := min (min Z₁.h Z₂.h) k
  have hm₁ : m ≤ Z₁.h := (min_le_left _ _).trans (min_le_left _ _)
  have hm₂ : m ≤ Z₂.h := (min_le_left _ _).trans (min_le_right _ _)
  { h := m + (Z₁.h - m) + (Z₂.h - m)
    c := Z₁.c + Z₂.c
    G := Fin.append
      (Fin.append (fun i : Fin m => Z₁.G (Fin.castLE hm₁ i) + Z₂.G (Fin.castLE hm₂ i))
        (fun i : Fin (Z₁.h - m) => Z₁.G ⟨m + i, by have := i.2; omega⟩))
      (fun i : Fin (Z₂.h - m) => Z₂.G ⟨m + i, by have := i.2; omega⟩) }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
