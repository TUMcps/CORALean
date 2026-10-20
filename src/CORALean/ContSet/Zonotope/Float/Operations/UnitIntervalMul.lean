module

public import CORALean.ContSet.Zonotope.Float.Zonotope

@[expose] public section

/-!
# `Zonotope.unitIntervalMul`, `[-1, 1] ⊗ Z` at a float zonotope

`Real.Zonotope.unitIntervalMul`, [1, Eq. 11]: the center becomes a generator and the new center
is `0`. The error box `I_error` scales by `s ∈ [-1, 1]` too, so it becomes its symmetric hull
`[-m, m]`, `mᵢ = max(|E̲ᵢ|, |Ēᵢ|)`; `neg`, `absolute` and `maximum` are exact, so nothing rounds.

## Inputs
* `Z` – zonotope

## Output
* zonotope with the box's symmetric hull as generators

## References

* [1] M. Althoff and B. H. Krogh. "Avoiding Geometric Intersection Operations in
      Reachability Analysis of Hybrid Systems". In Proc. of the 15th ACM
      International Conference on Hybrid Systems: Computation and Control (HSCC),
      2012, pp. 45-54.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Eq. 11]: `(0, c, g⁽¹⁾, ..., g⁽ᵖ⁾)` with the box's symmetric hull. -/
def Zonotope.unitIntervalMul (Z : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  let m : Vec 𝕋 n := fun i => maximum (absolute (Z.I_error.inf i)) (absolute (Z.I_error.sup i))
  { h := Z.h + 1
    c := fun _ => zero
    G := Fin.cons Z.c Z.G
    I_error := ⟨-m, m⟩ }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
