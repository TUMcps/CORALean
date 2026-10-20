module

public import CORALean.ContSet.Zonotope.Real.Operations.SupportStrip
public import CORALean.ContSet.Zonotope.Real.Theorems.SupportDotProduct

@[expose] public section

/-!
# Meeting the support strip first changes nothing

[1, Sec. 3.2]: with `F_S` the support strip of `Z` and `F_T = F_S ∩ F` the tight strip of a strip
`F`, "`F ∩ Z = F_S ∩ F ∩ Z = F_T ∩ Z`", because `Z ⊆ F_S` (by [1, Def. 7], `support_dotProduct`).
Proved for every set `F`, which a strip is.

## Inputs
* `Z` – zonotope
* `c` – direction
* `F` – set

## Hypotheses
* none

## Conclusion
* adding the support strip does not change the intersection

## References

* [1] J. M. Bravo, T. Alamo and E. F. Camacho. "Bounded error identification of systems with
      time-varying parameters". IEEE Transactions on Automatic Control, 51(7):1144-1150, 2006.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.construct_inter_supportStrip_inter (Z : Zonotope (Vec ℝ n)) (c : Vec ℝ n)
    (F : Set (Vec ℝ n)) :
    Z.construct ∩ (Z.supportStrip c ∩ F) = Z.construct ∩ F := by -- --- PROOF ---
  ext x
  constructor
  · rintro ⟨hx, -, hF⟩
    exact ⟨hx, hF⟩
  · -- a point of the zonotope lies between the two tangent hyperplanes
    rintro ⟨hx, hF⟩
    obtain ⟨⟨_, hmax⟩, ⟨_, hmin⟩⟩ := Zonotope.support_dotProduct Z c
    exact ⟨hx, ⟨hmin ⟨x, hx, rfl⟩, hmax ⟨x, hx, rfl⟩⟩, hF⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
