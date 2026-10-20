module

public import CORALean.ContSet.Zonotope.Real.Theorems.IntervalAttained
public import CORALean.ContSet.Interval.Real.Definitions.Hull
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeIntervalContains

@[expose] public section

/-!
# The box of a zonotope is its interval hull

[1, Property 4]: `Box(⟨p, H⟩)` is `[p - Σⱼ |Hᵢⱼ|, p + Σⱼ |Hᵢⱼ|]` coordinate by coordinate, which
is `Zonotope.interval`: it contains the zonotope (`interval_contains`) and its bounds are
attained (`interval_attained`), so they are the coordinates' supremum and infimum. The paper's
sums run from `j = 0`; the generators are `j = 1, …, m`. [1, Eq. 35] is this at the zonotope
of the zonotope method, its sum printed over `i`.

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the bounding box is the interval hull of `Z`

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.interval_eq_hull (Z : Zonotope (Vec ℝ n)) : -- --- CONCL ---
    Z.interval = Interval.hull Z.construct := by -- --- PROOF ---
  -- each bound is attained, and bounds every point
  have hin := Z.interval_contains
  have hinf : Z.interval.inf = (Interval.hull Z.construct).inf := funext fun i => by
    obtain ⟨z, hz, hzi⟩ := (Z.interval_attained i).2
    show _ = sInf ((fun x : Vec ℝ n => x i) '' Z.construct)
    refine (IsLeast.csInf_eq (s := (fun x : Vec ℝ n => x i) '' Z.construct)
      ⟨⟨z, hz, hzi⟩, ?_⟩).symm
    rintro _ ⟨x, hx, rfl⟩
    exact (hin hx i).1
  have hsup : Z.interval.sup = (Interval.hull Z.construct).sup := funext fun i => by
    obtain ⟨z, hz, hzi⟩ := (Z.interval_attained i).1
    show _ = sSup ((fun x : Vec ℝ n => x i) '' Z.construct)
    refine (IsGreatest.csSup_eq (s := (fun x : Vec ℝ n => x i) '' Z.construct)
      ⟨⟨z, hz, hzi⟩, ?_⟩).symm
    rintro _ ⟨x, hx, rfl⟩
    exact (hin hx i).2
  calc Z.interval = ⟨Z.interval.inf, Z.interval.sup⟩ := rfl
    _ = Interval.hull Z.construct := by rw [hinf, hsup]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
