module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope
public import CORALean.ContSet.HPolytope.Real.Operations.Basic

@[expose] public section

/-!
# A constrained zonotope lies in a halfspace polytope exactly when every optimum is `≤ 0`

[1, Prop. 7]: `CZ ⊆ ⟨C,d⟩_H ⇔ max(ν₁,…,ν_a) ≤ 0`, where `νᵢ` is the optimum of eq. (45)'s linear
program `max C(i,·)c + C(i,·)Gα − d(i)` over `α ∈ [−1,1]`, `Aα = b`. That feasible region, read
through `x = c + Gα`, is `ConZonotope.construct` itself, so the objective is taken over it.
`max(ν₁,…,ν_a) ≤ 0` is `∀ i, νᵢ ≤ 0`, also the right test when there are no halfspaces at all. `νᵢ`
is a hypothesis (`IsGreatest`), as the paper's own `max` presupposes an optimum;
`ConZonotope.exists_isGreatest_ineqs` supplies it whenever `CZ` is nonempty. `⇒` needs the optimum
attained, `⇐` needs it to be an upper bound. The claim is about `⟨C,d⟩_H`, not a general
`HPolytope`, whose equality rows a family of maxima cannot test.

## Inputs
* `cZ` – constrained zonotope
* `C` – halfspace normals
* `d` – halfspace offsets
* `ν` – optimal violations

## Hypotheses
* `hν` – each violation is the maximum over the set

## Conclusion
* the set lies in the polytope iff every optimum is nonpositive

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 7]: the containment check, with each `νᵢ` the optimum of eq. (45). -/
theorem ConZonotope.ineqs_contains_iff (cZ : ConZonotope (Vec ℝ n)) (C : Mat ℝ q n) (d : Vec ℝ q)
    (ν : Fin q → ℝ)
    (hν : ∀ i, IsGreatest ((fun x => (C *ᵥ x) i - d i) '' cZ.construct) (ν i)) :
    cZ.construct ⊆ (HPolytope.ineqs C d).construct ↔ ∀ i, ν i ≤ 0 := by -- --- PROOF ---
  constructor
  -- forward: the optimum is attained, at a point the halfspace already bounds
  · intro hsub i
    obtain ⟨x, hx, hval⟩ := (hν i).1
    have hval' : (C *ᵥ x) i - d i = ν i := hval
    have hrow := HPolytope.mem_ineqs_iff.mp (hsub hx) i
    linarith
  -- back: every point's value is at most the optimum, hence at most `0`
  · intro h0 x hx
    refine HPolytope.mem_ineqs_iff.mpr fun i => ?_
    have hle : (C *ᵥ x) i - d i ≤ ν i := (hν i).2 (Set.mem_image_of_mem _ hx)
    have := h0 i
    linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
