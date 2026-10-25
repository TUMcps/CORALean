module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.Global.Tensor

@[expose] public section

/-!
# What the dichotomic search of [1, Alg. 4] keeps true

The state `(P, G, s)` of the loop, with `σ = ±1` the direction searched (`σ = 1` right of the
lowest vertex, `σ = -1` left of it): some set `B` of generators pointing along `σ` has been
passed, `P` is the lowest vertex plus `∑_B 2g`, `G` is a set of generators pointing along `σ` that
follow `B` and precede the others in the order of `σ·cross`, `s = ∑_G 2g`, and the line is between
the abscissae of `P` and `P + s`. `B` is the part of the walk already taken; it makes the vertex
`P` a vertex of the zonogon, and `G` a stretch of its boundary that the search narrows.

## Inputs
* `Z` – planar zonotope
* `γ` – abscissa of the vertical line
* `σ` – search direction, plus or minus one
* `st` – loop state

## Output
* `Prop` that the loop invariant holds on the state

## References

* [1] A. Girard and C. Le Guernic. "Zonotope/Hyperplane Intersection for Hybrid Systems Reachability
      Analysis". Hybrid Systems: Computation and Control, 2008.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The invariant of the loop on the state `(P, G, s)` of the dichotomic search of [1]. -/
def Zonotope.IsBisectInv (Z : Zonotope (Vec ℝ 2)) (γ σ : ℝ)
    (st : Vec ℝ 2 × Finset (Fin Z.h) × Vec ℝ 2) : Prop :=
  ∃ B : Finset (Fin Z.h),
    Disjoint B st.2.1 ∧ (∀ i ∈ B, 0 < σ * Z.G i 0) ∧ (∀ i ∈ st.2.1, 0 < σ * Z.G i 0) ∧
    st.1 = (Z.c - ∑ j, Z.G j) + ∑ i ∈ B, (2 : ℝ) • Z.G i ∧
    st.2.2 = ∑ i ∈ st.2.1, (2 : ℝ) • Z.G i ∧
    (∀ b ∈ B, ∀ i ∈ st.2.1, 0 ≤ σ * (Z.G b 0 * Z.G i 1 - Z.G b 1 * Z.G i 0)) ∧
    (∀ i ∈ st.2.1, ∀ r : Fin Z.h, 0 < σ * Z.G r 0 → r ∉ B → r ∉ st.2.1 →
      0 ≤ σ * (Z.G i 0 * Z.G r 1 - Z.G i 1 * Z.G r 0)) ∧
    (min (st.1 0) ((st.1 + st.2.2) 0) ≤ γ ∧ γ ≤ max (st.1 0) ((st.1 + st.2.2) 0)) ∧
    (B.Nonempty → st.2.1.Nonempty)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
