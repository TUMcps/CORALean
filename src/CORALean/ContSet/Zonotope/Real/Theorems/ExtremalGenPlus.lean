module

public import CORALean.ContSet.Zonotope.Real.Operations.ExtremalGen
public import CORALean.ContSet.Zonotope.Real.Operations.Plus
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The under-approximation of a sum is the `⊞` of the under-approximations

[1, Lemma 1]: with `(u, [g₁, …, g_ℓ]_S) ⊞ (u', [g'₁, …, g'_ℓ]_S) = (u + u', [g₁ + g'₁, …,
g_ℓ + g'_ℓ]_S)`, the under-approximation of `Z ⊕ Z'` is `Z̲ ⊞ Z̲'`. Stated at the
representation, which is what [1] compares: the centre of `Z ⊕ Z'` is `u + u'`, and its
extremal offset along every direction is `gᵢ + g'ᵢ`, since `Z ⊕ Z'` concatenates the two
generator lists and the offset sums over the generators one at a time. The sets
`Zonotope.underS` of the two sides are then equal by rewriting.

## References

* [1] A. Girard, C. Le Guernic and O. Maler. "Efficient Computation of Reachable Sets of
      Linear Time-Invariant Systems with Inputs". In Hybrid Systems: Computation and
      Control (HSCC), LNCS 3927, Springer, 2006, pp. 257-271.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Lemma 1]: `(Z ⊕ Z')` has centre `u + u'` and extremal offsets `gᵢ + g'ᵢ`. -/
theorem Zonotope.extremalGen_plus (Z Z' : Zonotope (Vec ℝ n)) :
    (Z.plus Z').c = Z.c + Z'.c ∧
      ∀ s : Vec ℝ n,
        (Z.plus Z').extremalGen s = Z.extremalGen s + Z'.extremalGen s := by -- --- PROOF ---
  refine ⟨rfl, fun s => ?_⟩
  -- the sum over the concatenated generators splits at the seam
  have h := Fin.sum_univ_add fun j : Fin (Z.h + Z'.h) =>
    Real.sign (s ⬝ᵥ Fin.append Z.G Z'.G j) • Fin.append Z.G Z'.G j
  simp only [Fin.append_left, Fin.append_right] at h
  exact h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
