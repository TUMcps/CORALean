import CORALean.ContSet.Zonotope.Real.Operations.ExtremalGen

/-!
# The under-approximation of a zonotope by its extremal points along `S`

[1, Sec. 5.1]: for directions `S = {s₁, …, s_ℓ}`, the zonotope `Z = (u, ⟨v₁, …, v_m⟩)` is
under-approximated by `Z̲ = (u, [g₁, …, g_ℓ]_S) = {u + Σᵢ αᵢgᵢ : Σᵢ |αᵢ| ≤ 1}`, the convex
hull of its extremal points `u ± gᵢ` (`Zonotope.extremalGen`). The paper writes it both
as that hull and in this form; the form is the one taken here. The order of `S` matters,
as [1] remarks, so the directions are a family `s : Fin ℓ → Vec ℝ n`.

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

variable {n ℓ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 5.1]: `Z̲ = {u + Σᵢ αᵢgᵢ : Σᵢ |αᵢ| ≤ 1}`, `gᵢ` the extremal offset along `sᵢ`. -/
def Zonotope.underS (Z : Zonotope (Vec ℝ n)) (s : Fin ℓ → Vec ℝ n) : Set (Vec ℝ n) :=
  {x | ∃ α : Fin ℓ → ℝ, ∑ i, |α i| ≤ 1 ∧ x = Z.c + ∑ i, α i • Z.extremalGen (s i)}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
