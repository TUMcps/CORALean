module

public import CORALean.ContSet.HPolytope.Real.Operations.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A certificate maps one H-polytope into another

The step every encoding in `[1]` rests on, `[1, Thm. 1, Eq. 17]`: nonnegative weights `Λ` with
`Λ Hx = Hy Γ` and `Λ hx ≤ hy + Hy β` put `Γ p - β` in `{y | Hy y ≤ hy}` for every `p` with
`Hx p ≤ hx`. Weak duality, row by row; no hypothesis on either polytope.

## References

* [1] S. Sadraddini and R. Tedrake. "Linear Encodings for Polytope Containment Problems". In
      Proc. of the 58th IEEE Conference on Decision and Control (CDC), pp. 4367-4372, 2019.
      arXiv:1903.05214.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {qx nx qy ny : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.mem_ineqs_of_cert {Hx : Mat ℝ qx nx} {hx : Vec ℝ qx} {Hy : Mat ℝ qy ny}
    {hy : Vec ℝ qy} {Γ : Mat ℝ ny nx} {β : Vec ℝ ny} {Λ : Mat ℝ qy qx}
    (hΛ : ∀ i j, 0 ≤ Λ i j) (h1 : Λ * Hx = Hy * Γ) (h2 : Λ *ᵥ hx ≤ hy + Hy *ᵥ β)
    {p : Vec ℝ nx} (hp : p ∈ (HPolytope.ineqs Hx hx).construct) : -- --- CONCL ---
    Γ *ᵥ p - β ∈ (HPolytope.ineqs Hy hy).construct := by -- --- PROOF ---
  rw [HPolytope.mem_ineqs_iff] at hp ⊢
  intro i
  -- `Hy Γ p = Λ Hx p`, and a nonnegative row of `Λ` keeps `Hx p ≤ hx`
  have hmono : (Λ *ᵥ (Hx *ᵥ p)) i ≤ (Λ *ᵥ hx) i := by
    simp only [mulVec, dotProduct]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hp j) (hΛ i j)
  have heq : (Hy *ᵥ (Γ *ᵥ p - β)) i = (Λ *ᵥ (Hx *ᵥ p)) i - (Hy *ᵥ β) i := by
    rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, h1, Pi.sub_apply]
  have h2i := h2 i
  rw [Pi.add_apply] at h2i
  rw [heq]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
