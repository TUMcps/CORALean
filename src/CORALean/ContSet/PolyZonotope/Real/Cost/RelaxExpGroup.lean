import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpGroup
import CORALean.ContSet.PolyZonotope.Real.Cost.RelaxWidthGroup

/-!
# `PolyZonotope.relaxExpGroupCost`

Asserted, not proved, at `Vec ℝ n`: `Operations/RelaxExpGroup.lean` merges `k`
generators into one of `d` kept ones. Summing the `k` merged generators is
`n * k` additions and adding that to the target `n`; the `d` kept generators
are each compared against the target index; and each of the `k` merged
generators gets its width over `p` factors and a scaling (`n`).
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxExpGroup` costs at `Vec ℝ n`, `p` factors, `d` kept
and `k` merged generators. -/
def PolyZonotope.relaxExpGroupCost (n p d k : ℕ) : Cost :=
  ⟨n * (k + 1) + d + k * n⟩ + k • PolyZonotope.relaxWidthGroupCost p

/-- Monotone in the factor and merged counts. -/
theorem PolyZonotope.relaxExpGroupCost_mono {p p' k k' : ℕ} (n d : ℕ) (hp : p ≤ p')
    (hk : k ≤ k') :
    PolyZonotope.relaxExpGroupCost n p d k ≤
      PolyZonotope.relaxExpGroupCost n p' d k' := by -- --- PROOF ---
  have a := PolyZonotope.relaxWidthGroupCost_mono hp
  simp only [PolyZonotope.relaxExpGroupCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul] at a ⊢
  have e := Nat.mul_le_mul hk a
  have f : n * (k + 1) + d + k * n ≤ n * (k' + 1) + d + k' * n := by
    have := Nat.mul_le_mul_left n hk
    have := Nat.mul_le_mul_right n hk
    rw [Nat.mul_succ, Nat.mul_succ]
    omega
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
