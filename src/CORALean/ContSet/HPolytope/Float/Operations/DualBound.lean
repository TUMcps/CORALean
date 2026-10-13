import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
import CORALean.Global.Float.FloatBound

/-!
# Where a float halfspace description's own bounds come from

Weak duality again, at this layer's row structure. An equality row here is an
interval one, so it is two inequalities — `Ae x ≤ be.sup` and
`-Ae x ≤ -be.inf` — and a dual solution is three nonnegative vectors rather
than a nonnegative one and a free one. The interval right-hand side therefore
needs no special case; it is the reason there is none.

The value is `dotUp`, rounded away from the set, so it is a float and still a
bound.

Dual feasibility is stated over ℝ and is the caller's to discharge, which is
deliberate: a float dual solution does not reproduce `c` exactly, and forcing it
to here would make the certificate unusable. The gap is paid by `addDir`
instead — bound `c - yᵀA` over any enclosure already in hand and add the two.
That keeps the rounding where it can be measured rather than hidden in a
definition.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def HPolytope.boundOfDual (P : HPolytope 𝕋 (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (y : Vec 𝕋 P.m) (zu zl : Vec 𝕋 P.me)
    (hy : ∀ i, 0 ≤ toReal (y i)) (hzu : ∀ i, 0 ≤ toReal (zu i))
    (hzl : ∀ i, 0 ≤ toReal (zl i))
    (hc : ∀ x : Vec ℝ n, c x =
      (∑ i, toReal (y i) * (toRealMat P.A *ᵥ x) i)
        + (∑ i, toReal (zu i) * (toRealMat P.Ae *ᵥ x) i)
        - ∑ i, toReal (zl i) * (toRealMat P.Ae *ᵥ x) i) :
    FloatBound 𝕋 P.construct c where
  val := addUp (dotUp y P.b) (addUp (dotUp zu P.be.sup) (dotUp zl fun i => neg (P.be.inf i)))
  -- weak duality: every dual weight is nonnegative, so each term is capped by its own row
  le x hx := by
    obtain ⟨hle, heq⟩ := HPolytope.mem_construct_iff.mp hx
    have h1 : (∑ i, toReal (y i) * (toRealMat P.A *ᵥ x) i) ≤ toReal (dotUp y P.b) :=
      le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle i) (hy i))
        (le_dotUp _ _)
    have h2 : (∑ i, toReal (zu i) * (toRealMat P.Ae *ᵥ x) i)
        ≤ toReal (dotUp zu P.be.sup) :=
      le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (heq i).2 (hzu i))
        (le_dotUp _ _)
    have h3 : (∑ i, toReal (zl i) * (-(toRealMat P.Ae *ᵥ x) i))
        ≤ toReal (dotUp zl fun i => neg (P.be.inf i)) := by
      refine le_trans (Finset.sum_le_sum fun i _ => ?_) (le_dotUp _ _)
      rw [toReal_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_neg (heq i).1) (hzl i)
    -- the negated sum against its own negation, joined only by `Finset.sum_add_distrib`
    have hcancel : (∑ i, toReal (zl i) * (-(toRealMat P.Ae *ᵥ x) i))
        + ∑ i, toReal (zl i) * (toRealMat P.Ae *ᵥ x) i = 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun i _ => by ring
    have hround := add_le_addUp (dotUp y P.b)
      (addUp (dotUp zu P.be.sup) (dotUp zl fun i => neg (P.be.inf i)))
    have hround' := add_le_addUp (dotUp zu P.be.sup) (dotUp zl fun i => neg (P.be.inf i))
    rw [hc x]
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
