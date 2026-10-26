module

public import CORALean.Specification.STL.Operations.UnsafeFactors
public import CORALean.Specification.STL.Operations.UnsafeFactorsFloat
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The float factors that may reach a polytope enclose the real ones on the box

A factor `α̃` in the box `[-1, 1]^p` that lies in `unsafeFactors` of the data read as reals
satisfies every row of `unsafeFactorsFloat`: the real row `C G(·,H)` lies between the rows rounded
down and up, so the stored one misses it by at most their gap, which the box turns into the slack
`radius` the offset carries; the offset itself is rounded up term by term.

## Inputs
* `C` – polytope matrix
* `d` – polytope offsets
* `c` – center of the reachable set
* `G` – generator matrix
* `H` – generator selection
* `K` – generators carrying only uncertainty
* `α` – factor vector

## Hypotheses
* `hp` – the selection fits the factor dimension
* `hbox` – the factors lie in the box `[-1, 1]^p`
* `hα` – the factors lie in the real set

## Conclusion
* the factors satisfy every row of the float polytope
-/

-- Authors:       Claude Opus 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n s γ h p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.unsafeFactorsFloat_outer (C : Mat 𝕋 s n) (d : Vec 𝕋 s) (c : Vec 𝕋 n)
    (G : Mat 𝕋 n γ) (H : Fin h → Fin γ) (K : Finset (Fin γ)) (hp : h ≤ p) (α : Fin p → ℝ)
    (hbox : ∀ l, |α l| ≤ 1)
    (hα : α ∈ STL.unsafeFactors (toRealMat C) (toRealVec d) (toRealVec c) (toRealMat G) H K
      hp) : -- --- CONCL ---
    ∀ r, ∑ i, toReal ((STL.unsafeFactorsFloat C d c G H K).1 r i) * α (Fin.castLE hp i) ≤
      toReal ((STL.unsafeFactorsFloat C d c G H K).2 r) := by -- --- PROOF ---
  intro r
  set M := toRealMat C * toRealMat G with hM
  -- the real product lies between the products rounded down and up
  have hlo : ∀ r j, toReal (matMulDown C G r j) ≤ M r j := fun r j => by
    rw [hM, Matrix.mul_apply]; exact dotDown_le _ _
  have hhi : ∀ r j, M r j ≤ toReal (matMulUp C G r j) := fun r j => by
    rw [hM, Matrix.mul_apply]; exact le_dotUp _ _
  -- the stored rows miss the real ones by at most the slack on the box
  have hgap : |∑ i, (M r (H i) - toReal (matMulDown C G r (H i))) * α (Fin.castLE hp i)| ≤
      toReal (radius (fun r i => subUp (matMulUp C G r (H i)) (matMulDown C G r (H i))) r) := by
    refine abs_sum_le_radius (Δ := fun r i => M r (H i) - toReal (matMulDown C G r (H i)))
      (β := fun i => α (Fin.castLE hp i)) (fun r' i => ?_) (fun i => hbox _) r
    have h1 := hlo r' (H i)
    have h2 := le_trans (sub_le_sub_right (hhi r' (H i)) (toReal (matMulDown C G r' (H i))))
      (sub_le_subUp _ _)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (le_trans (by linarith) h2)]
    exact h2
  -- the uncertain generators: their absolute products, each bounded by the larger end
  set unc : 𝕋 := sumUp fun k => if k ∈ K then
    maximum (absolute (matMulDown C G r k)) (absolute (matMulUp C G r k)) else zero with hunc_def
  have hunc : ∑ k ∈ K, |M r k| ≤ toReal unc := by
    refine le_trans ?_ (sum_le_sumUp _)
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ K)]
    rw [show Finset.univ.filter (· ∈ K) = K by ext; simp]
    refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun k hk => ?_)
      (Finset.sum_nonneg fun k hk => ?_)
    · rw [if_pos hk, toReal_maximum, toReal_absolute, toReal_absolute]
      exact abs_le_max_abs_abs (hlo r k) (hhi r k)
    · rw [Finset.mem_filter] at hk
      rw [if_neg hk.2, toReal_zero]
  -- the center term, rounded down
  have hcen : toReal (dotDown (C r) c) ≤ (toRealMat C).mulVec (toRealVec c) r := dotDown_le _ _
  -- the real row, from the stored one and the gap
  have hsplit : ∑ i, toReal (matMulDown C G r (H i)) * α (Fin.castLE hp i) =
      ∑ i, M r (H i) * α (Fin.castLE hp i) -
        ∑ i, (M r (H i) - toReal (matMulDown C G r (H i))) * α (Fin.castLE hp i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hreal := hα r
  have hd : toRealVec d r = toReal (d r) := rfl
  show ∑ i, toReal (matMulDown C G r (H i)) * α (Fin.castLE hp i) ≤ toReal (addUp (addUp
    (subUp (d r) (dotDown (C r) c)) _) _)
  rw [hsplit]
  -- the offset, rounded up term by term
  have a1 := add_le_addUp (subUp (d r) (dotDown (C r) c)) unc
  have a2 := add_le_addUp (addUp (subUp (d r) (dotDown (C r) c)) unc)
    (radius (fun r i => subUp (matMulUp C G r (H i)) (matMulDown C G r (H i))) r)
  have hs := sub_le_subUp (d r) (dotDown (C r) c)
  have hab := neg_abs_le (∑ i, (M r (H i) - toReal (matMulDown C G r (H i))) *
    α (Fin.castLE hp i))
  rw [hd] at hreal
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
