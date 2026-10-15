module

public import CORALean.ContSet.ConZonotope.Float.Operations.AnchorSlab
public import CORALean.ContSet.ConZonotope.Float.Theorems.MemNominalSet
public import CORALean.ContSet.HPolytope.Float.Operations.MemSlabNominalIff
public import CORALean.ContSet.HPolytope.Float.Operations.MemStackRowsNominalIff
public import CORALean.ContSet.HPolytope.Float.Operations.MulVecAppendLeft
public import CORALean.Global.Float.ToRealMatMulVec
public import CORALean.ContSet.HPolytope.Float.Theorems.AnchorEqsInBoxSound

@[expose] public section

/-!
# `ConZonotope.anchorSlab` contains the slab version

A point `y + e` of the constrained zonotope with the rows added as the slab `lo ≤ A β ≤ hi`, so
`y` described by coefficients `β` of the box that meet the old constraints and read between `lo`
and `hi` on the new rows, and `e` in the error box, lies in the result on either branch. With
the certificate, `β` meets the stacked rows of the anchoring polytope, the old equalities
exactly and the new ones within `hi - lo`, so `HPolytope.anchorEqsInBox_sound` moves it to a
`β''` of the box on all of them, by at most `τ`; the point `y''` that `β''` describes is within
`∑ⱼ |Gⱼᵢ| τ` of `y`, which the widened box takes. Without, the result is the slab version.
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.anchorSlab_outer (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) (A : Mat 𝕋 q cZ.h)
    (lo hi : Vec 𝕋 q) :
    ({ cZ with P := cZ.P.stackRows (HPolytope.slab A lo hi) } : ConZonotope 𝕋 (Vec 𝕋 n)).construct
      ⊆ (cZ.anchorSlab A lo hi).construct := by -- --- PROOF ---
  rintro _ ⟨y, hy', e, he, rfl⟩
  obtain ⟨β, hβ, hPs, hy⟩ := ConZonotope.mem_nominalSet_iff.mp hy'
  obtain ⟨hP, hsl⟩ := HPolytope.mem_stackRows_nominal_iff.mp hPs
  have hslab := HPolytope.mem_slab_nominal_iff.mp hsl
  unfold ConZonotope.anchorSlab
  dsimp only
  split
  · rename_i Q' τ hQ
    obtain ⟨hle, heq⟩ := HPolytope.mem_nominal_iff.mp hP
    -- `β` meets the stacked rows: the old ones as they are, the new ones within `hi - lo`
    obtain ⟨hτ0, β'', hbox, hmem, hmove⟩ := HPolytope.anchorEqsInBox_sound hQ β hβ
      (fun k => by
        refine Fin.addCases (fun k => ?_) (fun k => k.elim0) k
        show (toRealMat (Fin.append cZ.P.A fun i => i.elim0) *ᵥ β) (Fin.castAdd 0 k)
          ≤ toReal (Fin.append cZ.P.b (fun i => i.elim0) (Fin.castAdd 0 k))
        rw [HPolytope.mulVec_append_left, Fin.append_left]
        exact hle k)
      (fun i => by
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        -- the old equalities hold exactly
        · show |(toRealMat (Fin.append cZ.P.Ae A) *ᵥ β) (Fin.castAdd q i)
              - toReal (Fin.append cZ.P.be hi (Fin.castAdd q i))|
            ≤ toReal (Fin.append (fun _ => (zero : 𝕋)) (fun i => subUp (hi i) (lo i))
              (Fin.castAdd q i))
          rw [HPolytope.mulVec_append_left, Fin.append_left, Fin.append_left, heq i, sub_self,
            abs_zero, toReal_zero]
        -- the new ones within the gap
        · show |(toRealMat (Fin.append cZ.P.Ae A) *ᵥ β) (Fin.natAdd cZ.P.me i)
              - toReal (Fin.append cZ.P.be hi (Fin.natAdd cZ.P.me i))|
            ≤ toReal (Fin.append (fun _ => (zero : 𝕋)) (fun i => subUp (hi i) (lo i))
              (Fin.natAdd cZ.P.me i))
          rw [toRealMat_append_mulVec_natAdd, Fin.append_right, Fin.append_right, abs_le]
          have h := sub_le_subUp (hi i) (lo i)
          constructor <;> linarith [(hslab i).1, (hslab i).2])
    -- the point `β''` describes, and the move from `y` to it
    set y'' : Vec ℝ n := fun i => toReal (cZ.c i) + ∑ j, toReal (cZ.G j i) * β'' j
    have hsplit : y + e = y'' + (y - y'' + e) := by abel
    rw [hsplit]
    refine Set.add_mem_add (ConZonotope.mem_nominalSet_iff.mpr ⟨β'', hbox, hmem, fun i => rfl⟩)
      fun i => ?_
    set w := mulUp (sumUp fun j => absolute (cZ.G j i)) τ with hw
    have hdiff : |y i - y'' i| ≤ toReal w := by
      have hyi : y i - y'' i = ∑ j, toReal (cZ.G j i) * (β j - β'' j) := by
        rw [hy i]
        simp only [y'', mul_sub, Finset.sum_sub_distrib]
        ring
      have hsum := sum_le_sumUp fun j => absolute (cZ.G j i)
      simp only [toReal_absolute] at hsum
      -- the move, generator by generator
      rw [hyi]
      calc |∑ j, toReal (cZ.G j i) * (β j - β'' j)|
          ≤ ∑ j, |toReal (cZ.G j i)| * toReal τ := by
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
            rw [abs_mul, abs_sub_comm]
            exact mul_le_mul_of_nonneg_left (hmove j) (abs_nonneg _)
        _ = (∑ j, |toReal (cZ.G j i)|) * toReal τ := (Finset.sum_mul _ _ _).symm
        _ ≤ toReal (sumUp fun j => absolute (cZ.G j i)) * toReal τ :=
            mul_le_mul_of_nonneg_right hsum hτ0
        _ ≤ _ := mul_le_mulUp _ _
    -- the widened box takes the move
    have hlo : toReal (cZ.I_error.inf i) ≤ e i := (he i).1
    have hhi : e i ≤ toReal (cZ.I_error.sup i) := (he i).2
    have h1 := subDown_le_sub (cZ.I_error.inf i) w
    have h2 := add_le_addUp (cZ.I_error.sup i) w
    have hab := abs_le.mp hdiff
    refine ⟨?_, ?_⟩
    · show toReal (subDown (cZ.I_error.inf i) w) ≤ (y - y'' + e) i
      simp only [Pi.add_apply, Pi.sub_apply]
      linarith
    · show (y - y'' + e) i ≤ toReal (addUp (cZ.I_error.sup i) w)
      simp only [Pi.add_apply, Pi.sub_apply]
      linarith
  -- without a certificate: the slab version itself
  · exact Set.add_mem_add hy' he

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
