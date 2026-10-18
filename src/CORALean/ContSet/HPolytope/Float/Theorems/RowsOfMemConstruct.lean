module

public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

@[expose] public section

/-!
# The rows of a polytope with an error box, as its points read them

A point of `nominal ⊕ box` is a nominal point plus a box point. Each row reads the first at
most its right-hand side and the second at most `errUp`, so the point reads the row at most
the right-hand side with the box folded in (`bU`, `beU`, `beLN`). This is how an operation
that reads the rows sees a polytope that carries a box.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The most the row `a` reads on the error box: a linear function of one coordinate is largest
at one end of its range, so each term is bounded by the end its sign picks, and the terms are
summed upward. -/
private theorem HPolytope.le_errUp (P : HPolytope 𝕋 (Vec 𝕋 n)) (a : Vec 𝕋 n) {e : Vec ℝ n}
    (he : e ∈ P.I_error.construct) :
    ∑ j, toReal (a j) * e j ≤ toReal (P.errUp a) := by -- --- PROOF ---
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) (sum_le_sumUp _)
  have hlo : toReal (P.I_error.inf j) ≤ e j := (he j).1
  have hhi : e j ≤ toReal (P.I_error.sup j) := (he j).2
  rw [toReal_maximum]
  rcases le_total 0 (toReal (a j)) with hs | hs
  · refine le_trans ?_ (le_max_left _ _)
    exact le_trans (mul_le_mul_of_nonneg_left hhi hs) (mul_le_mulUp _ _)
  · refine le_trans ?_ (le_max_right _ _)
    exact le_trans (mul_le_mul_of_nonpos_left hlo hs) (mul_le_mulUp _ _)


theorem HPolytope.rows_of_mem_construct {P : HPolytope 𝕋 (Vec 𝕋 n)} {x : Vec ℝ n}
    (hx : x ∈ P.construct) : -- --- STMT ---
    (∀ i, (toRealMat P.A *ᵥ x) i ≤ toReal (P.bU i)) ∧
      ∀ i, (toRealMat P.Ae *ᵥ x) i ≤ toReal (P.beU i)
        ∧ -(toRealMat P.Ae *ᵥ x) i ≤ toReal (P.beLN i) := by -- --- PROOF ---
  obtain ⟨y, hy, e, he, rfl⟩ := Set.mem_add.mp hx
  obtain ⟨hle, heq⟩ := HPolytope.mem_nominal_iff.mp hy
  -- a row reads the sum as the sum of what it reads
  have hrow : ∀ {k : ℕ} (M : Mat 𝕋 k n) (i : Fin k),
      (toRealMat M *ᵥ (y + e)) i = (toRealMat M *ᵥ y) i + ∑ j, toReal (M i j) * e j := by
    intro k M i
    rw [Matrix.mulVec_add, Pi.add_apply]
    rfl
  -- an inequality row, then the two halves of an equality
  refine ⟨fun i => ?_, fun i => ⟨?_, ?_⟩⟩
  · rw [hrow]
    have h := add_le_addUp (addUp (P.b i) (absolute (P.b_error i))) (P.errUp (P.A i))
    have h₀ := add_le_addUp (P.b i) (absolute (P.b_error i))
    have h' := P.le_errUp (P.A i) he
    have := hle i
    rw [toReal_absolute] at h₀
    show _ ≤ toReal (addUp (addUp (P.b i) (absolute (P.b_error i))) (P.errUp (P.A i)))
    linarith
  · rw [hrow]
    have h := add_le_addUp (addUp (P.be i) (absolute (P.be_error i))) (P.errUp (P.Ae i))
    have h₀ := add_le_addUp (P.be i) (absolute (P.be_error i))
    have h' := P.le_errUp (P.Ae i) he
    have := (abs_le.mp (heq i)).2
    rw [toReal_absolute] at h₀
    show _ ≤ toReal (addUp (addUp (P.be i) (absolute (P.be_error i))) (P.errUp (P.Ae i)))
    linarith
  -- the lower half, as the row negated
  · rw [hrow]
    have h := add_le_addUp (addUp (neg (P.be i)) (absolute (P.be_error i))) (P.errUp (-(P.Ae i)))
    have h₀ := add_le_addUp (neg (P.be i)) (absolute (P.be_error i))
    have h' := P.le_errUp (-(P.Ae i)) he
    have := (abs_le.mp (heq i)).1
    rw [toReal_absolute, toReal_neg] at h₀
    simp only [Pi.neg_apply, toReal_neg', neg_mul, Finset.sum_neg_distrib] at h h'
    show _ ≤ toReal (addUp (addUp (neg (P.be i)) (absolute (P.be_error i))) (P.errUp (-(P.Ae i))))
    linarith

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
