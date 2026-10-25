module

public import CORALean.ContSet.Zonotope.Float.Operations.ErrUp
public import CORALean.ContSet.Zonotope.Float.Theorems.AbsLeAbsBoundError
public import CORALean.Global.Err

@[expose] public section

/-!
# `errUp` bounds `err`

Every set inside `Z`'s `construct` has its [1] eq. (11) `err` under `Z.errUp`: each point's
coordinate is under `absBoundError` (`abs_le_absBoundError`), `aux_err_le_norm₂_of_forall_abs_le`
turns that into a bound on `err` by the Euclidean norm of the magnitudes, and `norm₂_le_normUp`
bounds that norm from above: a Euclidean bound, which `Zonotope.errOp`, in the sup norm,
could not give.

## Inputs
* `Z` – zonotope
* `S` – subset of the zonotope

## Hypotheses
* `hS` – set lies in the zonotope

## Conclusion
* error of the set is at most the upper bound

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control, 2023.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

section
variable {n : ℕ}

/-- Squaring is monotone on magnitudes, so a coordinatewise bound on magnitudes is a bound on
the Euclidean norm. -/
theorem _root_.CORALean.aux_norm₂_le_of_abs_le_err {x y : Vec ℝ n}
    (h : ∀ i, |x i| ≤ |y i|) : ‖x‖₂ ≤ ‖y‖₂ := by
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have hi := mul_self_le_mul_self (abs_nonneg (x i)) (h i)
  rwa [abs_mul_abs_self, abs_mul_abs_self, ← pow_two, ← pow_two] at hi


/-- A coordinatewise bound on the magnitudes of `S` is a Euclidean bound on `err S`. -/
theorem _root_.CORALean.aux_err_le_norm₂_of_forall_abs_le {S : Set (Vec ℝ n)} {m : Vec ℝ n}
    (h : ∀ y ∈ S, ∀ i, |y i| ≤ |m i|) : -- --- CONCL ---
    err S ≤ ‖m‖₂ := by -- --- PROOF ---
  refine aux_norm₂_le_of_abs_le_err fun i => ?_
  rw [abs_of_nonneg (le_max_of_le_left (abs_nonneg _))]
  rcases Set.eq_empty_or_nonempty S with hS | ⟨y0, hy0⟩
  · simp [hS, Real.sSup_empty, Real.sInf_empty]
  -- both endpoints of the box at `i` are values of `S`-points at `i`, so `h` reaches
  have hA : ∀ z ∈ (fun x : Vec ℝ n => x i) '' S, z ≤ |m i| := by
    rintro _ ⟨y, hy, rfl⟩; exact (le_abs_self _).trans (h y hy i)
  have hB : ∀ z ∈ (fun x : Vec ℝ n => x i) '' S, -|m i| ≤ z := by
    rintro _ ⟨y, hy, rfl⟩; exact (abs_le.mp (h y hy i)).1
  have hbA : BddAbove ((fun x : Vec ℝ n => x i) '' S) := ⟨|m i|, hA⟩
  have hbB : BddBelow ((fun x : Vec ℝ n => x i) '' S) := ⟨-|m i|, hB⟩
  have hmemi : y0 i ∈ (fun x : Vec ℝ n => x i) '' S := ⟨y0, hy0, rfl⟩
  have hsup_le : sSup ((fun x : Vec ℝ n => x i) '' S) ≤ |m i| := csSup_le ⟨y0 i, hmemi⟩ hA
  have hsup_ge : -|m i| ≤ sSup ((fun x : Vec ℝ n => x i) '' S) :=
    (hB (y0 i) hmemi).trans (le_csSup hbA hmemi)
  have hinf_ge : -|m i| ≤ sInf ((fun x : Vec ℝ n => x i) '' S) := le_csInf ⟨y0 i, hmemi⟩ hB
  have hinf_le : sInf ((fun x : Vec ℝ n => x i) '' S) ≤ |m i| :=
    (csInf_le hbB hmemi).trans (hA (y0 i) hmemi)
  exact max_le (abs_le.mpr ⟨hsup_ge, hsup_le⟩) (abs_le.mpr ⟨hinf_ge, hinf_le⟩)

end


-- =======================================  MAIN THEOREM  ======================================= --

/-- `err S ≤ Z.errUp` for every `S` inside `Z`'s `construct`. -/
theorem Zonotope.err_le_errUp (Z : Zonotope (Vec 𝕋 n)) {S : Set (Vec ℝ n)}
    (hS : S ⊆ Zonotope.construct Z) : -- --- CONCL ---
    err S ≤ toReal Z.errUp := by -- --- PROOF ---
  have hnorm := norm₂_le_normUp (v := fun j => toReal (Z.absBoundError j))
    (m := fun j => Z.absBoundError j) 64 fun j => le_rfl
  refine le_trans (aux_err_le_norm₂_of_forall_abs_le (m := fun j => toReal (Z.absBoundError j))
    fun y hy i => ?_) hnorm
  exact (Zonotope.abs_le_absBoundError (hS hy) i).trans (le_abs_self _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
