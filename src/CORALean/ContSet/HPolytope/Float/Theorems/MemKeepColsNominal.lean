module

public import CORALean.ContSet.HPolytope.Float.Operations.KeepCols
public import CORALean.ContSet.HPolytope.Float.Theorems.MemNominalIff

@[expose] public section

/-!
# What `HPolytope.keepCols` keeps

A point of the nominal part whose dropped coordinates lie in `[-1, 1]` keeps its kept ones in the
result: each row splits along the partition (`Partition.sum_split₂`), and the dropped part reads
at most the row's absolute sum over the dropped columns either way, which the slack has gained.

## Inputs
* `P` – H-polytope
* `part` – split of the coordinates into `q` kept and `r` dropped
* `x` – point of length `n`

## Hypotheses
* `hP` – `x` lies in `P.nominal`
* `hx` – the dropped coordinates of `x` lie in `[-1, 1]`

## Conclusion
* the kept coordinates of `x` lie in the nominal part of `keepCols`
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q r : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- A row's dropped part, against coordinates in `[-1, 1]`, reads at most the row's rounded
absolute sum over the dropped columns either way. -/
private theorem HPolytope.aux_abs_dropped_le {k : ℕ} (M : Mat 𝕋 k n)
    (part : Split (Fin n) into (Fin q) ⊕ (Fin r)) {x : Vec ℝ n}
    (hx : ∀ l, |x (part.right l)| ≤ 1) (i : Fin k) : -- --- CONCL ---
    |∑ l, toReal (M i (part.right l)) * x (part.right l)|
      ≤ toReal (radius (fun i l => M i (part.right l)) i) := by -- --- PROOF ---
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun l _ => ?_)
    (sum_abs_le_radius (d := fun i l => M i (part.right l)) i))
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_left (hx l) (abs_nonneg (toReal (M i (part.right l))))


-- =======================================  MAIN THEOREM  ======================================= --

/-- The kept coordinates of a nominal point with its dropped ones in `[-1, 1]` are in the
result's nominal part. -/
theorem HPolytope.mem_keepCols_nominal (P : HPolytope 𝕋 (Vec 𝕋 n))
    (part : Split (Fin n) into (Fin q) ⊕ (Fin r)) {x : Vec ℝ n}
    (hP : x ∈ P.nominal.construct) (hx : ∀ l, |x (part.right l)| ≤ 1) : -- --- CONCL ---
    (fun l => x (part.left l)) ∈ (P.keepCols part).nominal.construct := by -- --- PROOF ---
  obtain ⟨hin, heq⟩ := HPolytope.mem_nominal_iff.mp hP
  -- a row splits along the partition
  have hsplit : ∀ {k : ℕ} (M : Mat 𝕋 k n) (i : Fin k),
      (toRealMat M *ᵥ x) i = ∑ l, toReal (M i (part.left l)) * x (part.left l)
        + ∑ l, toReal (M i (part.right l)) * x (part.right l) := fun M i =>
    part.sum_split₂ fun j => toReal (M i j) * x j
  refine HPolytope.mem_nominal_iff.mpr ⟨fun i => ?_, fun i => ?_⟩
  -- an inequality: the dropped part is paid by the slack
  · have hd := abs_le.mp (HPolytope.aux_abs_dropped_le P.A part hx i)
    have hu := add_le_addUp (absolute (P.b_error i)) (radius (fun i l => P.A i (part.right l)) i)
    rw [toReal_absolute] at hu
    have hk := hin i
    rw [hsplit] at hk
    show ∑ l, toReal (P.A i (part.left l)) * x (part.left l) ≤ toReal (P.b i)
      + |toReal (addUp (absolute (P.b_error i)) (radius (fun i l => P.A i (part.right l)) i))|
    linarith [hd.1, le_abs_self (toReal (addUp (absolute (P.b_error i))
      (radius (fun i l => P.A i (part.right l)) i)))]
  -- an equality: the same, on both sides
  · have hd := abs_le.mp (HPolytope.aux_abs_dropped_le P.Ae part hx i)
    have hu := add_le_addUp (absolute (P.be_error i))
      (radius (fun i l => P.Ae i (part.right l)) i)
    rw [toReal_absolute] at hu
    have hk := abs_le.mp (heq i)
    rw [hsplit] at hk
    show |∑ l, toReal (P.Ae i (part.left l)) * x (part.left l) - toReal (P.be i)|
      ≤ |toReal (addUp (absolute (P.be_error i)) (radius (fun i l => P.Ae i (part.right l)) i))|
    have hw := le_abs_self (toReal (addUp (absolute (P.be_error i))
      (radius (fun i l => P.Ae i (part.right l)) i)))
    rw [abs_le]
    constructor <;> linarith [hd.1, hd.2, hk.1, hk.2]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
