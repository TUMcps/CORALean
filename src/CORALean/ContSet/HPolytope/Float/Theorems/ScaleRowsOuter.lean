module

public import CORALean.ContSet.HPolytope.Float.Operations.ScaleRows
public import CORALean.ContSet.HPolytope.Float.Theorems.MemSetRhsNominal
public import CORALean.ContSet.HPolytope.Float.Theorems.Basic
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners

@[expose] public section

/-!
# `HPolytope.scaleRows` keeps every point of the polytope inside the domain

Each row is multiplied by a number, positive for an inequality, and the stored row `ṽ` is `s v`
rounded down. For a point of the polytope in the domain, `ṽᵀ x = s vᵀ x - (s v - ṽ)ᵀ x`: the first
term is at most `s b` (for an equality it is `s bₑ`), and the second lies between `aux_scaleDevLo`
and `aux_scaleDevHi`. So the point reads every scaled row within its (zero) slack of
`s b - (s v - ṽ)ᵀ x`, a value between the two ends `setRhs` is given
(`HPolytope.mem_setRhs_nominal`). Outer over the domain: the rounding of the rows, which names other
halfspaces, is paid in the slacks there, as `reduceOverDomain_outer` pays it on the right-hand side.

## Inputs
* `P` – H-polytope
* `sA` – scalars indexed by `Fin P.m`
* `sE` – scalars indexed by `Fin P.me`
* `dom` – domain interval

## Hypotheses
* `hP` – `P.IsErrFree`
* `hA` – every inequality scaling `sA i` is positive

## Conclusion
* inside `dom`, the scaled polytope contains the error-free one
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   19-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- What rounding a scaled row costs, bounded over a domain. -/
theorem HPolytope.aux_scaleDev_between (v : Vec 𝕋 n) (s : 𝕋) (dom : Interval (Vec 𝕋 n))
    {x : Vec ℝ n} (hx : x ∈ dom.construct) : -- --- CONCL ---
    toReal (HPolytope.aux_scaleDevLo v s dom)
        ≤ ∑ j, (toReal s * toReal (v j) - toReal (mulDown (v j) s)) * x j
      ∧ ∑ j, (toReal s * toReal (v j) - toReal (mulDown (v j) s)) * x j
        ≤ toReal (HPolytope.aux_scaleDevHi v s dom) := by -- --- PROOF ---
  have hdev : ∀ j, toReal (subDown (mulDown (v j) s) (mulDown (v j) s))
        ≤ toReal s * toReal (v j) - toReal (mulDown (v j) s)
      ∧ toReal s * toReal (v j) - toReal (mulDown (v j) s)
        ≤ toReal (subUp (mulUp (v j) s) (mulDown (v j) s)) := by
    intro j
    have h3 := mulDown_le_mul (v j) s
    have h4 := mul_le_mulUp (v j) s
    have h5 := subDown_le_sub (mulDown (v j) s) (mulDown (v j) s)
    have h6 := sub_le_subUp (mulUp (v j) s) (mulDown (v j) s)
    constructor <;> nlinarith
  have hxj : ∀ j, toReal (dom.inf j) ≤ x j ∧ x j ≤ toReal (dom.sup j) := hx
  have hprod := fun j => Interval.mul_between_corners (hdev j).1 (hdev j).2 (hxj j).1 (hxj j).2
  exact ⟨le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun j _ => (hprod j).1),
    le_trans (Finset.sum_le_sum fun j _ => (hprod j).2) (sum_le_sumUp _)⟩


-- =======================================  MAIN THEOREM  ======================================= --

/-- Inside `dom`, the scaled polytope contains the error-free one. -/
theorem HPolytope.scaleRows_outer (P : HPolytope 𝕋 (Vec 𝕋 n)) (hP : P.IsErrFree)
    (sA : Fin P.m → 𝕋) (sE : Fin P.me → 𝕋)
    (hA : ∀ i, 0 < toReal (sA i)) (dom : Interval (Vec 𝕋 n)) : -- --- CONCL ---
    P.construct ∩ dom.construct ⊆
      (P.scaleRows sA sE dom).construct ∩ dom.construct := by -- --- PROOF ---
  -- a point of the polytope in the domain, and its two blocks of rows
  rintro x ⟨hP', hd⟩
  refine ⟨?_, hd⟩
  obtain ⟨h1, h2⟩ := (HPolytope.mem_construct_iff hP).mp hP'
  -- the stored row is the scaled row less the deviation
  have hsplit : ∀ {k : ℕ} (M : Mat 𝕋 k n) (s : Fin k → 𝕋) (i : Fin k),
      (toRealMat (fun i j => mulDown (M i j) (s i)) *ᵥ x) i
        = toReal (s i) * (toRealMat M *ᵥ x) i
          - ∑ j, (toReal (s i) * toReal (M i j) - toReal (mulDown (M i j) (s i))) * x j := by
    intro k M s i
    simp only [mulVec, dotProduct, toRealMat, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the exact bound of a scaled row at `x`, and its two ends
  have hends : ∀ {k : ℕ} (M : Mat 𝕋 k n) (c s : Fin k → 𝕋) (i : Fin k),
      toReal (subDown (mulDown (c i) (s i)) (HPolytope.aux_scaleDevHi (M i) (s i) dom))
          ≤ toReal (s i) * toReal (c i)
            - ∑ j, (toReal (s i) * toReal (M i j) - toReal (mulDown (M i j) (s i))) * x j
        ∧ toReal (s i) * toReal (c i)
            - ∑ j, (toReal (s i) * toReal (M i j) - toReal (mulDown (M i j) (s i))) * x j
          ≤ toReal (subUp (mulUp (c i) (s i)) (HPolytope.aux_scaleDevLo (M i) (s i) dom)) := by
    intro k M c s i
    obtain ⟨hlo, hhi⟩ := HPolytope.aux_scaleDev_between (M i) (s i) dom hd
    have h1 := mulDown_le_mul (c i) (s i)
    have h2 := subDown_le_sub (mulDown (c i) (s i)) (HPolytope.aux_scaleDevHi (M i) (s i) dom)
    have h3 := mul_le_mulUp (c i) (s i)
    have h4 := sub_le_subUp (mulUp (c i) (s i)) (HPolytope.aux_scaleDevLo (M i) (s i) dom)
    constructor <;> nlinarith
  refine (HPolytope.mem_nominal_of_origin rfl).mpr (HPolytope.mem_setRhs_nominal _ _ _
    (fun i => hends P.A P.b sA i) (fun i => hends P.Ae P.be sE i) (fun i => ?_) (fun i => ?_))
  · -- an inequality row: the scaled row at most the scaled bound
    have hscaled := mul_le_mul_of_nonneg_left (h1 i) (hA i).le
    show (toRealMat (fun i j => mulDown (P.A i j) (sA i)) *ᵥ x) i ≤ _ + |toReal (zero : 𝕋)|
    rw [hsplit P.A sA i, toReal_zero, abs_zero, add_zero]
    linarith
  · -- an equality row: the scaled row is the scaled bound
    show |(toRealMat (fun i j => mulDown (P.Ae i j) (sE i)) *ᵥ x) i - _| ≤ |toReal (zero : 𝕋)|
    rw [hsplit P.Ae sE i, h2 i, toReal_zero, abs_zero, abs_nonpos_iff]
    ring

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
