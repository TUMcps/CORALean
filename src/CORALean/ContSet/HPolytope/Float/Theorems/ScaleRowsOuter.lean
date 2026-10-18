module

public import CORALean.ContSet.HPolytope.Float.Operations.ScaleRows
public import CORALean.ContSet.HPolytope.Float.Theorems.AnchorEqsOuter
public import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct
public import CORALean.ContSet.HPolytope.Float.Theorems.ScaleDevBetween

@[expose] public section

/-!
# `HPolytope.scaleRows` keeps every point of the polytope inside the domain

Each row is multiplied by a number, positive for an inequality, and the stored row `ṽ` is `s v`
rounded down. For a point of the polytope in the domain, `ṽᵀ x = s vᵀ x - (s v - ṽ)ᵀ x`, the first
term bounded by the scaled right-hand side (rounded up; for an equality it is that right-hand side
scaled, rounded both ways) and the second from below by `scaleDevLo` (from above by `scaleDevHi`,
for the lower end of an equality). So the point meets every scaled inequality at
the stored right-hand side, and reads every scaled equality within the gap `anchorEqs` is given
(`HPolytope.anchorEqs_outer`). Outer over the domain: the rounding of the rows, which names other
halfspaces, is paid on the right-hand sides there, as `reduceOverDomain_outer` does.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       12-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.scaleRows_outer (P : HPolytope 𝕋 (Vec 𝕋 n)) (hP : P.ErrFree)
    (sA : Fin P.m → 𝕋) (sE : Fin P.me → 𝕋)
    (hA : ∀ i, 0 < toReal (sA i)) (dom : Interval (Vec 𝕋 n)) : -- --- STMT ---
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
  rw [← add_zero x]
  refine HPolytope.anchorEqs_outer _ _ (fun i => ?_) (fun i => ?_) ?_
  · -- an inequality row: the deviation's lower end, the right-hand side rounded up
    refine le_add_of_le_of_nonneg ?_ (abs_nonneg _)
    have hdev := (HPolytope.scaleDev_between (P.A i) (sA i) dom hd).1
    have hb1 := mul_le_mulUp (P.b i) (sA i)
    have hsub := sub_le_subUp (mulUp (P.b i) (sA i)) (HPolytope.scaleDevLo (P.A i) (sA i) dom)
    have hscaled := mul_le_mul_of_nonneg_left (h1 i) (hA i).le
    show (toRealMat (fun i j => mulDown (P.A i j) (sA i)) *ᵥ x) i
      ≤ toReal (subUp (mulUp (P.b i) (sA i)) (HPolytope.scaleDevLo (P.A i) (sA i) dom))
    rw [hsplit P.A sA i]
    linarith
  · -- an equality row reads between the deviation's two ends
    set U := subUp (mulUp (P.be i) (sE i)) (HPolytope.scaleDevLo (P.Ae i) (sE i) dom) with hU
    set L := subDown (mulDown (P.be i) (sE i)) (HPolytope.scaleDevHi (P.Ae i) (sE i) dom) with hL
    obtain ⟨hdlo, hdhi⟩ := HPolytope.scaleDev_between (P.Ae i) (sE i) dom hd
    have hu1 := mul_le_mulUp (P.be i) (sE i)
    have hu2 : toReal (mulUp (P.be i) (sE i)) - toReal (HPolytope.scaleDevLo (P.Ae i) (sE i) dom)
        ≤ toReal U := sub_le_subUp _ _
    have hl1 := mulDown_le_mul (P.be i) (sE i)
    have hl2 : toReal L ≤ toReal (mulDown (P.be i) (sE i))
        - toReal (HPolytope.scaleDevHi (P.Ae i) (sE i) dom) := subDown_le_sub _ _
    have hgap := sub_le_subUp U L
    have hs : toReal (sE i) * (toRealMat P.Ae *ᵥ x) i = toReal (sE i) * toReal (P.be i) := by
      rw [h2 i]
    show |(toRealMat (fun i j => mulDown (P.Ae i j) (sE i)) *ᵥ x) i - toReal U|
      ≤ toReal (subUp U L)
    rw [hsplit P.Ae sE i, abs_le]
    constructor <;> linarith
  · -- the scaled rows carry the origin box
    intro j
    show toReal (zero : 𝕋) ≤ 0 ∧ 0 ≤ toReal (zero : 𝕋)
    rw [toReal_zero]
    exact ⟨le_rfl, le_rfl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
