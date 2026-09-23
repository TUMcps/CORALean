import CORALean.ContSet.Interval.Real.Interval
import CORALean.NN.MergeBucket

/-!
# [1, Alg. 1]: the bucket tolerance a reduction rate asks for

[1, Alg. 1] turns a reduction rate `ρ` into merge buckets: grow `δmax` tenfold until at most
`ρ n_k` neurons would remain, then bisect `[δmin, δmax]` until the fraction remaining is `≈ ρ`,
and return the buckets at that `δ`. The buckets are those of [1, Eq. 5] or [1, Eq. 6], built at
each `δ` tried; a bucket is only ever used through the neurons it merges, so each is returned as
one mask, `true` on a merged neuron, and `n_k - Σ |B|` counts the rest.

Every decision goes through the caller's `le`, so the float layer transcribes this with
`FloatOps.le` and it runs. Neither loop is bounded in [1], and the first need not end (`δmax`
may start at `0`), so both take `fuel` and the result is an `Option`. [1] leaves `≈` open: it is
`|n̂_k/n_k - ρ| ≤ tol` here. Soundness asks nothing of any of this — Prop. 4 holds at every
bucket — so what `bucketTolerance_approx` proves is only line 16's exit condition.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}

/-- `max(u_k)`, and `0` over a layer with no neurons. -/
noncomputable def maxOver : {n : ℕ} → Vec ℝ n → ℝ
  | 0, _ => 0
  | _ + 1, v => Finset.univ.sup' Finset.univ_nonempty v

/-- `min(l_k)`, and `0` over a layer with no neurons. -/
noncomputable def minOver : {n : ℕ} → Vec ℝ n → ℝ
  | 0, _ => 0
  | _ + 1, v => Finset.univ.inf' Finset.univ_nonempty v

/-- [1, Def. 3]'s `I_k(i) ⊆ [y - δ, y + δ]`, decided by `le`. -/
def inMergeBucket (le : ℝ → ℝ → Bool) (I : Interval (Vec ℝ n)) (y δ : ℝ) (i : Fin n) : Bool :=
  le (y - δ) (I.inf i) && le (I.sup i) (y + δ)

/-- [1, Eq. 5]'s static buckets `B_{k,y,δ}`, one per asymptotic value `y`: a neuron is merged
when one of them holds it, and belongs to the first that does. -/
def staticMergeBuckets (le : ℝ → ℝ → Bool) (ys : List ℝ) (I : Interval (Vec ℝ n)) (δ : ℝ) :
    Fin n → Bool :=
  fun i => ys.any fun y => inMergeBucket le I y δ i

/-- [1, Eq. 6]'s dynamic buckets, one at each neuron's centre `c = (l_k + u_k)/2` in turn, kept
disjoint by skipping the neurons already merged and used only when they hold two or more. -/
noncomputable def dynamicMergeBuckets (le : ℝ → ℝ → Bool) (I : Interval (Vec ℝ n)) (δ : ℝ) :
    Fin n → Bool :=
  Fin.foldl n (fun merged j =>
      let c := (I.inf j + I.sup j) / 2                              -- [1, Eq. 6]'s `c(j)`
      let B_cδ := fun i => !merged i && inMergeBucket le I c δ i    -- `B_{k,c(j),δ}`, disjoint
      if 2 ≤ bucketed B_cδ then fun i => merged i || B_cδ i else merged)  -- used if not a singleton
    fun _ => false

/-- "Initialize merge buckets `B_{k,δ}`", whichever of [1]'s two ways (Sec. 3.2) the layer names. -/
noncomputable def initMergeBuckets (le : ℝ → ℝ → Bool) :
    MergeBuckets ℝ → Interval (Vec ℝ n) → ℝ → Fin n → Bool
  | .static ys => staticMergeBuckets le ys
  | .dynamic => dynamicMergeBuckets le

/-- Lines 2-6: `δmax` grown tenfold until at most `ρ n_k` neurons remain; `none` past `fuel`. -/
noncomputable def growBucketTolerance (le : ℝ → ℝ → Bool) (B : MergeBuckets ℝ)
    (I_k : Interval (Vec ℝ n)) (ρ : ℝ) : ℝ → ℕ → Option ℝ
  | _, 0 => none
  | δmax, fuel + 1 =>
    let δmax := 10 * δmax                                           -- Alg. 1, line 3
    let B_kδmax := initMergeBuckets le B I_k δmax                   -- Alg. 1, line 4
    let nhat_k := n - bucketed B_kδmax                              -- Alg. 1, line 5
    if le ((nhat_k : ℝ) / n) ρ then some δmax                       -- Alg. 1, line 6
    else growBucketTolerance le B I_k ρ δmax fuel

/-- Lines 7-16: bisect `[δmin, δmax]` until `n̂_k/n_k ≈ ρ`, returning the buckets at the `δ`
that stopped it; `none` past `fuel`. -/
noncomputable def bisectBucketTolerance (le : ℝ → ℝ → Bool) (tol : ℝ) (B : MergeBuckets ℝ)
    (I_k : Interval (Vec ℝ n)) (ρ : ℝ) : ℝ → ℝ → ℕ → Option (Fin n → Bool)
  | _, _, 0 => none
  | δmin, δmax, fuel + 1 =>
    let δ := (δmin + δmax) / 2                                      -- Alg. 1, line 8
    let B_kδ := initMergeBuckets le B I_k δ                         -- Alg. 1, line 9
    let nhat_k := n - bucketed B_kδ                                 -- Alg. 1, line 10
    let tooManyMerged := !le (ρ * n) nhat_k                         -- Alg. 1, line 11
    let δmax := if tooManyMerged then δ else δmax                   -- Alg. 1, line 12
    let δmin := if tooManyMerged then δmin else δ                   -- Alg. 1, line 14
    if le |(nhat_k : ℝ) / n - ρ| tol then some B_kδ                 -- Alg. 1, lines 16-17
    else bisectBucketTolerance le tol B I_k ρ δmin δmax fuel


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: the merge buckets `B_{k,δ}` of the layer bounded by `I_k = [l_k, u_k]` that
leave `≈ ρ n_k` of its neurons, `none` where `fuel` runs out first. -/
noncomputable def bucketTolerance (le : ℝ → ℝ → Bool) (tol : ℝ) (fuel : ℕ) (B : MergeBuckets ℝ)
    (I_k : Interval (Vec ℝ n)) (ρ : ℝ) : Option (Fin n → Bool) :=
  let δmin := (0 : ℝ)                                               -- Alg. 1, line 1
  let δmax := maxOver I_k.sup - minOver I_k.inf                     -- Alg. 1, line 1
  match growBucketTolerance le B I_k ρ δmax fuel with               -- Alg. 1, lines 2-6
  | none => none
  | some δmax => bisectBucketTolerance le tol B I_k ρ δmin δmax fuel  -- Alg. 1, lines 7-17

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
