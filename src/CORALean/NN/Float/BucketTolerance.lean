import CORALean.ContSet.Interval.Float.Interval
import CORALean.NN.MergeBucket

/-!
# [1, Alg. 1] over a floating-point scalar

`Real.bucketTolerance` line for line, every comparison `FloatOps.le` and every quantity a float:
`δmax` grows by `nsmulUp 10`, the bisection halves exactly, and `n̂_k/n_k` is `ratio`. Nothing
here is a soundness hypothesis — [1]'s Prop. 4 holds at every bucket — so which way anything
rounds is a choice of which buckets come out, never of whether the reduction is sound, and each
operation rounds whichever way reads simplest.

Like the exact layer's, both loops take `fuel` and return an `Option`.

## References

* [1] T. Ladner and M. Althoff. "Fully Automatic Neural Network Reduction for
      Formal Verification". TMLR. arXiv:2305.01932.
-/

-- Authors:       Tobias Ladner
-- Written:       23-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- `max(u_k)`, exact, and `zero` over a layer with no neurons. -/
def maxOver : {n : ℕ} → Vec 𝕋 n → 𝕋
  | 0, _ => zero
  | _ + 1, v => Fin.foldl _ (fun a i => maximum a (v i)) (v 0)

/-- `min(l_k)`, exact, and `zero` over a layer with no neurons. -/
def minOver : {n : ℕ} → Vec 𝕋 n → 𝕋
  | 0, _ => zero
  | _ + 1, v => Fin.foldl _ (fun a i => minimum a (v i)) (v 0)

/-- `a / b` for two counts, as a float. -/
def ratio (a b : ℕ) : 𝕋 := divDown (nsmulDown a one) (nsmulUp b one)

/-- [1, Def. 3]'s `I_k(i) ⊆ [y - δ, y + δ]`, decided by `FloatOps.le`. -/
def inMergeBucket (I : Interval 𝕋 n) (y δ : 𝕋) (i : Fin n) : Bool :=
  le (subDown y δ) (I.inf i) && le (I.sup i) (addUp y δ)

/-- [1, Eq. 5]'s static buckets, one per asymptotic value `y`: a neuron is merged when one of
them holds it, and belongs to the first that does. -/
def staticMergeBuckets (ys : List 𝕋) (I : Interval 𝕋 n) (δ : 𝕋) : Fin n → Bool :=
  fun i => ys.any fun y => inMergeBucket I y δ i

/-- [1, Eq. 6]'s dynamic buckets, one at each neuron's centre in turn, kept disjoint by
skipping the neurons already merged and used only when they hold two or more. -/
def dynamicMergeBuckets (I : Interval 𝕋 n) (δ : 𝕋) : Fin n → Bool :=
  Fin.foldl n (fun merged j =>
      let c := half (addUp (I.inf j) (I.sup j))                     -- [1, Eq. 6]'s `c(j)`
      let B_cδ := fun i => !merged i && inMergeBucket I c δ i       -- `B_{k,c(j),δ}`, disjoint
      if 2 ≤ bucketed B_cδ then fun i => merged i || B_cδ i else merged)
    fun _ => false

/-- "Initialize merge buckets `B_{k,δ}`", whichever way (Sec. 3.2) the layer names. -/
def initMergeBuckets : MergeBuckets 𝕋 → Interval 𝕋 n → 𝕋 → Fin n → Bool
  | .static ys => staticMergeBuckets ys
  | .dynamic => dynamicMergeBuckets

/-- Lines 2-6: `δmax` grown tenfold until at most `ρ n_k` neurons remain; `none` past `fuel`. -/
def growBucketTolerance (B : MergeBuckets 𝕋) (I_k : Interval 𝕋 n) (ρ : 𝕋) :
    𝕋 → ℕ → Option 𝕋
  | _, 0 => none
  | δmax, fuel + 1 =>
    let δmax := nsmulUp 10 δmax                                     -- Alg. 1, line 3
    let B_kδmax := initMergeBuckets B I_k δmax                      -- Alg. 1, line 4
    let nhat_k := n - bucketed B_kδmax                              -- Alg. 1, line 5
    if le (ratio nhat_k n) ρ then some δmax                         -- Alg. 1, line 6
    else growBucketTolerance B I_k ρ δmax fuel

/-- Lines 7-16: bisect `[δmin, δmax]` until `n̂_k/n_k ≈ ρ`; `none` past `fuel`. -/
def bisectBucketTolerance (tol : 𝕋) (B : MergeBuckets 𝕋) (I_k : Interval 𝕋 n) (ρ : 𝕋) :
    𝕋 → 𝕋 → ℕ → Option (Fin n → Bool)
  | _, _, 0 => none
  | δmin, δmax, fuel + 1 =>
    let δ := half (addUp δmin δmax)                                 -- Alg. 1, line 8
    let B_kδ := initMergeBuckets B I_k δ                            -- Alg. 1, line 9
    let nhat_k := n - bucketed B_kδ                                 -- Alg. 1, line 10
    let tooManyMerged := !le (mulUp ρ (nsmulUp n one)) (nsmulDown nhat_k one)  -- Alg. 1, line 11
    let δmax := if tooManyMerged then δ else δmax                   -- Alg. 1, line 12
    let δmin := if tooManyMerged then δmin else δ                   -- Alg. 1, line 14
    if le (absolute (subUp (ratio nhat_k n) ρ)) tol then some B_kδ  -- Alg. 1, lines 16-17
    else bisectBucketTolerance tol B I_k ρ δmin δmax fuel


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: the merge buckets of the layer bounded by `I_k` that leave `≈ ρ n_k` of its
neurons, `none` where `fuel` runs out first. -/
def bucketTolerance (tol : 𝕋) (fuel : ℕ) (B : MergeBuckets 𝕋) (I_k : Interval 𝕋 n) (ρ : 𝕋) :
    Option (Fin n → Bool) :=
  let δmin := (zero : 𝕋)                                            -- Alg. 1, line 1
  let δmax := subUp (maxOver I_k.sup) (minOver I_k.inf)             -- Alg. 1, line 1
  match growBucketTolerance B I_k ρ δmax fuel with                  -- Alg. 1, lines 2-6
  | none => none
  | some δmax => bisectBucketTolerance tol B I_k ρ δmin δmax fuel   -- Alg. 1, lines 7-17

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
