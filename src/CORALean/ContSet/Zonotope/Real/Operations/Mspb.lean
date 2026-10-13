import CORALean.ContSet.Interval.Real.Interval
import CORALean.ContSet.Zonotope.Real.Operations.Cloud2zonotope
import CORALean.ContSet.Zonotope.Real.Operations.Volume

/-!
# `Zonotope.mspb`

[1, Alg. 5] (`MSPB`): merge a list `L` of solution domains `A [r] + [v]` (a parallelotope plus an
axis-aligned box, "MSPB") into one zonotope. `P` collects the potential vertices
`A [r]± + [v]±`, the images of the vertices of the two boxes ([1, Remark 3]); `cloud2zonotope`
encloses them for `ratio = 0, 0.1, ..., 1` with `s₁ = n`, `s₂ = 0`; the one of least volume
`µ` ([1, Eq. 45], [1, Eq. 44], `Zonotope.volume`) is kept, the first of equal ones.
`svd(X)(:, 1)` has no algorithm here, so `dir` is an argument. The MSPB attributes `A`, `[r]`,
`[v]` of the result are not split off: the zonotope `c ⊕ Z(R)` is returned, from which they are its
first `n` and last `n` generators and centre.

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on
      Automatic Control, 61(9):2341-2356, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `L := MSPB(L)`, [1, Alg. 5]: the MSPBs `A [r] + [v]` are the triples `(A, [r], [v])`. -/
noncomputable def Zonotope.mspb [NeZero m]
    (dir : (Fin m × (Fin n → Bool) × (Fin n → Bool) → Vec ℝ n) → Vec ℝ n)
    (L : Fin m → Mat ℝ n n × Interval (Vec ℝ n) × Interval (Vec ℝ n)) : Zonotope (Vec ℝ n) :=
  let XP : Fin m × (Fin n → Bool) × (Fin n → Bool) → Vec ℝ n := fun (l, b, b') =>
    (L l).1 *ᵥ (fun i => if b i then (L l).2.1.sup i else (L l).2.1.inf i) +
      fun i => if b' i then (L l).2.2.sup i else (L l).2.2.inf i
  let M := Zonotope.cloud2zonotope dir 0 n 0 XP
  (List.range' 1 10).foldl
    (fun M (k : ℕ) =>
      let M' := Zonotope.cloud2zonotope dir ((k : ℝ) / 10) n 0 XP
      if M'.volume < M.volume then M' else M)
    M

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
