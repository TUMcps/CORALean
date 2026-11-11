module

public import CORALean.Global.Float.Sqrt
public import CORALean.Global.StepOf

@[expose] public section

/-!
# The Arnoldi iteration, in floats

[1, Alg. 1] (`Krylov.arnoldi`) at a float representation, as CORA runs it: the start vector `c`
scaled by its norm `ν` (line 1), each pass taking `w = A v(k)` (line 3), sweeping it against the
earlier vectors by modified Gram–Schmidt (lines 4–7), storing `h_{k+1,k} = ‖w‖` and `v(k+1) =
w / h_{k+1,k}` (lines 8 and 12), a happy breakdown `h_{k+1,k} ≤ ε` storing `v(k+1) = 0`. Every
operation rounds up, a dot product summed from its last term (`sumUp`), the vectors stored once
(`Vector`). At the sound representations that rounds the stored basis, which nothing relies on
(the residual of what is stored is measured); at `nearest` it is CORA's.

## Inputs
* `p` – Newton steps per norm
* `ε` – breakdown threshold
* `A` – matrix
* `c` – start vector
* `ν` – its norm

## Output
* Arnoldi vectors and Hessenberg entries after `k` passes

## References

* [1] [M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
      Krylov Subspace". IEEE Transactions on Automatic Control,
      2020.](../../../../../../references/2020/althoff-tac-krylov.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- Lines 4–7 of [1, Alg. 1]: `w` swept against `V 0, …, V (j - 1)`, `h = w·v` first and `w - h v`
after, rounded up, `w` stored after every update. -/
@[step_of Krylov.arnoldiFloat]
def Krylov.step_arnoldiSweep (w : Vector 𝕋 n) (V : ℕ → Vector 𝕋 n) :
    ℕ → Vector 𝕋 n × (ℕ → 𝕋)
  | 0 => (w, fun _ => zero)
  | j + 1 =>
    let prev := Krylov.step_arnoldiSweep w V j
    -- 5. h_{j,k} ← w* v(j), 6. w ← w - h_{j,k} v(j)
    let h := dotUp (fun r : Fin n => prev.1[r]) (fun r : Fin n => (V j)[r])
    (Vector.ofFn fun r : Fin n => subUp prev.1[r] (mulUp h (V j)[r]), Function.update prev.2 j h)

/-- Line 1 of [1, Alg. 1]: `v(1) = c / ν`, no Hessenberg entries yet. -/
@[step_of Krylov.arnoldiFloat]
def Krylov.step_arnoldiStart (c : Vec 𝕋 n) (ν : 𝕋) : (ℕ → Vector 𝕋 n) × (ℕ → ℕ → 𝕋) :=
  -- 1. v(1) ← c / ‖c‖
  let v1 : Vector 𝕋 n := Vector.ofFn fun r => divUp (c r) ν
  (fun _ => v1, fun _ _ => zero)

/-- Pass `k + 1` of [1, Alg. 1] from the state after `k` passes. -/
@[step_of Krylov.arnoldiFloat]
def Krylov.step_arnoldiPass (p : ℕ) (ε : 𝕋) (A : Mat 𝕋 n n) (k : ℕ)
    (prev : (ℕ → Vector 𝕋 n) × (ℕ → ℕ → 𝕋)) : (ℕ → Vector 𝕋 n) × (ℕ → ℕ → 𝕋) :=
  let V := prev.1
  -- 3. w ← C v(k)
  let w : Vector 𝕋 n := Vector.ofFn fun r => dotUp (A r) (fun l : Fin n => (V k)[l])
  -- 4.-7. h_{j,k} ← w* v(j), w ← w - h_{j,k} v(j)
  let swept := Krylov.step_arnoldiSweep w V (k + 1)
  -- 8. h_{k+1,k} ← ‖w‖
  let hnext := normUp p (fun r : Fin n => swept.1[r])
  -- 9.-12. happy breakdown, else v(k+1) ← w / h_{k+1,k}
  let vnext : Vector 𝕋 n :=
    if le hnext ε then Vector.ofFn fun _ => zero
    else Vector.ofFn fun r : Fin n => divUp swept.1[r] hnext
  (Function.update V (k + 1) vnext,
    fun i j => if j = k then (if i ≤ k then swept.2 i else if i = k + 1 then hnext else zero)
      else prev.2 i j)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] after `k` passes in floats: the vectors `v(1), …, v(k+1)` at indices `0, …, k` and
the Hessenberg entries `h_{i,j}` at `(i - 1, j - 1)`. -/
def Krylov.arnoldiFloat (p : ℕ) (ε : 𝕋) (A : Mat 𝕋 n n) (c : Vec 𝕋 n) (ν : 𝕋) :
    ℕ → (ℕ → Vector 𝕋 n) × (ℕ → ℕ → 𝕋)
  -- 1. start, 2.-13. one pass per `k`
  | 0 => Krylov.step_arnoldiStart c ν
  | k + 1 => Krylov.step_arnoldiPass p ε A k (Krylov.arnoldiFloat p ε A c ν k)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
