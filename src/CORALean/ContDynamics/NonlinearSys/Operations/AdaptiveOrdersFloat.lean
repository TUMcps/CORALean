module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `aux_getPowers` of CORA's `linReach_adaptive`, in floats

The order `q_i` in `Δt` of the abstraction error in each dimension that CORA's
`linReach_adaptive.m` derives at `alg = 'lin'`, line by line: `sigma_i`, the order of the error
of the dynamics in dimension `i` (`2` from a point, `0` from a full-dimensional set, and from a
degenerate one what the Hessian at the linearization point couples to the zero-width dimensions),
and then `q_i = min_p (q_i^(p) + p)` over the powers `A^p`, until no lower value can follow, with
CORA's safety stop at `p = 100`. The products `A^p` are taken as patterns of nonzero entries,
where CORA multiplies numbers (they differ only where entries cancel exactly). `none` is CORA's
`Inf`. A tuning heuristic.

## Inputs
* `A` – state matrix
* `zeroWidthDim` – dimensions of zero width
* `Gzero` – zero rows of the abstraction error
* `H` – Hessian at the linearization point
* `fuel` – bound on the powers

## Output
* the order per dimension
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- `min(a, b)` with `none` as `Inf`. -/
@[step_of NonlinearSys.adaptiveOrdersFloat]
def step_optMin : Option ℕ → Option ℕ → Option ℕ
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

/-- Whether a box entry is not the point `0`. -/
@[step_of NonlinearSys.adaptiveOrdersFloat]
def step_nonzero (lo hi : 𝕋) : Bool :=
  !(le lo zero && le zero lo && le hi zero && le zero hi)

/-- `sigma`: the order of the error of the dynamics in each dimension. -/
@[step_of NonlinearSys.adaptiveOrdersFloat]
def step_sigma (zeroWidthDim : Fin n → Bool) (H : Fin n → Interval (Mat 𝕋 (n + m) (n + m)))
    (i : Fin n) : ℕ :=
  if ∀ j, zeroWidthDim j = true then 2                               -- start set a point
  else if ∀ j, zeroWidthDim j = false then 0                         -- full-dimensional
  else
    let h := fun (a b : Fin n) => ((H i).inf (Fin.castAdd m a) (Fin.castAdd m b),
      (H i).sup (Fin.castAdd m a) (Fin.castAdd m b))
    if ∃ j, zeroWidthDim j = false ∧ step_nonzero (h j j).1 (h j j).2 = true then 0  -- H(j,j)
    else
      let pairs := (List.finRange n).flatMap fun j => ((List.finRange n).filter (j < ·)).map
        fun jj => (j, jj)
      let found := pairs.filter fun q => step_nonzero (addDown (h q.1 q.2).1 (h q.2 q.1).1)
        (addUp (h q.1 q.2).2 (h q.2 q.1).2)                         -- H(j,jj) + H(jj,j) ~= 0
      match found.map (fun q => (if zeroWidthDim q.1 then 1 else 0) +
          (if zeroWidthDim q.2 then 1 else 0)) with
      | [] => 2                                                     -- sigma still not found
      | c :: cs => cs.foldl min c                                   -- nnz(zeroWidthDim([j,jj]))

/-- The `q_i` loop over the powers of `A`, as nonzero patterns, from power `p`. -/
@[step_of NonlinearSys.adaptiveOrdersFloat]
def step_ordersLoop (Apat : Fin n → Fin n → Bool) (Gzero : Fin n → Bool) (sigma : Fin n → ℕ) :
    ℕ → ℕ → (Fin n → Fin n → Bool) → (Fin n → Option ℕ) → Fin n → Option ℕ
  | 0, _, _, qi => qi
  | fuel + 1, p, Apow, qi =>
    let qip := fun i => (List.finRange n).foldl (fun acc j =>       -- qip(i,p+1)
      if Gzero j = false ∧ Apow i j = true then step_optMin acc (some (sigma j)) else acc) none
    let qi' := fun i => step_optMin (qi i) ((qip i).map (· + p))    -- min(qi, qip + p)
    if ∀ i, (qi' i).any (· < p + 1) = true then qi'                 -- all(qi < p+1)
    else step_ordersLoop Apat Gzero sigma fuel (p + 1)
      (fun i j => (List.finRange n).any fun k => Apow i k && Apat k j) qi'  -- Apower * A


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `aux_getPowers` at `alg = 'lin'`: the order `q_i` of the abstraction error. -/
def NonlinearSys.adaptiveOrdersFloat (A : Mat 𝕋 n n) (zeroWidthDim Gzero : Fin n → Bool)
    (H : Fin n → Interval (Mat 𝕋 (n + m) (n + m))) (fuel : ℕ) : Fin n → Option ℕ :=
  let Apat := fun i j => step_nonzero (A i j) (A i j)               -- A(i,j) ~= 0
  step_ordersLoop Apat Gzero (step_sigma zeroWidthDim H) fuel 0     -- p = 0, Apower = eye(n)
    (fun i j => decide (i = j)) fun _ => none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
