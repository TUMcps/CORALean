module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.FloatOps
public import CORALean.Global.Float.PowDown
public import CORALean.Global.Float.PowUp
public import CORALean.Specification.SyntaxTree.Operations.Nthroot
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `aux_nthroot_` over a float scalar

MATLAB's `nthroot(x,k)`: the real `k`-th root, negative arguments allowed, with the result enclosed
by an interval of floats. A root of `|x|` is bracketed by bisection: the lower end moves to a
midpoint only where its power rounded up (`powUp`) is certified at most `|x|`, the upper end only
where its power rounded down (`powDown`) is certified at least `|x|`, so every end that is kept
satisfies its inequality whatever the steps do. A negative argument reflects the roots, and an
argument of unknown sign takes the hull. Degree `0` is enclosed by `[-1,1]`. Soundness is
`SyntaxTree.nthrootFloat_contains`.

## Inputs
* `steps` – bisection steps
* `x` – number
* `k` – degree

## Output
* an interval of floats containing the real root of that degree
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       25-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋]


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- Bisection for a lower bound of the root: the lower end moves to a midpoint certified to have a
power at most `x`. -/
@[step_of SyntaxTree.nthrootFloat]
def SyntaxTree.step_nthrootFloat_downIter (x : 𝕋) (k : ℕ) : ℕ → 𝕋 → 𝕋 → 𝕋
  | 0, lo, _ => lo
  | n + 1, lo, hi =>
    let mid := maximum zero (half (addDown lo hi))
    if le (powUp mid k) x = true then SyntaxTree.step_nthrootFloat_downIter x k n mid hi
    else SyntaxTree.step_nthrootFloat_downIter x k n lo mid

/-- Bisection for an upper bound of the root: the upper end moves to a midpoint certified to have a
power at least `x`. -/
@[step_of SyntaxTree.nthrootFloat]
def SyntaxTree.step_nthrootFloat_upIter (x : 𝕋) (k : ℕ) : ℕ → 𝕋 → 𝕋 → 𝕋
  | 0, _, hi => hi
  | n + 1, lo, hi =>
    let mid := maximum zero (half (addUp lo hi))
    if le x (powDown mid k) = true then SyntaxTree.step_nthrootFloat_upIter x k n lo mid
    else SyntaxTree.step_nthrootFloat_upIter x k n mid hi

/-- A lower bound of the `k`-th root of a nonnegative `x`, from the bracket `[0, max(1,x)]`. -/
@[step_of SyntaxTree.nthrootFloat]
def SyntaxTree.step_nthrootFloat_down (steps : ℕ) (x : 𝕋) (k : ℕ) : 𝕋 :=
  SyntaxTree.step_nthrootFloat_downIter x k steps zero (maximum one x)

/-- An upper bound of the `k`-th root of a nonnegative `x`, from the bracket `[0, max(1,x)]`. -/
@[step_of SyntaxTree.nthrootFloat]
def SyntaxTree.step_nthrootFloat_up (steps : ℕ) (x : 𝕋) (k : ℕ) : 𝕋 :=
  SyntaxTree.step_nthrootFloat_upIter x k steps zero (maximum one x)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `nthroot(x,k)`: an interval of floats containing the real `k`-th root of `x`. -/
def SyntaxTree.nthrootFloat (steps : ℕ) (x : 𝕋) (k : ℕ) : Float.Interval 𝕋 :=
  if k = 0 then ⟨neg one, one⟩
  else if le zero x = true then
    ⟨SyntaxTree.step_nthrootFloat_down steps x k, SyntaxTree.step_nthrootFloat_up steps x k⟩
  else if le x zero = true then
    ⟨neg (SyntaxTree.step_nthrootFloat_up steps (neg x) k),
      neg (SyntaxTree.step_nthrootFloat_down steps (neg x) k)⟩
  else ⟨neg (SyntaxTree.step_nthrootFloat_up steps (absolute x) k),
    SyntaxTree.step_nthrootFloat_up steps (absolute x) k⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
