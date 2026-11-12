module

public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.ErrorBoundFloatOuter
public import CORALean.ContDynamics.LinearSys.Krylov.Theorems.WindowErrorBoundFloatSound

@[expose] public section

/-!
# The error inside a window from the Krylov bound at its end

`Krylov.windowErrorBoundFloat_sound` asks the local error of window `N` to be within `ε_N` at every
time `s ∈ [0, T]`. For a Krylov step that is not an extra hypothesis, as [1, Thm. 3] bounds the
error at every `s ∈ [0, t]` and `Krylov.error_le_errorBoundFloat` rounds that bound up at `t`. So
with `ε_N = errorBoundFloat(T)`, as CORA.cpp forms it, the weighted bound holds at every time of
the window, with no hypothesis on the times before `T`.

## Inputs
* `p` – Newton steps per root
* `q` – squarings of the exponential
* `A` – matrix
* `P` – symmetric weight
* `L` – factor of `P - aI`
* `a` – shift
* `Δt` – lengths of the finished windows
* `ε` – local 2-norm errors of the windows
* `N` – number of finished windows
* `t` – length of window `N`
* `c` – start vector of window `N`, the approximate iterate `w^{[N]}`
* `ν` – scale of the first basis vector
* `V` – basis vectors
* `H` – Hessenberg entries
* `m` – order minus one
* `μA` – bound of the quadratic form of `A`
* `r` – bounds of the residual norms
* `v` – exact iterates
* `w` – approximate iterates
* `S` – approximate step maps

## Hypotheses
* `hok` – the weight was accepted and the rate is nonpositive
* `hv` – exact iterates follow the exact steps
* `hw` – approximate iterates follow the approximate steps
* `h0` – both start at the same vector
* `hloc` – local errors of the finished windows within the bounds
* `hwN` – window `N` starts at `c`
* `hq` – at least one squaring
* `hH` – Hessenberg entries below the subdiagonal zero
* `hμA` – quadratic form of `A` bounded
* `hr` – residual norms bounded
* `ht` – time nonnegative
* `hcap` – `tμ` within the exponential's range
* `hεN` – the local error of window `N` is the Krylov bound at its end

## Conclusion
* at every time of window `N` the 2-norm error is at most the float bound

## References

* [1] [T. Jawecki, W. Auzinger and O. Koch. "Computable upper error bounds for Krylov
      approximations to matrix exponentials and associated φ-functions". BIT Numerical
      Mathematics, 2020.](../../../../../../references/2020/jawecki-bit-krylov-error-bounds.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- With `ε_N` the Krylov bound at the window's end, the weighted bound holds throughout it. -/
theorem Krylov.windowErrorBoundFloat_sound_of_errorBoundFloat (p q : ℕ) (A P L : Mat 𝕋 n n)
    (a : 𝕋) (Δt ε : ℕ → 𝕋) (N : ℕ) (t : 𝕋) (c : Vec 𝕋 n) (ν : 𝕋) (V : ℕ → Vector 𝕋 n)
    (H : ℕ → ℕ → 𝕋) (m : ℕ) (μA : 𝕋) (r : ℕ → 𝕋)
    (hok : Krylov.windowErrorOkFloat q (Krylov.lyapunovCertificateFloat A P L a) Δt N = true)
    (v w : ℕ → Vec ℝ n) (S : ℕ → Vec ℝ n → Vec ℝ n)
    (hv : ∀ j < N, v (j + 1) = exp (toReal (Δt j) • toRealMat A) *ᵥ v j)
    (hw : ∀ j < N, w (j + 1) = S j (w j)) (h0 : v 0 = w 0)
    (hloc : ∀ j < N,
      ‖exp (toReal (Δt j) • toRealMat A) *ᵥ w j - S j (w j)‖₂ ≤ toReal (ε j))
    (hwN : w N = fun i => toReal (c i)) (hq : 1 ≤ q)
    (hH : ∀ i j, j + 1 < i → toReal (H i j) = 0)
    (hμA : ∀ x : Vec ℝ n, x ⬝ᵥ (toRealMat A *ᵥ x) ≤ toReal μA * (x ⬝ᵥ x))
    (hr : ∀ j, j < m + 1 → ‖fun i => (toRealMat A *ᵥ fun l => toReal (V j)[l]) i -
        ∑ k : Fin (j + 2), toReal (H k j) * toReal (V k)[i]‖₂ ≤ toReal (r j))
    (ht : 0 ≤ toReal t)
    (hcap : le (mulUp t (maximum zero (maximum μA
        (Krylov.quadBoundUp fun i j : Fin (m + 1) => H i j)))) (nsmulDown (2 ^ (q - 1)) one) =
      true)
    (hεN : ε N = Krylov.errorBoundFloat p q μA r c ν V H (m + 1) t) : -- --- CONCL ---
    ∀ s, 0 ≤ s → s ≤ toReal t → ‖exp (s • toRealMat A) *ᵥ v N -
        toReal ν • ((Matrix.of fun (i : Fin n) (j : Fin (m + 1)) => toReal (V j)[i]) *ᵥ
          (exp (s • Matrix.of fun (i j : Fin (m + 1)) => toReal (H i j)) *ᵥ Pi.single 0 1))‖₂ ≤
      toReal (Krylov.windowErrorBoundFloat p q (Krylov.lyapunovCertificateFloat A P L a) Δt ε
        N) := by -- --- PROOF ---
  refine Krylov.windowErrorBoundFloat_sound p q A P L a Δt ε N (toReal t) hok v w S
    (fun s => toReal ν • ((Matrix.of fun (i : Fin n) (j : Fin (m + 1)) => toReal (V j)[i]) *ᵥ
      (exp (s • Matrix.of fun (i j : Fin (m + 1)) => toReal (H i j)) *ᵥ Pi.single 0 1)))
    hv hw h0 hloc ?_
  intro s hs0 hst
  rw [hwN, hεN]
  exact Krylov.error_le_errorBoundFloat p q A c ν V H m t μA r hq hH hμA hr ht hcap s ⟨hs0, hst⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
