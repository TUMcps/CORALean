# Note on the derivatives with respect to a parameter of the solutions of a system of differential equations

T. H. Gronwall. "Note on the derivatives with respect to a parameter of the solutions of
a system of differential equations". Annals of Mathematics, 20(4):292-296, 1919.

**Source:** https://archive.org/download/jstor-1967124/1967124.pdf (a scanned/OCR'd JSTOR copy hosted on the Internet Archive; AMS/JSTOR's own pages return HTTP 403. The PDF's text layer uses a custom-subset TrueType font whose raw character codes are NOT ASCII/Latin-1 — they had to be decoded via the font's embedded /ToUnicode CMap with a purpose-built script, since the plain byte values are meaningless without it. Some OCR artifacts remain, e.g. "y_v" sometimes rendered "Yv" or "yv?", and a few characters are misrecognized — these are the original scan's OCR errors, not further corruption introduced here.)  
**Inventory:** confirmed

Grönwall's inequality, which bounds a trajectory by the growth its field
allows. Used through Mathlib's `ODE/Gronwall.lean` rather than reproved, and it
is what encloses `LinParamSys`'s `'varParam'` case in place of the Peano–Baker
series Mathlib does not have.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Sec. 1` | Motivates the problem: extending J. F. Ritt's single-equation proof (that the solution of a parametrized ODE is differentiable w.r.t. the parameter) to systems of equations; also announces analogous results for differentiability w.r.t. initial values. | n/a — motivation and history, not a claim to formalize | `not-a-claim` |
| `Sec. 2 (setup)` | Sets up the system dy_ν/dx = f_ν(x,y_1,...,y_n;a), y_ν=y_ν⁰ at x=x0, and states that ∂y_ν/∂a exist and satisfy the variational (first-order sensitivity) equations (4) with initial condition (5). | n/a — differentiability of a solution in a parameter, which CORALean does not do: it uses the inequality alone | `not-covered` |
| `Sec. 2 (the lemma)` | ("Grönwall's inequality", unlabeled in the source) If a continuous z(x) satisfies 0 ≤ z ≤ ∫(Mz+A)dx on [x0,x0+h] with M,A ≥ 0 constants, then 0 ≤ z ≤ Ah·e^{Mh} on that interval. | n/a — Mathlib's `gronwallBound` and `norm_le_gronwallBound_of_norm_deriv_right_le` provide it, used in [`TrajectoryNormLe.lean`](../../src/CORALean/ContDynamics/LinParamSys/Theorems/IsTrajectoryNormLe.lean) | `mathlib` |
| `Sec. 2 (the theorem)` | Using the lemma, proves that the y_ν are uniformly continuous (in fact differentiable) functions of the parameter a, establishing existence of ∂y_ν/∂a satisfying (4)-(5) as stated at the top of §2. | n/a — differentiability of a solution in a parameter, which CORALean does not do | `not-covered` |
| `Sec. 3` | Extends the result: the partial derivatives ∂y_ν/∂y_μ⁰ (w.r.t. initial values) all exist and satisfy the differential equations (12) with initial conditions (13) (∂y_ν/∂y_μ⁰ = δ_{νμ} at x=x0), proved by treating y_μ⁰ as the "parameter" a in the §2 theorem. | n/a — differentiability in the initial values, which CORALean does not do | `not-covered` |
| `Sec. 4` | Further extends the result to partial derivatives ∂y_ν/∂x0 (w.r.t. the initial point x0 itself), which exist and satisfy (14) with initial conditions (15), proved analogously via an auxiliary linear system. | n/a — differentiability in the initial point, which CORALean does not do | `not-covered` |

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`TrajectoryNormLe.lean`](../../src/CORALean/ContDynamics/LinParamSys/Theorems/IsTrajectoryNormLe.lean)
