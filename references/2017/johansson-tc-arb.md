# Arb: Efficient Arbitrary-Precision Midpoint-Radius Interval Arithmetic

```bibtex
@article{johansson2017arb,
  author = {Johansson, F.},
  title = {Arb: Efficient Arbitrary-Precision Midpoint-Radius Interval Arithmetic},
  journal = {IEEE Transactions on Computers},
  year = {2017}
}
```

**Source:** https://arxiv.org/pdf/1611.02831 (the arXiv version v1, 9 November 2016, read with `pypdf`; numbering as there).
**Inventory:** partial (only the section on the number types was read, for what `Flint` takes from it)

The paper behind the C library whose `arf_t` type FLINT's `arf_add`/`arf_mul`/`arf_div` operate
on: a floating-point number with a mantissa of any precision and an exponent that is itself an
arbitrary-size integer. `Global/Float/Instances/Flint/` takes from it that the exponent is
unbounded, so that no operation overflows or underflows, and that rounded operations take a
precision `prec` in bits; everything else the paper treats (ball arithmetic, special functions)
is not used here.

## Results

| Result | What it says | In CORALean | Class |
|---|---|---|---|
| `Sec. 3.1.2` | The exponent of an `arf_t` is an arbitrarily large integer (a FLINT `fmpz_t`), unlike MPFR's single word, so underflow and overflow cannot occur. | n/a — a design statement about a library, with no theorem to prove | `not-a-claim` |
