/*
 * The C side of `Flint p` (src/CORALean/Global/Float/Instances/Flint): the six
 * rounded operations, each one FLINT `arf_*` call at the precision `p` and in
 * the direction `trustedFlint` assumes (ARF_RND_CEIL up, ARF_RND_FLOOR down).
 *
 * DRAFT: compiles, but not yet linked or tested; see the branch's WIP commit.
 *
 * The conversion boundary. Lean's runtime links its own GMP (6.1.2, static),
 * FLINT needs >= 6.2, so no GMP object crosses: a Lean `Int` is read through
 * lean.h alone (scalar fast path, else 64-bit limbs via `lean_nat_land` and
 * `lean_nat_shiftr`), and built back the same way. The FLINT/MPFR/GMP copy is
 * bundled into one relocatable object whose only globals are `coralean_flint_*`
 * (scripts/build/build-flint-shim.sh, to be written), so the two GMPs never meet.
 *
 * Every conversion is exact: `arf_set_fmpz_2exp` and `arf_get_fmpz_2exp` do not
 * round. A precision below 2 is raised to 2, and one above CORALEAN_MAX_PREC
 * lowered to it; a directed rounding is directed at any precision, so the laws
 * still hold. A special result (only a zero divisor produces one) comes back
 * as 0, which the class leaves unconstrained.
 */
#include <lean/lean.h>
#include <flint/fmpz.h>
#include <flint/arf.h>
#include <stdlib.h>

#define CORALEAN_MAX_PREC ((slong)1 << 30)

static slong prec_of(b_lean_obj_arg p) {
    if (!lean_is_scalar(p)) return CORALEAN_MAX_PREC;
    size_t v = lean_unbox(p);
    if (v < 2) return 2;
    if (v > (size_t)CORALEAN_MAX_PREC) return CORALEAN_MAX_PREC;
    return (slong)v;
}

/* Lean `Int` (borrowed) to `fmpz`, exactly. */
static void int_to_fmpz(fmpz_t out, b_lean_obj_arg x) {
    if (lean_is_scalar(x)) { fmpz_set_si(out, lean_scalar_to_int64(x)); return; }
    int neg = lean_int_lt(x, lean_box(0));
    lean_object *mag = lean_nat_abs(x);                  /* owned */
    lean_object *mask = lean_uint64_to_nat(UINT64_MAX);  /* owned */
    lean_object *sh = lean_box(64);
    size_t cap = 4, n = 0;
    ulong *limbs = malloc(cap * sizeof(ulong));
    while (!lean_nat_eq(mag, lean_box(0))) {
        if (n == cap) { cap *= 2; limbs = realloc(limbs, cap * sizeof(ulong)); }
        lean_object *lo = lean_nat_land(mag, mask);
        limbs[n++] = lean_uint64_of_nat(lo);
        lean_dec(lo);
        lean_object *next = lean_nat_shiftr(mag, sh);
        lean_dec(mag);
        mag = next;
    }
    lean_dec(mag); lean_dec(mask);
    fmpz_set_ui_array(out, limbs, (slong)n);
    if (neg) fmpz_neg(out, out);
    free(limbs);
}

/* `fmpz` to a Lean `Int` (owned), exactly. */
static lean_obj_res fmpz_to_int(const fmpz_t x) {
    if (fmpz_fits_si(x)) return lean_int64_to_int(fmpz_get_si(x));
    int sgn = fmpz_sgn(x);
    fmpz_t a; fmpz_init(a); fmpz_abs(a, x);
    slong n = fmpz_size(a);
    ulong *limbs = malloc(n * sizeof(ulong));
    fmpz_get_ui_array(limbs, n, a);
    lean_object *acc = lean_box(0), *sh = lean_box(64);
    for (slong i = n - 1; i >= 0; i--) {
        lean_object *hi = lean_nat_shiftl(acc, sh);
        lean_object *lo = lean_uint64_to_nat(limbs[i]);
        lean_dec(acc);
        acc = lean_nat_lor(hi, lo);
        lean_dec(hi); lean_dec(lo);
    }
    free(limbs); fmpz_clear(a);
    lean_object *r = lean_nat_to_int(acc);               /* consumes acc */
    if (sgn < 0) { lean_object *t = lean_int_neg(r); lean_dec(r); r = t; }
    return r;
}

static void flint_to_arf(arf_t out, b_lean_obj_arg v) {
    fmpz_t m, e; fmpz_init(m); fmpz_init(e);
    int_to_fmpz(m, lean_ctor_get(v, 0));
    int_to_fmpz(e, lean_ctor_get(v, 1));
    arf_set_fmpz_2exp(out, m, e);
    fmpz_clear(m); fmpz_clear(e);
}

static lean_obj_res arf_to_flint(const arf_t x) {
    fmpz_t m, e; fmpz_init(m); fmpz_init(e);
    if (arf_is_finite(x)) arf_get_fmpz_2exp(m, e, x);   /* zero gives 0, 0 */
    lean_object *r = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(r, 0, fmpz_to_int(m));
    lean_ctor_set(r, 1, fmpz_to_int(e));
    fmpz_clear(m); fmpz_clear(e);
    return r;
}

typedef int (*arf_binop)(arf_ptr, arf_srcptr, arf_srcptr, slong, arf_rnd_t);

static lean_obj_res run(arf_binop op, arf_rnd_t rnd, b_lean_obj_arg p,
                        b_lean_obj_arg a, b_lean_obj_arg b) {
    arf_t x, y, z; arf_init(x); arf_init(y); arf_init(z);
    flint_to_arf(x, a); flint_to_arf(y, b);
    op(z, x, y, prec_of(p), rnd);
    lean_obj_res r = arf_to_flint(z);
    arf_clear(x); arf_clear(y); arf_clear(z);
    return r;
}

/* `arf_mul` is a macro in FLINT 3, so it needs a function to be passed. */
static int mul_fn(arf_ptr z, arf_srcptr x, arf_srcptr y, slong prec, arf_rnd_t rnd)
{ return arf_mul(z, x, y, prec, rnd); }

#define OP(name, fn, rnd) \
    LEAN_EXPORT lean_obj_res name(b_lean_obj_arg p, b_lean_obj_arg a, b_lean_obj_arg b) \
    { return run(fn, rnd, p, a, b); }

OP(coralean_flint_add_up,   arf_add, ARF_RND_CEIL)
OP(coralean_flint_add_down, arf_add, ARF_RND_FLOOR)
OP(coralean_flint_mul_up,   mul_fn,  ARF_RND_CEIL)
OP(coralean_flint_mul_down, mul_fn,  ARF_RND_FLOOR)
OP(coralean_flint_div_up,   arf_div, ARF_RND_CEIL)
OP(coralean_flint_div_down, arf_div, ARF_RND_FLOOR)
