# An embedding theorem for spaces of convex sets

H. Rådström. "An embedding theorem for spaces of convex sets". Proc. Amer. Math. Soc. 3
(1952), pp. 165-169.

**Source:** (unobtainable — see notes)  
**Inventory:** unconfirmed

The cancellation law: `X + E ⊆ Y + E` gives `X ⊆ Y` when `Y` is convex and
closed and `E` is bounded. Mathlib does not have it, so `Global/Radstrom.lean`
proves it — and it is what turns an outer approximation with a known error into
an inner one, which is where every inner approximation here starts.

The paper itself is behind a challenge page at the AMS and has no open mirror,
so its results are not listed: ⚪ here means *not read*, not *not formalized*.
What `Global/Radstrom.lean` proves is the cancellation law as stated above.

## Results

| Result | What it says | In CORALean |
|---|---|---|

## Cited without a result

These name the paper as a whole. A locator would put each in a row above.

* [`Radstrom.lean`](../../src/CORALean/Global/Radstrom.lean)
