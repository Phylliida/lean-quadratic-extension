# lean-quadratic-extension

General quadratic extension formalized in Lean — a Lean 4 / Mathlib re-take on the
ordered-field construction that lives, in Z3-driven form, in `verus-quadratic-extension`
(the `dts_nonneg` "chungus").

The question this answers: **what is that proof like in Lean instead of Verus?** The
headline is that the *hard part is the same mathematics* — the order on a quadratic
extension is defined **syntactically**, without `√d` ever existing as an element — but
the proof ergonomics differ sharply.

## What's proven (`OneLevel.lean`)

For a single quadratic extension `F(√d)` over **any** linearly ordered field `F`
(`[Field F] [LinearOrder F] [IsStrictOrderedRing F]`), with the order defined exactly
as syntactically as Verus does it — the 3-way sign predicate, no `√d` element:

```
Nonneg d a b  :=  (0 ≤ a ∧ 0 ≤ b)                    -- C1
              ∨  (0 ≤ a ∧ b < 0 ∧ d·b² ≤ a²)        -- C2
              ∨  (a < 0 ∧ 0 < b ∧ a² ≤ d·b²)         -- C3
```

* **`nonneg_add`** — the positive cone is closed under `+` (all 9 sign cases).
  Verus equivalent: `lemma_dts_nonneg_add_closed_fuel` + the ~470-line
  `lemma_dts_nonneg_add_remaining`.
* `nonneg_add_c2c3` — the genuinely hard C2+C3 case (Verus needed *four* sub-lemmas:
  `c2c3_norm_bound`, `c2c3_neg_norm_bound`, `case4_contradiction`,
  `iszero_sum_im_implies_nonneg_sum_re`). Here it is a 4-way sign split, each branch
  closed by a hand-derived degree-4 certificate, e.g. for the "M" sub-case:
  ```
  b₁²·[(a₁+a₂)² − d(b₁+b₂)²] = (a₁²−db₁²)·(b₁+b₂)²
                             + (a₁b₂−a₂b₁)·(−b₁(a₁+a₂) − a₁(b₁+b₂))
  ```
  Both summands are manifestly ≥ 0 and `b₁² > 0` lets `nlinarith` divide.

`#print axioms QuadExt.nonneg_add` → `[propext, Classical.choice, Quot.sound]` only
(no `sorryAx`). Fully verified.

## The dynamic tower (`Tower.lean`)

The actual Verus chungus is the *dynamic tower* (`re`, `im`, `d` are themselves towers,
unbounded depth). This file ports the `DynTower` datatype and `depth` measure faithfully
and lays out the roadmap: the per-level algebra is exactly what `OneLevel` discharges;
the outstanding work is the ring structure on the tower and the fuel/well-founded
induction wrapping it. Not yet done — that's the multi-session part.

## Verus vs Lean, in one paragraph

The order is *constructed*, not *inherited* (no embedding into ℝ — `F` is abstract), so
both systems must derive every "obviously `a+b√d ≥ 0`" from the syntactic sign cases.
Lean's wins over the Z3 version: no fuel-reconciliation lemmas (with well-founded
recursion), no context-pollution choreography (named `have`s persist), and `nlinarith`
eats the easy/medium cases outright. Lean's cost: the genuinely hard C2+C3 certificate
still has to be found by hand and handed to `nlinarith` as exact product hints — the
analogue of Verus' "cancellation-by-B²" — rather than discovered automatically.

## Build

```
lake exe cache get   # prebuilt Mathlib oleans
lake build
```

Toolchain: `leanprover/lean4:v4.25.0`, Mathlib `v4.25.0`.
