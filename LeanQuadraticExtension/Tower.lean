import Mathlib

/-!
# The dynamic tower — datatype and roadmap

`OneLevel.lean` proves cone-closure for a *single* quadratic extension `F(√d)`.
The Verus `verus-quadratic-extension` "chungus" is the **dynamic tower**: `re`, `im`
and the radicand `d` are themselves towers, so the depth is unbounded. This file
gives the datatype faithfully and maps out what the full port needs — the algebra
per level is exactly what `OneLevel` already discharges; the new ingredient is the
*induction*.

## Datatype

`DynTower F` mirrors Verus `DynTowerSpec<T>` (`dyn_tower.rs`):
* `base r`        ↔ `DynTowerSpec::Rat(r)`
* `ext re im d`   ↔ `DynTowerSpec::Ext(Box re, Box im, Box d)`  ≈ `re + im·√d`
-/

namespace DynTower

inductive DynTower (F : Type*) where
  | base : F → DynTower F
  | ext  : DynTower F → DynTower F → DynTower F → DynTower F
  deriving Repr

variable {F : Type*}

/-- Tower depth. `ext` is one deeper than its deepest child. Mirrors Verus
`dts_depth`; it is the well-founded measure the recursive `Nonneg` decreases on. -/
def depth : DynTower F → Nat
  | .base _      => 0
  | .ext re im d => 1 + max (depth re) (max (depth im) (depth d))

@[simp] theorem depth_base (r : F) : depth (.base r) = 0 := rfl

@[simp] theorem depth_ext (re im d : DynTower F) :
    depth (.ext re im d) = 1 + max (depth re) (max (depth im) (depth d)) := rfl

/-!
## Roadmap to `nonneg_add_tower`

The remaining pieces — each its own Verus sub-file in the original — are:

1. **Ring structure** `add, neg, sub, mul, isZero` on `DynTower F` by structural
   recursion (Verus `dts_add/dts_neg/dts_mul/...`). Needs `same_radicand` side
   conditions so `ext _ _ d + ext _ _ d'` is only formed when `d = d'`. This is a
   `CommRing (DynTower F)` instance built by induction — comparable work in Lean
   and Verus; Mathlib gives no shortcut for "towers form a ring".

2. **Fuel-recursive `Nonneg`**, a direct port of Verus `dts_nonneg_fuel`:
   ```
   def Nonneg (x : DynTower F) (fuel : Nat) : Prop :=
     match x, fuel with
     | .base r,        _      => 0 ≤ r
     | .ext _ _ _,     0      => False
     | .ext a b d,     f+1    =>
         let a2 := mul a a; let b2d := mul d (mul b b)
         (Nonneg a f ∧ Nonneg b f) ∨
         (Nonneg a f ∧ (Nonneg (neg b) f ∧ ¬ isZero b) ∧ Nonneg (sub a2 b2d) f) ∨
         ((Nonneg (neg a) f ∧ ¬ isZero a) ∧ (Nonneg b f ∧ ¬ isZero b)
            ∧ Nonneg (sub b2d a2) f)
   ```
   Using an explicit `fuel : Nat` (structural recursion) sidesteps termination
   proofs entirely — the *same trick Verus uses*. The Lean alternative is
   well-founded recursion on `depth`, which removes the fuel-bookkeeping lemmas
   (`fuel_monotone/_stabilize/_congruence`) at the cost of proving
   `depth (mul a a) ≤ depth a` for `decreasing_by`.

3. **`nonneg_add_tower`** by strong induction on `fuel`. The `base` case is
   `add_nonneg`. The `ext` case is the 3×3 sign dispatch — and its arithmetic core,
   "`a²−d·b² ≥ 0` combines correctly", is precisely `OneLevel.nonneg_add_c2c3` and
   friends, now with the "numbers" being lower-fuel `Nonneg` *induction hypotheses*
   rather than `F`-elements. That lift is the genuine multi-session chungus; the
   per-level algebra above is already done.
-/

end DynTower
