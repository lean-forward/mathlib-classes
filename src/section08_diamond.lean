-- Boilerplate:
import algebra.module.basic
set_option old_structure_cmd true
namespace examples

/-
Each `add_comm_monoid M` structure naturally gives rise to an `ℕ`-module structure,
where `n • x` is defined as `x + x + ⋯ + x`, `n` times.
-/
#print add_comm_monoid.nat_module
/-
In addition, each `semiring R` structure naturally gives rise to an `R`-module structure on itself,
where `x • y` is defined as `x * y`.
-/
#print semiring.to_module
/-
The class `decidable_pred {α : Type*} (p : α → Prop) : Type*` provides a decision algorithm for `p`,
and is used in \mathlib for small numeric computations.
-/
#print decidable_pred
/-
Instead, \mathlib adds extra data to \lstinline{add_comm_monoid}'s ancestor \lstinline{add_monoid}:
a field `nsmul : ℕ → M → M` defines scalar multiplication by a natural number,
and two proof fields assert it (propositionally) equals the left-recursive definition:
-/
-- Adapted from `algebra/group/defs.lean:459`
class add_monoid (M : Type*) extends add_semigroup M, add_zero_class M :=
(nsmul : ℕ → M → M)
(nsmul_zero : ∀ x, nsmul 0 x = 0)
(nsmul_succ : ∀ (n : ℕ) x, nsmul (n + 1) x = x + nsmul n x)
/-
A generic implementation `nsmul_rec` is provided for instances where definitional equality is not a concern.
-/
#print nsmul_rec

end examples
