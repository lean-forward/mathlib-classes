-- Boilerplate:
import data.real.basic
namespace examples

/-
A basic example is the definition of the multiplication operator `*` in core Lean:
-/
-- Adapted from `library/init/core.lean:301`
class has_mul (α : Type*) := (mul : α → α → α)
infix * := has_mul.mul
/-
[T]he `has_inv` class providing `⁻¹` notation for the multiplicative inverse does not have any fields requiring a multiplicative group structure.
-/
#print has_inv

/-
Notation typeclasses are also used in Lean 3 to parse numerals into a little-endian binary representation.
For example, `(37 : ℝ) = 0b100101` is represented as:
-/
set_option pp.numerals false
#check (37 : ℝ)

/-
Whenever the elaborator encounters a term `t : A` that is instead expected to have type `B`,
it replaces `t` with `@coe A B _ t`,
where the `_` marks an instance parameter of type `has_lift_t A B`.-/
#print coe
#print has_coe_t
/-
Similarly, when a term `f : F` produces a type error because it is expected to have a dependent function type,
it is replaced with `coe_fn f` (where `coe_fn {F A} [has_coe_to_fun F A] : Π (f : F), A f`),
-/
#print coe_fn
#print has_coe_to_fun
/-
and when `t` is expected to be of the form `Sort u` (either `Type v` or `Prop`), it is replaced with `coe_sort t`
(where `coe_sort {A} [has_coe_to_sort A] : Sort u`).
-/
#print coe_sort
#print has_coe_to_sort

end examples
