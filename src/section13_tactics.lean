-- Boilerplate:
import tactic.ring
namespace examples

/-
Lean also offers a built-in tactic `tactic.mk_instance : expr → tactic expr` that takes a goal type and performs synthesis.
-/
#check tactic.mk_instance

/-
the tactic `ring` for solving equalities in the language of commutative (semi)rings
-/
#check tactic.interactive.ring

/-
mathlib provides a `instance_cache` structure that allows tactic programmers to explicitly store common instances
-/
#print tactic.instance_cache

/-
Suppose that we completely unbundle the operation and identity element from the `monoid` class:
-/
class monoid (M : Type*) (op : M → M → M) (id : M) :=
(id_op : ∀ x, op id x = x)
(op_id : ∀ x, op x id = x)
(op_assoc : ∀ x y z, op (op x y) z = op x (op y z))

#check monoid.op_id

end examples
