namespace examples

/-
As an example, the `comm_monoid` typeclass is implemented in \mathlib essentially as follows:
-/
set_option old_structure_cmd true -- explained below

-- Adapted from `algebra/group/defs.lean:189`
class semigroup (G : Type*) extends has_mul G :=
(mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))

-- Adapted from `algebra/group/defs.lean:305`
class mul_one_class (M : Type*) extends has_one M, has_mul M :=
(one_mul : ∀ a : M, 1 * a = a) (mul_one : ∀ a : M, a * 1 = a)

-- Adapted from `algebra/group/defs.lean:211`
class comm_semigroup (G : Type*) extends semigroup G :=
(mul_comm : ∀ a b : G, a * b = b * a)

-- Adapted from `algebra/group/defs.lean:465`
class monoid (M : Type*) extends semigroup M, mul_one_class M

-- Adapted from `algebra/group/defs.lean:509`
class comm_monoid (M : Type*) extends monoid M, comm_semigroup M

/-
Compare the following two desugarings of `extends`:
-/
class monoid_new (M : Type*) :=
(to_semigroup : semigroup M)
(to_mul_one_class : mul_one_class M)

class monoid_old (M : Type*) :=
(mul : M → M → M) (infix (name := mul') * := mul)
(mul_assoc : ∀ a b c : M, (a * b) * c = a * (b * c))
(one : M) (notation 1 := one)
(one_mul : ∀ a : M, 1 * a = a)
(mul_one : ∀ a : M, a * 1 = a)

end examples
