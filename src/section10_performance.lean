-- Boilerplate:
import data.nat.basic
import group_theory.congruence
namespace examples

section unbundled

/-
This example concerns product type instances of an unbundled class such as the following modification to the `comm_monoid` class:
-/
class semigroup (G : Type*) [has_mul G] := (mul_assoc : ∀ (x y z : G), (x * y) * z = x * (y * z))
class mul_one_class (M : Type*) [has_one M] [has_mul M].
class comm_semigroup (G : Type*) [has_mul G] [semigroup G].
class monoid (M : Type*) [has_mul M] [has_one M] [semigroup M] [mul_one_class M].
class comm_monoid (M : Type*) [has_mul M] [has_one M] [semigroup M] [mul_one_class M] [monoid M] [comm_semigroup M].

/-
Providing an instance for the natural numbers is straightforward, although it now involves instantiating each step in the hierarchy separately:
-/
instance : semigroup ℕ := ⟨mul_assoc⟩
instance : mul_one_class ℕ := ⟨⟩
instance : comm_semigroup ℕ := ⟨⟩
instance : monoid ℕ := ⟨⟩
instance : comm_monoid ℕ := ⟨⟩
/-
When we want to instantiate the commutative monoid structure on the product of two commutative monoids, we see that the length of types starts to grow noticeably:
-/
variables {G H M N : Type*}
instance prod.has_mul [has_mul G] [has_mul H] : has_mul (G × H) :=
{ mul := λ a b, (a.1 * b.1, a.2 * b.2) }
@[simp] lemma prod.mul_def [has_mul G] [has_mul H]
  (a b : G) (c d : H) : (a, c) * (b, d) = (a * b, c * d) := rfl

instance prod.has_one [has_one G] [has_one H] : has_one (G × H) :=
{ one := (1, 1) }
@[simp] lemma prod.one_def [has_one G] [has_one H] :
  (1 : G × H) = (1, 1) := rfl

instance prod.semigroup [has_mul G] [has_mul H]
  [semigroup G] [semigroup H] : semigroup (G × H) :=
⟨λ x y z, by { cases x, cases y, cases z, simp only [prod.mul_def, semigroup.mul_assoc] }⟩
instance prod.comm_semigroup [has_mul G] [has_mul H]
  [semigroup G] [semigroup H] [comm_semigroup G] [comm_semigroup H] :
  comm_semigroup (G × H) :=
⟨⟩
instance prod.mul_one_class [has_mul G] [has_mul H] [has_one G] [has_one H]
  [mul_one_class G] [mul_one_class H] : mul_one_class (G × H) :=
⟨⟩
instance prod.monoid [has_mul M] [has_mul N] [has_one M] [has_one N]
  [semigroup M] [semigroup N] [mul_one_class M] [mul_one_class N] :
  monoid (M × N) :=
⟨⟩
instance prod.comm_monoid
  [has_one M] [has_one N] [has_mul M] [has_mul N]
  [semigroup M] [semigroup N] [mul_one_class M] [mul_one_class N]
  [monoid M] [monoid N] [comm_semigroup M] [comm_semigroup N]
  [comm_monoid M] [comm_monoid N] :
  comm_monoid (M × N) :=
⟨⟩
/-
The linear growth in the types translates to an exponential growth in the term size of concrete instances,
since each instance parameter implicit in `comm_monoid (ℕ × ⋯ × ℕ)` is filled with a term that has itself the same number of instance arguments.
-/

set_option pp.implicit true
#check (by apply_instance : comm_monoid ℕ)
#check (by apply_instance : comm_monoid (ℕ × ℕ))
#check (by apply_instance : comm_monoid (ℕ × ℕ × ℕ))
#check (by apply_instance : comm_monoid (ℕ × ℕ × ℕ × ℕ))
#check (by apply_instance : comm_monoid (ℕ × ℕ × ℕ × ℕ × ℕ))
-- and so on

end unbundled

section fails_quickly

/-
The `fails_quickly` linter can also detect timeouts caused by looping or diverging synthesis,
for example the loop `nonempty → has_bot → nonempty` in the following code:
-/

-- Adapted from `order/bounded_order.lean:54`
-- `has_bot.bot` is notation for the minimum element of `α`
class has_bot (α : Type*) := (bot : α)

-- Adapted from `order/bounded_order.lean:60`
instance has_bot_nonempty (α : Type*) [has_bot α] : nonempty α :=
⟨has_bot.bot⟩

-- The natural numbers are well-ordered so each nonempty subtype has a bottom element.
-- Adapted from `data/nat/basic.lean:106`
instance nat.subtype.has_bot (s : set ℕ) [decidable_pred (∈ s)] [h : nonempty s] :
  has_bot s :=
{ bot := ⟨nat.find (nonempty_subtype.1 h), nat.find_spec (nonempty_subtype.1 h)⟩ }

#lint only fails_quickly

end fails_quickly

section priority

-- Adapted from `group_theory/congruence.lean:209`
@[priority 500] -- Reduce the priority from 1000 to 500 since it's slow to apply.
instance con.quotient.decidable_eq {M : Type*} [has_mul M] (c : con M)
  [d : ∀ (a b : M), decidable (c a b)] : decidable_eq (con.quotient c) :=
@quotient.decidable_eq M c.to_setoid d

end priority

end examples
