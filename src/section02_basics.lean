-- Boilerplate:
import algebra.group.basic
import algebra.pointwise
import data.int.basic
open has_add has_neg
namespace examples

/-
Let us start with the following two Lean declarations, not found in \mathlib, showing the main forms that parameters can take in Lean.
-/
def sub {A : Type*} [add_group A] (a b : A) : A :=
add a (neg b)

lemma sub_eq_add_neg {A : Type*} [add_group A] (a b : A) :
  sub a b = add a (neg b) := by refl

/-
For example, defining `add_group ℤ` instance allows us to subtract two integers using the `sub` operator we defined above:
-/
instance : add_group ℤ := by apply_instance
lemma subtraction_example : (sub 42 37 : ℤ) = 5 := by refl
/-
Instance parameters are considered a form of implicit parameters, and can thus be made explicit using the `@` operator:
-/
#check sub
#check @sub
/-
Here `?M_1` stands for a free metavariable that the elaborator could not (yet) fill in.

Instance declarations can themselves have their own instance parameters.
For example, the subsets of a monoid form a monoid under pointwise operations, which we can express as
-/
open set

-- Adapted from `algebra/pointwise.lean:241`
instance pointwise_monoid {A : Type*} [monoid A] : monoid (set A) :=
{ mul := image2 has_mul.mul,
  mul_assoc := λ _ _ _, set.image2_assoc mul_assoc,
  one := {1},
  mul_one := λ s, by simp,
  one_mul := λ s, by simp }

/-!--------------
Class definitions
-----------------/

/-
Thus, a definition for `add_group` could look like:
-/
-- Adapted from `algebra/group/defs.lean:607`
class add_group (A : Type*) :=
(zero : A) (neg : A → A) (add : A → A → A)
(add_assoc : ∀ (x y z : A), add x (add y z) = add (add x y) z)
(zero_add : ∀ (x : A), add zero x = x)
(neg_add : ∀ (x : A), add (neg x) x = zero)
/-
The projections of a class automatically use instance parameters, generating the declarations:
-/
#print add_group.zero
#print add_group.neg
#print add_group.add
#print add_group.add_assoc
-- and so on.

/-!--------
Subclassing
----------/

/-
To define abelian groups as a subclass of additive groups, we write
-/
namespace unbundled
open examples.add_group

-- Adapted from `algebra/group/defs.lean:668`
class add_comm_group (A : Type*) [add_group A] :=
(add_comm : ∀ (x y : A), add x y = add y x)
end unbundled

namespace bundled
class add_comm_group (A : Type*) extends add_group A :=
(add_comm : ∀ (x y : A), add x y = add y x)
end bundled
/-
This has analogous effects to writing
-/
namespace bundled_expanded
class add_comm_group (A : Type*) :=
(to_add_group : add_group A)
(add_comm : ∀ (x y : A),
  @add_group.add A to_add_group x y = @add_group.add A to_add_group y x)
-- Register the projection as an instance:
attribute [instance] add_comm_group.to_add_group
end bundled_expanded

/-!--------------------------------
Extensions of the typeclass pattern
----------------------------------/

/-
For example, \mathlib uses a typeclass parametrized over a natural number $p$ to express the characteristic of a ring:
-/
-- Adapted from `algebra/char_p/basic.lean:21`
class char_p (R : Type*) [semiring R] (p : ℕ) : Prop :=
(cast_eq_zero_iff : ∀ (x : ℕ), (coe x : R) = 0 ↔ p ∣ x)

end examples
