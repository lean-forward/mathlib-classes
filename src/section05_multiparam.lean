-- Boilerplate:
import algebra.group.defs
import algebra.module.basic
import algebra.ring.basic
namespace examples

/-
Following the pattern of monoids, the base class introduces notation, and is subclassed to add the axioms of the structure:
-/
-- Adapted from `algebra/group/defs.lean:47`
class has_scalar (α β : Type*) :=
(smul : α → β → β)
infix • := has_scalar.smul

-- Adapted from `group_theory/group_action/defs.lean:85`
class mul_action (M A : Type*) [monoid M] extends has_scalar M A :=
(one_smul : ∀ (x : A), (1 : M) • x = x)
(mul_smul : ∀ (r s : M) (x : A), (r * s) • x = r • (s • x))

-- Adapted from `group_theory/group_action/defs.lean:446`
class distrib_mul_action (M A : Type*) [monoid M] [add_monoid A]
  extends mul_action M A :=
(smul_add : ∀ (r : M) (x y : A), r • (x + y) = r • x + r • y)
(smul_zero : ∀ (r : M), r • (0 : A) = 0)

-- Adapted from `algebra/module/basic.lean:50`
class module (R M : Type*) [semiring R] [add_comm_monoid M]
  extends distrib_mul_action R M :=
(add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x)
(zero_smul : ∀ (x : M), (0 : R) • x = 0)

namespace extend
/-
Namely, declaring that `module R M extends add_comm_monoid M`
-/
class module (R M : Type*) [semiring R] extends add_comm_monoid M, distrib_mul_action R M :=
(add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x)
(zero_smul : ∀ (x : M), (0 : R) • x = 0)
/-
would generate the following instance:
-/
#print module.to_add_comm_monoid
end extend

namespace out
/-
[W]e can make `R` a functional dependency of `M` by instead defining:
-/
class module (R : out_param Type*) (M : Type*) [semiring R]
  extends add_comm_monoid M, distrib_mul_action R M :=
(add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x)
(zero_smul : ∀ (x : M), (0 : R) • x = 0)
end out

/-
For `module` this functional dependency is not acceptable
since each `add_comm_monoid M` has a natural `module ℕ M` structure given by the instance `add_comm_monoid.nat_module` -/
#check add_comm_monoid.nat_module

/-
A final way to resolve dangerous instances is to remove the \lstinline{instance} keyword so that it does not participate in synthesis.
\mathlib takes this approach when stating the theorem that any module over a ring has additive inverses:
-/
-- Adapted from `algebra/module/basic.lean:170`
def module.add_comm_monoid_to_add_comm_group (R M : Type*)
  [ring R] [add_comm_monoid M] [module R M] :
  add_comm_group M :=
{ neg          := λ a, (-1 : R) • a,
  add_left_neg := λ a, show (-1 : R) • a + a = 0, by
  { nth_rewrite 1 ← mul_action.one_smul a,
    rw [← module.add_smul, add_left_neg, module.zero_smul] },
  ..(infer_instance : add_comm_monoid M), }

end examples
