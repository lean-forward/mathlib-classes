-- Boilerplate:
import analysis.normed_space.lp_space
import data.zmod.basic
import field_theory.splitting_field
import geometry.manifold.instances.real
import group_theory.specific_groups.dihedral
namespace examples

namespace unfact
/-
Thus, we could define a class `nat.prime n` asserting `n : ℕ` is a prime number,
and take an instance of this class as a parameter of the `zmod.field` instance:
-/
class nat.prime (n : ℕ) : Prop :=
(nontrivial : 2 ≤ n) (only_two_divisors : ∀ m ∣ n, m = 1 ∨ m = n)

-- Adapted from `data/zmod/basic.lean:74`
def zmod' : ℕ → Type
| 0     := ℤ
| (n+1) := fin (n+1)

-- Adapt the definition of `nat.prime` so we don't need to copy the implementation of `zmod`:
instance (n : ℕ) [h : nat.prime n] : fact (n.prime) :=
⟨nat.prime_def_lt.mpr ⟨h.nontrivial, λ m lt dvd, (nat.prime.only_two_divisors m dvd).resolve_right lt.ne⟩⟩

-- Adapted from `data/zmod/basic.lean:836`
instance zmod.field (n : ℕ) [nat.prime n] : field (zmod n) :=
{ mul_inv_cancel := begin
    intros a h,
    obtain ⟨k, rfl⟩ := zmod.nat_cast_zmod_surjective a,
    apply zmod.coe_mul_inv_eq_one,
    apply nat.coprime.symm,
    rwa [nat.prime.coprime_iff_not_dvd (fact.out n.prime), ← char_p.cast_eq_zero_iff (zmod n)]
  end,
  inv_zero := zmod.inv_zero n,
  .. zmod.comm_ring n,
  .. zmod.has_inv n,
  .. zmod.nontrivial n }

end unfact

namespace fact

/-
Instead \mathlib provides a mechanism for ad hoc typeclass creation,
by supplying a proposition to the `fact` class:
-/
-- Adapted from `data/nat/prime.lean:39`
def nat.prime (n : ℕ) : Prop := 2 ≤ n ∧ (∀ m ∣ n, m = 1 ∨ m = n)

-- Adapted from `logic/basic.lean:191`
class fact' (p : Prop) : Prop := (out : p)

-- Adapt the definition of `nat.prime` so we don't need to copy the implementation of `zmod`:
instance (n : ℕ) [h : fact (nat.prime n)] : fact (n.prime) :=
⟨nat.prime_def_lt.mpr ⟨(fact.out (nat.prime n)).1, λ m lt dvd, ((fact.out (nat.prime n)).2 m dvd).resolve_right lt.ne⟩⟩

-- Adapted from `data/zmod/basic.lean:836`
instance zmod.field (n : ℕ) [fact (nat.prime n)] : field (zmod n) :=
{ mul_inv_cancel := begin
    intros a h,
    obtain ⟨k, rfl⟩ := zmod.nat_cast_zmod_surjective a,
    apply zmod.coe_mul_inv_eq_one,
    apply nat.coprime.symm,
    rwa [nat.prime.coprime_iff_not_dvd (fact.out n.prime), ← char_p.cast_eq_zero_iff (zmod n)]
  end,
  inv_zero := zmod.inv_zero n,
  .. zmod.comm_ring n,
  .. zmod.has_inv n,
  .. zmod.nontrivial n }

end fact

/-
In a similar way, the \lstinline{fact} class is used for the assumption \lstinline{x < y} when showing that the interval $[x, y] \subset \R$ is a manifold with boundary,
-/
#print set.Icc.smooth_manifold_with_corners
/-
to provide the natural inclusion of the splitting field of a polynomial $f$ into an arbitrary field under the assumption that $f$ splits,
-/
#print polynomial.splitting_field.algebra
/-
and to provide non-negativity or positivity assumptions in various contexts.
-/
#print dihedral_group.fintype
#print lp.normed_space
#print zmod.nontrivial

/-
Along with the ad hoc class pattern provided by `fact`,
there is an ad hoc instance pattern provided by the tactic `letI`.
-/
#print tactic.interactive.letI
/-
The `letI` tactic is also called by the `nontriviality` tactic that performs a case distinction on whether
a given type `α` satisfies `subsingleton α` or `nontrivial α`, adding the relevant instance to the context using `letI`.
-/
#print tactic.interactive.nontriviality

end examples
