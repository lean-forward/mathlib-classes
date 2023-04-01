-- Boilerplate:
import algebra.group.type_tags
import algebra.group.opposite
import data.nat.prime
import data.zmod.basic
import field_theory.finite.basic
import order.synonym
import ring_theory.integral_domain
noncomputable theory
namespace examples
variables {α : Type*}

/-
`multiplicative α` is declared to be a synonym of the type `α` onto which we can safely copy the monoid instance:
-/
-- Adapted from `algebra/group/type_tags.lean:37`
def multiplicative' (α : Type*) := α
-- Adapted from `algebra/group/type_tags.lean:195`
instance [h : add_monoid α] : monoid (multiplicative α) :=
{ one     := (0 : α),
  mul     := λ x y, (x + y : α),
  npow   := @add_monoid.nsmul α h,
  npow_zero' := add_monoid.nsmul_zero',
  npow_succ' := add_monoid.nsmul_succ',
  ..multiplicative.mul_one_class,
  ..multiplicative.semigroup }

/-
Other type synonyms used in mathlib include
`mul_opposite`, the multiplicative opposite where the left and right arguments to multiplications are swapped,
`lex`, used to equip a product of partial orders with the lexicographic order instead of pointwise comparison,
and `order_dual`, the dual order where the left and right arguments to < and ≤ are swapped.
-/
#print mul_opposite
#print lex
#print order_dual

/-
Using this technique, mathlib could redefine the `*` operator as notation for `binop mul` and `+` notation for `binop add`, where `mul` and `add` are different constants of some unspecified type.
-/
inductive binop_display : Type
| mul
| add

class has_binop (α : Type*) (d : binop_display) :=
(binop : α → α → α)
export has_binop (binop) -- move `binop` into the surrounding namespace

instance [has_binop α binop_display.mul] : has_mul α := ⟨binop binop_display.mul⟩
instance [has_binop α binop_display.add] : has_add α := ⟨binop binop_display.add⟩

open subgroup submonoid

/-
Using the type `mul_equiv` of (multiplicative) group isomorphisms,
`multiplicative` allows us to state the multiplicative subgroup of the field ℤ/pℤ is
cyclic when p is prime, by stating it is isomorphic to ℤ/(p − 1)ℤ:
-/
def powers_mul_equiv_powers {G H : Type*} [group G] [fintype G] [group H] [fintype H]
  (x : G) (y : H) (h : order_of x = order_of y) :
  mul_equiv (powers x) (powers y) :=
{ to_fun := λ g, fin_equiv_powers y (fin.cast h ((fin_equiv_powers x).symm g)),
  map_mul' := begin
    rintro ⟨_, ⟨n, rfl⟩⟩ ⟨_, ⟨k, rfl⟩⟩,
    simp only [fin_equiv_powers_apply, fin.coe_cast, fin_equiv_powers_symm_apply,
      fin.coe_mk],
    apply subtype.ext,
    have : (⟨x ^ n * x ^ k, _⟩ : powers x) = ⟨x ^ (n + k), ⟨n + k, rfl⟩⟩,
    { ext,
      rw [subtype.coe_mk, subtype.coe_mk, pow_add] },
    conv_lhs { erw [submonoid.mk_mul_mk, subtype.coe_mk, this] },
    conv_rhs
    { erw [submonoid.mk_mul_mk, subtype.coe_mk],
      rw [h, ← pow_eq_mod_order_of, ← pow_eq_mod_order_of] },
    rw [fin_equiv_powers_symm_apply, fin.coe_mk, h, ← pow_eq_mod_order_of, pow_add],
  end,
  ..((fin_equiv_powers x).symm.trans ↑(fin.cast h)).trans (fin_equiv_powers y) }

def is_cyclic.equiv {G H : Type*} [group G] [fintype G] [group H] [fintype H]
  (hG : is_cyclic G) (hH : is_cyclic H)
  (hn : fintype.card G = fintype.card H) :
  mul_equiv G H :=
begin
  unfreezingI
  { choose x hx using @is_cyclic.exists_monoid_generator G _ _ _,
    choose y hy using @is_cyclic.exists_monoid_generator H _ _ _, },
  let e : G ≃* powers x,
  { have : powers x = ⊤,
    { exact eq_top_iff.mpr (λ g _, hx g) },
    rw this,
    exact submonoid.top_equiv.symm },
  let f : H ≃* powers y,
  { have : powers y = ⊤,
    { exact eq_top_iff.mpr (λ h _, hy h) },
    rw this,
    exact submonoid.top_equiv.symm },
  refine (e.trans (powers_mul_equiv_powers x y _)).trans f.symm,
  rw [order_of_eq_card_of_forall_mem_zpowers, order_of_eq_card_of_forall_mem_zpowers, hn],
  { exact λ h, mem_powers_iff_mem_zpowers.mp (hy _) },
  { exact λ g, mem_powers_iff_mem_zpowers.mp (hx _) },
end

instance : Π (p : ℕ) [fact (nat.prime p)], ne_zero (p - 1)
| 0 hp := (not_irreducible_zero hp.out).elim
| 1 hp := (not_irreducible_one hp.out).elim
| (p + 2) hp := ⟨by simp⟩

def zmod.units_equiv_zmod (p : ℕ) (hp : nat.prime p) :
  mul_equiv (units (zmod p)) (multiplicative (zmod (p - 1))) :=
by letI : fact (nat.prime p) := ⟨hp⟩; exact
is_cyclic.equiv
  units.is_cyclic
  ⟨⟨(1 : zmod (p - 1)), λ x, ⟨x.val,
    (show (x.val : ℤ) • (1 : zmod (p - 1)) = x,
      by rw [int.smul_one_eq_coe, zmod.nat_cast_val]; simp)⟩⟩⟩
  ((zmod.card_units p).trans (zmod.card _).symm)

end examples
