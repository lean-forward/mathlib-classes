import algebra.order.hom.basic

namespace examples

section mul_equiv_map_one

/-
For example, a bijection that preserves multiplication also preserves an identity element in a monoid, which we express through the following instance:
-/
-- adapted from algebra/group/hom/equiv.lean:88
class mul_equiv_class' (F : Type*) (M N : out_param Type*)
  [has_mul M] [has_mul N] extends mul_hom_class F M N :=
(bijective : ∀ (e : F), function.bijective e)

open mul_equiv_class

-- adapted from algebra/group/hom/equiv.lean:107
instance mul_equiv_class.monoid_hom_class (F : Type*) {M N : Type*}
  [monoid M] [monoid N] [mul_equiv_class F M N] :
  monoid_hom_class F M N :=
{ coe := (coe : F → M → N),
  map_one := λ e,
  calc e 1 = e 1 * 1 : (mul_one _).symm
       ... = e 1 * e (inv e (1 : N) : M) : congr_arg _ (right_inv e 1).symm
       ... = e (inv e (1 : N)) : by rw [← _root_.map_mul, one_mul]
       ... = 1 : right_inv e 1,
  .. mul_equiv_class.mul_hom_class F }

/-
suppose Lean infers the type of the application `map_one e` where `e : mul_equiv M N`.
-/
structure M : Type
structure N : Type

instance : has_mul M := ⟨λ _ _, ⟨⟩⟩
instance : has_mul N := ⟨λ _ _, ⟨⟩⟩

instance : monoid M :=
{ mul := (*),
  one := ⟨⟩,
  mul_one := by rintro ⟨⟩; refl,
  one_mul := by rintro ⟨⟩; refl,
  mul_assoc := by rintro ⟨⟩ ⟨⟩ ⟨⟩; refl }
instance : monoid N :=
{ mul := (*),
  one := ⟨⟩,
  mul_one := by rintro ⟨⟩; refl,
  one_mul := by rintro ⟨⟩; refl,
  mul_assoc := by rintro ⟨⟩ ⟨⟩ ⟨⟩; refl }

def e : mul_equiv M N :=
{ to_fun := λ _, ⟨⟩,
  inv_fun := λ _, ⟨⟩,
  map_mul' := λ _ _, rfl,
  left_inv := by rintro ⟨⟩; refl,
  right_inv := by rintro ⟨⟩; refl }

/-
set_option trace.class_instances true
set_option trace.type_context.is_def_eq_detail true
-/
example : e (1 : M) = (1 : N) :=
begin
  have := map_one e,
  exact this
end

end mul_equiv_map_one

/-
Concretely, the inheritance graph should not contain the following shape:
-/
set_option old_structure_cmd true

class root (α : Type) : Type :=
(value : α)
class left (α : Type) extends root α
class right (α : Type) extends root α
class leaf (α : Type) extends left α, right α

class bottom (α : Type) (β : out_param Type) [root β]
class middle (α : Type) (β : out_param Type) [root β]
class top (α : Type) (β : out_param Type) [root β]

instance top.to_middle {α β} [left β] [top α β] : middle α β := ⟨⟩
instance middle.to_bottom {α β} [right β] [middle α β] : bottom α β := ⟨⟩

instance top.to_bottom {α β} [leaf β] [top α β] : bottom α β :=
by apply_instance -- Fails

/-
In particular, this occurs in the declaration of `ring_seminorm_class` as subclass of add_group_seminorm_class under the assumption of an ordered_semiring,
-/
#check ring_seminorm_class.to_add_group_seminorm_class
/-
which is itself a subclass of `nonneg_hom_class` under the assumption of `linear_ordered_add_comm_monoid`;
-/
#check add_group_seminorm_class.to_nonneg_hom_class
/-
the assumptions have a common descendant `linear_ordered_semiring` which cannot be reliably synthesised due to this limitation.
-/
#check linear_ordered_semiring
/-
The workaround in this case was to declare `ring_seminorm_class` directly as subclass of `nonneg_hom_class`
-/
#check ring_seminorm_class.to_nonneg_hom_class

end examples
