-- Boilerplate:
import algebra.algebra.basic
import algebra.big_operators.basic
import data.equiv.ring
namespace examples
open_locale big_operators

/-
The `is_ring_hom` predicate stated `f} preserves the ring operations `*`, `+`, `1` and `0`.
Instances were available for the common operations, except composition:
-/
-- Adapted from `deprecated/group.lean:77`
class is_monoid_hom {M N : Type*} [monoid M] [monoid N] (f : M → N) : Prop :=
(map_mul : ∀ x y : M, f (x * y) = f x * f y)
(map_one : f 1 = 1)

-- Adapted from `deprecated/ring.lean:64`
class is_ring_hom {R S : Type*} [semiring R] [semiring S] (f : R → S)
  extends is_monoid_hom f :=
(map_add : ∀ x y : R, f (x + y) = f x + f y)
(map_zero : f 0 = 0)

-- Adapted from `deprecated/ring.lean:93`
instance id.is_ring_hom (R : Type*) [semiring R] :
  is_ring_hom (id : R → R) :=
{ map_mul := λ _ _, rfl,
  map_one := rfl,
  map_add := λ _ _, rfl,
  map_zero := rfl }

-- Adapted from `deprecated/ring.lean:97`
lemma comp.is_ring_hom {R S T : Type*} (f : R → S) (g : S → T)
  [semiring R] [semiring S] [semiring T] [hf : is_ring_hom f] [hg : is_ring_hom g] :
  is_ring_hom (g ∘ f) :=
{ map_add := λ x y, by simp [hf.map_add]; rw hg.map_add; refl,
  map_mul := λ x y, by simp [hf.map_mul]; rw hg.map_mul; refl,
  map_one := by simp [hf.map_one]; exact hg.map_one,
  map_zero := by simp [hf.map_zero]; exact hg.map_zero }

/-!--------------
Bundled morphisms
----------------/

namespace bundled
/-
For these reasons, \mathlib was refactored to prefer bundled morphisms:
-/
-- Adapted from `algebra/group/hom.lean:248`
structure monoid_hom (M N : Type*) [monoid M] [monoid N] :=
(to_fun : M → N)
(map_mul : ∀ x y, to_fun (x * y) = to_fun x * to_fun y)
(map_one : to_fun 1 = 1)

-- Adapted from `algebra/ring/basic.lean:329`
structure ring_hom (R S : Type*) [semiring R] [semiring S]
  extends monoid_hom R S :=
{map_add : ∀ x y, to_fun (x + y) = to_fun x + to_fun y}
(map_zero : to_fun 0 = 0)

-- Adapted from `algebra/group/hom.lean:406`
instance monoid_hom.has_coe_to_fun (M N : Type*) [monoid M] [monoid N] :
  has_coe_to_fun (monoid_hom M N) (λ _, M → N) :=
{ coe := monoid_hom.to_fun }

-- Adapted from `algebra/group/hom.lean:661`
def monoid_hom.id (M : Type*) [monoid M] : monoid_hom M M :=
{ to_fun := id,
  map_one := rfl,
  map_mul := λ _ _, rfl }

-- Adapted from `algebra/group/hom.lean:688`
def monoid_hom.comp {M N O : Type*} [monoid M] [monoid N] [monoid O]
  (f : monoid_hom M N) (g : monoid_hom N O) : monoid_hom M O :=
{ to_fun := g ∘ f,
  map_one := by simp [coe_fn, has_coe_to_fun.coe, monoid_hom.has_coe_to_fun, monoid_hom.map_one],
  map_mul := by simp [coe_fn, has_coe_to_fun.coe, monoid_hom.has_coe_to_fun, monoid_hom.map_mul] }

/-
[T]he additive group endomorphism of a ring given by multiplying by a constant \lstinline{c}:
-/
-- Adapted from `deprecated/group.lean:71`
class is_add_monoid_hom {M N : Type*} [add_monoid M] [add_monoid N] (f : M → N) : Prop :=
(map_add : ∀ x y : M, f (x + y) = f x + f y)
(map_zero : f 0 = 0)

-- Adapted from `deprecated/group.lean:166`
instance mul.is_add_monoid_hom {R : Type*} [ring R] (c : R) :
  is_add_monoid_hom ((*) c) :=
{ map_zero := mul_zero c,
  map_add := mul_add c }

-- Adapted from `algebra/ring/basic.lean:303`
def add_monoid_hom.mul_left {R : Type*} [ring R] (c : R) :
  add_monoid_hom R R :=
{ to_fun := (*) c,
  map_zero' := mul_zero c,
  map_add' := mul_add c }
end bundled

#check monoid_hom.map_prod

/-
Thus \mathlib ended up with many copies of lemmas such as `map_prod`:
-/
-- Adapted from `algebra/big_operators/basic.lean:111`
lemma monoid_hom.map_prod {ι M N : Type*} (s : finset ι) (f : ι → M) [comm_monoid M] [comm_monoid N]
  (g : monoid_hom M N) :
  g (∏ i in s, f i) = ∏ i in s, g (f i) :=
by simp only [finset.prod_eq_multiset_prod, g.map_multiset_prod, multiset.map_map]

-- Adapted from `algebra/big_operators/basic.lean:144`
lemma ring_hom.map_prod {ι R S : Type*} (s : finset ι) (f : ι → R) [comm_semiring R] [comm_semiring S]
  (g : ring_hom R S) :
  g (∏ i in s, f i) = ∏ i in s, g (f i) :=
monoid_hom.map_prod s f g.to_monoid_hom

-- Adapted from `algebra/big_operators/basic.lean:116`
lemma mul_equiv.map_prod {ι M N : Type*} (s : finset ι) (f : ι → M) [comm_monoid M] [comm_monoid N]
  (g : mul_equiv M N) :
  g (∏ i in s, f i) = ∏ i in s, g (f i) :=
monoid_hom.map_prod s f g.to_monoid_hom

-- Adapted from `data/equiv/ring.lean:386`
lemma ring_equiv.map_prod {ι R S : Type*} (s : finset ι) (f : ι → R) [comm_semiring R] [comm_semiring S]
  (g : ring_equiv R S) :
  g (∏ i in s, f i) = ∏ i in s, g (f i) :=
monoid_hom.map_prod s f g.to_monoid_hom

-- Adapted from `algebra/algebra/basic.lean:704`
lemma alg_hom.map_prod {ι R A B : Type*} (s : finset ι) (f : ι → A) [comm_semiring R]
  [comm_semiring A] [comm_semiring B] [algebra R A] [algebra R B]
  (g : alg_hom R A B) :
  g (∏ i in s, f i) = ∏ i in s, g (f i) :=
ring_hom.map_prod s f g.to_ring_hom

-- Adapted from `algebra/algebra/basic.lean:1142`
lemma alg_equiv.map_prod {ι R A B : Type*} (s : finset ι) (f : ι → A) [comm_semiring R]
  [comm_semiring A] [comm_semiring B] [algebra R A] [algebra R B]
  (g : alg_equiv R A B) :
  g (∏ i in s, f i) = ∏ i in s, g (f i) :=
g.to_alg_hom.map_prod f s

/-!-------------
Morphism classes
---------------/

/-
My first step in introducing this interface was a typeclass `fun_like` for *types* of bundled (dependent) functions,
based on Eric Wieser's `set_like` class for types of bundled subobjects. (https://github.com/leanprover-community/mathlib/pull/6768)
-/
-- Adapted from `library/init/coe.lean:54`
class has_coe_to_fun' (F : Type*) (α : out_param (F → Type*)) :=
(coe : Π x : F, α x)

-- Adapted from `data/fun_like/basic.lean:127`
class fun_like (F : Type*)
  (α : out_param Type*) (β : out_param (α → Type*))
  extends has_coe_to_fun F (λ _, Π a : α, β a) :=
(coe_injective' : function.injective to_has_coe_to_fun.coe)

-- A typical instance looks like:
instance monoid_hom.fun_like {M N : Type*} [monoid M] [monoid N] :
  fun_like (monoid_hom M N) M (λ _, N) :=
{ coe := monoid_hom.to_fun,
  coe_injective' := λ f g h, by { cases f, cases g, congr' } }
/-
The next step in addressing the duplication is to introduce a class for
the bundled morphism types that coerce to `monoid_hom`:
-/
-- Adapted from `algebra/group/hom.lean:260`
class monoid_hom_class (F : Type*) (M N : out_param Type*)
  [monoid M] [monoid N] extends fun_like F M (λ _, N) :=
(map_one : ∀ (f : F), f 1 = 1)
(map_mul : ∀ (f : F) (x y : M), f (x * y) = f x * f y)

-- Adapted from `algebra/group/hom.lean:265`
instance monoid_hom.monoid_hom_class {M N : Type*} [monoid M] [monoid N] :
  monoid_hom_class (monoid_hom M N) M N :=
{ coe := monoid_hom.to_fun,
  coe_injective' := λ f g h, by { cases f, cases g, congr' },
  map_one := monoid_hom.map_one',
  map_mul := monoid_hom.map_mul' }

/-
The types such as \lstinline{ring_hom} extending \lstinline{monoid_hom} should receive a \lstinline{monoid_hom_class} instance,
which we can do by subclassing \lstinline{monoid_hom_class} and instantiating the subclass:
-/
-- Adapted from `algebra/ring/basic.lean:354`
class ring_hom_class (F : Type*) (R S : out_param Type*)
  [semiring R] [semiring S]
  extends monoid_hom_class F R S :=
(map_zero : ∀ (f : F), f 0 = 0)
(map_add : ∀ (f : F) (x y : R), f (x + y) = f x + f y)

-- Adapted from `algebra/ring/basic.lean:382`
instance ring_hom.ring_hom_class {R S : Type*} [semiring R] [semiring S] :
  ring_hom_class (ring_hom R S) R S :=
{ coe := ring_hom.to_fun,
  coe_injective' := λ f g h, by { cases f, cases g, congr' },
  map_mul := ring_hom.map_mul',
  map_one := ring_hom.map_one',
  map_add := ring_hom.map_add',
  map_zero := ring_hom.map_zero' }

/-
Now lemmas can be made generic by parametrising over all the types of bundled morphisms,
reducing the multiplicative amount of lemmas to an additive amount:
each extension of \lstinline{monoid_hom} should get a \lstinline{monoid_hom_class} instance,
and each operation preserved by \lstinline{monoid_hom}s should get a lemma taking a \lstinline{monoid_hom_class} parameter.
-/
lemma map_prod {ι M N : Type*} (s : finset ι) (f : ι → M) [comm_monoid M] [comm_monoid N]
  {G : Type*} [monoid_hom_class G M N] (g : G) :
  g (∏ i in s, f i) = ∏ i in s, g (f i) :=
begin
  letI := classical.dec_eq ι,
  refine finset.induction_on s _ _,
  { simp [monoid_hom_class.map_one] },
  { intros i s hi ih,
    simp [finset.prod_insert hi, monoid_hom_class.map_mul, ih] },
end

end examples
