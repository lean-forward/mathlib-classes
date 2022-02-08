-- Boilerplate
import algebra.group.units
import logic.basic
namespace examples

/-
For example, `subsingleton : Π (α : Type*), Prop` asserts the type `α` has at most one element:
-/
-- Adapted from `library/init/logic.lean:808`
class subsingleton (α : Type*) : Prop := (h : ∀ (a b : α), a = b)
/-
The subclass `unique α` of `subsingleton α` (constructively) asserts that `α` has exactly one element.
-/
class unique (α : Type*) extends subsingleton α :=
(default : α)
/-
This means `unique α` is also a subclass of `inhabited α`, which (constructively) specifies an element of `α` while also allowing for more.
-/
-- Adapted from `library/init/logic.lean:775`
class inhabited (α : Type*) := (default : α)

instance unique.to_inhabited (α : Type*) [h : unique α] := { ..h }

/-
A theorem about trivial monoids will take these assumptions as separate parameters `[monoid M] [subsingleton M]`:
-/
instance units.unique {M : Type*} [monoid M] [subsingleton M] : unique (units M) :=
{ default := 1,
  h := λ x y, by { cases x, cases y, congr; apply subsingleton.h } }

/-
In fact, `unique α` is equivalent to the conjunction of `subsingleton α` and `inhabited α`.
However, the implication `∀ {α}, subsingleton α → inhabited α → unique α` cannot be added while keeping `subsingleton` and `inhabited` superclasses of `unique`,
since that would result in an infinite loop `unique → subsingleton → unique → subsingleton → ⋯` during instance synthesis.
-/
instance unique.of_subsingleton_of_inhabited (α : Type*) [hs : subsingleton α] [hi : inhabited α] : unique α :=
⟨hi.default⟩

example (α : Type*) : unique α :=
begin
  success_if_fail { apply_instance }, -- maximum class-instance resolution depth has been reached
  sorry
end

end examples
