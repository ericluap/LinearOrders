import Mathlib.Order.Hom.Basic

namespace OrderIso

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [LinearOrder α] [LinearOrder β] [LinearOrder γ]

def id (α : Type*) [LinearOrder α] : α ≃o α where
  toFun x := x
  map_rel_iff' := by simp
  invFun x := x
  left_inv := by unfold Function.LeftInverse; simp
  right_inv := by unfold Function.RightInverse; unfold Function.LeftInverse; simp

noncomputable def ofSurjective (f : α ↪o β) (hf : Function.Surjective f) : (α ≃o β) :=
 { Equiv.ofBijective f (And.intro f.inj' hf) with map_rel_iff' := f.map_rel_iff'}
