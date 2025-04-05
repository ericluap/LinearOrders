import Mathlib.Data.Set.Basic
import Mathlib.Order.Hom.Basic

namespace OrderEmbedding

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [LinearOrder α] [LinearOrder β] [LinearOrder γ]

def id (α : Type*) [LinearOrder α] : α ↪o α where
  toFun x := x
  inj' := by unfold Function.Injective; simp;
  map_rel_iff' := by simp

def comp (hbg : β ↪o γ) (hab : α ↪o β) :
  α ↪o γ where
  toFun := hbg ∘ hab
  inj' := Function.Injective.comp hbg.inj' hab.inj'
  map_rel_iff' := by simp

@[simp]
theorem coe_comp (g : β ↪o γ) (f : α ↪o β) : ↑(g.comp f) = g ∘ f := rfl

@[simp]
theorem comp_id (f : α ↪o β) : f.comp (.id α) = f :=
  RelEmbedding.ext fun _ => rfl

@[simp]
theorem id_comp (f : α ↪o β) : (OrderEmbedding.id β).comp f = f :=
  RelEmbedding.ext fun _ => rfl

def Elem.val {s : Set α} : Set.Elem s ↪o α where
  toFun := Subtype.val
  inj' := by unfold Function.Injective; simp
  map_rel_iff' := by simp
