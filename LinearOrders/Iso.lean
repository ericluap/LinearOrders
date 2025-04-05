import Mathlib.Order.Hom.Basic
import Mathlib.Order.Hom.Set
import Mathlib.Order.InitialSeg
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sum.Order
import LinearOrders.Lindenbaum
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sum.Order
import Mathlib.Data.Set.Subset
import LinearOrders.InitialFinal
import LinearOrders.OrderIso
import LinearOrders.OrderEmbedding

noncomputable section
open Classical
open Set
open Set.Notation

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]

theorem make_iso {f : α → β} (hinj : Function.Injective f) (hsurj : Function.Surjective f)
 (hord : ∀{a b : α}, f a ≤ f b ↔ a ≤ b) : Nonempty (α ≃o β) := by
  have hbij : Function.Bijective f := ⟨hinj, hsurj⟩
  rw [Function.bijective_iff_has_inverse] at hbij
  rcases hbij with ⟨h, ⟨left_inv, right_inv⟩⟩
  set g : α ≃ β := ⟨f, h, left_inv, right_inv⟩
    with g_def
  have gord : ∀{a b : α}, g a ≤ g b ↔ a ≤ b := by
    simp [g_def]
    exact hord
  have orderbij : α ≃o β := ⟨g, gord⟩
  apply nonempty_of_exists
  use orderbij

theorem nonempty_nonempty_iso_trans : Nonempty (α ≃o β) -> Nonempty (β ≃o γ) -> Nonempty (α ≃o γ) := by
  intros x y
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  apply nonempty_of_exists
  use (x.trans y)

theorem nonempty_iso_trans : Nonempty (α ≃o β) -> β ≃o γ -> Nonempty (α ≃o γ) := by
  intros x y
  rcases x with ⟨x⟩
  apply nonempty_of_exists
  use (x.trans y)

def iso_to_image (f : α ↪o β) (a : Set α) :
  a ≃o f '' a := OrderIso.ofSurjective
    (⟨⟨fun x => ⟨f x, by simp⟩, by simp [Function.Injective]⟩, by simp⟩)
    (by simp [Function.Surjective])

def univ_iso_type : α ≃o (univ : Set α) := OrderIso.ofSurjective
    ⟨⟨fun x => ⟨OrderEmbedding.id α x, by simp⟩, by simp [Function.Injective]⟩, by simp⟩
    (by simp [Function.Surjective, OrderEmbedding.id])


def type_iso_image (f : α ↪o β) : α ≃o f '' univ := univ_iso_type.trans (iso_to_image f univ)

def subset_cap_iso {a b : Set α} (ha : a ⊆ b) : (b ↓∩ a ≃o a) where
  toFun x := ⟨x, x.property⟩
  invFun x := ⟨⟨x, ha x.property⟩, x.property⟩
  left_inv := by unfold Function.LeftInverse; simp
  right_inv := by unfold Function.RightInverse Function.LeftInverse; simp
  map_rel_iff' := by simp

def equal_iso {a b : Set α} (eq : a = b) :
  a ≃o b where
  toFun x := ⟨x, by simp [←eq]⟩
  invFun x := ⟨x, by simp [eq]⟩
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  map_rel_iff' := by simp

omit [LinearOrder α] [LinearOrder β] in
theorem swap_equal_left {a b : Set α} (eq : a = b) :
  (a ⊕ₗ β) = (b ⊕ₗ β) := by
  rw [eq]
