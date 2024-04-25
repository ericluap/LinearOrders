import Mathlib.Init.Order.LinearOrder
import Mathlib.Order.Hom.Basic
import Mathlib.Order.InitialSeg
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sum.Order
import Lindenbaum.Lindenbaum

noncomputable section
open Classical
open Set

universe u v w x y

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]

section Parts
variable (f : α ⊕ₗ β ≃o γ)

def left_part : Set (α ⊕ₗ β) := Sum.inl '' (univ : Set α)
def right_part : Set (α ⊕ₗ β) := Sum.inr '' (univ : Set β)

theorem in_left_or_right : ∀x : α ⊕ₗ β, x ∈ left_part ∨ x ∈ right_part := by
  intros x
  cases' x with x x
  constructor
  · unfold left_part
    simp
  · unfold right_part
    simp

theorem left_initial : isInitial (@left_part α β) := by
  unfold isInitial
  intros x hx y hy
  have y_lr := in_left_or_right y
  cases' y_lr with z z
  trivial
  unfold left_part at *
  unfold right_part at z
  simp at *
  rcases z with ⟨z, hz⟩
  rcases hx with ⟨q, hq⟩
  rw [←hz, ←hq] at hy
  have := Sum.Lex.inl_lt_inr z q
  contradiction

theorem right_final : isFinal (@right_part α β) := by
  unfold isFinal
  intros x hx y hy
  have y_lr := in_left_or_right y
  cases' y_lr with z z
  unfold left_part at *
  unfold right_part at hx
  simp at *
  rcases z with ⟨z, hz⟩
  rcases hx with ⟨q, hq⟩
  rw [←hz, ←hq] at hy
  have := Sum.Lex.inl_lt_inr z q
  contradiction
  trivial

def image_left : Set γ := f '' left_part
def image_right : Set γ := f '' right_part

def iso_to_initial (g : α ≃o β) : (@LT.lt α _) ≼i (@LT.lt β _) :=
  {
    toFun := g.toFun
    inj' := g.left_inv.injective,
    init' := by
      intros _ b _
      simp at *
      use (g.invFun b)
      apply g.right_inv
    map_rel_iff' := by
      simp at *
  }

instance : Coe (α ≃o β) ((@LT.lt α _) ≼i (@LT.lt β _)) :=
  ⟨iso_to_initial⟩

def iso_to_final (g : α ≃o β) : (@LT.lt α _) ≼f (@LT.lt β _) :=
  {
    toFun := g.toFun
    inj' := g.left_inv.injective,
    final' := by
      intros _ b _
      simp at *
      use (g.invFun b)
      apply g.right_inv
    map_rel_iff' := by
      simp at *
  }

theorem image_left_initial : isInitial (image_left f) := by
  unfold image_left
  exact (image_of_initial_initial'
          (iso_to_initial f) left_initial)

theorem image_right_final : isFinal (image_right f) := by
  unfold image_right
  exact (image_of_final_final'
          (iso_to_final f) right_final)

def isInitialInside (a b : Set α) := a ⊆ b ∧ ∀x ∈ a, ∀y ∈ b, y < x → y ∈ a
def isFinalInside (a b : Set α) := a ⊆ b ∧ ∀x ∈ a, ∀y ∈ b, y > x → y ∈ a

theorem image_image_subset (a b : Set α) (ha : isInitial a) (hb : isInitial b)
: a ⊆ b ∨ b ⊆ a := by
  by_cases hq : a ⊆ b
  · left
    trivial
  · right
    rw [not_subset] at hq
    rcases hq with ⟨z, ⟨hz, hz'⟩⟩
    have hab : ∀t ∈ b, t < z := by
      intros t ht
      by_contra h
      simp at h
      rw [le_iff_lt_or_eq] at h
      rcases h with hq | hq
      exact (hz' (hb t ht z hq))
      rw [hq] at hz'
      exact hz' ht
    rw [subset_def]
    intros x hx
    exact ha z hz x (hab x hx)

theorem image_image_initial (a b : Set α) (ha : isInitial a) (hb : isInitial b)
: isInitialInside a b ∨ isInitialInside b a := by
  have := image_image_subset a b ha hb
  rcases this with hq | hq
  left
  unfold isInitialInside
  constructor
  trivial
  intros x hx y _ hyx
  exact ha x hx y hyx
  right
  unfold isInitialInside
  constructor
  trivial
  intros x hx y _ hyx
  exact hb x hx y hyx

theorem comp_of_initial_final_inside (a b : Set α) (hin : isInitialInside a b)
: isFinalInside (b \ a) b := by
  unfold isFinalInside
  constructor
  rw [diff_subset_iff]
  apply subset_union_right
  intros x hx y hy hyx
  simp
  constructor
  trivial
  by_contra h
  unfold isInitialInside at hin
  rcases hin with ⟨_, hz⟩
  simp at hx
  rcases hx with ⟨hx, hna⟩
  exact hna (hz y h x hx hyx)

end Parts

def map_back {j : Type} (f1 : γ → j) (f2 : e → j)
    | Sum.inl a => f1 a
    | Sum.inr a => f2 a

theorem sum_refinement
  (f : α ⊕ₗ β ≃o γ ⊕ₗ δ)
: ∃e : Type (max x w), [LinearOrder e] →
  (Nonempty (γ ⊕ₗ e ≃o α) ∧ Nonempty (e ⊕ₗ β ≃o δ)) ∨
  (Nonempty (α ⊕ₗ e ≃o γ) ∧ Nonempty (e ⊕ₗ δ ≃o β)) := by
  have := image_image_initial left_part (image_left f) left_initial (image_left_initial f)
  rcases this with h | h
  have := (image_left f) \ left_part
  use this
  intros s
  left
  constructor
  rw [←exists_true_iff_nonempty]
  set q := map_back (λ g => f.invFun (Sum.inl g)) (f.invFun)
