import Mathlib.Init.Order.LinearOrder
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Hom.Set
import Mathlib.Order.InitialSeg
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sum.Order
import Lindenbaum.Lindenbaum
import Lindenbaum.InitialFinal
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sum.Order
import Mathlib.Data.Set.Subset

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

theorem iso_to_image (f : α ↪o β) (a : Set α) :
  Nonempty (a ≃o f '' a) := by
  have : ∀x ∈ a, f x ∈ f '' a := by
    intros x hx
    simp
    trivial
  set q : a → f '' a := λ g => ⟨f g.val, this g.val g.property⟩
    with q_def
  have qinj : Function.Injective q := by
    unfold Function.Injective
    intros x y hxy
    simp [q_def] at hxy
    apply Subtype.eq
    trivial
  have qsurj : Function.Surjective q := by
    unfold Function.Surjective
    intros x
    have := x.property
    simp at this
    rcases this with ⟨z, ⟨hz1, hz2⟩⟩
    use ⟨z, hz1⟩
    simp [q_def]
    apply Subtype.eq
    simp
    trivial
  have qord : ∀{x y : a}, q x ≤ q y ↔ x ≤ y := by
    intros x y
    constructor
    intros hxy
    simp [q_def] at hxy
    trivial
    intros hxy
    simp [q_def]
    trivial
  exact make_iso qinj qsurj qord

theorem univ_iso_type : Nonempty (α ≃o (univ : Set α)) := by
  have : ∀x : α, x ∈ univ := by
    intros x
    simp
  set q : α → univ := λ g => ⟨g, this g⟩
    with q_def
  have qinj : Function.Injective q := by
    unfold Function.Injective
    intros x y hxy
    simp [q_def] at hxy
    trivial
  have qsurj : Function.Surjective q := by
    unfold Function.Surjective
    intros x
    use x
  have qord : ∀{x y : α}, q x ≤ q y ↔ x ≤ y := by
    intros x y
    constructor
    intros hxy
    simp [q_def] at hxy
    trivial
    intros hxy
    simp [q_def]
    trivial
  exact make_iso qinj qsurj qord

theorem subset_cap_iso {a b : Set α} (ha : a ⊆ b)
: Nonempty (b ↓∩ a ≃o a) := by
  set q : b ↓∩ a → a := λ g => by
    have := g.property
    simp at *
    exact ⟨g, this⟩
    with q_def
  have qinj : Function.Injective q := by
    unfold Function.Injective
    intros x y hxy
    simp [q_def] at hxy
    apply Subtype.eq
    apply Subtype.eq
    trivial
  have qsurj : Function.Surjective q := by
    unfold Function.Surjective
    intros x
    have : x.val ∈ b := by
      rw [subset_def] at ha
      exact (ha x.val x.property)
    use ⟨⟨x.val, this⟩, x.property⟩
  have qord : ∀{c d : b ↓∩ a},
    q c ≤ q d ↔ c ≤ d := by
    intros c d
    constructor
    intros hcd
    simp [q_def] at hcd
    trivial
    intros hcd
    simp [q_def]
    trivial
  exact make_iso qinj qsurj qord

theorem equal_iso {a b : Set α} (eq : a = b) :
  Nonempty (a ≃o b) := by
  have atob : ∀q ∈ a, q ∈ b := by
    rw [eq]
    simp
  have btoa : ∀q ∈ b, q ∈ a := by
    rw [eq]
    simp
  set g : a → b := λ q => ⟨q.val, atob q q.property⟩
    with g_def
  have ginj : Function.Injective g := by
    unfold Function.Injective
    intros x y hxy
    simp [g_def] at hxy
    apply Subtype.eq
    trivial
  have gsurj : Function.Surjective g := by
    unfold Function.Surjective
    intros x
    have := btoa x.val x.property
    use ⟨x.val, this⟩
  have gord : ∀{x y : a}, g x ≤ g y ↔ x ≤ y := by
    intros x y
    constructor
    intros hxy
    simp [g_def] at hxy
    trivial
    intros hxy
    simp [g_def]
    trivial
  exact make_iso ginj gsurj gord

theorem swap_equal_left {a b : Set α} (eq : a = b) :
  (a ⊕ₗ β) = (b ⊕ₗ β) := by
  rw [eq]

theorem change_iso_right (f : β ≃o γ) :
Nonempty (α ⊕ₗ β ≃o α ⊕ₗ γ) := by
  set g : α ⊕ₗ β → α ⊕ₗ γ := λ g =>
    match g with
    | Sum.inl g => Sum.inl g
    | Sum.inr g => Sum.inr (f g)
    with g_def
  have ginj : Function.Injective g := by
    unfold Function.Injective
    intros a b hab
    simp [g_def] at hab
    rcases a with a | a
    rcases b with b | b
    simp at hab
    apply Sum.inl_injective at hab
    rw [hab]
    simp at hab
    rcases b with b | b
    simp at hab
    simp at hab
    apply Sum.inr_injective at hab
    simp at hab
    rw [hab]
  have gsurj : Function.Surjective g := by
    unfold Function.Surjective
    intros a
    rcases a with a | a
    use (Sum.inl a)
    use (Sum.inr (f.invFun a))
    simp [g_def]
  have gord : ∀{a b : α ⊕ₗ β}, g a ≤ g b ↔ a ≤ b := by
    intros a b
    constructor
    intros hab
    rcases a with a | a
    rcases b with b | b
    simp [g_def] at hab
    have : toLex (Sum.inl a) ≤ toLex (Sum.inl b) := by
      trivial
    rw [Sum.Lex.inl_le_inl_iff] at this
    apply Sum.Lex.inl_mono
    trivial
    simp [g_def] at hab
    apply Sum.Lex.inl_le_inr
    rcases b with b | b
    simp [g_def] at hab
    apply Sum.Lex.not_inr_le_inl at hab
    contradiction
    simp [g_def] at hab
    have : toLex (Sum.inr (f a)) ≤ toLex (Sum.inr (f b)) := by
      trivial
    rw [Sum.Lex.inr_le_inr_iff] at this
    simp at this
    apply Sum.Lex.inr_mono
    trivial
    intros hab
    rcases a with a | a
    rcases b with b | b
    simp [g_def]
    apply Sum.Lex.inl_mono
    have : toLex (Sum.inl a) ≤ toLex (Sum.inl b) := by
      trivial
    rw [Sum.Lex.inl_le_inl_iff] at this
    trivial
    simp [g_def]
    apply Sum.Lex.inl_le_inr
    rcases b with b | b
    simp [g_def]
    apply Sum.Lex.not_inr_le_inl at hab
    contradiction
    simp [g_def]
    apply Sum.Lex.inr_mono
    simp
    have : toLex (Sum.inr a) ≤ toLex (Sum.inr b) := by
      trivial
    rw [Sum.Lex.inr_le_inr_iff] at this
    trivial
  exact make_iso ginj gsurj gord

theorem change_iso_left (f : α ≃o γ) :
Nonempty (α ⊕ₗ β ≃o γ ⊕ₗ β) := by
  set g : α ⊕ₗ β → γ ⊕ₗ β := λ g =>
    match g with
    | Sum.inl g => Sum.inl (f g)
    | Sum.inr g => Sum.inr g
    with g_def
  have ginj : Function.Injective g := by
    unfold Function.Injective
    intros a b hab
    simp [g_def] at hab
    rcases a with a | a
    rcases b with b | b
    simp at hab
    have : f a = f b := by
      apply Sum.inl_injective
      trivial
    simp at this
    rw [this]
    simp at hab
    rcases b with b | b
    simp at hab
    simp at hab
    have : a = b := by
      apply Sum.inr_injective
      trivial
    rw [this]
  have gsurj : Function.Surjective g := by
    unfold Function.Surjective
    intros a
    rcases a with a | a
    use (Sum.inl (f.invFun a))
    simp [g_def]
    use (Sum.inr a)
  have gord : ∀{a b : α ⊕ₗ β}, g a ≤ g b ↔ a ≤ b := by
    intros a b
    constructor
    intros hab
    rcases a with a | a
    rcases b with b | b
    simp [g_def] at hab
    have : toLex (Sum.inl (f a)) ≤ toLex (Sum.inl (f b)) := by
      trivial
    rw [Sum.Lex.inl_le_inl_iff] at this
    simp at this
    apply Sum.Lex.inl_mono
    trivial
    apply Sum.Lex.inl_le_inr
    rcases b with b | b
    simp [g_def] at hab
    apply Sum.Lex.not_inr_le_inl at hab
    contradiction
    simp [g_def] at hab
    have : toLex (Sum.inr a) ≤ toLex (Sum.inr b) := by
      trivial
    rw [Sum.Lex.inr_le_inr_iff] at this
    apply Sum.Lex.inr_mono
    trivial
    intros hab
    simp [g_def]
    rcases a with a | a
    rcases b with b | b
    simp
    apply Sum.Lex.inl_mono
    simp
    have : toLex (Sum.inl a) ≤ toLex (Sum.inl b) := by
      trivial
    rw [Sum.Lex.inl_le_inl_iff] at this
    trivial
    simp
    apply Sum.Lex.inl_le_inr
    rcases b with b | b
    simp
    apply Sum.Lex.not_inr_le_inl at hab
    contradiction
    simp
    apply Sum.Lex.inr_mono
    have : toLex (Sum.inr a) ≤ toLex (Sum.inr b) := by
      trivial
    rw [Sum.Lex.inr_le_inr_iff] at this
    trivial
  exact make_iso ginj gsurj gord

theorem swap_iso_right (f : β ≃o δ) (h : α ⊕ₗ β ≃o γ) :
Nonempty (α ⊕ₗ δ ≃o γ) := by
  have : Nonempty (α ⊕ₗ β ≃o α ⊕ₗ δ) := change_iso_right f
  rcases this with ⟨this⟩
  have := this.symm.trans h
  apply nonempty_of_exists
  use this

theorem swap_iso_left (f : α ≃o δ) (h : α ⊕ₗ β ≃o γ) :
Nonempty (δ ⊕ₗ β ≃o γ) := by
  have : Nonempty (α ⊕ₗ β ≃o δ ⊕ₗ β) := change_iso_left f
  rcases this with ⟨this⟩
  have := this.symm.trans h
  apply nonempty_of_exists
  use this
