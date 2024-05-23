import Mathlib.Init.Order.LinearOrder
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Hom.Set
import Mathlib.Order.InitialSeg
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sum.Order
import LinearOrders.Lindenbaum
import LinearOrders.InitialFinal
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sum.Order
import Mathlib.Data.Set.Subset
import LinearOrders.Iso

noncomputable section
open Classical
open Set
open Set.Notation

universe u v w x y

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]

theorem sum_assoc : Nonempty ((α ⊕ₗ β) ⊕ₗ γ ≃o α ⊕ₗ (β ⊕ₗ γ)) := by
  set q : (α ⊕ₗ β) ⊕ₗ γ → α ⊕ₗ (β ⊕ₗ γ) := λg =>
    match g with
    | Sum.inl (Sum.inl a) => Sum.inlₗ a
    | Sum.inl (Sum.inr b) => Sum.inrₗ (Sum.inlₗ b)
    | Sum.inr c => Sum.inrₗ (Sum.inrₗ c)
    with q_def
  have qinj : Function.Injective q := by
    unfold Function.Injective
    intros x y hxy
    simp [q_def] at hxy
    rcases x with x | x
    · rcases x with x | x
      · rcases y with y | y
        · rcases y with y | y
          · simp at hxy
            rw [hxy]
          · simp at hxy
        · simp at hxy
      · rcases y with y | y
        · rcases y with y | y
          · simp at hxy
          · simp at hxy
            rw [hxy]
        · simp at hxy
    · rcases y with y | y
      · rcases y with y | y
        · simp at hxy
        · simp at hxy
      · simp at hxy
        rw [hxy]
  have qsurj : Function.Surjective q := by
    unfold Function.Surjective
    intros x
    rcases x with x | x
    · use (Sum.inl (Sum.inl x))
      simp [q_def]
      change _ = toLex _
      simp
    · rcases x with x | x
      · use (Sum.inl (Sum.inr x))
        simp [q_def]
        change _ = toLex _
        simp
        change _ = toLex _
        simp
      · use (Sum.inr x)
        simp [q_def]
        change _ = toLex _
        simp
        change _ = toLex _
        simp
  have qord : ∀{x y : (α ⊕ₗ β) ⊕ₗ γ}, q x ≤ q y ↔ x ≤ y := by
    intros x y
    constructor
    · intros hxy
      simp [q_def] at hxy
      rcases x with x | x
      · rcases x with x | x
        · rcases y with y | y
          · rcases y with y | y
            · simp at hxy
              change toLex _ ≤ toLex _
              simp
              change toLex _ ≤ toLex _
              simp
              trivial
            · change toLex _ ≤ toLex _
              simp
              exact Sum.Lex.inl_le_inr x y
          · change toLex _ ≤ toLex _
            simp
        · rcases y with y | y
          · rcases y with y | y
            · simp at hxy
            · simp at hxy
              change toLex _ ≤ toLex _
              simp
              change toLex _ ≤ toLex _
              simp
              trivial
          · change toLex _ ≤ toLex _
            simp
      · rcases y with y | y
        · rcases y with y | y
          · simp at hxy
          · simp at hxy
        · simp at hxy
          change toLex _ ≤ toLex _
          simp
          trivial
    · intros hxy
      simp [q_def]
      rcases x with x | x
      · rcases x with x | x
        · rcases y with y | y
          · rcases y with y | y
            · simp
              change toLex _ ≤ toLex _ at hxy
              simp at hxy
              change toLex _ ≤ toLex _ at hxy
              simp at hxy
              trivial
            · simp
          · simp
        · rcases y with y | y
          · rcases y with y | y
            · contradiction
            · simp
              change toLex _ ≤ toLex _ at hxy
              simp at hxy
              change toLex _ ≤ toLex _ at hxy
              simp at hxy
              trivial
          · simp
      · rcases y with y | y
        · rcases y with y | y
          · contradiction
          · contradiction
        · simp
          change toLex _ ≤ toLex _ at hxy
          simp at hxy
          trivial
  exact make_iso qinj qsurj qord

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

theorem in_left_not_right : ∀x : α ⊕ₗ β, x ∈ left_part -> x ∉ right_part := by
  intros x hx
  rcases x with x | x
  · intros hy
    unfold right_part at hy
    simp at hy
  · unfold left_part at hx
    simp at hx

theorem in_right_not_left : ∀x : α ⊕ₗ β, x ∈ right_part -> x ∉ left_part := by
  intros x hx
  rcases x with x | x
  · unfold right_part at hx
    simp at hx
  · intros hy
    unfold left_part at hy
    simp at hy

theorem not_left_in_right {x : α ⊕ₗ β} : x ∉ left_part → x ∈ right_part := by
  rcases (in_left_or_right x) with h | h
  · intros hx
    contradiction
  · intros _
    trivial

theorem not_right_in_left {x : α ⊕ₗ β} : x ∉ right_part → x ∈ left_part := by
  rcases (in_left_or_right x) with h | h
  · intros _
    trivial
  · intros hx
    contradiction

theorem left_compl_right : left_partᶜ = (right_part : Set (α ⊕ₗ β)) := by
  simp [compl_def]
  apply Set.Subset.antisymm
  rw [subset_def]
  intros x hx
  simp at hx
  exact not_left_in_right hx
  rw [subset_def]
  intros x hx
  simp
  apply in_right_not_left
  trivial

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

theorem image_left_initial : isInitial (image_left f) := by
  unfold image_left
  exact (initial_maps_initial_initial
          (f : α ⊕ₗ β ≼i γ) left_initial)

theorem image_right_final : isFinal (image_right f) := by
  unfold image_right
  exact (final_maps_final_final
          (f : α ⊕ₗ β ≼f γ) right_final)

theorem in_image_left_or_right (x : γ) : (x ∈ image_left f ∧ x ∉ image_right f) ∨ (x ∈ image_right f ∧ x ∉ image_left f) := by
  set inv := (f.invFun x) with inv_def
  rcases inv with y | y
  left
  unfold image_left
  simp
  constructor
  left
  use y
  constructor
  · unfold left_part
    simp
    use y
    exact rfl
  · have : toLex (Sum.inl y : (α ⊕ₗ β)) = Sum.inl y := by
      exact rfl
    rw [this]
    simp [inv_def]
  unfold image_right
  simp
  intros z
  rcases z with z | z
  rcases z with ⟨w, hw1, _⟩
  unfold right_part at hw1
  simp at hw1
  rcases hw1 with ⟨q, hq⟩
  have : toLex (Sum.inl w : (α ⊕ₗ β)) = Sum.inl w := by exact rfl
  rw [this] at hq
  simp at hq
  rcases z with ⟨w, hw1, hw2⟩
  have : toLex (Sum.inr w : (α ⊕ₗ β)) = Sum.inr w := by exact rfl
  rw [this] at hw1
  rw [this] at hw2
  have : f (Sum.inl y) = x := by
    simp [inv_def]
  have : f (Sum.inl y) = f (Sum.inr w) := by
    rw [hw2, this]
  simp at this
  right
  unfold image_right
  simp
  constructor
  right
  use y
  constructor
  · unfold right_part
    simp
    use y
    exact rfl
  · have : toLex (Sum.inr y : (α ⊕ₗ β)) = Sum.inr y := by
      exact rfl
    rw [this]
    simp [inv_def]
  unfold image_left
  simp
  intros z
  rcases z with z | z
  rcases z with ⟨w, hw1, hw2⟩
  have : toLex (Sum.inl w : (α ⊕ₗ β)) = Sum.inl w := by exact rfl
  rw [this] at hw2
  rw [this] at hw1
  have : f (Sum.inr y) = x := by
    simp [inv_def]
  have : f (Sum.inr y) = f (Sum.inl w) := by
    rw [hw2, this]
  simp at this
  rcases z with ⟨w, hw1, hw2⟩
  have : toLex (Sum.inr w : (α ⊕ₗ β)) = Sum.inr w := by exact rfl
  rw [this] at hw1
  rw [this] at hw2
  unfold left_part at hw1
  simp at hw1

theorem not_in_image_left_right {x : γ} : x ∉ image_left f → x ∈ image_right f := by
  intros h
  rcases (in_image_left_or_right f x) with ⟨z,_⟩ | ⟨z,_⟩
  · contradiction
  · trivial

theorem not_in_image_right_left {x : γ} : x ∉ image_right f → x ∈ image_left f := by
  intros h
  rcases (in_image_left_or_right f x) with ⟨z,_⟩ | ⟨z,_⟩
  · trivial
  · contradiction

theorem in_image_left_not_right {x : γ} : x ∈ image_left f → x ∉ image_right f := by
  intros h
  rcases (in_image_left_or_right f x) with ⟨_,z2⟩ | ⟨_,z2⟩
  trivial
  contradiction

theorem in_image_right_not_left {x : γ} : x ∈ image_right f → x ∉ image_left f := by
  intros h
  rcases (in_image_left_or_right f x) with ⟨_,z2⟩ | ⟨_,z2⟩
  contradiction
  trivial

theorem image_left_compl_image_right : (image_left f)ᶜ = (image_right f) := by
  simp [compl_def]
  apply Set.Subset.antisymm
  rw [subset_def]
  intros x hx
  simp at hx
  exact not_in_image_left_right f hx
  rw [subset_def]
  intros x hx
  simp
  apply in_image_right_not_left
  trivial

section init_final
variable {a : Set α}

theorem initial_plus_final (ha : isInitial a) :
Nonempty (a ⊕ₗ (aᶜ : Set α) ≃o α) := by
  set q : a ⊕ₗ (aᶜ : Set α) → α := λ g =>
    match g with
    | Sum.inl g => g
    | Sum.inr g => g
    with q_def
  have qinj : Function.Injective q := by
    unfold Function.Injective
    intros c d hcd
    simp [q_def] at hcd
    rcases c with c | c
    rcases d with d | d
    simp at hcd
    have := Subtype.eq hcd
    rw [this]
    simp at hcd
    have cin : ↑c ∈ a := c.property
    have din : ↑d ∈ aᶜ := d.property
    rw [hcd] at cin
    contradiction
    rcases d with d | d
    simp at hcd
    have cin := c.property
    have din := d.property
    rw [hcd] at cin
    contradiction
    simp at hcd
    have := Subtype.eq hcd
    rw [this]
  have qsurj : Function.Surjective q := by
    unfold Function.Surjective
    intros b
    by_cases hb : b ∈ a
    use (Sum.inl ⟨b, hb⟩)
    use (Sum.inr ⟨b, hb⟩)
  have qbij : Function.Bijective q := ⟨qinj, qsurj⟩
  rw [Function.bijective_iff_has_inverse] at qbij
  rcases qbij with ⟨h, ⟨left_inv, right_inv⟩⟩
  set q' : a ⊕ₗ (aᶜ : Set α) ≃ α := ⟨q, h, left_inv, right_inv⟩
    with q'_def
  have q'ord : ∀{c d : a ⊕ₗ (aᶜ : Set α)},
    q' c ≤ q' d ↔ c ≤ d := by
    intros c d
    constructor
    intros hcd
    rcases c with c | c
    rcases d with d | d
    simp [q'_def, q_def] at hcd
    have : Monotone (toLex ∘ Sum.inl : a → a ⊕ₗ (aᶜ : Set α)):= Sum.Lex.inl_mono
    unfold Monotone at this
    have := this hcd
    trivial
    have : toLex (Sum.inl c) ≤ toLex (Sum.inr d):= Sum.Lex.inl_le_inr c d
    trivial
    rcases d with d | d
    simp [q'_def, q_def] at hcd
    rw [le_iff_eq_or_lt] at hcd
    rcases hcd with heq | hlt
    have cin := c.property
    have din := d.property
    rw [heq] at cin
    contradiction
    have := ha d d.property c hlt
    have cin := c.property
    contradiction
    simp [q'_def, q_def] at hcd
    have : Monotone (toLex ∘ Sum.inr : (aᶜ : Set α) → a ⊕ₗ (aᶜ : Set α)):= Sum.Lex.inr_mono
    unfold Monotone at this
    have := this hcd
    trivial
    intros hcd
    rcases c with c | c
    rcases d with d | d
    simp [q'_def, q_def]
    have : toLex (Sum.inl c) ≤ toLex (Sum.inl d) := hcd
    simp [Sum.Lex.le_def] at this
    trivial
    simp [q'_def, q_def]
    by_contra x
    simp at x
    have := ha c c.property d x
    have din := d.property
    contradiction
    rcases d with d | d
    simp [q'_def, q_def]
    have : toLex (Sum.inr c) ≤ toLex (Sum.inl d) := hcd
    simp [Sum.Lex.le_def] at this
    simp [q'_def, q_def]
    have : toLex (Sum.inr c) ≤ toLex (Sum.inr d) := hcd
    simp [Sum.Lex.le_def] at this
    trivial
  have orderbij : (a ⊕ₗ (aᶜ : Set α)) ≃o α := RelIso.mk q' q'ord
  apply nonempty_of_exists
  use orderbij

end init_final

theorem inl_iff_monotone : ∀(a b : α), ((toLex ∘ Sum.inl) a : α ⊕ₗ β) ≤ (toLex ∘ Sum.inl) b ↔ a ≤ b := by
    intros a b
    constructor
    intros hab
    simp at hab
    trivial
    intros hab
    simp
    trivial

theorem inr_iff_monotone : ∀(a b : β), ((toLex ∘ Sum.inr) a : α ⊕ₗ β) ≤ (toLex ∘ Sum.inr) b ↔ a ≤ b := by
    intros a b
    constructor
    intros hab
    simp at hab
    trivial
    intros hab
    simp
    trivial

theorem left_part_iso : Nonempty (α ≃o (left_part : Set (α ⊕ₗ β))) := by
  set inl_order : α ↪o α ⊕ₗ β := OrderEmbedding.ofMapLEIff (toLex ∘ Sum.inl) inl_iff_monotone
    with inl_order_def
  have hq : Nonempty (↑univ ≃o ↑(⇑inl_order '' univ)) := (iso_to_image (inl_order) univ)
  have inl_order_image : inl_order '' univ = left_part := by
    unfold left_part
    rw [inl_order_def]
    simp
    unfold range
    constructor
  rw [inl_order_image] at hq
  rcases hq with ⟨j⟩
  have a_iso_univ : Nonempty (α ≃o univ) := univ_iso_type
  rcases a_iso_univ with ⟨a_iso⟩
  have iso_trans : α ≃o left_part := (a_iso.trans j)
  apply nonempty_of_exists
  use iso_trans

theorem right_part_iso : Nonempty (β ≃o (right_part : Set (α ⊕ₗ β))) := by
  set inr_order : β ↪o α ⊕ₗ β := OrderEmbedding.ofMapLEIff (toLex ∘ Sum.inr) inr_iff_monotone
    with inr_order_def
  have hq : Nonempty (↑univ ≃o ↑(⇑inr_order '' univ)) := (iso_to_image (inr_order) univ)
  have inr_order_image : inr_order '' univ = right_part := by
    unfold right_part
    rw [inr_order_def]
    simp
    unfold range
    constructor
  rw [inr_order_image] at hq
  rcases hq with ⟨j⟩
  have b_iso_univ : Nonempty (β ≃o univ) := univ_iso_type
  rcases b_iso_univ with ⟨b_iso⟩
  have iso_trans : β ≃o ↑right_part := (b_iso.trans j)
  apply nonempty_of_exists
  use iso_trans

theorem left_iso_image_left : Nonempty (α ≃o image_left f) := by
  have := (iso_to_image (f.toRelEmbedding) left_part)
  rw [←exists_true_iff_nonempty] at this
  rcases this with ⟨z, hz⟩
  simp at z
  have : image_left f = f '' left_part := by
    unfold image_left
    trivial
  rw [←this] at z
  rcases (left_part_iso : Nonempty (α ≃o (left_part : Set (α ⊕ₗ β)))) with ⟨a⟩
  have iso_trans : α ≃o image_left f := a.trans z
  apply nonempty_of_exists
  use iso_trans

theorem right_iso_image_right : Nonempty (β ≃o image_right f) := by
  rcases (iso_to_image (f.toRelEmbedding) right_part) with ⟨z⟩
  simp at z
  have : image_right f = f '' right_part := by
    unfold image_right
    trivial
  rw [←this] at z
  rcases (right_part_iso : Nonempty (β ≃o (right_part : Set (α ⊕ₗ β)))) with ⟨a⟩
  have iso_trans : β ≃o image_right f := a.trans z
  apply nonempty_of_exists
  use iso_trans

end Parts

theorem small_left_plus_compl {a b : Set α} :
Nonempty (↑(b ↓∩ a)ᶜ ≃o ↑(b \ a)) := by
  set q : ↑(b ↓∩ a)ᶜ → ↑(b \ a) :=
    λg => ⟨g.val.val, ⟨(g.val.property), (g.property)⟩⟩
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
    have := x.property
    rcases this with ⟨x_in_b, x_not_in_a⟩
    use ⟨⟨x.val, x_in_b⟩, x_not_in_a⟩
  have qord : ∀{x y : ↑(b ↓∩ a)ᶜ}, (q x ≤ q y) ↔ x ≤ y := by
    intros x y
    constructor
    intros hxy
    simp [q_def] at hxy
    trivial
    intros hxy
    simp [q_def]
    trivial
  exact make_iso qinj qsurj qord

theorem initial_inside_sum_iso {a b : Set α}
(hab : isInitialInside b a) : Nonempty (b ⊕ₗ ↑(a \ b) ≃o a) := by
  rcases hab with ⟨b_sub_a, b_initial_a⟩
  rcases (initial_plus_final b_initial_a) with ⟨iso⟩
  rcases (subset_cap_iso b_sub_a) with ⟨iso2⟩
  rcases (swap_iso_left iso2 iso) with ⟨iso⟩
  rcases (small_left_plus_compl : Nonempty (↑(a ↓∩ b)ᶜ ≃o ↑(a \ b))) with ⟨iso2⟩
  rcases (swap_iso_right iso2 iso) with ⟨iso⟩
  apply nonempty_of_exists
  exists iso

theorem initial_compl_initial {a b : Set α}
(ha : isInitial a) : isInitial (bᶜ ↓∩ ↑(a \ b)) := by
  unfold isInitial
  intros x hx y hy
  simp at *
  exact (ha x hx y hy)

lemma setminus_not_in {x : α} {a b : Set α} (hnb : x ∈ bᶜ) (hnab : x ∉ a \ b) :
x ∉ a := by
  simp at *
  by_contra z
  exact hnb (hnab z)

theorem subset_compl_compl {a b : Set α}
(b_subset_a : b ⊆ a) : Nonempty (↑(bᶜ ↓∩ a \ b)ᶜ ≃o ↑aᶜ) := by
  set q : ↑(bᶜ ↓∩ a \ b)ᶜ → ↑aᶜ := λg => by
    have := g.property
    simp at this
    exact ⟨g.val, this⟩
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
    have x_not_in_a := x.property
    have a_comp_sub_b_comp : aᶜ ⊆ bᶜ := by
      rw [compl_subset_compl]
      trivial
    have x_not_in_b : ↑x ∈ bᶜ := by
      exact a_comp_sub_b_comp x_not_in_a
    set j : {x // x ∈ bᶜ} := ⟨↑x, x_not_in_b⟩
    have j_in : j ∈ (bᶜ ↓∩ a \ b)ᶜ := by
      simp
      trivial
    use ⟨j, j_in⟩
  have qord : ∀{x y : ↑(bᶜ ↓∩ a \ b)ᶜ}, (q x ≤ q y) ↔ x ≤ y := by
    intros x y
    constructor
    · intros hxy
      simp [q_def] at hxy
      trivial
    · intros hxy
      simp [q_def]
      trivial
  exact make_iso qinj qsurj qord

theorem initial_inside_sum_compl_iso {a b : Set α}
(ha : isInitial a) (b_sub_a : b ⊆ a) : Nonempty (↑(a \ b) ⊕ₗ ↑aᶜ ≃o ↑bᶜ) := by
  have a_minus_b_subset : a \ b ⊆ bᶜ := by
    simp [subset_def]
  have a_minus_b_initial : isInitial (bᶜ ↓∩ ↑(a \ b)) := initial_compl_initial ha
  rcases (initial_plus_final a_minus_b_initial) with ⟨iso⟩
  rcases (subset_cap_iso a_minus_b_subset) with ⟨iso2⟩
  rcases (swap_iso_left iso2 iso) with ⟨iso⟩
  rcases (subset_compl_compl b_sub_a) with ⟨iso2⟩
  rcases (swap_iso_right iso2 iso) with ⟨iso⟩
  apply nonempty_of_exists
  use iso

theorem sum_refinement
  (f : α ⊕ₗ β ≃o γ ⊕ₗ δ)
: ∃e : Type (max w x), ∃s : LinearOrder e,
  (Nonempty (γ ⊕ₗ e ≃o α) ∧ Nonempty (e ⊕ₗ β ≃o δ)) ∨
  (Nonempty (α ⊕ₗ e ≃o γ) ∧ Nonempty (e ⊕ₗ δ ≃o β)) := by
  have := image_image_initial left_part (image_left f) left_initial (image_left_initial f)
  rcases this with h | h
  · set e := (image_left f) \ left_part with e_def
    use e, Subtype.instLinearOrder e
    left
    have first_part : Nonempty (γ ⊕ₗ e ≃o α) := by
      rw [←exists_true_iff_nonempty]
      rcases (initial_inside_sum_iso h) with ⟨iso⟩
      rw [←e_def] at iso
      rcases (left_iso_image_left f) with ⟨w⟩
      rcases (left_part_iso : Nonempty (γ ≃o (left_part : Set (γ ⊕ₗ δ)))) with ⟨q⟩
      rcases (nonempty_iso_trans (swap_iso_left q.symm iso) w.symm) with ⟨iso⟩
      use iso
    have second_part : Nonempty (e ⊕ₗ β ≃o δ) := by
      rcases h with ⟨left_subset_image, _⟩
      rcases (initial_inside_sum_compl_iso (image_left_initial f) left_subset_image)
        with ⟨iso⟩
      rcases (equal_iso e_def) with ⟨iso2⟩
      rcases (swap_iso_left iso2.symm iso) with ⟨iso⟩
      rcases (equal_iso (image_left_compl_image_right f)) with ⟨iso2⟩
      rcases (swap_iso_right iso2 iso) with ⟨iso⟩
      rcases (right_iso_image_right f) with ⟨iso2⟩
      rcases (swap_iso_right iso2.symm iso) with ⟨iso⟩
      rcases (equal_iso (left_compl_right : (left_partᶜ = (right_part : Set (γ ⊕ₗ δ)))))
        with ⟨iso2⟩
      have iso := iso.trans iso2
      rcases (right_part_iso : Nonempty (δ ≃o ↑(right_part : Set (γ ⊕ₗ δ))))
        with ⟨iso2⟩
      have iso := iso.trans iso2.symm
      apply nonempty_of_exists
      use iso
    constructor
    trivial
    trivial
  · set e := left_part \ (image_left f) with e_def
    use e, Subtype.instLinearOrder e
    right
    have first_part : Nonempty (α ⊕ₗ e ≃o γ) := by
      rcases (initial_inside_sum_iso h) with ⟨iso⟩
      rcases (left_iso_image_left f) with ⟨iso2⟩
      rcases (swap_iso_left iso2.symm iso) with ⟨iso⟩
      rcases (left_part_iso : Nonempty (γ ≃o (left_part : Set (γ ⊕ₗ δ)))) with ⟨iso2⟩
      have iso := iso.trans iso2.symm
      rcases (equal_iso e_def) with ⟨iso2⟩
      rcases (swap_iso_right iso2.symm iso) with ⟨iso⟩
      apply nonempty_of_exists
      use iso
    have second_part : Nonempty (e ⊕ₗ δ ≃o β) := by
      rcases h with ⟨image_subset_left, _⟩
      rcases (initial_inside_sum_compl_iso left_initial image_subset_left)
        with ⟨iso⟩
      rcases (equal_iso e_def) with ⟨iso2⟩
      rcases (swap_iso_left iso2.symm iso) with ⟨iso⟩
      rcases (equal_iso (image_left_compl_image_right f)) with ⟨iso2⟩
      have iso := iso.trans iso2
      rcases (right_iso_image_right f) with ⟨iso2⟩
      have iso := iso.trans iso2.symm
      rcases (equal_iso (left_compl_right : (left_partᶜ = (right_part : Set (γ ⊕ₗ δ)))))
        with ⟨iso2⟩
      rcases (swap_iso_right iso2 iso) with ⟨iso⟩
      rcases (right_part_iso : Nonempty (δ ≃o ↑(right_part : Set (γ ⊕ₗ δ))))
        with ⟨iso2⟩
      rcases (swap_iso_right iso2.symm iso) with ⟨iso⟩
      apply nonempty_of_exists
      use iso
    constructor
    trivial
    trivial

theorem initial_plus (f : α ≼i β) :
∃e : Type v, ∃s : LinearOrder e, Nonempty (α ⊕ₗ e ≃o β) := by
  use ↑(f '' univ)ᶜ, Subtype.instLinearOrder (f '' univ)ᶜ
  have := image_of_univ_initial f
  rcases (initial_plus_final this) with ⟨iso⟩
  rcases (type_iso_image f.toRelEmbedding) with ⟨iso2⟩
  rcases (swap_iso_left iso2.symm iso) with ⟨iso⟩
  apply nonempty_of_exists
  use iso

theorem plus_initial (f : α ⊕ₗ β ≃o γ) : α ≼i γ := by
  set f' : α → γ := λg => f (Sum.inl g) with f'_def
  have : Function.Injective f' := by
    unfold Function.Injective
    intros x y hxy
    simp [f'_def] at hxy
    change toLex _ = toLex _ at hxy
    simp at hxy
    trivial
  set f'' : α ↪ γ := ⟨f', this⟩ with f''_def
  have : ∀ {a b}, (f'' a) ≤ (f'' b) ↔ a ≤ b := by
    intros x y
    constructor
    · intros hxy
      simp [f''_def, f'_def] at hxy
      change toLex _ ≤ toLex _ at hxy
      simp at hxy
      trivial
    · intros hxy
      simp [f''_def, f'_def]
      change toLex _ ≤ toLex _
      simp
      trivial
  set f''' : @LE.le α _ ↪r @LE.le γ _ := ⟨f'', this⟩ with f'''_def
  have init' : ∀a b, b ≤ (f''' a) → ∃ a', f''' a' = b := by
    intros x y hxy
    simp [f'''_def, f''_def, f'_def] at hxy
    set z := f.invFun y with z_def
    rcases z with z | z
    · use z
      simp [*]
    · have : f (Sum.inr z) ≤ f (Sum.inl x) := by
        simp [*]
      simp at this
      contradiction
  exact ⟨f''', init'⟩

theorem dual_sum : Nonempty (α ⊕ₗ β ≃o (βᵒᵈ ⊕ₗ αᵒᵈ)ᵒᵈ) := by
  set q : α ⊕ₗ β → (βᵒᵈ ⊕ₗ αᵒᵈ)ᵒᵈ := λg =>
    match g with
    | Sum.inlₗ a => Sum.inrₗ a
    | Sum.inrₗ b => Sum.inlₗ b
    with q_def
  have qinj : Function.Injective q := by
    unfold Function.Injective
    intros x y hxy
    simp [q_def] at hxy
    rcases x with x | x
    · rcases y with y | y
      · simp at hxy
        have : Function.Injective (Sum.inr : αᵒᵈ → Lex (βᵒᵈ ⊕ αᵒᵈ)):= Sum.inr_injective
        have := this hxy
        rw [this]
      · simp at hxy
        contradiction
    · rcases y with y | y
      · simp at hxy
        contradiction
      · simp at hxy
        have : Function.Injective (Sum.inl : βᵒᵈ → Lex (βᵒᵈ ⊕ αᵒᵈ)):= Sum.inl_injective
        have := this hxy
        rw [this]
  have qsurj : Function.Surjective q := by
    unfold Function.Surjective
    intros x
    rcases x with x | x
    · use (Sum.inr x)
      simp [q_def]
      change _ = toLex _
      simp
    · use (Sum.inl x)
      simp [q_def]
      change _ = toLex _
      simp
  have qord : ∀{x y : α ⊕ₗ β}, q x ≤ q y ↔ x ≤ y := by
    intros x y
    constructor
    · intros hxy
      simp [q_def] at hxy
      rcases x with x | x
      · rcases y with y | y
        · simp at hxy
          have := Sum.Lex.inr_le_inr_iff.mp hxy
          change toLex _ ≤ toLex _
          simp
          trivial
        · change toLex _ ≤ toLex _
          simp
      · rcases y with y | y
        · simp at hxy
          contradiction
        · simp at hxy
          change toLex _ ≤ toLex _
          simp
          have := Sum.Lex.inl_le_inl_iff.mp hxy
          trivial
    · intros hxy
      simp [q_def]
      rcases x with x | x
      · rcases y with y | y
        · simp
          change toLex _ ≤ toLex _ at hxy
          simp at hxy
          apply Sum.Lex.inr_le_inr_iff.mpr
          trivial
        · simp
          apply Sum.Lex.inl_le_inr
      · rcases y with y | y
        · simp
          contradiction
        · simp
          apply Sum.Lex.inl_le_inl_iff.mpr
          change toLex _ ≤ toLex _ at hxy
          simp at hxy
          trivial
  exact make_iso qinj qsurj qord

theorem plus_final (f : α ⊕ₗ β ≃o γ) : β ≼f γ := by
  set f' : β → γ := λg => f (Sum.inr g) with f'_def
  have : Function.Injective f' := by
    unfold Function.Injective
    intros x y hxy
    simp [f'_def] at hxy
    change toLex _ = toLex _ at hxy
    simp at hxy
    trivial
  set f'' : β ↪ γ := ⟨f', this⟩ with f''_def
  have : ∀ {a b}, (f'' a) ≤ (f'' b) ↔ a ≤ b := by
    intros x y
    constructor
    · intros hxy
      simp [f''_def, f'_def] at hxy
      change toLex _ ≤ toLex _ at hxy
      simp at hxy
      trivial
    · intros hxy
      simp [f''_def, f'_def]
      change toLex _ ≤ toLex _
      simp
      trivial
  set f''' : @LE.le β _ ↪r @LE.le γ _ := ⟨f'', this⟩ with f'''_def
  have final' : ∀ a b, (f''' a) ≤ b -> ∃ a', f''' a' = b := by
    intros x y hxy
    simp [f'''_def, f''_def, f'_def] at hxy
    set z := f.invFun y with z_def
    rcases z with z | z
    · have : f (Sum.inr x) ≤ f (Sum.inl z) := by
        simp [*]
      simp at this
      contradiction
    · use z
      simp [*]
  exact ⟨f''', final'⟩
