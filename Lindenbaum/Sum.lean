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
import Lindenbaum.Iso

noncomputable section
open Classical
open Set
open Set.Notation

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
  rcases z with ⟨w, hw1, hw2⟩
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

theorem sum_refinement
  (f : α ⊕ₗ β ≃o γ ⊕ₗ δ) [Nonempty α]
: ∃e : Type (max w x), ∃s : LinearOrder e,
  (Nonempty (γ ⊕ₗ e ≃o α) ∧ Nonempty (e ⊕ₗ β ≃o δ)) ∨
  (Nonempty (α ⊕ₗ e ≃o γ) ∧ Nonempty (e ⊕ₗ δ ≃o β)) := by
  have := image_image_initial left_part (image_left f) left_initial (image_left_initial f)
  rcases this with h | h
  set e := (image_left f) \ left_part with e_def
  use e, Subtype.instLinearOrder e
  left
  ·
    have first_part : Nonempty (γ ⊕ₗ e ≃o α) := by
      rw [←exists_true_iff_nonempty]
      have left_part_initial_image : isInitial ((image_left f) ↓∩ left_part) := by
        apply initial_in_subset
        exact left_initial
      have : Nonempty ((↑(image_left f ↓∩ left_part) ⊕ₗ ↑(image_left f ↓∩ left_part)ᶜ) ≃o ↑(image_left f))
        := initial_plus_final left_part_initial_image
      rw [←exists_true_iff_nonempty] at this
      rcases this with ⟨z,_⟩
      have domain_iso_image : Nonempty (α ≃o image_left f) := left_iso_image_left f
      rcases domain_iso_image with ⟨w⟩
      have w : image_left f ≃o α := OrderIso.symm w
      have z : (↑(image_left f ↓∩ left_part) ⊕ₗ ↑(image_left f ↓∩ left_part)ᶜ) ≃o α := z.trans w
      unfold isInitialInside at h
      rcases h with ⟨left_subset_image, left_rest_initial⟩
      rcases (subset_cap_iso left_subset_image) with ⟨j⟩
      rcases (left_part_iso : Nonempty (γ ≃o (left_part : Set (γ ⊕ₗ δ)))) with ⟨q⟩
      have z_temp : Nonempty (left_part ⊕ₗ ↑(image_left f ↓∩ left_part)ᶜ ≃o α) := swap_iso_left j z
      rcases z_temp with ⟨z⟩
      have right_equal : Nonempty (↑(image_left f ↓∩ left_part)ᶜ ≃o ↑e) := small_left_plus_compl
      rcases right_equal with ⟨right_equal⟩
      have z_temp : Nonempty (↑left_part ⊕ₗ ↑e ≃o α) := swap_iso_right right_equal z
      rcases z_temp with ⟨z⟩
      have z_swapped3 :
        Nonempty ((left_part : Set (γ ⊕ₗ δ)) ⊕ₗ e ≃o γ ⊕ₗ e) := change_iso_left q.symm
      rcases z_swapped3 with ⟨z_swapped3⟩
      have z := z_swapped3.symm.trans z
      use z
    have second_part : Nonempty (e ⊕ₗ β ≃o δ) := by
      have e_initial_in_delta : isInitial (right_part ↓∩ e) := by
        unfold isInitial
        intros x hx y hy
        simp
        have x_in_image : ↑x ∈ (image_left f) := by
          simp at hx
          simp [e_def] at hx
          rcases hx with ⟨in_image, _⟩
          exact in_image
        have y_in_image : ↑y ∈ (image_left f) := image_left_initial f x x_in_image y hy
        by_contra hne
        simp [e_def] at hne
        have h_in_left := hne y_in_image
        have := in_left_not_right y.val h_in_left y.property
        contradiction
      have z : Nonempty ((right_part ↓∩ e) ⊕ₗ ↑(right_part ↓∩ e)ᶜ ≃o right_part)
        := initial_plus_final e_initial_in_delta
      rcases z with ⟨z⟩
      have right_iso_delta : Nonempty (δ ≃o ↑right_part) := @right_part_iso γ δ _ _
      rcases right_iso_delta with ⟨right_iso_delta⟩
      have z := z.trans (right_iso_delta.symm)
      have e_subset_right : e ⊆ right_part := by
        simp [e_def, subset_def]
        constructor
        · intros x hx hnl
          apply (not_left_in_right) at hnl
          trivial
        · intros x hx hnl
          apply not_left_in_right at hnl
          trivial
      have e_cap_iso := subset_cap_iso e_subset_right
      rcases e_cap_iso with ⟨e_cap_iso⟩
      have z_swap : Nonempty ((right_part ↓∩ e) ⊕ₗ ↑(right_part ↓∩ e)ᶜ ≃o e ⊕ₗ ↑(right_part ↓∩ e)ᶜ)
        := change_iso_left e_cap_iso
      rcases z_swap with ⟨z_swap⟩
      have z := z_swap.symm.trans z
      have e_compl : Nonempty (↑(right_part ↓∩ e)ᶜ ≃o ↑(right_part \ e)) := small_left_plus_compl
      rcases e_compl with ⟨e_compl⟩
      have z_temp := swap_iso_right e_compl z
      rcases z_temp with ⟨z⟩
      have : (image_left f)ᶜ = (right_part : Set (γ ⊕ₗ δ))\ e := by
        simp [compl_def]
        apply Set.Subset.antisymm
        simp [subset_def]
        constructor
        · intros x hx
          have : toLex (Sum.inl x : (γ ⊕ₗ δ)) = Sum.inl x := by exact rfl
          rw [this] at hx
          constructor
          · rw [this]
            have := not_in_image_left_right f hx
            by_contra q
            unfold right_part at q
            unfold image_right at this
