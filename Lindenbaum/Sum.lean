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

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u}
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

theorem image_left_initial : isInitial (image_left f) := by
  unfold image_left
  exact (initial_maps_initial_initial
          (f : α ⊕ₗ β ≼i γ) left_initial)

theorem image_right_final : isFinal (image_right f) := by
  unfold image_right
  exact (final_maps_final_final
          (f : α ⊕ₗ β ≼f γ) right_final)

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

theorem sum_refinement
  (f : α ⊕ₗ β ≃o γ ⊕ₗ δ) [Nonempty α]
: ∃e : Type (max u w), [LinearOrder e] →
  (Nonempty (γ ⊕ₗ e ≃o α) ∧ Nonempty (e ⊕ₗ β ≃o δ)) ∨
  (Nonempty (α ⊕ₗ e ≃o γ) ∧ Nonempty (e ⊕ₗ δ ≃o β)) := by
  have := image_image_initial left_part (image_left f) left_initial (image_left_initial f)
  rcases this with h | h
  set e := (image_left f) \ left_part with e_def
  use e
  intros s
  left
  constructor
  rw [←exists_true_iff_nonempty]
  have image_left_initial : isInitial (image_left f) := by
    unfold image_left
    have := (initial_maps_initial_initial (iso_to_initial f) left_initial)
    trivial
  have left_part_initial_image : isInitial ((image_left f) ↓∩ left_part) := by
    apply initial_in_subset
    exact left_initial
  have efinal : isFinal (image_left f ↓∩ e) := by
    simp [e_def]
    apply comp_initial_final
    apply (initial_in_subset (left_initial))
  have := initial_plus_final left_part_initial_image
  rw [←exists_true_iff_nonempty] at this
  rcases this with ⟨z,_⟩
  have domain_iso_image : Nonempty (α ≃o image_left f) := left_iso_image_left f
  rcases domain_iso_image with ⟨w⟩
  have flip_w : image_left f ≃o α := OrderIso.symm w
  unfold isInitialInside at h
  rcases h with ⟨left_subset_image, left_rest_initial⟩
  rcases (subset_cap_iso left_subset_image) with ⟨j⟩
  rcases (left_part_iso : Nonempty (γ ≃o (left_part : Set (γ ⊕ₗ δ)))) with ⟨q⟩
  have swap : ((image_left f ↓∩ left_part) : Set (γ ⊕ₗ δ)) = (left_part : Set (γ ⊕ₗ δ)) := by
    simp
    trivial
  have z_swapped :
    Nonempty ((↑(image_left f ↓∩ left_part) ⊕ₗ ↑(image_left f ↓∩ left_part)ᶜ) ≃o
      left_part ⊕ₗ ↑(image_left f ↓∩ left_part)ᶜ) := swap_iso_left j
  rcases z_swapped with ⟨z_swapped⟩
  have z_swapped := OrderIso.symm z_swapped
  have z' := z_swapped.trans z
  #check Subtype.preorder
  /-have right_equal : Nonempty ((@Elem (↑(image_left f)) (image_left f ↓∩ left_part)ᶜ) ≃o e) := by-/
  /-have right_equal : Nonempty ((@OrderIso (↑(image_left f ↓∩ left_part)ᶜ) (↑e)
    (@Preorder.toLE (Subtype (image_left f ↓∩ left_part)ᶜ) _)
    (@Preorder.toLE e  _))) := by-/
  have right_equal : Nonempty ((@OrderIso (↑(image_left f ↓∩ left_part)ᶜ) (↑e)
    (@Preorder.toLE (Subtype (image_left f ↓∩ left_part)ᶜ) (PartialOrder.toPreorder _))
    (@Preorder.toLE e (PartialOrder.toPreorder _)))) := by
    set q : (@Elem (↑(image_left f)) (image_left f ↓∩ left_part)ᶜ) → ↑e := λ g => by
      set g1 := g.val
        with g1_def
      have g2 := g.property
      simp at g2
      have g3 := g1.property
      have g1 := g.val
      have g2 := g.property
      set o := (@Subtype.val (↑(image_left f)) (fun x => x ∈ (image_left f ↓∩ left_part)ᶜ) g : ↑(image_left f)).val
        with o_def
      have ho := (@Subtype.val (↑(image_left f)) (fun x => x ∈ (image_left f ↓∩ left_part)ᶜ) g : ↑(image_left f)).property
      rw [e_def]
      have both : o ∈ image_left f ∧ o ∉ left_part := by
        constructor
        trivial
        trivial
      exact ⟨o, both⟩
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
      have ein := x.val
      have eprop := x.property
      have ein' : ↑x ∈ (image_left f \ left_part) := by
        rw [←e_def]
        simp
      have ein2 : ↑x ∈ (image_left f) := by
        simp at ein'
        rcases ein' with ⟨out, _⟩
        exact out
      have ein3 : ⟨↑x, ein2⟩ ∈ (image_left f ↓∩ left_part)ᶜ := by
        simp
        simp at ein'
        rcases ein' with ⟨_, out⟩
        exact out
      use ⟨⟨↑x, ein2⟩, ein3⟩
      rw [q_def]
      simp
    /-
    have qord : ∀{x y : (@Elem (↑(image_left f)) (image_left f ↓∩ left_part)ᶜ)},
    -/
    have qord : ∀{x y : ↑(image_left f ↓∩ left_part)ᶜ},
      @LE.le (↑e) Preorder.toLE (q x) (q y) ↔ x ≤ y := by
      intros x y
      constructor
      intros hxy
      simp [q_def] at hxy
      trivial
      intros hxy
      simp [q_def]
      trivial
    exact make_iso qinj qsurj qord
    sorry
  rcases right_equal with ⟨right_equal⟩
  have z_swapped2 :
    (left_part ⊕ₗ ↑(image_left f ↓∩ left_part)ᶜ ≃o left_part ⊕ₗ e)
    := swap_iso_right right_equal

  /-
  /-have right_iso := equal_iso right_equal-/
  rcases right_iso with ⟨right_iso⟩
  have right_equal' : (@Elem (Lex (γ ⊕ δ)) ↑(image_left f ↓∩ left_part)ᶜ)
    = (@Elem (↑(image_left f)) (image_left f ↓∩ left_part)ᶜ) := by
    simp
    unfold Elem
    simp
    apply funext
    apply Subtype.heq_iff_coe_eq
  -/
