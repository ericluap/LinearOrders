import LinearOrders.Lindenbaum
import LinearOrders.InitialFinal
import LinearOrders.Iso
import LinearOrders.OrderEmbedding
import LinearOrders.OrderIso


noncomputable section
open Classical
open Set
open Set.Notation
open OrderEmbedding

universe u v w x y z

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {α' : Type y} {β' : Type z}
  [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ] [LinearOrder α'] [LinearOrder β']

def inl : α ↪o α ⊕ₗ β where
  toFun := Sum.inlₗ
  inj' := Sum.inl_injective
  map_rel_iff' := by simp

def inr : β ↪o α ⊕ₗ β where
  toFun := Sum.inrₗ
  inj' := Sum.inr_injective
  map_rel_iff' := by simp

@[simp]
theorem inl_le_inl_iff {a b : α}: (inl a : α ⊕ₗ β) ≤ inl b ↔ a ≤ b := by simp

@[simp]
theorem inr_le_inr_iff {a b : β} : (inr a : α ⊕ₗ β) ≤ inr b ↔ a ≤ b := by simp

@[simp]
theorem inl_lt_inl_iff {a b : α} : (inl a : α ⊕ₗ β) < inl b ↔ a < b := by simp

@[simp]
theorem inr_lt_inr_iff {a b : β} : (inr a : α ⊕ₗ β) < inr b ↔ a < b := by simp

@[simp]
theorem not_inr_le_inl {a : α} {b : β} : ¬inr b ≤ inl a := by unfold inl inr; simp

@[simp]
theorem not_inr_lt_inl [LT α] [LT β] {a : α} {b : β} : ¬inr b < inl a := by unfold inl inr; simp

@[simp]
theorem inl_le_inr {a : α} {b : β} : inl a ≤ inr b := by unfold inl inr; simp

@[simp]
theorem inl_lt_inr {a : α} {b : β} : inl a < inr b := by unfold inl inr; simp

@[simp]
theorem elim_sum_inl (f : α → γ) (g : β → γ) (x : α) :
  Sum.elim f g (Sum.inlₗ x) = f x := rfl

@[simp]
theorem elim_sum_inr (f : α → γ) (g : β → γ) (x : β) :
  Sum.elim f g (Sum.inrₗ x) = g x := rfl

@[simp]
theorem elim_inl (f : α → γ) (g : β → γ) (x : α) :
  Sum.elim f g (inl x) = f x := rfl

@[simp]
theorem elim_inr (f : α → γ) (g : β → γ) (x : β) :
  Sum.elim f g (inr x) = g x := rfl

abbrev Sum.mapₗ (f : α → α') (g : β → β') (x : α ⊕ₗ β) :=
  toLex (Sum.map f g x)

@[simp] theorem map_sum_inl (f : α → α') (g : β → β') (x : α) : Sum.mapₗ f g (Sum.inlₗ x) = Sum.inlₗ (f x) := rfl

@[simp] theorem map_sum_inr (f : α → α') (g : β → β') (x : β) : Sum.mapₗ f g (Sum.inrₗ x) = Sum.inrₗ (g x) := rfl

@[simp] theorem map_inl (f : α → α') (g : β → β') (x : α) : Sum.mapₗ f g (inl x) = inl (f x) := rfl

@[simp] theorem map_inr (f : α → α') (g : β → β') (x : β) : Sum.mapₗ f g (inr x) = inr (g x) := rfl

def Lex.sumCasesOn
    {motive : α ⊕ₗ β → Sort w}
    (t : α ⊕ₗ β)
    (inlₗ : (val : α) → motive (inl val))
    (inrₗ : (val : β) → motive (inr val)) : motive t :=
  Sum.casesOn t inlₗ inrₗ

@[ext]
theorem hom_ext {f g : α ⊕ₗ β ↪o γ} (h₁ : f.comp inl = g.comp inl) (h₂ : f.comp inr = g.comp inr) :
  f = g := by
  ext a
  cases' a using Lex.sumCasesOn with a a
  · apply DFunLike.congr_fun h₁ a
  · apply DFunLike.congr_fun h₂ a

theorem map_ord_preserving (f : α ↪o α') (g : β ↪o β') :
  ∀ {a b : α ⊕ₗ β}, Sum.mapₗ f g a ≤ Sum.mapₗ f g b ↔ a ≤ b := by
  intros a b
  cases' a using Lex.sumCasesOn with a a <;> cases' b using Lex.sumCasesOn with b b
  <;> simp

def map (f : α ↪o α') (g : β ↪o β') : α ⊕ₗ β ↪o α' ⊕ₗ β' where
  toFun := Sum.mapₗ f g
  inj' := Function.Injective.sum_map f.inj' g.inj'
  map_rel_iff' := map_ord_preserving f g

@[simp] theorem map_apply_inl (f : α ↪o α') (g : β ↪o β') (x : α) : (inl x).map f g = inl (f x) := rfl

@[simp] theorem map_apply_inr (f : α ↪o α') (g : β ↪o β') (x : β) : (inr x).map f g = inr (g x) := rfl

@[simp] theorem map_comp_inl (f : α ↪o α') (g : β ↪o β') : (map f g).comp inl = (inl : α' ↪o α' ⊕ₗ β').comp f := rfl

@[simp] theorem map_comp_inr (f : α ↪o α') (g : β ↪o β') : (map f g).comp inr = (inr : β' ↪o α' ⊕ₗ β').comp g := rfl

@[simp] theorem map_id_id : map (.id α) (.id β) = .id (α ⊕ₗ β) := by ext a <;> simp

@[simp] theorem map_comp_map {α'' β''} [LinearOrder α''] [LinearOrder β''] (f' : α' ↪o α'') (g' : β' ↪o β'')
  (f : α ↪o α') (g : β ↪o β') : (map f' g').comp (map f g) = map (f'.comp f) (g'.comp g) :=
  hom_ext rfl rfl

@[simp] theorem map_map {α'' β''} [LinearOrder α''] [LinearOrder β''] (f' : α' ↪o α'') (g' : β' ↪o β'')
  (f : α ↪o α') (g : β ↪o β') (x : α ⊕ₗ β) : map f' g' (map f g x) = map (f'.comp f) (g'.comp g) x :=
  DFunLike.congr_fun (map_comp_map f' g' f g) x

@[simp] theorem map_applied_comp_inl (f : α ↪o α') (g : β ↪o β') (x : α) : (map f g) (inl x) = (map f g).comp inl x := by rfl
@[simp] theorem map_applied_comp_inr (f : α ↪o α') (g : β ↪o β') (x : β) : (map f g) (inr x) = (map f g).comp inr x := by rfl

def toOrderIso (f : α ↪o β) (g : β ↪o α)
    (h₁ : g.comp f = OrderEmbedding.id _) (h₂ : f.comp g = OrderEmbedding.id _) : α ≃o β where
  toFun := f
  invFun := g
  left_inv := DFunLike.congr_fun h₁
  right_inv := DFunLike.congr_fun h₂
  map_rel_iff' := by simp

def sumCongr (f : α ≃o α') (g : β ≃o β') : α ⊕ₗ β ≃o α' ⊕ₗ β' :=
  toOrderIso (map f g) (map f.symm g.symm) (by ext <;> simp) (by ext <;> simp)

def change_left (f : α ≃o α') : α ⊕ₗ β ≃o α' ⊕ₗ β := sumCongr f (OrderIso.id β)

def change_right (g : β ≃o β') : α ⊕ₗ β ≃o α ⊕ₗ β' := sumCongr (OrderIso.id α) g

def swap_left (f : α ≃o α') (g : α ⊕ₗ β ≃o γ) : α' ⊕ₗ β ≃o γ := (change_left f).symm.trans g

def swap_right (g : β ≃o β') (f : α ⊕ₗ β ≃o γ) : α ⊕ₗ β' ≃o γ := (change_right g).symm.trans f

def lift (f : α ↪o γ) (g : β ↪o γ) (h : ∀a : α, ∀b : β, f a < g b) : (α ⊕ₗ β) ↪o γ where
  toFun := Sum.elim f g
  inj' := by
    unfold Function.Injective
    intros x y hxy
    rcases x with x | x <;> rcases y with y | y <;> simp at hxy <;> try rw [hxy]
    · have := h x y
      rw [hxy] at this
      simp at *
    · have := h y x
      rw [hxy] at this
      simp at *
  map_rel_iff' := by
    intros a b
    cases' a using Lex.sumCasesOn with a a
    <;> cases' b using Lex.sumCasesOn with b b
    <;> simp
    · exact LT.lt.le (h a b)
    · exact (h b a)

@[simp]
theorem lift_apply_inl (f : α ↪o γ) (g : β ↪o γ) (h : ∀a : α, ∀b : β, f a < g b) (x : α) : lift f g h (inl x) = f x :=
  rfl

@[simp]
theorem lift_apply_inr (f : α ↪o γ) (g : β ↪o γ) (h : ∀a : α, ∀b : β, f a < g b) (x : β) : lift f g h (inr x) = g x :=
  rfl

@[simp]
theorem lift_comp_inl (f : α ↪o γ) (g : β ↪o γ) (h : ∀a : α, ∀b : β, f a < g b) : (lift f g h).comp inl = f := rfl

@[simp]
theorem lift_comp_inr (f : α ↪o γ) (g : β ↪o γ) (h : ∀a : α, ∀b : β, f a < g b) : (lift f g h).comp inr = g := rfl

def sum_assoc : (α ⊕ₗ β) ⊕ₗ γ ≃o α ⊕ₗ (β ⊕ₗ γ) :=
  toOrderIso
    (lift (map (.id α) inl)
      ((inr : (β ⊕ₗ γ) ↪o α ⊕ₗ (β ⊕ₗ γ)).comp (inr : γ ↪o (β ⊕ₗ γ)))
      (by intros a b; cases' a using Lex.sumCasesOn with a a <;> simp))
    (lift
      ((inl : (α ⊕ₗ β ↪o ((α ⊕ₗ β) ⊕ₗ γ))).comp inl : α ↪o (α ⊕ₗ β) ⊕ₗ γ)
      (map inr (.id γ))
      (by intros a b; cases' b using Lex.sumCasesOn with b b <;> simp))
    (by ext <;> rfl) (by ext <;> rfl)

section Parts
variable (f : α ⊕ₗ β ≃o γ)

def left_part : Set (α ⊕ₗ β) := inl '' (univ : Set α)
def right_part : Set (α ⊕ₗ β) := inr '' (univ : Set β)

theorem in_left_or_right : ∀x : α ⊕ₗ β, x ∈ left_part ∨ x ∈ right_part := by
  intros x
  cases' x using Lex.sumCasesOn with x x
  constructor
  · unfold left_part
    simp
  · unfold right_part
    simp

theorem in_left_not_right : ∀x : α ⊕ₗ β, x ∈ left_part -> x ∉ right_part := by
  intros x hx
  cases' x using Lex.sumCasesOn with x x
  · intros hy
    unfold right_part at hy
    simp at hy
    rcases hy with ⟨y, hy⟩
    contradiction
  · unfold left_part at hx
    simp at hx
    rcases hx with ⟨x, hx⟩
    contradiction

theorem in_right_not_left : ∀x : α ⊕ₗ β, x ∈ right_part -> x ∉ left_part := by
  intros x hx
  cases' x using Lex.sumCasesOn with x x
  · unfold right_part at hx
    simp at hx
    rcases hx with ⟨x,hx⟩
    contradiction
  · intros hy
    unfold left_part at hy
    simp at hy
    rcases hy with ⟨y, hy⟩
    contradiction

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

theorem left_initial : isInitial (@left_part α β _ _) := by
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

theorem right_final : isFinal (@right_part α β _ _) := by
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
          (iso_to_initial f) left_initial)

theorem image_right_final : isFinal (image_right f) := by
  unfold image_right
  exact (final_maps_final_final
          (iso_to_final f) right_final)

theorem in_image_left_or_right (x : γ) : (x ∈ image_left f ∧ x ∉ image_right f) ∨ (x ∈ image_right f ∧ x ∉ image_left f) := by
  set inv := (f.invFun x) with inv_def
  cases' h : inv using Lex.sumCasesOn with y y
  · left
    constructor
    · simp [image_left, left_part]
      use y
      rw [←h]
      simp [inv_def]
    · simp [image_right]
      constructor
      · intros z hz1
        unfold right_part at hz1
        simp at hz1
        rcases hz1 with ⟨q, hq⟩
        contradiction
      · intros z hz2 q
        have := congr_arg f.invFun q
        rw [←inv_def, h] at this
        simp at this
        contradiction
  · right
    constructor
    · simp [image_right, right_part]
      use y
      rw [←h]
      simp [inv_def]
    · simp [image_left]
      constructor
      · intros z hz q
        have := congr_arg f.invFun q
        rw [←inv_def, h] at this
        simp at this
        contradiction
      · intros z hz1
        unfold left_part at hz1
        simp at hz1
        rcases hz1 with ⟨q,hq⟩
        contradiction

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

def split_map_from_initial (a : Set α) (ha : isInitial a) : α ↪o a ⊕ₗ (aᶜ : Set α) where
  toFun x := if h : x ∈ a then inl ⟨x, h⟩ else inr ⟨x, h⟩
  inj' := by
    unfold Function.Injective
    intros x y hxy
    simp at hxy
    by_cases h : x ∈ a <;> by_cases g : y ∈ a
    · simp [dif_pos h, dif_pos g] at hxy; trivial
    · simp [dif_pos h, dif_neg g] at hxy; trivial
    · simp [dif_neg h, dif_pos g] at hxy; trivial
    · simp [dif_neg h, dif_neg g] at hxy; trivial
  map_rel_iff' := by
    intros x y
    simp
    by_cases h : x ∈ a <;> by_cases g : y ∈ a
    · simp [dif_pos h, dif_pos g]
    · simp [dif_pos h, dif_neg g, initial_le_compl ha x h y g]
    · simp [dif_neg h, dif_pos g, initial_lt_compl ha y g x h]
    · simp [dif_neg h, dif_neg g]

def split_map_from_final (a : Set α) (ha : isFinal a) : α ↪o (aᶜ : Set α) ⊕ₗ a where
  toFun x := if h : x ∈ a then inr ⟨x, h⟩ else inl ⟨x, h⟩
  inj' := by
    unfold Function.Injective
    intros x y hxy
    simp at hxy
    by_cases h : x ∈ a <;> by_cases g : y ∈ a
    · simp [dif_pos h, dif_pos g] at hxy; trivial
    · simp [dif_pos h, dif_neg g] at hxy; trivial
    · simp [dif_neg h, dif_pos g] at hxy; trivial
    · simp [dif_neg h, dif_neg g] at hxy; trivial
  map_rel_iff' := by
    intros x y
    simp
    by_cases h : x ∈ a <;> by_cases g : y ∈ a
    · simp [dif_pos h, dif_pos g]
    · simp [dif_pos h, dif_neg g, compl_lt_final ha y g x h]
    · simp [dif_neg h, dif_pos g, compl_le_final ha x h y g]
    · simp [dif_neg h, dif_neg g]

def initial_plus_initial_compl (ha : isInitial a) :
  (a ⊕ₗ (aᶜ : Set α) ≃o α) :=
  toOrderIso
    (lift (Elem.val : a ↪o α) (Elem.val : (aᶜ : Set α) ↪o α)
      (by intros a b; unfold Elem.val; simp
          exact initial_lt_compl ha a a.property b b.property))
    (split_map_from_initial a ha)
    (by ext x <;> simp [split_map_from_initial] <;> by_cases h : Elem.val x ∈ a
        · simp [dif_pos h]; rfl
        · have := x.property; contradiction
        · have := x.property; contradiction
        · simp [dif_neg h]; rfl)
    (by ext x; simp [split_map_from_initial]; by_cases h : x ∈ a
        · simp [dif_pos h]; rfl
        · simp [dif_neg h]; rfl)

def final_compl_plus_final (ha : isFinal a) :
  (aᶜ : Set α) ⊕ₗ a ≃o α :=
  toOrderIso
    (lift (Elem.val : (aᶜ : Set α) ↪o α) (Elem.val : a ↪o α)
      (by intros a b; unfold Elem.val; simp
          exact compl_lt_final ha a a.property b b.property))
    (split_map_from_final a ha)
    (by ext x <;> simp [split_map_from_final] <;> by_cases h : Elem.val x ∈ a
        · have := x.property; contradiction
        · simp [dif_neg h]; rfl
        · simp [dif_pos h]; rfl
        · have := x.property; contradiction)
    (by ext x; simp [split_map_from_final]; by_cases h : x ∈ a
        · simp [dif_pos h]; rfl
        · simp [dif_neg h]; rfl)

end init_final

def left_part_iso : α ≃o (left_part : Set (α ⊕ₗ β)) := by
  have hq : ↑univ ≃o ↑(⇑inl '' univ) := iso_to_image inl univ (β := α ⊕ₗ β)
  have inl_order_image : (inl : α ↪o α ⊕ₗ β) '' univ = left_part := by constructor
  rw [inl_order_image] at hq
  exact (univ_iso_type.trans hq)

def right_part_iso : β ≃o (right_part : Set (α ⊕ₗ β)) := by
  have hq : (↑univ ≃o ↑(⇑inr '' univ)) := iso_to_image inr univ (β := α ⊕ₗ β)
  have inr_order_image : (inr : β ↪o α ⊕ₗ β) '' univ = right_part := by constructor
  rw [inr_order_image] at hq
  exact (univ_iso_type.trans hq)

def left_iso_image_left : α ≃o image_left f := by
  have z : left_part ≃o f '' left_part := iso_to_image (f.toRelEmbedding) left_part
  have : image_left f = f '' left_part := by
    unfold image_left
    trivial
  rw [←this] at z
  have a : α ≃o (left_part : Set (α ⊕ₗ β)) := left_part_iso
  exact a.trans z

def right_iso_image_right : β ≃o image_right f := by
  have z := iso_to_image f right_part (α := α ⊕ₗ β) (β := γ)
  simp at z
  have : image_right f = f '' right_part := by simp [image_right]
  rw [←this] at z
  exact (right_part_iso.trans z)

end Parts

def small_left_plus_compl {a b : Set α} : (↑(b ↓∩ a)ᶜ ≃o ↑(b \ a)) where
  toFun x := ⟨x.val.val, ⟨x.val.property, x.property⟩⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, by simp; exact x.property.2⟩
  left_inv := by unfold Function.LeftInverse; simp
  right_inv := by unfold Function.RightInverse Function.LeftInverse; simp
  map_rel_iff' := by simp

def initial_inside_sum_iso {a b : Set α}
(hab : isInitialInside b a) : b ⊕ₗ ↑(a \ b) ≃o ↑a := by
  rcases hab with ⟨b_sub_a, b_initial_a⟩
  have : (a ↓∩ b) ⊕ₗ ↑(a ↓∩ b)ᶜ ≃o a := initial_plus_initial_compl b_initial_a
  have : b ⊕ₗ ↑(a ↓∩ b)ᶜ ≃o a := swap_left (subset_cap_iso b_sub_a) this
  have : b ⊕ₗ ↑(a \ b) ≃o a := swap_right small_left_plus_compl this
  exact this

theorem initial_compl_initial {a b : Set α}
(ha : isInitial a) : isInitial (bᶜ ↓∩ ↑(a \ b)) := by
  unfold isInitial
  intros x hx y hy
  simp at *
  exact (ha x hx y hy)

def subset_compl_compl {a b : Set α}
(b_subset_a : b ⊆ a) : ↑(bᶜ ↓∩ a \ b)ᶜ ≃o ↑aᶜ where
  toFun x := ⟨x.val, by have := x.property; simp at this; trivial⟩
  invFun x := ⟨⟨x.val, compl_subset_compl.2 b_subset_a x.property⟩, by simp; exact x.property⟩
  left_inv := by unfold Function.LeftInverse; simp
  right_inv := by unfold Function.RightInverse Function.LeftInverse; simp
  map_rel_iff' := by simp

def initial_inside_sum_compl_iso {a b : Set α}
(ha : isInitial a) (b_sub_a : b ⊆ a) : (↑(a \ b) ⊕ₗ ↑aᶜ ≃o ↑bᶜ) := by
  have a_minus_b_subset : a \ b ⊆ bᶜ := by
    simp [subset_def]
  have a_minus_b_initial : isInitial (bᶜ ↓∩ ↑(a \ b)) := initial_compl_initial ha
  have : bᶜ ↓∩ ↑(a \ b) ⊕ₗ ↑(bᶜ ↓∩ ↑(a \ b))ᶜ ≃o ↑bᶜ := initial_plus_initial_compl a_minus_b_initial
  have : ↑(a \ b) ⊕ₗ ↑(bᶜ ↓∩ ↑(a \ b))ᶜ ≃o ↑bᶜ := swap_left (subset_cap_iso a_minus_b_subset) this
  have : ↑(a \ b) ⊕ₗ ↑aᶜ ≃o ↑bᶜ := swap_right (subset_compl_compl b_sub_a) this
  exact this

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
    have first_part : γ ⊕ₗ e ≃o α := by
      have iso := initial_inside_sum_iso h
      rw [←e_def] at iso
      have iso := iso.trans (left_iso_image_left f).symm
      exact (swap_left left_part_iso.symm iso)
    have second_part : e ⊕ₗ β ≃o δ := by
      rcases h with ⟨left_subset_image, _⟩
      have := initial_inside_sum_compl_iso (image_left_initial f) left_subset_image
      rw [←e_def] at this
      rw [image_left_compl_image_right f] at this
      have := swap_right (right_iso_image_right f).symm this
      rw [left_compl_right] at this
      exact this.trans right_part_iso.symm
    constructor <;> apply nonempty_of_exists
    use first_part
    use second_part
  · set e := left_part \ (image_left f) with e_def
    use e, Subtype.instLinearOrder e
    right
    have first_part : α ⊕ₗ e ≃o γ := by
      have := initial_inside_sum_iso h
      rw [←e_def] at this
      have := swap_left (left_iso_image_left f).symm this
      exact this.trans left_part_iso.symm
    have second_part : e ⊕ₗ δ ≃o β := by
      rcases h with ⟨image_subset_left, _⟩
      have iso := initial_inside_sum_compl_iso left_initial image_subset_left
      rw [←e_def, image_left_compl_image_right f, left_compl_right] at iso
      have iso := iso.trans (right_iso_image_right f).symm
      exact swap_right (right_part_iso).symm iso
    constructor <;> apply nonempty_of_exists
    use first_part
    use second_part

theorem initial_plus (f : α ≼i β) :
∃e : Type v, ∃s : LinearOrder e, Nonempty (α ⊕ₗ e ≃o β) := by
  use ↑(f '' univ)ᶜ, Subtype.instLinearOrder (f '' univ)ᶜ
  have := image_of_univ_initial f
  have iso := initial_plus_initial_compl this
  have iso2 := type_iso_image f.toRelEmbedding
  have iso := swap_left iso2.symm iso
  apply nonempty_of_exists
  use iso

theorem final_plus (f : α ≼f β) :
∃e : Type v, ∃s : LinearOrder e, Nonempty (e ⊕ₗ α ≃o β) := by
  use ↑(f '' univ)ᶜ, Subtype.instLinearOrder (f '' univ)ᶜ
  have := image_of_univ_final f
  have iso := final_compl_plus_final this
  have iso2 := type_iso_image f.toRelEmbedding
  have iso := swap_right iso2.symm iso
  apply nonempty_of_exists
  use iso

def plus_initial (f : α ⊕ₗ β ≃o γ) : α ≼i γ where
  toFun x := f (inl x)
  inj' := by simp [Function.Injective]
  mem_range_of_rel' := by
    simp; intros a b hab
    cases' g : (f.invFun b) using Lex.sumCasesOn with z z
    use z
    simp [←g]
    have : f (inr z) ≤ f (inl a) := by simp [←g]; trivial
    simp at this
  map_rel_iff' := by simp

def plus_final (f : α ⊕ₗ β ≃o γ) : β ≼f γ where
  toFun x := f (inr x)
  inj' := by simp [Function.Injective]
  final' := by
    simp; intros a b hab
    cases' g : (f.invFun b) using Lex.sumCasesOn with z z
    have : f (inr a) ≤ f (inl z) := by simp [←g]; trivial
    simp at this
    use z
    simp [←g]
  map_rel_iff' := by simp

def initial_initial_sum (f : α ≼i β) : α ≼i β ⊕ₗ γ := by
  have : β ⊕ₗ γ ≃o β ⊕ₗ γ := OrderIso.refl (Lex (β ⊕ γ))
  have : β ≼i β ⊕ₗ γ := plus_initial this
  have : α ≼i β ⊕ₗ γ := f.trans this
  trivial

def final_final_sum (f : α ≼f β) : α ≼f γ ⊕ₗ β := by
  have : γ ⊕ₗ β ≃o γ ⊕ₗ β := OrderIso.refl (Lex (γ ⊕ β))
  have : β ≼f γ ⊕ₗ β := plus_final this
  have : α ≼f γ ⊕ₗ β := f.trans this
  trivial
