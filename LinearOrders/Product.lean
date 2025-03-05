import Mathlib.Order.Hom.Basic
import Mathlib.Order.Hom.Set
import Mathlib.Order.InitialSeg
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Sum.Order
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sum.Order
import Mathlib.Data.Set.Subset
import LinearOrders.Iso
import Mathlib.Data.Prod.Lex
import Mathlib.SetTheory.Ordinal.Basic
import LinearOrders.Sum
import LinearOrders.Lindenbaum
import LinearOrders.InitialFinal
import Mathlib.Data.Int.ModEq

noncomputable section
open Classical
open Set
open Set.Notation

universe u v w x y

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]

theorem le_iff' {a b : α ×ₗ β} : a ≤ b ↔ a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2 := by
  constructor
  · intros h
    have h : toLex (ofLex a) ≤ toLex (ofLex b) := by
      exact h
    rw [Prod.Lex.le_iff] at h
    rcases h with h | h
    · left
      exact h
    · rcases h with ⟨l, r⟩
      right
      constructor
      · exact l
      · exact r
  · intros h
    rcases h with h | h
    have : a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2 := by
      left
      exact h
    change (ofLex a).1 < (ofLex b).1 ∨
      (ofLex a).1 = (ofLex b.1) ∧ (ofLex a).2 ≤ (ofLex b).2 at this
    rw [Prod.Lex.le_iff]
    exact this
    rcases h with ⟨l, r⟩
    have : a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2 := by
      right
      constructor
      exact l
      exact r
    change (ofLex a).1 < (ofLex b).1 ∨
      (ofLex a).1 = (ofLex b.1) ∧ (ofLex a).2 ≤ (ofLex b).2 at this
    rw [Prod.Lex.le_iff]
    exact this

theorem swap_left_prod (f : α ≃o γ) : Nonempty (α ×ₗ β ≃o γ ×ₗ β) := by
  set q : α ×ₗ β → γ ×ₗ β := λg => (f g.fst, g.snd) with q_def
  have qinj : Function.Injective q := by
    unfold Function.Injective
    intros x y hxy
    simp [q_def] at hxy
    rw [Prod.ext_iff] at hxy
    simp at hxy
    rw [Prod.ext_iff]
    exact hxy
  have qsurj : Function.Surjective q := by
    unfold Function.Surjective
    intros x
    use (f.invFun x.fst, x.snd)
    simp [q_def]
  have qord : ∀{x y : α ×ₗ β}, q x ≤ q y ↔ x ≤ y := by
    intros x y
    constructor
    · intros hxy
      simp [q_def] at hxy
      rw [le_iff']
      rw [le_iff'] at hxy
      simp at hxy
      rcases hxy with h | h
      left
      trivial
      right
      exact h
    · intros hxy
      simp [q_def]
      rw [le_iff']
      rw [le_iff'] at hxy
      simp
      exact hxy
  exact make_iso qinj qsurj qord

theorem times_one : Nonempty (Fin 1 ×ₗ α ≃o α) := by
  set q : Fin 1 ×ₗ α → α := λg => g.snd with q_def
  have qinj : Function.Injective q := by
    exact Prod.snd_injective
  have qsurj : Function.Surjective q := by
    unfold Function.Surjective
    intros x
    use ⟨0, x⟩
  have qord : ∀{x y : Fin 1 ×ₗ α}, q x ≤ q y ↔ x ≤ y := by
    intros x y
    constructor
    · intros hxy
      simp [q_def] at hxy
      have : x ≤ y ↔ toLex (ofLex x) ≤ toLex (ofLex y):= by
        exact ge_iff_le
      rw [this, Prod.Lex.le_iff]
      right
      constructor
      · rw [Fin.ext_iff]
        simp
      · trivial
    · intros hxy
      simp [q_def]
      have : x ≤ y ↔ toLex (ofLex x) ≤ toLex (ofLex y):= by
        exact ge_iff_le
      rw [this, Prod.Lex.le_iff] at hxy
      rcases hxy with h | h
      rw [←Fin.val_fin_lt] at h
      simp at h
      rcases h with ⟨_, z⟩
      trivial
  exact make_iso qinj qsurj qord

theorem distribute : Nonempty ((α ⊕ₗ β) ×ₗ γ ≃o (α ×ₗ γ) ⊕ₗ (β ×ₗ γ)) := by
  set q : (α ⊕ₗ β) ×ₗ γ → (α ×ₗ γ) ⊕ₗ (β ×ₗ γ) := λg =>
    match g.fst with
    | Sum.inlₗ a => Sum.inlₗ (toLex (a, g.snd))
    | Sum.inrₗ b => Sum.inrₗ (toLex (b, g.snd))
    with q_def
  have qinj : Function.Injective q := by
    unfold Function.Injective
    intros x y hxy
    simp [q_def] at hxy
    rcases x with ⟨x | x, xsnd⟩
    · rcases y with ⟨y | y, ysnd⟩
      · simp at hxy
        rcases hxy with ⟨fst_eq, snd_eq⟩
        rw [Prod.ext_iff]
        simp
        constructor
        rw [fst_eq]
        trivial
      · simp at hxy
    · rcases y with ⟨y | y, ysnd⟩
      · simp at hxy
      · simp at hxy
        rcases hxy with ⟨fst_eq, snd_eq⟩
        rw [Prod.ext_iff]
        simp
        constructor
        rw [fst_eq]
        trivial
  have qsurj : Function.Surjective q := by
    unfold Function.Surjective
    intros x
    rcases x with ⟨xfst, xsnd⟩ | ⟨xfst, xsnd⟩
    · use (Sum.inl xfst, xsnd)
      simp [q_def]
      change _ = toLex _
      simp
      change _ = toLex _
      simp
    · use (Sum.inr xfst, xsnd)
      simp [q_def]
      change _ = toLex _
      simp
      change _ = toLex _
      simp
  have qord : ∀{x y : (α ⊕ₗ β) ×ₗ γ}, q x ≤ q y ↔ x ≤ y := by
    intros x y
    constructor
    · intros hxy
      change toLex _ ≤ toLex _
      simp [q_def] at hxy
      rcases x with ⟨x | x, xsnd⟩
      · rcases y with ⟨y | y, ysnd⟩
        · simp at hxy
          rw [Prod.Lex.le_iff]
          rw [Prod.Lex.le_iff] at hxy
          rcases hxy with h | h
          · left
            simp
            simp at h
            rw [←Sum.Lex.inl_lt_inl_iff (β := β)] at h
            exact h
          · right
            simp
            simp at h
            rcases h with ⟨xy, snd⟩
            constructor
            · rw [xy]
            · trivial
        · rw [Prod.Lex.le_iff]
          simp
          exact (Sum.Lex.inl_lt_inr x y)
      · rcases y with ⟨y | y, ysnd⟩
        · simp at hxy
        · simp at hxy
          rw [Prod.Lex.le_iff] at hxy
          rw [Prod.Lex.le_iff]
          rcases hxy with h | h
          · left
            simp
            simp at h
            rw [←Sum.Lex.inr_lt_inr_iff (α := α)] at h
            exact h
          · right
            simp
            simp at h
            rcases h with ⟨xy, snd⟩
            constructor
            · rw [xy]
            · trivial
    · intros hxy
      change toLex _ ≤ toLex _ at hxy
      simp [q_def]
      rcases x with ⟨x | x, xsnd⟩
      · rcases y with ⟨y | y, ysnd⟩
        · simp
          rw [Prod.Lex.le_iff] at hxy
          rcases hxy with h | h
          · simp at h
            rw [Prod.Lex.le_iff]
            left
            simp
            change toLex _ < toLex _ at h
            simp at h
            trivial
          · simp at h
            rw [Prod.Lex.le_iff]
            right
            simp
            change toLex _ = toLex _ ∧ _ at h
            simp at h
            exact h
        · simp
      · rcases y with ⟨y | y, ysnd⟩
        · rw [Prod.Lex.le_iff] at hxy
          simp at hxy
          contradiction
        · simp
          rw [Prod.Lex.le_iff] at hxy
          change toLex _ < toLex _ ∨ toLex _ = toLex _ ∧ _ at hxy
          simp at hxy
          rw [Prod.Lex.le_iff]
          trivial
  exact make_iso qinj qsurj qord

theorem fin_sum : ∀{n m : Nat}, Nonempty (Fin (n+m) ≃o (Fin n) ⊕ₗ (Fin m)) := by
  intros n m
  set q : (Fin n) ⊕ₗ (Fin m) → Fin (n+m) := λg =>
    match g with
    | Sum.inl a => ⟨a.val, by omega⟩
    | Sum.inr b => ⟨b.val+n, by omega⟩
    with q_def
  have qinj : Function.Injective q := by
    unfold Function.Injective
    intros x y hxy
    simp [q_def] at hxy
    rcases x with x | x
    · rcases y with y | y
      · simp at hxy
        change toLex _ = toLex _
        simp
        exact Fin.eq_of_val_eq hxy
      · simp at hxy
        omega
    · rcases y with y | y
      · simp at hxy
        omega
      · simp at hxy
        change toLex _ = toLex _
        simp
        exact Fin.eq_of_val_eq hxy
  have qsurj : Function.Surjective q := by
    unfold Function.Surjective
    intros x
    by_cases h : x.val < n
    · use (Sum.inl ⟨x, h⟩)
    · have : x-n < m := by omega
      use (Sum.inr ⟨x-n, this⟩)
      simp [q_def]
      apply Fin.eq_of_val_eq
      simp
      omega
  have qord : ∀{x y : (Fin n) ⊕ₗ (Fin m)}, q x ≤ q y ↔ x ≤ y := by
    intros x y
    constructor
    · intros hxy
      simp [q_def] at hxy
      rcases x with x | x
      · rcases y with y | y
        · simp at hxy
          change toLex _ ≤ toLex _
          simp
          trivial
        · exact (Sum.Lex.inl_le_inr x y)
      · rcases y with y | y
        · simp at hxy
          omega
        · simp at hxy
          change toLex _ ≤ toLex _
          simp
          trivial
    · intros hxy
      simp [q_def]
      rcases x with x | x
      · rcases y with y | y
        · simp
          change toLex _ ≤ toLex _ at hxy
          simp at hxy
          trivial
        · simp
          omega
      · rcases y with y | y
        · have : ¬Sum.inr x ≤ Sum.inl y := Sum.not_inr_le_inl
          contradiction
        · simp
          change toLex _ ≤ toLex _ at hxy
          simp at hxy
          trivial
  rcases make_iso qinj qsurj qord with ⟨iso⟩
  apply nonempty_of_exists
  use iso.symm

/-
theorem fin_dual {n : ℕ}: Nonempty ((Fin (n+1)) ≃o (Fin (n+1))ᵒᵈ) := by
  set q' : ℕ → ℕ := λg => Int.natMod (-(g : ℤ) -1) (n+1) with q'_def
  have : ∀m : ℕ, q' m < n+1 := by
    simp [q'_def]
    intros m
    apply Int.natMod_lt
    simp
  set q : Fin (n+1) → (Fin (n+1))ᵒᵈ := λg => ⟨q' g.val, this g.val⟩
    with q_def
  have qinj : Function.Injective q := by
    unfold Function.Injective
    intros x y hxy
    simp [q_def] at hxy
    apply Fin.val_eq_of_eq at hxy
    simp [q'_def] at hxy
    have : (-x - 1) ≡ (-y - 1) [ZMOD n+1] := by
      unfold Int.ModEq
      simp
    #check Int.ModEq
    #check Int.modEq_iff_add_fac.mp hxy
    #check Int.natMod_eq-/

lemma initial_in_finite_prod_initial_base_case : ∀ (α : Type u) (β : Type v) [inst : LinearOrder α] [inst_1 : LinearOrder β],
  (Lex (Fin (Nat.zero + 1) × α) ≼i Lex (Fin (Nat.zero + 1) × β) → Nonempty (α ≼i β)) := by
  intros α β _ _ initial
  simp at initial
  rcases (times_one (α := α)) with ⟨times_a⟩
  rcases (times_one (α := β)) with ⟨times_b⟩
  have := initial_swap_left initial times_a.symm
  have := initial_swap_right this times_b
  apply nonempty_of_exists
  use this

lemma initial_in_finite_prod_initial_induction_step (x : ℕ) (ih : ∀ (α : Type u) (β : Type v) [inst : LinearOrder α] [inst_1 : LinearOrder β],
  (Lex (Fin (x + 1) × α) ≼i Lex (Fin (x + 1) × β) → Nonempty (α ≼i β)) ∧
    (Lex (Fin (x + 1) × β) ≼i Lex (Fin (x + 1) × α) → Nonempty (β ≼i α))) :
Lex (Fin (Nat.succ x + 1) × α) ≼i Lex (Fin (Nat.succ x + 1) × β) → Nonempty (α ≼i β) := by
  intros initial
  rcases fin_sum (n := Nat.succ x) (m := 1) with ⟨iso2⟩
  rcases swap_left_prod iso2 (β := α) with ⟨iso⟩
  rcases distribute (α := Fin (x+1)) (β := Fin 1) (γ := α) with ⟨iso2⟩
  have iso := iso.trans iso2
  rcases times_one (α := α) with ⟨iso2⟩
  have iso2 := change_right iso2 (α := (Fin (x + 1) ×ₗ α))
  have iso := iso.trans iso2
  have new_init := initial_swap_left initial iso.symm
  apply initial_plus at new_init
  rcases new_init with ⟨e, ⟨_, ⟨eiso⟩⟩⟩
  have assoc := sum_assoc (α := (Fin (x + 1) ×ₗ α)) (β := α) (γ := e)
  have eiso := assoc.symm.trans eiso
  rcases fin_sum (n := Nat.succ x) (m := 1) with ⟨iso2⟩
  rcases swap_left_prod iso2 (β := β) with ⟨iso⟩
  rcases distribute (α := Fin (x+1)) (β := Fin 1) (γ := β) with ⟨iso2⟩
  have iso := iso.trans iso2
  rcases times_one (α := β) with ⟨iso2⟩
  have iso2 := change_right iso2 (α := (Fin (x + 1) ×ₗ β))
  have iso := iso.trans iso2
  have iso := eiso.trans iso
  have refined := sum_refinement iso
  rcases refined with ⟨e', ⟨_, new_cases⟩⟩
  rcases new_cases with ⟨⟨fst_iso⟩, ⟨snd_iso⟩⟩ | ⟨⟨fst_iso⟩, ⟨_⟩⟩
  have := plus_initial fst_iso
  rcases ih α β with ⟨_, ih'⟩
  rcases ih' this with ⟨binit⟩
  have final := plus_final snd_iso
  have : β ≼i α ⊕ₗ e := initial_initial_sum binit
  rcases lindenbaum this final with ⟨iso⟩
  have := plus_initial iso.symm
  apply nonempty_of_exists
  use this
  have := plus_initial fst_iso
  rcases ih α β with ⟨ih', _⟩
  have := ih' this
  trivial

theorem initial_in_finite_prod_initial' : ∀n : Nat,
∀α : Type u, ∀β : Type v, [LinearOrder α] → [LinearOrder β] →
(Fin (n+1) ×ₗ α ≼i Fin (n+1) ×ₗ β → Nonempty (α ≼i β)) ∧
(Fin (n+1) ×ₗ β ≼i Fin (n+1) ×ₗ α → Nonempty (β ≼i α)) := by
  intros n
  induction n with
  | zero =>
    intros α β _ _
    constructor
    · exact initial_in_finite_prod_initial_base_case α β
    · exact initial_in_finite_prod_initial_base_case β α
  | succ x ih =>
    intros α β _ _
    constructor
    · exact initial_in_finite_prod_initial_induction_step x ih
    · have : ∀ (α : Type v) (β : Type u) [inst : LinearOrder α] [inst_1 : LinearOrder β],
    (Lex (Fin (x + 1) × α) ≼i Lex (Fin (x + 1) × β) → Nonempty (α ≼i β)) ∧
      (Lex (Fin (x + 1) × β) ≼i Lex (Fin (x + 1) × α) → Nonempty (β ≼i α)) := by
        intros a b _ _
        have ih := ih b a
        tauto
      exact initial_in_finite_prod_initial_induction_step x this

theorem initial_in_finite_prod_initial : ∀n : Nat,
∀α : Type u, ∀β : Type v, [LinearOrder α] → [LinearOrder β] →
(Fin (n+1) ×ₗ α ≼i Fin (n+1) ×ₗ β → Nonempty (α ≼i β)) := by
  intros n α β _ _
  rcases initial_in_finite_prod_initial' n α β with ⟨initial, _ ⟩
  trivial

lemma final_in_finite_prod_final_base_case : ∀ (α : Type u) (β : Type v) [inst : LinearOrder α] [inst_1 : LinearOrder β],
  (Lex (Fin (Nat.zero + 1) × α) ≼f Lex (Fin (Nat.zero + 1) × β) → Nonempty (α ≼f β)) := by
  intros α β _ _ final
  simp at final
  rcases (times_one (α := α)) with ⟨times_a⟩
  rcases (times_one (α := β)) with ⟨times_b⟩
  have := final_swap_left final times_a.symm
  have := final_swap_right this times_b
  apply nonempty_of_exists
  use this

lemma final_in_finite_prod_final_induction_step (x : ℕ) (ih : ∀ (α : Type u) (β : Type v) [inst : LinearOrder α] [inst_1 : LinearOrder β],
  (Lex (Fin (x + 1) × α) ≼f Lex (Fin (x + 1) × β) → Nonempty (α ≼f β)) ∧
    (Lex (Fin (x + 1) × β) ≼f Lex (Fin (x + 1) × α) → Nonempty (β ≼f α))) :
  (Lex (Fin (Nat.succ x + 1) × α) ≼f Lex (Fin (Nat.succ x + 1) × β) → Nonempty (α ≼f β)) := by
  intros final
  have : Nat.succ x + 1 = 1 + Nat.succ x := by omega
  rw [this] at final
  rcases fin_sum (m := Nat.succ x) (n := 1) with ⟨iso2⟩
  rcases swap_left_prod iso2 (β := α) with ⟨iso⟩
  rcases distribute (β := Fin (x+1)) (α := Fin 1) (γ := α) with ⟨iso2⟩
  have iso := iso.trans iso2
  rcases times_one (α := α) with ⟨iso2⟩
  have iso2 := change_left iso2 (β := (Fin (x + 1) ×ₗ α))
  have iso := iso.trans iso2
  have new_final := final_swap_left final iso.symm
  apply final_plus at new_final
  rcases new_final with ⟨e, ⟨_, ⟨eiso⟩⟩⟩
  have assoc := sum_assoc (α := e) (γ := Fin (x + 1) ×ₗ α) (β := α)
  have eiso := assoc.trans eiso
  rcases fin_sum (m := Nat.succ x) (n := 1) with ⟨iso2⟩
  rcases swap_left_prod iso2 (β := β) with ⟨iso⟩
  rcases distribute (β := Fin (x+1)) (α := Fin 1) (γ := β) with ⟨iso2⟩
  have iso := iso.trans iso2
  rcases times_one (α := β) with ⟨iso2⟩
  have iso2 := change_left iso2 (β := (Fin (x + 1) ×ₗ β))
  have iso := iso.trans iso2
  have iso := eiso.trans iso
  have refined := sum_refinement iso
  rcases refined with ⟨e', ⟨_, new_cases⟩⟩
  rcases new_cases with ⟨⟨_⟩, ⟨snd_iso⟩⟩ | ⟨⟨fst_iso⟩, ⟨snd_iso⟩⟩
  have := plus_final snd_iso
  rcases ih α β with ⟨ih', _⟩
  have := ih' this
  trivial
  have := plus_final snd_iso
  rcases ih α β with ⟨_, ih'⟩
  rcases ih' this with ⟨bfinal⟩
  have final : β ≼f e ⊕ₗ α := final_final_sum bfinal
  have : e ⊕ₗ α ≼i β := plus_initial fst_iso
  rcases lindenbaum this final with ⟨iso⟩
  have := plus_final iso
  apply nonempty_of_exists
  use this

theorem final_in_finite_prod_final' : ∀n : Nat,
∀α : Type u, ∀β : Type v, [LinearOrder α] → [LinearOrder β] →
  (Fin (n+1) ×ₗ α ≼f Fin (n+1) ×ₗ β → Nonempty (α ≼f β)) ∧ (Fin (n+1) ×ₗ β ≼f Fin (n+1) ×ₗ α → Nonempty (β ≼f α)) := by
  intros n
  induction n with
  | zero =>
    intros α β _ _
    constructor
    · exact final_in_finite_prod_final_base_case α β
    · exact final_in_finite_prod_final_base_case β α
  | succ x ih =>
    intros α β _ _
    constructor
    · exact final_in_finite_prod_final_induction_step x ih
    · have : ∀ (α : Type v) (β : Type u) [inst : LinearOrder α] [inst_1 : LinearOrder β],
    (Lex (Fin (x + 1) × α) ≼f Lex (Fin (x + 1) × β) → Nonempty (α ≼f β)) ∧
      (Lex (Fin (x + 1) × β) ≼f Lex (Fin (x + 1) × α) → Nonempty (β ≼f α)) := by
        intros a b _ _
        have ih := ih b a
        tauto
      exact final_in_finite_prod_final_induction_step x this

theorem final_in_finite_prod_final : ∀n : Nat,
∀α : Type u, ∀β : Type v, [LinearOrder α] → [LinearOrder β] →
(Fin (n+1) ×ₗ α ≼f Fin (n+1) ×ₗ β → Nonempty (α ≼f β)) := by
  intros n α β _ _
  rcases final_in_finite_prod_final' n α β with ⟨final, _ ⟩
  trivial

theorem finite_prod_cancel (n : ℕ) :
Fin (n+1) ×ₗ α ≃o Fin (n+1) ×ₗ β → Nonempty (α ≃o β) := by
  intros finite_iso
  rcases initial_in_finite_prod_initial n α β (iso_to_initial finite_iso) with ⟨initial⟩
  rcases final_in_finite_prod_final n β α (iso_to_final finite_iso.symm) with ⟨final⟩
  have := lindenbaum initial final
  trivial
