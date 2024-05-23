import Mathlib.Init.Order.LinearOrder
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
    rw [←Prod.Lex.le_iff] at this
    exact this
    rcases h with ⟨l, r⟩
    have : a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2 := by
      right
      constructor
      exact l
      exact r
    rw [←Prod.Lex.le_iff] at this
    exact this

theorem swap_left (f : α ≃o γ) : Nonempty (α ×ₗ β ≃o γ ×ₗ β) := by
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

theorem initial_in_finite_prod_initial : ∀n : Nat,
∀α : Type u, ∀β : Type u, [LinearOrder α] → [LinearOrder β] → Fin (n+1) ×ₗ α ≼i Fin (n+1) ×ₗ β → Nonempty (α ≼i β) := by
  intros n
  induction n with
  | zero =>
    intros α β _ _ initial
    simp at initial
    have : 0 + 1 = 1 := by simp
    rw [this] at initial
    rcases (times_one (α := α)) with ⟨times_a⟩
    rcases (times_one (α := β)) with ⟨times_b⟩
    have := initial_swap_left initial times_a.symm
    have := initial_swap_right this times_b
    apply nonempty_of_exists
    use this
  | succ x ih =>
    intros α β _ _ initial
    rcases fin_sum (n := Nat.succ x) (m := 1) with ⟨iso2⟩
    rcases swap_left iso2 (β := α) with ⟨iso⟩
    rcases distribute (α := Fin (x+1)) (β := Fin 1) (γ := α) with ⟨iso2⟩
    have iso := iso.trans iso2
    rcases times_one (α := α) with ⟨iso2⟩
    rcases change_iso_right iso2 (α := (Fin (x + 1) ×ₗ α)) with ⟨iso2⟩
    have iso := iso.trans iso2
    have new_init := initial_swap_left initial iso.symm
    apply initial_plus at new_init
    rcases new_init with ⟨e, ⟨_, ⟨eiso⟩⟩⟩
    rcases sum_assoc (α := (Fin (x + 1) ×ₗ α)) (β := α) (γ := e) with ⟨assoc⟩
    have eiso := assoc.symm.trans eiso
    rcases fin_sum (n := Nat.succ x) (m := 1) with ⟨iso2⟩
    rcases swap_left iso2 (β := β) with ⟨iso⟩
    rcases distribute (α := Fin (x+1)) (β := Fin 1) (γ := β) with ⟨iso2⟩
    have iso := iso.trans iso2
    rcases times_one (α := β) with ⟨iso2⟩
    rcases change_iso_right iso2 (α := (Fin (x + 1) ×ₗ β)) with ⟨iso2⟩
    have iso := iso.trans iso2
    have iso := eiso.trans iso
    have refined := sum_refinement iso
    rcases refined with ⟨e', ⟨_, new_cases⟩⟩
    rcases new_cases with ⟨⟨fst_iso⟩, ⟨snd_iso⟩⟩ | ⟨⟨fst_iso⟩, ⟨_⟩⟩
    have := plus_initial fst_iso
    rcases ih β α this with ⟨binit⟩
    have final := plus_final snd_iso
    have : α ⊕ₗ e ≃o α ⊕ₗ e := by exact OrderIso.refl (Lex (α ⊕ e))
    have : α ≼i α ⊕ₗ e := plus_initial this
    have := binit.trans this
    have : β ≼i α ⊕ₗ e := by exact this
    rcases lindenbaum this final with ⟨iso⟩
    have := plus_initial iso.symm
    apply nonempty_of_exists
    use this
    have := plus_initial fst_iso
    have := ih α β this
    trivial
