import Mathlib.Init.Order.LinearOrder
import Mathlib.Order.Hom.Basic
import Mathlib.Order.InitialSeg
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.Data.Finset.Basic
import Mathlib.Init.Set
import Mathlib.Data.Set.Subset

noncomputable section
open Classical
open Set
open Set.Notation

universe u v

/-
Define what a final embedding is and add coerceions
-/
variable {α : Type*} {β : Type*} {γ : Type*} {r : α → α → Prop} {s : β → β → Prop}
  {t : γ → γ → Prop}

structure FinalSeg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s where
  final' : ∀ a b, s (toRelEmbedding a) b -> ∃ a', toRelEmbedding a' = b

infixl:24 " ≼f " => FinalSeg

instance : Coe (r ≼f s) (r ↪r s) :=
  ⟨FinalSeg.toRelEmbedding⟩

instance : FunLike (r ≼f s) α β where
  coe f := f.toFun
  coe_injective' := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    congr with x
    exact congr_fun h x

instance : EmbeddingLike (r ≼f s) α β where
  injective' f := f.inj'

abbrev OrderInitialSeg (α β : Type*) [LinearOrder α] [LinearOrder β] :=
  @LE.le α _ ≼i @LE.le β _
infixl:25 " ≼i " => OrderInitialSeg

abbrev OrderFinalSeg (α β : Type*) [LinearOrder α] [LinearOrder β] :=
  @LE.le α _ ≼f @LE.le β _
infixl:25 " ≼f " => OrderFinalSeg

variable [LinearOrder α] [LinearOrder β]

variable (f : α ≼i β) (g : β ≼f α)

def FinalSeg_to_dual : βᵒᵈ ≼i αᵒᵈ  :=
  {
    toFun := g.toFun
    inj' := g.inj',
    init' := by
      intros x y z
      simp at *
      exact g.final' x y z
    map_rel_iff' := by
      simp at *
      intros x y
      exact RelEmbedding.map_rel_iff g.toRelEmbedding
  }

def InitialSeg_to_dual : αᵒᵈ ≼f βᵒᵈ :=
 {
    toFun := f.toFun
    inj' := f.inj',
    final' := by
      intros x y z
      simp at *
      exact f.init' x y z
    map_rel_iff' := by
      simp at *
      intros x y
      exact RelEmbedding.map_rel_iff f.toRelEmbedding
  }

/-
Define what it means for a subset of a linear order to be an initial or final segment
-/
def isInitial (s : Set α) := ∀x ∈ s, ∀y : α, y < x → y ∈ s
def isFinal (s : Set α) := ∀x ∈ s, ∀y : α, y > x → y ∈ s

theorem isFinal_to_dual {s : Set α} (hs : isFinal s) : isInitial (α := αᵒᵈ) s := by
  unfold isInitial
  intros x hx y hy
  exact hs x hx y hy

theorem isInitial_to_dual {s : Set α} (hs : isInitial s) : isFinal (α := αᵒᵈ) s := by
  unfold isFinal
  intros x hx y hy
  exact hs x hx y hy

/-
Initial embedding maps an initial segment to an initial segment
-/
theorem initial_maps_initial_initial {s : Set α} (hs : isInitial s) : isInitial (f '' s) := by
  unfold isInitial at *
  intros x hx y hy
  rw [mem_image] at *
  obtain ⟨w, hw⟩ := hx
  obtain ⟨w_in_s, fw_x⟩ := hw
  rw [←fw_x] at hy
  have hy' : y ≤ f w := le_of_lt hy
  have hf := (f.init' w y hy')
  obtain ⟨z, hz⟩ := hf
  simp at *
  rw [←hz] at hy
  have ord : z < w := by
    rw [←lt_iff_lt_of_le_iff_le f.map_rel_iff']
    trivial
  use z
  constructor
  exact (hs w w_in_s z ord)
  trivial

theorem image_of_univ_initial : isInitial (f '' univ) := by
  apply initial_maps_initial_initial
  unfold isInitial
  simp

/-
Final embedding maps a final segment to a final segment
-/
theorem final_maps_final_final {s : Set β} (hs : isFinal s) : isFinal (g '' s) := by
  apply isFinal_to_dual at hs
  apply initial_maps_initial_initial (FinalSeg_to_dual g) at hs
  trivial

theorem image_of_univ_final : isFinal (g '' univ) := by
  apply final_maps_final_final
  unfold isFinal
  simp

/-
Complement of initial segment is final
-/
theorem comp_initial_final {s : Set α} (hs : isInitial s) : isFinal (univ \ s) := by
  unfold isFinal
  intros x hx y hy
  unfold isInitial at hs
  apply byContradiction
  intros hny
  simp at *
  have contra := hs y hny x hy
  trivial

/-
Complement of final segment is initial
-/
theorem comp_final_initial {s : Set α} (hs : isFinal s) : isInitial (univ \ s) := by
  apply isFinal_to_dual at hs
  apply comp_initial_final at hs
  trivial

/-
The union of initial segments is an initial segment
-/
theorem union_initial_initial [LinearOrder α]
  (f : ℕ → Set α) (hf : ∀ n : ℕ, isInitial (f n)) : isInitial (⋃ n, f n) := by
  unfold isInitial
  intros x hx y hy
  rw [mem_iUnion]
  rw [mem_iUnion] at hx
  obtain ⟨w, hw⟩ := hx
  use w
  exact (hf w) x hw y hy

theorem initial_in_subset {a b : Set α} (ha : isInitial a) :
  isInitial (b ↓∩ a) := by
  unfold isInitial
  intros x hx y hy
  simp at *
  exact (ha x hx y hy)

def isInitialInside (a b : Set α) := a ⊆ b ∧ isInitial (b ↓∩ a)
def isFinalInside (a b : Set α) := a ⊆ b ∧ isFinal (b ↓∩ a)

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
  unfold isInitial
  intros x hx y hy
  simp at *
  exact ha x hx y hy
  right
  unfold isInitialInside
  constructor
  trivial
  unfold isInitial
  intros x hx y  hyx
  exact hb x hx y hyx

def iso_to_initial (g : α ≃o β) : α ≼i β :=
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

instance : Coe (α ≃o β) (α ≼i β) :=
  ⟨iso_to_initial⟩

def iso_to_final (g : α ≃o β) : α ≼f β :=
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

instance : Coe (α ≃o β) (α ≼f β) :=
  ⟨iso_to_final⟩
