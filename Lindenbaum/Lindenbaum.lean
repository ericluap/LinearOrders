import Mathlib.Init.Order.LinearOrder
import Mathlib.Order.Hom.Basic
import Mathlib.Order.InitialSeg
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.Data.Finset.Basic

noncomputable section
open Classical
open Set

universe u v

/-
Define what a final embedding is and add coerceions
-/
section FinalSeg
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
end FinalSeg

variable {α : Type u} {β : Type v} [LinearOrder α] [LinearOrder β]

variable
  (f : (@LT.lt α _) ≼i (@LT.lt β _))
  (g : (@LT.lt β _) ≼f (@LT.lt α _))

/-
Define what it means for a subset of a linear order to be an initial or final segment
-/
def isInitial (s : Set α) := ∀x ∈ s, ∀y : α, y < x → y ∈ s
def isFinal (s : Set α) := ∀x ∈ s, ∀y : α, y > x → y ∈ s

/-
Initial embedding implies its image is initial
-/
theorem image_of_initial_initial : isInitial (f '' univ) := by
  unfold isInitial
  intros x hx y hy
  rw [mem_image] at *
  obtain ⟨w, hw⟩ := hx
  cases hw with
  | intro h1 h2 =>
    rw [←h2] at hy
    have h3 := (f.init' w y hy)
    obtain ⟨a, ha⟩ := h3
    use a
    trivial

/-
Final embedding implies its image is final
-/
theorem image_of_final_final : isFinal (g '' univ) := by
  unfold isFinal
  intros x hx y hy
  rw [mem_image] at *
  obtain ⟨w, hw⟩ := hx
  cases hw with
  | intro h1 h2 =>
    rw [←h2] at hy
    have h3 := (g.final' w y hy)
    obtain ⟨a, ha⟩ := h3
    use a
    trivial

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
  have hf := (f.init' w y hy)
  obtain ⟨z, hz⟩ := hf
  simp at *
  rw [←hz] at hy
  have ord : z < w := by
    rw [←f.map_rel_iff']
    trivial
  use z
  constructor
  exact (hs w w_in_s z ord)
  trivial

/-
Final embedding maps a final segment to a final segment
-/
theorem final_maps_final_final {s : Set β} (hs : isFinal s) : isFinal (g '' s) := by
  unfold isFinal at *
  intros x hx y hy
  rw [mem_image] at *
  obtain ⟨w, hw⟩ := hx
  obtain ⟨w_in_s, fw_x⟩ := hw
  rw [←fw_x] at hy
  have hf := (g.final' w y hy)
  obtain ⟨z, hz⟩ := hf
  simp at *
  rw [←hz] at hy
  have ord : w < z := by
    rw [←g.map_rel_iff']
    trivial
  use z
  constructor
  exact (hs w w_in_s z ord)
  trivial

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
  unfold isInitial
  intros x hx y hy
  unfold isFinal at hs
  apply byContradiction
  intros hny
  simp at *
  have contra := hs y hny x hy
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

/-
Modification of the proof of Schroder-Bernstein from Mathematics in Lean book
-/
def sbAux : ℕ -> Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n) ∪ (sbAux n)

theorem sbAuxZero_subset_all : ∀ n : ℕ, sbAux f g 0 ⊆ sbAux f g n := by
  intros n
  induction' n with n hn
  trivial
  rw [subset_def]
  intros x hx
  unfold sbAux
  rw [mem_union]
  right
  rw [subset_def] at hn
  exact (hn x hx)

/-
Each sbAux is an initial segment.
We use this later to show that the union of all the sbAux is an initial segment.
-/
theorem sbAux_initial : ∀ n : ℕ, isInitial (sbAux f g n) := by
  intros n
  induction' n with n hn
  unfold sbAux
  have g_image_final : isFinal (g '' univ) := by apply image_of_final_final
  apply comp_final_initial
  trivial
  unfold sbAux
  have prev_is_initial : isInitial (f '' sbAux f g n) := by
    apply initial_maps_initial_initial
    trivial
  have initial_in_image : ∀x ∈ g '' (f '' sbAux f g n), ∀y ∈ g '' univ, y < x → y ∈ g '' (f '' sbAux f g n) := by
    intros x hx y hy hyx
    rw [mem_image] at hy
    rcases hy with ⟨a,⟨_,hz⟩⟩
    rw [←hz] at hyx
    rw [mem_image] at hx
    rcases hx with ⟨b, ⟨w,hw⟩⟩
    rw [←hw] at hyx
    have alb : a < b := by
      rw [←g.map_rel_iff']
      trivial
    unfold isInitial at prev_is_initial
    have a_in_image : a ∈ f '' sbAux f g n := prev_is_initial b w a alb
    rw [←hz]
    apply mem_image_of_mem
    trivial
  unfold isInitial
  intros x hx y hy
  rcases hx with z | z
  · rcases Classical.em (y ∈ g '' univ) with s | s
    have hs := initial_in_image x z y s hy
    rw [mem_union]
    constructor
    trivial
    simp
    right
    apply sbAuxZero_subset_all
    trivial
  · unfold isInitial at hn
    rw [mem_union]
    right
    exact (hn x z y hy)

def sbSet := ⋃ n, sbAux f g n

/-
The sbSet is an initial segment
-/
theorem sbSet_initial : isInitial (sbSet f g) := by
  unfold sbSet
  apply union_initial_initial
  apply sbAux_initial

def sbFun [Nonempty β] (x : α) : β :=
  if x ∈ sbSet f g then f x else Function.invFun g x

theorem sb_right_inv [Nonempty β] {x : α} (hx : x ∉ sbSet f g) : g (Function.invFun g x ) = x := by
  have : x ∈ g '' univ := by
    contrapose! hx
    rw [sbSet, mem_iUnion]
    use 0
    rw [sbAux, mem_diff]
    trivial
  have : ∃y, g y = x := by
    rw [mem_image] at this
    rcases this with ⟨z, _, hz'⟩
    use z
  exact Function.invFun_eq this

theorem sb_injective [Nonempty β] (hf : Function.Injective f) : Function.Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x1 x2 hxeq
  show x1 = x2
  simp only [h_def, sbFun, ←A_def] at hxeq
  by_cases xA : x1 ∈ A ∨ x2 ∈ A
  · wlog x1A : x1 ∈ A generalizing x1 x2 hxeq xA
    · symm
      apply this hxeq.symm xA.symm (xA.resolve_left x1A)
    have x2A : x2 ∈ A := by
      apply not_imp_self.mp
      intro x2nA
      rw [if_pos x1A, if_neg x2nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x1A
      have x2eq : x2 = g (f x1) := by
        rw [hxeq, sb_right_inv f g]
        apply x2nA
      rcases x1A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]
      use n + 1
      simp [sbAux]
      left
      use x1
      constructor
      trivial
      symm
      trivial
    rw [if_pos x1A, if_pos x2A] at hxeq
    apply hf at hxeq
    trivial
  push_neg at xA
  rcases xA with ⟨x1nA, x2nA⟩
  rw [if_neg x1nA, if_neg x2nA] at hxeq
  have hxeq' : g (Function.invFun g x1) = g (Function.invFun g x2) := by
    rw [hxeq]
  rw [sb_right_inv f g, sb_right_inv f g] at hxeq'
  trivial
  rw [A_def] at *
  trivial
  trivial

theorem sb_surjective [Nonempty β] (hg : Function.Injective g) : Function.Surjective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    induction n with
    | zero =>
      simp [sbAux] at hn
    | succ n hn =>
      simp [sbAux] at hn
      rcases hn with ⟨x, xmem, hx⟩
      use x
      have : x ∈ A := by
        rw [A_def, sbSet, mem_iUnion]
        exact ⟨n, xmem⟩
      simp only [h_def, sbFun, if_pos this]
      trivial
      apply hn
      trivial
  use g y
  simp [A_def] at gyA
  simp [h_def, sbFun, if_neg gyA]
  apply Function.leftInverse_invFun hg

/-
Any bijection hh that is equal to sbFun is order preserving
-/
theorem order_preserving' [Nonempty β] (hh : α ≃ β) (ht : hh = sbFun f g) :
  ∀{a b : α}, hh a < hh b ↔ a < b := by
  intros a b
  by_cases ha : a ∈ (sbSet f g)
  by_cases hb : b ∈ (sbSet f g)
  constructor
  · intros halhb
    simp at halhb
    rw [ht] at halhb
    unfold sbFun at halhb
    simp [if_pos ha, if_pos hb] at halhb
    rw [←f.map_rel_iff']
    trivial
  · intros halb
    rw [ht]
    unfold sbFun
    simp [if_pos ha, if_pos hb]
    rw [←f.map_rel_iff'] at halb
    trivial
  constructor
  · intros halhb
    unfold sbFun at halhb
    simp [ht, if_pos ha, if_neg hb] at halhb
    have := sbSet_initial f g a ha
    have : ¬ b < a := by
      intros hba
      have hq := this b hba
      contradiction
    simp at this
    rw [le_iff_lt_or_eq] at this
    rcases this with hq | hq
    trivial
    rw [hq] at ha
    contradiction
  · intros _
    rw [ht]
    unfold sbFun
    simp [if_pos ha, if_neg hb]
    have f_img_initial : isInitial (f '' sbSet f g) := by
      apply initial_maps_initial_initial
      apply sbSet_initial f g
    have fa_in_img : f a ∈ f '' sbSet f g := by
      simp
      trivial
    have gb_not_ing_img : Function.invFun g b ∉ f '' sbSet f g := by
      simp
      intros x hx hx'
      have q : (sbFun f g x = sbFun f g b) := by
        unfold sbFun
        simp [if_pos hx, if_neg hb]
        trivial
      rw [←ht] at q
      simp at q
      rw [q] at hx
      contradiction
    have : ¬Function.invFun g b < f a := by
      intros q
      have := f_img_initial (f a) fa_in_img (Function.invFun g b) q
      contradiction
    simp at this
    rw [le_iff_lt_or_eq] at this
    rcases this with hq | hq
    trivial
    rw [hq] at fa_in_img
    contradiction
  by_cases hb : b ∈ (sbSet f g)
  · constructor
    · intros halhb
      rw [ht] at halhb
      unfold sbFun at halhb
      simp [ht, if_neg ha, if_pos hb] at halhb
      have f_img_initial : isInitial (f '' sbSet f g) := by
        apply initial_maps_initial_initial
        apply sbSet_initial f g
      have fb_in_img : f b ∈ f '' sbSet f g := by
        simp
        trivial
      have := f_img_initial (f b) fb_in_img (Function.invFun g a) halhb
      have ga_not_ing_img : Function.invFun g a ∉ f '' sbSet f g := by
        simp
        intros x hx hx'
        have q : (sbFun f g x = sbFun f g a) := by
          unfold sbFun
          simp [if_pos hx, if_neg ha]
          trivial
        rw [←ht] at q
        simp at q
        rw [q] at hx
        contradiction
      contradiction
    · intros halb
      rw [ht]
      unfold sbFun
      simp [if_neg ha, if_pos hb]
      have := sbSet_initial f g b hb a halb
      contradiction
  · constructor
    · intros halhb
      rw [ht] at halhb
      unfold sbFun at halhb
      simp [if_neg ha, if_neg hb] at halhb
      have : g (Function.invFun g a) < g (Function.invFun g b) := by
        rw [←g.map_rel_iff'] at halhb
        trivial
      rw [sb_right_inv f g ha, sb_right_inv f g hb] at this
      trivial
    · intros halb
      rw [ht]
      unfold sbFun
      simp [if_neg ha, if_neg hb]
      have : g (Function.invFun g a) < g (Function.invFun g b) → (Function.invFun g a) < (Function.invFun g b) := by
        intros hg
        rw [←g.map_rel_iff']
        trivial
      apply this
      rw [sb_right_inv f g ha, sb_right_inv f g hb]
      trivial

/-
Restatement of order_preserving' with ≤ instead of <
-/
theorem order_preserving [Nonempty β] (hh : α ≃ β) (ht : hh = sbFun f g) :
  ∀{a b : α}, hh a ≤ hh b ↔ a ≤ b := by
  intros a b
  rw [le_iff_eq_or_lt, le_iff_eq_or_lt]
  constructor
  · intros z
    rcases z with z | z
    simp at z
    left
    trivial
    rw [(order_preserving' f g hh ht)] at z
    right
    trivial
  · intros z
    rcases z with z | z
    left
    simp
    trivial
    rw [←(order_preserving' f g hh ht)] at z
    right
    trivial

/-
If α and β are linear orders, f : α → β is an initial segment, g : β → α is a final segment,
then α is order isomorphic to β (aka the type of order isomorphisms is nonempty)
-/
theorem lindenbaum {α : Type u} {β : Type v}
  [LinearOrder α] [LinearOrder β]
  (f : (@LT.lt α _) ≼i (@LT.lt β _))
  (g : (@LT.lt β _) ≼f (@LT.lt α _))
: Nonempty (α ≃o β) := by
  cases' isEmpty_or_nonempty β with hβ hβ
  · have : IsEmpty α := Function.isEmpty f
    have bij := ((Equiv.equivEmpty α).trans (Equiv.equivEmpty β).symm)
    have orderbij : α ≃o β := by
      constructor
      · intros a b
        simp
      · trivial
    apply nonempty_of_exists
    use orderbij
  set h := sbFun f g with h_def
  have h_bij : Function.Bijective h := ⟨sb_injective f g f.inj', sb_surjective f g g.inj'⟩
  set h_bij' := h_bij
  rw [Function.bijective_iff_has_inverse] at h_bij
  rcases h_bij with ⟨q, ⟨left_inv, right_inv⟩⟩
  set q : α ≃ β := ⟨h, q, left_inv, right_inv⟩ with q_def
  have : q = h := by
    rw [h_def, q_def]
    simp
  have orderbij : α ≃o β := RelIso.mk q (order_preserving f g q this)
  apply nonempty_of_exists
  use orderbij
