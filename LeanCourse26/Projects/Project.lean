import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Defs.Induced
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Topology.Category.TopCat.Basic

-- 17.11.

section Def1

variable (X : Type*) [TopologicalSpace X] [DecidableEq X] (k : ℕ)

-- Λ : FiniteSubsetSpace means
--   Λ is a finite subset of X with 0 < #Λ ≤ k
-- expₖX
-- exception: exp₀X := ∅ (by lecture: rather use nonsensical than constraints)
structure FiniteSubsetSpace where
  finiteSubset : Finset X
  nonempty : k = 0 ∨ finiteSubset.Nonempty
  maxCard : finiteSubset.card ≤ k -- TODO: Notation # ?

-- TODO: Coercion?

#click_suggestions

/-def finPowerSpace := Fin k → X

instance : TopologicalSpace (finPowerSpace X k) := by
  unfold finPowerSpace
  infer_instance-/

-- if X = ∅, then expₖ∅ = ∅ and also ∅ᵏ = ∅
def Q (x : Fin k → X) : FiniteSubsetSpace X k where
  finiteSubset := Finset.univ.image x -- {x 1, ..., x k} Finset X
  nonempty := by
    by_cases hk : k > 0
    · right
      let zero : Fin k := ⟨0, hk⟩
      use x zero
      simp
    · left
      lia
  maxCard := by
    have := @Finset.card_image_le _ _ Finset.univ x _
    have := Finset.card_fin k
    lia

-- 18.11.

-- better? (also 20.11.)
omit [TopologicalSpace X] in
lemma Q_surjective : Function.Surjective (Q X k) := by
  by_cases hk : k > 0
  · intro Λ
    have hx : Λ.finiteSubset.Nonempty := Λ.nonempty.resolve_left (by lia)
    --let x₀ := hx.choose
    let x_list_short := Λ.finiteSubset.toList
    --let Λ' := x_list_short.toFinset
    --have : Λ' = Λ.finiteSubset := by
    --  exact Finset.toList_toFinset Λ.finiteSubset
    have h_x_ls_l : x_list_short.length = Λ.finiteSubset.card := by
      exact Finset.length_toList Λ.finiteSubset
    have : 0 < x_list_short.length := by calc
      x_list_short.length = Λ.finiteSubset.card := by assumption
                        _ > 0 := by exact Finset.card_pos.mpr hx
    let x₀ := x_list_short.get ⟨0, by assumption⟩
    let x_rest := List.replicate (k - x_list_short.length) x₀
    let x_list := x_list_short ++ x_rest
    have hxlk : x_list.length = k := by
      calc x_list.length
        _ = x_list_short.length + x_rest.length := by
          exact List.length_append
        _ = x_list_short.length + (k - x_list_short.length) := by
          unfold x_rest
          rw [List.length_replicate]
        _ = (k - x_list_short.length) + x_list_short.length := by lia
        _ = k := by
          refine Nat.sub_add_cancel ?_
          rw [h_x_ls_l]
          exact Λ.maxCard

    let x : Fin k → X := fun i ↦ x_list.get (Fin.cast hxlk.symm i)
    use x
    have hIm : Finset.image x Finset.univ = Λ.finiteSubset := by
      ext a
      simp
      constructor
      · intro ha
        obtain ⟨i, hi⟩ := ha
        have h1 : x i ∈ x_list := by simp [x]
        have h2 : x i ∈ x_list_short ++ x_rest := by exact h1
        have h3 : x i ∈ x_list_short := by
          simp at h2
          obtain hrs | hr := h2
          · assumption
          · have h21 : x i = x₀ := by
              unfold x_rest at hr
              simp at hr
              exact hr.right
            rw [h21, Finset.mem_toList]
            --exact hx.choose_spec
            suffices x₀ ∈ Λ.finiteSubset.toList by exact Finset.mem_toList.mp this
            unfold x₀
            apply List.get_mem
        rw [Finset.mem_toList] at h3
        rwa [← hi]
      · intro ha
        rw [← Finset.mem_toList, List.mem_iff_get] at ha
        obtain ⟨i, hai⟩ := ha
        let i' : Fin k := Fin.castLE (by
          calc Λ.finiteSubset.toList.length
            _ = Λ.finiteSubset.card := by exact Finset.length_toList Λ.finiteSubset
            _ ≤ k := Λ.maxCard
          ) i
        use i'
        unfold x x_list
        have : x_list_short.get i = a := by
          unfold x_list_short
          exact hai
        simp
        rw [List.getElem_append_left (by
          calc i'.val
            _ = i.val := by rfl
            _ < Λ.finiteSubset.toList.length := i.isLt
        )]
        simp at this
        assumption
    simp [Q, hIm]
  · replace hk : k = 0 := by lia
    intro y
    have hy : y.finiteSubset = ∅ := by
      rw [← Finset.card_eq_zero]
      have := y.maxCard
      lia
    use fun i ↦ by
      rw [hk] at i
      apply Fin.pos at i
      exfalso
      contradiction
    simp [Q]
    congr
    simp [hy, hk]


-- 17.11.

/-
unfold Function.Surjective
    intro Λ
    obtain hk0 | h_ne := Λ.nonempty
    · sorry
    · sorry
-/

end Def1

-- TODO: name
instance topFSS
  {X : Type*} [TopologicalSpace X] [DecidableEq X] {k : ℕ} :
  TopologicalSpace (FiniteSubsetSpace X k) :=
  TopologicalSpace.coinduced (Q X k) inferInstance

#check topFSS

section Def2

def inducedMap'
    {X Y : Type*} [DecidableEq X]
    {k : ℕ}
    (f : Fin k → Y → X) :
    Y → FiniteSubsetSpace X k :=
  fun y ↦ {
    finiteSubset := Finset.univ.image (fun i ↦ f i y)
    nonempty := by
      by_cases hk : k > 0
      · right
        let zero : Fin k := ⟨0, hk⟩
        use f zero y
        simp
      · left
        lia
    maxCard := by
      -- ?
      have := @Finset.card_image_le _ _ Finset.univ (fun i ↦ f i y) _
      have := Finset.card_fin k
      lia
  }

-- expₖf : expₖX → expₖY
def inducedMap
    {X Y : Type*} [DecidableEq Y]
    (k : ℕ) (f : X → Y) :
    FiniteSubsetSpace X k → FiniteSubsetSpace Y k :=
  fun Λ ↦ {
    finiteSubset := Λ.finiteSubset.image f
    nonempty := by
      by_cases hk : k > 0
      · right
        obtain hk0 | ⟨⟨x⟩⟩ := Λ.nonempty
        · lia
        · use f x
          simp
          use x
      · left
        lia
    maxCard := by
      have := @Finset.card_image_le _ _ Λ.finiteSubset f _
      have := Λ.maxCard
      lia
  }

-- TODO: they are continuous if induced by continuous

-- 18.11.

--open Classical

#click_suggestions

-- TODO: Name, type
lemma continuous_induces_continuous
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    [TopologicalSpace X] [TopologicalSpace Y]
    {k : ℕ} {f : X → Y}
    (hf : Continuous f) :
    Continuous (inducedMap k f) := by
  let expf := inducedMap k f
  let fk : (Fin k → X) → (Fin k → Y) := fun x ↦ f ∘ x
  have hfk : Continuous fk := by
    exact Pi.continuous_postcomp hf
  have hQf : (Q Y k) ∘ fk = expf ∘ (Q X k) := by
    ext x
    simp [fk, expf, inducedMap, Q, Finset.image_comp]
  constructor
  intro U hU
  have h_preims := by
    calc fk ⁻¹' ((Q Y k) ⁻¹' U)
      _ = ((Q Y k) ∘ fk) ⁻¹' U := by trivial
      _ = (expf ∘ (Q X k)) ⁻¹' U := by rw [hQf]
      _ = (Q X k) ⁻¹' (expf ⁻¹' U) := by trivial
  have : IsOpen ((Q Y k) ⁻¹' U) := by
    rw [← isOpen_coinduced]
    exact hU
  have : IsOpen (fk ⁻¹' ((Q Y k) ⁻¹' U)) := by
    apply IsOpen.preimage hfk
    assumption
  have h_preimQ : IsOpen ((Q X k) ⁻¹' (expf ⁻¹' U)) := by
    rwa [← h_preims]
  rwa [← isOpen_coinduced] at h_preimQ


-- 17.11.

end Def2

open Classical

open CategoryTheory

#click_suggestions

noncomputable def exp (k : ℕ) : TopCat ⥤ TopCat where
  obj := fun X ↦ {
    carrier := FiniteSubsetSpace X k
    str := inferInstance
  }
  map f := TopCat.ofHom {
    toFun := inducedMap k f
    continuous_toFun := continuous_induces_continuous f.hom.continuous
  }
  map_id X := by
    apply TopCat.hom_ext
    ext Λ
    simp [inducedMap]
  map_comp f g := by
    apply TopCat.hom_ext
    ext Λ
    simp [inducedMap, Finset.image_comp]

#click_suggestions

theorem fss_compact
    {X : Type*} [TopologicalSpace X]
    {k : ℕ}
    (hX : CompactSpace X) : CompactSpace (FiniteSubsetSpace X k) := by
  have : IsCompact ((Q X k) '' Set.univ) := by
    apply IsCompact.image
    exact isCompact_univ
    exact continuous_coinduced_rng
  have h_im_Q : (Q X k) '' Set.univ = Set.univ := by
    apply Set.image_univ_of_surjective
    exact Q_surjective X k
  rwa [← isCompact_univ_iff, ← h_im_Q]


variable {X : Type*} [TopologicalSpace X] {k : ℕ}
#check CompactSpace (FiniteSubsetSpace X k)

-- TODO: homotopy

-- TODO: Hausdorff
