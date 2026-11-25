import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Homotopy.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Topology.Category.TopCat.Basic

-- 17.11.

section Def1

-- TODO: switch order to k X
-- 23.11.: refactor this
--variable (X : Type*) [TopologicalSpace X] [DecidableEq X] (k : ℕ)

-- Λ : FiniteSubsetSpace means
--   Λ is a finite subset of X with 0 < #Λ ≤ k
-- expₖX
-- exception: exp₀X := ∅ (by lecture: rather use nonsensical than constraints)
structure FiniteSubsetSpace
    (k : ℕ) (X: Type*)
    --[TopologicalSpace X]
    --[DecidableEq X]
    where
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
def Q
    {k : ℕ} {X: Type*}
    --[TopologicalSpace X]
    [DecidableEq X]
    (x : Fin k → X) :
    FiniteSubsetSpace k X where
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

variable {k : ℕ} {X: Type*} [DecidableEq X]
#check (@Q k X _)

-- 18.11.

-- better? (also 20.11.)
lemma Q_surjective
    {k : ℕ} {X: Type*} [DecidableEq X] :
    Function.Surjective (@Q k X _) := by
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
  {k : ℕ} {X : Type*} [TopologicalSpace X] [DecidableEq X] :
  TopologicalSpace (FiniteSubsetSpace k X) :=
  TopologicalSpace.coinduced Q inferInstance

#check topFSS

section Def2

def inducedMap'
    {X Y : Type*} [DecidableEq X]
    {k : ℕ}
    (f : Fin k → Y → X) :
    Y → FiniteSubsetSpace k X :=
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
    FiniteSubsetSpace k X → FiniteSubsetSpace k Y :=
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
  have hQf : Q ∘ fk = expf ∘ Q := by
    ext x
    simp [fk, expf, inducedMap, Q, Finset.image_comp]
  constructor
  intro U hU
  have preimages_commute := by
    calc fk ⁻¹' (Q ⁻¹' U)
      _ = (Q ∘ fk) ⁻¹' U := by trivial
      _ = (expf ∘ Q) ⁻¹' U := by rw [hQf]
      _ = Q ⁻¹' (expf ⁻¹' U) := by trivial
  have : IsOpen (Q ⁻¹' U) := by
    rw [← isOpen_coinduced]
    exact hU
  have : IsOpen (fk ⁻¹' (Q ⁻¹' U)) := by
    apply IsOpen.preimage hfk
    assumption
  have h_preimQ : IsOpen (Q ⁻¹' (expf ⁻¹' U)) := by
    rwa [← preimages_commute]
  rwa [← isOpen_coinduced] at h_preimQ


-- 17.11.

end Def2

--open Classical

open CategoryTheory

#click_suggestions

-- push 20.11.

noncomputable def exp_obj (k : ℕ) (X : TopCat) [DecidableEq X] : TopCat where
  carrier := FiniteSubsetSpace k X
  str := inferInstance

noncomputable def exp_hom
    (k : ℕ) {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [DecidableEq X] [DecidableEq Y]
    (f : C(X, Y)) :
    C(FiniteSubsetSpace k X, FiniteSubsetSpace k Y) where
  toFun := inducedMap k f
  continuous_toFun := continuous_induces_continuous f.continuous

-- pop 20.11.

open Classical in
noncomputable def exp_functor (k : ℕ) : TopCat ⥤ TopCat where
  obj X := exp_obj k X
  map f := TopCat.ofHom (exp_hom k f.hom)
  map_id X := by
    apply TopCat.hom_ext
    ext Λ
    simp [exp_hom]
    unfold inducedMap
    simp
    congr
  map_comp f g := by
    apply TopCat.hom_ext
    ext Λ
    simp [exp_hom]
    unfold inducedMap
    simp [Finset.image_comp]
    congr

#click_suggestions

theorem fss_compact
    {X : Type*} [TopologicalSpace X] [DecidableEq X]
    {k : ℕ}
    (hX : CompactSpace X) : CompactSpace (FiniteSubsetSpace k X) := by
  have : IsCompact ((@Q k X _) '' Set.univ) := by
    apply IsCompact.image
    exact isCompact_univ
    exact continuous_coinduced_rng -- TODO: Lemma?
  have q_surjective : (@Q k X _) '' Set.univ = Set.univ := by
    apply Set.image_univ_of_surjective
    exact Q_surjective
  rwa [← isCompact_univ_iff, ← q_surjective]


--variable {X : Type*} [TopologicalSpace X] {k : ℕ}
--#check CompactSpace (FiniteSubsetSpace X k)

-- TODO: homotopy

-- TODO: Hausdorff

-- TODO: rename hypotheses

-- 21.11.

noncomputable def exp_homotopy_fun
    {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [DecidableEq Y]
    (k : ℕ)
    (H : unitInterval × X → Y) :
    unitInterval × FiniteSubsetSpace k X → FiniteSubsetSpace k Y := fun tΛ ↦ {
    finiteSubset := tΛ.2.finiteSubset.image (H.curry tΛ.1)
    nonempty := by
      by_cases hk : k > 0
      · right
        simp
        exact tΛ.2.nonempty.resolve_left (by lia)
      · left
        lia
    maxCard := by
      grw [Finset.card_image_le] -- TODO: see if grw is applicable anywhere else
      exact tΛ.2.maxCard
  }

-- TODO: "def" lemma? Here or anywhere?

noncomputable def exp_homotopy
    {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [DecidableEq X] [DecidableEq Y]
    (k : ℕ) {f g : C(X, Y)}
    (H : ContinuousMap.Homotopy f g) :
    ContinuousMap.Homotopy (exp_hom k f) (exp_hom k g) where
  toFun := exp_homotopy_fun k H
  -- TODO: the following two are the same
  map_zero_left := by
    intro Λ
    simp [exp_hom]
    unfold inducedMap
    congr
    simp [exp_homotopy_fun]
    ext x
    simp
  map_one_left := by
    intro Λ
    simp [exp_hom]
    unfold inducedMap
    congr
    simp [exp_homotopy_fun]
    ext x
    simp
  continuous_toFun := by
    -- TODO: shorthands for these functions? also for the other proof
    let H' := exp_homotopy_fun k H
    let Hk : (Fin k → (unitInterval × X)) → (Fin k → Y) := fun tx ↦ H ∘ tx
    have cont_Hk : Continuous Hk := by
      unfold Hk
      apply Pi.continuous_postcomp
      exact H.continuous
    let id_times_Q : (unitInterval × (Fin k → X)) → (unitInterval × FiniteSubsetSpace k X) := fun tx ↦ (tx.1, Q (tx.2))
    have cont_id_times_Q : Continuous id_times_Q := by
      unfold id_times_Q
      simp
      constructor
      · exact continuous_fst
      · apply Continuous.snd'
        exact continuous_coinduced_rng
    let iso : ((Fin k → unitInterval) × (Fin k → X)) → (Fin k → (unitInterval × X)) :=
      fun tx i ↦ (tx.1 i, tx.2 i)
      --fun tx ↦ Equiv.arrowProdEquivProdArrow.symm tx.1 tx.2
    have cont_iso : Continuous iso := by
      unfold iso
      rw [continuous_pi_iff]
      intro i
      rw [continuous_prodMk]
      have h1 : ∀ i : Fin k, Continuous fun tx : ((Fin k → unitInterval) × (Fin k → X)) ↦ tx.1 i := by
        rw [← continuous_pi_iff]
        exact continuous_fst
      have h2 : ∀ i : Fin k, Continuous fun tx : ((Fin k → unitInterval) × (Fin k → X)) ↦ tx.2 i := by
        rw [← continuous_pi_iff]
        exact continuous_snd
      exact ⟨h1 i, h2 i⟩
    let ids : (unitInterval × (Fin k → X)) → ((Fin k → unitInterval) × (Fin k → X)) := fun tx ↦ (fun _ ↦ tx.1, fun i ↦ tx.2 i)
    have cont_ids : Continuous ids := by
      unfold ids
      rw [continuous_prodMk]
      constructor
      · rw [continuous_pi_iff]
        intro _
        exact continuous_fst
      · exact continuous_snd
    have comm_rect : H' ∘ id_times_Q = Q ∘ Hk ∘ iso ∘ ids := by
      ext tx
      simp [Hk, iso, ids, H', id_times_Q, exp_homotopy_fun, Q]
      -- H(t)({x1,...}) = {H(t,x1),...}
      ext y
      constructor
      · intro hy
        rw [Finset.mem_image] at hy ⊢
        obtain ⟨x, ⟨hx1, hx2⟩⟩ := hy
        rw [Finset.mem_image] at hx1
        obtain ⟨i, ⟨hi', hi⟩⟩ := hx1
        use i, hi'
        simp
        rw [hi]
        simp at hx2
        exact hx2
      · intro hy
        rw [Finset.mem_image] at hy ⊢
        obtain ⟨i, ⟨hi', hi⟩⟩ := hy
        use tx.2 i
        simp
        exact hi
    rw [continuous_def]
    intro U hU
    have cont_path1 : Continuous (Q ∘ Hk ∘ iso ∘ ids) := by
      rw [← continuous_coinduced_dom]
      sorry
    have : IsOpen ((Q ∘ Hk ∘ iso ∘ ids) ⁻¹' U) := by
      exact cont_path1.isOpen_preimage U hU
    have : IsOpen ((H' ∘ id_times_Q) ⁻¹' U) := by
      rwa [comm_rect]
    have : IsOpen (id_times_Q ⁻¹' (H' ⁻¹' U)) := by
      rwa [← Set.preimage_comp]
    rw [← isOpen_coinduced] at this
    rw [show exp_homotopy_fun k H = H' by rfl]
    sorry



theorem exp_preserves_homotopy
    {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [DecidableEq X] [DecidableEq Y]
    {k : ℕ} {f g : C(X, Y)}
    (f_hom_g : ContinuousMap.Homotopic f g) :
    ContinuousMap.Homotopic (exp_hom k f) (exp_hom k g) := by
  unfold ContinuousMap.Homotopic at f_hom_g ⊢
  obtain ⟨homotopy⟩ := f_hom_g
  exact ⟨exp_homotopy k homotopy⟩

theorem fss_hausdorff
    {X : Type*} [TopologicalSpace X] [DecidableEq X]
    {k : ℕ}
    (hX : T2Space X) : T2Space (FiniteSubsetSpace k X) := by
  rw [t2_iff_nhds]
  intro S T
  contrapose
  intro hST
  simp
  rw [Filter.inf_eq_bot_iff]
  have s : X := sorry
  have hs : s ∈ S.finiteSubset := sorry
  have hs : s ∉ T.finiteSubset := sorry
  have UV (t : X) (ht : t ∈ T.finiteSubset) := by
    rw [t2_iff_nhds] at hX
    have : ¬s = t → ¬(nhds s ⊓ nhds t).NeBot := by contrapose; exact hX
    simp at this
    specialize this sorry
    exact this
  have U_f : Set X := sorry
  have V_f : Set X := sorry
  have hU : U_f ∈ nhds s := by sorry
  have hV : V_f ∈ nhdsSet T.finiteSubset := by sorry
  rw [mem_nhds_iff] at hU
  obtain ⟨U, hU⟩ := hU
  rw [mem_nhdsSet] at hV
  obtain ⟨V, hV⟩ := hV
  let U_times_X_pow : Set (Fin k → X) := {x | x ⟨0, by sorry⟩ ∈ U}
  let V_pow : Set (Fin k → X) := {x | ∀ i, x i ∈ V}
  let QU := Q '' U_times_X_pow
  let QV := Q '' V_pow
  use QU, by sorry, QV, by sorry
  apply Disjoint.inter_eq
  apply Set.disjoint_image_image
  intro x hx y hy
  have : ∀ l ∈ (Q y).finiteSubset, l ∈ V := by sorry
  have : ∃ l ∈ (Q x).finiteSubset, l ∉ V := by sorry
  have : (Q x).finiteSubset ≠ (Q y).finiteSubset := by sorry
  intro hQ
  have : (Q x).finiteSubset = (Q y).finiteSubset := by congr
  contradiction

def OrderedConfig (k : ℕ) (X : Type*) :=
  {f : Fin k → X // Function.Injective f}

instance topOC
    {k : ℕ} {X : Type*} [TopologicalSpace X] :
    TopologicalSpace (OrderedConfig k X) :=
  instTopologicalSpaceSubtype

def actPerm
    {k : ℕ} {X : Type*}
    (σ : Equiv.Perm (Fin k)) (x : OrderedConfig k X) :
    OrderedConfig k X where
  val := x.val ∘ σ
  property := by
    rw [Equiv.injective_comp]
    exact x.property

def UnorderedConfigSetoid (k : ℕ) (X : Type*) : Setoid (OrderedConfig k X) where
  r x y := ∃ σ : Equiv.Perm (Fin k), actPerm σ x = y
  iseqv := {
    refl x := by
      use Equiv.refl (Fin k)
      congr
    symm := by
      intro x y hσ
      obtain ⟨σ, hσ⟩ := hσ
      use Equiv.symm σ
      unfold actPerm at hσ ⊢
      congr 1
      obtain ⟨_⟩ := hσ
      rw [Equiv.comp_symm_eq]
    trans := by
      intro x y z hσ hτ
      obtain ⟨σ, hσ⟩ := hσ
      obtain ⟨τ, hτ⟩ := hτ
      use Equiv.trans τ σ
      unfold actPerm at hσ hτ ⊢
      congr 1
      unfold Equiv.trans
      simp
      obtain ⟨_⟩ := hσ
      obtain ⟨_⟩ := hτ
      simp
      rw [Function.comp_assoc]
  }

def UnorderedConfig (k : ℕ) (X : Type*) :=
 Quotient (UnorderedConfigSetoid k X)

instance topUC
    {k : ℕ} {X : Type*} [TopologicalSpace X] :
    TopologicalSpace (UnorderedConfig k X) :=
  instTopologicalSpaceQuotient
