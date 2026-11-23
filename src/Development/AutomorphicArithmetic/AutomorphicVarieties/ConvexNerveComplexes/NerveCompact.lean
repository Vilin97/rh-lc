module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
public import Mathlib.Analysis.Convex.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AcycCone
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AltDoubleSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
public import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Convex.PathConnected

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.BdMem

section

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.bd_mem :
    ∀ {I : Type} {S : ∀ n, Set (Fin n → I)}, FaceClosed S → ∀ (n : ℕ) (c : Ch I (n + 1)), c ∈ Finsupp.supported ℤ ℤ (S (n + 1)) → bd I n c ∈ Finsupp.supported ℤ ℤ (S n) := by
  intro I S hS n c hc
  rw [bd, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
  exact Finsupp.single_mem_supported ℤ _ (hS n t (hc (Finset.mem_coe.2 ht)) j)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AcycUnion

section

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.acyc_union :
    ∀ {I : Type} (A B : ∀ n, Set (Fin n → I)), FaceClosed A → FaceClosed B → Acyc A → Acyc B → Acyc (fun n => A n ∩ B n) → Acyc (fun n => A n ∪ B n) := by
  intro I A B hA hB hAc hBc hABc
  refine ⟨?_, ?_⟩
  · intro c hc
    rw [Finsupp.supported_union, Submodule.mem_sup] at hc
    obtain ⟨y, hy, z, hz, rfl⟩ := hc
    obtain ⟨f, hf, rfl⟩ := hAc.1 y hy
    obtain ⟨g, hg, rfl⟩ := hBc.1 z hz
    refine ⟨f + g, ?_, map_add _ _ _⟩
    rw [Finsupp.supported_union]
    exact Submodule.add_mem_sup hf hg
  · intro n c hc hcyc
    rw [Finsupp.supported_union, Submodule.mem_sup] at hc
    obtain ⟨y, hy, z, hz, rfl⟩ := hc
    rw [map_add (f := _)] at hcyc
    have hdA : bd I n y ∈ Finsupp.supported ℤ ℤ (A n) := bd_mem hA n y hy
    have hdB : bd I n y ∈ Finsupp.supported ℤ ℤ (B n) := by
      rw [eq_neg_of_add_eq_zero_left hcyc]
      exact Submodule.neg_mem _ (bd_mem hB n z hz)
    have hd : bd I n y ∈ Finsupp.supported ℤ ℤ (A n ∩ B n) := by
      rw [Finsupp.supported_inter]
      exact ⟨hdA, hdB⟩
    obtain ⟨e, he, hee⟩ : ∃ e ∈ Finsupp.supported ℤ ℤ (A (n + 1) ∩ B (n + 1)), bd I n e = bd I n y := by
      cases n with
      | zero => exact hABc.1 _ hd
      | succ m => exact hABc.2 m _ hd (bd_bd I m y)
    rw [Finsupp.supported_inter] at he
    obtain ⟨f, hf, hfe⟩ := hAc.2 n (y - e) (Submodule.sub_mem _ hy he.1) (by rw [map_sub, hee, sub_self])
    obtain ⟨g, hg, hge⟩ := hBc.2 n (z + e) (Submodule.add_mem _ hz he.2) (by rw [map_add (f := _), hee, add_comm]; exact hcyc)
    refine ⟨f + g, ?_, ?_⟩
    · rw [Finsupp.supported_union]
      exact Submodule.add_mem_sup hf hg
    · rw [map_add (f := _), hfe, hge]
      abel
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveCut

section

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.nerve_cut :
    ∀ {I F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (X : Set F) (A : I → Set F) (f : F →L[ℝ] ℝ) (u : ℝ), Convex ℝ X → (∀ i, Convex ℝ (A i)) → (nerve X A = fun n => nerve (X ∩ {x | f x ≤ u}) A n ∪ nerve (X ∩ {x | u ≤ f x}) A n) ∧ (nerve (X ∩ {x | f x = u}) A = fun n => nerve (X ∩ {x | f x ≤ u}) A n ∩ nerve (X ∩ {x | u ≤ f x}) A n) := by
  intro I F _ _ X A f u hX hA
  constructor
  · funext n
    ext t
    simp only [nerve, Set.mem_union, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨x, hx, ht⟩
      rcases le_total (f x) u with h | h
      · exact Or.inl ⟨x, ⟨hx, h⟩, ht⟩
      · exact Or.inr ⟨x, ⟨hx, h⟩, ht⟩
    · rintro (⟨x, ⟨hx, _⟩, ht⟩ | ⟨x, ⟨hx, _⟩, ht⟩) <;> exact ⟨x, hx, ht⟩
  · funext n
    ext t
    simp only [nerve, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, ⟨hx, hfx⟩, ht⟩
      exact ⟨⟨x, ⟨hx, hfx.le⟩, ht⟩, ⟨x, ⟨hx, hfx.ge⟩, ht⟩⟩
    · rintro ⟨⟨x, ⟨hx, h1⟩, ht⟩, ⟨y, ⟨hy, h2⟩, ht'⟩⟩
      rcases lt_or_ge (f x) (f y) with hd | hd
      · have hd' : 0 < f y - f x := sub_pos.2 hd
        have hne : f y - f x ≠ 0 := hd'.ne'
        have ha0 : 0 ≤ (f y - u) / (f y - f x) := div_nonneg (by linarith) hd'.le
        have hb0 : 0 ≤ (u - f x) / (f y - f x) := div_nonneg (by linarith) hd'.le
        have hab : (f y - u) / (f y - f x) + (u - f x) / (f y - f x) = 1 := by
          rw [← add_div, div_eq_one_iff_eq hne]
          ring
        refine ⟨((f y - u) / (f y - f x)) • x + ((u - f x) / (f y - f x)) • y,
          ⟨hX hx hy ha0 hb0 hab, ?_⟩, fun j => hA _ (ht j) (ht' j) ha0 hb0 hab⟩
        rw [map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        field_simp
        ring
      · exact ⟨x, ⟨hx, le_antisymm h1 (h2.trans hd)⟩, ht⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveSep

section

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.nerve_sep :
    ∀ {I F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (X : Set F) (A : I → Set F), IsCompact X → Convex ℝ X → X.Nonempty → (∀ i, IsClosed (A i)) → (∀ i, Convex ℝ (A i)) → {i | (X ∩ A i).Nonempty}.Finite → (¬ ∃ x ∈ X, ∀ i, (X ∩ A i).Nonempty → x ∈ A i) → ∃ (f : F →L[ℝ] ℝ) (u : ℝ) (i : I) (σ : Finset I), (X ∩ A i).Nonempty ∧ (∀ x ∈ X ∩ A i, f x < u) ∧ (∃ x ∈ X, ∀ j ∈ σ, x ∈ A j) ∧ (∀ x ∈ X, (∀ j ∈ σ, x ∈ A j) → u < f x) := by
  intro I F _ _ X A hXk hXc hXn hAc hAv hfin hno
  classical
  let P : Finset I → Prop := fun σ => ∃ x ∈ X, ∀ j ∈ σ, x ∈ A j
  let cands := hfin.toFinset.powerset.filter P
  have hne : cands.Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [cands, Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, true_and]
    obtain ⟨x, hx⟩ := hXn
    exact ⟨x, hx, fun j hj => absurd hj (Finset.notMem_empty j)⟩
  obtain ⟨σ, hσ, hmax⟩ := cands.exists_max_image Finset.card hne
  simp only [cands, Finset.mem_filter, Finset.mem_powerset] at hσ hmax
  obtain ⟨hσS, x0, hx0X, hx0σ⟩ := hσ
  have hex : ∃ i, (X ∩ A i).Nonempty ∧ x0 ∉ A i := by
    by_contra hc
    push_neg at hc
    exact hno ⟨x0, hx0X, hc⟩
  obtain ⟨i, hiX, hix0⟩ := hex
  have hiσ : i ∉ σ := fun h => hix0 (hx0σ i h)
  have hempty : ¬ P (insert i σ) := by
    intro hP
    have hsub : insert i σ ⊆ hfin.toFinset := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa using hiX
      · exact hσS hj
    have := hmax (insert i σ) ⟨hsub, hP⟩
    rw [Finset.card_insert_of_notMem hiσ] at this
    omega
  let C : Set F := X ∩ ⋂ j ∈ σ, A j
  have hCmem : ∀ x, x ∈ C ↔ x ∈ X ∧ ∀ j ∈ σ, x ∈ A j := by
    intro x
    simp [C, Set.mem_iInter₂]
  have hCk : IsCompact C := hXk.inter_right (isClosed_biInter fun j _ => hAc j)
  have hCv : Convex ℝ C := hXc.inter (convex_iInter₂ fun j _ => hAv j)
  have hDk : IsCompact (X ∩ A i) := hXk.inter_right (hAc i)
  have hDv : Convex ℝ (X ∩ A i) := hXc.inter (hAv i)
  have hdis : Disjoint (X ∩ A i) C := by
    rw [Set.disjoint_left]
    intro x hx hxC
    rw [hCmem] at hxC
    apply hempty
    refine ⟨x, hx.1, fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hx.2
    · exact hxC.2 j hj
  obtain ⟨f, u, v, hfu, huv, hfv⟩ :=
    geometric_hahn_banach_compact_closed hDv hDk hCv hCk.isClosed hdis
  refine ⟨f, u, i, σ, hiX, hfu, ⟨x0, hx0X, hx0σ⟩, ?_⟩
  intro x hx hxσ
  exact huv.trans (hfv x ((hCmem x).mpr ⟨hx, hxσ⟩))
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveCompact

section

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

private theorem faces_finite {I F : Type} (X : Set F) (A : I → Set F)
    (hfin : {i | (X ∩ A i).Nonempty}.Finite) :
    {σ : Finset I | ∃ x ∈ X, ∀ j ∈ σ, x ∈ A j}.Finite := by
  apply ((hfin.toFinset.powerset : Finset (Finset I)).finite_toSet).subset
  rintro σ ⟨x, hxX, hx⟩
  rw [Finset.mem_coe, Finset.mem_powerset]
  intro j hj
  rw [Set.Finite.mem_toFinset]
  exact ⟨x, hxX, hx j hj⟩

private theorem faces_lt {I F : Type} (X Y : Set F) (A : I → Set F)
    (hfin : {i | (X ∩ A i).Nonempty}.Finite) (hYX : Y ⊆ X) (σ : Finset I)
    (h1 : ∃ x ∈ X, ∀ j ∈ σ, x ∈ A j) (h2 : ¬ ∃ x ∈ Y, ∀ j ∈ σ, x ∈ A j) :
    {σ : Finset I | ∃ x ∈ Y, ∀ j ∈ σ, x ∈ A j}.ncard <
      {σ : Finset I | ∃ x ∈ X, ∀ j ∈ σ, x ∈ A j}.ncard := by
  have hsub : {σ : Finset I | ∃ x ∈ Y, ∀ j ∈ σ, x ∈ A j} ⊆ {σ : Finset I | ∃ x ∈ X, ∀ j ∈ σ, x ∈ A j} := by
    rintro τ ⟨x, hx, hxt⟩
    exact ⟨x, hYX hx, hxt⟩
  exact Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).2 ⟨σ, h1, h2⟩) (faces_finite X A hfin)

theorem UpperTheory.V.ConeExtensionAcyclic.nerve_compact :
    ∀ {I F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (X : Set F) (A : I → Set F), IsCompact X → Convex ℝ X → X.Nonempty → (∀ i, IsClosed (A i)) → (∀ i, Convex ℝ (A i)) → {i | (X ∩ A i).Nonempty}.Finite → (∀ x ∈ X, ∃ i, x ∈ A i) → Acyc (nerve X A) := by
  intro I F _ _ X A hc hcv hne hcl hca hfin hcov
  suffices key : ∀ n : ℕ, ∀ X : Set F, {σ : Finset I | ∃ x ∈ X, ∀ j ∈ σ, x ∈ A j}.ncard = n →
      IsCompact X → Convex ℝ X → X.Nonempty → {i | (X ∩ A i).Nonempty}.Finite →
      (∀ x ∈ X, ∃ i, x ∈ A i) → Acyc (nerve X A) by
    exact key _ X rfl hc hcv hne hfin hcov
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hn hc hcv hne hfin hcov
  by_cases hcone : ∃ x ∈ X, ∀ i, (X ∩ A i).Nonempty → x ∈ A i
  · obtain ⟨x, hxX, hx⟩ := hcone
    obtain ⟨a, ha⟩ := hcov x hxX
    apply acyc_cone _ a
    intro m t ht
    simp only [nerve, Set.mem_setOf_eq] at ht ⊢
    obtain ⟨y, hyX, hy⟩ := ht
    refine ⟨x, hxX, ?_⟩
    intro j
    cases j using Fin.cases with
    | zero => simpa using ha
    | succ k => simpa using hx (t k) ⟨y, hyX, hy k⟩
  · obtain ⟨f, u, i, σ, hi, hiu, hσ, hσu⟩ := nerve_sep X A hc hcv hne hcl hca hfin hcone
    have hcut := nerve_cut X A f u hcv hca
    have step : ∀ (Y : Set F) (τ : Finset I), Y ⊆ X → IsCompact Y → Convex ℝ Y → Y.Nonempty →
        (∃ x ∈ X, ∀ j ∈ τ, x ∈ A j) → (¬ ∃ x ∈ Y, ∀ j ∈ τ, x ∈ A j) → Acyc (nerve Y A) := by
      intro Y τ hYX hYc hYv hYn h1 h2
      have hfinY : {i | (Y ∩ A i).Nonempty}.Finite :=
        hfin.subset (fun k hk => Set.Nonempty.mono (Set.inter_subset_inter hYX subset_rfl) hk)
      exact ih _ ((faces_lt X Y A hfin hYX τ h1 h2).trans_eq hn) Y rfl hYc hYv hYn hfinY
        (fun x hx => hcov x (hYX hx))
    have hfc : Continuous f := f.continuous
    obtain ⟨p, hp⟩ := hi
    obtain ⟨q, hqX, hq⟩ := hσ
    have hpu : f p < u := hiu p hp
    have hqu : u < f q := hσu q hqX hq
    obtain ⟨r, hr, hfr⟩ : u ∈ f '' X :=
      hcv.isPreconnected.intermediate_value hp.1 hqX hfc.continuousOn ⟨hpu.le, hqu.le⟩
    have A1 : Acyc (nerve (X ∩ {x | f x ≤ u}) A) :=
      step _ σ Set.inter_subset_left (hc.inter_right (isClosed_le hfc continuous_const))
        (hcv.inter ((convex_Iic u).linear_preimage f.toLinearMap)) ⟨p, hp.1, hpu.le⟩ ⟨q, hqX, hq⟩
        (fun ⟨x, hx, hxs⟩ => absurd hx.2 (not_le.mpr (hσu x hx.1 hxs)))
    have A2 : Acyc (nerve (X ∩ {x | u ≤ f x}) A) :=
      step _ {i} Set.inter_subset_left (hc.inter_right (isClosed_le continuous_const hfc))
        (hcv.inter ((convex_Ici u).linear_preimage f.toLinearMap)) ⟨q, hqX, hqu.le⟩
        ⟨p, hp.1, fun j hj => (Finset.mem_singleton.mp hj) ▸ hp.2⟩
        (fun ⟨x, hx, hxs⟩ => absurd hx.2 (not_le.mpr (hiu x ⟨hx.1, hxs i (Finset.mem_singleton_self i)⟩)))
    have A0 : Acyc (nerve (X ∩ {x | f x = u}) A) :=
      step _ σ Set.inter_subset_left (hc.inter_right (isClosed_eq hfc continuous_const))
        (hcv.inter ((convex_singleton u).linear_preimage f.toLinearMap)) ⟨r, hr, hfr⟩ ⟨q, hqX, hq⟩
        (fun ⟨x, hx, hxs⟩ => (hσu x hx.1 hxs).ne' hx.2)
    rw [hcut.1]
    exact acyc_union (nerve (X ∩ {x | f x ≤ u}) A) (nerve (X ∩ {x | u ≤ f x}) A)
      (nerve_faceClosed _ _) (nerve_faceClosed _ _) A1 A2 (hcut.2 ▸ A0)
end
end
