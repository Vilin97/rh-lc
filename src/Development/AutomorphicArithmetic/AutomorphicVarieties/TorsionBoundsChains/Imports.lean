module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.RingTheory.TotallySplit
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Order.CompletePartialOrder
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.Tactic.ENatToNat
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.TorsSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.L1MapDomainLeAndL1FaceDSingleLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.QuotientsEquivOfKerEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Transport

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FullEnum

section

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.fullEnum :
    ∀ (ι : Type) [Finite ι] (b : Set (ι →₀ ℤ)), LinearIndepOn ℤ id b →
      (∀ k : ι, ∃ n : ℤ, n ≠ 0 ∧ n • Finsupp.single k (1 : ℤ) ∈ Submodule.span ℤ b) →
      ∃ v : ι → (ι →₀ ℤ), LinearIndependent ℤ v ∧ Set.range v = b := by
  intro ι _ b hb hn
  have hli : LinearIndependent ℤ (fun x : b => (x : ι →₀ ℤ)) := hb
  haveI : Finite b := hli.finite
  classical
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite b
  have h1 : Fintype.card b ≤ Fintype.card ι := by
    have := hli.fintype_card_le_finrank
    rwa [Module.finrank_finsupp_self] at this
  choose n hn0 hmem using hn
  have hind : LinearIndependent ℤ (fun k : ι => n k • Finsupp.single k (1 : ℤ)) := by
    rw [linearIndependent_iff']
    intro s c hs i hi
    have := congrArg (fun f : ι →₀ ℤ => f i) hs
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
      Finsupp.coe_zero, Pi.zero_apply] at this
    rw [Finset.sum_eq_single i] at this
    · simp only [if_true, mul_one] at this
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h (hn0 i)
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd hi h
  let w : ι → Submodule.span ℤ b := fun k => ⟨n k • Finsupp.single k (1 : ℤ), hmem k⟩
  have hw : LinearIndependent ℤ w :=
    LinearIndependent.of_comp (Submodule.span ℤ b).subtype hind
  have h2 : Fintype.card ι ≤ Fintype.card b := by
    have := hw.fintype_card_le_finrank
    rw [finrank_span_set_eq_card hb, Set.toFinset_card] at this
    convert this
  let e : ι ≃ b := Fintype.equivOfCardEq (le_antisymm h2 h1)
  refine ⟨fun k => (e k : ι →₀ ℤ), hli.comp e e.injective, ?_⟩
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    exact (e k).2
  · intro hy
    exact ⟨e.symm ⟨y, hy⟩, by simp⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.DetNatAbsLeProdL1Norms

section

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.det_natAbs_le_prod_l1_norms :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ),
      M.det.natAbs ≤ ∏ i, ∑ k, (M i k).natAbs := by
  intro ι _ _ M
  have key : |M.det| ≤ ∏ i, ∑ k, |M i k| := by
    rw [← Matrix.det_transpose, Matrix.det_apply]
    let e : Equiv.Perm ι ↪ (ι → ι) := ⟨fun σ => ⇑σ, DFunLike.coe_injective⟩
    calc |∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, M.transpose (σ i) i|
        ≤ ∑ σ : Equiv.Perm ι, |Equiv.Perm.sign σ • ∏ i, M.transpose (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ σ : Equiv.Perm ι, ∏ i, |M i (σ i)| := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
            simp [h, Finset.abs_prod, Matrix.transpose_apply]
      _ = ∑ f ∈ (Finset.univ : Finset (Equiv.Perm ι)).map e, ∏ i, |M i (f i)| := by
          rw [Finset.sum_map]
          rfl
      _ ≤ ∑ f : ι → ι, ∏ i, |M i (f i)| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun f _ _ => Finset.prod_nonneg fun i _ => abs_nonneg _)
      _ = ∏ i, ∑ k, |M i k| := (Fintype.prod_sum (fun i k => |M i k|)).symm
  have h2 : ((M.det.natAbs : ℕ) : ℤ) ≤ ((∏ i, ∑ k, (M i k).natAbs : ℕ) : ℤ) := by
    push_cast
    simpa [Int.natCast_natAbs] using key
  exact_mod_cast h2
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.IndexLe

section

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.indexLe :
    ∀ (ι : Type) [Finite ι] (v : ι → (ι →₀ ℤ)) (b : ℕ), LinearIndependent ℤ v → (∀ i, l1 (v i) ≤ b) →
      CardLe ((ι →₀ ℤ) ⧸ Submodule.span ℤ (Set.range v)) (b ^ Nat.card ι) := by
  intro ι _ v b hv hb
  classical
  haveI := Fintype.ofFinite ι
  set N := Submodule.span ℤ (Set.range v)
  let bE : Module.Basis ι ℤ (ι →₀ ℤ) := Finsupp.basisSingleOne
  let bN : Module.Basis ι ℤ N := Module.Basis.span hv
  have hfin : Finite ((ι →₀ ℤ) ⧸ N) := by
    apply Submodule.finiteQuotientOfFreeOfRankEq
    rw [Module.finrank_eq_card_basis bN, Module.finrank_eq_card_basis bE]
  refine ⟨hfin, ?_⟩
  rw [← Submodule.natAbs_det_basis_change bE N bN]
  have hcoe : ((↑) ∘ bN : ι → (ι →₀ ℤ)) = v := by
    funext i
    exact congrArg Subtype.val (Module.Basis.span_apply hv i)
  rw [hcoe, Module.Basis.det_apply, ← Matrix.det_transpose]
  refine (det_natAbs_le_prod_l1_norms ι _).trans ?_
  have hrow : ∀ i, ∑ k, ((bE.toMatrix v).transpose i k).natAbs = l1 (v i) := by
    intro i
    simp only [Matrix.transpose_apply, Module.Basis.toMatrix_apply, bE, Finsupp.basisSingleOne_repr,
      LinearEquiv.refl_apply, l1]
    rw [Finsupp.sum_fintype]
    simp
  simp_rw [hrow]
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact Finset.prod_le_pow_card _ _ _ (fun i _ => hb i)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.MaxIndep

section

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.maxIndep :
    ∀ (M : Type) [AddCommGroup M] [IsAddTorsionFree M] (s t : Set M), s ⊆ t →
      LinearIndepOn ℤ id s → ∃ b : Set M, s ⊆ b ∧ b ⊆ t ∧ LinearIndepOn ℤ id b ∧
        ∀ x ∈ t, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ Submodule.span ℤ b := by
  intro M _ _ s t hst hs
  let S : Set (Set M) := {b | s ⊆ b ∧ b ⊆ t ∧ LinearIndepOn ℤ id b}
  obtain ⟨m, hsm, hmax⟩ := zorn_subset_nonempty S (by
    intro c hcS hc hne
    refine ⟨⋃₀ c, ⟨?_, ?_, ?_⟩, fun b hb => Set.subset_sUnion_of_mem hb⟩
    · obtain ⟨b, hb⟩ := hne
      exact (hcS hb).1.trans (Set.subset_sUnion_of_mem hb)
    · exact Set.sUnion_subset fun b hb => (hcS hb).2.1
    · exact linearIndepOn_sUnion_of_directed hc.directedOn fun b hb => (hcS hb).2.2)
    s ⟨subset_rfl, hst, hs⟩
  obtain ⟨-, hmt, hmi⟩ := hmax.prop
  refine ⟨m, hsm, hmt, hmi, fun x hx => ?_⟩
  by_cases hxm : x ∈ m
  · exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hxm⟩
  have hdep : ¬ LinearIndepOn ℤ id (insert x m) := by
    intro hi
    have he := hmax.eq_of_subset
      ⟨hsm.trans (Set.subset_insert _ _), Set.insert_subset hx hmt, hi⟩ (Set.subset_insert _ _)
    exact hxm (he ▸ Set.mem_insert x m)
  rw [linearIndepOn_iff] at hdep
  push_neg at hdep
  obtain ⟨l, hl, hl0, hlne⟩ := hdep
  have hl' : Finsupp.erase x l ∈ Finsupp.supported ℤ ℤ m := by
    rw [Finsupp.mem_supported] at hl ⊢
    intro y hy
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hy
    have hyx : y ≠ x := by
      rintro rfl
      exact hy (by simp)
    rw [Finsupp.erase_ne hyx] at hy
    exact (hl (Finsupp.mem_support_iff.mpr hy)).resolve_left hyx
  have hsum : l x • x + Finsupp.linearCombination ℤ id (Finsupp.erase x l) = 0 := by
    have h1 := congrArg (Finsupp.linearCombination ℤ id) (Finsupp.single_add_erase x l)
    rw [map_add (f := _), Finsupp.linearCombination_single, hl0] at h1
    simpa using h1
  have hxne : l x ≠ 0 := by
    intro h0
    apply hlne
    have he : Finsupp.erase x l = l := by
      ext y
      by_cases hy : y = x
      · subst hy
        simp [h0]
      · simp [Finsupp.erase_ne hy]
    rw [← he]
    apply (linearIndepOn_iff.mp hmi) _ hl'
    rw [h0, zero_smul, zero_add] at hsum
    exact hsum
  refine ⟨l x, hxne, ?_⟩
  have hmem : Finsupp.linearCombination ℤ id (Finsupp.erase x l) ∈ Submodule.span ℤ m := by
    have h2 := (Finsupp.mem_span_image_iff_linearCombination ℤ (v := id) (s := m)).mpr ⟨_, hl', rfl⟩
    simpa using h2
  rw [eq_neg_of_add_eq_zero_left hsum]
  exact Submodule.neg_mem _ hmem
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.CokerTors

section

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.cokerTors :
    ∀ (ι : Type) (A b : ℕ) (L : Set (ι →₀ ℤ)), CardLe ι A → 1 ≤ b → (∀ x ∈ L, l1 x ≤ b) →
      TorsLe ((ι →₀ ℤ) ⧸ Submodule.span ℤ L) (b ^ A) := by
  intro ι A b L hι hb hL
  obtain ⟨hfin, hA⟩ := hι
  haveI : IsAddTorsionFree (ι →₀ ℤ) :=
    Function.Injective.isAddTorsionFree (Finsupp.coeFnAddHom : (ι →₀ ℤ) →+ (ι → ℤ))
      DFunLike.coe_injective
  obtain ⟨b₀, -, hb₀L, hb₀i, hb₀⟩ := maxIndep (ι →₀ ℤ) ∅ L (Set.empty_subset _)
    (linearIndepOn_empty _ _)
  obtain ⟨b₁, h01, hb₁s, hb₁i, hb₁⟩ := maxIndep (ι →₀ ℤ) b₀
    (b₀ ∪ Set.range fun k : ι => Finsupp.single k (1 : ℤ)) Set.subset_union_left hb₀i
  obtain ⟨v, hv, hvr⟩ := fullEnum ι b₁ hb₁i fun k => hb₁ _ (Or.inr ⟨k, rfl⟩)
  have hshort : ∀ i, l1 (v i) ≤ b := by
    intro i
    have hi : v i ∈ b₁ := hvr ▸ Set.mem_range_self i
    rcases hb₁s hi with h | ⟨k, hk⟩
    · exact hL _ (hb₀L h)
    · rw [← hk]
      unfold l1
      rw [Finsupp.sum_single_index (by simp)]
      simpa using hb
  have hc := indexLe ι v b hv hshort
  have ht := torsSat (ι →₀ ℤ) ι L v _ hv (fun x hx => by
    obtain ⟨n, hn, hnx⟩ := hb₀ x hx
    refine ⟨n, hn, Submodule.span_mono ?_ hnx⟩
    rw [hvr]
    exact Set.subset_inter h01 hb₀L) hc
  exact ⟨ht.1, ht.2.trans (Nat.pow_le_pow_right hb hA)⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Imports

section

@[expose] public section

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.base :
    ∀ (G X Y : Type) [Group G] [MulAction G X] (M : Rep ℤ G) (e : permRep G X ⟶ M)
      (d : (Y →₀ ℤ) →ₗ[ℤ] (X →₀ ℤ)) (A b : ℕ), Function.Surjective e.hom → Function.Exact d e.hom →
      OrbLe G X A → 1 ≤ b → (∀ y, l1 (d (Finsupp.single y 1)) ≤ b) →
      TorsLe (groupHomology M 0) (b ^ A) := by
  intro G X Y _ _ M e d A b hsurj hex hA hb hd
  set S : Set (X →₀ ℤ) := Set.range (fun y => d (Finsupp.single y 1)) with hS
  have hspan : Submodule.span ℤ S = LinearMap.range d := by
    have h1 : S = d '' Set.range (fun y : Y => Finsupp.single y (1 : ℤ)) := by
      rw [hS, ← Set.range_comp]
      rfl
    rw [h1, Submodule.span_image, ← Submodule.map_top]
    congr 1
    have := (Finsupp.basisSingleOne (R := ℤ) (ι := Y)).span_eq
    rw [Finsupp.coe_basisSingleOne] at this
    exact this
  have hker : ∀ f : X →₀ ℤ, e.hom f = 0 ↔ f ∈ Submodule.span ℤ S := by
    intro f
    rw [hspan, LinearMap.mem_range]
    exact (hex f).trans Set.mem_range
  obtain ⟨φ⟩ := hZero G X M e S hsurj hker
  have hL : ∀ x ∈ Finsupp.mapDomain (Quotient.mk (MulAction.orbitRel G X)) '' S, l1 x ≤ b := by
    rintro x ⟨s, ⟨y, rfl⟩, rfl⟩
    exact (l1_mapDomain_le_and_l1_faceD_single_le.1 _ _ _ _).trans (hd y)
  have hT := cokerTors (MulAction.orbitRel.Quotient G X) A b _ hA hb hL
  exact transport.1 _ _ φ.symm _ hT
end
end
