module

public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
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
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Filtration
public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatFiniteFree
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientOfCompleteNakayama
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FreeModuleAdicCompleteSeparated
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModUniformiserCocyclesFiniteClassesLocalStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleEqAddUniformizerSmulAddCoboundary

section

@[expose] public section

open ReciprocityTheory.Gal

namespace GlobalTheory

theorem cocycle_lift_mod_uniformizer
    {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul O M] {G : Type} [Group G] [TopologicalSpace G]
    (ρ : Representation O G M) (hρ : ContAction ρ) (ϖ : O)
    (hemb : Topology.IsEmbedding (fun m : M => ϖ • m)) (s : Finset (Z1 ρ))
    (hs : ∀ c : Z1 ρ, ∃ i ∈ s, ∃ x : M, ∀ g, (c : G → M) g - (i : G → M) g - (ρ g x - x) ∈
      LinearMap.range (LinearMap.lsmul O M ϖ))
    (c : Z1 ρ) : ∃ (a : Z1 ρ → O) (c' : Z1 ρ) (x : M),
      (c : G → M) = ∑ i ∈ s, a i • (i : G → M) + ϖ • (c' : G → M) + d0 ρ x := by
  classical
  obtain ⟨i, his, x, hx⟩ := hs c
  let d : Z1 ρ := ⟨d0 ρ x, coboundaries_le_cocycles ρ hρ ⟨x, rfl⟩⟩
  let E : Z1 ρ := c - i - d
  have hE : ∀ g, (E : G → M) g = (c : G → M) g - (i : G → M) g - (ρ g x - x) := fun g => rfl
  have hx' : ∀ g, ∃ y : M, ϖ • y = (E : G → M) g := by
    intro g
    obtain ⟨y, hy⟩ := hx g
    exact ⟨y, by rw [hE]; simpa using hy⟩
  choose f hf using hx'
  have hfE : (fun g => ϖ • f g) = (E : G → M) := funext hf
  have hfc : Continuous f := by
    rw [hemb.continuous_iff]
    change Continuous (fun g => ϖ • f g)
    rw [hfE]
    exact E.2.1
  have hfco : ∀ g h, f (g * h) = f g + ρ g (f h) := by
    intro g h
    apply hemb.injective
    change ϖ • f (g * h) = ϖ • (f g + ρ g (f h))
    rw [smul_add, ← map_smul, hf, hf, hf]
    exact E.2.2 g h
  refine ⟨fun j => if j = i then 1 else 0, ⟨f, hfc, hfco⟩, x, ?_⟩
  have hsum : ∑ j ∈ s, (if j = i then (1 : O) else 0) • (j : G → M) = (i : G → M) := by
    simp only [ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq' s i (fun j => (j : G → M))]
    simp [his]
  rw [hsum]
  funext g
  have := hf g
  rw [hE] at this
  simp only [Pi.add_apply, Pi.smul_apply, amitsur_d0_apply]
  rw [this]
  abel

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleEqAddUniformizerSmulAddCoboundaryStatement

section

@[expose] public section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.cocycle_eq_add_uniformizer_smul_add_coboundary : ∀ {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] {G : Type} [Group G] [TopologicalSpace G] (ρ : Representation O G M), ContAction ρ → ∀ (ϖ : O), Topology.IsEmbedding (fun m : M => ϖ • m) → ∀ (s : Finset (Z1 ρ)), (∀ c : Z1 ρ, ∃ i ∈ s, ∃ x : M, ∀ g, (c : G → M) g - (i : G → M) g - (ρ g x - x) ∈ LinearMap.range (LinearMap.lsmul O M ϖ)) → ∀ c : Z1 ρ, ∃ (a : Z1 ρ → O) (c' : Z1 ρ) (x : M), (c : G → M) = ∑ i ∈ s, a i • (i : G → M) + ϖ • (c' : G → M) + d0 ρ x := by
  first | exact @GlobalTheory.cocycle_lift_mod_uniformizer | exact GlobalTheory.cocycle_lift_mod_uniformizer | (intros; apply GlobalTheory.cocycle_lift_mod_uniformizer <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactDvrAdicCompleteSeparatedUniformizer

section

@[expose] public section

namespace GlobalTheory

theorem compact_dvr_complete_separated : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (ϖ : O), Irreducible ϖ → (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) ∧ (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ϖ ^ n * b) → a = 0) := by
  intro O _ _ _ _ _ _ _ _ ϖ hϖ
  refine ⟨fun x => ?_, fun a ha => ?_⟩
  · set s : ℕ → O := fun n => ∑ j ∈ Finset.range n, ϖ ^ j * x j with hs
    let C : ℕ → Set O := fun n => Set.range (fun b : O => s n + ϖ ^ n * b)
    have hcpt : ∀ n, IsCompact (C n) := fun n =>
      isCompact_range (continuous_const.add (continuous_const.mul continuous_id))
    have hdec : ∀ n, C (n + 1) ⊆ C n := by
      intro n y ⟨b, hb⟩
      refine ⟨x n + ϖ * b, ?_⟩
      rw [← hb]
      simp only [hs, Finset.sum_range_succ, pow_succ]
      ring
    have hne : ∀ n, (C n).Nonempty := fun n => ⟨_, ⟨0, rfl⟩⟩
    obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hdec hne
      (hcpt 0) (fun n => (hcpt n).isClosed)
    refine ⟨a, fun n => ?_⟩
    obtain ⟨b, hb⟩ := Set.mem_iInter.mp ha n
    exact ⟨b, by rw [← hb]; simp [hs]⟩
  · have hne : Ideal.span {ϖ} ≠ (⊤ : Ideal O) := by
      rw [Ne, Ideal.span_singleton_eq_top]; exact hϖ.not_isUnit
    have h := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {ϖ}) hne
    have : a ∈ ⨅ i, (Ideal.span {ϖ}) ^ i := by
      rw [Submodule.mem_iInf]
      intro i
      obtain ⟨b, hb⟩ := ha i
      rw [Ideal.span_singleton_pow, hb]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [h] at this
    exact (Submodule.mem_bot O).mp this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactDvrAdicCompleteSeparatedUniformizerStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.compact_dvr_adic_complete_separated_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (ϖ : O), Irreducible ϖ → (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) ∧ (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ϖ ^ n * b) → a = 0) := by
  first | exact @GlobalTheory.compact_dvr_complete_separated | exact GlobalTheory.compact_dvr_complete_separated | (intros; apply GlobalTheory.compact_dvr_complete_separated <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatFiniteFreeStatement

section

@[expose] public section

open Formalism.RepresentationBoundsCohomology.LOC

theorem _root_.GlobalTheory.T.dualLat_finite_free_of_isLatticeIn : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V V' : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V'] [Module (FractionRing O) V'] [IsScalarTower O (FractionRing O) V'] (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (T : Submodule O V), IsLatticeIn T → PerfectRight b → Module.Finite O (dualLat b T) ∧ Module.Free O (dualLat b T) := by
  first | exact @GlobalTheory.dualLat_finite_free | exact GlobalTheory.dualLat_finite_free | (intros; apply GlobalTheory.dualLat_finite_free <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFreeModuleCompactAdicDvr

section

@[expose] public section

namespace GlobalTheory

open IsLocalRing

theorem finite_free_compact_adic_dvr
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] (hadic : IsAdic (IsLocalRing.maximalIdeal O))
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] [T2Space M] [Module.Free O M] [Module.Finite O M]
    (ϖ : O) (hϖ : Irreducible ϖ) :
    CompactSpace M ∧ IsOpen (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) ∧
      Topology.IsClosedEmbedding (fun m : M => ϖ • m) := by
  classical
  let b := Module.Free.chooseBasis O M
  have hΦ : Continuous (b.equivFun.symm : (Module.Free.ChooseBasisIndex O M → O) → M) := by
    have : (b.equivFun.symm : (Module.Free.ChooseBasisIndex O M → O) → M) =
        fun v => ∑ i, v i • b i := by
      funext v; simp
    rw [this]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  let H : (Module.Free.ChooseBasisIndex O M → O) ≃ₜ M :=
    hΦ.homeoOfEquivCompactToT2 (f := b.equivFun.symm.toEquiv)
  have hH : ∀ v, H v = b.equivFun.symm v := fun v => rfl
  have hcpt : CompactSpace M := by
    refine ⟨?_⟩
    have := isCompact_univ.image H.continuous
    rwa [Set.image_univ, H.surjective.range_eq] at this
  refine ⟨hcpt, ?_, ?_⟩
  · have hm : IsOpen ((IsLocalRing.maximalIdeal O : Ideal O) : Set O) := by
      have := (isAdic_iff.mp hadic).1 1
      simpa using this
    let S : Set (Module.Free.ChooseBasisIndex O M → O) :=
      ⋂ i, (fun v => v i) ⁻¹' ((IsLocalRing.maximalIdeal O : Ideal O) : Set O)
    have hS : IsOpen S := isOpen_iInter_of_finite fun i => hm.preimage (continuous_apply i)
    have heq : (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) = H '' S := by
      ext m
      simp only [SetLike.mem_coe, LinearMap.mem_range, LinearMap.lsmul_apply, S,
        Set.mem_image, Set.mem_iInter, Set.mem_preimage, hϖ.maximalIdeal_eq,
        Ideal.mem_span_singleton', hH]
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨b.equivFun (ϖ • x), fun i => ⟨b.equivFun x i, ?_⟩, by simp⟩
        simp [mul_comm]
      · rintro ⟨v, hv, rfl⟩
        choose c hc using hv
        refine ⟨b.equivFun.symm c, ?_⟩
        rw [← LinearEquiv.map_smul]
        congr 1
        funext i
        simp [← hc i, mul_comm]
    rw [heq]
    exact H.isOpenMap S hS
  · refine (continuous_const_smul ϖ).isClosedEmbedding ?_
    exact smul_right_injective M hϖ.ne_zero

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFreeModuleCompactAdicDvrStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.finite_free_module_compact_adic_dvr : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul O M] [T2Space M] [Module.Free O M] [Module.Finite O M] (ϖ : O), Irreducible ϖ → CompactSpace M ∧ IsOpen (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) ∧ Topology.IsClosedEmbedding (fun m : M => ϖ • m) := by
  first | exact @GlobalTheory.finite_free_compact_adic_dvr | exact GlobalTheory.finite_free_compact_adic_dvr | (intros; apply GlobalTheory.finite_free_compact_adic_dvr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinIsoDualLatticeOfLocalTateDuality

section

@[expose] public section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal ReciprocityTheory.ChartRestriction.T2

namespace GlobalTheory.FinIsoDualLattice

theorem finIso_of_localTateDuality (hT : Formalism.GaloisCohomology.LocalTateDualityK) : FinIso := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ hK hO i D hD
  obtain ⟨hR, hC, hT2, hA, hpm, hp0⟩ := hO
  haveI := hR; haveI := hC; haveI := hT2; haveI := hD.t2'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hFin, hFree⟩ := GlobalTheory.T.dualLat_finite_free_of_isLatticeIn D.bT D.T hD.lat hD.perf
  haveI := hFin; haveI := hFree
  obtain ⟨hcpl, hsep⟩ := GlobalTheory.T.compact_dvr_adic_complete_separated_uniformizer hA ϖ hϖ
  obtain ⟨hcT, hsT⟩ := GlobalTheory.freeModule_adicComplete_separated ϖ hcpl hsep (↥D.T')
  obtain ⟨hcomp, hopen, hemb⟩ := GlobalTheory.T.finite_free_module_compact_adic_dvr hA (M := ↥D.T') ϖ hϖ
  haveI := hcomp
  have hρ : ContAction D.ρTl' := sub_contAction D.contT' D.T' D.stT'
  have hpϖ : (p : O) ∈ Ideal.span {ϖ} := by
    rwa [← Irreducible.maximalIdeal_eq hϖ]
  obtain ⟨s, hs⟩ := GlobalTheory.T.modUniformiser_cocycles_finite_classes_local hT hK i D.ρTl' hρ ϖ hpϖ hopen
  have hl := GlobalTheory.T.cocycle_eq_add_uniformizer_smul_add_coboundary D.ρTl' hρ ϖ hemb.isEmbedding s hs
  have hd : ∀ t : ↥D.T', d0 D.ρTl' t ∈ Z1 D.ρTl' := fun t => by
    refine ⟨?_, fun g h => ?_⟩
    · exact (hρ.comp (continuous_id.prodMk continuous_const)).sub continuous_const
    · simp only [amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]; abel
  let d : ↥D.T' →ₗ[O] ↥(Z1 D.ρTl') := LinearMap.codRestrict _ (d0 D.ρTl') hd
  have hdN : LinearMap.range d ≤ (B1 D.ρTl').comap (Z1 D.ρTl').subtype := by
    rintro _ ⟨t, rfl⟩; exact ⟨t, rfl⟩
  have hZ : ∀ c : ↥(Z1 D.ρTl'), (∀ n : ℕ, ∃ z : ↥(Z1 D.ρTl'), c = ϖ ^ n • z) → c = 0 := by
    intro c hc
    apply Subtype.ext; funext g
    exact hsT _ fun n => by
      obtain ⟨z, hz⟩ := hc n
      exact ⟨(z : G → ↥D.T') g, by rw [hz]; rfl⟩
  refine GlobalTheory.finite_quotient_of_complete_nakayama ϖ hcpl hcT hZ d _ hdN s fun c => ?_
  obtain ⟨a, c', x, hx⟩ := hl c
  refine ⟨a, c', x, Subtype.ext ?_⟩
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, d, LinearMap.codRestrict_apply]
  exact hx

end GlobalTheory.FinIsoDualLattice
end
end
