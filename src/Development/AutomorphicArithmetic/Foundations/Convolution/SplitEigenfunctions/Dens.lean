module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.DetCentralSection
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.ExistsForm0
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.FormBd
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AutomorphicArithmetic.AdelicSL2.ExistsHaarRestrictRangeSl2IdeleMapEqSmulProd
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.MeasurableSetUS
public import GroundTheory.AutomorphicForms.ReductionMeasure
public import Development.AutomorphicArithmetic.AdelicSL2.EqSl2RatMulOfGl2RatSmulAdelicSL2IdeleMapEq
public import Development.AutomorphicArithmetic.AdelicSL2.ExistsGl2RatSmulMemRangeAdelicSL2IdeleMap
import Development.AutomorphicArithmetic.AdelicSL2.IsOpenEmbeddingProjection
import GroundTheory.AutomorphicForms.Reduction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.UMeasEx

-- Source module: Development.AutomorphicArithmetic.AdelicSL2.IsFundamentalDomainImageSl2DomainProdIdeles

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Pointwise Classical ENNReal NNReal

theorem UpperTheory.isFundamentalDomain_image_sl2Domain_prod_ideles :
    ∀ (M : Meas ℚ) (U : UMeas) (μ : Measure GG) [μ.IsHaarMeasure], IsFundamentalDomain Ga (pm '' (M.D ×ˢ Set.univ)) μ := by
  intro M U μ _
  haveI := M.haar
  have emb : MeasurableEmbedding pm := UpperTheory.isOpenEmbedding_projection.measurableEmbedding
  obtain ⟨c, hc⟩ := UpperTheory.exists_haar_restrict_range_sl2IdeleMap_eq_smul_prod M U μ
  have null : ∀ N : Set (G1 ℚ), M.μ N = 0 → μ (pm '' (N ×ˢ Set.univ)) = 0 := fun N hN => by
    rw [← Measure.restrict_eq_self μ (Set.image_subset_range _ _), hc, Measure.smul_apply, emb.map_apply,
      Set.preimage_image_eq _ emb.injective, Measure.prod_prod, hN, zero_mul, smul_zero]
  have lift : ∀ s : SpecialLinearGroup (Fin 2) ℚ, ∃ γ : Ga, ∀ p : G1 ℚ × US, γ • pm p = pm (ratS ℚ s * p.1, p.2) := fun s => by
    refine ⟨⟨pm (ratS ℚ s, 1), ?_⟩, fun p => Subtype.ext ?_⟩
    · refine Subgroup.mem_subgroupOf.2 ⟨SpecialLinearGroup.toGL s, Units.ext ?_⟩
      change _ = (ratS ℚ s).1 * !![1, 0; 0, (1 : A ℚ)]
      rw [← Matrix.one_fin_two, mul_one]
      rfl
    · change gl (ratS ℚ s) * dM 1 * (gl p.1 * dM p.2.1) = gl (ratS ℚ s * p.1) * dM p.2.1
      have : dM (1 : (A ℚ)ˣ) = 1 := Units.ext Matrix.one_fin_two.symm
      rw [this, mul_one, ← mul_assoc, ← map_mul]
  refine ⟨(emb.measurableSet_image.2 (M.meas.prod MeasurableSet.univ)).nullMeasurableSet, ?_, fun γ γ' hne => ?_⟩
  · have h0 := null _ (ae_iff.1 M.fund.ae_covers)
    rw [ae_iff]
    refine measure_mono_null (t := ⋃ γ : Ga, (fun x : GG => (γ : GG) * x) ⁻¹'
      (pm '' ({g | ¬ ∃ s : Gam ℚ, s • g ∈ M.D} ×ˢ Set.univ))) (fun x hx => ?_)
      (measure_iUnion_null fun γ => by rw [measure_preimage_mul]; exact h0)
    obtain ⟨γ, p, hp⟩ := UpperTheory.exists_gl2Rat_smul_mem_range_adelicSL2IdeleMap x
    refine Set.mem_iUnion.2 ⟨γ, p, ⟨?_, trivial⟩, hp⟩
    rintro ⟨⟨_, s, rfl⟩, hs⟩
    obtain ⟨δ, hδ⟩ := lift s
    exact hx ⟨δ * γ, (ratS ℚ s * p.1, p.2), ⟨hs, trivial⟩, by rw [mul_smul, ← hp, hδ]⟩
  · haveI : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
    haveI : Countable (SpecialLinearGroup (Fin 2) ℚ) := Subtype.countable
    have hN : M.μ (⋃ s : {s : SpecialLinearGroup (Fin 2) ℚ // ratS ℚ s ≠ 1},
        ((⟨ratS ℚ s.1, s.1, rfl⟩ : Gam ℚ) • M.D ∩ (1 : Gam ℚ) • M.D)) = 0 :=
      measure_iUnion_null fun s => M.fund.aedisjoint fun h => s.2 (congrArg Subtype.val h)
    refine measure_mono_null (t := (fun x : GG => ((γ'⁻¹ : Ga) : GG) * x) ⁻¹' (pm '' (_ ×ˢ Set.univ))) ?_
      (by rw [measure_preimage_mul]; exact null _ hN)
    rintro x ⟨⟨_, ⟨p, hp, rfl⟩, e⟩, ⟨_, ⟨q, hq, rfl⟩, e'⟩⟩
    have e1 : (γ'⁻¹ * γ) • pm p = pm q := by
      rw [mul_smul, inv_smul_eq_iff]
      exact e.trans e'.symm
    obtain ⟨-, s, h1, h2⟩ := UpperTheory.eq_sl2Rat_mul_of_gl2Rat_smul_adelicSL2IdeleMap_eq _ p q e1
    have hs : ratS ℚ s ≠ 1 := fun h => hne (by
      rw [h] at h2
      exact (inv_mul_eq_one.1 (Subtype.ext (Subtype.ext (h2.trans (Units.ext rfl))))).symm)
    refine ⟨q, ⟨Set.mem_iUnion.2 ⟨⟨s, hs⟩, ⟨p.1, hp.1, h1.symm⟩, by rw [one_smul]; exact hq.1⟩, trivial⟩, ?_⟩
    change pm q = γ'⁻¹ • x
    rw [eq_inv_smul_iff]
    exact e'
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.Imports

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical
open scoped ENNReal NNReal

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.fibre :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fibre := by
  intro M μ _ Φ hΦ h0
  obtain ⟨U⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.uMeasEx_of
  haveI := M.haar
  have hemb : MeasurableEmbedding pm := UpperTheory.isOpenEmbedding_projection.measurableEmbedding
  set F : Set GG := pm '' (M.D ×ˢ Set.univ) with hFdef
  have hF : IsFundamentalDomain Ga F μ := UpperTheory.isFundamentalDomain_image_sl2Domain_prod_ideles M U μ
  have hFm : MeasurableSet F := hemb.measurableSet_image.2 (M.meas.prod MeasurableSet.univ)
  have hinv : ∀ (γ : Ga) (x : GG), Φ ((γ • x : GG) : GL (Fin 2) (A ℚ)) = Φ (x : GL (Fin 2) (A ℚ)) := by
    intro γ x
    obtain ⟨r, hr⟩ : ∃ r : GL (Fin 2) ℚ, ratGL ℚ 2 r = ((γ : GG) : GL (Fin 2) (A ℚ)) := by
      obtain ⟨r, hr⟩ := γ.2
      exact ⟨r, hr⟩
    have := hΦ.left r (x : GL (Fin 2) (A ℚ))
    rw [hr] at this
    exact this
  let Φq : GroundTheory.Automorphic.RightCosetSpace Ga → ℂ := fun y => Φ ((Quotient.out y : GG) : GL (Fin 2) (A ℚ))
  have hq : ∀ x : GG, Φq (GroundTheory.Automorphic.RightCosetSpace.mk Ga x) = Φ (x : GL (Fin 2) (A ℚ)) := by
    intro x
    have h : GroundTheory.Automorphic.RightCosetSpace.mk Ga (Quotient.out (GroundTheory.Automorphic.RightCosetSpace.mk Ga x)) =
        GroundTheory.Automorphic.RightCosetSpace.mk Ga x := Quotient.out_eq _
    obtain ⟨γ, hγ⟩ := GroundTheory.Automorphic.RightCosetSpace.mk_eq_mk_iff.1 h
    change Φ ((Quotient.out (GroundTheory.Automorphic.RightCosetSpace.mk Ga x) : GG) : GL (Fin 2) (A ℚ)) = _
    rw [← hγ, hinv]
  have hqc : Continuous Φq := by
    refine (GroundTheory.Automorphic.RightCosetSpace.isOpenQuotientMap_mk (Γ := Ga)).isQuotientMap.continuous_iff.2 ?_
    have : Φq ∘ GroundTheory.Automorphic.RightCosetSpace.mk Ga = fun x : GG => Φ (x : GL (Fin 2) (A ℚ)) := funext hq
    rw [this]
    exact hΦ.cont.comp continuous_subtype_val
  change ∫ y, Φq y ∂(GroundTheory.Automorphic.RightCosetSpace.quotientMeasure Ga μ) = 0
  rw [← GroundTheory.Automorphic.RightCosetSpace.map_restrict_eq_quotientMeasure μ hF,
    integral_map (GroundTheory.Automorphic.RightCosetSpace.measurable_mk Ga).aemeasurable hqc.aestronglyMeasurable]
  simp only [hq]
  obtain ⟨c, hc⟩ := UpperTheory.exists_haar_restrict_range_sl2IdeleMap_eq_smul_prod M U μ
  have hFR : F ⊆ Set.range pm := Set.image_subset_range _ _
  have hres : μ.restrict F = (c • (M.μ.prod (us U)).map pm).restrict F := by
    rw [← hc, Measure.restrict_restrict hFm, Set.inter_eq_self_of_subset_left hFR]
  rw [hres, Measure.restrict_smul, integral_smul_nnreal_measure, hemb.setIntegral_map]
  have hpre : pm ⁻¹' F = M.D ×ˢ Set.univ := hemb.injective.preimage_image _
  have hr : (M.μ.prod (us U)).restrict (M.D ×ˢ Set.univ) = (M.μ.restrict M.D).prod (us U) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hpre, hr]
  by_cases hi : Integrable (fun x : G1 ℚ × US => Φ (pm x : GL (Fin 2) (A ℚ))) ((M.μ.restrict M.D).prod (us U))
  · rw [integral_prod_symm _ hi]
    have : ∀ t : US, ∫ g in M.D, Φ (pm (g, t) : GL (Fin 2) (A ℚ)) ∂M.μ = 0 := fun t => h0 t t.2
    simp [this]
  · rw [integral_undef hi, smul_zero]
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Dens

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical
open UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.dens :
    Dens := by
  intro M u hu hne
  obtain ⟨F, hF, he, hc⟩ := Cp.ext u hu
  have h1 : (1 : (A ℚ)ˣ) ∈ UU := ⟨rfl, fun v => by
    change Valued.v (1 : v.adicCompletion ℚ) = 1
    exact map_one _⟩
  have hF0 : F ≠ 0 := fun h => hne (funext fun g => by rw [← he g 1 h1, h]; rfl)
  obtain ⟨π, hπ, f, hf, hint⟩ := pairL Measure.haar F hF hF0 hc
  obtain ⟨hb, ht⟩ := formBd π hπ f hf
  refine ⟨π, hπ, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨B, hB⟩ := hb.bdd
  obtain ⟨B', hB'⟩ := hF.bdd
  refine hint (fibre M Measure.haar (fun x => f.1 x * F x) ⟨hb.cont.mul hF.cont, fun γ g => by rw [hb.left, hF.left],
    ⟨B * B', fun x => by rw [norm_mul]; exact mul_le_mul (hB x) (hB' x) (norm_nonneg _) ((norm_nonneg _).trans (hB x))⟩,
    fun s x => by rw [hb.cen, hF.cen]⟩ fun t htU => ?_)
  obtain ⟨f', hf', e⟩ := ht t htU
  simpa only [e, he _ t htU] using hcon f' hf'
end
end
