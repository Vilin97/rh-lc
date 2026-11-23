module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingSecsOfClsEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecNonzeroOnFiniteOfGenerated
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSemipositiveWeightOfGenerated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpen
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocityDefectAddBundleSectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySectionsGeneratedBundles
import Mathlib.AlgebraicGeometry.QuasiAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratedTwistSectionNonvanishingFiniteSet

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TwistMove

theorem exists_generating_secs_tens_lbPow {F : Type} [Field F] {X : Scheme.{0}} (p : X ⟶ Sp F)
    (H : LB X) (N : ℕ) (s : Fin (N + 1) → H.Sec) (hH : H.IsLB) (hs : AbLaw.VeryAmpleBy p H s)
    (M : LB X) (hM : M.IsLB) : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ (n : ℕ) (u : Fin n → (CechPic.tens M (lbPow H m)).Sec), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  obtain ⟨t₀, ht⟩ := GlobalTheory.TwistGen.twist_generated F X p H N s hH hs M hM
  refine ⟨t₀.toNat, fun m hm => ?_⟩
  obtain ⟨n, u, hu⟩ := ht m (by omega)
  have hP : (lbPow H m).IsLB := DVR.linComb_isLB H hH _ _
  have hT : (CechPic.tens M (lbPow H m)).IsLB := isLB_tens hM hP
  have e : cls (AbLaw.tw M H m) (AbLaw.isLB_tw hM hH _) =
      cls M hM - cls (AbLaw.pw H (-(m : ℤ))) (AbLaw.isLB_pw hH _) :=
    cls_div hM (AbLaw.isLB_pw hH _) (AbLaw.isLB_tw hM hH _)
  have e' : cls (AbLaw.tw M H m) (AbLaw.isLB_tw hM hH _) = cls _ hT := by
    rw [e, GlobalTheory.AmpleStabFinite.cls_pw hH, cls_tens hM hP, cls_lbPow hH, neg_zsmul, natCast_zsmul,
      sub_neg_eq_add]
  obtain ⟨v, hv⟩ := exists_generating_secs_of_cls_eq _ _ _ _ hT e' _ u hu
  exact ⟨_, v, hv⟩

theorem exists_twist_generated_sec_nonzero : ∀ (F : Type) [Field F] [Infinite F] (X : Scheme.{0}) (p : X ⟶ Sp F), IsProjOver p → ∀ (B : LB X), B.IsLB → ∀ S : Set X, S.Finite → ∃ (A : LB X) (_ : A.IsLB) (a : A.Sec), (∃ (n : ℕ) (u : Fin n → A.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) ∧ (∃ (n : ℕ) (u : Fin n → (CechPic.tens B A).Sec), ⨆ i, nonzeroLocus (u i) = ⊤) ∧ ∀ z ∈ S, z ∈ nonzeroLocus a := by
  intro F _ _ X p hp B hB S hS
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨N, ι, hι, e⟩ := hp
  haveI := hι
  have hs := ProjSpace.veryAmpleBy_secPull_coord ι
  rw [e] at hs
  have hH : ((ProjSpace.O1 F N).pull ι).IsLB := pull_isLB (ProjSpace.O1_isLB F N) _
  obtain ⟨H, hH, s, hs⟩ : ∃ H : LB X, H.IsLB ∧ ∃ s : Fin (N + 1) → H.Sec, AbLaw.VeryAmpleBy p H s :=
    ⟨_, hH, _, hs⟩
  obtain ⟨m₁, h₁⟩ := exists_generating_secs_tens_lbPow p H N s hH hs B hB
  obtain ⟨m₂, h₂⟩ := exists_generating_secs_tens_lbPow p H N s hH hs (LB.triv X) (LB.isLB_triv X)
  obtain ⟨n₁, u₁, hu₁⟩ := h₁ (max m₁ m₂) (le_max_left _ _)
  obtain ⟨n₂, u₂, hu₂⟩ := h₂ (max m₁ m₂) (le_max_right _ _)
  have hP : (lbPow H (max m₁ m₂)).IsLB := DVR.linComb_isLB H hH _ _
  have hT : (CechPic.tens (LB.triv X) (lbPow H (max m₁ m₂))).IsLB := isLB_tens (LB.isLB_triv X) hP
  have e₂ : cls _ hT = cls _ hP := by rw [cls_tens (LB.isLB_triv X) hP, cls_triv, zero_add]
  obtain ⟨v, hv⟩ := exists_generating_secs_of_cls_eq _ _ _ _ hP e₂ _ u₂ hu₂
  obtain ⟨a, ha⟩ := exists_sec_nonzero_on_finite_of_generated F X p _ hP _ v hv S hS
  exact ⟨_, hP, a, ⟨_, v, hv⟩, ⟨_, u₁, hu₁⟩, ha⟩

end GlobalTheory.TwistMove
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratedTwistSectionNonvanishingFiniteSetStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.exists_generated_twist_section_nonvanishing_finite_set : ∀ (F : Type) [Field F] [Infinite F] (X : Scheme.{0}) (p : X ⟶ Sp F), IsProjOver p → ∀ (B : LB X), B.IsLB → ∀ S : Set X, S.Finite → ∃ (A : LB X) (_ : A.IsLB) (a : A.Sec), (∃ (n : ℕ) (u : Fin n → A.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) ∧ (∃ (n : ℕ) (u : Fin n → (CechPic.tens B A).Sec), ⨆ i, nonzeroLocus (u i) = ⊤) ∧ ∀ z ∈ S, z ∈ nonzeroLocus a := by
  first | exact @GlobalTheory.TwistMove.exists_twist_generated_sec_nonzero | exact GlobalTheory.TwistMove.exists_twist_generated_sec_nonzero | (intros; apply GlobalTheory.TwistMove.exists_twist_generated_sec_nonzero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpenStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.finite_coheight_one_notMem_of_genericPoint_mem : ∀ (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (U : X.Opens), genericPoint X ∈ U → {z : X | Order.coheight z = 1 ∧ z ∉ U}.Finite := by
  first | exact @GlobalTheory.Mix.finite_coheight_one_notMem_open | exact GlobalTheory.Mix.finite_coheight_one_notMem_open | (intros; apply GlobalTheory.Mix.finite_coheight_one_notMem_open <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocitySectionsGeneratedBundlesStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.reciprocity_sections_generatedBundles : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → (∃ (n : ℕ) (u : Fin n → M.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → (∃ (n : ℕ) (u : Fin n → N.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  first | exact @GlobalTheory.RecSec.reciprocity_sec | exact GlobalTheory.RecSec.reciprocity_sec | (intros; apply GlobalTheory.RecSec.reciprocity_sec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithReciprocityNoCommonDivisorProjective

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.Mix

theorem isNoetherian_of_locallyNoetherian_projOverField {F : Type} [Field F] {X : Scheme.{0}} [IsLocallyNoetherian X] {p : X ⟶ Sp F}
    (hproj : IsProjOver p) : AlgebraicGeometry.IsNoetherian X := by
  obtain ⟨n, i, hi, hpi⟩ := hproj
  have := isProper_str F n
  have : IsProper p := hpi ▸ inferInstance
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact {}

theorem infinite_of_ringHom_complex {F : Type} [Field F] (σ : F →+* ℂ) : Infinite F := by
  haveI : CharZero F := σ.charZero
  exact Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective

theorem reciprocity_of_generated_right (hP : GlobalTheory.Published.Principalisation) (F : Type) [Field F] (X : Scheme.{0})
    [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ) (hproj : IsProjOver p)
    (hdim : topologicalKrullDim X = (e + 1 : ℕ)) (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t)
    (hcod : ∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t)
    (hN : ∃ (n : ℕ) (u : Fin n → N.B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) :
    side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) =
      side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  haveI := isNoetherian_of_locallyNoetherian_projOverField hproj
  haveI := infinite_of_ringHom_complex σ
  let S : Set X := {genericPoint X} ∪ {z | Order.coheight z = 1 ∧ z ∉ nonzeroLocus t}
  have hS : S.Finite := (Set.finite_singleton _).union (GlobalTheory.T.finite_coheight_one_notMem_of_genericPoint_mem X (nonzeroLocus t) ht)
  obtain ⟨A, hA, a, hAgen, hMAgen, haS⟩ := GlobalTheory.T.exists_generated_twist_section_nonvanishing_finite_set F X p hproj M.B M.φ.isLB S hS
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.weight_cInf_semiPos_of_generated F X p σ A hA hAgen
  let A' : MLine p σ := ⟨A, φ, hφ⟩
  have ha : genericPoint X ∈ nonzeroLocus a := haS _ (Or.inl rfl)
  have haz : ∀ z : X, Order.coheight z = 1 → z ∉ nonzeroLocus t → z ∈ nonzeroLocus a :=
    fun z hz hzt => haS z (Or.inr ⟨hz, hzt⟩)
  obtain ⟨s₁, h₁, hloc, hadd⟩ := GlobalTheory.T.reciprocityDefect_add_bundleSection hP F X p σ e hproj hdim L M A' N s hs a ha t ht (by
    intro z hz
    by_cases hzt : z ∈ nonzeroLocus t
    · exact Or.inr hzt
    · exact Or.inl ⟨(hcod z hz).resolve_right hzt, haz z hz hzt⟩)
  have h0A := GlobalTheory.T.reciprocity_sections_generatedBundles hP F X p σ e hproj hdim L A' N a ha t ht (by
    intro z hz
    by_cases hzt : z ∈ nonzeroLocus t
    · exact Or.inr hzt
    · exact Or.inl (haz z hz hzt)) hAgen hN
  have h0MA := GlobalTheory.T.reciprocity_sections_generatedBundles hP F X p σ e hproj hdim L (M.tens A') N s₁ h₁ t ht (by
    intro z hz
    by_cases hzt : z ∈ nonzeroLocus t
    · exact Or.inr hzt
    · left
      rw [hloc]
      exact ⟨(hcod z hz).resolve_right hzt, haz z hz hzt⟩) hMAgen hN
  linarith

theorem reciprocity_of_noCommonDivisor : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP F _ X _ _ p σ e hproj hdim L M N s hs t ht hcod
  haveI := isNoetherian_of_locallyNoetherian_projOverField hproj
  haveI := infinite_of_ringHom_complex σ
  let S : Set X := {genericPoint X} ∪ {z | Order.coheight z = 1 ∧ z ∉ nonzeroLocus s}
  have hS : S.Finite := (Set.finite_singleton _).union (GlobalTheory.T.finite_coheight_one_notMem_of_genericPoint_mem X (nonzeroLocus s) hs)
  obtain ⟨A, hA, a, hAgen, hNAgen, haS⟩ := GlobalTheory.T.exists_generated_twist_section_nonvanishing_finite_set F X p hproj N.B N.φ.isLB S hS
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.weight_cInf_semiPos_of_generated F X p σ A hA hAgen
  let A' : MLine p σ := ⟨A, φ, hφ⟩
  have ha : genericPoint X ∈ nonzeroLocus a := haS _ (Or.inl rfl)
  have haz : ∀ z : X, Order.coheight z = 1 → z ∉ nonzeroLocus s → z ∈ nonzeroLocus a :=
    fun z hz hzs => haS z (Or.inr ⟨hz, hzs⟩)
  obtain ⟨t₁, h₁, hloc, hadd⟩ := GlobalTheory.T.reciprocityDefect_add_bundleSection hP F X p σ e hproj hdim L N A' M t ht a ha s hs (by
    intro z hz
    by_cases hzs : z ∈ nonzeroLocus s
    · exact Or.inr hzs
    · exact Or.inl ⟨(hcod z hz).resolve_left hzs, haz z hz hzs⟩)
  have h0A := reciprocity_of_generated_right hP F X p σ e hproj hdim L M A' s hs a ha (by
    intro z hz
    by_cases hzs : z ∈ nonzeroLocus s
    · exact Or.inl hzs
    · exact Or.inr (haz z hz hzs)) hAgen
  have h0NA := reciprocity_of_generated_right hP F X p σ e hproj hdim L M (N.tens A') s hs t₁ h₁ (by
    intro z hz
    by_cases hzs : z ∈ nonzeroLocus s
    · exact Or.inl hzs
    · right
      rw [hloc]
      exact ⟨(hcod z hz).resolve_left hzs, haz z hz hzs⟩) hNAgen
  linarith

end GlobalTheory.Mix
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithReciprocityNoCommonDivisorProjectiveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.arithReciprocity_noCommonDivisor_projective : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  first | exact @GlobalTheory.Mix.reciprocity_of_noCommonDivisor | exact GlobalTheory.Mix.reciprocity_of_noCommonDivisor | (intros; apply GlobalTheory.Mix.reciprocity_of_noCommonDivisor <;> assumption)
end
end
