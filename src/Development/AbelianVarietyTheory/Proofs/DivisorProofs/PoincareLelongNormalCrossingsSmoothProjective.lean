module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralEqMongeAmpereIntegralCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
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
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableLogNormSectionMixedChernFormsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAnalyticSNCOfAlgebraicSNCSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralEqMongeAmpereIntegralCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasiRegularSeqOfIsFreeGen
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleLogSectionNormProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncClosedEqIUnionClosureCodimOnePointsStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereIntegralInvariantHomeomorphTransport

section

@[expose] public section

namespace MongeAmpereTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MaTransport

variable {e : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']

def carryPartition (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : ChartPartition A) :
    ChartPartition (tAtlas A h) where
  χ j := P.χ j ∘ h.symm
  smooth j k := by
    have e₁ : (P.χ j ∘ h.symm) ∘ ((tAtlas A h).chart k).symm = P.χ j ∘ (A.chart k).symm :=
      funext fun y => by simp [tAtlas_symm]
    rw [e₁]
    exact P.smooth j k
  nonneg j x := P.nonneg j _
  tsupport_subset j := fun x hx =>
    P.tsupport_subset j (tsupport_comp_subset_preimage (P.χ j) h.symm.continuous hx)
  sum_eq_one x := P.sum_eq_one (h.symm x)

theorem isPotential_pullback (A : FinHolAtlas e X) (h : X ≃ₜ X') {Q : LocPot X'}
    (hQ : IsPotential (tAtlas A h) Q) : IsPotential A (Q.pullback h h.continuous) := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · exact hQ.1 (h x) j
  · obtain ⟨W, hW, hyW, G, hG, hd⟩ := hQ.2 (h x) (h x') (h y) hy
    refine ⟨h ⁻¹' W, hW.preimage h.continuous, hyW, G ∘ h, fun j => ?_, fun z hz => ?_⟩
    · exact hG j
    · exact hd (h z) hz

theorem integralWith_carry (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : ChartPartition A)
    (Φ : Fin e → LocPot X') (g : X' → ℝ) :
    integralWith (tAtlas A h) (carryPartition A h P) Φ g =
      integralWith A P (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change P.χ j (h.symm (h ((A.chart j).symm y))) * g (h ((A.chart j).symm y)) * _ =
    P.χ j ((A.chart j).symm y) * g (h ((A.chart j).symm y)) * _
  rw [h.symm_apply_apply]
  rfl

theorem mInt_tAtlas (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X'] [CompactSpace X]
    [T2Space X] [CompactSpace X'] [T2Space X'] (A : FinHolAtlas e X) (h : X ≃ₜ X')
    (Φ : Fin e → LocPot X') (g : X' → ℝ) (hΦ : ∀ i, IsPotential (tAtlas A h) (Φ i))
    (hg : Continuous g) :
    mInt (tAtlas A h) Φ g = mInt A (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  obtain ⟨P⟩ := existsPartition A
  have hΨ : ∀ i, IsPotential A ((Φ i).pullback h h.continuous) :=
    fun i => isPotential_pullback A h (hΦ i)
  rw [mIntEq (tAtlas A h) (carryPartition A h P) Φ hΦ g (mIntegrableCont _ Φ hΦ g hg),
    mIntEq A P _ hΨ (g ∘ h) (mIntegrableCont A _ hΨ _ (hg.comp h.continuous)),
    integralWith_carry]

end GlobalTheory.CompanionTheory.MaTransport

end
end

end MongeAmpereTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
theorem _root_.GlobalTheory.Adopt.mongeAmpereIntegral_invariant_homeomorph_transport : ∀ (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X'] [CompactSpace X] [T2Space X] [CompactSpace X'] [T2Space X'] (A : FinHolAtlas e X) (h : X ≃ₜ X') (Φ : Fin e → LocPot X') (g : X' → ℝ), (∀ i, IsPotential (tAtlas A h) (Φ i)) → Continuous g → mInt (tAtlas A h) Φ g = mInt A (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  first | exact @MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas | exact MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas | (intros; apply MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas <;> assumption)

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicSubAtlasSmoothClosedSubscheme

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix


open GlobalTheory.Mean4O.CombForm in
theorem exists_subAtlas : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (e : ℕ) (A : FinHolAtlas (e + 1) (CxPts p σ)), IsAlgAtlas A → SmoothOfRelativeDimension e q → ∃ B : FinHolAtlas e (Set.range (ptMap π hπ σ)), HoloMap B A Subtype.val ∧ ∀ (L : Fin e → MLine p σ) (v : CxPts p σ → ℝ), Continuous v → mInt B (fun i => (L i).φ.locPot.pullback Subtype.val continuous_subtype_val) (v ∘ Subtype.val) = Mix.int (fun i => (L i).pull π hπ) (fun y => v (ptMap π hπ σ y)) := by
  intro k _ X Y p q σ hp π _ hπ e A hA hs
  have hq : IsProjOver q := by
    obtain ⟨N, i, hi, h⟩ := hp
    exact ⟨N, π ≫ i, inferInstance, by rw [Category.assoc, h, hπ]⟩
  haveI : CompactSpace (CxPts q σ) := CxPts.compactSpace σ hq
  haveI : T2Space (CxPts q σ) := CxPts.t2Space_cxPts_of_isProjOver σ hq
  haveI : SecondCountableTopology (CxPts q σ) := CxPts.secondCountableTopology_of_isProjOver σ hq
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hp
  have hc : Continuous (ptMap π hπ σ) := PtsOver.continuous_map π hπ _
  have hinj : Function.Injective (ptMap π hπ σ) := fun a b h =>
    Subtype.ext ((cancel_mono π).1 (congrArg Subtype.val h))
  have hE : IsClosedEmbedding (ptMap π hπ σ) := hc.isClosedEmbedding hinj
  let h : CxPts q σ ≃ₜ Set.range (ptMap π hπ σ) := hE.isEmbedding.toHomeomorph
  haveI : CompactSpace (Set.range (ptMap π hπ σ)) := h.compactSpace
  let A' : FinHolAtlas e (CxPts q σ) := (AnRead.all q σ e).finAtlas
  have hA' : IsAlgAtlas A' := AnRead.isAlgAtlas_finAtlas _
  have hm : HoloMap A' A (ptMap π hπ σ) := hA.holoMap hA' (f := π) fun _ => rfl
  have hB : HoloMap (tAtlas A' h) A Subtype.val := ⟨continuous_subtype_val, fun j l => hm.2 j l⟩
  refine ⟨tAtlas A' h, hB, fun L v hv => ?_⟩
  have hsm (i : Fin e) : (L i).φ.IsSmooth hA.anRead := (Weight.isCInf_iff_isSmooth _).1 (L i).cInf
  have hv' : Continuous fun y => v (ptMap π hπ σ y) := hv.comp hc
  have hP (i : Fin e) : IsPotential A' ((L i).pull π hπ).φ.locPot :=
    Weight.isPotential_locPot ((Weight.isCInf_iff_isSmooth _).1 ((L i).pull π hπ).cInf)
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact k Y q σ e A' hA' (fun i => (L i).pull π hπ) _ hv'.measurable
  rw [h₂ (h₁.2 (mIntegrableCont _ _ hP _ hv')),
    GlobalTheory.Adopt.mongeAmpereIntegral_invariant_homeomorph_transport e _ _ A' h _ _
      (fun i => isPotentialPullback A _ _ hB _ ((hsm i).isPotential hA))
      (hv.comp continuous_subtype_val)]
  exact (SameForm.mInt_eq (fun i => (hsm i).sameForm_pull hA hA' π hπ) _).symm

end GlobalTheory.Mix
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicSubAtlasSmoothClosedSubschemeStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.exists_holomorphic_subAtlas_smooth_closedSubscheme : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (e : ℕ) (A : FinHolAtlas (e + 1) (CxPts p σ)), IsAlgAtlas A → SmoothOfRelativeDimension e q → ∃ B : FinHolAtlas e (Set.range (ptMap π hπ σ)), HoloMap B A Subtype.val ∧ ∀ (L : Fin e → MLine p σ) (v : CxPts p σ → ℝ), Continuous v → mInt B (fun i => (L i).φ.locPot.pullback Subtype.val continuous_subtype_val) (v ∘ Subtype.val) = Mix.int (fun i => (L i).pull π hπ) (fun y => v (ptMap π hπ σ y)) := by
  first | exact @GlobalTheory.Mix.exists_subAtlas | exact GlobalTheory.Mix.exists_subAtlas | (intros; apply GlobalTheory.Mix.exists_subAtlas <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSncComponentClosureCharZero

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.SncComp

theorem smooth_of_regular_stalk (K : Type) [Field K] [PerfectField K] (Y : Scheme.{0}) (q : Y ⟶ Sp K)
    [LocallyOfFiniteType q] (d : ℕ)
    (h : ∀ y : Y, IsClosed ({y} : Set Y) →
      IsRegularLocalRing (Y.presheaf.stalk y) ∧ ringKrullDim (Y.presheaf.stalk y) = d) :
    SmoothOfRelativeDimension d q := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace q
  choose A _ _ j _ pt hj hq using exists_affine_chart_over q
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y (fun y => Spec (.of (A y))) j (fun y => ⟨y, pt y, hj y⟩)
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension d)
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension d) 𝒰 fun (y : Y) => ?_
  change SmoothOfRelativeDimension d (j y ≫ q)
  have hft : LocallyOfFiniteType (spMap (algebraMap K (A y))) := by
    have : LocallyOfFiniteType (j y ≫ q) := inferInstance
    rwa [hq y] at this
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have : Algebra.FiniteType K (A y) := RingHom.finiteType_algebraMap.mp hft
  rw [hq y]
  refine RegGenSmooth.smooth_of_regular K (A y) d fun m hm => ?_
  let w : Spec (.of (A y)) := (⟨m, inferInstance⟩ : PrimeSpectrum _)
  have hw : IsClosed ({w} : Set (Spec (.of (A y)))) := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm
  have hc : IsClosed ({j y w} : Set Y) := by
    have h1 := (j y).isOpenEmbedding.preimage_closedPoints
    have h2 : w ∈ (j y) ⁻¹' closedPoints Y := by rw [h1]; exact hw
    exact h2
  obtain ⟨h1, h2⟩ := h _ hc
  let e := (asIso ((j y).stalkMap w) ≪≫ Spec.stalkIso (.of _) w).commRingCatIsoToRingEquiv
  exact ⟨IsRegularLocalRing.of_ringEquiv e, (ringKrullDim_eq_of_ringEquiv e).symm.trans h2⟩

theorem smooth_component : ∀ (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (r : ℕ) (z : Fin r → X), (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → ∀ a, SmoothOfRelativeDimension e (closι (z a) ≫ p) := by
  intro F _ _ X _ p e _ hsm r z hL a
  have : Smooth p := SmoothOfRelativeDimension.smooth (e + 1) p
  have hdim := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p (e + 1) hsm
  refine smooth_of_regular_stalk F _ _ e fun y hy => ?_
  let I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z a})
  have hc : IsClosed ({closι (z a) y} : Set X) := by
    simpa using (closι (z a)).isClosedEmbedding.isClosedMap _ hy
  have hd := (ProperCut.ringKrullDim_stalk_eq p hc).trans hdim
  obtain ⟨hreg, n, t, ε, hR, hI⟩ := hL (closι (z a) y)
  have hmem : closι (z a) y ∈ Closeds.closure {z a} := by
    have := Vanishing.ι_mem_support I y
    have h := Scheme.IdealSheafData.coe_support_vanishingIdeal (Closeds.closure {z a})
    exact h.le this
  have hker : RingHom.ker ((closι (z a)).stalkMap y).hom = Ideal.span {t (ε ⟨a, hmem⟩)} :=
    (Vanishing.ker_stalkMap I y).trans (hI ⟨a, hmem⟩)
  have hm : t (ε ⟨a, hmem⟩) ∈ IsLocalRing.maximalIdeal _ := hR.1 ▸ Ideal.subset_span ⟨_, rfl⟩
  obtain ⟨h1, h2⟩ := isRegularLocalRing_quotient_of_not_mem_sq hm ((regular_params_spec t hR.1 hR.2).1 _)
  let φ := (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective ((closι (z a)).stalkMap_surjective y))
  refine ⟨IsRegularLocalRing.of_ringEquiv φ, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv φ]
  rw [hd] at h2
  generalize ringKrullDim (X.presheaf.stalk (closι (z a) y) ⧸ Ideal.span {t (ε ⟨a, hmem⟩)}) = u at h2
  induction u using WithBot.recBotCoe with
  | bot => exact absurd h2 (by rw [WithBot.bot_add]; exact WithBot.bot_ne_coe)
  | coe u =>
    induction u using ENat.recTopCoe with
    | top => exact absurd (WithBot.coe_injective h2) (ENat.top_ne_coe _)
    | coe u =>
      have : u + 1 = e + 1 := by exact_mod_cast h2
      exact_mod_cast Nat.succ_injective this

end GlobalTheory.SncComp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSncComponentClosureCharZeroStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.smooth_snc_component_closure_charZero : ∀ (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (r : ℕ) (z : Fin r → X), (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → ∀ a, SmoothOfRelativeDimension e (closι (z a) ≫ p) := by
  first | exact @GlobalTheory.SncComp.smooth_component | exact GlobalTheory.SncComp.smooth_component | (intros; apply GlobalTheory.SncComp.smooth_component <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLelongNormalCrossingsSmoothProjective

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix.PLSnc

theorem int_half {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) : Mix.int L (fun y => f y / 2) = Mix.int L f / 2 := by
  simp only [Mix.int, integral_div, sub_div]

theorem finsum_mult {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {B : LB X} (hB : B.IsLB) (s : B.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) {r : ℕ} {z : Fin r → X} (hz : Function.Injective z)
    (h : ∀ w : X, w ∉ nonzeroLocus s → Order.coheight w = 1 → ∃ a, w = z a) (g : X → ℝ) :
    ∑ᶠ w, ((divOfSec hB s hs).mult w : ℝ) * g w =
      ∑ a, ((((divOfSec hB s hs).mult (z a)).toNat : ℕ) : ℝ) * g (z a) := by
  classical
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.image z), Finset.sum_image fun a _ b _ e => hz e]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (mult_divOfSec_nonneg _)]
  · intro w hw
    have h0 : (divOfSec hB s hs).mult w ≠ 0 := fun e => hw (by simp [e])
    obtain ⟨a, rfl⟩ := h w (fun e => notMem_supp_divOfSec.2 e (CartierDiv.mem_supp_of_mult_ne_zero h0))
      (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)
    simp

theorem poincareLelong_snc : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (L : Fin e → MLine p σ) (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (nonzeroLocus s).compl) → ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), 2 * Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) = ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L u z - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
  intro F _ X _ _ p σ e hp hsm L M s hs hsnc u hu
  haveI : CharZero F := σ.charZero
  haveI := CxPts.compactSpace σ hp
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hp
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hp
  let R := AnRead.all p σ (e + 1)
  have hA := R.isAlgAtlas_finAtlas
  generalize R.finAtlas = A at hA
  obtain ⟨r, z, hinj, hco, hT, hall, hl⟩ := GlobalTheory.T.snc_closed_eq_iUnion_closure_codim_one_points F X p (e + 1) hp hsm _ hsnc
  have hS := GlobalTheory.T.isAnalyticSNC_of_algebraicSNC_section F X p σ (e + 1) hp hsm A hA M s hs r z hinj hco hT hl
  choose B hB hBint using fun a => GlobalTheory.T.exists_holomorphic_subAtlas_smooth_closedSubscheme F X (clos (z a)) p _ σ hp (closι (z a)) rfl e A hA
    (GlobalTheory.T.smooth_snc_component_closure_charZero F X p e hp hsm r z hl a)
  have pot (N : MLine p σ) : IsPotential A N.φ.locPot :=
    ((Weight.isCInf_iff_isSmooth R).1 N.cInf).isPotential hA
  have hv (y) : CInfAt (fun y => u y / 2) y :=
    ((hu y).const_mul (1 / 2)).congr (.of_forall fun z => by ring)
  have hvc : Continuous fun y => u y / 2 := continuous_iff_continuousAt.2 fun y => (hv y).continuousAt
  have key := poincareLelong A M.φ.locPot _ _ _ B (pot M)
    (M.φ.isSection_of_isAlgAtlas hA (R.secVal_mem_holSec s)) hS hB (fun y => u y / 2)
    ((hA.smooth_iff R).2 ((cInfAt_iff_smoothOn R isOpen_univ).1 fun y _ => hv y))
    (fun i => (L i).φ.locPot) fun i => pot _
  have e₁ : logNormSec M.φ.locPot (M.φ.locSec (secVal p σ s)) = M.logSec s := funext fun y => by
    rw [Weight.logNormSec_locSec, MLine.logSec]; ring
  have e₂ : Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) =
      mInt A (Fin.cons (LocPot.ofFun fun y => u y / 2) fun i => (L i).φ.locPot) (M.logSec s) := by
    rw [(GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F X p σ _ A hA _ _ (GlobalTheory.Mix.SecNorm.logSec_basic F X p σ M s).1).2
      (GlobalTheory.T.integrable_logNormSection_mixedChernForms F X p σ _ hp hsm _ M s hs)]
    refine SameForm.mInt_eq (fun i => ?_) _
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Weight.sameForm_ofFun A u
    · exact SameForm.refl _ _
  have e₃ : Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (fun y => u y / 2) =
      mInt A (Fin.cons M.φ.locPot fun i => (L i).φ.locPot) fun y => u y / 2 := by
    have h := GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F X p σ _ A hA (Fin.cons M L : Fin (e + 1) → MLine p σ) _ hvc.measurable
    rw [h.2 (h.1.2 (mIntegrableCont A _ (fun i => pot _) _ hvc))]
    congr 1
    exact funext fun i => Fin.cases rfl (fun _ => rfl) i
  have e₄ (a) : mInt (B a) (fun i => (L i).φ.locPot.pullback Subtype.val continuous_subtype_val)
      ((fun y => u y / 2) ∘ Subtype.val) = cycInt L u (z a) / 2 :=
    (hBint a L _ hvc).trans (int_half _ _)
  rw [e₁, ← e₂, ← e₃, int_half] at key
  simp only [e₄] at key
  rw [key, finsum_mult M.φ.isLB s hs hinj (fun w hw => hall w hw), mul_sub, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun a _ => by ring
  · ring

end GlobalTheory.Mix.PLSnc
end
end
