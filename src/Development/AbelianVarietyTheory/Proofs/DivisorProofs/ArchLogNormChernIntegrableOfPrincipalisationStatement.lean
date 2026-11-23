module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensityPullbackWeightInLiftedChartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartPreimageOfFiniteLiftedChartCoveringStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleChartCoveringComplexPointsStatement
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnLogNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableRegularVariety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalisationGenericSmoothCover
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegrableOnDescendGenericallyFinite

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernDescend

theorem chernIntegrableOn_descend : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (ρ : Y' ⟶ Y), IsArithVar (ρ ≫ q) e → ρ (genericPoint Y') = genericPoint Y → ρ.residueDegree (genericPoint Y') ≠ 0 → ∀ (N : HermLB q) (σ : k →+* ℂ) (U : Y.Opens) (f : CxPts q σ → ℝ), ContinuousOn f (ptsIn q σ U) → ((N.restr ρ).φ σ).ChernIntegrableOn e (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ U)) (fun y => f (PtsOver.map ρ rfl _ y)) → (N.φ σ).ChernIntegrableOn e (ptsIn q σ U) f := by
  intro k _ Y _ q e hY Y' _ ρ hY' hη hδ N σ U f hf hint
  obtain ⟨V, hVη, hV⟩ := GlobalTheory.T.exists_open_etaleChart_covering_complexPoints hY hY' ρ rfl hη hδ
  obtain ⟨hcard, hchart, hlift⟩ := hV σ
  have hFm : Measurable (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ)) :=
    (PtsOver.continuous_map _ _ _).measurable
  have hpre : ∀ W : Y.Opens, PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' ptsIn q σ W =
      ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ W) := by
    intro W
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have hUm : MeasurableSet (ptsIn q σ U) := (isOpen_ptsIn U).measurableSet
  have hVm : MeasurableSet (ptsIn q σ V) := (isOpen_ptsIn V).measurableSet
  have h0 : ∀ ε : ℤˣ, (N.φ σ).chernPart e ε (ptsIn q σ V)ᶜ = 0 := by
    intro ε
    have h := GlobalTheory.T.chernPart_over_properClosed_eq_zero hY ((V : Y.Opens) : Set Y)ᶜ V.isOpen.isClosed_compl (by simp [hVη]) σ
      (N.φ σ) ε
    convert h using 2
    ext y
    simp [mem_ptsIn]
  have hmeas : ∀ ε : ℤˣ, (ρ.residueDegree (genericPoint Y') : ℝ≥0∞) •
      ((N.φ σ).chernPart e ε).restrict (ptsIn q σ U) =
      Measure.map (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ))
        ((((N.φ σ).pull ρ rfl).chernPart e ε).restrict
          (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' (ptsIn q σ U ∩ ptsIn q σ V))) := by
    intro ε
    ext A hA
    rw [Measure.smul_apply, Measure.restrict_apply hA, Measure.map_apply hFm hA,
      Measure.restrict_apply (hFm hA), ← Set.preimage_inter,
      GlobalTheory.T.chernPart_preimage_of_finite_liftedChartCovering hY hY' ρ rfl (N.φ σ) (N.cInf σ) ε (ptsIn q σ V) (isOpen_ptsIn V) _ hcard hchart
        hlift (fun c c' hc w hw => GlobalTheory.T.chernDensity_pullbackWeight_in_liftedChart ρ rfl (N.φ σ) (N.cInf σ) c c' hc w hw) _
        (hA.inter (hUm.inter hVm)) (fun x hx => hx.2.2), smul_eq_mul, ← Set.inter_assoc,
      measure_inter_conull (h0 ε)]
  have hδ1 : (1 : ℝ≥0∞) ≤ (ρ.residueDegree (genericPoint Y') : ℝ≥0∞) :=
    Nat.one_le_cast.2 (Nat.pos_of_ne_zero hδ)
  have key : ∀ ε : ℤˣ, IntegrableOn (fun y => f (PtsOver.map ρ rfl _ y))
      (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ U)) (((N.φ σ).pull ρ rfl).chernPart e ε) →
      IntegrableOn f (ptsIn q σ U) ((N.φ σ).chernPart e ε) := by
    intro ε h
    refine ⟨hf.aestronglyMeasurable hUm, ?_⟩
    have h1 := h.2
    unfold HasFiniteIntegral at h1 ⊢
    refine lt_of_le_of_lt ?_ h1
    calc ∫⁻ y, ‖f y‖ₑ ∂((N.φ σ).chernPart e ε).restrict (ptsIn q σ U)
        ≤ (ρ.residueDegree (genericPoint Y') : ℝ≥0∞) *
          ∫⁻ y, ‖f y‖ₑ ∂((N.φ σ).chernPart e ε).restrict (ptsIn q σ U) :=
          le_mul_of_one_le_left' hδ1
      _ = ∫⁻ y, ‖f y‖ₑ ∂Measure.map (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ))
          ((((N.φ σ).pull ρ rfl).chernPart e ε).restrict
            (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' (ptsIn q σ U ∩ ptsIn q σ V))) := by
          rw [← hmeas ε, lintegral_smul_measure, smul_eq_mul]
      _ ≤ ∫⁻ z, ‖f (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) z)‖ₑ
          ∂((((N.φ σ).pull ρ rfl).chernPart e ε).restrict
            (PtsOver.map ρ (rfl : ρ ≫ q = ρ ≫ q) (spMap σ) ⁻¹' (ptsIn q σ U ∩ ptsIn q σ V))) :=
          lintegral_map_le _ hFm.aemeasurable
      _ ≤ _ := by
          refine lintegral_mono' (Measure.restrict_mono ?_ le_rfl) le_rfl
          rw [← hpre U]
          exact Set.preimage_mono Set.inter_subset_left
  exact ⟨key 1 hint.1, key (-1) hint.2⟩

end GlobalTheory.ChernDescend

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegrableOnDescendGenericallyFiniteStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

theorem _root_.GlobalTheory.T.chernIntegrableOn_descend_genericallyFinite : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (ρ : Y' ⟶ Y), IsArithVar (ρ ≫ q) e → ρ (genericPoint Y') = genericPoint Y → ρ.residueDegree (genericPoint Y') ≠ 0 → ∀ (N : HermLB q) (σ : k →+* ℂ) (U : Y.Opens) (f : CxPts q σ → ℝ), ContinuousOn f (ptsIn q σ U) → ((N.restr ρ).φ σ).ChernIntegrableOn e (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ U)) (fun y => f (PtsOver.map ρ rfl _ y)) → (N.φ σ).ChernIntegrableOn e (ptsIn q σ U) f := by
  first | exact @GlobalTheory.ChernDescend.chernIntegrableOn_descend | exact GlobalTheory.ChernDescend.chernIntegrableOn_descend | (intros; apply GlobalTheory.ChernDescend.chernIntegrableOn_descend <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormRationalSectionArchIntegrableStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

theorem _root_.GlobalTheory.T.logNorm_rationalSection_archIntegrable : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → GenSmooth p D → ∀ (M N : HermLB p) {r : N.B.ι → X.functionFieldˣ} (hr : IsRatSec N.B r), M.ArchIntegrable N D hr := by
  intro k _ X _ p D hX hs M N r hr σ
  have := hX.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  obtain ⟨R⟩ := hs σ
  have hσ : Function.Injective σ := ChernNull.injective_of_arithVar hX σ
  have key (ε : ℤˣ) : IntegrableOn (logNorm (N.φ σ) r) (offSupp p σ (N.div hr))
      ((M.φ σ).chernPart D ε) := by
    have h (y : CxPts p σ) : ∃ O ∈ 𝓝 y, IntegrableOn (logNorm (N.φ σ) r)
        (offSupp p σ (N.div hr) ∩ O) ((M.φ σ).chernPart D ε) :=
      have ⟨_, hi⟩ := R.cover y
      LogNormInt.exists_integrableOn hσ (M.cInf σ) (N.cInf σ) hr ε _ hi
    choose O hO hint using h
    obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover O fun y _ => hO y
    refine ((integrableOn_finset_iUnion (s := t)).2 fun y _ => hint y).mono_set fun z hz => ?_
    obtain ⟨y, hy, hz'⟩ := mem_iUnion₂.1 (ht (mem_univ z))
    exact mem_iUnion₂.2 ⟨y, hy, hz, hz'⟩
  exact ⟨key 1, key (-1)⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrable

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchIntGenSmooth

open Set

theorem archIntegrable : Published.Principalisation → ∀ (k : Type) [CommRing k] (Y : Scheme.{0})
    [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∀ (M N : HermLB q)
    (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.ArchIntegrable M e hr := by
  intro hP k _ Y _ q e hY M N r hr σ
  obtain ⟨Y', ρ, _, hcov, hgs⟩ := GlobalTheory.GenSmoothCover.exists_isCov_genSmooth hP k Y q e hY
  have hη : ρ (genericPoint Y') ⤳ genericPoint Y := hcov.2.1 ▸ specializes_rfl
  have hr' := MultPull.isRatSec_pull_map ρ hη hr
  have hup := GlobalTheory.T.logNorm_rationalSection_archIntegrable hcov.1 hgs (N.restr ρ) (M.restr ρ) hr' σ
  have hsub : ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl) ⊆
      offSupp (ρ ≫ q) σ ((M.restr ρ).div hr') := fun y hy =>
    GlobalTheory.ArchIntAlter.mem_offSupp_pull M ρ hη hr hy
  have hm : MeasurableSet (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) :=
    (isOpen_ptsIn _).measurableSet
  have heq : EqOn (logNorm ((M.restr ρ).φ σ) fun c => Units.map
      (TrueGeo.SmallSec.fnMap ρ hη).toMonoidHom (r (c PUnit.unit)))
      (fun y => logNorm (M.φ σ) r (PtsOver.map ρ rfl _ y))
      (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) := fun y hy =>
    GlobalTheory.ArchIntAlter.logNorm_pull M ρ hη hr hy
  exact GlobalTheory.T.chernIntegrableOn_descend_genericallyFinite k Y q e hY Y' ρ hcov.1 hcov.2.1 hcov.2.2 N σ _ _
    (GlobalTheory.ArchIntAlter.continuousOn_logNorm (M.φ σ) hr (M.cInf σ))
    ⟨(hup.1.mono_set hsub).congr_fun heq hm, (hup.2.mono_set hsub).congr_fun heq hm⟩

end GlobalTheory.ArchIntGenSmooth
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchLogNormChernIntegrableOfPrincipalisation

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.ArchIntegClosing

theorem archInteg : GlobalTheory.Published.Principalisation → GlobalTheory.MixHt.ArchInteg :=
  fun hP k _ Y _ q e hY M N r hr => GlobalTheory.ArchIntGenSmooth.archIntegrable hP k Y q e hY M N r hr

end GlobalTheory.ArchIntegClosing
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchLogNormChernIntegrableOfPrincipalisationStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.archLogNormChernIntegrable_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.MixHt.ArchInteg := by
  first | exact @GlobalTheory.ArchIntegClosing.archInteg | exact GlobalTheory.ArchIntegClosing.archInteg | (intros; apply GlobalTheory.ArchIntegClosing.archInteg <;> assumption)
end
end
