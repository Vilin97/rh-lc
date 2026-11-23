module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentFundamentalDomainLayersIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnitaryOrbitActionTransitiveWithStabilizerStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Formalism.LocalRingCardinality.DataHost
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SFiniteCovolumeOneMatrixUnitriangularMeasures
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFundamentalDomainProdOfKernelImageStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralUnfoldSumTransitiveOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentMeanThetaLiftEqOrbitIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerIntegralToIntegralCoordinates

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory

theorem lowerIntegral_to_integral_coords : ∀ (X U Y : Type) [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace Y] (G : Type) [MeasurableSpace G] (ν : Measure X) (νU : Measure U) (μ : Measure Y) [SFinite νU] [SFinite μ] (i : X → G) (p : U → Y → G) (Inv : (G → G) → Prop), Measurable i → Measurable (Function.uncurry p) → ∀ (Dom : Set G), (∀ f : G → ENNReal, Measurable f → (∀ t, Inv t → ∀ n ∈ Dom, f (t n) = f n) → ∫⁻ x, f (i x) ∂ν = ∫⁻ u, ∫⁻ y, f (p u y) ∂μ ∂νU) → ∀ f : G → ℂ, Measurable f → (∀ t, Inv t → ∀ n ∈ Dom, f (t n) = f n) → Integrable (fun x => f (i x)) ν → Integrable (fun q : U × Y => f (p q.1 q.2)) (νU.prod μ) ∧ ∫ x, f (i x) ∂ν = ∫ u, ∫ y, f (p u y) ∂μ ∂νU := by
  intro X U Y _ _ _ G _ ν νU μ _ _ i p Inv hi hp Dom H f hf hinv hfi
  have hpm : Measurable (fun q : U × Y => p q.1 q.2) := hp

  have hprod : ∀ g : G → ENNReal, Measurable g → (∀ t, Inv t → ∀ n ∈ Dom, g (t n) = g n) →
      ∫⁻ x, g (i x) ∂ν = ∫⁻ q, g (p q.1 q.2) ∂(νU.prod μ) := by
    intro g hg hgi
    rw [H g hg hgi, lintegral_prod (fun q : U × Y => g (p q.1 q.2)) (hg.comp hpm).aemeasurable]
  have hint : Integrable (fun q : U × Y => f (p q.1 q.2)) (νU.prod μ) := by
    refine ⟨(hf.comp hpm).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have := hprod (fun n => ‖f n‖ₑ) hf.enorm (fun t ht n hn => by simp only [hinv t ht n hn])
    rw [← this]
    exact hfi.2
  refine ⟨hint, ?_⟩
  rw [← integral_prod _ hint]

  have hreal : ∀ g : G → ℝ, Measurable g → (∀ t, Inv t → ∀ n ∈ Dom, g (t n) = g n) →
      Integrable (fun x => g (i x)) ν → Integrable (fun q : U × Y => g (p q.1 q.2)) (νU.prod μ) →
      ∫ x, g (i x) ∂ν = ∫ q, g (p q.1 q.2) ∂(νU.prod μ) := by
    intro g hg hgi h1 h2
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h1,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part h2]
    have e1 := hprod (fun n => ENNReal.ofReal (g n)) (ENNReal.measurable_ofReal.comp hg)
      (fun t ht n hn => by simp only [hgi t ht n hn])
    have e2 := hprod (fun n => ENNReal.ofReal (- g n)) (ENNReal.measurable_ofReal.comp hg.neg)
      (fun t ht n hn => by simp only [hgi t ht n hn])
    rw [e1, e2]
  apply Complex.ext
  · have a := integral_re hfi; have b := integral_re hint
    simp only [RCLike.re_to_complex] at a b
    rw [← a, ← b]
    exact hreal (fun n => (f n).re) (Complex.measurable_re.comp hf)
      (fun t ht n hn => by simp only [hinv t ht n hn]) hfi.re hint.re
  · have a := integral_im hfi; have b := integral_im hint
    simp only [RCLike.im_to_complex] at a b
    rw [← a, ← b]
    exact hreal (fun n => (f n).im) (Complex.measurable_im.comp hf)
      (fun t ht n hn => by simp only [hinv t ht n hn]) hfi.im hint.im

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerIntegralToIntegralCoordinatesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.lowerIntegral_to_integral_coordinates : ∀ (X U Y : Type) [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace Y] (G : Type) [MeasurableSpace G] (ν : Measure X) (νU : Measure U) (μ : Measure Y) [SFinite νU] [SFinite μ] (i : X → G) (p : U → Y → G) (Inv : (G → G) → Prop), Measurable i → Measurable (Function.uncurry p) → ∀ (Dom : Set G), (∀ f : G → ENNReal, Measurable f → (∀ t, Inv t → ∀ n ∈ Dom, f (t n) = f n) → ∫⁻ x, f (i x) ∂ν = ∫⁻ u, ∫⁻ y, f (p u y) ∂μ ∂νU) → ∀ f : G → ℂ, Measurable f → (∀ t, Inv t → ∀ n ∈ Dom, f (t n) = f n) → Integrable (fun x => f (i x)) ν → Integrable (fun q : U × Y => f (p q.1 q.2)) (νU.prod μ) ∧ ∫ x, f (i x) ∂ν = ∫ u, ∫ y, f (p u y) ∂μ ∂νU := by
  first | exact @GlobalTheory.lowerIntegral_to_integral_coords | exact GlobalTheory.lowerIntegral_to_integral_coords | (intros; apply GlobalTheory.lowerIntegral_to_integral_coords <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralBaseTermUnfoldingCoordinates

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf



theorem integral_base_term_coords : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsTh ψ d W x₀ Th → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ (𝓐 : Set (flagN d)) (𝓑 : Set (GA D W)), NullMeasurableSet 𝓐 vN.ν → NullMeasurableSet 𝓑 vW.μ → (∀ f : GA D V → ENNReal, Measurable f → (∀ c, ∀ n ∈ flagN d, f (d.nC c * n) = f n) → ∫⁻ n in 𝓐, f n.1 ∂vN.ν = ∫⁻ u, ∫⁻ b in vb.𝓕, f (d.nB b * d.levi u.1) ∂vb.μ ∂vU.ν) → ∫⁻ p in 𝓐 ×ˢ 𝓑, ‖Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) x₀‖ₑ ∂(vN.ν.prod vW.μ) ≠ ⊤ → IntegrableOn (fun h => G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ)) 𝓑 vW.μ ∧ ∫ p in 𝓐 ×ˢ 𝓑, Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) x₀ ∂(vN.ν.prod vW.μ) = ∫ h in 𝓑, G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) ∂vW.μ := by
  intro D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vb vU vW x₀ Th hTh G Φ hG hΦ 𝓐 𝓑 h𝓐 h𝓑 hlay hfin
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)
  obtain ⟨hN1, hN2, hN3⟩ := vN.unit
  haveI := vW.haar
  haveI : SFinite vN.ν := inferInstance
  haveI : SFinite vW.μ := inferInstance
  obtain ⟨sb, sU⟩ := GlobalTheory.Unf.sFinite_vol D ρ V₀.rank vb vU
  haveI : IsFiniteMeasure (vb.μ.restrict vb.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, vb.covol.2.2]; exact ENNReal.one_lt_top⟩
  haveI : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  have hTL := GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS
  have hsplit : ∀ (g : GA D V) (h : GA D W), om (g, h) Φ = om (g, 1) (om (1, h) Φ) := by
    intro g h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hψ1 : ∀ x, star (ψ x) * ψ x = 1 := fun x => by
    rw [Complex.star_def, Complex.conj_mul', hω.std.1.2.1 x]; norm_num
  have hq0 : d.qS W 0 (rat x₀) = 0 := by
    simp [HypDec.qS, symplOH, symplO, hO]
  set F : flagN d × GA D W → ℂ := fun p => Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) x₀ with hFdef
  have hFm : Measurable F := by
    refine Continuous.measurable ?_
    refine ((hTh.cont.comp continuous_fst).mul (hG.2.1.comp continuous_snd)).mul ?_
    exact ((hTL Φ hΦ).2.2.2.1 x₀).comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hint : Integrable F ((vN.ν.restrict 𝓐).prod (vW.μ.restrict 𝓑)) := by
    rw [Measure.prod_restrict]
    exact ⟨hFm.aestronglyMeasurable, lt_top_iff_ne_top.2 hfin⟩
  have hpm : Measurable (Function.uncurry fun (u : UX D ρ) (b : Mx D ρ V₀.rank) => d.nB b * d.levi u.1) :=
    (d.continuous_nB.measurable.comp measurable_snd).mul
      ((d.continuous_levi.comp continuous_subtype_val).measurable.comp measurable_fst)
  have hfib : ∀ h, Integrable (fun n => F (n, h)) (vN.ν.restrict 𝓐) →
      ∫ n, F (n, h) ∂(vN.ν.restrict 𝓐) = G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) := by
    intro h hih
    classical
    have hΨ := hω.om_pres (1, h) Φ hΦ
    set f : GA D V → ℂ := (flagN d : Set (GA D V)).piecewise
      (fun g => Th g * G h * term ψ d W vS (om (g, h) Φ) x₀) 0 with hfdef
    have hfm : Measurable f := by
      refine ContinuousOn.measurable_piecewise ?_ continuousOn_const (GlobalTheory.Mem.TrueRecord.isClosed_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)).measurableSet
      refine ((continuousOn_iff_continuous_restrict.2 hTh.cont).mul continuousOn_const).mul ?_
      exact (((hTL Φ hΦ).2.2.2.1 x₀).comp (continuous_id.prodMk continuous_const)).continuousOn
    have hfF : ∀ n : flagN d, f n.1 = F (n, h) := fun n => Set.piecewise_eq_of_mem _ _ _ n.2
    have hcen : ∀ (c : skewA D ρ) (n : GA D V), n ∈ flagN d →
        term ψ d W vS (om (d.nC c * n, h) Φ) x₀ = ψ (d.qS W c (rat x₀)) * term ψ d W vS (om (n, h) Φ) x₀ := by
      intro c n hn
      have hΨ' := hω.om_pres (n, h) Φ hΦ
      have t1 := (hTL _ hΨ').1 x₀ 0 1 c
      rw [d.nB_zero, OneMemClass.coe_one, map_one, mul_one, mul_one, ← Module.End.mul_apply, ← map_mul,
        Prod.mk_mul_mk, one_mul] at t1
      rw [t1]
      simp [term]
    have hfinv : ∀ t, (fun t : GA D V → GA D V => ∃ c, t = (d.nC c * ·)) t → ∀ n ∈ (flagN d : Set (GA D V)),
        f (t n) = f n := by
      rintro t ⟨c, rfl⟩ n hn
      have hm : d.nC c * n ∈ (flagN d : Set (GA D V)) := mul_mem (d.nC_mem_NFlag c) hn
      rw [hfdef, Set.piecewise_eq_of_mem _ _ _ hm, Set.piecewise_eq_of_mem _ _ _ hn, hTh.cen c n hn, hcen c n hn]
      calc star (ψ (d.qS W c (rat x₀))) * Th n * G h * (ψ (d.qS W c (rat x₀)) * term ψ d W vS (om (n, h) Φ) x₀)
          = (star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x₀))) * (Th n * G h * term ψ d W vS (om (n, h) Φ) x₀) := by
            ring
        _ = _ := by rw [hψ1, one_mul]
    have hcoord : ∀ (u : UX D ρ) (b : Mx D ρ V₀.rank),
        f (d.nB b * d.levi u.1) = G h * flFun ψ d W vS Th (rat x₀) (om (1, h) Φ) u b := by
      intro u b
      have hm : d.nB b * d.levi u.1 ∈ (flagN d : Set (GA D V)) := mul_mem (d.nB_mem_NFlag b) (d.levi_mem_NFlag u.2)
      have t1 := (hTL _ hΨ).1 x₀ b u 0
      rw [d.nC_zero, one_mul, hq0, AddChar.map_zero_eq_one, one_mul] at t1
      rw [hfdef, Set.piecewise_eq_of_mem _ _ _ hm, hsplit, t1, flFun]
      ring
    have hlay' : ∀ g : GA D V → ENNReal, Measurable g →
        (∀ t, (fun t : GA D V → GA D V => ∃ c, t = (d.nC c * ·)) t → ∀ n ∈ (flagN d : Set (GA D V)), g (t n) = g n) →
        ∫⁻ x, g (Subtype.val x) ∂(vN.ν.restrict 𝓐) =
          ∫⁻ u, ∫⁻ y, g ((fun (u : UX D ρ) (b : Mx D ρ V₀.rank) => d.nB b * d.levi u.1) u y) ∂(vb.μ.restrict vb.𝓕) ∂vU.ν :=
      fun g hg hinv => hlay g hg fun c n hn => hinv _ ⟨c, rfl⟩ n hn
    have hih' : Integrable (fun x : flagN d => f x.1) (vN.ν.restrict 𝓐) := by
      refine hih.congr (ae_of_all _ fun n => (hfF n).symm)
    obtain ⟨-, heq⟩ := GlobalTheory.T.lowerIntegral_to_integral_coordinates (flagN d) (UX D ρ) (Mx D ρ V₀.rank) (GA D V) (vN.ν.restrict 𝓐) vU.ν
      (vb.μ.restrict vb.𝓕) Subtype.val (fun u b => d.nB b * d.levi u.1) (fun t => ∃ c, t = (d.nC c * ·))
      measurable_subtype_coe hpm (flagN d) hlay' f hfm hfinv hih'
    calc ∫ n, F (n, h) ∂(vN.ν.restrict 𝓐) = ∫ x, f x.1 ∂(vN.ν.restrict 𝓐) :=
          integral_congr_ae (ae_of_all _ fun n => (hfF n).symm)
      _ = ∫ u, ∫ b, f (d.nB b * d.levi u.1) ∂(vb.μ.restrict vb.𝓕) ∂vU.ν := heq
      _ = ∫ u, ∫ b, G h * flFun ψ d W vS Th (rat x₀) (om (1, h) Φ) u b ∂(vb.μ.restrict vb.𝓕) ∂vU.ν := by
          refine integral_congr_ae (ae_of_all _ fun u => ?_)
          exact integral_congr_ae (ae_of_all _ fun b => hcoord u b)
      _ = G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) := by
          simp only [integral_const_mul]; rfl
  have hae := hint.prod_left_ae
  have hI := hint.integral_prod_right
  have hEq : (fun h => ∫ n, F (n, h) ∂(vN.ν.restrict 𝓐)) =ᵐ[vW.μ.restrict 𝓑]
      fun h => G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) := hae.mono fun h hh => hfib h hh
  refine ⟨hI.congr hEq, ?_⟩
  rw [← Measure.prod_restrict, integral_prod_symm F hint]
  exact integral_congr_ae hEq

end GlobalTheory.Unf

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralBaseTermUnfoldingCoordinatesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.integral_baseTerm_unfolding_coordinates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsTh ψ d W x₀ Th → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ (𝓐 : Set (flagN d)) (𝓑 : Set (GA D W)), NullMeasurableSet 𝓐 vN.ν → NullMeasurableSet 𝓑 vW.μ → (∀ f : GA D V → ENNReal, Measurable f → (∀ c, ∀ n ∈ flagN d, f (d.nC c * n) = f n) → ∫⁻ n in 𝓐, f n.1 ∂vN.ν = ∫⁻ u, ∫⁻ b in vb.𝓕, f (d.nB b * d.levi u.1) ∂vb.μ ∂vU.ν) → ∫⁻ p in 𝓐 ×ˢ 𝓑, ‖Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) x₀‖ₑ ∂(vN.ν.prod vW.μ) ≠ ⊤ → IntegrableOn (fun h => G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ)) 𝓑 vW.μ ∧ ∫ p in 𝓐 ×ˢ 𝓑, Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) x₀ ∂(vN.ν.prod vW.μ) = ∫ h in 𝓑, G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) ∂vW.μ := by
  first | exact @GlobalTheory.Unf.integral_base_term_coords | exact GlobalTheory.Unf.integral_base_term_coords | (intros; apply GlobalTheory.Unf.integral_base_term_coords <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldOverFlagUnipotentThetaLift

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

theorem mt_mem_GQ_rat {D : D7} (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ M : Matrix (Fin V.rank) (Fin V.rank) D.host.E, mt V γ = rat M := by
  simp only [GQ, HFinIn, HFin, Subgroup.mem_subgroupOf] at hγ
  obtain ⟨u, -, hu⟩ := hγ
  exact ⟨u.1, (congrArg Units.val hu).symm⟩



theorem unfold_over_N_lift : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat x₀) : Subgroup (GA D W)) 𝓑 vW.μ → IntegrableOn (fun h => G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ)) 𝓑 vW.μ ∧ ∫ n in vN.𝓝, Th n.1 * liftS om vW.μ vW.𝓕 G Φ n.1 ∂vN.ν = ∫ h in 𝓑, G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) ∂vW.μ := by
  intro D hD ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vb vU vW x₀ Th hx hTh G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)
  obtain ⟨hN1, hN2, hN3⟩ := vN.unit
  haveI := vW.haar
  haveI : SFinite vN.ν := inferInstance
  haveI : SFinite vW.μ := inferInstance
  obtain ⟨act, y₀, hy₀, hrel, htrans, hstab1, hstab2⟩ := GlobalTheory.T.flagUnitaryOrbitAction_transitive_with_stabilizer D V V₀ W ρ d x₀ hx
  letI := act
  obtain ⟨𝓐, h𝓐, hlay⟩ := GlobalTheory.T.flagUnipotent_fundamentalDomain_layers_integral D V V₀ ρ d vN vb vU
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin W.rank) (Fin ρ) D.host.E) := inferInstanceAs (Countable (Fin _ → Fin _ → _))
  haveI hΓc : Countable ((NFlagQ V d.e).prod (GQ W)) := Function.Injective.countable
    (f := fun γ : (NFlagQ V d.e).prod (GQ W) => ((⟨γ.1.1, (Subgroup.mem_prod.1 γ.2).1⟩ : NFlagQ V d.e),
      (⟨γ.1.2, (Subgroup.mem_prod.1 γ.2).2⟩ : GQ W)))
    fun a b h => by
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Subtype.ext (Prod.ext h.1 h.2)
  haveI : Countable ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _)) :=
    (Subgroup.inclusion_injective (Subgroup.map_subtype_le (MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀))).countable
  have hF : IsFundamentalDomain ((NFlagQ V d.e).prod (GQ W)) (vN.𝓝 ×ˢ vW.𝓕) (vN.ν.prod vW.μ) := by
    refine GlobalTheory.T.isFundamentalDomain_prod_of_kernel_image _ _ vN.ν vW.μ _ vN.𝓝 vW.𝓕 ?_ ?_
    · have hc : ((NFlagQ V d.e).prod (GQ W)).comap (MonoidHom.inl (flagN d) (GA D W)) = NFlagQ V d.e := by
        ext n
        simp only [Subgroup.mem_comap, MonoidHom.inl_apply, Subgroup.mem_prod, one_mem, and_true]
      rw [hc]; exact hN2
    · have hc : ((NFlagQ V d.e).prod (GQ W)).map (MonoidHom.snd (flagN d) (GA D W)) = GQ W := by
        ext h
        constructor
        · rintro ⟨p, hp, rfl⟩
          exact (Subgroup.mem_prod.1 hp).2
        · intro hh
          exact ⟨(1, h), Subgroup.mem_prod.2 ⟨one_mem _, hh⟩, rfl⟩
      rw [hc]; exact vW.fund
  have hG' : IsFundamentalDomain ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _))
      (𝓐 ×ˢ 𝓑) (vN.ν.prod vW.μ) := by
    refine GlobalTheory.T.isFundamentalDomain_prod_of_kernel_image _ _ vN.ν vW.μ _ 𝓐 𝓑 ?_ ?_
    · rw [hstab1]; exact h𝓐
    · rw [hstab2]; exact h𝓑
  have hmeas : ∀ y : Orb W x₀, Measurable fun p : flagN d × GA D W =>
      Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) y.1 := by
    intro y
    have t4 := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS Φ hΦ).2.2.2.1 y.1
    refine Continuous.measurable ?_
    refine ((hTh.cont.comp continuous_fst).mul (hG.2.1.comp continuous_snd)).mul ?_
    exact t4.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hinv : ∀ (γ : (NFlagQ V d.e).prod (GQ W)) (y : Orb W x₀) (p : flagN d × GA D W),
      Th ((γ : flagN d × GA D W) * p).1.1 * G ((γ : flagN d × GA D W) * p).2 *
        term ψ d W vS (om (((γ : flagN d × GA D W) * p).1.1, ((γ : flagN d × GA D W) * p).2) Φ) (γ • y).1 =
      Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) y.1 := by
    intro γ y p
    have hmem := Subgroup.mem_prod.1 γ.2
    have hq1 : ((γ.1.1 : flagN d) : GA D V) ∈ GQ V := hmem.1
    have hq2 : γ.1.2 ∈ GQ W := hmem.2
    obtain ⟨M, hM⟩ := mt_mem_GQ_rat W hq2
    have hΨ := hω.om_pres (p.1.1, p.2) Φ hΦ
    have hΨ' := hω.om_pres (1, γ.1.2) _ hΨ
    have key : term ψ d W vS (om ((γ.1.1 : GA D V) * p.1.1, γ.1.2 * p.2) Φ) (γ • y).1 =
        term ψ d W vS (om (p.1.1, p.2) Φ) y.1 := by
      have hsplit : ((γ.1.1 : GA D V) * p.1.1, γ.1.2 * p.2) =
          (((γ.1.1 : GA D V), 1) * ((1 : GA D V), γ.1.2)) * (p.1.1, p.2) := by
        ext <;> simp
      rw [hsplit, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      have t2 := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS _ hΨ').2.1
      have t3 := (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hω hω' vS _ hΨ).2.2.1
      have e1 : (rat (M * y.1) : Mx D W.rank ρ) = rat (γ • y).1 ⬝ blockX d (γ.1.1 : GA D V) := by
        rw [hrel γ y, hM, rat_mul]
      rw [t2 _ hq1 γ.1.1.2 (γ • y).1 (M * y.1) e1, t3 _ hq2 (M * y.1) y.1 (by rw [hM, rat_mul])]
    have hT : Th ((γ.1.1 : GA D V) * p.1.1) = Th p.1.1 := hTh.left _ hq1 γ.1.1.2 _ p.1.2
    have hGG : G (γ.1.2 * p.2) = G p.2 := hG.1 _ hq2 p.2
    show Th ((γ.1.1 : GA D V) * p.1.1) * G (γ.1.2 * p.2) *
        term ψ d W vS (om ((γ.1.1 : GA D V) * p.1.1, γ.1.2 * p.2) Φ) (γ • y).1 = _
    exact congrArg₂ (· * ·) (congrArg₂ (· * ·) hT hGG) key
  obtain ⟨hl, hi⟩ := GlobalTheory.T.lintegral_unfold_sum_transitive_orbit (flagN d × GA D W) (vN.ν.prod vW.μ) ((NFlagQ V d.e).prod (GQ W)) (Orb W x₀) y₀ htrans
    (vN.𝓝 ×ˢ vW.𝓕) (𝓐 ×ˢ 𝓑) hF hG'
    (fun y p => Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) y.1) hmeas hinv
  obtain ⟨hfin, hLA⟩ := GlobalTheory.T.unipotentMean_thetaLift_eq_orbitIntegral D hD ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vW x₀ Th hx hTh G Φ hG hΦ
  simp only [hy₀] at hl hi
  have hfin' := hl ▸ hfin
  obtain ⟨hint, hLC⟩ := GlobalTheory.T.integral_baseTerm_unfolding_coordinates D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vb vU vW x₀ Th hTh G Φ hG hΦ 𝓐 𝓑
    h𝓐.nullMeasurableSet h𝓑.nullMeasurableSet hlay hfin'
  exact ⟨hint, by rw [hLA, ← hi hfin, hLC]⟩

end GlobalTheory.Unf
end
end
end
