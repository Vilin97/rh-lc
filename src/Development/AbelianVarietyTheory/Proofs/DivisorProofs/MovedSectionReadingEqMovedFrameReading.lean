module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrMoveValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSecGeneratorFibre
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPeriodCompIsometry
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsChangeLevelIsometryLinearMap
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulReadingOfMovedSectionAtFrameStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCoordinatesFrameRationalIsometry
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionSqMultiplierAlongIsometryMoveStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnReadingsNormalisedThetaPointsStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagDomainModelsOfFamilyUniformisation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNormalisedFramedPointOnEachComponentStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryMatrixOfLatticeIsometry
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUniformisationIsComplexUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonemptyThetaDataFlagDomainModelsStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointArithmeticGroupInvariantSig
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointArithmeticGroupInvariantSigStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointTriangularFrameWeightRuleStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedPointsSatisfySingleFrameStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CabsGenEqOneOfNormPin

section

@[expose] public section

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.UnitFrameGen MeasureTheory

noncomputable section

namespace GlobalTheory.GeoLevel



theorem cabs_gen_eq_one_of_normPin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (i i' : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di i').La →+ (Fin g → ℂ)) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (y z y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), IsPeriod (F.Di i) ty P → IsPeriod (F.Di i') ty P' → y.x = F.u i P → z.x = F.u i' P' → NormPin F i P y → NormPin F i' P' z → FrMove ρ ν y y' → FrBor t z y' → cabs (t none : CAt σ) = 1 := by
  intro E _ _ _ H Dw l Xo c σ σ' g ty F i i' P P' ρ ν y₀ z₀ y' t hp hp' hu hu' hx hx' hmv hb
  obtain ⟨Hm, χ, fr, θ, Fd, hH, -, him, hd, hn, hc, h0, ha, hv, hF, hI⟩ := hx
  obtain ⟨Hm', χ', fr', θ', Fd', hH', -, him', hd', hn', hc', h0', ha', hv', hF', hI'⟩ := hx'
  obtain ⟨O, ω, o1, o2, o3, o4, o5⟩ := GlobalTheory.MoveValues.frMove_values E H Dw l Xo c σ ρ ν _ _ hmv
  have hxρ : z₀.x = y₀.x ≫ ρ := hb.1.symm.trans hmv.1
  obtain ⟨hxx, -, hbc⟩ := hb
  clear hmv
  obtain ⟨gam, hl, hg1, hg4, hex0⟩ := exists_isometry_of_sabMap F ν hp hp'
    ((congrArg (· ≫ ρ) hu).symm.trans (hxρ.symm.trans hu'))
  obtain ⟨h, hdet, hh⟩ : ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h.det ∧ ∀ z, h *ᵥ z = hl z :=
    ⟨LinearMap.toMatrix' hl.toLinearMap, by
      rw [LinearMap.det_toMatrix']; exact LinearEquiv.isUnit_det' hl,
      fun a => by rw [LinearMap.toMatrix'_mulVec]; rfl⟩
  have hg : ∀ a, P' (gam a) = h *ᵥ P a := fun a => by rw [hh, hg4]
  have hex : ∀ z, (F.ex i' P' (h *ᵥ z)).left = (F.ex i P z).left ≫ ν.φ := fun z => by rw [hh, hex0]
  have hspan : Submodule.span ℝ (P.range : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hp.2.2.2.1
  have hHH : ∀ z w, hermForm Hm' (h *ᵥ z) (h *ᵥ w) = hermForm Hm z w :=
    hermForm_eq_of_im _ hspan Hm Hm' h (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← hg, ← hg, him, him', hg1])
  have hexp : ∀ a ∈ P.range, ∀ z, F.ex i P (z + a) = F.ex i P z := fun a ha z => by
    rw [F.ex_add i P hp, (F.ex_ker i P hp a).2 ha]
    exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hcov : ∀ z, ∃ j, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z =>
    GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB _
  have hcov2 : ∀ z, ∃ q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O q.1 q.2 := fun z => by
    obtain ⟨j, hj⟩ := hcov z
    obtain ⟨j', hj'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB ((F.ex i P z).left ≫ ν.φ)
    exact ⟨(j', j), (o1 _ _ _).2 ⟨hj', hj⟩⟩
  have tr : ∀ j j' z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex i' P' (h *ᵥ z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j j' z hz => by
    rw [hex]; exact ((o1 _ _ _).1 hz).1
  have tr2 : ∀ j j' z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O j j' →
      ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j' := fun j j' z hz => ((o1 _ _ _).1 hz).2
  have hm : ∀ j, ∀ a ∈ P.range, ∀ z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → ‖fr j z‖ =
      Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re) * ‖fr j (z + a)‖ := by
    rintro j _ ⟨a, rfl⟩ z hz
    exact norm_factor Hm _ _ _ _ _ (ha a j z).1 ((ha a j z).2 hz)
  have dl : Differentiable ℂ (fun z' : Fin g → ℂ => h *ᵥ z') :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h)).differentiable
  have hw0 : ∀ z, (F.ex i P z).left ≫ Xo.univ.t.G.hom = (y₀.x : Sp ℂ ⟶ Xo.X) := fun z =>
    (Over.w (F.ex i P z)).trans hu.symm
  have hw0' : ∀ z, (F.ex i' P' z).left ≫ Xo.univ.t.G.hom = (z₀.x : Sp ℂ ⟶ Xo.X) := fun z =>
    (Over.w (F.ex i' P' z)).trans hu'.symm
  have hz0 : (F.ex i P 0).left = (y₀.x : Sp ℂ ⟶ Xo.X) ≫ eSec Xo.univ.t.G := by
    rw [(F.ex_ker i P hp 0).2 (zero_mem _), hu]
    rfl
  have hfr : ∀ q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι, ∀ z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O q.1 q.2 →
      fr' q.1 (h *ᵥ z) = valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * fr q.2 z :=
    frames_eq P.range hspan (fun q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι => {z | ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ O q.1 q.2})
      (fun j => GlobalTheory.FamilyUnif_isOpen_ex F i P hp _) hcov2
      (fun j a ha z hz => by rw [Set.mem_setOf_eq, hexp a ha]; exact hz)
      (fun q z => valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * fr q.2 z) (fun q z => fr' q.1 (h *ᵥ z))
      (fun q q' z => valAt' ((F.ex i P z).left ≫ ν.φ) (Xo.univ.t.PP.L.U q.1 ⊓ Xo.univ.t.PP.L.U q'.1)
        (Xo.univ.t.PP.L.g q.1 q'.1).val)
      (fun a z => Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re))
      (fun q => (((GlobalTheory.ClassUniq.isHolTo_ex F i P hp) (O q.1 q.2) (ω q.1 q.2)).2.mono
        fun z hz => ⟨Set.mem_univ _, hz⟩).mul ((hd q.2).mono fun z hz => tr2 _ _ z hz))
      (fun q => (hd' q.1).comp dl.differentiableOn fun z hz => tr _ _ z hz)
      (fun q z hz => mul_ne_zero (o2 _ _ _ hz) (hn _ z (tr2 _ _ z hz)))
      (fun q q' z h1 h2 => by
        rw [hc q.2 q'.2 z ((top_le_preimage_inf _ _ _).2 ⟨tr2 _ _ z h1, tr2 _ _ z h2⟩), ← mul_assoc,
          o3 _ _ _ _ _ h1 h2, mul_assoc])
      (fun q q' z h1 h2 => by
        have e2 := hc' q.1 q'.1 (h *ᵥ z) ((top_le_preimage_inf _ _ _).2 ⟨tr _ _ _ h1, tr _ _ _ h2⟩)
        rw [hex] at e2
        exact e2)
      (fun q hz => by
        have t0 := tr _ _ 0 hz
        simp only [Matrix.mulVec_zero] at t0 ⊢
        rw [h0 _ (tr2 _ _ 0 hz), h0' _ t0, hxρ]
        exact o4 _ _ _ _ hz0 hz)
      (fun q a haa z hz => by
        rw [hexp a haa, norm_mul, norm_mul, hm _ a haa z (tr2 _ _ z hz)]
        ring)
      (by
        rintro q _ ⟨a, rfl⟩ z hz
        have := norm_factor Hm' _ _ _ _ _ (ha' (gam a) q.1 (h *ᵥ z)).1
          ((ha' (gam a) q.1 (h *ᵥ z)).2 (tr _ _ z hz))
        rw [hg, hHH, hHH, ← Matrix.mulVec_add] at this
        exact this)
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by simp [spMap]
  have hbc' : GlobalTheory.Frames.SecBC (RingHom.id ℂ) (Formalism.L2.PjFree.toC (t none : CAt σ)) z₀.x y'.x
      z₀.s y'.s := by
    obtain ⟨pm, p1, p2, p3⟩ := hbc
    exact ⟨pm, p1, by rw [hid]; exact p2.trans (Category.comp_id _).symm, p3⟩
  have hθ : ∀ z, θ z = Formalism.L2.PjFree.toC (t none : CAt σ) * θ' (h *ᵥ z) := fun z => by
    obtain ⟨q, hq⟩ := hcov2 z
    let p : Over.mk (y₀.x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex i P z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv q.2 z _ e1 e2 (tr2 _ _ z hq)
    have hval := GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hxx _ _ _ hbc'
      (Over.homMk (F.ex i' P' (h *ᵥ z)).left (hw0' _)) q.1 _ _
      (fun pt h1 h2 => hv' q.1 (h *ᵥ z) pt h1 h2 (tr _ _ z hq))
      (fun pt h1 h2 => o5 q.1 q.2 _ pt _ e1 e2 (h1.trans (hex z)) h2 hq)
    have hval2 : valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * (θ z * fr q.2 z) =
        Formalism.L2.PjFree.toC (t none : CAt σ) * (θ' (h *ᵥ z) * fr' q.1 (h *ᵥ z)) :=
      (congrArg (valAt' (F.ex i P z).left (O q.1 q.2) (ω q.1 q.2) * ·) v1).symm.trans hval
    rw [hfr q z hq] at hval2
    apply mul_right_cancel₀ (mul_ne_zero (o2 _ _ _ hq) (hn _ z (tr2 _ _ z hq)))
    linear_combination hval2
  have ht0 : Formalism.L2.PjFree.toC (t none : CAt σ) ≠ 0 := Units.ne_zero (M₀ := ℂ) (t none)
  have hθp : ∀ a ∈ P.range, ∀ z, ‖θ (z + a)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm (z + a) (z + a)).re) =
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) := fun a ha z => by
    obtain ⟨j, hj⟩ := hcov z
    have hj' : ⊤ ≤ (F.ex i P (z + a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [hexp a ha]; exact hj
    let p : Over.mk (y₀.x : Sp ℂ ⟶ Xo.X) ⟶ Xo.univ.t.G := Over.homMk (F.ex i P z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv j z _ e1 e2 hj
    have v2 := hv j (z + a) _ (by rw [hexp a ha]; exact e1) e2 hj'
    exact normSq_periodic hH _ _ _ _ z a (hn j _ hj') (v2.symm.trans v1) (hm j a ha z hj)
  haveI : Countable P.range := by
    haveI := hp.2.2.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hinj : Function.Injective (fun z : Fin g → ℂ => h *ᵥ z) :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hdet)
  have hn0 : ‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ≠ 0 := norm_ne_zero_iff.2 ht0
  have key : ∀ z, ‖θ' (h *ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' (h *ᵥ z) (h *ᵥ z)).re) =
      (‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ^ 2)⁻¹ *
        (‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) :=
    fun z => by rw [hθ, hHH, norm_mul, mul_pow]; field_simp
  have hmean := mean_comp_eq P.range P'.range h hdet (fun z => ⟨?_, ?_⟩) Fd Fd' hF hF'
    (fun z => ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re))
    (fun a ha z => by simp only [key, hθp a ha z])
  · simp only [key] at hmean
    rw [hI', integral_const_mul, mul_div_assoc, hI, mul_one, inv_eq_one] at hmean
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hmean
  · rintro ⟨a, ha⟩
    refine ⟨gam.symm a, hinj ?_⟩
    simp only
    rw [← hg, gam.apply_symm_apply, ha]
  · rintro ⟨a, rfl⟩
    exact ⟨gam a, hg a⟩

end GlobalTheory.GeoLevel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCoordinatesFrameRationalIsometryStatement

section

@[expose] public section

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

theorem _root_.GlobalTheory.T.period_coordinates_frame_rational_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (a : GL (Fin r) E) (h : IsMatch X X' a) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ), Formalism.L2.PjFree.perFr X' (lact a (castFr h.psi x)) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = Formalism.L2.PjFree.perFr X x v τ i := by
  first | exact @GlobalTheory.GeoLevel.perFr_lact_of_isMatch | exact GlobalTheory.GeoLevel.perFr_lact_of_isMatch | (intros; apply GlobalTheory.GeoLevel.perFr_lact_of_isMatch <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSectionReadingEqMovedFrameReading

section

@[expose] public section

set_option autoImplicit false

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

noncomputable section

namespace GlobalTheory.GeoLevel

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}



theorem exists_isometry_of_move_deriv {g : ℕ} {σ' : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty)
    {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ) {i : Fin F.n} {P P' : (F.Di i).La →+ (Fin g → ℂ)}
    (p : IsPeriod (F.Di i) ty P) (p' : IsPeriod (F.Di i) ty P') (hu : F.u i P ≫ ρ = F.u i P')
    (hd : ∀ j, ∃ v, IsDerivAt0 (fun z => (F.ex i P z).left) (Pi.single j 1) v ∧
      IsDerivAt0 (fun z => (F.ex i P' z).left) (Pi.single j 1) (v ≫ ν.φ)) :
    ∃ gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i).La, (∀ a b, (F.Di i).EF (gam a) (gam b) = (F.Di i).EF a b) ∧
      (∀ a, P' (gam a) = P a) ∧ ∀ z, (F.ex i P' z).left = (F.ex i P z).left ≫ ν.φ := by
  obtain ⟨gam, h, hiso, hh, hex⟩ := exists_isometry_of_sabMap F ν p p' hu
  have hcol : ∀ j, h.toLinearMap (Pi.single j 1) = Pi.single j 1 := by
    intro j
    obtain ⟨v, hv, d1⟩ := hd j
    have d0 := FibreDeriv.isDerivAt0_comp hv ν.φ
    simp only [← hex] at d0
    have d2 := (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F _ P' p') h.toLinearMap _ _).1 d0
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P' p'
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have hid : h.toLinearMap = LinearMap.id := by
    refine (Pi.basisFun ℂ (Fin g)).ext fun j => ?_
    rw [Pi.basisFun_apply, hcol, LinearMap.id_apply]
  have hz : ∀ z, h z = z := fun z => LinearMap.congr_fun hid z
  exact ⟨gam, hiso, fun a => by rw [hh, hz], fun z => by rw [← hex, hz]⟩



theorem evR_normUn_move {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)}
    {M : ModelsOf F r} {k : Fin F.n} (T : ThetaData e F M k) {un : (M.X k).dom → FrPt Xo c (CAt σ)}
    (hun : IsNormUn T un) (x x' : (M.X k).dom) (A : Matrix (Fin r) (Fin r) E)
    (hA : A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E))
    (hper : ∀ a, ∃ a', (M.φ k a' : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E) ∧ T.Pf x'.1 a' = T.Pf x.1 a)
    {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ) (hρ : ρ ≫ Xo.s = Xo.s)
    (hx : (un x').x = (un x).x ≫ ρ) (hu : ∀ τ i, (un x').u τ i = (un x).u τ i ≫ ν.φ)
    {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hw : Dom w n) {f f' : Rul Xo c} (hf : f ∈ sec Xo c w n)
    (hff : ∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') :
    evR Xo c f' (un x) = evR Xo c f (un x') := by
  obtain ⟨κ, hκ, hy⟩ := hun x
  obtain ⟨κ', hκ', hy'⟩ := hun x'
  have hb : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm x.1) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact x.2
  have hb' : T.co.symm x'.1 ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm x'.1) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact x'.2
  have p := T.isPer _ hb
  have p' := T.isPer _ hb'
  obtain ⟨gam, hiso, hP, hex⟩ := exists_isometry_of_move_deriv F ν p p'
    ((congrArg (· ≫ ρ) hy.1).symm.trans (hx.symm.trans hy'.1)) (fun j => by
      obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective j
      exact ⟨_, hy.2.1 τ i, hu τ i ▸ hy'.2.1 τ i⟩)
  have hgam : ∀ a, (M.φ k (gam a) : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E) := fun a => by
    obtain ⟨a', h1, h2⟩ := hper a
    have h3 : gam a = a' := p'.2.1 (by rw [hP, T.co.apply_symm_apply, T.co.apply_symm_apply, h2])
    rw [h3, h1]
  obtain ⟨y', hmv⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hρ (CAt σ) (un x)).1
  obtain ⟨t₀, ht⟩ := exists_frBor_gen (un x') y' (hmv.1.trans hx.symm)
    (funext fun τ => funext fun i => (hmv.2.1 τ i).trans (hu τ i).symm)
  have hC : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : Formalism.L2.PjFree.relab c σ (e j).1 (M.X k).ξ0 ≠ 0 := (map_ne_zero _).2 (M.X k).ξ0_ne
    positivity
  have d1 := (T.norm _ hb).1.ne_zero
  have d2 := (T.norm _ hb').1.ne_zero
  have k1 : κ ≠ 0 := fun h0 => mul_ne_zero hC d1 (by rw [← hκ, h0]; simp)
  have k2 : κ' ≠ 0 := fun h0 => mul_ne_zero hC d2 (by rw [← hκ', h0]; simp)
  have hth := GlobalTheory.T.thetaSection_sq_multiplier_along_isometry_move E H Dw l Xo c σ g e F r M k T _ hb _ hb' κ κ' (un x) (un x') y' gam A ρ ν _ k1 k2 hy hy'
    hiso hgam hA hP hex hmv ht
  have ht2 : Formalism.L2.PjFree.toC (t₀ : CAt σ) ^ 2 = 1 := by
    rw [hκ, hκ'] at hth
    refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hC d2) d1) ?_
    refine hth.trans ?_
    ring
  have hred : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  rw [hff _ _ hmv, (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 (CAt σ) hred w n f hf _ _ _ ht,
    wchar_ex_sign Dw _ ht2 (fun _ => rfl) w n hw.2, one_mul]

theorem exists_isMatch_of_models (D : Datum H) {X X' : Data E r} (φ : D.La ≃ₗ[𝓞 E] X.Λ) (φ' : D.La ≃ₗ[𝓞 E] X'.Λ)
    (hΨ : X.Ψ = X'.Ψ) (hp : X.p0 = X'.p0) (hG : X'.Gm = X.Gm) (hξ : X'.ξ0 = X.ξ0)
    (ef : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (ef' : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X'.ξ0 * herm X'.Gm (φ' a : Fin r → E) (φ' b))) :
    ∃ δ : GL (Fin r) E, IsMatch X X' δ ∧
      ∀ a, (φ' a : Fin r → E) = (δ : Matrix (Fin r) (Fin r) E) *ᵥ (φ a : Fin r → E) := by
  have hs : ∀ (Y : Data E r) (ψ : D.La ≃ₗ[𝓞 E] Y.Λ), Function.Injective (Y.Λ.subtype ∘ₗ ψ.toLinearMap) ∧
      Submodule.span E (Set.range (Y.Λ.subtype ∘ₗ ψ.toLinearMap)) = ⊤ := fun Y ψ => by
    refine ⟨Subtype.val_injective.comp ψ.injective, ?_⟩
    rw [← Y.Λ_span]
    congr 1
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (ψ a).2
    · intro hv
      exact ⟨ψ.symm ⟨v, hv⟩, congrArg Subtype.val (ψ.apply_symm_apply _)⟩
  have hc : cc (-X.ξ0) = -(-X.ξ0) := by
    have := X.ξ0_im
    unfold cc at this ⊢
    rw [map_neg, this]
  rw [hG, hξ] at ef'
  obtain ⟨δ, h1, h2⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry E H D D r (-X.ξ0) X.Gm
    (X.Λ.subtype ∘ₗ φ.toLinearMap) (X'.Λ.subtype ∘ₗ φ'.toLinearMap) (LinearEquiv.refl _ _) hc
    ⟨(hs X φ).1, (hs X φ).2, X.Gm_herm, X.Gm_det, ef⟩ ⟨(hs X' φ').1, (hs X' φ').2, X.Gm_herm, X.Gm_det, ef'⟩
    (fun _ _ => rfl)
  have h3 : ∀ a, (φ' a : Fin r → E) = (δ : Matrix (Fin r) (Fin r) E) *ᵥ (φ a : Fin r → E) := h2
  refine ⟨δ, ⟨hΨ, hp, hξ.symm, fun u v => by rw [hG, h1], fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩, h3⟩
  · have := h3 (φ.symm ⟨v, hv⟩)
    rw [φ.apply_symm_apply] at this
    exact this ▸ (φ' _).2
  · have := h3 (φ'.symm ⟨_, hv⟩)
    rw [φ'.apply_symm_apply] at this
    have e := congrArg (fun u => ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u) this
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at e
    rw [e]
    exact (φ _).2

end



theorem rdU_move_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (φD : Dw.La →ₗ[𝓞 E] (Fin r → E)), Function.Injective φD → Submodule.span E (Set.range φD) = ⊤ → (∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φD x) (φD y))) → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ (U.X k).ξ0).im < 0) → ∀ (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k) δ), ((δ : Matrix (Fin r) (Fin r) E).det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ (δ : Matrix (Fin r) (Fin r) E).det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U k k h ρ ν → ∀ w n, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n, (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k (lact δ (castFr h.psi x)) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k φD hinj hsp hEF hneg δ h hdet ρ ν hρ hmm w n hw f hf f' hf' hff x hx
  obtain ⟨g, e, F, ik, φ, ⟨hef, hpin⟩, hnorm⟩ := exists_pinned_of_isUnf hU
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨M, hM, hξ, hMG⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt E H Dw l Xo _ _ _ F r
    (U.X k).ξ0 (U.X k).Gm φD (U.X k).ξ0_im hneg ⟨hinj, hsp, (U.X k).Gm_herm, (U.X k).Gm_det, hEF⟩
  have T : ∀ k, ThetaData e F M k := fun k => (GlobalTheory.T.nonempty_thetaData_flagDomainModels E H Dw l Xo c σ g e F r M hσ hM hξ k).some
  choose un hun using fun k => GlobalTheory.T.exists_normalisedFramedPoint_on_each_component hT E H Dw l Xo c σ g e F r M k (T k)
  have hok : FramesOK e F M un :=
    ⟨fun k => GlobalTheory.T.normalised_points_satisfy_single_frame hT E H Dw l Xo c σ g e F r M k (T k) (un k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_triangularFrame_weightRule hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_arithmeticGroup_invariant_sign hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
      fun a n han f hf k => GlobalTheory.T.differentiableOn_readings_normalised_theta_points hB hT E H Dw l Xo c σ g e F r M un k (T k) (hun k) a n han f hf⟩
  have hU₀ := isUnf_built hB E H Dw l Xo c σ g e F r M un hσ hM hξ hok
  obtain ⟨δ₀, h₀, hφ⟩ := exists_isMatch_of_models (F.Di (ik k)) (φ k) (M.φ (ik k))
    (Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hM.type (ik k)).2 τ).symm)
    ((hU.2.1 k).1.trans (hM.type (ik k)).1.symm) (hMG _).1 (hMG _).2 (hef k) (hM.ef _)
  have hPf : ∀ (y : Frame (U.X k).Ψ r) a j, (T (ik k)).Pf (lact δ₀ (castFr h₀.psi y)) a j =
      Formalism.L2.PjFree.perFr (U.X k) y (φ k a : Fin r → E) (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2 := fun y a j => by
    rw [(T (ik k)).per, hφ]
    exact GlobalTheory.T.period_coordinates_frame_rational_isometry E r _ _ δ₀ h₀ y _ _ _
  have key : ∀ y : (U.X k).dom, (un (ik k) ⟨_, h₀.mem_dom y.2⟩).x = (U.un k y).x ∧
      (un (ik k) ⟨_, h₀.mem_dom y.2⟩).u = (U.un k y).u ∧
      (IsUnitFr (U.X k) y.1 → ∃ P : (F.Di (ik k)).La →+ (Fin g → ℂ),
        IsPeriod (F.Di (ik k)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P ∧ (U.un k y).x = F.u (ik k) P ∧
        NormPin F (ik k) P (U.un k y) ∧ NormPin F (ik k) P (un (ik k) ⟨_, h₀.mem_dom y.2⟩)) := fun y => by
    obtain ⟨P, a1, a2, a3, a4⟩ := hpin k y
    obtain ⟨P', b1, -, b3, b4, b5⟩ := hok.1 (ik k) ⟨_, h₀.mem_dom y.2⟩
    obtain rfl : P' = P := AddMonoidHom.ext fun v => funext fun j =>
      (b1 v j).trans (((T (ik k)).per _ v j).symm.trans ((hPf y.1 v j).trans (a1 v j).symm))
    refine ⟨b3.trans a3.symm, funext fun τ => funext fun i =>
      ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ _ a2).2.1 _).unique (b4 τ i) (a4 τ i), fun hy =>
      ⟨P', a2, a3, hnorm k y P' a1 hy, b5 fun τ i => (congrArg norm (h₀.dmin_eq y.1 τ i)).trans (hy _ i)⟩⟩
  obtain ⟨ν₁, hν₁, hid⟩ := (GlobalTheory.MoveCalc.frMove_calculus E H Dw l Xo c).1
  have hmm₀ : MoveMatch U (unfOf e F M un) k (ik k) h₀ (𝟙 _) ν₁ := fun y y' hy =>
    ⟨hy.1.trans ((Category.comp_id _).trans (key y).1.symm), (funext fun τ => funext fun i =>
      (hy.2.1 τ i).trans ((congrArg _ hν₁).trans (Category.comp_id _))).trans (key y).2.1.symm⟩
  obtain ⟨ε, -, hε⟩ := GlobalTheory.T.exists_const_mul_reading_of_moved_section_at_frame E H Dw l Xo c σ r U (unfOf e F M un) hσ hU hU₀ k (ik k) δ₀ h₀ (𝟙 _) ν₁
    (Category.id_comp _) hmm₀ (fun y y' t hy hmv hb => by
      obtain ⟨P, p, a1, a2, a3⟩ := (key y).2.2 hy
      exact cabs_gen_eq_one_of_normPin E H Dw l Xo c σ _ g _ F _ _ P P _ ν₁ _ _ y' t p p a1
        ((key y).1.trans a1) a2 a3 hmv hb) n
  have hself : ∀ (f₀ : Rul Xo c) (y y' : FrPt Xo c (CAt σ)), FrMove (𝟙 _) ν₁ y y' →
      evR Xo c f₀ y = evR Xo c f₀ y' := fun f₀ y y' hy => by
    rw [(GlobalTheory.exists_unique_frMove E H Dw l Xo c _ ν₁ (Category.id_comp _) (CAt σ) y).2 y y' ν₁ rfl (hid _ y) hy]
  have hx' := h.mem_dom hx
  rw [hε w hw f' hf' f' hf' (hself f') x hx, hε w hw f hf f hf (hself f) _ hx']
  refine congrArg (ε * ·) ?_
  refine (rdU_of_mem (unfOf e F M un) f' (ik k) (h₀.mem_dom hx)).trans
    (Eq.trans (congrArg Formalism.L2.PjFree.toC ?_) (rdU_of_mem (unfOf e F M un) f (ik k) (h₀.mem_dom hx')).symm)
  obtain ⟨y', hmv⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hρ (CAt σ) (U.un k ⟨x, hx⟩)).1
  obtain ⟨m1, m2⟩ := hmm ⟨x, hx⟩ y' hmv
  obtain ⟨k1, k2, -⟩ := key ⟨x, hx⟩
  obtain ⟨k3, k4, -⟩ := key ⟨_, hx'⟩
  refine evR_normUn_move (T (ik k)) (hun (ik k)) ⟨_, h₀.mem_dom hx⟩ ⟨_, h₀.mem_dom hx'⟩
    ((δ₀ * δ * δ₀⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ?_ (fun a => ?_) ν hρ ?_ (fun τ i => ?_) hw hf hff
  · have : ((δ₀ * δ * δ₀⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).det = (δ : Matrix (Fin r) (Fin r) E).det := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj]
    rw [this]
    exact hdet
  · obtain ⟨a', ha'⟩ := (φ k).surjective ⟨_, (h.lat _).1 (φ k a).2⟩
    have ha : (φ k a' : Fin r → E) = (δ : Matrix (Fin r) (Fin r) E) *ᵥ (φ k a : Fin r → E) := congrArg Subtype.val ha'
    refine ⟨a', ?_, funext fun j => ?_⟩
    · rw [hφ, hφ, ha, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Matrix.mul_assoc, Units.inv_mul,
        Matrix.mul_one, Units.val_mul]
    · refine (hPf _ a' j).trans (Eq.trans ?_ (hPf _ a j).symm)
      rw [ha]
      exact GlobalTheory.T.period_coordinates_frame_rational_isometry E r _ _ δ h x _ _ _
  · exact k3.trans (m1.symm.trans (hmv.1.trans (congrArg (· ≫ ρ) k1.symm)))
  · exact (congrFun (congrFun (k4.trans m2.symm) τ) i).trans
      ((hmv.2.1 τ i).trans (congrArg (· ≫ ν.φ) (congrFun (congrFun k2.symm τ) i)))

end GlobalTheory.GeoLevel
end
end
end
