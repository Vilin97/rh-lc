module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSecGeneratorFibre
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsChangeLevelIsometryLinearMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ContinuousOnNormDiagOfTriangularSqrtStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicFactorGeneratorThetaSection
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicPeriodsAdaptedStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ImNegOfFramePeriodVectorStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MeanSquareMultipleThetaSectionFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PeriodEqTriangularOrthonormalStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularFrameChangeOfTriangularPeriodStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnLeftInverse
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOfImHermFormEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermEqOfNormalised
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaCharHalfDifferentiableNeZeroFamilies
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.AppellHumbertMeanSquareEqOfProportionalSections

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm


open GlobalTheory.UnitFrameGen MeasureTheory in
theorem ahMean_eq_of_secBC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P P' : (F.Di k).La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ) (x x' : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (a : ℂ) (m m' : ℝ), IsPeriod (F.Di k) ty P → IsPeriod (F.Di k) ty P' → (∀ v, P v = h₀ *ᵥ P' v) → x = F.u k P → x' = x → SecBC (RingHom.id ℂ) a x x' s s' → AHMean F k P x s m → AHMean F k P' x' s' m' → m' = ‖a‖ ^ 2 * m := by
  intro E _ _ _ H Dw l Xo σ' g ty F i P' P h x' x s' s a m' m hp' hp hg hu' hxx hbc hA' hA
  obtain ⟨Hm, χ, fr, θ, Fd, hH, -, him, hd, hn, hc, h0, ha, hv, hF, hI⟩ := hA
  obtain ⟨Hm', χ', fr', θ', Fd', hH', -, him', hd', hn', hc', h0', ha', hv', hF', hI'⟩ := hA'
  obtain ⟨hdet, huu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F i
    P P' (LinearEquiv.refl _ _) h hp hp' (fun _ _ => rfl) (fun _ _ => ⟨0, by simp⟩) (fun _ => ⟨0, by simp⟩) hg
  have hspan : Submodule.span ℝ (P.range : Set (Fin g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hp.2.2.2.1
  have hHH : ∀ z w, hermForm Hm' (h *ᵥ z) (h *ᵥ w) = hermForm Hm z w :=
    hermForm_eq_of_im _ hspan Hm Hm' h (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← hg, ← hg, him, him'])
  have hexp : ∀ a ∈ P.range, ∀ z, F.ex i P (z + a) = F.ex i P z := fun a ha z => by
    rw [F.ex_add i P hp, (F.ex_ker i P hp a).2 ha]
    exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hcov : ∀ z, ∃ j, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z =>
    GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB _
  have tr : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ (F.ex i P' (h *ᵥ z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j z hz => by rw [hex]; exact hz
  have hm : ∀ j, ∀ a ∈ P.range, ∀ z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → ‖fr j z‖ =
      Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re) * ‖fr j (z + a)‖ := by
    rintro j _ ⟨a, rfl⟩ z hz
    exact norm_factor Hm _ _ _ _ _ (ha a j z).1 ((ha a j z).2 hz)
  have dl : Differentiable ℂ (fun z' : Fin g → ℂ => h *ᵥ z') :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin h)).differentiable
  have hfr : ∀ j z, ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h *ᵥ z) = fr j z :=
    frames_eq P.range hspan (fun j => {z | ⊤ ≤ (F.ex i P z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
      (fun j => GlobalTheory.FamilyUnif_isOpen_ex F i P hp _) hcov
      (fun j a ha z hz => by rw [Set.mem_setOf_eq, hexp a ha]; exact hz)
      fr (fun j z => fr' j (h *ᵥ z))
      (fun j j' z => valAt' (F.ex i P z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val)
      (fun a z => Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re))
      hd (fun j => (hd' j).comp dl.differentiableOn fun z hz => tr j z hz) hn
      (fun j j' z h1 h2 => hc j j' z ((top_le_preimage_inf _ _ _).2 ⟨h1, h2⟩))
      (fun j j' z h1 h2 => by
        have e2 := hc' j j' (h *ᵥ z) ((top_le_preimage_inf _ _ _).2 ⟨tr _ _ h1, tr _ _ h2⟩)
        rw [hex] at e2
        exact e2)
      (fun j hz => by
        have t0 := tr j 0 hz
        simp only [Matrix.mulVec_zero] at t0 ⊢
        rw [h0 j hz, h0' j t0, hxx])
      hm (by
        rintro j _ ⟨a, rfl⟩ z hz
        have := norm_factor Hm' _ _ _ _ _ (ha' a j (h *ᵥ z)).1 ((ha' a j (h *ᵥ z)).2 (tr j z hz))
        rw [hg, hHH, hHH, ← Matrix.mulVec_add] at this
        exact this)
  have hS : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hw0 : ∀ z, (F.ex i P z).left ≫ Xo.univ.t.G.hom = x' := fun z => by
    rw [← hex z]
    exact (Over.w (F.ex i P' (h *ᵥ z))).trans hu'.symm
  have hθ : ∀ z, θ z = a * θ' (h *ᵥ z) := fun z => by
    obtain ⟨j, hj⟩ := hcov z
    have hval := GlobalTheory.ThetaPtChg.val_of_secBC hS (Xo := Xo) _ _ hxx _ _ _ hbc
      (Over.homMk (F.ex i P z).left (hw0 z)) j _ _
      (fun pt h1 h2 => hv' j (h *ᵥ z) pt (h1.trans (hex z).symm) h2 (tr j z hj))
      (fun pt h1 h2 => hv j z pt h1 h2 hj)
    rw [hfr j z hj, ← mul_assoc] at hval
    exact mul_right_cancel₀ (hn j z hj) hval
  have hθp : ∀ b ∈ P.range, ∀ z, ‖θ' (h *ᵥ (z + b))‖ ^ 2 *
      Real.exp (-Real.pi * (hermForm Hm (z + b) (z + b)).re) =
      ‖θ' (h *ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) := fun b hb z => by
    obtain ⟨j, hj⟩ := hcov z
    have hj' : ⊤ ≤ (F.ex i P (z + b)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by rw [hexp b hb]; exact hj
    let p : Over.mk x' ⟶ Xo.univ.t.G := Over.homMk (F.ex i P z).left (hw0 z)
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := hv' j (h *ᵥ z) _ (by rw [hex]; exact e1) e2 (tr j z hj)
    have v2 := hv' j (h *ᵥ (z + b)) _ (by rw [hex, hexp b hb]; exact e1) e2 (tr j _ hj')
    rw [hfr j _ hj] at v1
    rw [hfr j _ hj'] at v2
    exact normSq_periodic hH _ _ _ _ z b (hn j _ hj') (v2.symm.trans v1) (hm j b hb z hj)
  haveI : Countable P.range := by
    haveI := hp.2.2.1
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hinj : Function.Injective (fun z : Fin g → ℂ => h *ᵥ z) :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hdet)
  have hmean := mean_comp_eq P.range P'.range h hdet (fun z => ⟨?_, ?_⟩) Fd Fd' hF hF'
    (fun z => ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re))
    (fun b hb z => by simp only [hHH, hθp b hb z])
  · rw [← hI, ← hI', ← hmean, ← mul_div_assoc, ← integral_const_mul]
    congr 2
    funext z
    rw [hθ, hHH, norm_mul, mul_pow, mul_assoc]
  · rintro ⟨b, hb⟩
    refine ⟨b, hinj ?_⟩
    simp only
    rw [← hg, hb]
  · rintro ⟨b, rfl⟩
    exact ⟨b, hg b⟩

end GlobalTheory.FrameNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.AppellHumbertMeanSquareEqOfProportionalSectionsStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.appellHumbertMeanSquare_eq_of_proportional_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P P' : (F.Di k).La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ) (x x' : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (a : ℂ) (m m' : ℝ), IsPeriod (F.Di k) ty P → IsPeriod (F.Di k) ty P' → (∀ v, P v = h₀ *ᵥ P' v) → x = F.u k P → x' = x → SecBC (RingHom.id ℂ) a x x' s s' → AHMean F k P x s m → AHMean F k P' x' s' m' → m' = ‖a‖ ^ 2 * m := by
  first | exact @GlobalTheory.FrameNorm.ahMean_eq_of_secBC | exact GlobalTheory.FrameNorm.ahMean_eq_of_secBC | (intros; apply GlobalTheory.FrameNorm.ahMean_eq_of_secBC <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicFactorGeneratorThetaSectionStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_holomorphicFactor_generator_thetaSection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → IsHolPeriods (F.Di k) ty B P → (∀ b ∈ B, (y b).x = F.u k (P b)) → (∀ z, DifferentiableOn ℂ (fun b => θ b z) B) → (∀ b ∈ B, ∃ z, θ b z ≠ 0) → IsThetaFrame Xo.univ.t.PP B (fun b => F.u k (P b)) (fun b z => (F.ex k (P b) z).left) θ → ∃ (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ) (κ : (Fin m → ℂ) → ℂ), RigFrame F k B P fr ∧ DifferentiableOn ℂ κ B ∧ ∀ b ∈ B, κ b ≠ 0 ∧ SecVal F k (P b) (y b).x (y b).s (fun z => κ b * θ b z) (fun j z => fr j (b, z)) := by
  first | exact @GlobalTheory.GenFactor.exists_holomorphic_factor | exact GlobalTheory.GenFactor.exists_holomorphic_factor | (intros; apply GlobalTheory.GenFactor.exists_holomorphic_factor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousOnHolomorphicFramedFamily

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm.Hol

theorem continuousOn_form {V : Type} [TopologicalSpace V] {g : ℕ} {B : Set V} (h τ : V → Matrix (Fin g) (Fin g) ℂ)
    (hh : ∀ i j, ContinuousOn (fun b => h b i j) B) (hτ : ∀ i j, ContinuousOn (fun b => τ b i j) B)
    (hp : ∀ b ∈ B, ((τ b).map Complex.im).PosDef) :
    ContinuousOn (fun b => ((τ b).map Complex.im).det) B ∧ ∀ i j, ContinuousOn (fun b =>
      ((h b)ᵀ * (((τ b).map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * (h b).map (starRingEnd ℂ)) i j) B := by
  simp only [continuousOn_iff_continuous_restrict] at hh hτ ⊢
  have h1 : Continuous fun b : B => h b := continuous_matrix hh
  have h2 : Continuous fun b : B => (τ b).map Complex.im :=
    (continuous_matrix hτ : Continuous fun b : B => τ b).matrix_map Complex.continuous_im
  have h3 : Continuous fun b : B => ((τ b).map Complex.im)⁻¹ := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    exact (h2.matrix_det.inv₀ fun b => (hp b b.2).det_pos.ne').smul h2.matrix_adjugate
  refine ⟨h2.matrix_det, fun i j => ?_⟩
  exact ((h1.matrix_transpose.matrix_mul (h3.matrix_map Complex.continuous_ofReal)).matrix_mul
    (h1.matrix_map Complex.continuous_conj)).matrix_elem i j

theorem exists_continuous_form_mean {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (k : Fin F.n)
    (hty : IsTypeFn H Dw.p Dw.q ty) {A : Type} [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) {m : ℕ}
    {B : Set (Fin m → ℂ)} (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ))
    (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (hB : IsOpen B)
    (hφ : ∀ a, DifferentiableOn ℂ (fun b => toC (φ b a)) B) (hy : ∀ b ∈ B, FrMap (φ b) yA (y b))
    (hP : IsHolPeriods (F.Di k) ty B P) (hx : ∀ b ∈ B, (y b).x = F.u k (P b)) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) :
    ∃ (B' : Set (Fin m → ℂ)) (Hm : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ) (μ : (Fin m → ℂ) → ℝ),
      IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ (∀ i j, ContinuousOn (fun b => Hm b i j) B') ∧ ContinuousOn μ B' ∧
      ∀ b ∈ B', (∀ v w, (hermForm (Hm b) (P b v) (P b w)).im = (F.Di k).EF v w) ∧
        AHMean F k (P b) (y b).x (y b).s (μ b) := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hB b₀ hb₀
  obtain ⟨hg, -⟩ := (GlobalTheory.PeriodExists.typeFn_period_exist E H (F.Di k)).2.1 g ty
    (by rw [(F.sig k).1, (F.sig k).2]; exact hty)
  obtain ⟨bas, hbas, -⟩ := GlobalTheory.exists_symplectic_basis_adapted_mod_eight E H (F.Di k) g hg
  obtain ⟨hR1, hR2⟩ := GlobalTheory.RiemannRel.riemann_relations E H (F.Di k) g ty bas hbas
  have hP' : IsHolPeriods (F.Di k) ty (Metric.ball b₀ ε) P :=
    ⟨fun b hb => hP.1 b (hsub hb), fun v => (hP.2 v).mono hsub⟩
  choose! h τ hn hdet hsym hpos _ using fun b hb => hR1 _ (hP'.1 b hb)
  have hhol := hR2 m _ P h τ hP' hn
  obtain ⟨c₁, c₂, hc₁, hc₂, hθ⟩ := F.theta k m _ P bas (-1) h τ Metric.isOpen_ball
    (convex_ball b₀ ε).isPreconnected hP' (fun a b => by rw [hbas]; simp) (fun b hb => ⟨hpos b hb, hn b hb⟩)
  obtain ⟨t1, t2⟩ := GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g c₁ c₂ hc₁ hc₂
  have t3 := t2 m _ h τ Metric.isOpen_ball (fun b hb => ⟨hsym b hb, hpos b hb⟩) hhol
  obtain ⟨fr, κ, hfr, hκ, hval⟩ := GlobalTheory.T.exists_holomorphicFactor_generator_thetaSection E H Dw l Xo c σ σ' g ty F k A yA m _ φ y P
    (fun b z => thetaChar (τ b) c₁ c₂ (h b *ᵥ z)) Metric.isOpen_ball
    (fun a => (hφ a).mono hsub) (fun b hb => hy b (hsub hb)) hP' (fun b hb => hx b (hsub hb))
    (fun z => DifferentiableOn.comp (f := fun b : Fin m → ℂ => ((b, z) : (Fin m → ℂ) × (Fin g → ℂ)))
      (g := fun bz : (Fin m → ℂ) × (Fin g → ℂ) => thetaChar (τ bz.1) c₁ c₂ (h bz.1 *ᵥ bz.2))
      t3 (by fun_prop) fun b hb => ⟨hb, trivial⟩)
    (fun b hb => by
      obtain ⟨-, w, hw⟩ := t1 _ (hsym b hb) (hpos b hb)
      obtain ⟨z, hz⟩ := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (hdet b hb)) w
      exact ⟨z, by rw [hz]; exact hw⟩) hθ
  obtain ⟨c1, c2⟩ := continuousOn_form h τ (fun i j => (hhol i j).1.continuousOn)
    (fun i j => (hhol i j).2.continuousOn) hpos
  refine ⟨Metric.ball b₀ ε, _, fun b => ‖κ b‖ ^ 2 * (Real.sqrt (2 ^ g * ((τ b).map Complex.im).det))⁻¹,
    Metric.isOpen_ball, Metric.mem_ball_self hε, hsub, c2, ?_, fun b hb => ⟨?_, ?_⟩⟩
  · refine (hκ.continuousOn.norm.pow 2).mul (ContinuousOn.inv₀ (continuousOn_const.mul c1).sqrt fun b hb => ?_)
    have := (hpos b hb).det_pos
    positivity
  · obtain ⟨Hm, -, -, hH⟩ := (hP'.1 b hb).2.2.2.2
    rw [← (GlobalTheory.RiemannForm.herm_eq_of_normalised E H _ g _ bas _ (h b) (τ b) Hm hbas (hP'.1 b hb) (hn b hb)
      ⟨hsym b hb, hpos b hb⟩ hH).1]
    exact hH
  · exact GlobalTheory.T.meanSquare_multiple_thetaSection_family E H Dw l Xo σ' g ty F k m _ P fr bas b (h b) (τ b) c₁ c₂ _ _ (κ b) hb (hP'.1 b hb) hbas (hdet b hb)
      (hsym b hb) (hpos b hb) (hn b hb) hc₁ hc₂ hfr (hx b (hsub hb)) (hval b hb).1 (hval b hb).2

end GlobalTheory.FrameNorm.Hol

theorem GlobalTheory.FrameNorm.fn_continuousOn_hol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → ∀ i, ContinuousOn (fun b => |fn σ (y b) i|) B := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn _ hpin σ hσ A _ _ yA m B φ y hB hφ hy i b₀ hb₀
  obtain ⟨hr, hty, hcov, -, -, g, e, F, ik, ψ, hef, hun⟩ := hU σ hσ
  obtain ⟨B₁, k, P, hB₁, hb₁, hs₁, hP, hyP⟩ := GlobalTheory.T.exists_holomorphic_periods_adapted E H Dw l Xo c σ g e F A yA m B φ y hB hφ hy b₀ hb₀
  obtain ⟨k₀, x₁, t₁, ht₁⟩ := hcov (y b₀)
  obtain ⟨P₁, hP₁, hP₁', hx₁, -⟩ := hun k₀ x₁
  obtain rfl : ik k₀ = k := F.disj _ _ _ _ hP₁' (hP.1 b₀ hb₁) (hx₁.symm.trans (ht₁.1.symm.trans (hyP b₀ hb₁).1))
  obtain ⟨d, hd, horth⟩ := GlobalTheory.T.period_eq_triangular_orthonormal_alt E H Dw l c σ g e _ r ((U σ).X k₀) (ψ k₀) hσ (F.sig _).1 (F.sig _).2 hr
    (hty k₀).1 (hty k₀).2 (hef k₀)
    (GlobalTheory.T.im_neg_of_frame_period_vector E H Dw l c σ g e _ r ((U σ).X k₀) (ψ k₀) hσ hr (hty k₀).1 (hty k₀).2 (hef k₀) x₁.1 x₁.2 P₁ hP₁ hP₁')
  obtain ⟨B₂, Hm, μ, hB₂, hb₂, hs₂, hHm, hμ, hAH⟩ := GlobalTheory.FrameNorm.Hol.exists_continuous_form_mean F (ik k₀)
    ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw g e) yA φ y P hB₁ (fun a => (hφ a).mono hs₁)
    (fun b hb => hy b (hs₁ hb)) hP (fun b hb => (hyP b hb).1) hb₁
  have key : ∀ b ∈ B₂, ∃ S : Matrix (Fin g) (Fin g) ℂ, (IsUnit S.det ∧
      (∀ j j', S j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧
      Hm b = Sᵀ * ((Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) * S.map (starRingEnd ℂ))) ∧
      (∀ j, |fn σ (y b) (some (e j))| = ‖S j j‖ * Real.sqrt (2 * Real.pi * xR)) ∧
      |fn σ (y b) none| = Real.sqrt (μ b) := by
    intro b hb
    have hp := hP.1 b (hs₂ hb)
    obtain ⟨x₀, hx₀, hunit, S, hS, hsupp, hper, hform⟩ := horth _ hp
    obtain ⟨P₀, hP₀, hP₀', hux, hud, hmean⟩ := hun k₀ ⟨x₀, hx₀⟩
    have hPS : ∀ a, P₀ a = S *ᵥ P b a := fun a => funext fun j => (hP₀ a j).trans (hper a j).symm
    obtain ⟨t, ht, htS⟩ := GlobalTheory.T.triangular_frame_change_of_triangular_period E H Dw l Xo c σ g e F _ (P b) P₀ S (y b) ((U σ).un k₀ ⟨x₀, hx₀⟩) hp hP₀' hPS hsupp
      (hyP b (hs₂ hb)).1 hux (hyP b (hs₂ hb)).2 hud
    have hfn := hpin.1 σ hσ k₀ ⟨x₀, hx₀⟩ hunit t (y b) ht
    refine ⟨S, ⟨hS, hsupp, ?_⟩, fun j => ?_, ?_⟩
    · refine GlobalTheory.UnitDet.eq_of_im_hermForm_eq _ hp.2.2.2.1 _ _ ?_
      rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
      rw [← GlobalTheory.UnitDet.hermForm_mulVec, hform, (hAH b hb).1]
    · rw [hfn, ← htS j]
      rfl
    · obtain ⟨hxx, -, pm, p1, p2, p3⟩ := ht
      have hbc : SecBC (RingHom.id ℂ) (toC (t none : CAt σ)) ((U σ).un k₀ ⟨x₀, hx₀⟩).x (y b).x
          ((U σ).un k₀ ⟨x₀, hx₀⟩).s (y b).s := ⟨pm, p1, p2.trans (by rw [GlobalTheory.Frames.SecCalc.spMap_id']; exact (Category.comp_id _).symm), p3⟩
      have h1 := GlobalTheory.T.appellHumbertMeanSquare_eq_of_proportional_sections E H Dw l Xo _ g _ F _ P₀ (P b) S _ _ _ _ _ 1 (μ b) hP₀' hp hPS hux hxx hbc (hmean hunit)
        (hAH b hb).2
      rw [hfn, h1, mul_one, Real.sqrt_sq (norm_nonneg _)]
      exact mul_one _
  choose! S hS hlie hgen using key
  refine ContinuousAt.continuousWithinAt (ContinuousOn.continuousAt (s := B₂) ?_ (hB₂.mem_nhds hb₂))
  cases i with
  | none => exact hμ.sqrt.congr hgen
  | some s =>
    obtain ⟨j, rfl⟩ := e.surjective s
    refine ((GlobalTheory.T.continuousOn_norm_diag_of_triangular_factor g (E →+* ℂ) _ (fun j => (e j).1) (fun j => (e j).2) d B₂ S Hm (fun j j' h1 h2 => ?_) hd hHm hS
      j).mul continuousOn_const).congr fun b hb => hlie b hb j
    exact e.injective (Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2))
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousOnHolomorphicFramedFamilyStatement

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

theorem _root_.GlobalTheory.T.frameNorms_continuousOn_holomorphic_framedFamily : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → ∀ i, ContinuousOn (fun b => |fn σ (y b) i|) B := by
  first | exact @GlobalTheory.FrameNorm.fn_continuousOn_hol | exact GlobalTheory.FrameNorm.fn_continuousOn_hol | (intros; apply GlobalTheory.FrameNorm.fn_continuousOn_hol <;> assumption)
end
end
