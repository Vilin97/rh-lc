module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFrameFamilyOfHolomorphicPeriodMapsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CongruenceActionMemFrameOrbit
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryMatrixOfLatticeIsometry
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicChartLiftHolomorphicPeriodMaps

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option autoImplicit false

theorem GlobalTheory.ShFam.chart_lift_periods_of_openPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (i : Fin Fu.n) (B : Set (ReciprocityTheory.L2DbarEstimates.V X.dim)) (P : ReciprocityTheory.L2DbarEstimates.V X.dim → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B ∧ c'.e y ∈ B ∧ B ⊆ c'.e.target ∧ (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) ∧ (∀ x, DifferentiableOn ℂ (fun b => P b x) B) ∧ ∀ b ∈ B, ∃ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), cxPt T.Z q = cxOf e σ hj (c'.e.symm b) ∧ Fu.u i (P b) = q.x := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ g ty Fu X j hj hjo y hy c' hyc
  have := T.Z.jQ_open
  have : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  let L := EuclideanSpace.equiv (Fin X.dim) ℂ
  have hsy := GlobalTheory.TrueCx.TorHolo.isHolTo_symm c'
  have hsj := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hsy j
  have hB₀ := (hsj T.Z.jQ.opensRange 0).1
  set B₀ := {b ∈ c'.e.target | ⊤ ≤ ((c'.e.symm b).1 ≫ j) ⁻¹ᵁ T.Z.jQ.opensRange} with hB₀def
  have hb₀ : c'.e y ∈ B₀ := by
    refine ⟨c'.e.map_source hyc, ?_⟩
    rw [c'.e.left_inv hyc]
    intro s _
    have h1 : y.1 s ∈ openPart j := hy (Set.mem_univ s)
    exact not_not.1 h1
  have hw : ∀ b ∈ B₀, ∃ w : Sp ℂ ⟶ Xo.XF c, w ≫ T.Z.jQ = (c'.e.symm b).1 ≫ j := fun b hb =>
    ⟨IsOpenImmersion.lift T.Z.jQ _ (by rintro _ ⟨s, rfl⟩; exact hb.2 (Set.mem_univ s)), IsOpenImmersion.lift_fac _ _ _⟩
  have : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨(hw _ hb₀).choose⟩
  choose! w hw using hw
  have hwh : IsHolTo B₀ w := GlobalTheory.TrueCx.TorHolo.isHolTo_of_openImmersion T.Z.jQ
    (LocLift.isHolTo_congr (LocLift.isHolTo_mono hsj hB₀ fun b hb => hb.1) hw)
  have hyh := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hwh (Limits.pullback.fst _ _)
  have hsnd : ∀ b ∈ B₀, w b ≫ Limits.pullback.snd _ _ = spMap σ := fun b hb => by
    rw [← T.Z.jQ_over, ← Category.assoc, hw b hb]
    exact (Category.assoc _ _ _).trans (cxOf e σ hj (c'.e.symm b)).2
  have hB₁ : IsOpen (L.symm ⁻¹' B₀) := hB₀.preimage L.symm.continuous
  obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ := Fu.lift X.dim (L.symm ⁻¹' B₀) (fun x => w (L.symm x) ≫ Limits.pullback.fst _ _) hB₁
    (fun x hx => by
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hsnd _ hx, ← Spec.map_comp]
      rfl)
    (LocLift.isHolTo_comp hyh hB₁ L.symm.differentiableOn fun x hx => hx) (L (c'.e y))
    (by simpa only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hb₀)
  refine ⟨i, L ⁻¹' B', fun v => P (L v), hB'.preimage L.continuous, hb', fun v hv => ?_, fun v hv => hP.1 _ hv,
    fun x => (hP.2 x).comp L.differentiableOn fun v hv => hv, fun b hb => ?_⟩
  · have := hsub hv
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at this
    exact this.1
  · have hb1 := hsub hb
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at hb1
    have h2 := hu _ hb
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h2
    have ho : (w b ≫ Limits.pullback.fst _ _) ≫ Xo.s = sOf c (CAt σ) := by
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hsnd b hb1]
      exact OpenReg.spMap_comp _ _
    obtain ⟨q, hq⟩ : ∃ q : FrPt Xo c (CAt σ), q.x = w b ≫ Limits.pullback.fst _ _ := GlobalTheory.FlagTan.exists_frPt _ ho
    refine ⟨q, Subtype.ext ?_, h2.trans hq.symm⟩
    have h3 : GlobalTheory.AllWt.ptF (S := CAt σ) q = w b :=
      Limits.pullback.hom_ext ((ptF_fst q).trans hq) ((ptF_snd q).trans (hsnd b hb1).symm)
    exact (congrArg (· ≫ T.Z.jQ) h3).trans (hw b hb1)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicChartLiftHolomorphicPeriodMapsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix


theorem _root_.GlobalTheory.T.algebraicChart_lift_holomorphic_periodMaps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (i : Fin Fu.n) (B : Set (ReciprocityTheory.L2DbarEstimates.V X.dim)) (P : ReciprocityTheory.L2DbarEstimates.V X.dim → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B ∧ c'.e y ∈ B ∧ B ⊆ c'.e.target ∧ (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) ∧ (∀ x, DifferentiableOn ℂ (fun b => P b x) B) ∧ ∀ b ∈ B, ∃ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), cxPt T.Z q = cxOf e σ hj (c'.e.symm b) ∧ Fu.u i (P b) = q.x := by
  first | exact @GlobalTheory.ShFam.chart_lift_periods_of_openPart | exact GlobalTheory.ShFam.chart_lift_periods_of_openPart | (intros; apply GlobalTheory.ShFam.chart_lift_periods_of_openPart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMapMemberEqFramePeriodMapLinearChange

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointLift

open ReciprocityTheory.ChartRestriction.G.FD

theorem pm_lift_pointwise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (W : GlobalTheory.ArcQ.UnfWit U), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → Function.Injective W.ik → ∀ (k : U.Comp) (Q : (W.F.Di (W.ik k)).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di (W.ik k)) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) Q → ∀ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), W.F.u (W.ik k) Q = q.x → ∃ x' : (U.X k).dom, (U.un k x').x = q.x ∧ ∃ h : (Fin W.g → ℂ) ≃ₗ[ℂ] (Fin W.g → ℂ), ∀ a, Q a = h (W.Pm k x' a) := by
  intro E _ _ _ H Dw l Xo c σ r U W hσ hU hinj k Q hQ q hq
  obtain ⟨k₁, x₁, t, hB⟩ := hU.2.2.1 q
  have hx₁ : (U.un k₁ x₁).x = W.F.u (W.ik k₁) (W.Pm k₁ x₁) := (W.lie k₁ x₁).1
  have hk : k₁ = k := hinj (W.F.disj _ _ _ _ (W.period k₁ x₁) hQ (by rw [← hx₁, ← hB.1, hq]))
  subst hk
  obtain ⟨gam, h, hEF, -, -, hgh⟩ := (W.F.fibre _ Q (W.Pm k₁ x₁) hQ (W.period k₁ x₁)).1
    (by rw [hq, ← hx₁, hB.1])
  let φL : (W.F.Di (W.ik k₁)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k₁).Λ.subtype ∘ₗ (W.φ k₁).toLinearMap
  have hφi : Function.Injective φL := (U.X k₁).Λ.injective_subtype.comp (W.φ k₁).injective
  have hrange : Set.range φL = ((U.X k₁).Λ : Set (Fin r → E)) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (W.φ k₁ a).2
    · intro hv
      exact ⟨(W.φ k₁).symm ⟨v, hv⟩, by simp [φL]⟩
  have hspan : Submodule.span E (Set.range φL) = ⊤ := by rw [hrange]; exact (U.X k₁).Λ_span
  have hcc : cc (-(U.X k₁).ξ0) = -(-(U.X k₁).ξ0) := by
    have h0 := (U.X k₁).ξ0_im
    unfold cc at h0 ⊢
    rw [map_neg, h0]
  have hl : Function.Injective φL ∧ Submodule.span E (Set.range φL) = ⊤ ∧
      (∀ a b, cc ((U.X k₁).Gm a b) = (U.X k₁).Gm b a) ∧ (U.X k₁).Gm.det ≠ 0 ∧
      ∀ x y, (((W.F.Di (W.ik k₁)).EF x y : ℤ) : ℚ) =
        Algebra.trace ℚ E (-(U.X k₁).ξ0 * herm (U.X k₁).Gm (φL x) (φL y)) :=
    ⟨hφi, hspan, (U.X k₁).Gm_herm, (U.X k₁).Gm_det, fun x y => W.iso k₁ x y⟩
  obtain ⟨γ, hγh, hγφ⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry E H _ _ r (-(U.X k₁).ξ0) (U.X k₁).Gm φL φL gam
    hcc hl hl hEF
  have hinv : ∀ v : Fin r → E, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hinv' : ∀ v : Fin r → E, (γ : Matrix (Fin r) (Fin r) E) *ᵥ
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hγi : IsUStab (U.X k₁).Gm (U.X k₁).Λ γ⁻¹ := by
    refine ⟨fun u v => ?_, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · rw [← hγh, hinv', hinv']
    · obtain ⟨b, hb⟩ : v ∈ Set.range φL := by rw [hrange]; exact hv
      have e : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v = φL (gam.symm b) := by
        rw [← hb, ← LinearEquiv.apply_symm_apply gam b, hγφ, hinv, LinearEquiv.apply_symm_apply]
      rw [e]
      exact (W.φ k₁ (gam.symm b)).2
    · obtain ⟨a, ha⟩ : _ ∈ Set.range φL := by rw [hrange]; exact hv
      have e : v = φL (gam a) := by rw [hγφ, ha, hinv']
      rw [e]
      exact (W.φ k₁ (gam a)).2
  let x' : (U.X k₁).dom := ⟨lact γ⁻¹ x₁.1, GlobalTheory.MajInv.lact_mem_dom _ hγi x₁.2⟩
  have hPm : ∀ a, W.Pm k₁ x' a = W.Pm k₁ x₁ (gam a) := by
    intro a
    funext j
    rw [W.Pm_eq, W.Pm_eq]
    have e : (W.φ k₁ a : Fin r → E) = ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        (W.φ k₁ (gam a) : Fin r → E) := by
      change φL a = _ *ᵥ φL (gam a)
      rw [hγφ, hinv]
    rw [e]
    exact GlobalTheory.CongrOrbit.perFr_lact _ _ _ hγi.1 _ _ _
  have hQx : ∀ a, W.Pm k₁ x' a = h (Q a) := fun a => by rw [hPm, hgh]
  have hu : W.F.u (W.ik k₁) Q = W.F.u (W.ik k₁) (W.Pm k₁ x') :=
    (W.F.fibre _ Q (W.Pm k₁ x') hQ (W.period k₁ x')).2
      ⟨LinearEquiv.refl _ _, h, fun a b => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩,
        fun a => hQx a⟩
  refine ⟨x', by rw [(W.lie k₁ x').1, ← hu, hq], h.symm, fun a => ?_⟩
  rw [hQx, LinearEquiv.symm_apply_apply]

end GlobalTheory.PointLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMapMemberEqFramePeriodMapLinearChangeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix


theorem _root_.GlobalTheory.T.periodMap_member_eq_frame_periodMap_linear_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (W : GlobalTheory.ArcQ.UnfWit U), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → Function.Injective W.ik → ∀ (k : U.Comp) (Q : (W.F.Di (W.ik k)).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di (W.ik k)) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) Q → ∀ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), W.F.u (W.ik k) Q = q.x → ∃ x' : (U.X k).dom, (U.un k x').x = q.x ∧ ∃ h : (Fin W.g → ℂ) ≃ₗ[ℂ] (Fin W.g → ℂ), ∀ a, Q a = h (W.Pm k x' a) := by
  first | exact @GlobalTheory.PointLift.pm_lift_pointwise | exact GlobalTheory.PointLift.pm_lift_pointwise | (intros; apply GlobalTheory.PointLift.pm_lift_pointwise <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFlagDomainFrameLiftAlgebraicChart

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

theorem exists_analytic_frame_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (k' : U.Comp) (s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)), AnalyticAt ℂ s (c'.e y) ∧ ∀ᶠ w in 𝓝 (c'.e y), ∃ hs : s w ∈ (U.X k').dom, cxPt T.Z (U.un k' ⟨s w, hs⟩) = cxOf e σ hj (c'.e.symm w) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU X j hj hjo y hy c' hyc
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with hr | hr
  · obtain ⟨W⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf _ _ _ _ _ _ _ _ U hU
    obtain ⟨i, B, P, hB, hb₀, -, hper, -, hq⟩ := GlobalTheory.T.algebraicChart_lift_holomorphic_periodMaps E H Dw l Xo c O β Y T F e σ W.g _ W.F X j hj hjo y hy c' hyc
    obtain ⟨q₀, hq₀, hu₀⟩ := hq _ hb₀
    have hne : ¬ LiesIn (cxOf e σ hj y) (genBd T.Z) := by
      rw [← c'.e.left_inv hyc, ← hq₀]; exact not_liesIn_cxPt q₀
    obtain ⟨k, x, -, hkx⟩ := GlobalTheory.HodgeSmooth.exists_orth (Z := T.Z) hσ hU hne
    have hg : IsEmpty (Fin W.g) := by
      refine ⟨fun a => ?_⟩
      have := (W.e a).2.2
      simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult] at this
      split_ifs at this <;> omega
    refine ⟨k, fun _ => x.1, analyticAt_const, Filter.mem_of_superset (hB.mem_nhds hb₀) fun w hw => ⟨x.2, ?_⟩⟩
    obtain ⟨q, hq1, hq2⟩ := hq w hw
    have hfib : W.F.u i (P (c'.e y)) = W.F.u i (P w) :=
      (W.F.fibre i _ _ (hper _ hb₀) (hper w hw)).2 ⟨LinearEquiv.refl _ _, LinearEquiv.refl _ _, fun _ _ => rfl,
        fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, fun a => funext fun t => (hg.false t).elim⟩
    have e1 : cxPt T.Z q₀ = cxPt T.Z q := cxPt_congr (hu₀.symm.trans (hfib.trans hq2))
    rw [← hq1, ← e1, hq₀, c'.e.left_inv hyc]
    exact hkx
  · obtain ⟨W, hinj⟩ := GlobalTheory.HodgeSmooth.exists_unfWit_inj hσ hU hr
    obtain ⟨i, B, P, hB, hb₀, -, hper, hdiff, hq⟩ := GlobalTheory.T.algebraicChart_lift_holomorphic_periodMaps E H Dw l Xo c O β Y T F e σ W.g _ W.F X j hj hjo y hy c' hyc
    obtain ⟨q₀, -, hu₀⟩ := hq _ hb₀
    obtain ⟨k, x₁, t, hbor⟩ := hU.2.2.1 q₀
    have hk : W.ik k = i := W.F.disj _ _ _ _ (W.period k x₁) (hper _ hb₀)
      (((W.lie k x₁).1.symm.trans hbor.1.symm).trans hu₀.symm)
    subst hk
    obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
    obtain ⟨hp0, hty⟩ := hU.2.1 k
    have hmult : ∀ τ : E →+* ℂ, Formalism.L2.PjFree.relab c σ τ ∉ (U.X k).Ψ → Dw.mult τ = (U.X k).p0 := by
      intro τ hτ
      rw [hp0]
      exact if_neg fun h => hτ ((hty _).2 ((hrt τ).2 h))
    have hrep : ∀ b ∈ B, ∀ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), W.F.u (W.ik k) (P b) = q.x →
        ∃ x' : (U.X k).dom, (U.un k x').x = q.x ∧ ∃ h : (Fin W.g → ℂ) ≃ₗ[ℂ] (Fin W.g → ℂ), ∀ v, P b v =
          h (fun j => Formalism.L2.PjFree.perFr (U.X k) x'.1 (W.φ k v : Fin (Dw.p + Dw.q) → E)
            (Formalism.L2.PjFree.relab c σ (W.e j).1) ((W.e j).2 : ℕ)) := by
      intro b hb q hqu
      obtain ⟨x', hx', h, hh⟩ := GlobalTheory.T.periodMap_member_eq_frame_periodMap_linear_change E H Dw l Xo c σ _ U W hσ hU hinj k (P b) (hper b hb) q hqu
      exact ⟨x', hx', h, fun v => (hh v).trans (congrArg h (funext fun j => W.Pm_eq k x' v j))⟩
    obtain ⟨s, hs, hev⟩ := GlobalTheory.T.exists_analytic_frame_family_of_holomorphic_periodMaps E (Dw.p + Dw.q) (U.X k) _ (W.φ k) W.g (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1)
      (fun j => ((W.e j).2 : ℕ)) X.dim B P (c'.e y) hB hb₀ (fun b hb => (hper b hb).1) hdiff
      (fun ρ hρ m hm => by
        obtain ⟨τ', hτ'⟩ := hbij.2 (conjEmb ρ)
        have hn : Formalism.L2.PjFree.relab c σ τ' ∉ (U.X k).Ψ := by
          rw [hτ']
          exact ((U.X k).cmType ρ).1 hρ
        have hm' : m < Dw.mult τ' := by rw [hmult τ' hn]; exact hm
        exact ⟨W.e.symm ⟨τ', ⟨m, hm'⟩⟩, by rw [Equiv.apply_symm_apply]; exact hτ', by rw [Equiv.apply_symm_apply]⟩)
      (fun j j' h1 h2 => by
        have h1' := hbij.1 h1
        exact W.e.injective (Sigma.ext h1' ((Fin.heq_ext_iff (by rw [h1'])).2 h2)))
      (fun j hj' => by
        exact lt_of_lt_of_eq (W.e j).2.2 (hmult _ hj'))
      (fun b hb => by
        obtain ⟨q, -, hqu⟩ := hq b hb
        obtain ⟨x', -, h, hh⟩ := hrep b hb q hqu
        exact ⟨x'.1, x'.2, h, hh⟩)
    refine ⟨k, s, hs, (hev.and (hB.mem_nhds hb₀)).mono fun w hw => ⟨hw.1.1, ?_⟩⟩
    obtain ⟨q, hq1, hqu⟩ := hq w hw.2
    obtain ⟨x', hx', h, hh⟩ := hrep w hw.2 q hqu
    obtain ⟨h1, h2⟩ := hw.1.2 x'.1 x'.2 ⟨h, hh⟩
    rw [← hq1]
    exact cxPt_congr ((GlobalTheory.TrueCx.PointWell.pt_eq_of_block hU hσ k ⟨s w, hw.1.1⟩ x' h1 h2).trans hx')

end GlobalTheory.LieBase
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFlagDomainFrameLiftAlgebraicChartStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix


theorem _root_.GlobalTheory.T.exists_analytic_flagDomain_frame_lift_algebraicChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (k' : U.Comp) (s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)), AnalyticAt ℂ s (c'.e y) ∧ ∀ᶠ w in 𝓝 (c'.e y), ∃ hs : s w ∈ (U.X k').dom, cxPt T.Z (U.un k' ⟨s w, hs⟩) = cxOf e σ hj (c'.e.symm w) := by
  first | exact @GlobalTheory.LieBase.exists_analytic_frame_lift | exact GlobalTheory.LieBase.exists_analytic_frame_lift | (intros; apply GlobalTheory.LieBase.exists_analytic_frame_lift <;> assumption)
end
end
