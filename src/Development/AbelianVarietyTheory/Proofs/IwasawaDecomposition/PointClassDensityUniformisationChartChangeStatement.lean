module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCompEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Formalism.DegreeFormula.Statement
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfA
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CurvNormNonneg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HPInvEqForm
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodicSchwarzLemma
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityCompHolomorphicNormSqDet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationContinuousOnAnalyticAtChaStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricLieFramesSmoothHermitianOffBoundary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationImageBoundedDomainEqOpenPartStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopChartIndependent

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical

open Filter Topology AlgebraicGeometry CategoryTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ChernWeilLine

theorem cInfAt_eventually {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {f : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) : ∀ᶠ z in 𝓝 y, CInfAt f z := by
  obtain ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have hW := (isOpen_ptsIn (p := p) (σ := σ) W).mem_nhds h₁
  have hc : ContinuousAt (fun z a => ev p σ W (g a) z) y :=
    continuousAt_pi.2 fun a => (continuousOn_ev (g a)).continuousAt hW
  filter_upwards [hW, hc.preimage_mem_nhds (h₂.mem_nhds h₃), h₅.eventuallyEq_nhds] with z hz hzO hz5
  exact ⟨W, ι, i, g, F, O, hz, h₂, hzO, h₄, hz5⟩

theorem chernTop_congr {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ)
    {G G' : V n → Mat m ℂ} {v : V n} (h : G =ᶠ[𝓝 v] G') : chernTop R G v = chernTop R G' v := by
  have hc : ∀ x : ι × ℕ, chernPoly (fun u => G u x.1) v x.2 = chernPoly (fun u => G' u x.1) v x.2 := by
    intro x
    unfold chernPoly curvPoly
    simp only [curv_congr (h.mono fun u hu => congrFun hu x.1)]
  simp only [chernTop, hc]

end GlobalTheory.ChernWeilLine
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BetaLowerAndSmul

section

@[expose] public section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.PoincareLower

open Topology Filter

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end General

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem isOpen_domFlat : IsOpen (DomFlat ι p q) := by
  refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
  refine Filter.eventually_all.2 fun τ => ExhB.posDef_eventually
    (fun v : ι × Fin p × Fin q → ℂ => 1 - (unflat v τ)ᴴ * unflat v τ) (fun i j => ?_)
    (fun v => isHermitian_one.sub (isHermitian_conjTranspose_mul_self _)) x0 (hx0 τ)
  simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, unflat, Matrix.of_apply]
  fun_prop

variable {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (B : BdData ι p q Γ)

end GlobalTheory.PoincareLower
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricLieFramesSmoothHermitianOffBoundaryStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.hodgeMetric_lie_frames_smooth_hermitian_off_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → IsMetricOn Eb (openPart j) (lieGram e U hj f₀ A₀) := by
  first | exact @GlobalTheory.LieBase.isMetricOn_lieGram | exact GlobalTheory.LieBase.isMetricOn_lieGram | (intros; apply GlobalTheory.LieBase.isMetricOn_lieGram <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointClassDensityUniformisationChartChange

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

open Filter Topology GlobalTheory.GoodMetric
open scoped ComplexOrder



theorem GlobalTheory.UnifDens.chernTop_unif_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ ch : AlgChart X.str (σ.comp e.toRingHom) X.dim, ψ (GlobalTheory.UnifDens.flatL h v) ∈ ch.e.source → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) v = Complex.normSq (LinearMap.det (fderiv ℂ (fun u => ch.e (ψ (GlobalTheory.UnifDens.flatL h u))) v : ReciprocityTheory.L2DbarEstimates.V X.dim →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim)) * chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ch.e.symm u)) (ch.e (ψ (GlobalTheory.UnifDens.flatL h v))) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv ch hch A hA
  have hholo := GlobalTheory.T.componentUniformisation_continuousOn_analyticAt_charts E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hM := GlobalTheory.T.hodgeMetric_lie_frames_smooth_hermitian_off_boundary E H Dw l Xo c O β Y T F e σ U hσ hU (Φ.C k) X j f f₀ Eb A₀ hj hL
  have hyO : ψ (GlobalTheory.UnifDens.flatL h v) ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j) := by
    rw [← GlobalTheory.T.uniformisation_image_boundedDomain_eq_openPart E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ]
    exact ⟨_, hv, rfl⟩
  set y := ψ (GlobalTheory.UnifDens.flatL h v) with hydef
  let K : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ := fun u => lieGram e U hj f₀ A₀ A (ch.e.symm u)
  let φ : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.L2DbarEstimates.V X.dim := fun u => ch.e (ψ (GlobalTheory.UnifDens.flatL h u))
  have hφ : AnalyticAt ℂ φ v :=
    (hholo.2 _ hv ch hch).comp (show AnalyticAt ℂ (GlobalTheory.UnifDens.flatL h) v from (GlobalTheory.UnifDens.flatL h).toContinuousLinearMap.analyticAt v)
  have hy'' : ch.e.symm (ch.e y) = y := ch.e.left_inv hch
  have hK2 : ∀ τ, MContDiffAt 2 (fun u => K u τ) (φ v) := by
    intro τ a b
    have hsm := hM.smooth y hyO A hA τ a b
    have hre := GlobalTheory.ChernWeilLine.cInfAt_eventually hsm.1
    have him := GlobalTheory.ChernWeilLine.cInfAt_eventually hsm.2
    have hn : ∀ {g : CxPts X.str (σ.comp e.toRingHom) → ℝ}, (∀ᶠ z in 𝓝 y, CInfAt g z) →
        ContDiffAt ℝ 2 (g ∘ ch.e.symm) (ch.e y) := by
      intro g hg
      have hs : ch.e.target ∩ ch.e.symm ⁻¹' {z | CInfAt g z} ∈ 𝓝 (ch.e y) := by
        refine Filter.inter_mem (ch.e.open_target.mem_nhds (ch.e.map_source hch)) ?_
        exact (ch.e.continuousAt_symm (ch.e.map_source hch)).preimage_mem_nhds (hy''.symm ▸ hg)
      exact ((contDiffOn_chart (fun z hz => hz) ch).contDiffAt hs).of_le (by norm_cast)
    have h1 := (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn hre)).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn him)).mul (contDiffAt_const (c := Complex.I)))
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    simp only [Function.comp_apply, Complex.ofRealCLM_apply, K]
    exact (Complex.re_add_im _).symm
  have hKu : ∀ τ, IsUnit (K (φ v) τ).det := by
    intro τ
    have hp := hM.posDef y hyO A hA τ
    show IsUnit (lieGram e U hj f₀ A₀ A (ch.e.symm (ch.e y)) τ).det
    rw [hy'']
    exact (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit
  have key := GlobalTheory.ChernPull.chernTop_comp (pointPoly H Dw) K φ v hφ hK2 hKu
  have hcont : ContinuousAt (fun u => ψ (GlobalTheory.UnifDens.flatL h u)) v :=
    (hholo.1.continuousAt (GlobalTheory.PoincareLower.isOpen_domFlat.mem_nhds hv)).comp
      (GlobalTheory.UnifDens.flatL h).continuous.continuousAt
  have hg : (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) =ᶠ[𝓝 v] fun w => K (φ w) := by
    filter_upwards [hcont.preimage_mem_nhds (ch.e.open_source.mem_nhds hch)] with w hw
    simp only [K, φ, ch.e.left_inv hw]
  rw [GlobalTheory.ChernWeilLine.chernTop_congr _ hg, key]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointClassDensityUniformisationChartChangeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx


theorem _root_.GlobalTheory.T.point_class_density_uniformisation_chart_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ ch : AlgChart X.str (σ.comp e.toRingHom) X.dim, ψ (GlobalTheory.UnifDens.flatL h v) ∈ ch.e.source → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) v = Complex.normSq (LinearMap.det (fderiv ℂ (fun u => ch.e (ψ (GlobalTheory.UnifDens.flatL h u))) v : ReciprocityTheory.L2DbarEstimates.V X.dim →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim)) * chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ch.e.symm u)) (ch.e (ψ (GlobalTheory.UnifDens.flatL h v))) := by
  first | exact @GlobalTheory.UnifDens.chernTop_unif_chart | exact GlobalTheory.UnifDens.chernTop_unif_chart | (intros; apply GlobalTheory.UnifDens.chernTop_unif_chart <;> assumption)
end
end
