module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralOneEqMongeAmpereIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothProjVarietyCompactManifoldStatement
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Calculus
import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpaCHessComp
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralTopIndependentOfSmoothWeight

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ChernMass

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {L : LB X}

theorem sub_pick_eq (φ ψ : Weight p σ L) {y : CxPts p σ} {i : L.ι} (hi : y ∈ ptsIn p σ (L.U i)) :
    ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y = ψ.φ i y - φ.φ i y := by
  rw [ψ.trans _ i y (mem_pick φ.isLB y) hi, φ.trans _ i y (mem_pick φ.isLB y) hi]
  ring

theorem cInfAt_half_sub {φ ψ : Weight p σ L} (hφ : φ.IsCInf) (hψ : ψ.IsCInf) (x : CxPts p σ) :
    CInfAt (fun y => (ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y) / 2) x := by
  have hx := mem_pick φ.isLB x
  refine (((hψ _ x hx).add (hφ _ x hx).neg).const_mul 2⁻¹).congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds hx] with z hz
  rw [sub_pick_eq φ ψ hz]
  ring

theorem mInt_one_eq {D : ℕ} [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    {A : FinHolAtlas D (CxPts p σ)} (hA : IsAlgAtlas A) {φ ψ : Weight p σ L} (hφ : φ.IsCInf)
    (hψ : ψ.IsCInf) :
    mInt A (fun _ => φ.locPot) (fun _ => 1) = mInt A (fun _ => ψ.locPot) (fun _ => 1) := by
  have hP : IsPotential A φ.locPot :=
    ((Weight.isCInf_iff_isSmooth hA.anRead).1 hφ).isPotential hA
  have hu : A.Smooth fun y => (ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y) / 2 :=
    (hA.smooth_iff hA.anRead).2 ((cInfAt_iff_smoothOn hA.anRead isOpen_univ).1
      fun y _ => cInfAt_half_sub hφ hψ y)
  rw [← massIndep A (fun _ => φ.locPot) (fun _ => _) (fun _ => hP) fun _ => hu]
  refine SameForm.mInt_eq (fun _ j y hy => hessCGerm _ _ _ ?_) _
  refine eventually_of_mem (((A.chart j).isOpen_inter_preimage_symm (isOpen_ptsIn _)).mem_nhds
    ⟨hy, mem_pick φ.isLB ((A.chart j).symm y)⟩) fun w hw => ?_
  change φ.φ _ _ / 2 + (_ - _) / 2 = ψ.φ (pick φ.isLB _) _ / 2
  rw [sub_pick_eq φ ψ hw.2]
  ring

theorem chernInt_one_eq : ∀ (Y : Var ℂ) (L : LB Y.X) (φ ψ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ψ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = Weight.chernInt ψ Y.dim Set.univ (fun _ => 1) := fun Y L φ ψ hφ hψ => by
  obtain ⟨h₁, h₂, -, A, hA⟩ := GlobalTheory.T.complexPoints_smoothProjVariety_compact_manifold Y
  rw [(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y L φ hφ).2 A hA, (GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y L ψ hψ).2 A hA]
  exact mInt_one_eq hA hφ hψ

end GlobalTheory.ChernMass
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralTopIndependentOfSmoothWeightStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.chernIntegral_top_independent_of_smooth_weight : ∀ (Y : Var ℂ) (L : LB Y.X) (φ ψ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → ψ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = Weight.chernInt ψ Y.dim Set.univ (fun _ => 1) := by
  first | exact @GlobalTheory.ChernMass.chernInt_one_eq | exact GlobalTheory.ChernMass.chernInt_one_eq | (intros; apply GlobalTheory.ChernMass.chernInt_one_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassLineBundleWeightOfIso

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory.ChartGlue
open scoped ContDiff

namespace GlobalTheory.ChernIso

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {A B : LB X} {φ : Weight p σ B} {D : ℕ}

theorem cInfAt_log_normSq {W : X.Opens} (g : Γ(X, W)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W)
    (h0 : ev p σ W g y ≠ 0) : CInfAt (fun z => Real.log (‖ev p σ W g z‖ ^ 2)) y := by
  have hs : ContDiff ℝ ∞ fun v : Unit → ℂ => ‖v ()‖ ^ 2 := (contDiff_apply ℝ (fun _ => ℂ) ()).norm_sq ℂ
  refine ⟨W, Unit, inferInstance, fun _ => g, fun v => Real.log (‖v ()‖ ^ 2),
    {v | ‖v ()‖ ^ 2 ≠ 0}, hy, isOpen_ne_fun hs.continuous continuous_const,
    pow_ne_zero _ (norm_ne_zero_iff.2 h0), hs.contDiffOn.log fun _ h => h, EventuallyEq.rfl⟩

theorem ofIso_apply (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) {a : A.ι} {b : B.ι}
    {y : CxPts p σ} (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    (φ.ofIso hA w hw).φ a y = φ.φ b y + Real.log (‖ev p σ _ (w.s (a, b)).val y‖ ^ 2) := by
  rw [Weight.ofIso, Weight.ofPairs_φ ha hb]

theorem isCInf_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) :
    (φ.ofIso hA w hw).IsCInf := fun a y ha => by
  have hb := mem_pick φ.isLB y
  refine ((h _ y hb).add (cInfAt_log_normSq (w.s (a, pick φ.isLB y)).val
    (mem_ptsIn_inf.2 ⟨ha, hb⟩) (ev_iso_ne_zero w hb ha))).congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds ha, (isOpen_ptsIn _).mem_nhds hb] with z h₁ h₂
  exact ofIso_apply hA w hw h₁ h₂

theorem hess_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen)
    (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) {a : A.ι} {b : B.ι}
    (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    c.hess (φ.ofIso hA w hw) a y = c.hess φ b y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (A.U a ⊓ B.U b))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have hg := c.holo (A.U a ⊓ B.U b) (w.s (a, b)).val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (A.U a ⊓ B.U b),
      (ev p σ (A.U a ⊓ B.U b) (w.s (a, b)).val ∘ c.e.symm) v ≠ 0 := fun v hv =>
    ev_iso_ne_zero w (mem_ptsIn_inf.1 hv.2).2 (mem_ptsIn_inf.1 hv.2).1
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (h b) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩)
    (contDiffOn_log_normSq ho hg h0) 1 hm
  have e₀ : cHess D (fun v => ((Real.log (‖(ev p σ (A.U a ⊓ B.U b) (w.s (a, b)).val ∘
      c.e.symm) v‖ ^ 2) : ℝ) : ℂ)) (c.e y) = 0 := by
    ext i j
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 i j
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [ofIso_apply hA w hw (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, one_mul]
  rfl

theorem chernPart_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) (ε : ℤˣ) :
    (φ.ofIso hA w hw).chernPart D ε = φ.chernPart D ε := by
  refine iSup_congr fun c => Measure.ext fun S hS => ?_
  rw [chartMeas_apply _ _ hS, chartMeas_apply _ _ hS]
  refine setLIntegral_congr_fun (measurableSet_image c.e
    (c.e.open_source.measurableSet.inter hS) inter_subset_left) ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [c.e.left_inv hy.1]
  rw [AlgChart.chernDens, AlgChart.chernDens,
    hess_ofIso h hA w hw c hy.1 (mem_pick _ y) (mem_pick φ.isLB y)]

theorem chernInt_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen)
    (S : Set (CxPts p σ)) (f : CxPts p σ → ℝ) :
    (φ.ofIso hA w hw).chernInt D S f = φ.chernInt D S f := by
  rw [Weight.chernInt, Weight.chernInt, chernPart_ofIso h, chernPart_ofIso h]

theorem chernMass_ofIso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L)
    (hA : A.IsLB) (w : L.Iso A) (hw : w.IsGen), φ.IsCInf → (φ.ofIso hA w hw).IsCInf ∧
      Weight.chernInt (φ.ofIso hA w hw) Y.dim Set.univ (fun _ => 1) =
        Weight.chernInt φ Y.dim Set.univ (fun _ => 1) :=
  fun _ _ _ _ hA w hw h => ⟨isCInf_ofIso h hA w hw, chernInt_ofIso h hA w hw _ _⟩

end GlobalTheory.ChernIso
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassLineBundleWeightOfIsoStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.chernMass_lineBundleWeightOfIso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L) (hA : A.IsLB) (w : L.Iso A) (hw : w.IsGen), φ.IsCInf → (φ.ofIso hA w hw).IsCInf ∧ Weight.chernInt (φ.ofIso hA w hw) Y.dim Set.univ (fun _ => 1) = Weight.chernInt φ Y.dim Set.univ (fun _ => 1) := by
  first | exact @GlobalTheory.ChernIso.chernMass_ofIso | exact GlobalTheory.ChernIso.chernMass_ofIso | (intros; apply GlobalTheory.ChernIso.chernMass_ofIso <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralEqOfLineBundleIso

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
namespace GlobalTheory

theorem chernInt_indep_of_iso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) A), LBIso L A → φ.IsCInf → ψ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = Weight.chernInt ψ Y.dim Set.univ (fun _ => 1) := by
  intro Y L A φ ψ hLA hφ hψ
  obtain ⟨w, hw⟩ := hLA
  obtain ⟨h1, h2⟩ := GlobalTheory.T.chernMass_lineBundleWeightOfIso Y L A φ ψ.isLB w hw hφ
  rw [← h2]
  exact GlobalTheory.T.chernIntegral_top_independent_of_smooth_weight Y A _ ψ h1 hψ

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralEqOfLineBundleIsoStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.chernIntegral_eq_of_lineBundle_iso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) A), LBIso L A → φ.IsCInf → ψ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = Weight.chernInt ψ Y.dim Set.univ (fun _ => 1) := by
  first | exact @GlobalTheory.chernInt_indep_of_iso | exact GlobalTheory.chernInt_indep_of_iso | (intros; apply GlobalTheory.chernInt_indep_of_iso <;> assumption)
end
end
