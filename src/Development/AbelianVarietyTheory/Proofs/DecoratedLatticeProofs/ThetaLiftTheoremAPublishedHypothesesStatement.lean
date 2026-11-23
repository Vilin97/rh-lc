module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CommutingLevelOperators
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerProductEqConstMulLValueStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftAdjointScalarFormulaInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialFixesVacuaGoodInertPlaceStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteTypeCarriesOnePart
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows

-- Source module: Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.CarriesOfKilled

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftScalarTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem apply_eq_smul_of_unique_eigenvalue {M : Type} [AddCommGroup M] [Module ℂ M] (f : M → M) (h0 : f 0 = 0) (P : Submodule ℂ M) (m : ℝ)
    (h : ∀ l : ℝ, P ≠ ⊥ → (∀ x ∈ P, f x = (l : ℂ) • x) → m = l) (hA : ∃ l : ℝ, ∀ x ∈ P, f x = (l : ℂ) • x) :
    ∀ x ∈ P, f x = (m : ℂ) • x := by
  obtain ⟨l, hl⟩ := hA
  intro x hx
  by_cases hp : P = ⊥
  · rw [hp, Submodule.mem_bot] at hx
    rw [hx, h0, smul_zero]
  · rw [h l hp hl]; exact hl x hx

theorem scal_of_one {M C : Type} [AddCommGroup M] [Module ℂ M] (f : M → M) (h0 : f 0 = 0) (P : C → Submodule ℂ M) (k : C → Prop)
    (h1 : ∀ c c', k c → k c' → P c = P c') (hA : ∀ c, P c ≠ ⊥ → ∃ l : ℝ, ∀ x ∈ P c, f x = (l : ℂ) • x) :
    ∃ l : ℝ, ∀ x ∈ ⨆ (c : C) (_ : k c), P c, f x = (l : ℂ) • x := by
  by_cases hc : ∃ c, k c ∧ P c ≠ ⊥
  · obtain ⟨c, hc, hn⟩ := hc
    obtain ⟨z, hz⟩ := hA c hn
    have hle : ⨆ (c : C) (_ : k c), P c ≤ P c := iSup₂_le fun c' hc' => (h1 c' c hc' hc).le
    exact ⟨z, fun x hx => hz x (hle hx)⟩
  · refine ⟨0, fun x hx => ?_⟩
    have hle : ⨆ (c : C) (_ : k c), P c ≤ ⊥ := iSup₂_le fun c' hc' => by
      by_contra hn
      exact hc ⟨c', hc', fun e => hn e.le⟩
    rw [(Submodule.mem_bot ℂ).1 (hle hx), h0, smul_zero]



theorem iff_of_pin (R : RealDat3 D A3 Ks) (h : R.eigenvalue_at_base_of_scalar) :
    R.PThmA ↔ ∀ i t p, ∃ l : ℝ, ∀ x ∈ R.Wp3 i p, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x := by
  constructor
  · intro hA i t p
    exact ⟨R.lam3 i t p A3.A.v0, hA i t p⟩
  · intro hA i t p
    exact apply_eq_smul_of_unique_eigenvalue (fun x => R.thG i t (LinearMap.adjoint (R.thG i t) x)) (by simp only [map_zero]) (R.Wp3 i p) _ (h i t p) (hA i t p)

def OnePart (R : RealDat3 D A3 Ks) : Prop := ∀ i p c c', R.Carries p c → R.Carries p c' → R.Wc' i c = R.Wc' i c'

def ScalC (R : RealDat3 D A3 Ks) : Prop :=
  ∀ i t c, R.Wc' i c ≠ ⊥ → ∃ l : ℝ, ∀ x ∈ R.Wc' i c, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x

theorem ex_of_aForm {A : FamIn D.what₂.LL G Pl0 T D.R.m} {R : RealDat D A Ks} {SF} (hA : GlobalTheory.LiftRows.AForm R SF) (i t c)
    (hn : GlobalTheory.Hk3.Wcc R SF i c ≠ ⊥) :
    ∃ l : ℝ, ∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x :=
  ⟨_, (hA.choose_spec.2 i t c hn).choose_spec.2⟩

theorem scalC_of_aForm (R : RealDat3 D A3 Ks) (hA : GlobalTheory.LiftRows.AForm R.toRealDat R.SF) : ScalC R :=
  fun i t c hn => ex_of_aForm hA i t c hn


theorem of_scalC (R : RealDat3 D A3 Ks) (hA : ScalC R) (h : R.eigenvalue_at_base_of_scalar) (h1 : OnePart R) : R.PThmA :=
  (iff_of_pin R h).2 fun i t p =>
    scal_of_one (fun x => R.thG i t (LinearMap.adjoint (R.thG i t) x)) (by simp only [map_zero]) (R.Wc' i) (R.Carries p)
      (h1 i p) (hA i t)

theorem of_aForm (R : RealDat3 D A3 Ks) (hA : GlobalTheory.LiftRows.AForm R.toRealDat R.SF) (h : R.eigenvalue_at_base_of_scalar) (h1 : OnePart R) : R.PThmA :=
  of_scalC R (scalC_of_aForm R hA) h h1

end GlobalTheory.LiftScalarTest

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAdjointScalarTheoremOfScalarFormula

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.ThmAFromAForm

theorem pThmA_of_aForm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → AForm R.toRealDat R.SF → (∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c') → R.PThmA := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _ hC _ hA h1
  exact GlobalTheory.LiftScalarTest.of_aForm R hA hC.scal.lam0 (fun i p c c' hc hc' => (h1 p c c' hc hc').2 i)

end GlobalTheory.ThmAFromAForm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAdjointScalarTheoremOfScalarFormulaStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.thetaAdjoint_scalar_theorem_of_scalar_formula : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → AForm R.toRealDat R.SF → (∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c') → R.PThmA := by
  first | exact @GlobalTheory.ThmAFromAForm.pThmA_of_aForm | exact GlobalTheory.ThmAFromAForm.pThmA_of_aForm | (intros; apply GlobalTheory.ThmAFromAForm.pThmA_of_aForm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteTypeCarriesOnePartStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.finiteType_carriesOnePart : GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → UpInj R.toRealDat → (∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c') := by
  first | exact @GlobalTheory.CarriesOne.parts_eq_of_carries | exact GlobalTheory.CarriesOne.parts_eq_of_carries | (intros; apply GlobalTheory.CarriesOne.parts_eq_of_carries <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRowsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.scalarHypotheses_of_topRows : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → Given R.toRealDat F.lv2 := by
  first | exact @GlobalTheory.GivenOfTop.given_of_top | exact GlobalTheory.GivenOfTop.given_of_top | (intros; apply GlobalTheory.GivenOfTop.given_of_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftFirstHypotheses

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
namespace GlobalTheory.ThmAFinal

theorem pThmA_short
    (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHCF : GlobalTheory.Published.HarishChandraFinite)
    (hHCM : GlobalTheory.Published.HarishChandraModules) (hCW : GlobalTheory.Published.CasselmanWallach)
    (hCusp : GlobalTheory.Published.CuspRapidDecay) (hHowe : GlobalTheory.Hk3.HoweUnram)
    (hWS : GlobalTheory.Published.WeilSiegelFormulaUnitary) (hHk : ∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D')
    (hSE : GlobalTheory.Published.SiegelEisensteinContinuation) (hUD : GlobalTheory.Published.UnramifiedDoublingGL)
    (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) :
    ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PThmA := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hCh hEx hHost hLed hcc hQ hGT hInert
  obtain ⟨hCore, hSF, hE, hW⟩ := GlobalTheory.T.core_clauses_of_weak_characterisation R F hCh hEx
  have hGiven := GlobalTheory.T.scalarHypotheses_of_topRows R F hOk hCh hEx hHost hLed hcc hQ hGT
  have hFix := GlobalTheory.T.hyperspecial_fixes_vacua_good_inert_place R F hCh hEx
  have hA := GlobalTheory.T.thetaInnerProduct_eq_const_mul_LValue hDS hHCM hCusp hWS hSE hUD hBZ R.toRealDat F.lv2 hGiven hcc R.SF hSF
  have hU := (GlobalTheory.T.thetaLift_adjoint_scalarFormula_injective hDS hHCF hHCM hCW hCusp hHowe hWS hHk hSE hUD R.toRealDat F.lv2 hGiven hcc hCh.allPl hFix R.SF hSF).2
  have hC := GlobalTheory.T.finiteType_carriesOnePart hHowe hCusp R F hOk hCh hEx hInert hU
  exact GlobalTheory.T.thetaAdjoint_scalar_theorem_of_scalar_formula R F hOk hCh hEx hA hC

end GlobalTheory.ThmAFinal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftTheoremAPublishedHypothesesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.thetaLift_theoremA_publishedHypotheses : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilSiegelFormulaUnitary → (∀ D' : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D') → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → HostHyp D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → D.host.ccK = ⊤ → FWT.QGuard R.toRealDat → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R.toRealDat → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PThmA := by
  first | exact @GlobalTheory.ThmAFinal.pThmA_short | exact GlobalTheory.ThmAFinal.pThmA_short | (intros; apply GlobalTheory.ThmAFinal.pThmA_short <;> assumption)
end
end
