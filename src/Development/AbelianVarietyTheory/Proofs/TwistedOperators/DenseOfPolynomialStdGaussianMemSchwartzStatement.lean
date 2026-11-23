module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrChInv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowKernelRealEqDetCharMulFockKernel
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryAverageFockPolynomialJetFunctionalStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFiniteDatumVectorThetaFockVacuum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiTContinuous
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactPairRealAverageFockEqJetOperator
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Mathlib.Algebra.Order.Star.Int
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowKernelRealEqDetCharMulFockKernelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.columnArrowKernel_real_eq_detChar_mul_fockKernel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m → ∀ (t : T) (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    ∀ (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (x : FinPt G (.top j)) (k : GA D (G.V (.top j))),
    k ∈ GinfC (G.V (.top j)) → ∀ (h : GA D (G.V (.top (j + 1)))),
      W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * k) h =
        (∏ τ, ((realIn W.θ S.N.fr (.top j) k τ : GL (Fin (G.V (.top j)).rank) ℂ) :
              Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ).det ^
                ((nuEnd G (.top t j) τ : ℤ) - (wt G (.top j) τ).detShift) *
            ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
              Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ).det ^ (wt G (.top (j + 1)) τ).detShift) *
          W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (GlobalTheory.AvgCol.frCh W S.N j
            (GlobalTheory.CompactHowe.substF
              (fun τ => ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
                Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ))
              (fun τ => (((realIn W.θ S.N.fr (.top j) k τ)⁻¹ : GL (Fin (G.V (.top j)).rank) ℂ) :
                Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)ᵀ)
              (GlobalTheory.AvgCol.frChInv W S.N j Q))))
            (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1)))) := by
  first | exact @GlobalTheory.ColKer.kerA_col_mul_real | exact GlobalTheory.ColKer.kerA_col_mul_real | (intros; apply GlobalTheory.ColKer.kerA_col_mul_real <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockComponentTransportedPointsEqJetOperator

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.AvgColJet

theorem fockIn_frC {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T} (hL : L.Is μ0)
    (W : G.Weil) {U : Set T} (N : Std G U) (t : T) (j : ℕ) (hj : j < D.R.m)
    (f : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ) (hf : IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) f)
    (Q : PolF D (G.pT (.top t j)).rank (G.pS (.top t j)).rank) :
    fockIn W N.frC (.top t j) f Q = W.fock (.top t j) f (AvgCol.frCh W N j Q) := by
  have hn : DefNode D.R.m (.top j) ∧ DefNode D.R.m (.top (j + 1)) :=
    ⟨show j ≤ D.R.m by omega, show j + 1 ≤ D.R.m by omega⟩
  have c1 : W.cart (.top j) = fun _ => 1 := funext (GlobalTheory.FockReal.cart_def hL W hn.1)
  have c2 : W.cart (.top (j + 1)) = fun _ => 1 := funext (GlobalTheory.FockReal.cart_def hL W hn.2)
  have e : ∀ X, DefNode D.R.m X → N.frC X = fun τ => W.onb X τ * AvgCol.frRel W N X τ := by
    intro X hX
    funext τ
    have hu : IsUnit (W.onb X τ).det := Matrix.isUnit_det_of_left_inverse (GlobalTheory.FockReal.onb_def hL W hX τ)
    rw [AvgCol.frRel, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  simp only [fockIn, GridData.Weil.fock, GridData.cartS, GridData.onT, GridData.onS, c1, c2, e _ hn.1, e _ hn.2]
  rw [GlobalTheory.FockBaseChange.pureTensorO_subst D W.ψ W.θ _ _ W.ψ_std W.θ_is _ _ _ _ f hf]
  rfl

theorem fockComp_frC_eq_jetOp : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m → ∀ (t : T) (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    ∀ (x : FinPt G (.top j)) (y : FinPt G (.top (j + 1))),
      fockComp W S.N.frC (.top t j) (S.Z.vec d) (x * S.N.u _) (y * S.N.u _) =
        Formalism.L2.Ker.jetOp (wt G (.top j)) (wt G (.top (j + 1)))
          (fun m => W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (GlobalTheory.AvgCol.frCh W S.N j (MvPolynomial.monomial m 1)))
            (x : GA D (G.V (.top j))) (y : GA D (G.V (.top (j + 1)))))
          (nuEnd G (.top t j)) := by
  intro D T L sc G W U S μ0 hL j hj t d hd x y
  have hp : DefPair D.R.m (Pair.top t j : Pair T) := show j + 1 ≤ D.R.m by omega
  have hf := (GlobalTheory.FockRealVec.vec_theta_fock W S.Z hp d hd).1
  unfold fockComp
  refine congrArg (fun F => Formalism.L2.Ker.jetOp (wt G (.top j)) (wt G (.top (j + 1))) F (nuEnd G (.top t j))) (funext fun m => ?_)
  unfold jetTab kerFin
  have hid : m.mapDomain (fvar G (.top t j)) = m := Finsupp.mapDomain_id
  rw [hid, Subgroup.coe_mul, Subgroup.coe_mul, GlobalTheory.FockReal.ker_mul, fockIn_frC hL W S.N t j hj _ hf]
  congr 1
  exact GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om (.top t j)) (W.om_is (.top t j) (show j + 1 ≤ D.R.m by omega))
    W.θ W.θ_is _ (S.N.u _).2 _ (S.N.u _).2 _ _ _ _ _ _ hf

end GlobalTheory.AvgColJet
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockComponentTransportedPointsEqJetOperatorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.fockComponent_transportedPoints_eq_jetOperator : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m → ∀ (t : T) (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    ∀ (x : FinPt G (.top j)) (y : FinPt G (.top (j + 1))),
      fockComp W S.N.frC (.top t j) (S.Z.vec d) (x * S.N.u _) (y * S.N.u _) =
        Formalism.L2.Ker.jetOp (wt G (.top j)) (wt G (.top (j + 1)))
          (fun m => W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (GlobalTheory.AvgCol.frCh W S.N j (MvPolynomial.monomial m 1)))
            (x : GA D (G.V (.top j))) (y : GA D (G.V (.top (j + 1)))))
          (nuEnd G (.top t j)) := by
  first | exact @GlobalTheory.AvgColJet.fockComp_frC_eq_jetOp | exact GlobalTheory.AvgColJet.fockComp_frC_eq_jetOp | (intros; apply GlobalTheory.AvgColJet.fockComp_frC_eq_jetOp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointsTopNodeOntoUnitaryHaarUnique

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowTest

theorem realPts_ontoUni_haar_unique : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j ≤ D.R.m →
    GlobalTheory.KJInf.OntoUni (fun (k : GinfC (G.V (.top j))) τ =>
      ((realIn W.θ S.N.fr (.top j) (k : GA D (G.V (.top j))) τ : GL (Fin (G.V (.top j)).rank) ℂ) :
        Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)) ∧
    ∀ κ κ' : Measure (GinfC (G.V (.top j))), κ.IsHaarMeasure → IsProbabilityMeasure κ → κ'.IsHaarMeasure →
      IsProbabilityMeasure κ' → κ = κ' := by
  intro D T L sc G W U S μ0 _ j hj
  have hX : DefNode D.R.m (Node.top j) := hj
  have hO := GlobalTheory.SeeSaw.ontoUni_inB D W.θ (G.V (.top j)) (S.N.frC _) W.θ_is (GlobalTheory.RealType.frC_on S.N hX)
  refine ⟨?_, ?_⟩
  · have e : (fun (k : GinfC (G.V (.top j))) τ =>
        ((realIn W.θ S.N.fr (.top j) (k : GA D (G.V (.top j))) τ : GL (Fin (G.V (.top j)).rank) ℂ) :
          Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)) =
        fun k : GinfC (G.V (.top j)) => GlobalTheory.SeeSaw.inB W.θ (G.V (.top j)) (S.N.frC (.top j)) k.1 :=
      funext fun k => funext fun τ => GlobalTheory.RowHoweAvg.realIn_coe W.θ S.N _ _ τ
    rw [e]
    exact hO
  · intro κ κ' h1 h2 h3 h4
    haveI : LocallyCompactSpace (GinfC (G.V (.top j))) :=
      (GlobalTheory.AdelicSplit.isClosed_GinfC' _).locallyCompactSpace
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure κ κ'

end GlobalTheory.RowTest
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointsTopNodeOntoUnitaryHaarUniqueStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.realPoints_topNode_onto_unitary_haar_unique : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j ≤ D.R.m →
    GlobalTheory.KJInf.OntoUni (fun (k : GinfC (G.V (.top j))) τ =>
      ((realIn W.θ S.N.fr (.top j) (k : GA D (G.V (.top j))) τ : GL (Fin (G.V (.top j)).rank) ℂ) :
        Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)) ∧
    ∀ κ κ' : Measure (GinfC (G.V (.top j))), κ.IsHaarMeasure → IsProbabilityMeasure κ → κ'.IsHaarMeasure →
      IsProbabilityMeasure κ' → κ = κ' := by
  first | exact @GlobalTheory.RowTest.realPts_ontoUni_haar_unique | exact GlobalTheory.RowTest.realPts_ontoUni_haar_unique | (intros; apply GlobalTheory.RowTest.realPts_ontoUni_haar_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseOfPolynomialStdGaussianMemSchwartz

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.AvgCol

theorem avg_col : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m →
    ∀ (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (Λ : Module.Dual ℂ (VV ℂ (wt G (.top j)))),
    ∃ Λ' : Module.Dual ℂ (VV ℂ (wt G (.top (j + 1)))), ∀ t ∈ U, ∀ d : FinDatum G t (.top t j), S.Z.HasVec d →
      ∀ κ : Measure (GinfC (G.V (.top j))), κ.IsHaarMeasure → IsProbabilityMeasure κ →
      ∀ (x : FinPt G (.top j)) (h : GA D (G.V (.top (j + 1)))) (v : VV ℂ (wt G (.top j))),
        ∫ k, W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * (k : GA D (G.V (.top j)))) h *
            Λ (realAct W.θ S.N.fr (.top j) ((k : GA D (G.V (.top j)))⁻¹) v) ∂κ =
          Λ' (realAct W.θ S.N.fr (.top (j + 1)) h⁻¹
            (fockComp W S.N.frC (.top t j) (S.Z.vec d) (x * S.N.u _) (finOf _ h * S.N.u _) v)) := by
  intro D T L sc G W U S μ0 hL j hj Q Λ
  obtain ⟨hr, huniq⟩ := GlobalTheory.T.realPoints_topNode_onto_unitary_haar_unique S hL j hj.le
  let r : GinfC (G.V (.top j)) →* (D.what₂.Tau → GL (Fin (G.V (.top j)).rank) ℂ) :=
    (realIn W.θ S.N.fr (.top j)).comp (GinfC (G.V (.top j))).subtype
  have hrk : (G.V (.top j)).rank ≤ (G.V (.top (j + 1))).rank ∧ 0 < (G.V (.top j)).rank := by
    rw [(node_isV G hL (X := .top j) (show j ≤ D.R.m by omega)).rank,
      (node_isV G hL (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)).rank]
    simp only [Node.rank, rankX, rankP, nRk]
    constructor
    · nlinarith
    · omega
  obtain ⟨hab, ha⟩ := hrk
  have hJ : Formalism.L2.Ker.JetInVV ℂ (wt G (.top j)) (wt G (.top (j + 1))) (nuEnd G (.top μ0 j)) :=
    (wtOK_of_defPair G (.top μ0 j) (show j + 1 ≤ D.R.m from hj)).2
  by_cases hex : ∃ κ₀ : Measure (GinfC (G.V (.top j))), κ₀.IsHaarMeasure ∧ IsProbabilityMeasure κ₀
  · obtain ⟨κ₀, h1, h2⟩ := hex
    haveI := h1
    haveI := h2
    obtain ⟨Λ', hΛ'⟩ := GlobalTheory.T.compactUnitaryAverage_fockPolynomial_jetFunctional D.what₂.Tau _ _ hab ha (wt G (.top j)) (wt G (.top (j + 1))) (nuEnd G (.top μ0 j)) hJ
      (GinfC (G.V (.top j))) κ₀ r hr (frChInv W S.N j Q) Λ
    refine ⟨Λ', fun t ht d hd κ hκ hκp x h v => ?_⟩
    obtain rfl := huniq κ κ₀ hκ hκp h1 h2
    let ℓ : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₗ[ℂ] ℂ :=
      (LinearMap.proj (R := ℂ) (φ := fun _ : WO (G.pS (.top t j)) (G.pT (.top t j)) => ℂ) 0).comp
        ((W.om (.top t j) (G.toPair (.top t j) (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1)))))).comp
          ((W.fock (.top t j) (movedVec t S d)).comp (frCh W S.N j).toLinearMap))
    have hℓ : ∀ P, ℓ P = W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (frCh W S.N j P))
        (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1)))) := fun P => rfl
    have e1 : ∀ k : GinfC (G.V (.top j)),
        W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * (k : GA D (G.V (.top j)))) h *
            Λ (realAct W.θ S.N.fr (.top j) ((k : GA D (G.V (.top j))))⁻¹ v) =
          (∏ τ, ((r k τ : GL (Fin (G.V (.top j)).rank) ℂ) : Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ).det ^ ((nuEnd G (.top μ0 j) τ : ℤ) - (wt G (.top j) τ).detShift) *
              ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ).det ^ (wt G (.top (j + 1)) τ).detShift) *
            ℓ (GlobalTheory.CompactHowe.substF (fun τ => ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ))
              (fun τ => (((r k τ)⁻¹ : GL (Fin (G.V (.top j)).rank) ℂ) : Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)ᵀ) (frChInv W S.N j Q)) *
            Λ (rhoK (wt G (.top j)) (invTrK (r k⁻¹)) v) := by
      intro k
      rw [GlobalTheory.T.columnArrowKernel_real_eq_detChar_mul_fockKernel S hL j hj t d hd Q x k k.2 h, hℓ]
      rfl
    rw [integral_congr_ae (Filter.Eventually.of_forall e1), hΛ' ℓ (realIn W.θ S.N.fr (.top (j + 1)) h) v,
      GlobalTheory.T.fockComponent_transportedPoints_eq_jetOperator S hL j hj t d hd x (finOf _ h)]
    have e2 : realAct W.θ S.N.fr (.top (j + 1)) h⁻¹ =
        rhoK (wt G (.top (j + 1))) (invTrK (realIn W.θ S.N.fr (.top (j + 1)) h)⁻¹) := by
      simp only [realAct, MonoidHom.comp_apply, map_inv]
    rw [e2]
    rfl
  · exact ⟨0, fun t _ d _ κ hκ hκp => absurd ⟨κ, hκ, hκp⟩ hex⟩

end GlobalTheory.AvgCol

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseOfPolynomialStdGaussianMemSchwartzStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.exists_dual_integral_arrowKernel_fock_eq_fockComp_top : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m →
    ∀ (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (Λ : Module.Dual ℂ (VV ℂ (wt G (.top j)))),
    ∃ Λ' : Module.Dual ℂ (VV ℂ (wt G (.top (j + 1)))), ∀ t ∈ U, ∀ d : FinDatum G t (.top t j), S.Z.HasVec d →
      ∀ κ : Measure (GinfC (G.V (.top j))), κ.IsHaarMeasure → IsProbabilityMeasure κ →
      ∀ (x : FinPt G (.top j)) (h : GA D (G.V (.top (j + 1)))) (v : VV ℂ (wt G (.top j))),
        ∫ k, W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * (k : GA D (G.V (.top j)))) h *
            Λ (realAct W.θ S.N.fr (.top j) ((k : GA D (G.V (.top j)))⁻¹) v) ∂κ =
          Λ' (realAct W.θ S.N.fr (.top (j + 1)) h⁻¹
            (fockComp W S.N.frC (.top t j) (S.Z.vec d) (x * S.N.u _) (finOf _ h * S.N.u _) v)) := by
  first | exact @GlobalTheory.AvgCol.avg_col | exact GlobalTheory.AvgCol.avg_col | (intros; apply GlobalTheory.AvgCol.avg_col <;> assumption)
end
end
