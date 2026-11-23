module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Params
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftScalarIdentityMatchingAdjointInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialFixesVacuaGoodInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransferEigensystemPartsThreeLevelsOfMultEqStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEqMapDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTameCharactersSeriesIdempotentsTameLabelleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdempotentCoefficientConjugate
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SecOfDm

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodStableOfIrr

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.GoodStableDual

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.DimPartsCompare GlobalTheory.BI

theorem isChar_dual {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (h : IsChar ℂ ℂ χ) :
    IsChar ℂ ℂ fun g => χ g⁻¹ := by
  obtain ⟨n, ρ, hρ⟩ := h
  let e : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) := (Pi.basisFun ℂ (Fin n)).dualBasis.equivFun
  let σ : Representation ℂ G (Fin n → ℂ) :=
    { toFun := fun g => e.conj (ρ.dual g)
      map_one' := by rw [map_one]; exact LinearEquiv.conj_id e
      map_mul' := fun a b => by rw [map_mul]; exact LinearEquiv.conj_comp e _ _ }
  refine ⟨n, σ, fun g => ?_⟩
  have : σ.character g = ρ.dual.character g := LinearMap.trace_conj' _ e
  show χ g⁻¹ = _
  rw [Algebra.algebraMap_self, RingHom.id_apply, this, Representation.char_dual, hρ, Algebra.algebraMap_self,
    RingHom.id_apply]


open Formalism.L2.DIV in
theorem coeff_idemOf_inv {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hrec : R.grp_record) {om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ} (hI : IdemTie D om) (g : G) :
    (idemOf A.X).coeff g⁻¹ = (idemOf A.X).coeff g := by
  obtain ⟨eR, plg, iso, h1, -, -⟩ := hrec
  let π : LevelCuspCharacters.LevelGroup D.host ≃* G0g D.nd :=
    MulEquiv.ofBijective (⟨⟨pull, rfl⟩, fun _ _ => rfl⟩ : LevelCuspCharacters.LevelGroup D.host →* G0g D.nd) pull_bijective
  let φ : G ≃* LevelCuspCharacters.LevelGroup D.host := eR.trans π.symm
  have hφ : ∀ g, pull (φ g) = eR g := fun g => π.apply_symm_apply (eR g)
  apply D.what₂.embLL.injective
  rw [h1, h1, ← hφ, ← hφ, hI, hI]
  exact GlobalTheory.GoodIdemFlip.coeff_goodIdem_flip _ D.host om Set.univ (φ g) (φ g⁻¹)
    (fun v _ => by rw [map_inv, Pi.inv_apply]) (fun v hv => absurd (Set.mem_univ v) hv)


open Formalism.L2.DIV in
theorem goodStable_of_irr {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A) (hirr : ∀ χ ∈ A.X, IsAbsIrrChar χ) (hG : R.IsGrp F) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ)
    (hI : IdemTie D om) : GoodStable A.X := by
  classical
  have hsym := coeff_idemOf_inv R hG.record hI
  intro χ hχ
  obtain ⟨ψ, hψ, hψe⟩ := GlobalTheory.GoodTypeGeneric.exists_eq_of_idemOf D.what₂.embLL A.X hirr A.X
    (fun ψ g => D.what₂.embLL (ψ g⁻¹)) (fun ψ hψ => by
      obtain ⟨n, ρ, -, hρ⟩ := GlobalTheory.GoodTypeGeneric.isIrrChar_of_isAbsIrrChar D.what₂.embLL (hirr ψ hψ)
      exact isChar_dual ⟨n, ρ, hρ⟩) (fun g => by
      rw [← hsym g]

      simp only [idemOf, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, coeff_chiIdem, map_sum, map_mul, map_div₀,
      map_natCast, inv_one, inv_inv, Nat.card_eq_fintype_card]) hχ
  convert hψ using 1
  funext g
  apply D.what₂.embLL.injective
  simpa using hψe g⁻¹

end GlobalTheory.GoodStableDual
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodCharactersDualStableOfThetaLiftScalars

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.GoodStableGiven

theorem goodStable_of_given : GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), Given R F → Formalism.L2.DIV.GoodStable A.X := by
  intro hGC D G _ _ Pl0 T A Ks _ _ _ R F h
  obtain ⟨om, hT⟩ := GlobalTheory.T.exists_tameCharacters_seriesIdempotentsTameLabelled R F h
  exact GlobalTheory.GoodStableDual.goodStable_of_irr R F h.irr h.core.grp om
    (GlobalTheory.GoodIdemTie.idemTie_of_tameTie hGC D om hT)

end GlobalTheory.GoodStableGiven

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodCharactersDualStableOfThetaLiftScalarsStatement

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.goodCharacters_dual_stable_of_thetaLift_scalars : GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → Formalism.L2.DIV.GoodStable A.X := by
  first | exact @GlobalTheory.GoodStableGiven.goodStable_of_given | exact GlobalTheory.GoodStableGiven.goodStable_of_given | (intros; apply GlobalTheory.GoodStableGiven.goodStable_of_given <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityOneGivesLiftData

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
namespace GlobalTheory.PrimBase
theorem base_of_ties_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → GlobalTheory.LiftRows.Given R.toRealDat F.lv2 ∧ GoodStable A3.A.X ∧ GlobalTheory.CuspMult.CuspDecomp D ∧ GlobalTheory.Chain.LiftInteg D ∧ GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF ∧ GlobalTheory.LiftRows.UpInj R.toRealDat ∧ GlobalTheory.LiftRows.UpInjW R.toRealDat := by
  intro hP D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hT hM
  have hGiv : GlobalTheory.LiftRows.Given R.toRealDat F.lv2 :=
    GlobalTheory.GivenOfTop.given_of_top R F hT.ok hT.char hT.ex hT.host hT.params hT.ccK hT.guard hT.types
  have hStab : GoodStable A3.A.X := GlobalTheory.T.goodCharacters_dual_stable_of_thetaLift_scalars hP.q12 R.toRealDat F.lv2 hGiv
  have hCD : GlobalTheory.CuspMult.CuspDecomp D := GlobalTheory.CuspDec.cuspDecomp hP.q3 hP.q2 D
  have hLI : GlobalTheory.Chain.LiftInteg D := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hP.q2 D
  have hCore := GlobalTheory.CoreOfWeak.core_of_weak R F hT.char hT.ex
  have hSch : GlobalTheory.Hk3.SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hP.q2 R.toRealDat
  have hTR : GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF :=
    GlobalTheory.T.transfer_eigensystem_parts_three_levels_of_mult_eq R.toRealDat F.lv2 1 hT.ok.ok2 hCore.1 hSch hStab hCD hM R.SF hCore.2.1
  have hFix : ∀ t P, GlobalTheory.Hk3.Good R.toRealDat t P → Formalism.DivisionValues.conjPl P = P → GlobalTheory.Hk3.FixAll R.toRealDat t P :=
    GlobalTheory.FixAllGood.fixAll_of_good R F hT.char hT.ex
  have hU := GlobalTheory.T.thetaLift_scalarIdentity_matching_adjointInjective hP.q5 hP.q3 hP.q4 hP.q6 hP.q2 hP.q1 hP.q7 hP.q8
    (_root_.ResidueKilled.sec_of_dm hP.q9) hP.q10 hP.q11 R.toRealDat F.lv2 hGiv hT.ccK
    hT.char.allPl hFix R.SF hCore.2.1 hTR
  exact ⟨hGiv, hStab, hCD, hLI, hTR, hU.2.2.1, hU.2.2.2⟩
end GlobalTheory.PrimBase
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

theorem _root_.GlobalTheory.T.lift_data_of_multiplicity_one : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → GlobalTheory.LiftRows.Given R.toRealDat F.lv2 ∧ GoodStable A3.A.X ∧ GlobalTheory.CuspMult.CuspDecomp D ∧ GlobalTheory.Chain.LiftInteg D ∧ GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF ∧ GlobalTheory.LiftRows.UpInj R.toRealDat ∧ GlobalTheory.LiftRows.UpInjW R.toRealDat := by
  first | exact @_root_.GlobalTheory.PrimBase.base_of_ties_alt | exact _root_.GlobalTheory.PrimBase.base_of_ties_alt | (intros; apply _root_.GlobalTheory.PrimBase.base_of_ties_alt <;> assumption)
end
end
end
