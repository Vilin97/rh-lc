module

public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatesOfRationalThetaLiftFromCharacterisatioStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumLiftScalarOfInnerProductFormula
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.HermitianLattices.StatementMaj
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.QuotientMetricDivisors.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapRangeAdjointLeBlockSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTransposeMajorant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapConjTransposeTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLiftReadingsScaleClassSumEigenspacesStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftPointsPartEigenformsCoefficientFieldStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeCoefficientsSqIntegrable
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfRangeAdjoint
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartFamily
import Formalism.LocalToGlobal.IndefiniteReal.MajAtEqZeroOfMemQpOfNe
import Formalism.LocalToGlobal.IndefiniteReal.MemRangeAdjointOfKerStable
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.UnitaryTwoPackage
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RangeAdjointRat
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatThOfLiftTest

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumLiftScalarOfInnerProductFormulaStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjugateDatum_lift_scalar_of_innerProductFormula : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R → GlobalTheory.ConjScalar.ConjScalarAt R := by
  first | exact @GlobalTheory.ConjScalarProof.conjScalarAt_of_sourceLevelLaw_fock_zeta | exact GlobalTheory.ConjScalarProof.conjScalarAt_of_sourceLevelLaw_fock_zeta | (intros; apply GlobalTheory.ConjScalarProof.conjScalarAt_of_sourceLevelLaw_fock_zeta <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ScalAtZeroOfLiftMat

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open scoped InnerProductSpace Matrix

namespace GlobalTheory.ScalarConjugation

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links

section Abstract

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem maj_eq_zero {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x y : Fin n → K)
    (h : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) X v x x = 0) : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) X v x y = 0 := by
  have hc : ∀ i, Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) X v x i = 0 := by
    have hs : ∑ i, ((Complex.normSq (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) X v x i) : ℝ) : ℂ) = 0 := by
      rw [← h]
      unfold Formalism.HermitianLatticesTheory.majAt
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    have hr : ∑ i, Complex.normSq (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) X v x i) = 0 := by
      exact_mod_cast hs
    intro i
    exact Complex.normSq_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun k _ => Complex.normSq_nonneg _).1 hr i (Finset.mem_univ i))
  unfold Formalism.HermitianLatticesTheory.majAt
  exact Finset.sum_eq_zero fun i _ => by rw [hc i, star_zero, zero_mul]

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

end Abstract

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

end Concrete

section Comparison₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.MainNotions

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


end Comparison₂

end GlobalTheory.ScalarConjugation
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftWeightComplexPointEqTwist

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjScalarCoord

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool)

theorem wC_cpt (j : Fin D.R.m) (v : InfinitePlace D.what₂.LL) (c : Fin ((R.toCx3 F).dW b j) → D.what₂.LL) :
    ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c)) :
        R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H) =
      (((Real.sqrt (RealDat.nP F.lv2 b))⁻¹ : ℝ) : ℂ) •
        (R.FW j).j (sgAt D.what₂.embLL v) (∑ k, c k • R.toRealDat.bL F.lv2 b j k) := by
  have e : ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c)) :
        R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H) =
      ((∑ k, cj (twAt D.what₂.embLL v) (v.embedding (c k)) •
        (⟨R.toRealDat.bC F.lv2 b j _ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) :
        (R.HW j (sgAt D.what₂.embLL v)).H) := rfl

  rw [e, Submodule.coe_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Submodule.coe_smul, emb_eq D.what₂.embLL v, cj_cj, LinearMap.map_smulₛₗ, smul_comm]
  rfl

theorem sqrt_ne : ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 (RealDat.nP_pos (F := F.lv2) b)).ne'

theorem liftWeight_complexPoint_eq_twist (j : Fin D.R.m) (c : Fin ((R.toCx3 F).dW b j) → D.what₂.LL) :
    (Tw.out (s := twAt D.what₂.embLL A3.A.v0) ((R.toCx3 F).w0C b j (cpt A3.A.v0.embedding c)) : (R.HW j (sg0 D A3.A)).H) =
      (R.FW j).j (sg0 D A3.A) (∑ k, c k • R.toRealDat.bL F.lv2 b j k) := by
  have e : (Tw.out (s := twAt D.what₂.embLL A3.A.v0) ((R.toCx3 F).w0C b j (cpt A3.A.v0.embedding c)) : (R.HW j (sg0 D A3.A)).H) =
      ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • ((Tw.out (s := twAt D.what₂.embLL A3.A.v0)
        ((R.toCx3 F).wC b j A3.A.v0 (cpt A3.A.v0.embedding c)) :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL A3.A.v0)) : (R.HW j (sgAt D.what₂.embLL A3.A.v0)).H) := rfl
  rw [e, wC_cpt, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ (sqrt_ne F b), one_smul]

theorem inner_wC (j : Fin D.R.m) {v : InfinitePlace D.what₂.LL} (hv : v ≠ A3.A.v0) (c c' : Fin ((R.toCx3 F).dW b j) → D.what₂.LL) :
    ⟪(R.toCx3 F).wC b j v (cpt v.embedding c), (R.toCx3 F).wC b j v (cpt v.embedding c')⟫_ℂ =
      (Nat.card (F.lv2.lvl b).P : ℂ)⁻¹ * ⟪(R.FW j).j v.embedding (∑ k, c k • R.toRealDat.bL F.lv2 b j k),
        (R.FW j).j v.embedding (∑ k, c' k • R.toRealDat.bL F.lv2 b j k)⟫_ℂ := by
  have hs : sgAt D.what₂.embLL v = v.embedding := if_neg (R.hv0 ▸ hv)
  have ht : twAt D.what₂.embLL v = false := if_pos hs.symm
  have e : ⟪(R.toCx3 F).wC b j v (cpt v.embedding c), (R.toCx3 F).wC b j v (cpt v.embedding c')⟫_ℂ =
      cj (twAt D.what₂.embLL v) ⟪((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c)) :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H),
        ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c')) :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H)⟫_ℂ := rfl
  rw [e, wC_cpt, wC_cpt, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (RealDat.nP_pos (F := F.lv2) b).le, hs]
  generalize twAt D.what₂.embLL v = s at ht
  subst ht
  simp only [cj, RealDat.nP, Bool.false_eq_true, if_false]
  simp only [cond_false, RingHom.id_apply, Complex.ofReal_inv, Complex.ofReal_natCast]

theorem tC_cpt (cr : Crd A3.fam3.amb3 F.fc) (j : Fin D.R.m) (t : T0)
    (x : Fin ((lv (F.fc (R.toCx3 F).zs) b).dZ j t) → D.what₂.LL) :
    (R.toCx3 F).tC cr b j t (cpt A3.fam3.base3.v0.embedding x) =
      (R.toCx3 F).θ' j t ((R.toCx3 F).jL j t (cr.toL (R.toCx3 F).zs b j t x)) := by
  conv_rhs => rw [← (Pi.basisFun D.what₂.LL _).sum_repr x]

  simp only [CxData.tC, lin_apply, map_sum, map_smul, LinearMap.map_smulₛₗ, Pi.basisFun_repr, Pi.basisFun_apply, cpt,
  RingHom.id_apply]

theorem liftMat_isRatLift_inner : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3), (R.toCx3 F).H5 F.cr false → (R.toCx3 F).RATth F.cr false → ∀ i, (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R.toRealDat i (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x) (∑ k, (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec x) k • R.toRealDat.bL F.lv2 false i k)) ∧ ∀ v, v ≠ A3.A.v0 → ∀ x y, ⟪(R.toCx3 F).wC false i v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec x)), (R.toCx3 F).wC false i v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec y))⟫_ℂ = ((Nat.card F.P0 : ℕ) : ℂ)⁻¹ * ⟪(R.FW i).j v.embedding (∑ k, (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec x) k • R.toRealDat.bL F.lv2 false i k), (R.FW i).j v.embedding (∑ k, (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec y) k • R.toRealDat.bL F.lv2 false i k)⟫_ℂ := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hT hR i
  refine ⟨fun x => ?_, fun v hv x y => ?_⟩
  · show (R.FW i).j (sg0 D A3.A) _ = _
    refine (liftWeight_complexPoint_eq_twist R F false i _).symm.trans ?_
    have h1 := ((R.toCx3 F).key_lift F.cr false hT hR i A3.A.μ0 x).trans (tC_cpt R F false F.cr i A3.A.μ0 x)
    exact congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) h1
  · rw [inner_wC R F false i hv]
    rfl

end GlobalTheory.ConjScalarCoord
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftScalarIdentityOffFixedPlaceBaseLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalarOff

section SlopeTestRemainingChoices
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem range_adjoint_smul_le' {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (c : ℂ) (f : E →ₗ[ℂ] E') :
    LinearMap.range (LinearMap.adjoint (c • f)) ≤ LinearMap.range (LinearMap.adjoint f) := by
  rintro _ ⟨y, rfl⟩
  rw [RealDat3.adjoint_smul']
  exact ⟨starRingEnd ℂ c • y, by simp⟩

theorem jV_mem_range (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j : Fin D.R.m) (t : T0) :
    ∀ z ∈ (R.toCx3 F).Zl j t, R.jV j t z ∈ LinearMap.range (LinearMap.adjoint (R.thG j t)) := by
  intro z hz
  have hx1 := range_adjoint_smul_le' (R.phs j) (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j t)) hz
  exact (GlobalTheory.AdjBlock.mem_range_adjoint_tw (twAt D.what₂.embLL A3.A.v0) (R.thG j t) (R.jV j t z)).1 hx1

end SlopeTestRemainingChoices

theorem galD_base : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.ConjScalar.ConjScalarAt R.toRealDat → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → R.toRealDat.LUnif → ((R.toCx3 F).H5 F.cr false ∧ (R.toCx3 F).RATth F.cr false ∧ (R.toCx3 F).H3W F.cr false ∧ (lv (F.fc (R.toCx3 F).zs) false).Proviso) → (R.toCx3 F).GalD F.cr false := by
  intro hHowe hCRL D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s hOk hC hEx hCS hψ fw hBar hIo hPins hRow0 hPT hU hfacts
  obtain ⟨h5, hrat, h3w, hprov⟩ := hfacts
  have hcore := GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx
  intro j v hv p
  obtain ⟨a, ha⟩ := GlobalTheory.T.thetaLiftPoints_part_eigenforms_coefficientField R F s hOk hC h3w j p
  have hOne := hPT j hU (hRow0 j)
  have hHerm : Formalism.DivisionValues.IsRatHerm (Formalism.DivisionValues.cmMax D.what₂.LL) ((A3.A.fam.L j A3.A.μ0).HZ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0))
      ((A3.A.fam.L j A3.A.μ0).XQ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0)) := hprov j
  have hBH : BlockHyp (A3.A.fam.L j A3.A.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 s :=
    ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.lifts j A3.A.μ0⟩
  have hfE := GlobalTheory.QuotRational.fE_mem_cmMax _ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0) A3.A.v0 s hBH hHerm
  obtain ⟨l, hl⟩ := GlobalTheory.T.rationalLift_readings_scale_classSum_eigenspaces hHowe hCRL T R.toRealDat κ v₀ O F.lv2 _ hcore.1 hψ hCS fw hBar hIo hU hPins j hOne
    (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0) hHerm hfE (jV_mem_range R F j A3.A.μ0) v.embedding a
  have hmaj := (GlobalTheory.Proof.ConjugateTransposeMajorant.majAt_eq_csumAt _ (A3.A.fam.lvlA F.P0 F.ψ0) ((R.toCx3 F).Zl j A3.A.μ0) hHerm hfE).1 v
  have hco := GlobalTheory.ConjScalarCoord.liftMat_isRatLift_inner R F h5 hrat j
  have hS : ∀ x, (R.toCx3 F).tC F.cr false j A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp j p → ∀ y,
      ⟪(R.toCx3 F).wC false j v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false j A3.A.μ0).mulVec x)),
        (R.toCx3 F).wC false j v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false j A3.A.μ0).mulVec y))⟫_ℂ =
      ((l : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx3 F).zs) false).XT j A3.A.μ0) v x y := by
    intro x hx y
    have e1 := hco.2 v hv x y
    have e2 := hl x (F.cr.toL (R.toCx3 F).zs false j A3.A.μ0 y) _ _ (ha x hx) (hco.1 x) (hco.1 y)
    have e3 := hmaj x y
    rw [e1, e2]
    erw [e3]
    exact mul_left_comm _ _ _
  intro x hx y
  by_cases hP : R.PartAt F j p v
  · have e : R.lam3 j A3.A.μ0 p v = l := hC.scal.off j p v l hv hP hS
    exact (hS x hx y).trans (congrArg (fun t : ℝ => (t : ℂ) * _) e.symm)
  · have h0 := GlobalTheory.ScalarConjugation.maj_eq_zero _ v x y (by by_contra hn; exact hP ⟨x, hx, hn⟩)
    exact (hS x hx y).trans ((mul_eq_zero_of_right _ h0).trans (mul_eq_zero_of_right _ h0).symm)

end GlobalTheory.ConjScalarOff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftScalarIdentityOffFixedPlaceBaseLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.liftScalarIdentity_offFixedPlace_baseLevel : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.ConjScalar.ConjScalarAt R.toRealDat → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → R.toRealDat.LUnif → ((R.toCx3 F).H5 F.cr false ∧ (R.toCx3 F).RATth F.cr false ∧ (R.toCx3 F).H3W F.cr false ∧ (lv (F.fc (R.toCx3 F).zs) false).Proviso) → (R.toCx3 F).GalD F.cr false := by
  first | exact @GlobalTheory.ConjScalarOff.galD_base | exact GlobalTheory.ConjScalarOff.galD_base | (intros; apply GlobalTheory.ConjScalarOff.galD_base <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalConjBaseFacts

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem scalConj_base_facts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → 0 < R.kap → (∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.toRealDat.LUnif → R.PLevW F → R.PThmA → (R.toCx3 F).PartsW false → (R.toCx3 F).H5 F.cr false ∧ (R.toCx3 F).RATth F.cr false ∧ (R.toCx3 F).H3W F.cr false ∧ (lv (F.fc (R.toCx3 F).zs) false).Proviso := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F s hOk hsep hC hR hL hH hU hE hblk hrt hlt hltb honto hk hl hun hlev hA hsum
  have kR := RealDat3.kFormR_of (F := F) hC.base.models
  have kL := RealDat3.kFormL_of (F := F) hC.base.models
  have jR := RealDat3.jIsoR_of (F := F) hC.base.models
  have jL := RealDat3.jIsoL_of (F := F) hC.base.models
  have thR := hH.1.choose_spec
  have thL := hH.2.choose_spec
  have st : (R.toCx3 F).zs.Stable := CxData.cutStable (R.toCx3 F) kR kL
    (Formalism.IndefR.CxPass.definite_kernel_stable kR hE.1 thR) (Formalism.IndefR.CxPass.lift_kernel_stable kL hE.2 thL)
    (definite_adjoint_closed hOk hR kR jR) (lift_adjoint_closed hOk hL kL jL)
  have wf := A3.side_well_formed hOk F.P0 F.ψ0 (R.toCx3 F).zs st hblk hsep
  have rz : (R.toCx3 F).RatZ := Formalism.IndefR.Rat.ratZOfTests (R.toCx3 F) (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) kR kL jR jL hrt hlt
  have eig0 := (U2.unitary_two_package A3 (R.toCx3 F) s F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc hH.2.choose (R.gWx F) hOk kR kL jR jL hrt hlt hL thL hU.2 hE.2 hlev hsum (honto _ thL)).1
  have kf := RealDat3.kForm_of (F := F) hun false
  let X' : CxData A3.fam3.amb3 := { R.toCx3 F with lam := fun j t p _ => (R.toCx3 F).lam j t p A3.fam3.base3.v0 }
  have h5 : (R.toCx3 F).H5 F.cr false := (CxData.cutLifts X' (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) false wf
    ⟨fun _ => hk, fun j t p _ => hl j t p, RealDat.nP_pos⟩ kf
    (lift_isometry_of_norms hOk jL ⟨rfl, rfl⟩ false) (lift_coordinates_in_subspaces (R.toCx3 F) false) (lift_coordinates_in_good_part_family (R.toCx3 F) false)
    (Formalism.IndefR.CxPass.lift_rationality_of_equivariance hOk kL jL rz hU.2 hE.2 false)
    (Formalism.IndefR.CxPass.lift_descent_at_lower_type hOk kL jL rz hU.2 hE.2 hlev)
    (Formalism.IndefR.CxPass.upper_level_lift_at_lower_type hOk kL jL hU.2 hE.2 hlev)
    (RealDat3.thmAop_of hC.phase hA false) hsum).1
  exact ⟨h5, Formalism.IndefR.Rat.ratThOfLiftTest (R.toCx3 F) _ false hltb h5 kf (RealDat3.ewNorm false) (RealDat.nP_pos false),
    lift_equivariance_of_primitive F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc kL st hOk thL false,
    proviso_of_lift_eigenvalues A3 (R.toCx3 F) hOk (fun j => hL j A3.A.fam.μ0) F.P0 F.ψ0 eig0⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateBaseLevelOfHoweUnramifiedCorrespondence

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ScalConjRow

theorem galD_of_inputs : GlobalTheory.Hk3.HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.LiftRows.SourceLevelLawC R.toRealDat F.lv2 → GlobalTheory.LiftRows.InnerProductFormulaC R.toRealDat F.lv2 → GlobalTheory.LiftRows.FockCoefficientC R.toRealDat F.lv2 → GlobalTheory.LiftRows.FiniteZetaL R.toRealDat F.lv2 → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → 0 < R.kap → (∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.toRealDat.LUnif → R.PLevW F → R.PThmA → (R.toCx3 F).PartsW false → (R.toCx3 F).GalD F.cr false := by
  intro hH D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s hOk hsep hC hEx h1 h2 h3 h4 hph hstd fw hbar hio hom hone hpt hR hL hHe hU hE hblk hrt hlt hltb honto hk hl hun hlev hA hsum
  have core := (GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx).1
  exact GlobalTheory.T.liftScalarIdentity_offFixedPlace_baseLevel hH GlobalTheory.T.conjugatesOfRationalThetaLift_from_characterisation T R F κ v₀ O s hOk hC hEx
    (GlobalTheory.T.conjugateDatum_lift_scalar_of_innerProductFormula R.toRealDat F.lv2 core hOk.ok2.irr h1 h2 h3 h4
      (GlobalTheory.RealCoefSq.lowestKType_coefficients_sq_integrable R.toRealDat F.lv2 core))
    hstd fw hbar hio hom hone hpt hun
    (GlobalTheory.scalConj_base_facts R F s hOk hsep hC hR hL hHe hU hE hblk hrt hlt hltb honto hk hl hun hlev hA hsum)

end GlobalTheory.ScalConjRow
end
end
