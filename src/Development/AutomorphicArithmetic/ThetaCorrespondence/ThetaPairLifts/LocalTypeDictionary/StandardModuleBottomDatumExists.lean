module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumMovedThetaVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuumEntireFactorIsThetaMovedLattices
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistEveryTupleOfCmThetaHypotheses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleUnitConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairBigMemberTwistedTuple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridConductorIdealCMIsCoprimeHalfDifferentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterFiniteIdeleValueEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumConjOfNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridCoreIffFirstRowExtByZero
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuConductorExponentsPosProdEqModulusStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicVacuumStandardLatticesReadsTheta

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.VacRead

theorem vacuum_reads_theta : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
  D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 → ∀ v : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (stdL D S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) v →
  ∃ G ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d), G ≠ 0 ∧ Reads ψ θ hS hT ⊤ δ 1 G v := by
  intro D ψ θ S T a d hS hT δ hcc hSet v hv
  subst hS hT
  have hδ : δ ≠ 0 := GlobalTheory.NormExact.delta_ne_zero hSet.crv
  have h1 : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) D.host.E), M = 1 →
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) ((1 : GL (Fin k) D.host.E) : Matrix (Fin k) (Fin k) D.host.E) * M *
        ((1 : GL (Fin k) D.host.E) : Matrix (Fin k) (Fin k) D.host.E) = 1 := by
    intro k M hM
    subst hM
    simp [Formalism.UG.cT]
  obtain ⟨Φ, hΦd, hΦ⟩ := GlobalTheory.FockPos.vacuum_real_entire ψ θ S T 1 1 _ _ (h1 _ hSet.gS) (h1 _ hSet.gT) v hv
  have hinV : ∀ {k : ℕ} (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)),
      GlobalTheory.MovedDict.inV (D := D) 1 L = (L : Set (Fin k → D.host.E)) := by
    intro k L
    simp [GlobalTheory.MovedDict.inV]
  have hv' := hv
  rw [← hinV (stdL D S.rank), ← hinV (stdL D T.rank)] at hv'
  have hC : Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ := by rw [hcc]; exact hSet.crv
  have hTh := GlobalTheory.ThetaLawMoved.theta_of_vacuum_moved ψ θ S T 1 1 (h1 _ hSet.gS) (h1 _ hSet.gT) δ hC hδ
    (stdL D S.rank) (stdL D T.rank) (GlobalTheory.MovedVacuum.sd_stdL D _) (GlobalTheory.MovedVacuum.sd_stdL D _) v hv' Φ hΦd hΦ
  rw [hcc] at hTh
  refine ⟨fun Y => Φ (δ⁻¹ • Y), hTh, ?_, ?_⟩
  · intro hG
    have h0 : v = 0 := GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real hv.2.theta (fun w hw => by
      rw [hΦ w hw]
      have e := congrFun hG (δ • GlobalTheory.FockPos.zCo θ 1 1 w)
      simp only [smul_smul, inv_mul_cancel₀ hδ, one_smul, Pi.zero_apply] at e
      rw [e, mul_zero])
    obtain ⟨⟨p, hp⟩, hq⟩ := hv.2.norm
    have e := hq p hp
    rw [h0] at e
    simp [nrm2] at e
  · rw [GlobalTheory.NormExact.reads_iff hSet.crv hSet.scale]
    refine ⟨hv.2.theta, fun w hw => ?_⟩
    rw [hΦ w hw]
    congr 2
    funext τ i j
    simp [smul_eq_mul, map_one, mul_one, inv_mul_cancel_left₀ hδ]

end GlobalTheory.VacRead
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicVacuumStandardLatticesReadsThetaStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead


theorem _root_.GlobalTheory.T.adelicVacuum_standardLattices_readsTheta : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
  D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 → ∀ v : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (stdL D S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) v →
  ∃ G ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d), G ≠ 0 ∧ Reads ψ θ hS hT ⊤ δ 1 G v := by
  first | exact @GlobalTheory.VacRead.vacuum_reads_theta | exact GlobalTheory.VacRead.vacuum_reads_theta | (intros; apply GlobalTheory.VacRead.vacuum_reads_theta <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerModelComplexConjugateNegForm

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.ConjSchr

variable {D : D7}

theorem symplO_negS (S T : HSp D) (x y : WO S T) :
    symplO (GlobalTheory.ChiGrid.negSp S) T x y = -symplO S T x y := by
  simp only [symplO, hO, GlobalTheory.ChiGrid.negSp_gram, GlobalTheory.CjNeg.inv_neg_mat, Matrix.neg_apply, map_neg, neg_mul, mul_neg,
    Finset.sum_neg_distrib]

def cjF {X : Type} (g : X → ℂ) : X → ℂ := fun w => starRingEnd ℂ (g w)

theorem heisO_conj {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (x : WO S T)
    (g : WO S T → ℂ) :
    heisO ψ S T x (cjF g) = cjF (heisO ψ (GlobalTheory.ChiGrid.negSp S) T x g) := by
  funext w
  simp only [cjF, heisO, map_mul, GlobalTheory.CjNeg.conj_psi hψ, GlobalTheory.CjNeg.symplOH_negS, neg_neg]

theorem cjF_cjF {X : Type} (g : X → ℂ) : cjF (cjF g) = g := by
  funext w; simp [cjF]

def conjLin {X : Type} (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) : (X → ℂ) →ₗ[ℂ] (X → ℂ) where
  toFun g := cjF (T (cjF g))
  map_add' g h := by
    have : cjF (g + h) = cjF g + cjF h := by funext w; simp [cjF]
    funext w; simp [this, cjF]
  map_smul' c g := by
    have : cjF (c • g) = starRingEnd ℂ c • cjF g := by funext w; simp [cjF]
    funext w; simp [this, cjF]

theorem conjLin_apply {X : Type} (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) (g : X → ℂ) :
    conjLin T g = cjF (T (cjF g)) := rfl

theorem isSBHalf_cjF {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ : Mx D m n → ℂ}
    (h : IsSBHalf e Λ Φ) : IsSBHalf e Λ (cjF Φ) := by
  obtain ⟨hs, k, hk, hinv, hsupp⟩ := h
  refine ⟨fun t ht => hs t ?_, k, hk, fun u hu hue t => ?_, fun t ht => hsupp t ?_⟩
  · intro h0; apply ht; simp [cjF, h0]
  · simp only [cjF, hinv u hu hue t]
  · intro h0; apply ht; simp [cjF, h0]

theorem isPlaceModel_conjLin {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {e : AE D}
    {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h : IsPlaceModel ψ (symplO (GlobalTheory.ChiGrid.negSp S) T) (heisO ψ (GlobalTheory.ChiGrid.negSp S) T) e Λ 1 f₀ T₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (cjF f₀) (conjLin T₀) := by
  constructor
  · intro Φ hΦ x hx
    have e1 := h.trans _ (isSBHalf_cjF hΦ) x hx
    rw [conjLin_apply, conjLin_apply, heisO_conj hψ]
    have e2 : cjF (fun t => Φ (t + x)) = fun t => cjF Φ (t + x) := rfl
    rw [e2, e1]
  · intro Φ hΦ y hy
    have e1 := h.modul _ (isSBHalf_cjF hΦ) y hy
    rw [conjLin_apply, conjLin_apply, heisO_conj hψ]
    have e2 : cjF (fun t => ψ (symplO S T t y) * Φ t) =
        fun t => ψ (symplO (GlobalTheory.ChiGrid.negSp S) T t y) * cjF Φ t := by
      funext t; simp only [cjF, map_mul, GlobalTheory.CjNeg.conj_psi hψ, symplO_negS]
    rw [e2, e1]
  · have e2 : cjF ((1 : ℂ) • halfInd e Λ) = (1 : ℂ) • halfInd e Λ := by
      funext t; simp only [cjF, one_smul, halfInd]; split_ifs <;> simp
    rw [conjLin_apply, e2, h.vac]

end GlobalTheory.ConjSchr

open GlobalTheory.ConjSchr in
theorem GlobalTheory.ConjSchr.conj_schroedinger_neg : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A WW : HSp D) (e : AE D) (ΛA : Set (Fin A.rank → D.host.E))
  (ΛW : Set (Fin WW.rank → D.host.E)) (vac Φ f : WO A WW → ℂ),
  IsThetaAt ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO ψ (GlobalTheory.Grid.neg A) WW) e (latO (GlobalTheory.Grid.neg A) WW ΛA ΛW fun _ => True) 1 vac Φ f →
  ∃ Tm : (WO A WW → ℂ) →ₗ[ℂ] (WO A WW → ℂ),
    IsPlaceModel ψ (symplO A WW) (heisO ψ A WW) e (latO A WW ΛA ΛW fun _ => True) 1 (fun w => starRingEnd ℂ (vac w)) Tm ∧
      (fun w => starRingEnd ℂ (f w)) = Tm (fun w => starRingEnd ℂ (Φ w)) := by
  intro D ψ hψ A WW e ΛA ΛW vac Φ f hT
  have hL : latO (GlobalTheory.Grid.neg A) WW ΛA ΛW (fun _ => True) = latO A WW ΛA ΛW (fun _ => True) :=
    GlobalTheory.CoreRowLat.latO_negSp A WW ΛA ΛW _
  obtain ⟨⟨T₀, h0⟩, hall⟩ := hT
  have hf : f = T₀ Φ := hall T₀ h0
  rw [hL] at h0
  refine ⟨conjLin T₀, isPlaceModel_conjLin hψ h0, ?_⟩
  show cjF f = conjLin T₀ (cjF Φ)
  rw [conjLin_apply, cjF_cjF, hf]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerModelComplexConjugateNegFormStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead


theorem _root_.GlobalTheory.T.schrodingerModel_complexConjugate_negForm : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A WW : HSp D) (e : AE D) (ΛA : Set (Fin A.rank → D.host.E))
  (ΛW : Set (Fin WW.rank → D.host.E)) (vac Φ f : WO A WW → ℂ),
  IsThetaAt ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO ψ (GlobalTheory.Grid.neg A) WW) e (latO (GlobalTheory.Grid.neg A) WW ΛA ΛW fun _ => True) 1 vac Φ f →
  ∃ Tm : (WO A WW → ℂ) →ₗ[ℂ] (WO A WW → ℂ),
    IsPlaceModel ψ (symplO A WW) (heisO ψ A WW) e (latO A WW ΛA ΛW fun _ => True) 1 (fun w => starRingEnd ℂ (vac w)) Tm ∧
      (fun w => starRingEnd ℂ (f w)) = Tm (fun w => starRingEnd ℂ (Φ w)) := by
  first | exact @GlobalTheory.ConjSchr.conj_schroedinger_neg | exact GlobalTheory.ConjSchr.conj_schroedinger_neg | (intros; apply GlobalTheory.ConjSchr.conj_schroedinger_neg <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.StandardModuleBottomDatumExists

section

@[expose] public section

section
noncomputable section
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead
namespace GlobalTheory.StdRead
variable {D : D7}
variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
end GlobalTheory.StdRead
end
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.StdRead
theorem standard_module_bottom_datum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∀ (r : ℂ) (rc : ℝ), r ≠ 0 → (Formalism.MainNotions.StandardLatticesGL3.Crv D ⊤ δ → r = -δ) → (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) →
        (∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧
            ∀ (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
              GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
              GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
                P.W.Om x h (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)))) →
      ∃ κ : ℂ, κ ≠ 0 ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) = (κ * starRingEnd ℂ u) • P.F := by
  intro _ _ _ hInp _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro W hW i j A A' WW X δ t0 hX hβ r rc _ hr hrc _
  have hI := hInp D
  by_cases hC : Crv D ⊤ δ
  swap
  · exact ⟨1, one_ne_zero, fun s Q P _ _ => absurd P.crv hC⟩
  obtain rfl := hr hC
  have hcc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hIs := hX.is
  have hθ : IsInfFam W.θ := hIs.isVac.2.inf
  have hsc : GlobalTheory.NormExact.IsScale D ⊤ 1 := hcc ▸ GlobalTheory.NormExact.isScale_one D
  have hs : GlobalTheory.NormExact.Setup W.ψ W.θ A WW ⊤ δ 1 := ⟨hW, hθ, hX.std.1, hX.stdW.1, hC, hsc⟩
  have hδ := GlobalTheory.NormExact.delta_ne_zero hC
  have hrc' : rc = (area (lamOf D ⊤ δ))⁻¹ := by
    obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
    have h1 := hrc τ
    have h2 := GlobalTheory.NormExact.normSq_scale top_ne_bot hsc δ τ
    have hA := GlobalTheory.NormExact.area_pos hC
    have hx := GlobalTheory.NormExact.xiR_pos D
    rw [map_one, mul_one] at h2
    rw [norm_neg, ← Complex.normSq_eq_norm_sq, h2, GlobalTheory.FockPos.norm_embedding_xi0_eq] at h1
    field_simp
    have : 2 * Formalism.L2.Pj.xiR D * (rc * area (lamOf D ⊤ δ) - 1) = 0 := by linear_combination h1
    have h3 := (mul_eq_zero.1 this).resolve_left (by positivity)
    linarith
  subst hrc'
  have hΛ : ∀ {V : HSp D} (ρ : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V), ρ.IsStd → ρ.Λ = stdL D V.rank := fun ρ h => by
    ext y
    rw [h.2.1]
    simp [stdL, Submodule.mem_pi, Submodule.mem_one]
  have hΛA := hΛ X.rA hX.std
  have hΛW := hΛ X.rW hX.stdW
  have hv : IsVacO W.ψ W.θ A WW (fun _ => 1) (fun _ => 1) (stdL D A.rank : Set (Fin A.rank → D.host.E))
      (stdL D WW.rank : Set (Fin WW.rank → D.host.E)) (fun w => starRingEnd ℂ (X.vac w)) := by
    have h := GlobalTheory.VacConj.isVacO_conj_negSp W.ψ W.θ A WW X.rA.s X.rW.s _ _ X.vac hIs.isVac
    rwa [hΛA, hΛW, show X.rA.s = fun _ => 1 from funext fun τ => (hX.std.2.2 τ).1,
      show X.rW.s = fun _ => 1 from funext fun τ => (hX.stdW.2.2 τ).1] at h
  obtain ⟨G0, hG0, hne, hread⟩ := GlobalTheory.T.adelicVacuum_standardLattices_readsTheta W.ψ W.θ A WW rfl rfl δ hcc hs _ hv
  obtain ⟨κ, hκ, hc⟩ := exists_const hI δ t0 G0 hG0 hne
  have hc' : ∀ (a d : ℕ) (ea : a = A.rank) (ed : d = WW.rank) (e0 : VC D a d → ℂ), GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 →
      oddE0 D ⊤ δ t0 a d e0 → e0 ≠ 0 → ∃ u, IsPh u ∧ (κ * u) • e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) ∧
        GlobalTheory.NormExact.Reads W.ψ W.θ ea.symm ed.symm ⊤ δ 1 ((κ * u) • e0) (fun w => starRingEnd ℂ (X.vac w)) := by
    rintro a d rfl rfl e0 h1 h2 h3
    obtain ⟨u, hu, e⟩ := hc e0 hC h1 h2 h3
    exact ⟨u, hu, e ▸ hG0, e ▸ hread⟩
  refine ⟨κ, hκ, fun s Q P P' hB => ?_⟩
  have ea : P.a = A.rank := hB.rank.1.trans hX.rank.symm
  have ed : P.d = WW.rank := by rw [hB.rank.2.2.1, ← hIs.rank, hX.rank, hX.rank']
  obtain ⟨u, hu, hTh, hrd⟩ := hc' _ _ ea ed P.e0 P.pt0 P.vac P.W.nz
  obtain ⟨c0, cI⟩ := GlobalTheory.T.squareNuConductorExponents_pos_prod_eq_modulus G hL s i j (X.c s) (hIs.expo s)
  obtain ⟨q1, q2⟩ := GlobalTheory.SqTop.BotT.pde_ne_q hR
  have hm : GoodMod (X.e s) (GlobalTheory.SqTop.modT G s) := ⟨_, _, hIs.idem s, c0, cI.symm,
    GlobalTheory.FunObj.StdDatum.TwBig.modT_isCoprime_bb hL G s (GlobalTheory.T.gridConductorIdealCM_isCoprime_halfDifferent G.pl q1 q2)⟩
  have hν : GlobalTheory.NormExact.HasFinPart (G.nu s i (j + 1))⁻¹ P.W.chV' P.W.ep' := fun x y hxy => by
    rw [hB.chars.2 y, MonoidHom.inv_apply, Circle.coe_inv, GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ (chrEq_nu G s i j hL) x y hxy]
    exact (Units.val_inv_eq_inv_val _).symm
  obtain ⟨Tm, hTm, hf⟩ := GlobalTheory.T.schrodingerModel_complexConjugate_negForm W.ψ hW A WW _ _ _ _ _ _ (hIs.fst s)
  have eν : Lc.mu s (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) =
      G.nu s i (j + 1) := mul_div_mul_right_eq_div _ _ _
  have eI : X.ideal (locPl G) s = GlobalTheory.SqTop.modT G s := cI
  rw [hΛA, hΛW] at hTm
  rw [eν, eI, hβ] at hf
  obtain ⟨u', hu', hrf⟩ := reads_std hI P ea.symm ed.symm hcc hs hv hTh hrd hm hν (killsCong hL G s i j)
    (hΛA ▸ hIs.rigA.2.1) hB.std hTm hf
  have hw := (hu.mul hu').conj
  refine ⟨_, fun h => by simpa [h] using hw.1, hw.2.1, fun p _ _ lam => hw.2.2 p lam, fun ea' ed' => ?_⟩
  rw [xiN_eq hθ _ _ hδ hrf, Complex.conj_conj, mul_assoc]
end GlobalTheory.StdRead
end
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.standard_module_bottom_datum_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∀ (r : ℂ) (rc : ℝ), r ≠ 0 → (Formalism.MainNotions.StandardLatticesGL3.Crv D ⊤ δ → r = -δ) → (∀ τ, rc * ‖r‖ ^ 2 = 2 * ‖tauE D τ D.host.xi0‖) →
        (∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧
            ∀ (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
              GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
              GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.ω s (y, g) (X.f s) w)) =
                P.W.Om x h (GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)))) →
      ∃ κ : ℂ, κ ≠ 0 ∧
        ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank),
            GlobalTheory.AdForm.xiN W.θ A WW ea.symm ed.symm r rc (fun w => starRingEnd ℂ (X.f s w)) = (κ * starRingEnd ℂ u) • P.F := by
  first | exact @_root_.GlobalTheory.StdRead.standard_module_bottom_datum | exact _root_.GlobalTheory.StdRead.standard_module_bottom_datum | (intros; apply _root_.GlobalTheory.StdRead.standard_module_bottom_datum <;> assumption)
end
end
end
