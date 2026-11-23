module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawOneSourceOrthogonalSumTargets
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridHeckeCharactersExist
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumDiagThetaProductEqScalarSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledCoordsThetaTransformProductEqTensorConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerOperatorMemAdelicSchwartzStdChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumDiagActsOnExternalProduct

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblRestrictChar

open Formalism.IndefR.Datum



theorem dbl_diag_box : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
      ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
        Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
        (∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∃ c : ℂ, ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = c • (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)))) →
        ∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) := by
  intro D ψ hψ S T χS χT ω hω ωd hωd _ h hd hhd f₁ f₂ hf₁ hf₂
  obtain ⟨ωB, hB⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S (GlobalTheory.ChiGrid.negSp T) χS χT⁻¹
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecS (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_inv hω.hecT) hω.resS
    (resEta_inv hω.resT)
  let d := GlobalTheory.BiTransfer.sumDec T (GlobalTheory.ChiGrid.negSp T)
  have hωd' : IsWeilDatumO ψ S (GlobalTheory.Doubling.hsum T (GlobalTheory.ChiGrid.negSp T)) χS (χT * χT⁻¹) ωd := by
    rw [mul_inv_cancel]; exact hωd
  have key := (GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ _ T (GlobalTheory.ChiGrid.negSp T) d S).om_box χS χT χT⁻¹ ωd ω ωB
    hωd' hω hB 1 h 1 f₁ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f₂) hf₁ (GlobalTheory.CjNeg.theta_negT hψ hf₂)
  have e1 : d.emb (h, 1) = hd := by
    apply GlobalTheory.MixModel.mt_injective (GlobalTheory.Doubling.hsum T (GlobalTheory.ChiGrid.negSp T))
    rw [GlobalTheory.SeesawSumTarget.emb_sumDec, GlobalTheory.SquareComm.mt_blk]
    refine Eq.trans ?_ hhd.symm
    rw [GlobalTheory.Doubling.blkMat, Matrix.reindex_apply, GlobalTheory.AdelicLatMove.mt_one]
  have e2 : ωB ((1 : GA D S), (1 : GA D (GlobalTheory.ChiGrid.negSp T))) = 1 := map_one ωB
  rw [e1, e2, Module.End.one_apply, GlobalTheory.SeesawSumTarget.boxT_sumDec, GlobalTheory.SeesawSumTarget.boxT_sumDec] at key
  exact key

end GlobalTheory.DblRestrictChar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumDiagActsOnExternalProductStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.doubledWeilDatum_diag_acts_on_externalProduct : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
      ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
        Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
        (∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∃ c : ℂ, ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = c • (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)))) →
        ∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) := by
  first | exact @GlobalTheory.DblRestrictChar.dbl_diag_box | exact GlobalTheory.DblRestrictChar.dbl_diag_box | (intros; apply GlobalTheory.DblRestrictChar.dbl_diag_box <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumDiagThetaProductEqScalarSmulStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.doubledWeilDatum_diag_thetaProduct_eq_scalar_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
      ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
        Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
        ∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∃ c : ℂ, ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = c • (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) := by
  first | exact @GlobalTheory.DblThetaRestrict.scalar | exact GlobalTheory.DblThetaRestrict.scalar | (intros; apply GlobalTheory.DblThetaRestrict.scalar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformDoubledCoordsBoxProduct

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DblTarget.ThetaBox

variable {F : Type} [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)]

theorem thetaSum_schr_negY (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hu : ∀ a, ‖ψ a‖ = 1) {κ : Type} [Fintype κ]
    (x y : κ → AdeleRing (𝓞 F) F) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, -y) φ) =
      star (GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) (fun u => star (φ u)))) := by
  have hc : ∀ t, starRingEnd ℂ (ψ t) = ψ (-t) := fun t => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hu t)]
  unfold GlobalTheory.WeilM.thetaSum
  rw [Complex.star_def, Complex.conj_tsum]
  refine tsum_congr fun ξ => ?_
  generalize (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = a
  simp only [GlobalTheory.WeilM.schr, map_mul, Complex.star_def, Complex.conj_conj, hc, dotProduct_neg, neg_add, mul_neg]

end GlobalTheory.WeilSchrodinger.DblTarget.ThetaBox


open GlobalTheory.WeilSchrodinger.DblTarget.ThetaBox in
theorem GlobalTheory.WeilSchrodinger.DblTarget.thetaTr_coDbl_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) =>
            GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) *
              star (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => star (φ₂ x)) (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)) := by
  intro D ψ hψ S T JA JB ξ hA κ _ co φ₁ h₁ φ₂ h₂
  funext w
  have he : (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co).e w =
      (Sum.elim (co.e (w.submatrix (finSumFinEquiv ∘ Sum.inl) id)).1 (co.e (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)).1,
        Sum.elim (co.e (w.submatrix (finSumFinEquiv ∘ Sum.inl) id)).2
          (-(co.e (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)).2)) := rfl
  have hs : ∀ (v : (κ → AF D.host.F) × (κ → AF D.host.F)) (φ : (κ → AF D.host.F) → ℂ),
      φ ∈ GlobalTheory.WeilM.schA D.host.F κ → GlobalTheory.WeilM.schr ψ v φ ∈ GlobalTheory.WeilM.schA D.host.F κ :=
    fun v φ hφ => GlobalTheory.SchrSchA.schr_mem_schA_of_isStdChar D ψ hψ κ v φ hφ
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho]
  rw [he, DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.schr_boxFun_elim,
    DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaSum_boxFun _ (hs _ _ h₁) (hs _ _ h₂), thetaSum_schr_negY ψ hψ.1.2.1]

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformDoubledCoordsBoxProductStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.thetaTransform_doubledCoords_boxProduct : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) =>
            GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) *
              star (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => star (φ₂ x)) (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)) := by
  first | exact @GlobalTheory.WeilSchrodinger.DblTarget.thetaTr_coDbl_boxFun | exact GlobalTheory.WeilSchrodinger.DblTarget.thetaTr_coDbl_boxFun | (intros; apply GlobalTheory.WeilSchrodinger.DblTarget.thetaTr_coDbl_boxFun <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumDoubledTargetRestrictBoxTens

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DblRestrict



theorem omp_diag_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
          ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
          ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
          ∀ omp : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →*
                Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) ωd omp →
          ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
            (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ))),
            gd.1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1.1 0 0 1) →
            ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
              omp (gd, 1) (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (g, 1) φ₁) φ₂ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom ωd hωd omp homp g gd hgd φ₁ hφ₁ φ₂ hφ₂
  let h : GA D T := ⟨g.1, GlobalTheory.ThetaTransform.mem_GA_target hA g⟩
  let hd : GA D (GlobalTheory.Doubling.dblSp T) := ⟨gd.1, GlobalTheory.ThetaTransform.mem_GA_target rfl gd⟩
  have hh : Formalism.L2.Theta.mt T h = g.1.1 := rfl
  have hhd : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd = gd.1.1 := rfl
  have h1S : Formalism.L2.Theta.mt S 1 = ((1 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))⁻¹).1.1ᵀ := by
    simp [Formalism.L2.Theta.mt]
  obtain ⟨hB1, hΘ1⟩ := hom g 1 1 h hh h1S φ₁ hφ₁
  have hbox := GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ φ₁ hφ₁ φ₂ hφ₂
  obtain ⟨hA1, hΘA⟩ := homp gd 1 1 hd hhd h1S _ hbox
  have hφ₂' := GlobalTheory.ConjSch.star_mem_schA κ φ₂ hφ₂
  have bij := GlobalTheory.ThetaTransform.thetaTr_bij co hψ hA hB hrat
  have bijd := GlobalTheory.ThetaTransform.thetaTr_bij (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) hψ rfl hB
    (GlobalTheory.WeilSchrodinger.DblTarget.coDbl_rat hA co hrat)
  refine bijd.2.1 _ hA1 _ (GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ _ hB1 φ₂ hφ₂) ?_
  have e1 := GlobalTheory.T.thetaTransform_doubledCoords_boxProduct D ψ hψ S T JA JB ξ hA κ co _ hφ₁ _ hφ₂
  have e2 := GlobalTheory.T.thetaTransform_doubledCoords_boxProduct D ψ hψ S T JA JB ξ hA κ co _ hB1 _ hφ₂
  have hgd' : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) := hgd
  have key := GlobalTheory.T.doubledWeilDatum_diag_acts_on_externalProduct D ψ hψ S T χS χT ω hω ωd hωd (GlobalTheory.T.doubledWeilDatum_diag_thetaProduct_eq_scalar_smul D ψ hψ S T χS χT ω hω ωd hωd) h hd hgd' _ _
    ((bij.2.2 _).2 ⟨φ₁, hφ₁, rfl⟩) ((bij.2.2 _).2 ⟨_, hφ₂', rfl⟩)
  refine hΘA.trans ?_
  refine ((congrArg (ωd (1, hd)) e1).trans key).trans ?_
  refine Eq.trans ?_ e2.symm
  rw [hΘ1]

end GlobalTheory.WeilSchrodinger.DblRestrict

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumDoubledTargetRestrictBoxTensStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.transportedWeilDatum_doubledTarget_restrict_boxTensor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
          ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
          ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
          ∀ omp : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →*
                Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) ωd omp →
          ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
            (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ))),
            gd.1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1.1 0 0 1) →
            ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
              omp (gd, 1) (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (g, 1) φ₁) φ₂ := by
  first | exact @GlobalTheory.WeilSchrodinger.DblRestrict.omp_diag_boxFun | exact GlobalTheory.WeilSchrodinger.DblRestrict.omp_diag_boxFun | (intros; apply GlobalTheory.WeilSchrodinger.DblRestrict.omp_diag_boxFun <;> assumption)
end
end
