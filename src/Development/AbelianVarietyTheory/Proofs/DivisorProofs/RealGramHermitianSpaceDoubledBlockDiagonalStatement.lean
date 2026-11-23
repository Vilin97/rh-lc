module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceClosedUnderConjReflectionStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledCoordsThetaTransformProductEqTensorConj
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledGramSatisfiesXiRelation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalDarbouxStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPairPartnerInverseTransposeStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledCoordsThetaTransformProductEqTensorConjStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.doubledCoordsThetaTransform_product_eq_tensor_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  first | exact @GlobalTheory.Adopt.doubledCoordsThetaTransform_product_eq_tensor_conj | exact GlobalTheory.Adopt.doubledCoordsThetaTransform_product_eq_tensor_conj | (intros; apply GlobalTheory.Adopt.doubledCoordsThetaTransform_product_eq_tensor_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumFirstFactorOnDoublingTensor

section

@[expose] public section

namespace DoublingFirstFactorDivisor
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.DoublingFirstFactor

theorem doubled_first_factor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
    ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
    ∀ (g : GA D S) (f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
      ωd (GlobalTheory.Doubling.io S (g, 1), 1) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T f₁ f₂) =
        GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (ω (g, 1) f₁) f₂ := by
  intro D ψ _ S T χS χT ω hω ωd hωd g f₁ f₂ h₁ h₂
  have key := ((GlobalTheory.DoublingTheta.thetaClause D ψ S T χS χT ω ωd hω hωd f₁ f₂ h₁ h₂).2 g 1 1).1
  have e : ω ((1 : GA D S), (1 : GA D T)) = 1 := map_one ω
  rw [key, e, map_one, map_one, inv_one, Circle.coe_one, one_smul]
  rfl

end GlobalTheory.CompanionTheory.DoublingFirstFactor

end

end DoublingFirstFactorDivisor
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.Adopt.doubledWeilDatum_firstFactor_on_doublingTensor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
    ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
    ∀ (g : GA D S) (f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
      ωd (GlobalTheory.Doubling.io S (g, 1), 1) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T f₁ f₂) =
        GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (ω (g, 1) f₁) f₂ := by
  first | exact @DoublingFirstFactorDivisor.GlobalTheory.CompanionTheory.DoublingFirstFactor.doubled_first_factor | exact DoublingFirstFactorDivisor.GlobalTheory.CompanionTheory.DoublingFirstFactor.doubled_first_factor | (intros; apply DoublingFirstFactorDivisor.GlobalTheory.CompanionTheory.DoublingFirstFactor.doubled_first_factor <;> assumption)

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumFirstFactorOnDoublingTensorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.doubledWeilDatum_firstFactor_on_doublingTensor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
    ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
    ∀ (g : GA D S) (f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
      ωd (GlobalTheory.Doubling.io S (g, 1), 1) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T f₁ f₂) =
        GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (ω (g, 1) f₁) f₂ := by
  first | exact @GlobalTheory.Adopt.doubledWeilDatum_firstFactor_on_doublingTensor | exact GlobalTheory.Adopt.doubledWeilDatum_firstFactor_on_doublingTensor | (intros; apply GlobalTheory.Adopt.doubledWeilDatum_firstFactor_on_doublingTensor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformInjOnAdelicSchwartzSpace

section

@[expose] public section

namespace ThetaInjectivity
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThetaInj

theorem schr_reindex {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ κ' : Type}
    [Fintype κ] [Fintype κ'] (σ : κ ≃ κ') (w : (κ' → R) × (κ' → R)) (φ : (κ → R) → ℂ) (x : κ' → R) :
    GlobalTheory.WeilM.schr ψ w (fun u : κ' → R => φ (u ∘ σ)) x =
      GlobalTheory.WeilM.schr ψ (w.1 ∘ σ, w.2 ∘ σ) φ (x ∘ σ) := by
  have hd : ∀ u v : κ' → R, (u ∘ σ) ⬝ᵥ (v ∘ σ) = u ⬝ᵥ v := fun u v =>
    Equiv.sum_comp σ fun i => u i * v i
  simp only [GlobalTheory.WeilM.schr, hd]
  rfl

theorem thetaSum_reindex (F : Type) [Field F] [NumberField F] {κ κ' : Type} (σ : κ ≃ κ')
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (fun u : κ' → AdeleRing (𝓞 F) F => Φ (u ∘ σ)) = GlobalTheory.WeilM.thetaSum F Φ := by
  unfold GlobalTheory.WeilM.thetaSum
  exact (Equiv.arrowCongr σ.symm (Equiv.refl F)).tsum_eq
    (fun ξ : κ → F => Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))

theorem theta_transform_injOn : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w, GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ) = GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ')) →
      Φ = Φ' := by
  intro D ψ hψ κ _ Φ hΦ Φ' hΦ' h
  classical
  have hR : IsTotallyReal D.host.F := inferInstance
  let σ := Fintype.equivFin κ
  have key : ∀ (Ψ : (κ → AF D.host.F) → ℂ) (w : GlobalTheory.ThetaTransform.VA D.host.F (Fintype.card κ)),
      GlobalTheory.ThetaTransform.thV ψ (fun u : Fin (Fintype.card κ) → AF D.host.F => Ψ (u ∘ σ)) w =
        GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ (w.1 ∘ σ, w.2 ∘ σ) Ψ) := by
    intro Ψ w
    rw [← thetaSum_reindex D.host.F σ (GlobalTheory.WeilM.schr ψ (w.1 ∘ σ, w.2 ∘ σ) Ψ)]
    unfold GlobalTheory.ThetaTransform.thV
    congr 1
    funext x
    exact schr_reindex ψ σ w Ψ x
  have e := GlobalTheory.ThetaTransform.thV_injOn hR hψ.1 (GlobalTheory.ThetaTransform.comp_mem_schA σ hΦ)
    (GlobalTheory.ThetaTransform.comp_mem_schA σ hΦ') (funext fun w => by rw [key, key]; exact h _)
  funext x
  have := congrFun e (x ∘ σ.symm)
  simpa [Function.comp_assoc] using this

end GlobalTheory.CompanionTheory.ThetaInj

end

end ThetaInjectivity
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.Adopt.thetaTransform_injOn_adelicSchwartzSpace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w, GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ) = GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ')) →
      Φ = Φ' := by
  first | exact @ThetaInjectivity.GlobalTheory.CompanionTheory.ThetaInj.theta_transform_injOn | exact ThetaInjectivity.GlobalTheory.CompanionTheory.ThetaInj.theta_transform_injOn | (intros; apply ThetaInjectivity.GlobalTheory.CompanionTheory.ThetaInj.theta_transform_injOn <;> assumption)

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformInjOnAdelicSchwartzSpaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.thetaTransform_injOn_adelicSchwartzSpace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ],
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA D.host.F κ,
      (∀ w, GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ) = GlobalTheory.WeilM.thetaSum D.host.F (GlobalTheory.WeilM.schr ψ w Φ')) →
      Φ = Φ' := by
  first | exact @GlobalTheory.Adopt.thetaTransform_injOn_adelicSchwartzSpace | exact GlobalTheory.Adopt.thetaTransform_injOn_adelicSchwartzSpace | (intros; apply GlobalTheory.Adopt.thetaTransform_injOn_adelicSchwartzSpace <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealGramHermitianSpaceDoubledBlockDiagonal

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblRestr

open GlobalTheory.Doubling GlobalTheory.DblSchr GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero Formalism.IndefR.Datum

theorem partner_dbl {D : D7} (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))
    (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)))
    (hgd : gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1) (gs : GA D S) (hgs : mt S gs = (g⁻¹).1.1ᵀ)
    (gdd : GA D (dblSp S)) (hgdd : mt (dblSp S) gdd = ((reG _ finSumFinEquiv.symm (incM_JBd S JB) gd)⁻¹).1.1ᵀ) :
    gdd = io S (gs, 1) := by
  have hg1 : g.1.1 * (g⁻¹).1.1 = 1 := Units.mul_inv g.1
  have hinv : (gd⁻¹).1.1 = Matrix.fromBlocks (g⁻¹).1.1 0 0 (1 : Matrix (Fin S.rank) (Fin S.rank) _) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hgd, Matrix.fromBlocks_multiply, hg1]
    simp [Matrix.fromBlocks_one]
  have hr : ((reG _ finSumFinEquiv.symm (incM_JBd S JB) gd)⁻¹).1.1 =
      (Matrix.fromBlocks (g⁻¹).1.1 0 0 (1 : Matrix (Fin S.rank) (Fin S.rank) _)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← map_inv, reG_val, hinv]
  have hm3 : mt (dblSp S) (io S (gs, 1)) =
      (Matrix.fromBlocks (mt S gs) 0 0 (1 : Matrix (Fin S.rank) (Fin S.rank) _)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  have hm : mt (dblSp S) gdd = mt (dblSp S) (io S (gs, 1)) := by
    rw [hgdd, hr, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, ← hgs, hm3, Matrix.transpose_zero,
      Matrix.transpose_one]
  exact Subtype.ext (Units.ext hm)

theorem restr_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
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
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))
            (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB))),
            gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
            ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
              GlobalTheory.DblSchr.omdOf omd₀ gd (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (1, g) φ₁) φ₂ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom ωd hωd omd₀ homd g gd hgd φ₁ hφ₁ φ₂ hφ₂
  obtain ⟨gs, h1, hh1, hgs⟩ := GlobalTheory.T.unitaryPair_partner_inverse_transpose D S T JA JB ξ hA hB 1 g
  have h1e : h1 = 1 := Subtype.ext (Units.ext (hh1.trans rfl))
  obtain ⟨gdd, h2, hh2, hgdd⟩ := GlobalTheory.T.unitaryPair_partner_inverse_transpose D (dblSp S) T JA (JBd S JB) ξ hA (dblGram_xi D S JB ξ hB) 1
    (reG _ finSumFinEquiv.symm (incM_JBd S JB) gd)
  have h2e : h2 = 1 := Subtype.ext (Units.ext (hh2.trans rfl))
  have hgdd' : gdd = io S (gs, 1) := partner_dbl S JB g gd hgd gs hgs gdd hgdd
  subst h1e h2e hgdd'
  have t1 := hom 1 g gs 1 hh1 hgs φ₁ hφ₁
  have hΦ := GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ φ₁ hφ₁ φ₂ hφ₂
  have t2 := homd 1 (reG _ finSumFinEquiv.symm (incM_JBd S JB) gd) (io S (gs, 1)) 1 hh2 hgdd _ hΦ
  have hφ₂' := GlobalTheory.T.adelicSchwartzSpace_closed_under_conj_reflection D.host.F κ φ₂ hφ₂
  have th₁ := GlobalTheory.T.isThetaFunction_thetaTransform_rationalDarboux D ψ hψ S T JA JB ξ hA hB κ co hrat φ₁ hφ₁
  have th₂ := GlobalTheory.T.isThetaFunction_thetaTransform_rationalDarboux D ψ hψ S T JA JB ξ hA hB κ co hrat _ hφ₂'
  have key := t2.2.trans ((congrArg (ωd (io S (gs, 1), 1)) (GlobalTheory.T.doubledCoordsThetaTransform_product_eq_tensor_conj D ψ hψ S T JA JB ξ κ co φ₁ hφ₁ φ₂ hφ₂)).trans
    ((GlobalTheory.T.doubledWeilDatum_firstFactor_on_doublingTensor D ψ hψ S T χS χT ω hω ωd hωd gs _ _ th₁ th₂).trans
      ((congrArg (fun f => GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T f
        (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x))))) t1.2.symm).trans
        (GlobalTheory.T.doubledCoordsThetaTransform_product_eq_tensor_conj D ψ hψ S T JA JB ξ κ co _ t1.1 φ₂ hφ₂).symm)))
  refine GlobalTheory.T.thetaTransform_injOn_adelicSchwartzSpace D ψ hψ (κ ⊕ κ) _ t2.1 _ (GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ _ t1.1 φ₂ hφ₂) fun w => ?_
  have := congrFun key ((ddr co).e.symm w)
  simpa only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, LinearEquiv.apply_symm_apply] using this

end GlobalTheory.DblRestr

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealGramHermitianSpaceDoubledBlockDiagonalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.realGram_hermitianSpaceDoubled_blockDiagonal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
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
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))
            (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB))),
            gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
            ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
              GlobalTheory.DblSchr.omdOf omd₀ gd (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (1, g) φ₁) φ₂ := by
  first | exact @GlobalTheory.DblRestr.restr_boxFun | exact GlobalTheory.DblRestr.restr_boxFun | (intros; apply GlobalTheory.DblRestr.restr_boxFun <;> assumption)
end
end
