module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixCoeffRightTranslateDefiniteFormScalarStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealInvariantSesquilinearFormEqSmulInnerStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometry
import Mathlib.RingTheory.PiTensorProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralNormSqMatrixCoefficientNeZeroDefinite

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory

theorem integral_normSq_coef_ne_zero : ∀ (D : D7) (V : HSp D), V.SigOK → V.IsPosDef → ∀ (c : CoefA V), c.Is → ∀ w : c.W, w ≠ 0 → ∀ mR : Measure (GinfC V), mR.IsHaarMeasure → ∫ b : GinfC V, ‖⟪w, c.ρ (b : GA D V) w⟫_ℂ‖ ^ 2 ∂mR ≠ 0 := by
  intro D V hS hp c hc w hw mR hR
  have : CompactSpace (GinfC V) :=
    isCompact_iff_compactSpace.1 (Formalism.IndefR.Eqv.isCompact_GinfC hS fun τ => Or.inl (hp τ))
  set f : GinfC V → ℝ := fun b => ‖⟪w, c.ρ (b : GA D V) w⟫_ℂ‖ ^ 2 with hfdef
  have hcont : Continuous f := by
    have h1 : Continuous fun b : GinfC V => c.ρ (b : GA D V) w := (hc.2.2.1 w).comp continuous_subtype_val
    exact ((continuous_const.inner h1).norm).pow 2
  have hnn : 0 ≤ f := fun b => by positivity
  have hint : Integrable f mR := hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have h1 : f 1 ≠ 0 := by
    simp only [hfdef, OneMemClass.coe_one, map_one, Module.End.one_apply]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (inner_self_ne_zero.2 hw))
  have hpos : 0 < ∫ b, f b ∂mR := by
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    exact hcont.isOpen_support.measure_pos mR ⟨1, h1⟩
  exact hpos.ne'

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralNormSqMatrixCoefficientNeZeroDefiniteStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

theorem _root_.GlobalTheory.T.integral_normSq_matrix_coefficient_ne_zero_definite : ∀ (D : D7) (V : HSp D), V.SigOK → V.IsPosDef → ∀ (c : CoefA V), c.Is → ∀ w : c.W, w ≠ 0 → ∀ mR : Measure (GinfC V), mR.IsHaarMeasure → ∫ b : GinfC V, ‖⟪w, c.ρ (b : GA D V) w⟫_ℂ‖ ^ 2 ∂mR ≠ 0 := by
  first | exact @GlobalTheory.integral_normSq_coef_ne_zero | exact GlobalTheory.integral_normSq_coef_ne_zero | (intros; apply GlobalTheory.integral_normSq_coef_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCoefficientPureTensorEqSmulInner

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
noncomputable section
open scoped ComplexConjugate

namespace GlobalTheory.WeilCoefScalar

theorem integrableOn_mul_conj {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) {ν : Measure (WO S T)}
    {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕) :
    IntegrableOn (fun w => f w * conj (g w)) 𝓕 ν := by
  refine GlobalTheory.MixModel.covolOne_integrableOn hν _
    (hf.cont.mul (Complex.continuous_conj.comp hg.cont)) ?_
  rintro _ ⟨γ, rfl⟩ a
  have e1 := hf.quasi γ a
  have e2 := hg.quasi γ a
  have hn : ∀ x, conj (ψ x) * ψ x = 1 := fun x => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ.1.2.1 x]; norm_num
  change f (ratW T S γ + a) * conj (g (ratW T S γ + a)) = f a * conj (g a)
  rw [e1, e2, map_mul]
  linear_combination (f a * conj (g a)) * hn (-symplOH S T (ratW T S γ) a)

end GlobalTheory.WeilCoefScalar

namespace GlobalTheory.WeilCoefScalar

theorem wcoef_pure_eq_smul_inner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) ν 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) ν 𝓕 → ∃ z : ℂ, (∀ (w : (R.cV i).W), ∀ b ∈ GinfC (Vc D i), GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) b = z * ⟪w, (R.cV i).ρ b w⟫_ℂ) ∧ ∀ w : (R.cV i).W, R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w) ≠ 0 → z ≠ 0 := by

  intro D G _ _ Pl0 T A Ks _ _ _ R F hC _hF i t v ν 𝓕 hν
  have hc : (R.cV i).Is := hC.models.cV i
  have hW := hC.thP.ωP i t
  have hio := (hC.thP.ioP i t).1
  let J : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) :=
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
      (onb (R.MW i (sg0 D A))) (R.vP i t)).comp (R.ioP i (PiTensorProduct.tprod ℂ v))
  have hJ : ∀ x, R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) x) = J x := fun x => rfl
  have hth : ∀ x, IsThetaFunO R.ψ (Vc D i) (Wc D i) (J x) := fun x => hC.thP.pt_theta i t _
  have hint : ∀ x y, IntegrableOn (fun w => J y w * conj (J x w)) 𝓕 ν := fun x y =>
    integrableOn_mul_conj hW.std (hth y) (hth x) hν
  let B : (R.cV i).W →ₗ⋆[ℂ] (R.cV i).W →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ∫ w in 𝓕, J y w * conj (J x w) ∂ν)
      (fun x x' y => by
        simp only [map_add (f := _), Pi.add_apply, mul_add]
        exact integral_add (hint x y) (hint x' y))
      (fun a x y => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
        rw [← integral_const_mul]
        congr 1; funext w; ring)
      (fun x y y' => by
        simp only [map_add (f := _), Pi.add_apply, add_mul]
        exact integral_add (hint x y) (hint x y'))
      (fun a x y => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext w; ring)
  have hB : ∀ x y, B x y = ∫ w in 𝓕, J y w * conj (J x w) ∂ν := fun x y => rfl
  have hom : ∀ u ∈ GinfC (Vc D i), ∀ x, R.ωP i t (u, 1) (J x) = J ((R.cV i).ρ u x) := fun u hu x => by
    rw [← hJ, ← hJ]; exact hio u hu _ x
  have hinv : ∀ u ∈ GinfC (Vc D i), ∀ x y, B ((R.cV i).ρ u x) ((R.cV i).ρ u y) = B x y := by
    intro u hu x y
    rw [hB, hB, ← hom u hu x, ← hom u hu y]
    exact GlobalTheory.Mem.LiftPolar.scalar_eq D R.ψ hW.std _ _ ν 𝓕 hν.1 hν.2.1 (R.ωP i t (u, 1))
      (fun f hf => hW.om_pres _ f hf) (fun f hf => hW.om_unit ν 𝓕 hν.1 hν.2.1 _ f hf) (J y) (J x) (hth y) (hth x)
  obtain ⟨z, hz⟩ := GlobalTheory.T.real_invariant_sesquilinear_form_eq_smul_inner D (Vc D i) (R.cV i) hc B hinv
  refine ⟨z, fun w b hb => ?_, fun w hw hz0 => ?_⟩
  · rw [hJ, ← hz, hB, GlobalTheory.Core.Rk.IP.wcoef, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, hom b hb w]
  · rw [hJ] at hw
    have h1 := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hW.std (hth w) hw hν
    apply h1
    have h2 := hz w w
    rw [hz0, zero_mul, hB] at h2
    rw [GlobalTheory.RawLift.thetaIP, ← h2]
    congr 1; funext x
    rw [Complex.star_def, mul_comm]

end GlobalTheory.WeilCoefScalar
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCoefficientPureTensorEqSmulInnerStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

theorem _root_.GlobalTheory.T.weilCoefficient_pureTensor_eq_smul_inner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) ν 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) ν 𝓕 → ∃ z : ℂ, (∀ (w : (R.cV i).W), ∀ b ∈ GinfC (Vc D i), GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) b = z * ⟪w, (R.cV i).ρ b w⟫_ℂ) ∧ ∀ w : (R.cV i).W, R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w) ≠ 0 → z ≠ 0 := by
  first | exact @GlobalTheory.WeilCoefScalar.wcoef_pure_eq_smul_inner | exact GlobalTheory.WeilCoefScalar.wcoef_pure_eq_smul_inner | (intros; apply GlobalTheory.WeilCoefScalar.wcoef_pure_eq_smul_inner <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntegralThetaLiftDefiniteFormNeZero

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.Core.Rk.RealOcc

theorem pt_ne : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → R.FullP →
    ∀ (i : Fin D.R.m) (t : T), ∃ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (w : (R.cV i).W),
      R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w) ≠ 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hF i t
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)
  have hL : GlobalTheory.RawLift.Laws R F := ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.thP⟩
  obtain ⟨-, v, w, -, hne⟩ := GlobalTheory.RawLift.vecNe D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ
  refine ⟨v, w, fun h => hne ?_⟩
  unfold GlobalTheory.RawLift.jointVec GlobalTheory.RawLift.thetaIP
  rw [h]
  simp



theorem real_ne : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t (y : (R.HV i t).H), y ≠ 0 → ∀ m : Measure (GA D (Vc D i)), m.IsHaarMeasure → ∃ (l : (R.cV i).W →ₗ[ℂ] ℂ) (P : PolF D (Wc D i).rank (Vc D i).rank), ∀ ν 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) ν 𝓕 → ∀ mR : Measure (GinfC (Vc D i)), mR.IsHaarMeasure → ∫ b : GinfC (Vc D i), GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t P) (R.ptP i t P) b * GlobalTheory.Core.Rk.IP.rcoef m (fun g => l (R.extV i t y g)) (fun g => l (R.extV i t y g)) b ∂mR ≠ 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t y hy m hm
  obtain ⟨v, w, hJ⟩ := pt_ne D G Pl0 T A Ks R F hG.core hF i t
  have hw : w ≠ 0 := by
    rintro rfl
    refine hJ ?_
    rw [map_zero]
    unfold RealDat.ptP
    exact map_zero _
  have H2 := GlobalTheory.T.matrixCoeff_rightTranslate_definiteForm_scalar D G Pl0 T A Ks R F hG.core i t y m hm
  obtain ⟨z2, h2, h2ne⟩ := H2
  refine ⟨innerₛₗ ℂ w, R.ioP i (PiTensorProduct.tprod ℂ v) w, fun ν 𝓕 hν mR hmR => ?_⟩
  have H1 := GlobalTheory.T.weilCoefficient_pureTensor_eq_smul_inner D G Pl0 T A Ks R F hG.core hF i t v ν 𝓕 hν
  obtain ⟨z1, h1, h1ne⟩ := H1
  have e1 : ∀ b : GinfC (Vc D i),
      GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w))
                   (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) b = z1 * ⟪w, (R.cV i).ρ (b : GA D (Vc D i)) w⟫_ℂ :=
    fun b => h1 w b b.2
  have e : ∀ b : GinfC (Vc D i),
      GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w))
                   (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) w)) b *
        GlobalTheory.Core.Rk.IP.rcoef m (fun g => innerₛₗ ℂ w (R.extV i t y g)) (fun g => innerₛₗ ℂ w (R.extV i t y g)) b =
      (z1 * z2) * ((‖⟪w, (R.cV i).ρ (b : GA D (Vc D i)) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun b => by
    calc _ = (z1 * ⟪w, (R.cV i).ρ (b : GA D (Vc D i)) w⟫_ℂ) * (z2 * ⟪(R.cV i).ρ (b : GA D (Vc D i)) w, w⟫_ℂ) :=
          congrArg₂ (· * ·) (e1 b) (h2 w b b.2)
      _ = _ := by
        rw [← inner_conj_symm ((R.cV i).ρ (b : GA D (Vc D i)) w) w, Complex.ofReal_pow, ← Complex.mul_conj']
        ring
  rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul, integral_complex_ofReal]
  exact mul_ne_zero (mul_ne_zero (h1ne w hJ) (h2ne hy)) (Complex.ofReal_ne_zero.2
    (GlobalTheory.T.integral_normSq_matrix_coefficient_ne_zero_definite D (Vc D i) (D.sp.V_sig _) (hG.core.models.vpos i) (R.cV i) (hG.core.models.cV i) w hw mR hmR))

end GlobalTheory.Core.Rk.RealOcc

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntegralThetaLiftDefiniteFormNeZeroStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

theorem _root_.GlobalTheory.T.realIntegral_thetaLift_definiteForm_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t (y : (R.HV i t).H), y ≠ 0 → ∀ m : Measure (GA D (Vc D i)), m.IsHaarMeasure → ∃ (l : (R.cV i).W →ₗ[ℂ] ℂ) (P : PolF D (Wc D i).rank (Vc D i).rank), ∀ ν 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) ν 𝓕 → ∀ mR : Measure (GinfC (Vc D i)), mR.IsHaarMeasure → ∫ b : GinfC (Vc D i), GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t P) (R.ptP i t P) b * GlobalTheory.Core.Rk.IP.rcoef m (fun g => l (R.extV i t y g)) (fun g => l (R.extV i t y g)) b ∂mR ≠ 0 := by
  first | exact @GlobalTheory.Core.Rk.RealOcc.real_ne | exact GlobalTheory.Core.Rk.RealOcc.real_ne | (intros; apply GlobalTheory.Core.Rk.RealOcc.real_ne <;> assumption)
end
end
