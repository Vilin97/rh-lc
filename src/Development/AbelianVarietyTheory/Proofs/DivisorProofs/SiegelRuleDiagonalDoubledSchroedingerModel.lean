module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaIntegralEqNonzeroMulDiagonalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaIntegralSiegelRuleDoubledWeil

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantAdmissibleFormEqMulDiagonalIn

section

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.DiagUniq

open MeasureTheory GlobalTheory.DiagForm

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply v.1)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply v.1)

theorem glue_shiftOf (x : κ → AF F) : glue (shiftOf x) = x := by
  have h := glue_add_shiftOf (0 : Vi F κ × Vf F κ) x
  rwa [zero_add, GlobalTheory.DiagNonvan.glue_zero, zero_add] at h

theorem shiftOf_glue (p : Vi F κ × Vf F κ) : shiftOf (glue p) = p := by
  refine Prod.ext ?_ rfl
  refine (eI F κ).injective ?_
  show eI F κ ((eI F κ).symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  funext i
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem continuous_shiftOf : Continuous (shiftOf : (κ → AF F) → Vi F κ × Vf F κ) :=
  ((eI F κ).symm.continuous.comp (continuous_pi fun i =>
    continuous_toMixed.comp (continuous_fst.comp (continuous_apply i)))).prodMk
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))


variable (F κ) in
def glueE : (Vi F κ × Vf F κ) ≃ₜ+ (κ → AF F) where
  toFun := glue
  invFun := shiftOf
  left_inv := shiftOf_glue
  right_inv := glue_shiftOf
  map_add' := GlobalTheory.DiagNonvan.glue_add
  continuous_toFun := GlobalTheory.DiagNonvan.continuous_glue
  continuous_invFun := continuous_shiftOf

theorem lDiag_eq (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ c : ℂ, ∀ Φ ∈ schA F (κ ⊕ κ), lDiag F κ Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : ((mu F κ).map (glueE F κ)).IsAddHaarMeasure := (glueE F κ).isAddHaarMeasure_map _
  have h := Measure.isAddLeftInvariant_eq_smul ((mu F κ).map (glueE F κ)) μ
  refine ⟨((Measure.addHaarScalarFactor ((mu F κ).map (glueE F κ)) μ : ℝ) : ℂ), fun Φ hΦ => ?_⟩
  have e := (glueE F κ).toHomeomorph.measurableEmbedding.integral_map (μ := mu F κ) (fun u => Φ (Sum.elim u u))
  rw [lDiag, LinearMap.comp_apply, Lext_apply _ (integrable_resD hΦ)]
  refine e.symm.trans ?_
  change ∫ u, Φ (Sum.elim u u) ∂((mu F κ).map (glueE F κ)) = _
  conv_lhs => rw [h]
  rw [integral_smul_nnreal_measure]
  rfl


variable (F κ) in
def diagL : ((κ → F) × (κ → F)) →ₗ[F] ((κ ⊕ κ → F) × (κ ⊕ κ → F)) where
  toFun p := (Sum.elim p.1 p.1, Sum.elim p.2 (-p.2))
  map_add' p q := by
    refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp [add_comm]
  map_smul' c p := by
    refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp

omit [NumberField F] [Fintype κ] in
theorem diagL_injective : Function.Injective (diagL F κ) := by
  intro p q h
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact congrFun (congrArg Prod.fst h) (Sum.inl i)
  · exact congrFun (congrArg Prod.snd h) (Sum.inl i)

theorem eq_mul_diagInt : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] (l : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ), l ∈ (adeleClass F).adm (κ ⊕ κ) →
      (∀ x y : κ → AF F, ∀ Φ ∈ schA F (κ ⊕ κ), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) →
      ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∃ c : ℂ, ∀ Φ ∈ schA F (κ ⊕ κ), l Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  intro F _ _ ψ hψ κ _ l hl hinv μ hμ
  have key : ∀ l' : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ,
      (∀ x y : κ → AF F, ∀ Φ ∈ schA F (κ ⊕ κ), l' (schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l' Φ) →
      ∀ (t : AF F), ∀ w ∈ LinearMap.range (diagL F κ), ∀ φ ∈ schA F (κ ⊕ κ),
        l' (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l' φ := by
    rintro l' h t _ ⟨p, rfl⟩ φ hφ
    have e : t • ((fun i => algebraMap F (AF F) ((diagL F κ p).1 i)), (fun i => algebraMap F (AF F) ((diagL F κ p).2 i))) =
        (Sum.elim (fun i => t * algebraMap F (AF F) (p.1 i)) (fun i => t * algebraMap F (AF F) (p.1 i)),
          Sum.elim (fun i => t * algebraMap F (AF F) (p.2 i)) (-fun i => t * algebraMap F (AF F) (p.2 i))) := by
      refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp [diagL]
    rw [e]
    exact h _ _ φ hφ
  obtain ⟨c, hc⟩ := GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F ψ hψ (κ ⊕ κ) (LinearMap.range (diagL F κ))
    (by
      rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
      simp [diagL, dotProduct, Fintype.sum_sum_type])
    (by
      rw [LinearMap.finrank_range_of_inj diagL_injective]
      simp)
    l hl (lDiag F κ) lDiag_adm (key l hinv) (key _ fun x y Φ hΦ => lDiag_schr ψ x y hΦ) exists_lDiag_ne
  obtain ⟨d, hd⟩ := lDiag_eq μ hμ
  exact ⟨c * d, fun Φ hΦ => by rw [hc Φ hΦ, hd Φ hΦ, mul_assoc]⟩

end GlobalTheory.DiagUniq

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantAdmissibleFormEqMulDiagonalInStatement

section

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF


theorem _root_.GlobalTheory.T.heisenbergInvariant_admissibleForm_eq_mul_diagonalIntegral : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] (l : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ), l ∈ (adeleClass F).adm (κ ⊕ κ) →
      (∀ x y : κ → AF F, ∀ Φ ∈ schA F (κ ⊕ κ), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) →
      ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∃ c : ℂ, ∀ Φ ∈ schA F (κ ⊕ κ), l Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  first | exact @GlobalTheory.DiagUniq.eq_mul_diagInt | exact GlobalTheory.DiagUniq.eq_mul_diagInt | (intros; apply GlobalTheory.DiagUniq.eq_mul_diagInt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalHeisenbergInvariantFormEqSmulDiagonalInt

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HostDiagUniq

theorem eq_smul_diagInt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ] (l : ((κ ⊕ κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ),
      l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm (κ ⊕ κ) →
      (∀ x y : κ → AF D.host.F, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
        l (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) →
      ∀ μ : @MeasureTheory.Measure (κ → AF D.host.F) (borel _),
        @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ), l Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  intro D ψ hψ κ _ l hl hinv μ hμ
  exact GlobalTheory.T.heisenbergInvariant_admissibleForm_eq_mul_diagonalIntegral D.host.F ψ (GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ) κ l hl hinv μ hμ

end GlobalTheory.HostDiagUniq
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalHeisenbergInvariantFormEqSmulDiagonalIntStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.diagonalHeisenbergInvariant_form_eq_smul_diagonalIntegral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (κ : Type) [Fintype κ] (l : ((κ ⊕ κ → AF D.host.F) → ℂ) →ₗ[ℂ] ℂ),
      l ∈ (GlobalTheory.WeilM.adeleClass D.host.F).adm (κ ⊕ κ) →
      (∀ x y : κ → AF D.host.F, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
        l (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) →
      ∀ μ : @MeasureTheory.Measure (κ → AF D.host.F) (borel _),
        @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∃ c : ℂ, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ), l Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  first | exact @GlobalTheory.HostDiagUniq.eq_smul_diagInt | exact GlobalTheory.HostDiagUniq.eq_smul_diagInt | (intros; apply GlobalTheory.HostDiagUniq.eq_smul_diagInt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaIntegralSiegelRuleDoubledWeilStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.diagonalThetaIntegral_siegelRule_doubledWeil : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
            Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
          ∀ (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
            ResEta D χS S.rank → ResEta D χT T.rank →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          ∀ (p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)))
            (t : GL (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)),
            p.1.1 * GlobalTheory.WeilM.diagCols (Fin S.rank) = GlobalTheory.WeilM.diagCols (Fin S.rank) * t.1 →
          ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
            GlobalTheory.DblSchr.omdOf omd₀ p Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ) ∧
            GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ
                         (GlobalTheory.DblSchr.omdOf omd₀ p Φ)) =
              GlobalTheory.DiagSiegel.ruleFac (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) χT (Fintype.card (Fin T.rank)) t *
                GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) := by
  first | exact @GlobalTheory.DiagThetaRule.thetaDiagInt_omdOf | exact GlobalTheory.DiagThetaRule.thetaDiagInt_omdOf | (intros; apply GlobalTheory.DiagThetaRule.thetaDiagInt_omdOf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelRuleDiagonalDoubledSchroedingerModel

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagSiegel

open MeasureTheory

theorem dblD_diagCols {R E : Type} [CommRing R] [CommRing E] [Algebra R E] [Invertible (2 : R)] (c : E →ₐ[R] E)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {ξ : E} {JA : Matrix α α E}
    {JB : Matrix β β E} {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c ξ JA JB) κ)
    (z : Matrix α β E) :
    (GlobalTheory.DblSchr.dblD c d).e (z * (GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β E)ᵀ) =
      (Sum.elim (d.e z).1 (d.e z).1, Sum.elim (d.e z).2 (-(d.e z).2)) := by
  have h : z * (GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β E)ᵀ = Matrix.fromCols z z := by
    simp [GlobalTheory.WeilM.diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols]
  rw [h]
  exact GlobalTheory.DblSchr.isDblCoord_dblD c d z z

end GlobalTheory.DiagSiegel

theorem GlobalTheory.DiagSiegel.siegelRule_ddr : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          GlobalTheory.WeilM.SiegelRule (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ (incM D.host.F JA)
            (GlobalTheory.WeilM.dbl (incM D.host.F JB)) (GlobalTheory.DblSchr.dblD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) co) χT
            (GlobalTheory.WeilM.diagCols (Fin S.rank)) (GlobalTheory.DblSchr.omdOf omd₀) := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hξ κ _ co hco ωd hωd omd₀ htr
  intro l hl hinv p t hpt φ hφ
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Size.exists_isCovolOne (D := D) S T
  letI mκ : MeasurableSpace (κ → AF D.host.F) := borel _
  haveI : BorelSpace (κ → AF D.host.F) := ⟨rfl⟩
  let μ : MeasureTheory.Measure (κ → AF D.host.F) := MeasureTheory.Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  have hinv' : ∀ x y : κ → AF D.host.F, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
      l (GlobalTheory.WeilM.schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ := by
    intro x y Φ hΦ
    have h1 := hinv (co.e.symm (x, y)) Φ hΦ
    rw [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.DiagSiegel.dblD_diagCols, LinearEquiv.apply_symm_apply] at h1
    exact h1
  obtain ⟨c, hc⟩ := GlobalTheory.T.diagonalHeisenbergInvariant_form_eq_smul_diagonalIntegral D ψ hψ κ l hl hinv' μ hμ
  obtain ⟨c₂, hc₂0, hc₂⟩ := GlobalTheory.T.diagonalThetaIntegral_eq_nonzero_mul_diagonal D ψ hψ S T JA JB ξ hJA hξ κ co hco ν 𝓕 hν μ hμ
  obtain ⟨hmem, hrule⟩ := GlobalTheory.T.diagonalThetaIntegral_siegelRule_doubledWeil D ψ hψ S T JA JB ξ hJA hξ κ co hco ν 𝓕 hν χS χT hS hT rS rT ωd hωd omd₀ htr p t hpt φ hφ
  rw [hc₂ _ hmem, hc₂ _ hφ] at hrule
  have e := mul_left_cancel₀ hc₂0 (hrule.trans (mul_left_comm _ _ _))
  show l (GlobalTheory.DblSchr.omdOf omd₀ p φ) = _
  refine (hc _ hmem).trans ?_
  refine (congrArg (c * ·) e).trans ?_
  refine (mul_left_comm _ _ _).trans ?_
  have h3 := hc _ hφ
  rw [h3]
  rfl

end
end
end
