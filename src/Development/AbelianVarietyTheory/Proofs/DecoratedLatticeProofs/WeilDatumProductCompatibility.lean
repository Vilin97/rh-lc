module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleOrthogonalSumSourceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSumStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumPreservesThetaFundamentalDomainPairingStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorCommutesSuperpositionSlicesSourceStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunSuperpositionTargetOrthSummandStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorIntegralCommOfBoundedFiniteMeasureStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPairStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenbergStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariableKeepsThetaFunctionsStatement
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepConjSourceLineEqTargetLineStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorTargetSummandPreservesThetaFunctions

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger (dagger dagger_dagger conjAdjoint)

namespace GlobalTheory.SliceTarget

variable {D : D7} {T A B : HSp D}

theorem pA_giA (o : OrthDec T A B) : o.pA ⬝ giA T = giA A ⬝ adj o.jA := by
  rw [o.pA_eq]
  simp only [Matrix.mul_assoc, gA_mul_giA, Matrix.mul_one]

theorem resT_dagger (o : OrthDec T A B) (S : HSp D) (y : WO T S) :
    o.resT S (dagger T S y) = (dagger A S (o.resS S y).1, dagger B S (o.resS S y).2) := by
  have hA := pA_giA o
  have hB : o.pB ⬝ giA T = giA B ⬝ adj o.jB := pA_giA o.symm
  simp only [OrthDec.resT_apply, OrthDec.resS_apply, dagger, adj_mul, cancel₂ hA, cancel₂ hB, Matrix.mul_assoc]

theorem dagger_resS_symm (o : OrthDec T A B) (S : HSp D) (u : WO A S) (v : WO B S) :
    dagger T S ((o.resS S).symm (u, v)) = (o.resT S).symm (dagger A S u, dagger B S v) := by
  rw [AddEquiv.eq_symm_apply, resT_dagger, AddEquiv.apply_symm_apply]

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (T A B S : HSp D) (o : OrthDec T A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om S A), IsWeilDatumO ψ S A χ χ' om → ∀ p, IsThetaFunO ψ S T fun x => om p (fun u => F ((o.resT S).symm (u, (o.resT S x).2))) (o.resT S x).1 := by
  intro D ψ T A B S o F hF χ χ' om hom p
  have hd := (GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hom.std S T).2.2.1
  have h := (GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ T A B S o _ ((hd F).2 hF)).1 χ' χ (conjAdjoint om)
    (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S A χ χ' om hom) p.swap
  refine (hd _).1 ?_
  convert h using 1
  funext y
  show starRingEnd ℂ (om p (fun u => F ((o.resT S).symm (u, (o.resT S (dagger T S y)).2))) (o.resT S (dagger T S y)).1) =
    starRingEnd ℂ (om p (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S A) fun u => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) F ((o.resS S).symm (u, (o.resS S y).2)))
      (dagger A S (o.resS S y).1))
  have e : (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S A) fun u => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) F ((o.resS S).symm (u, (o.resS S y).2))) =
      fun u => F ((o.resT S).symm (u, dagger B S (o.resS S y).2)) := by
    funext u
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm, dagger_dagger, Complex.conj_conj]
  rw [resT_dagger, e]

end GlobalTheory.SliceTarget
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorTargetSummandPreservesThetaFunctionsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf


theorem _root_.GlobalTheory.T.weil_operator_target_summand_preserves_theta_functions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (T A B S : HSp D) (o : OrthDec T A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om S A), IsWeilDatumO ψ S A χ χ' om → ∀ p, IsThetaFunO ψ S T fun x => om p (fun u => F ((o.resT S).symm (u, (o.resT S x).2))) (o.resT S x).1 := by
  first | exact @GlobalTheory.SliceTarget.main | exact GlobalTheory.SliceTarget.main | (intros; apply GlobalTheory.SliceTarget.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepCommutesSliceSuperpositionTarget

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.SliceSumTarget

theorem decomp_re_im (z : ℂ) : ((max z.re 0 : ℝ) : ℂ) + -1 * ((max (-z.re) 0 : ℝ) : ℂ) + Complex.I * ((max z.im 0 : ℝ) : ℂ) +
    -Complex.I * ((max (-z.im) 0 : ℝ) : ℂ) = z := by
  have h1 := max_zero_sub_max_neg_zero_eq_self z.re
  have h2 := max_zero_sub_max_neg_zero_eq_self z.im
  apply Complex.ext
  · simp
    linarith
  · simp
    linarith

theorem isThetaFunO_sliceT {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {T A B S : HSp D}
    (o : OrthDec T A B) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F) (y : WO S B) :
    IsThetaFunO ψ S A fun u => F ((o.resT S).symm (u, y)) := by
  have h := GlobalTheory.T.isThetaFun_superposition_target_orthSummand D ψ hψ T A B S o F hF Unit (Measure.dirac ()) (fun _ => y) (fun _ => 1) measurable_const
    (integrable_const _)
  simpa only [integral_dirac, one_mul] using h

theorem weil_comm_sliceSum_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (T A B S : HSp D) (o : OrthDec T A B) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S A), IsWeilDatumO ψ S A χ χ' om → ∀ (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO S B) (a : Ω → ℂ), Measurable k → Integrable a μ → ∀ p, IsThetaFunO ψ S T (fun x => om p (fun u => F ((o.resT S).symm (u, (o.resT S x).2))) (o.resT S x).1) ∧ ∀ u₀, om p (fun u => ∫ w, a w * F ((o.resT S).symm (u, k w)) ∂μ) u₀ = ∫ w, a w * om p (fun u => F ((o.resT S).symm (u, k w))) u₀ ∂μ := by
  intro D ψ T A B S o χ χ' om hW F hF Ω _ μ k a hk ha p
  have hψ := hW.std
  have h1 := GlobalTheory.T.weil_operator_target_summand_preserves_theta_functions D ψ T A B S o F hF χ χ' om hW p
  refine ⟨h1, fun u₀ => ?_⟩
  obtain ⟨-, -, iB3, -⟩ := lattice_Mx D B.rank S.rank
  haveI : BorelSpace (WO S B) := ⟨rfl⟩

  set Fs : WO S B → WO S A → ℂ := fun y u => F ((o.resT S).symm (u, y)) with hFs
  set G : WO S T → ℂ := fun x => om p (fun u => F ((o.resT S).symm (u, (o.resT S x).2))) (o.resT S x).1 with hG
  have hGs : ∀ y u, om p (Fs y) u = G ((o.resT S).symm (u, y)) := by
    intro y u; simp only [hG, hFs, AddEquiv.apply_symm_apply]
  have cFs : Continuous fun q : WO S B × WO S A => Fs q.1 q.2 :=
    hF.cont.comp ((o.continuous_resT_symm S).comp (continuous_snd.prodMk continuous_fst))
  have cGs : Continuous fun q : WO S B × WO S A => om p (Fs q.1) q.2 := by
    simp only [hGs]
    exact h1.cont.comp ((o.continuous_resT_symm S).comp (continuous_snd.prodMk continuous_fst))
  obtain ⟨CF, hCF⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ F hF
  obtain ⟨CG, hCG⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ G h1
  have bFs : ∀ y u, ‖Fs y u‖ ≤ CF := fun y u => hCF _
  have bGs : ∀ y u, ‖om p (Fs y) u‖ ≤ CG := fun y u => by rw [hGs]; exact hCG _

  have mF : ∀ u, AEStronglyMeasurable (fun w => Fs (k w) u) μ := fun u =>
    ((cFs.comp (continuous_id.prodMk continuous_const)).measurable.comp hk).aestronglyMeasurable
  have mG : AEStronglyMeasurable (fun w => om p (Fs (k w)) u₀) μ :=
    ((cGs.comp (continuous_id.prodMk continuous_const)).measurable.comp hk).aestronglyMeasurable

  let P : (Ω → ℂ) → Prop := fun c => Integrable c μ ∧
    om p (fun u => ∫ w, c w * Fs (k w) u ∂μ) u₀ = ∫ w, c w * om p (Fs (k w)) u₀ ∂μ
  have intF : ∀ c, Integrable c μ → ∀ u, Integrable (fun w => c w * Fs (k w) u) μ := fun c hc u => by
    have := hc.bdd_mul (mF u) (c := CF) (Filter.Eventually.of_forall fun w => bFs _ _)
    simpa only [mul_comm] using this
  have intG : ∀ c, Integrable c μ → Integrable (fun w => c w * om p (Fs (k w)) u₀) μ := fun c hc => by
    have := hc.bdd_mul mG (c := CG) (Filter.Eventually.of_forall fun w => bGs _ _)
    simpa only [mul_comm] using this
  have Padd : ∀ c₁ c₂, P c₁ → P c₂ → P (c₁ + c₂) := by
    intro c₁ c₂ h₁ h₂
    refine ⟨h₁.1.add h₂.1, ?_⟩
    have e1 : (fun u => ∫ w, (c₁ + c₂) w * Fs (k w) u ∂μ) =
        (fun u => ∫ w, c₁ w * Fs (k w) u ∂μ) + (fun u => ∫ w, c₂ w * Fs (k w) u ∂μ) := by
      funext u
      simp only [Pi.add_apply, add_mul]
      exact integral_add (intF _ h₁.1 u) (intF _ h₂.1 u)
    rw [e1, map_add (f := _), Pi.add_apply, h₁.2, h₂.2]
    simp only [Pi.add_apply, add_mul]
    exact (integral_add (intG _ h₁.1) (intG _ h₂.1)).symm
  have Psmul : ∀ (z : ℂ) c, P c → P (fun w => z * c w) := by
    intro z c h
    refine ⟨h.1.const_mul z, ?_⟩
    have e1 : (fun u => ∫ w, (z * c w) * Fs (k w) u ∂μ) = z • (fun u => ∫ w, c w * Fs (k w) u ∂μ) := by
      funext u
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul z _
    rw [e1, map_smul, Pi.smul_apply, smul_eq_mul, h.2]
    simp only [mul_assoc]
    exact (integral_const_mul z _).symm

  have Ppos : ∀ b : Ω → ℝ, Measurable b → (∀ w, 0 ≤ b w) → Integrable b μ → P (fun w => (b w : ℂ)) := by
    intro b hbm hb0 hbi
    refine ⟨hbi.ofReal, ?_⟩
    let ν : Measure (WO S B) := (μ.withDensity fun w => ((Real.toNNReal (b w) : NNReal) : ENNReal)).map k
    haveI : IsFiniteMeasure (μ.withDensity fun w => ((Real.toNNReal (b w) : NNReal) : ENNReal)) :=
      isFiniteMeasure_withDensity_ofReal hbi.2
    have tr : ∀ φ : WO S B → ℂ, Continuous φ → ∫ y, φ y ∂ν = ∫ w, (b w : ℂ) * φ (k w) ∂μ := by
      intro φ hφ
      rw [integral_map hk.aemeasurable hφ.aestronglyMeasurable,
        integral_withDensity_eq_integral_smul (hbm.real_toNNReal) _]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only [NNReal.smul_def, Real.coe_toNNReal _ (hb0 w), Complex.real_smul]
    have hth : IsThetaFunO ψ S A fun u => ∫ y, Fs y u ∂ν := by
      have e : (fun u => ∫ y, Fs y u ∂ν) = fun u => ∫ w, (b w : ℂ) * F ((o.resT S).symm (u, k w)) ∂μ := by
        funext u
        exact tr (fun y => Fs y u) (cFs.comp (continuous_id.prodMk continuous_const))
      rw [e]
      exact GlobalTheory.T.isThetaFun_superposition_target_orthSummand D ψ hψ T A B S o F hF Ω μ k _ hk hbi.ofReal
    have hc := GlobalTheory.T.weilOperator_integral_comm_of_bounded_finiteMeasure D ψ S A χ χ' om hW (WO S B) ν Fs p (isThetaFunO_sliceT hψ o hF) cFs ⟨CF, bFs⟩ cGs
      ⟨CG, bGs⟩ hth u₀
    have e : (fun u => ∫ y, Fs y u ∂ν) = fun u => ∫ w, (b w : ℂ) * Fs (k w) u ∂μ := by
      funext u
      exact tr (fun y => Fs y u) (cFs.comp (continuous_id.prodMk continuous_const))
    rw [e] at hc
    rw [hc]
    exact tr (fun y => om p (Fs y) u₀) (cGs.comp (continuous_id.prodMk continuous_const))

  set a' := ha.1.mk a with ha'
  have hae : a =ᵐ[μ] a' := ha.1.ae_eq_mk
  have ha'm : Measurable a' := ha.1.stronglyMeasurable_mk.measurable
  have ha'i : Integrable a' μ := ha.congr hae
  have hre := ha'i.re
  have him := ha'i.im
  have mre : Measurable fun w => (a' w).re := Complex.measurable_re.comp ha'm
  have mim : Measurable fun w => (a' w).im := Complex.measurable_im.comp ha'm
  have P1 := Ppos _ (mre.max measurable_const) (fun w => le_max_right _ _) hre.pos_part
  have P2 := Psmul (-1) _ (Ppos _ (mre.neg.max measurable_const) (fun w => le_max_right _ _) hre.neg_part)
  have P3 := Psmul Complex.I _ (Ppos _ (mim.max measurable_const) (fun w => le_max_right _ _) him.pos_part)
  have P4 := Psmul (-Complex.I) _ (Ppos _ (mim.neg.max measurable_const) (fun w => le_max_right _ _) him.neg_part)
  have Pa' := Padd _ _ (Padd _ _ (Padd _ _ P1 P2) P3) P4
  have Pa'' : P a' := by
    have heq : (fun w => (((max (a' w).re 0 : ℝ) : ℂ) +
        -1 * ((max (-(a' w).re) 0 : ℝ) : ℂ) +
        Complex.I * ((max (a' w).im 0 : ℝ) : ℂ)) +
        -Complex.I * ((max (-(a' w).im) 0 : ℝ) : ℂ)) = a' := by
      funext w
      exact decomp_re_im (a' w)
    change P (fun w => (((max (a' w).re 0 : ℝ) : ℂ) +
        -1 * ((max (-(a' w).re) 0 : ℝ) : ℂ) +
        Complex.I * ((max (a' w).im 0 : ℝ) : ℂ)) +
        -Complex.I * ((max (-(a' w).im) 0 : ℝ) : ℂ)) at Pa'
    rwa [heq] at Pa'
  have e1 : (fun u => ∫ w, a w * Fs (k w) u ∂μ) = fun u => ∫ w, a' w * Fs (k w) u ∂μ := by
    funext u; exact integral_congr_ae (hae.mono fun w hw => by simp only [hw])
  have e2 : ∫ w, a w * om p (Fs (k w)) u₀ ∂μ = ∫ w, a' w * om p (Fs (k w)) u₀ ∂μ :=
    integral_congr_ae (hae.mono fun w hw => by simp only [hw])
  have := Pa''.2
  simp only [hFs] at this e1 e2 ⊢
  rw [e1, e2]
  exact this

end GlobalTheory.SliceSumTarget
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepCommutesSliceSuperpositionTargetStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.weilRep_commutes_slice_superposition_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (T A B S : HSp D) (o : OrthDec T A B) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S A), IsWeilDatumO ψ S A χ χ' om → ∀ (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO S B) (a : Ω → ℂ), Measurable k → Integrable a μ → ∀ p, IsThetaFunO ψ S T (fun x => om p (fun u => F ((o.resT S).symm (u, (o.resT S x).2))) (o.resT S x).1) ∧ ∀ u₀, om p (fun u => ∫ w, a w * F ((o.resT S).symm (u, k w)) ∂μ) u₀ = ∫ w, a w * om p (fun u => F ((o.resT S).symm (u, k w))) u₀ ∂μ := by
  first | exact @GlobalTheory.SliceSumTarget.weil_comm_sliceSum_target | exact GlobalTheory.SliceSumTarget.weil_comm_sliceSum_target | (intros; apply GlobalTheory.SliceSumTarget.weil_comm_sliceSum_target <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumProductCompatibility

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.ContrKernel

variable {D : D7}

theorem continuous_ofAdj (S T : HSp D) : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj S T) := by
  have h : Continuous fun z : Mx D S.rank T.rank => giA T ⬝ (adj z ⬝ gA S) :=
    continuous_const.matrix_mul
      ((GlobalTheory.MixModel.continuous_adj (D := D) (m := S.rank) (n := T.rank)).matrix_mul continuous_const)
  exact h.const_smul (incA D (-D.host.xi0⁻¹))

theorem continuous_kappa {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ')
    (S : HSp D) : Continuous (l.κ S) :=
  (continuous_ofAdj B.L S).comp (continuous_const.matrix_mul continuous_id)

theorem integrable_of_cont_bdd {m n : ℕ} (μ : Measure (Mx D m n)) [IsFiniteMeasure μ] (f : Mx D m n → ℂ)
    (hc : Continuous f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) : Integrable f μ := by
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem symm_resS_symm {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (u : WO B T) (v : WO A T) :
    (o.symm.resS T).symm (u, v) = (o.resS T).symm (v, u) := by
  rw [OrthDec.resS_symm_apply, OrthDec.resS_symm_apply, add_comm]; rfl

theorem symm_resT_symm {T A B : HSp D} (o : OrthDec T A B) (S : HSp D) (u : WO S B) (v : WO S A) :
    (o.symm.resT S).symm (u, v) = (o.resT S).symm (v, u) := by
  rw [OrthDec.resT_symm_apply, OrthDec.resT_symm_apply, add_comm]; rfl

theorem kernel_doubleStep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (χA χA' χz : ((AE D)ˣ →* Circle)) (oma : Om B.A J.W₀) (omz : Om B.L J.W₀) (omb : Om J.W₀ B'.A) (omz' : Om J.W₀ B'.L), s₁.χV = χA * χz → s₂.χW = χA' * χz → IsWeilDatumO ψ B.A J.W₀ χA s₁.χW oma → IsWeilDatumO ψ B.L J.W₀ χz s₁.χW omz → IsWeilDatumO ψ J.W₀ B'.A s₂.χV χA' omb → IsWeilDatumO ψ J.W₀ B'.L s₂.χV χz omz' → ∀ (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ₁ → IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂ → ∀ h₀ h₁ h₂, ∫ w in vL.𝓕, s₂.om₀ (h₁, B'.o.emb (h₂, 1)) Ξ₂ ((B'.o.resT J.W₀).symm (0, w)) * s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) ∂vL.μ = omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) 0 := by
  intro D ψ σ B J B' s₁ s₂ l vL χA χA' χz oma omz omb omz' hV hW hoa hoz hob hoz' Ξ₁ Ξ₂ hΞ₁ hΞ₂ h₀ h₁ h₂
  have hstd : IsStdChar D ψ (-1) := hoa.std
  have TS := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ hstd B.V₀ B.A B.L B.o J.W₀
  have TT := GlobalTheory.T.thetaTensorRule_targetOrthogonalSum D ψ hstd B'.V₀ B'.A B'.L B'.o J.W₀
  have hw₁ : IsWeilDatumO ψ B.V₀ J.W₀ (χA * χz) s₁.χW s₁.om₀ := hV ▸ s₁.weil₀
  have hw₂ : IsWeilDatumO ψ J.W₀ B'.V₀ s₂.χV (χA' * χz) s₂.om₀ := hW ▸ s₂.weil₀
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩
  haveI : BorelSpace (WO J.W₀ B'.L) := ⟨rfl⟩
  haveI : BorelSpace (WO B.L J.W₀) := ⟨rfl⟩

  have hS₁ : ∀ u, IsThetaFunO ψ B.L J.W₀ fun z => Ξ₁ ((B.o.resS J.W₀).symm (u, z)) := (TS.slice_theta Ξ₁ hΞ₁).2
  have hS₂ : ∀ v, IsThetaFunO ψ J.W₀ B'.L fun w => Ξ₂ ((B'.o.resT J.W₀).symm (v, w)) := (TT.slice_theta Ξ₂ hΞ₂).2

  obtain ⟨Hf, hHf⟩ : ∃ Hf : WO B.A J.W₀ → WO B.L J.W₀ → ℂ,
      Hf = fun u z => omz (1, h₁) (fun z' => Ξ₁ ((B.o.resS J.W₀).symm (u, z'))) z := ⟨_, rfl⟩
  obtain ⟨Gf, hGf⟩ : ∃ Gf : WO J.W₀ B'.A → WO J.W₀ B'.L → ℂ,
      Gf = fun v w => omz' (h₁, 1) (fun w' => Ξ₂ ((B'.o.resT J.W₀).symm (v, w'))) w := ⟨_, rfl⟩
  obtain ⟨F₁, hF₁d⟩ : ∃ F₁ : WO B.V₀ J.W₀ → ℂ, F₁ = fun x => Hf (B.o.resS J.W₀ x).1 (B.o.resS J.W₀ x).2 := ⟨_, rfl⟩
  obtain ⟨F₂, hF₂d⟩ : ∃ F₂ : WO J.W₀ B'.V₀ → ℂ, F₂ = fun x => Gf (B'.o.resT J.W₀ x).1 (B'.o.resT J.W₀ x).2 :=
    ⟨_, rfl⟩
  have hF₁s : ∀ u z, F₁ ((B.o.resS J.W₀).symm (u, z)) = Hf u z := by
    intro u z; rw [hF₁d]; simp only [AddEquiv.apply_symm_apply]
  have hF₂s : ∀ v w, F₂ ((B'.o.resT J.W₀).symm (v, w)) = Gf v w := by
    intro v w; rw [hF₂d]; simp only [AddEquiv.apply_symm_apply]

  have hF₁ : IsThetaFunO ψ B.V₀ J.W₀ F₁ := by
    have h := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.L B.A J.W₀ B.o.symm χz s₁.χW omz hoz Ξ₁ hΞ₁ Unit 0 (fun _ => 0) (fun _ => 0)
      measurable_const (integrable_zero _ _ _) (1, h₁)).1
    have e : F₁ = fun x => omz (1, h₁) (fun u => Ξ₁ ((B.o.symm.resS J.W₀).symm (u, (B.o.symm.resS J.W₀ x).2)))
        (B.o.symm.resS J.W₀ x).1 := by
      funext x; rw [hF₁d, hHf]; simp only [symm_resS_symm]; rfl
    rw [e]; exact h
  have hF₂ : IsThetaFunO ψ J.W₀ B'.V₀ F₂ := by
    have h := (GlobalTheory.T.weilRep_commutes_slice_superposition_target D ψ B'.V₀ B'.L B'.A J.W₀ B'.o.symm s₂.χV χz omz' hoz' Ξ₂ hΞ₂ Unit 0 (fun _ => 0) (fun _ => 0)
      measurable_const (integrable_zero _ _ _) (h₁, 1)).1
    have e : F₂ = fun x => omz' (h₁, 1) (fun u => Ξ₂ ((B'.o.symm.resT J.W₀).symm (u, (B'.o.symm.resT J.W₀ x).2)))
        (B'.o.symm.resT J.W₀ x).1 := by
      funext x; rw [hF₂d, hGf]; simp only [symm_resT_symm]; rfl
    rw [e]; exact h

  obtain ⟨b₁, hb₁d⟩ : ∃ b₁ : WO J.W₀ B'.L → ℂ, b₁ = fun w => oma (h₀, h₁) (fun u => Hf u (l.κ J.W₀ w)) 0 := ⟨_, rfl⟩
  have hA : ∀ w, s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) = b₁ w := by
    intro w
    rw [(TS.om_slice χA χz s₁.χW s₁.om₀ oma omz hw₁ hoa hoz h₀ 1 h₁ Ξ₁ hΞ₁ (l.κ J.W₀ w)).2 0, hb₁d, hHf]
  have hB : ∀ w, s₂.om₀ (h₁, B'.o.emb (h₂, 1)) Ξ₂ ((B'.o.resT J.W₀).symm (0, w)) = omb (h₁, h₂) (fun v => Gf v w) 0 := by
    intro w
    rw [(TT.om_slice s₂.χV χA' χz s₂.om₀ omb omz' hw₂ hob hoz' h₁ h₂ 1 Ξ₂ hΞ₂ w).2 0, hGf]

  have hb₁int : Integrable b₁ (vL.μ.restrict vL.𝓕) := by
    have th := hw₁.om_pres (B.o.emb (h₀, 1), h₁) Ξ₁ hΞ₁
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded B.V₀ J.W₀ ψ hstd _ th
    have e : b₁ = fun w => s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) :=
      funext fun w => (hA w).symm
    rw [e]
    exact integrable_of_cont_bdd _ _ (th.cont.comp ((B.o.continuous_resS_symm J.W₀).comp
      (continuous_const.prodMk (continuous_kappa l J.W₀)))) ⟨C, fun w => hC _⟩
  have hGint : ∀ v, Integrable (Gf v) (vL.μ.restrict vL.𝓕) := by
    intro v
    have th := hoz'.om_pres (h₁, 1) _ (hS₂ v)
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded J.W₀ B'.L ψ hstd _ th
    have e : Gf v = omz' (h₁, 1) (fun w' => Ξ₂ ((B'.o.resT J.W₀).symm (v, w'))) := by rw [hGf]
    rw [e]
    exact integrable_of_cont_bdd _ _ th.cont ⟨C, hC⟩

  have hLine : ∀ u v, ∫ w, Gf v w * Hf u (l.κ J.W₀ w) ∂(vL.μ.restrict vL.𝓕) = contr l J.W₀ vL Ξ₁ Ξ₂ u v := by
    intro u v
    have hrank : B.L.rank = B'.L.rank := B.line.1.trans B'.line.1.symm
    have hgram := (GlobalTheory.T.besselLineLink_gram_similitude_bijective D (σ + 1) B B'.L B'.ζ B'.line l).1
    have CL := GlobalTheory.T.weilRep_conj_sourceLine_eq_targetLine D ψ B.L B'.L J.W₀ l.τ hrank hgram χz s₁.χW s₂.χV omz omz' hoz hoz'
      (fun z => Ξ₁ ((B.o.resS J.W₀).symm (u, z))) (hS₁ u)
    have CU := GlobalTheory.T.weilDatum_preserves_thetaFundamentalDomainPairing D ψ J.W₀ B'.L s₂.χV χz omz' hoz' vL (h₁, 1) _ _ (hS₂ v) CL.1
    rw [CL.2 h₁] at CU
    simp only [thPair, star_star] at CU
    rw [hGf, hHf]
    exact CU

  have hInner : ∀ v, oma (h₀, h₁) (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0 =
      ∫ w, b₁ w * F₂ ((B'.o.resT J.W₀).symm (v, id w)) ∂(vL.μ.restrict vL.𝓕) := by
    intro v
    have e : (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) =
        fun u => ∫ w, Gf v w * F₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w)) ∂(vL.μ.restrict vL.𝓕) := by
      funext u; rw [← hLine u v]; simp only [hF₁s]
    rw [e, (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.A B.L J.W₀ B.o χA s₁.χW oma hoa F₁ hF₁ (WO J.W₀ B'.L) (vL.μ.restrict vL.𝓕)
      (l.κ J.W₀) (Gf v) (continuous_kappa l J.W₀).measurable (hGint v) (h₀, h₁)).2 0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hF₁s, hF₂s, id, hb₁d]
    exact mul_comm _ _
  have hOuter := (GlobalTheory.T.weilRep_commutes_slice_superposition_target D ψ B'.V₀ B'.A B'.L J.W₀ B'.o s₂.χV χA' omb hob F₂ hF₂ (WO J.W₀ B'.L)
    (vL.μ.restrict vL.𝓕) id b₁ measurable_id hb₁int (h₁, h₂)).2 0
  have e : (fun v => oma (h₀, h₁) (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) =
      fun v => ∫ w, b₁ w * F₂ ((B'.o.resT J.W₀).symm (v, id w)) ∂(vL.μ.restrict vL.𝓕) := funext hInner
  rw [e, hOuter]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [hA, hB, hF₂s, id]
  exact mul_comm _ _

end GlobalTheory.ContrKernel

end
end
end
