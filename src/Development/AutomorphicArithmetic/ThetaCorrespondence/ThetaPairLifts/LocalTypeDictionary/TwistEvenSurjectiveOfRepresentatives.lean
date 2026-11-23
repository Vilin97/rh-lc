module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalOperatorEigenvaluesDeterminedByParamsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParametersBoundedEigenfunctionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityValuesContinuousBoundedHeckeConjStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainLiftSurjectiveOfAdjointNonzero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainFiniteDimensionalAndPeterssonProduStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainSpannedParamsOfValueIndependentStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterTransferAllFinitePlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralConjCuspFormParameterTransferStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainStepFockVectorsSphericalLatticeVacStatement
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointExistsUniqueOfPosDef
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemRangeAdjointOfMemSpanEvaluationValues
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepRealZetaNonvanishingStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepSemilocalZetaNeZeroOfRealStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUpwardCuspSpanAndAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpwardThetaLiftNeZeroOfLValueNeZeroStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HeckeFormOfDoubling

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankChainParamsTrivialBoundRapidDecay

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.EvenOnto.parBound_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ParBound D := by
  intro hCRD D c hc j hj s hs u B hB
  obtain ⟨hu0, hpar⟩ := hB
  have hex : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu0
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact h v
  obtain ⟨v, hv⟩ := hex
  set f : GA D s.V → ℂ := fun g => conj (PiLocalization₂.val u v g) with hfdef
  have h3 : GlobalTheory.LFun.IsParamFunV s.V c.S f B := hpar v hv
  obtain ⟨h4a, _⟩ := GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj hCRD D c hc j hj s hs
  obtain ⟨hcont, ⟨C, hC⟩, hinv, hlev, _⟩ := h4a u v
  have hsph : SphOff (s.J : Set (GA D s.V)) 1 c.S := hs.sph
  have hfmem : f ∈ GlobalTheory.FinZeta.bddAut s.V := by
    refine ⟨(Complex.continuous_conj).comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [hfdef, hinv γ hγ g]
    · simpa [hfdef] using hC g
  have hf0 : f ≠ 0 := by
    intro h0
    apply hv
    funext g
    have := congrFun h0 g
    simpa [hfdef] using this
  have hlev' : ∀ k ∈ (s.J : Set (GA D s.V)), ∀ g, f (g * k) = (1 : GA D s.V → ℂ) k * f g := by
    intro k hk g
    simp only [hfdef, hlev k hk g, Pi.one_apply, one_mul]
  obtain ⟨a, ha⟩ := GlobalTheory.T.sphericalOperator_eigenvalues_determined_by_params D s.V (s.J : Set (GA D s.V)) 1 c.S hsph B
  obtain ⟨B', hB', hbd⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D s.V _ _ c.S hsph f hfmem hf0 hlev' a (fun P d R hR => ha f h3 P d R hR)
  intro w hw
  rw [GlobalTheory.LFun.IsParamVecOff.unique h3 hB' hw]
  exact hbd w hw
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankChainParamsTrivialBoundRapidDecayStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.evenRankChain_params_trivialBound_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ParBound D := by
  first | exact @GlobalTheory.EvenOnto.parBound_of_rapidDecay | exact GlobalTheory.EvenOnto.parBound_of_rapidDecay | (intros; apply GlobalTheory.EvenOnto.parBound_of_rapidDecay <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainLiftSurjectiveOfAdjointNonzeroStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.evenRankThetaChainLift_surjective_of_adjoint_nonzero : ∀ D : D7, FinDim D → MetEx D → EigSpan D → ParIndep D → ParBound D → StepUp D → OntoAll D := by
  first | exact @GlobalTheory.EvenOnto.ontoAll_of | exact GlobalTheory.EvenOnto.ontoAll_of | (intros; apply GlobalTheory.EvenOnto.ontoAll_of <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainUpwardLiftHeckeParamTransferred

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto

theorem PiLocalization₂.val_autCusp {D : D7} (c : Com D) (s : PiLocalization₂ D) (u : s.CC c) (x : SmT s.M) :
    IsAutFunSm c.θ s.V (PiLocalization₂.val u x) ∧ IsCuspFun s.V (PiLocalization₂.val u x) := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff D c.θ s.V _ s.M _ _ _).1 ((mem_multT _ _ _ _ _).1 u.2)
  have key : ∀ y : SmT s.M, PiLocalization₂.val u y =
      (PiTensorProduct.lift (PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))) y := by
    intro y; rw [LinearEquiv.apply_symm_apply]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [key, map_smul, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul r (hT.aut f), GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp f)⟩
  | add x y hx hy =>
    have e : PiLocalization₂.val u (x + y) = PiLocalization₂.val u x + PiLocalization₂.val u y := map_add _ _ _
    rw [e]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hx.1 hy.1,
      GlobalTheory.MultMem.isCuspFun_add hx.1.toIsAutFun hy.1.toIsAutFun hx.2 hy.2⟩

theorem upPar_of_transfer : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ D : D7, UpPar D := by
  intro hRD hHowe D c hc k hk s s' hs hs' p hp u B φ hu v _ hne
  set y := PiLocalization₂.val u v with hy
  have hy0 : y ≠ 0 := by
    intro h; apply hne; funext x; simp [Step.up, h]
  have hyB : GlobalTheory.LFun.IsParamFunV s.V c.S (fun g => conj (y g)) B := hu.2 v hy0
  have hconj : (fun x => conj (p.up φ y x)) =
      fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν := by
    funext x; simp only [Step.up]; rw [← integral_conj]; congr 1; funext g; simp [map_mul]
  have hne' : (fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν) ≠ 0 := by
    rw [← hconj]; intro h; apply hne; funext x; simpa using congrFun h x
  have hrank : s'.V.rank = s.V.rank + c.t := by rw [hs'.rank, hs.rank]; ring
  have hYA := PiLocalization₂.val_autCusp c s u v
  have hunr : ∀ w0 ∉ c.S, ∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w0 →
      GlobalTheory.LFun.UnrAt (c.χ k) w' ∧ GlobalTheory.LFun.UnrAt (c.χ k) w' := by
    intro w0 hw0 w' hw'
    have h1 := hc.unr k hk w' (by simpa [GlobalTheory.LFun.above, hw'] using hw0)
    exact ⟨h1, h1⟩
  unfold ParFun
  rw [hconj]
  intro w0 hw0 w h
  have hw0' : w0 ∉ c.S := by simpa using hw0
  exact GlobalTheory.T.thetaIntegral_conjCuspForm_parameterTransfer hRD D (GlobalTheory.T.sphericalParameterTransfer_all_finitePlaces hHowe D) c.ψ c.θ s.V s'.V _ _ p.ω hc.inf hp.pre.weil c.t hrank s.ν s.fd
    hs.haar hs.fund w0 (hunr w0 hw0') w h (p.pt φ)
    ((GlobalTheory.T.evenThetaChainStep_fockVectors_spherical_latticeVacua D c hc k hk s s' hs hs' p hp φ).2.2.2 w0 hw0') y (B w) hYA.1 hYA.2 (hyB w0 hw0 w h) hne'

end GlobalTheory.EvenOnto

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainUpwardLiftHeckeParamTransferredStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.evenThetaChainUpwardLift_heckeParam_transferred : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ D : D7, UpPar D := by
  first | exact @GlobalTheory.EvenOnto.upPar_of_transfer | exact GlobalTheory.EvenOnto.upPar_of_transfer | (intros; apply GlobalTheory.EvenOnto.upPar_of_transfer <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepAdjointNonzeroTransferredParams

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto

theorem pet_val_sum {D : D7} {c : Com D} {s : PiLocalization₂ D} {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (h : IsMet c s ipD ip) (y : s.CC c) (w : SmT s.M) (n : ℕ)
    (ys : Fin n → s.CC c) (ws : Fin n → SmT s.M) :
    s.pet (PiLocalization₂.val y w) (∑ i, PiLocalization₂.val (ys i) (ws i)) = ∑ i, ip y (ys i) * ipD w (ws i) := by
  have hs : ∀ i, s.pet (PiLocalization₂.val y w) (PiLocalization₂.val (ys i) (ws i)) = ip y (ys i) * ipD w (ws i) :=
    fun i => h.schur y (ys i) w (ws i)
  rw [← Finset.sum_congr rfl (fun i _ => hs i)]

  simp only [PiLocalization₂.pet, Lift.pet, Finset.sum_apply, map_sum, Finset.mul_sum]
  exact integral_finsetSum _ (fun i _ => h.integ y (ys i) w (ws i))

theorem stepUp : ∀ D : D7, FinDim D → ParOfVal D → UpSpan D → UpAdj D → UpPar D → UpNe D → StepUp D := by
  intro D hFin hPV hSpan hAdj hPar hNe
  intro c hc k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' u B hB hL
  have hk' : k + 1 ≤ c.m := hk
  haveI : FiniteDimensional ℂ (s'.CC c) := hFin c hc (k + 1) hk' s' hs'
  obtain ⟨x, hx, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique (s.CC c) (s'.CC c) ip ip' hM'.herm hM'.pos p.io u
  obtain ⟨φ, v, hv, hF⟩ := hNe c hc k hk s s' hs hs' p hp u B hB hL
  have key := GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span (GA D s'.V) (SmT s'.M) (s'.CC c) (s'.CC c).subtype s'.KF ipD' ip' s'.pet
    hM'.hermD hM'.posD hM'.herm hM'.pos (fun y w n ys ws => pet_val_sum hM' y w n ys ws) x
    (p.up φ (PiLocalization₂.val u v)) (fun w => ipD (p.It φ w) v) (hSpan c hc k hk s s' hs hs' p hp u φ v hv)
    (fun y w hw => by
      rw [hx y]
      exact (hAdj c hc k hk s s' hs hs' p hp u y φ v hv w hw).trans (hM.schur _ _ _ _)) hF
  obtain ⟨-, w₀, -, hFx⟩ := key
  have hPF := hPar c hc k hk s s' hs hs' p hp u B φ hB v hv hF
  have hFx' : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₀ := hFx
  refine ⟨x, hx, hPV c hc (k + 1) hk' s' hs' x w₀ _ ?_ ?_⟩
  · rw [← hFx']; exact hF
  · rw [← hFx']; exact hPF

end GlobalTheory.EvenOnto
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepAdjointNonzeroTransferredParamsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.even_theta_step_adjoint_nonzero_transferred_params : ∀ D : D7, FinDim D → ParOfVal D → UpSpan D → UpAdj D → UpPar D → UpNe D → StepUp D := by
  first | exact @GlobalTheory.EvenOnto.stepUp | exact GlobalTheory.EvenOnto.stepUp | (intros; apply GlobalTheory.EvenOnto.stepUp <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistEvenSurjectiveOfRepresentatives

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.EvenOnto
theorem even_surjective_of_representatives : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, OntoAll D := by
  intro hHC hCusp hDS hHCM hCW hHowe hWeil hSW hSWc hDoub hUnr D
  have hHecke := _root_.GlobalTheory.Core.Rk.IP.heckeForm_of_doubling' hWeil hCusp hSW hSWc hDoub hUnr D
  obtain ⟨hFin, hMet⟩ := GlobalTheory.T.evenThetaChain_finiteDimensional_and_peterssonProducts hHC hCusp D
  obtain ⟨hEig, hPoV, hInd⟩ := GlobalTheory.T.even_theta_chain_spanned_params_of_value_independent hCusp D hFin hMet
  have hBd := GlobalTheory.T.evenRankChain_params_trivialBound_rapidDecay hCusp D
  obtain ⟨hSpan, hAdj⟩ := GlobalTheory.T.thetaLiftUpward_cuspSpan_and_adjoint hDS hHCM hCusp hCW D
  have hPar := GlobalTheory.T.evenThetaChainUpwardLift_heckeParam_transferred hCusp hHowe D
  have hRZ := GlobalTheory.T.evenThetaStep_realZeta_nonvanishing hDS hHCM D
  have hZN := GlobalTheory.T.evenThetaStep_semilocalZeta_ne_zero_of_real D hMet hRZ
  have hNe := GlobalTheory.T.upwardThetaLift_ne_zero_of_lValue_ne_zero D hHecke hMet hZN
  have hStep := GlobalTheory.T.even_theta_step_adjoint_nonzero_transferred_params D hFin hPoV hSpan hAdj hPar hNe
  exact GlobalTheory.T.evenRankThetaChainLift_surjective_of_adjoint_nonzero D hFin hMet hEig hInd hBd hStep
end GlobalTheory.EvenOnto
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twist_even_surjective_of_representatives : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, OntoAll D := by
  first | exact @_root_.GlobalTheory.EvenOnto.even_surjective_of_representatives | exact _root_.GlobalTheory.EvenOnto.even_surjective_of_representatives | (intros; apply _root_.GlobalTheory.EvenOnto.even_surjective_of_representatives <;> assumption)
end
end
end
