module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMultiplicitySpaceLevelOfKFiniteTensorsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwapStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainStepFockVectorsSphericalLatticeVacStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealDiscreteSeriesDataThetaPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntertwinerValuesKFiniteStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaPairAnalyticHypothesesOfDiscreteSeriesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjWeilDatumExchangedPairStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinersUpwardThetaPairStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijectionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOfVanishOnFockStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOnFockStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairThetaLiftFactorsThroughIntertwinerStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaCorrespondenceUpwardPairBothDirectionsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftsCuspidalOfLowerTowerLiftsVanishStatement
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityValuesContinuousBoundedHeckeConjStatement
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftUpMultiplicitySpacesSpanKFiniteVectors

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.EvenOnto.LiftUp

theorem liftUp_stage_span : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (c : Com D) (k : ℕ) (s s' : PiLocalization₂ D) ω f, c.Is → k < c.m → s.Is c k → s'.Is c (k + 1) → PreStep c k s s' ω f → ∃ T : PolF D s'.V.rank s.V.rank → SmT s.M → SmT s'.M, (∀ P v, T P v ∈ s'.KF) ∧ s'.KF ≤ Submodule.span ℂ {w | ∃ P v, w = T P v} ∧ GlobalTheory.PairLift.LiftsM c.θ s.M s'.M s.ν s.fd (fun P h g => conj (thetaKO ω g h (GlobalTheory.Chain.ptOf c.ψ c.θ s.M s'.M f P))) T := by
  intro hDS hHC hCD hCW D c k s s' ω f hc hk hs _hs' hp
  obtain ⟨X, hX, _h1, _h2, h3, h4, h5⟩ := GlobalTheory.T.exists_real_discreteSeries_data_theta_properties hDS hHC
  have hIn : Inputs D X := GlobalTheory.T.thetaPairAnalyticHypotheses_of_discreteSeries hDS hHC hCD hCW D X hX
  have hPL : PairLifts D X :=
    GlobalTheory.T.pairThetaLift_factors_through_intertwiner D X hIn (GlobalTheory.T.thetaLifts_cuspidal_of_lower_tower_lifts_vanish D X hIn (GlobalTheory.T.lowerTowerLiftsVanish_of_vanish_on_fock D X hIn (GlobalTheory.T.lowerTowerLifts_vanish_on_fock D X hIn)))
  have hW := hp.weil
  have hstd : IsStdChar D c.ψ (-1) := hW.std
  have hadj : AdjLaw c.ψ s.V s'.V := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D c.ψ hstd s.V s'.V
  have h0 : adjO s.V s'.V 0 = 0 := by
    have := hadj.add 0 0
    simpa using this
  obtain ⟨ω', hW', hω'⟩ := GlobalTheory.T.exists_conj_weilDatum_exchangedPair D c.ψ s.V s'.V (c.χ k) (c.χ k) ω hW
  obtain ⟨j, -, hj⟩ := GlobalTheory.T.fockVectors_conjAdjointPullback_bijection D c.ψ c.θ hstd hc.inf s.V s'.V (Fr.ofModel s.M) (Fr.ofModel s'.M)
  obtain ⟨hvac', hpt⟩ := hj f (isVacF_of_isVacVec hp.vac)
  have hω'e : IsWeilExp c.ψ s'.V s.V (c.a k) (c.a k) ω' :=
    ⟨c.χ k, c.χ k, hW', fun τ => ⟨hc.exp k hk τ, hc.exp k hk τ⟩⟩
  have hne : dag s.V s'.V f ≠ 0 := by
    intro hz
    apply hp.vac.ne
    funext x
    have hx := congrFun hz (adjO s'.V s.V x)
    simp only [dag, hadj.invol, Pi.zero_apply] at hx
    simpa using hx
  have hf' : IsVacVec c.ψ c.θ s'.M s.M (dag s.V s'.V f) := ⟨hvac'.1, hne, hvac'.2⟩
  obtain ⟨It, hIt⟩ := (GlobalTheory.T.exists_realIntertwiners_upwardThetaPair hDS hHC D c.t s.V s'.V s.par s'.par s.M s'.M (c.a k) (c.a k) c.θ c.ψ hc.inf hp.par).2
  have hItW := hIt ω' (dag s.V s'.V f) hω'e hf'
  have hrule : ∀ τ, RulePar X (s'.par τ) (s.par τ) (c.a k τ) (c.a k τ) :=
    fun τ => ((GlobalTheory.T.realThetaCorrespondence_upwardPair_both_directions hDS hHC D c.t _ _ _ _ (hp.par τ)).2 X h3 h4 h5).2
  have hL := hPL _ _ _ _ hrule s'.V s.V s'.M s.M c.θ c.ψ hc.inf ω' hω'e (dag s.V s'.V f) It hf' hItW s.ν s.fd hs.haar hs.fund
    (dag s.V s'.V f) (isVacF_of_isVacVec hf')
  refine ⟨fun P v => It (j P) v, fun P v =>
    GlobalTheory.T.real_intertwiner_values_kFinite D s'.V s.V _ _ s'.M s.M c.θ c.ψ _ _ ω' (dag s.V s'.V f) It hc.inf hω'e hf' hItW (j P) v, ?_, ?_⟩
  · refine (GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D s'.V s.V _ _ s'.M s.M c.θ c.ψ _ _ ω' (dag s.V s'.V f) It hc.inf hω'e hf'
      hItW).trans (Submodule.span_mono ?_)
    rintro w ⟨P, v, -, rfl⟩
    exact ⟨j.symm P, v, by simp⟩
  · intro F hF
    obtain ⟨F', hF', hF'e⟩ := hL F hF
    refine ⟨F', hF', fun P v h => ?_⟩
    have key : ∀ g, conj (thetaKO ω g h (ptOf c.ψ c.θ s.M s'.M f P)) =
        thetaKO ω' h g (ptOf c.ψ c.θ s'.M s.M (dag s.V s'.V f) (j P)) := by
      intro g
      have e1 : ptOf c.ψ c.θ s'.M s.M (dag s.V s'.V f) (j P) = dag s.V s'.V (ptOf c.ψ c.θ s.M s'.M f P) := hpt P
      simp only [thetaKO]
      rw [e1, hω']
      simp [dag, h0]
    simp only [key]
    exact hF'e (j P) v h

end GlobalTheory.EvenOnto.LiftUp

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftUpMultiplicitySpacesSpanKFiniteVectorsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.liftUp_multiplicitySpaces_span_kFiniteVectors : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (c : Com D) (k : ℕ) (s s' : PiLocalization₂ D) ω f, c.Is → k < c.m → s.Is c k → s'.Is c (k + 1) → PreStep c k s s' ω f → ∃ T : PolF D s'.V.rank s.V.rank → SmT s.M → SmT s'.M, (∀ P v, T P v ∈ s'.KF) ∧ s'.KF ≤ Submodule.span ℂ {w | ∃ P v, w = T P v} ∧ GlobalTheory.PairLift.LiftsM c.θ s.M s'.M s.ν s.fd (fun P h g => conj (thetaKO ω g h (GlobalTheory.Chain.ptOf c.ψ c.θ s.M s'.M f P))) T := by
  first | exact @GlobalTheory.EvenOnto.LiftUp.liftUp_stage_span | exact GlobalTheory.EvenOnto.LiftUp.liftUp_stage_span | (intros; apply GlobalTheory.EvenOnto.LiftUp.liftUp_stage_span <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUpwardCuspSpanAndAdjoint

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.EvenOnto.UpLift

variable {D : D7}

theorem multT_le_noLevel' {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) : MultT θ M J χ ≤ MultT θ M ∅ 1 := by
  intro x hx
  rw [mem_multT] at hx ⊢
  refine Submodule.span_mono ?_ hx
  intro T hT
  exact ⟨hT.aut, hT.cusp, fun v k hk => absurd hk (Set.notMem_empty k), hT.equiv, hT.cont⟩

theorem upSpan : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ D : D7, UpSpan D := by
  intro h1 h2 h3 h4 D c hc k hk s s' hs hs' p hp u φ v _hv
  obtain ⟨T, hTK, hKT, hL⟩ := GlobalTheory.T.liftUp_multiplicitySpaces_span_kFiniteVectors h1 h2 h3 h4 D c k s s' p.ω p.f hc hk hs hs' hp.pre
  obtain ⟨F', hF', hint⟩ := hL _ (multT_le_noLevel' c.θ s.M _ _ u.2)
  have hlaw : ∀ P v', ∀ κ ∈ s'.J, ∀ g, F' (T P v') (g * κ) = F' (T P v') g := by
    intro P v' κ hκ g
    rw [← (hint P v' (g * κ)).2, ← (hint P v' g).2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)
    have hω : thetaKO p.ω g' (g * κ) (GlobalTheory.Chain.ptOf c.ψ c.θ s.M s'.M p.f P) =
        thetaKO p.ω g' g (GlobalTheory.Chain.ptOf c.ψ c.θ s.M s'.M p.f P) := by
      have hm : ((g', g * κ) : GA D s.V × GA D s'.V) = (g', g) * (1, κ) := by simp
      have h2 := hp.pre.law P 1 (one_mem _) κ hκ
      simp only [thetaKO]
      rw [hm, map_mul, Module.End.mul_apply, h2]
    simp only [hω]
  have hCC : F' ∈ s'.CC c := by
    refine GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors D s'.V s'.par s'.M c.θ hc.inf _ _ ?_ F' hF' ?_
    · intro κ hκ
      exact hs'.fin hκ
    · intro w hw κ hκ g
      have hx := hKT hw
      clear hw
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨P, v', rfl⟩ := hx
        simpa using hlaw P v' κ hκ g
      | zero => simp
      | add x y _ _ hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy, mul_add]
      | smul a x _ hx => simp only [map_smul, Pi.smul_apply, smul_eq_mul, hx]; ring
  have hup : p.up φ (PiLocalization₂.val u v) = F' (T φ v) := by
    funext h
    exact (hint φ v h).2
  rw [hup]
  exact Submodule.subset_span ⟨⟨F', hCC⟩, T φ v, hTK φ v, rfl⟩

theorem upAdj : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpAdj D := by
  intro hP D c hc k hk s s' hs hs' p hp u y φ v _ w _
  have hru : GlobalTheory.Grow.RapidDec s.V (PiLocalization₂.val u v) :=
    ((GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj hP D c hc k hk.le s hs).1 u v).2.2.2.2
  have hry : GlobalTheory.Grow.RapidDec s'.V (PiLocalization₂.val y w) :=
    ((GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj hP D c hc (k + 1) (Nat.succ_le_of_lt hk) s' hs').1 y w).2.2.2.2
  have hF := GlobalTheory.T.thetaKernel_iterated_integrals_swap D c.ψ c.θ s.V s'.V (c.χ k) (c.χ k) p.ω hc.inf hp.pre.weil (p.pt φ)
    (GlobalTheory.T.evenThetaChainStep_fockVectors_spherical_latticeVacua D c hc k hk s s' hs hs' p hp φ).1
    s.ν s.fd s'.ν s'.fd hs.haar hs.fund hs'.haar hs'.fund (PiLocalization₂.val u v) (PiLocalization₂.val y w) hru hry
  simp only [PiLocalization₂.pet, Lift.pet, Step.up]
  calc ∫ h in s'.fd, PiLocalization₂.val y w h * starRingEnd ℂ (∫ g in s.fd, conj (thetaKO p.ω g h (p.pt φ)) * PiLocalization₂.val u v g ∂s.ν) ∂s'.ν
      = ∫ h in s'.fd, ∫ g in s.fd, thetaKO p.ω g h (p.pt φ) * PiLocalization₂.val y w h * conj (PiLocalization₂.val u v g) ∂s.ν ∂s'.ν := by
        congr 1; funext h
        rw [← integral_conj, ← integral_const_mul]
        congr 1; funext g
        simp only [map_mul, Complex.conj_conj]; ring
    _ = ∫ g in s.fd, ∫ h in s'.fd, thetaKO p.ω g h (p.pt φ) * PiLocalization₂.val y w h * conj (PiLocalization₂.val u v g) ∂s'.ν ∂s.ν := hF
    _ = ∫ g in s.fd, PiLocalization₂.val (p.io y) (p.It φ w) g * starRingEnd ℂ (PiLocalization₂.val u v g) ∂s.ν := by
        congr 1; funext g
        rw [integral_mul_const]
        congr 1
        exact hp.io.eq y φ w g

theorem upSpan_upAdj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ D : D7, UpSpan D ∧ UpAdj D :=
  fun h1 h2 h3 h4 D => ⟨upSpan h1 h2 h3 h4 D, upAdj h3 D⟩

end GlobalTheory.EvenOnto.UpLift

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUpwardCuspSpanAndAdjointStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLiftUpward_cuspSpan_and_adjoint : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, UpSpan D ∧ UpAdj D := by
  first | exact @GlobalTheory.EvenOnto.UpLift.upSpan_upAdj | exact GlobalTheory.EvenOnto.UpLift.upSpan_upAdj | (intros; apply GlobalTheory.EvenOnto.UpLift.upSpan_upAdj <;> assumption)
end
end
