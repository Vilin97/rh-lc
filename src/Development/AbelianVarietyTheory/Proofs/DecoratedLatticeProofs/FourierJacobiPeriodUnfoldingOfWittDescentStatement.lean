module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSemidirectProductRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnFundamentalDomain
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSemidirectProductRational
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiPeriodLiftEqIntegralUnfoldedStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqMeanIntermediateSubgroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalUnitarySubgroupCountableDiscreteFundDoma
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientParaStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctionsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiHandOffAutomorphicStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedFlatMapFamilyContinuousInvariantIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedFunctionEqBesselPeriodIntegrandStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedFunctionEqBesselPeriodIntegrandStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbsConvOfInvariant

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.BesInt

theorem absConv_of_invariant : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∀ f : GA D B.V → ℂ, Continuous f →
    (∀ γ ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)), ∀ h, f (γ * h) = f h) →
    ∀ h, AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 fun h₁ n => f (n.1 * embA B.d B.o h₁ * h) := by
  intro D σ B f hf hinv h
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  obtain ⟨hemb, -, hconj, -, hrat⟩ := GlobalTheory.Unf.besSemi D σ B
  obtain ⟨KA, hKA, hcovA⟩ := B.cpt
  obtain ⟨⟨KN, hKN, hcovN⟩, -⟩ :=
    GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B.V σ B.d.e (isIsoSub_e B.d)

  let Φ : NFlag B.V B.d.e × GA D B.A → GA D B.V := fun p => p.1.1 * embA B.d B.o p.2 * h
  have hΦ : Continuous Φ :=
    ((continuous_subtype_val.comp continuous_fst).mul (hemb.comp continuous_snd)).mul continuous_const
  have hΩ : IsCompact (Φ '' (KN ×ˢ KA)) := (hKN.prod hKA).image hΦ
  obtain ⟨C, hC⟩ := hΩ.exists_bound_of_continuousOn hf.continuousOn

  have hbd : ∀ (h₁ : GA D B.A) (n : flagN B.d), ‖f (n.1 * embA B.d B.o h₁ * h)‖ ≤ C := by
    intro h₁ n
    obtain ⟨γ, hγ, hγK⟩ := hcovA h₁
    obtain ⟨δ, hδ, k, hk, hnk⟩ :=
      hcovN ⟨embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹, hconj n.1 n.2 γ⟩
    have heq : embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹ = δ.1 * k.1 := congrArg Subtype.val hnk
    have hγV : embA B.d B.o γ ∈ GQ B.V := by
      have := (hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩
      rwa [one_mul] at this
    have hδQ : (δ.1 : GA D B.V) ∈ GQ B.V := Subgroup.mem_subgroupOf.1 hδ
    have hηQ : (embA B.d B.o γ)⁻¹ * δ.1 ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hγV) hδQ,
        mul_mem (inv_mem (Subgroup.mem_sup_right ⟨γ, rfl⟩)) (Subgroup.mem_sup_left δ.2)⟩
    have e1 : n.1 = (embA B.d B.o γ)⁻¹ * (δ.1 * k.1) * embA B.d B.o γ := by rw [← heq]; group
    have e2 : n.1 * embA B.d B.o h₁ * h =
        ((embA B.d B.o γ)⁻¹ * δ.1) * (k.1 * embA B.d B.o (γ * h₁) * h) := by
      rw [e1, map_mul]; group
    rw [e2, hinv _ hηQ]
    exact hC _ ⟨(k, γ * h₁), ⟨hk, hγK⟩, rfl⟩

  have hfinA : B.vA.μ B.vA.𝓕 < ⊤ := by
    have hcov' : ∀ g : GA D B.A, ∃ γ ∈ GQ B.A, ∃ c ∈ KA, g = γ * c := fun g => by
      obtain ⟨γ, hγ, hc⟩ := hcovA g
      exact ⟨γ⁻¹, inv_mem hγ, γ * g, hc, by rw [inv_mul_cancel_left]⟩
    have h1 := GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain B.A B.vA.μ B.vA.𝓕 KA B.vA.haar B.vA.fund hKA
      hcov' (fun _ => (1 : ℂ)) continuous_const fun _ _ _ => rfl
    simpa using (integrableOn_const_iff (C := (1 : ℂ))).1 h1
  have hfinN : B.vN.ν B.vN.𝓝 < ⊤ := by rw [B.vN.unit.2.2]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2 hfinA.ne
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hfinN.ne
  have hK : Continuous (Function.uncurry fun (h₁ : GA D B.A) (n : flagN B.d) => f (n.1 * embA B.d B.o h₁ * h)) :=
    hf.comp (((continuous_subtype_val.comp continuous_snd).mul (hemb.comp continuous_fst)).mul continuous_const)
  exact Integrable.of_bound hK.aestronglyMeasurable C (Filter.Eventually.of_forall fun p => hbd p.1 p.2)

end GlobalTheory.Unf.BesInt

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSemidirectProductRationalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem _root_.GlobalTheory.T.besselGroup_semidirectProduct_rational : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), Continuous (embA B.d B.o) ∧ IsClosed (flagN B.d : Set (GA D B.V)) ∧ (∀ n ∈ flagN B.d, ∀ h, embA B.d B.o h * n * (embA B.d B.o h)⁻¹ ∈ flagN B.d) ∧ (∀ n ∈ flagN B.d, ∀ n' ∈ flagN B.d, ∀ h h', n * embA B.d B.o h = n' * embA B.d B.o h' → n = n' ∧ h = h') ∧ ∀ n ∈ flagN B.d, ∀ h, n * embA B.d B.o h ∈ GQ B.V ↔ n ∈ GQ B.V ∧ h ∈ GQ B.A := by
  first | exact @GlobalTheory.Unf.besSemi | exact GlobalTheory.Unf.besSemi | (intros; apply GlobalTheory.Unf.besSemi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselContinuousLeftInvariant

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

theorem unfF_continuous_invariant : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → Continuous (unfF s vL Y G Φ) ∧ ∀ γ ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)), ∀ h, unfF s vL Y G Φ (γ * h) = unfF s vL Y G Φ h := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ
  refine ⟨?_, ?_⟩
  · obtain ⟨hc, hi, he⟩ := GlobalTheory.T.pairedFlatMap_family_continuous_invariant_integral D hD ψ σ J B s vL Y Φ hY hΦ
    have h1 := (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D J.W₀ J.cpt J.v0 (GA D B.V)
      (fun h₀ h => tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)) hc hi).2.1
    have h2 : unfF s vL Y G Φ = fun h => G h *
        ∫ h₀ in J.v0.𝓕, tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂J.v0.μ := by
      funext h
      rw [unfF, he h]
    rw [h2]
    exact hG.2.1.mul h1
  · intro γ hγ h
    obtain ⟨hq, hb⟩ := Subgroup.mem_inf.1 hγ
    obtain ⟨-, hone, -, -, hdec, -⟩ :=
      GlobalTheory.MixPer.charLaws D ψ s.weil.std.1 B.V B.V₀ B.A B.L σ B.d B.o B.ζ 1
    obtain ⟨n, hn, h₁, rfl⟩ := (hdec γ).1 hb
    obtain ⟨hnq, hhq⟩ := ((GlobalTheory.T.besselGroup_semidirectProduct_rational D σ B).2.2.2.2 n hn h₁).1 hq
    have hth : IsThetaFunO ψ J.W₀ B.V₀ (flatFB s (s.om (1, h) Φ)) :=
      (GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ).2 σ J B s _ (s.weil.om_pres _ _ hΦ)
    have hinv := (GlobalTheory.T.fourierJacobiHandOff_automorphic D ψ σ J B s vL Y _ hY hth).1 h₁ hhq 1
    rw [mul_one] at hinv
    have e := GlobalTheory.T.unfoldedFunction_eq_besselPeriodIntegrand D hD ψ σ J B s vL Y G Φ hΦ h h₁ ⟨n, hn⟩
    refine e.trans ?_
    simp only [besFun, rTrans, unfF]
    rw [hinv, hone _ n hnq, hG.1 _ hq h, star_one, mul_one, mul_comm]

end GlobalTheory.Unf.FB
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselContinuousLeftInvariantStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem _root_.GlobalTheory.T.unfoldedBessel_continuous_leftInvariant : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → Continuous (unfF s vL Y G Φ) ∧ ∀ γ ∈ (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)), ∀ h, unfF s vL Y G Φ (γ * h) = unfF s vL Y G Φ h := by
  first | exact @GlobalTheory.Unf.FB.unfF_continuous_invariant | exact GlobalTheory.Unf.FB.unfF_continuous_invariant | (intros; apply GlobalTheory.Unf.FB.unfF_continuous_invariant <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiPeriodUnfoldingOfWittDescent

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem GlobalTheory.Unf.unfFB_of_descent : ∀ D : D7, Descent D → UnfFB D := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ
  haveI := s.vW.haar
  obtain ⟨hcnt, hdisc, hfd⟩ := GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain D B.V (GQ B.V ⊓ besGrp B.d B.o) inf_le_left
  obtain ⟨𝓑, h𝓑⟩ := hfd s.vW.μ s.vW.haar
  obtain ⟨hcont, hclN, hnorm, huniq, hrat⟩ := GlobalTheory.Unf.besSemi D σ B
  have hU := B.vN.unit
  have hHR : (semiMeas (flagN B.d) (embA B.d B.o) B.vA.μ B.vN.ν).IsHaarMeasure :=
    (GlobalTheory.MixPer.jacGrp_besGrp_haar D B.V B.V₀ B.A B.L σ B.d B.o B.vN.ν B.vN.𝓝 hU).2.2 B.vA.μ B.vA.haar
  obtain ⟨𝓡, h𝓡, hint⟩ := GlobalTheory.Unf.semiFd_iterated D B.V B.A (flagN B.d) (embA B.d B.o) hcont hclN hnorm huniq hrat B.vA B.vN.ν B.vN.𝓝
    hU.1 hU.2.1 hHR
  obtain ⟨hFc, hFi⟩ := GlobalTheory.T.unfoldedBessel_continuous_leftInvariant D hD ψ σ J B s vL Y G Φ hY hG hΦ
  obtain ⟨hI, hL⟩ := GlobalTheory.T.fourierJacobiPeriod_lift_eq_integral_unfolded D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  have habs := GlobalTheory.Unf.BesInt.absConv_of_invariant D σ B _ hFc hFi
  have hm : ∀ h : GA D B.V, Measurable fun g : GA D B.V => unfF s vL Y G Φ (g * h) :=
    fun h => (hFc.comp (continuous_mul_const h)).measurable
  have key := GlobalTheory.quot_fubini_mean (GA D B.V) s.vW.μ (besGrp B.d B.o) (GQ B.V ⊓ besGrp B.d B.o) inf_le_right
    (GlobalTheory.BesClosed.besGrp_isClosed D B.V B.V₀ B.A B.L σ B.d B.o) hcnt hdisc B.μR hHR 𝓡 𝓑 h𝓡 h𝓑 (unfF s vL Y G Φ)
    hFc.measurable hFi hI (fun h => ((hint _ (hm h)).1).2 (habs h))
  rw [← hL] at key
  convert key using 2 with h
  have e2 : (∫ r : besGrp B.d B.o in 𝓡, unfF s vL Y G Φ (r * h) ∂B.μR) =
      ∫ h₁ in B.vA.𝓕, ∫ n in B.vN.𝓝, unfF s vL Y G Φ (n.1 * embA B.d B.o h₁ * h) ∂B.vN.ν ∂B.vA.μ :=
    (hint _ (hm h)).2 (habs h)
  rw [e2, BesLev.per, besPer]
  congr 1; funext h₁; congr 1; funext n
  exact (GlobalTheory.T.unfoldedFunction_eq_besselPeriodIntegrand D hD ψ σ J B s vL Y G Φ hΦ h h₁ n).symm

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiPeriodUnfoldingOfWittDescentStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.fourierJacobi_period_unfolding_of_witt_descent : ∀ D : D7, Descent D → UnfFB D := by
  first | exact @GlobalTheory.Unf.unfFB_of_descent | exact GlobalTheory.Unf.unfFB_of_descent | (intros; apply GlobalTheory.Unf.unfFB_of_descent <;> assumption)
end
end
