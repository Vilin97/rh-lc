module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselBasePointIsUnfoldingBasePointSpecStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselThetaIntegrandIsUnfoldingTheta
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldOverFlagUnipotentThetaLiftStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedTermBasePointEqFlatMapPairingStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExistStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPaStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FubiniCompactQuotient
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedFlatMapFamilyContinuousInvariantIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalUnitarySubgroupCountableDiscreteFundDomaStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselJacobiIntegralAbsLeStatement
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedFlatMapFamilyContinuousInvariantIntegralStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselThetaIntegrandIsUnfoldingThetaStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem _root_.GlobalTheory.T.fourierBesselThetaIntegrand_isUnfoldingTheta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (y : WO J.W₀ B.L → ℂ), Quasi ψ J.W₀ B.L y → ∀ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = x0 B → IsTh ψ J.d B.V x₀ (th J ψ B y) := by
  first | exact @GlobalTheory.th_isTh | exact GlobalTheory.th_isTh | (intros; apply GlobalTheory.th_isTh <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiIntegralOverNUnfold

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.FB

theorem weilRepresentationOnFunctions_embed_mul {D : D7} {V W : HSp D} (om : Om V W) (e g : GA D V) (h : GA D W) (Φ : WO V W → ℂ) :
    om (g, h) (om (e, 1) Φ) = om (g * e, h) Φ := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem fjN_unfold : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → ∀ h₀, ∫ n in J.vN.𝓝, fjSrcKerFun ψ J.d (J.ker ψ B.ζ Y) (s.lift G Φ) h₀ n ∂J.vN.ν = ∫ h in 𝓑, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂s.vW.μ := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑 h₀
  obtain ⟨x₀, hx₀, hbase, hR, -, -⟩ := GlobalTheory.T.fourierBesselBasePoint_isUnfoldingBasePoint_spec D σ B
  obtain ⟨-, -, hvM, -⟩ := GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist D
  obtain ⟨vb⟩ := hvM (σ + 1) J.W₀.rank
  obtain ⟨om', hom'⟩ := (hD ψ J.W B.V s.χV s.χW s.om s.weil).1 J.W₀ (σ + 1) J.d
  have hq : Quasi ψ J.W₀ B.L (Y h₀) := quasi_of_fam hY h₀
  have hTh := GlobalTheory.T.fourierBesselThetaIntegrand_isUnfoldingTheta D ψ s.weil.std σ J B (Y h₀) hq x₀ hx₀
  have hΦ' : IsThetaFunO ψ J.W B.V (s.om (J.d.emb0 h₀, 1) Φ) := s.weil.om_pres _ _ hΦ
  have h𝓑' : IsFundamentalDomain (GQ B.V ⊓ Rgrp B.V (rat x₀) : Subgroup (GA D B.V)) 𝓑 s.vW.μ := by
    rw [hR]; exact h𝓑
  have key := (GlobalTheory.T.unfold_over_flagUnipotent_thetaLift D hD ψ J.W J.W₀ B.V (σ + 1) J.d s.χV s.χW s.om om' s.weil hom' s.vS J.vN vb s.vU s.vW x₀
    (th J ψ B (Y h₀)) hbase hTh G (s.om (J.d.emb0 h₀, 1) Φ) hG hΦ' 𝓑 h𝓑').2
  have hL : (fun n : flagN J.d => fjSrcKerFun ψ J.d (J.ker ψ B.ζ Y) (s.lift G Φ) h₀ n) =
      fun n => th J ψ B (Y h₀) n.1 * liftS s.om s.vW.μ s.vW.𝓕 G (s.om (J.d.emb0 h₀, 1) Φ) n.1 := by
    funext n
    simp only [fjSrcKerFun, JacLev.ker, th, Step.lift, liftS_apply, zl, weilRepresentationOnFunctions_embed_mul]
    ring
  have hR' : (fun h => G h * fl ψ J.d B.V s.vS vb s.vU (th J ψ B (Y h₀)) (rat x₀) (s.om (1, h) (s.om (J.d.emb0 h₀, 1) Φ))) =
      fun h => G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) := by
    funext h
    rw [weilRepresentationOnFunctions_embed_mul, one_mul, hx₀, (GlobalTheory.T.unfoldedTerm_basePoint_eq_flatMap_pairing D ψ σ J B s vb vL (Y h₀) _ hq (s.weil.om_pres _ _ hΦ)).1]
  rw [hL, ← hR']
  exact key

end GlobalTheory.Unf.FB

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiIntegralOverNUnfoldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem _root_.GlobalTheory.T.fourierJacobi_integral_over_N_unfold : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → ∀ h₀, ∫ n in J.vN.𝓝, fjSrcKerFun ψ J.d (J.ker ψ B.ζ Y) (s.lift G Φ) h₀ n ∂J.vN.ν = ∫ h in 𝓑, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂s.vW.μ := by
  exact @GlobalTheory.Unf.FB.fjN_unfold
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselUnfoldedIntegrandIntegrable

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

theorem quasiFam_bdd_on_compact {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S L : HSp D}
    (v : VolM D L.rank S.rank) {Y : GA D S → WO S L → ℂ} (hY : IsQuasiFam ψ S L Y) {K : Set (GA D S)}
    (hK : IsCompact K) : ∃ M : ℝ, ∀ h ∈ K, ∀ w, ‖Y h w‖ ≤ M := by
  set Kf : Mx D L.rank S.rank → GA D S → ℂ := fun x p => ((‖Y p x‖ : ℝ) : ℂ) with hKf
  have hc : Continuous (Function.uncurry Kf) :=
    Complex.continuous_ofReal.comp (continuous_norm.comp (hY.cont.comp continuous_swap))
  have hper : ∀ γ ∈ ratMx D L.rank S.rank, ∀ x p, Kf (γ + x) p = Kf x p := by
    rintro γ ⟨γ', rfl⟩ x p
    have hq := hY.quasi p γ' x
    have h1 : (incA D).toAddMonoidHom.mapMatrix γ' = ratW L S γ' := rfl
    simp only [hKf, h1, hq, norm_mul, hψ.1.2.1, one_mul]
  obtain ⟨-, -, hloc, -⟩ := GlobalTheory.T.adelicMatrixQuotient_periodicIntegral_continuous_param D L.rank S.rank v (GA D S) Kf hc hper
  choose C hC using hloc
  obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun p => {q | ∀ x, ‖Kf x q‖ ≤ C p}) (fun p _ => hC p)
  refine ⟨∑ p ∈ t, |C p|, fun h hh w => ?_⟩
  obtain ⟨p, hp, hhp⟩ := Set.mem_iUnion₂.1 (hcov hh)
  have := hhp w
  simp only [hKf, Complex.norm_real, Real.norm_eq_abs, abs_norm] at this
  exact this.trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun p => |C p|) (fun _ _ => abs_nonneg _) hp))

theorem unfolded_integrable : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → Integrable (Function.uncurry fun h₀ h => G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)) ((J.v0.μ.restrict J.v0.𝓕).prod (s.vW.μ.restrict 𝓑)) := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  haveI := J.v0.haar
  haveI := s.vW.haar
  obtain ⟨hcont, hinv, -⟩ := GlobalTheory.T.pairedFlatMap_family_continuous_invariant_integral D hD ψ σ J B s vL Y Φ hY hΦ
  obtain ⟨x₀, hx₀, hbase, hR, -, -⟩ := GlobalTheory.T.fourierBesselBasePoint_isUnfoldingBasePoint_spec D σ B
  obtain ⟨om', hom'⟩ := (hD ψ J.W B.V s.χV s.χW s.om s.weil).1 J.W₀ (σ + 1) J.d
  obtain ⟨-, -, hvb, -⟩ := GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist D
  obtain ⟨vb⟩ := hvb (σ + 1) J.W₀.rank
  have h𝓑' : IsFundamentalDomain (GQ B.V ⊓ Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) : Subgroup (GA D B.V)) 𝓑 s.vW.μ := by
    rw [hR]; exact h𝓑
  obtain ⟨C, A, hCA⟩ := GlobalTheory.T.unfolded_besselJacobi_integral_abs_le D ψ J.W J.W₀ B.V (σ + 1) J.d s.χV s.χW s.om om' s.weil hom' s.vS vb s.vU s.vW x₀
    hbase G Φ hG hΦ 𝓑 h𝓑'
  obtain ⟨hΓc, hΓd, -⟩ := GlobalTheory.T.rational_unitary_subgroup_countable_discrete_fundDomain D J.W₀ (GQ J.W₀) le_rfl
  refine GlobalTheory.fubini_compact_quotient (GA D J.W₀) J.v0.μ (GQ J.W₀) hΓc hΓd J.cpt J.v0.𝓕 J.v0.fund (GA D B.V)
    (s.vW.μ.restrict 𝓑) (fun h₀ h => G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)) ?_ ?_ ?_
  · exact ((hG.2.1.comp continuous_snd).mul hcont).measurable
  · intro γ hγ h x
    simp only [hinv γ hγ h x]
  · intro K hK
    obtain ⟨M, hM⟩ := quasiFam_bdd_on_compact s.weil.std vL hY hK
    obtain ⟨c, hc⟩ := hK.bddAbove_image
      ((continuous_const.mul ((continuous_height J.W).pow A)).comp J.d.continuous_embed).continuousOn
    refine ⟨M.toNNReal * c.toNNReal, fun h₀ hh₀ => ?_⟩
    have hc' : C * height J.W (J.d.emb0 h₀) ^ A ≤ c := hc ⟨h₀, hh₀, rfl⟩
    calc ∫⁻ h, ‖G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)‖ₑ ∂(s.vW.μ.restrict 𝓑)
        ≤ ∫⁻ h in 𝓑, ENNReal.ofReal M * (‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
            ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 (s.om (J.d.emb0 h₀, h) Φ) ((rat x₀ : Mx D B.V.rank (σ + 1)) ⬝ u.1.1)
              ((rat x₀ : Mx D B.V.rank (σ + 1)) ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν) ∂s.vW.μ := by
          refine lintegral_mono fun h => ?_
          rw [enorm_mul, mul_left_comm]
          have := (GlobalTheory.T.unfoldedTerm_basePoint_eq_flatMap_pairing D ψ σ J B s vb vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) (quasi_of_fam hY h₀)
            (s.weil.om_pres _ _ hΦ)).2 M (hM h₀ hh₀)
          rw [hx₀]
          gcongr
      _ = ENNReal.ofReal M * ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
            ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 (s.om (J.d.emb0 h₀, h) Φ) ((rat x₀ : Mx D B.V.rank (σ + 1)) ⬝ u.1.1)
              ((rat x₀ : Mx D B.V.rank (σ + 1)) ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν ∂s.vW.μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal c :=
          by gcongr; exact (hCA (J.d.emb0 h₀)).trans (ENNReal.ofReal_le_ofReal hc')
      _ = ((M.toNNReal * c.toNNReal : NNReal) : ENNReal) := by
          rw [ENNReal.coe_mul]; rfl

end GlobalTheory.Unf.FB
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselUnfoldedIntegrandIntegrableStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem _root_.GlobalTheory.T.jacobiToBessel_unfoldedIntegrand_integrable : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → Integrable (Function.uncurry fun h₀ h => G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ)) ((J.v0.μ.restrict J.v0.𝓕).prod (s.vW.μ.restrict 𝓑)) := by
  first | exact @GlobalTheory.Unf.FB.unfolded_integrable | exact GlobalTheory.Unf.FB.unfolded_integrable | (intros; apply GlobalTheory.Unf.FB.unfolded_integrable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiPeriodLiftEqIntegralUnfolded

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

theorem per_lift_eq_integral_unfF : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → IntegrableOn (unfF s vL Y G Φ) 𝓑 s.vW.μ ∧ J.per ψ B.ζ Y (s.lift G Φ) = ∫ h in 𝓑, unfF s vL Y G Φ h ∂s.vW.μ := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  have := s.vW.haar
  have := J.v0.haar
  have hI := GlobalTheory.T.jacobiToBessel_unfoldedIntegrand_integrable D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  have hin := GlobalTheory.T.fourierJacobi_integral_over_N_unfold D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  have hc := (GlobalTheory.T.pairedFlatMap_family_continuous_invariant_integral D hD ψ σ J B s vL Y Φ hY hΦ).2.2
  have hU : ∀ h, unfF s vL Y G Φ h = ∫ h₀ in J.v0.𝓕, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂J.v0.μ := by
    intro h
    rw [unfF, hc h, integral_const_mul]
  constructor
  · have := hI.integral_prod_right
    refine this.congr ?_
    exact Filter.Eventually.of_forall fun h => (hU h).symm
  · calc J.per ψ B.ζ Y (s.lift G Φ)
        = ∫ h₀ in J.v0.𝓕, ∫ h in 𝓑, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂s.vW.μ ∂J.v0.μ := by
          unfold JacLev.per fjSrcKer
          congr 1
          funext h₀
          exact hin h₀
      _ = ∫ h in 𝓑, ∫ h₀ in J.v0.𝓕, G h * tFlat s vL (Y h₀) (s.om (J.d.emb0 h₀, h) Φ) ∂J.v0.μ ∂s.vW.μ :=
          integral_integral_swap hI
      _ = ∫ h in 𝓑, unfF s vL Y G Φ h ∂s.vW.μ := by
          congr 1
          funext h
          exact (hU h).symm

end GlobalTheory.Unf.FB

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiPeriodLiftEqIntegralUnfoldedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem _root_.GlobalTheory.T.fourierJacobiPeriod_lift_eq_integral_unfolded : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ), IsQuasiFam ψ J.W₀ B.L Y → RapidDec B.V G → IsThetaFunO ψ J.W B.V Φ → ∀ 𝓑 : Set (GA D B.V), IsFundamentalDomain (GQ B.V ⊓ besGrp B.d B.o : Subgroup (GA D B.V)) 𝓑 s.vW.μ → IntegrableOn (unfF s vL Y G Φ) 𝓑 s.vW.μ ∧ J.per ψ B.ζ Y (s.lift G Φ) = ∫ h in 𝓑, unfF s vL Y G Φ h ∂s.vW.μ := by
  first | exact @GlobalTheory.Unf.FB.per_lift_eq_integral_unfF | exact GlobalTheory.Unf.FB.per_lift_eq_integral_unfF | (intros; apply GlobalTheory.Unf.FB.per_lift_eq_integral_unfF <;> assumption)
end
end
