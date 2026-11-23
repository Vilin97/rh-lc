module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RapidDecRTrans
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPairedKernelFlatMapWeilTranslateStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPaStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedThetaKernelContinuousAndRationallyInvarian
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuousStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitutionStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.XLastLin
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorThetaFunSupModerateGrowth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselFlatMapEquivariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralLeOfTsum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalEmbeddingLePow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightWittEmbeddingLeConstMul
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightComparableWittDecompositionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightOrthogonalSumComparableStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Topology.Compactness.Paracompact

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatKernelPairingRationalPointsInvariant

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.KerRat

theorem flat_kernel_rat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → ∀ h, (∀ γ ∈ GQ J.W₀, ∀ h₀ h₁, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ ((γ * h₀), B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz ((γ * h₀), 1) Φ₀) 0 = contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0) ∧ ∀ γ ∈ GQ B.A, ∀ h₀ h₁, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb ((γ * h₁), 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 = contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 := by
  intro D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ h
  obtain ⟨x, hx, hxe⟩ := GlobalTheory.JacMean.xLast_lin B.d B.o B.line
  have hΞ : IsThetaFunO ψ J.W₀ B.V₀ (flFB s (s.om (1, h) Φ)) := by
    have e := (GlobalTheory.Unf.Flat.flatLaw D ψ s.weil.std J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.vU x hx 0
      (s.om (1, h) Φ) (s.weil.om_pres (1, h) Φ hΦ)).2
    simp only [flFB, flatS, hxe]
    exact e
  generalize flFB s (s.om (1, h) Φ) = Ξ at hΞ ⊢
  set Y : GA D J.W₀ → WO J.W₀ B.L → ℂ := fun h₀ => omz (h₀, 1) Φ₀ with hYdef
  have hYl : ∀ γ ∈ GQ J.W₀, ∀ h₀ w, Y (γ * h₀) w = Y h₀ (w ⬝ mt J.W₀ γ) := by
    intro γ hγ h₀ w
    have e := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ J.W₀ B.L χ χz omz homz Φ₀ hΦ₀ γ hγ 1 (one_mem _) h₀ 1 w
    rw [one_mul, inv_one, mt_one, Matrix.one_mul] at e
    exact e
  have hJ : Continuous fun p : (GA D J.W₀ × GA D B.L) × WO J.W₀ B.L => omz p.1 Φ₀ p.2 :=
    (@GlobalTheory.Unf.jointCont_all D) ψ _ _ χ χz omz homz Φ₀ hΦ₀
  have hYc : Continuous fun p : GA D J.W₀ × WO J.W₀ B.L => Y p.1 p.2 :=
    hJ.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)
  have hn : ∀ x, ψ x * star (ψ x) = 1 := fun x => by
    have h1 : ‖ψ x‖ = 1 := s.weil₀.std.1.2.1 x
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
  set K : Mx D B.L.rank J.W₀.rank → GA D J.W₀ × GA D B.A → ℂ := fun w p =>
    s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB ⬝ w) * star (Y p.1 w) with hK
  have hP : ∀ h₀ h₁, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ) (omz (h₀, 1) Φ₀) 0 =
      ∫ w in vL.𝓕, K w (h₀, h₁) ∂vL.μ := fun h₀ h₁ => by
    simp only [contractT, thPair, OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add, hK, hYdef]
  have hc : Continuous (Function.uncurry K) := by
    have h1 := GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ _ _ _ _ _ s.weil₀ Ξ hΞ
    have h2 : Continuous fun q : Mx D B.L.rank J.W₀.rank × GA D J.W₀ × GA D B.A =>
        (((q.2.1, B.o.emb (q.2.2, 1)), B.o.jB ⬝ q.1) : (GA D J.W₀ × GA D B.V₀) × WO J.W₀ B.V₀) :=
      ((continuous_fst.comp continuous_snd).prodMk (B.o.continuous_emb.comp
        ((continuous_snd.comp continuous_snd).prodMk continuous_const))).prodMk
        (continuous_const.matrix_mul continuous_fst)
    have h3 : Continuous fun q : Mx D B.L.rank J.W₀.rank × GA D J.W₀ × GA D B.A =>
        ((q.2.1, q.1) : GA D J.W₀ × WO J.W₀ B.L) := (continuous_fst.comp continuous_snd).prodMk continuous_fst
    exact (h1.comp h2).mul (hYc.comp h3).star
  have hper : ∀ γ ∈ ratMx D B.L.rank J.W₀.rank, ∀ x p, K (γ + x) p = K x p := by
    rintro _ ⟨γ, rfl⟩ x p
    have e1 := (s.weil₀.om_pres (p.1, B.o.emb (p.2, 1)) Ξ hΞ).quasi (B.o.iB * γ) (B.o.jB ⬝ x)
    have e2 := (homz.om_pres (p.1, 1) Φ₀ hΦ₀).quasi γ x
    rw [ratW_eq, rat_mul] at e1
    rw [ratW_eq] at e2
    have e3 : symplOH J.W₀ B.V₀ (B.o.jB ⬝ rat γ) (B.o.jB ⬝ x) = symplOH J.W₀ B.L (rat γ) x := by
      rw [B.o.symplOH_resT]
      simp only [OrthDec.resT_apply, cancel₂ B.o.pA_jB, cancel₂ B.o.pB_jB, Matrix.zero_mul, Matrix.one_mul,
        symplOH_zero_left, zero_add]
    change s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB ⬝ (rat γ + x)) * star (omz (p.1, 1) Φ₀ (rat γ + x)) =
      s.om₀ (p.1, B.o.emb (p.2, 1)) Ξ (B.o.jB ⬝ x) * star (omz (p.1, 1) Φ₀ x)
    rw [Matrix.mul_add, e2]
    refine (congrArg (· * _) e1).trans ?_
    change ψ (-symplOH J.W₀ B.V₀ (B.o.jB ⬝ rat γ) (B.o.jB ⬝ x)) * _ * _ = _
    rw [e3, star_mul', mul_mul_mul_comm, hn, one_mul]
  obtain ⟨-, -, -, hinv⟩ := GlobalTheory.T.adelicMatrixQuotient_periodicIntegral_continuous_param D _ _ vL _ K hc hper
  refine ⟨fun γ hγ h₀ h₁ => ?_, fun γ hγ h₀ h₁ => ?_⟩
  · rw [hP, hP, ← hinv (GlobalTheory.PairKer.mulRight J.W₀ _ γ) (continuous_id.matrix_mul continuous_const)
      (continuous_id.matrix_mul continuous_const) ?_ (h₀, h₁)]
    · congr 1; funext w
      have e := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ _ _ _ _ _ s.weil₀ Ξ hΞ γ hγ 1 (one_mem _) h₀ (B.o.emb (h₁, 1)) (B.o.jB ⬝ w)
      rw [one_mul, inv_one, mt_one, Matrix.one_mul, Matrix.mul_assoc] at e
      change s.om₀ (γ * h₀, B.o.emb (h₁, 1)) Ξ (B.o.jB ⬝ w) * star (Y (γ * h₀) w) =
        s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ (B.o.jB ⬝ (w ⬝ mt J.W₀ γ)) * star (Y h₀ (w ⬝ mt J.W₀ γ))
      rw [e, hYl γ hγ]
    · intro x
      refine ⟨fun h => ?_, fun h => ratMx_mul h ((mem_GQ_iff _ _).1 hγ)⟩
      rw [← (GlobalTheory.PairKer.mulRight J.W₀ _ γ).symm_apply_apply x]
      exact ratMx_mul h ((mem_GQ_iff _ _).1 (inv_mem hγ))
  · refine (hP h₀ (γ * h₁)).trans (Eq.trans ?_ (hP h₀ h₁).symm)
    refine integral_congr_ae (.of_forall fun w => ?_)
    have e := GlobalTheory.PairKer.om_emb s.weil₀ hΞ B.o hγ h₀ h₁ w
    show K w (h₀, γ * h₁) = K w (h₀, h₁)
    rw [hK]
    exact congrArg (· * star (Y h₀ w)) e

end GlobalTheory.KerRat

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatKernelPairingRationalPointsInvariantStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.flatKernelPairing_rationalPoints_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → ∀ h, (∀ γ ∈ GQ J.W₀, ∀ h₀ h₁, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ ((γ * h₀), B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz ((γ * h₀), 1) Φ₀) 0 = contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0) ∧ ∀ γ ∈ GQ B.A, ∀ h₀ h₁, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb ((γ * h₁), 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 = contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 := by
  first | exact @GlobalTheory.KerRat.flat_kernel_rat | exact GlobalTheory.KerRat.flat_kernel_rat | (intros; apply GlobalTheory.KerRat.flat_kernel_rat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselPairedKernelHeightBound

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
namespace GlobalTheory.PairKerBound

theorem kernel_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → ∃ (C : ℝ) (a : ℕ), ∀ h h₀ h₁, ‖contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0‖ ≤ C * (height J.W₀ h₀ * height B.A h₁ * height B.V h) ^ a := by
  intro D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  obtain ⟨x, hx, hxe⟩ := GlobalTheory.JacMean.xLast_lin B.d B.o B.line
  obtain ⟨C₁, A₁, hC₁⟩ := GlobalTheory.FlatSup.flat_sup_growth D ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s x hx Φ hΦ
  obtain ⟨C₂, A₂, hC₂⟩ := GlobalTheory.SupThetaGrowth.om_sup_growth D ψ J.W₀ B.L χ χz omz homz Φ₀ hΦ₀
  obtain ⟨C₃, hC₃⟩ := GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le D J.W J.W₀ (σ + 1) J.d
  obtain ⟨C₄, hC₄⟩ := GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le D B.V B.V₀ σ B.d
  obtain ⟨C₅, a₅, hC₅⟩ := GlobalTheory.EmbHeight.height_emb_le D B.V₀ B.A B.L B.o
  have key : ∀ h h₀ h₁ w, s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ)) w =
      flatS J.d B.d s (rat x) 0 (s.om (J.d.emb0 h₀, embA B.d B.o h₁ * h) Φ) w := by
    intro h h₀ h₁ w
    have e := GlobalTheory.AscFlatEquiFB.flFB_equivariant D ψ σ J B s (s.om (1, h) Φ) (s.weil.om_pres _ _ hΦ) h₀ 1 (one_mem _) h₁
    have hp : psiBes ψ B.d 1 (vecB B.o B.ζ) 1 = 1 :=
      (GlobalTheory.MixPer.charLaws D ψ s.weil.std.1 B.V B.V₀ B.A B.L σ B.d B.o B.ζ 1).2.1 _ 1 (one_mem _)
    rw [hp, star_one, one_smul, one_mul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one] at e
    rw [← e]
    show flatS J.d B.d s (xLast B.d (vecB B.o B.ζ)) 0 _ w = _
    rw [hxe]
  have hC₃1 : 1 ≤ C₃ := by simpa using (GlobalTheory.Grow.one_le_height J.W (J.d.emb0 1)).trans (hC₃ 1)
  have hC₄1 : 1 ≤ C₄ := by simpa using (GlobalTheory.Grow.one_le_height B.V (B.d.emb0 1)).trans (hC₄ 1)
  have hC₅1 : 1 ≤ C₅ := by simpa using (GlobalTheory.Grow.one_le_height B.V₀ (B.o.emb (1, 1))).trans (hC₅ 1)
  have hM₁ : 0 ≤ max C₁ 0 := le_max_right _ _
  have hM₂ : 0 ≤ max C₂ 0 := le_max_right _ _
  have hK : 0 ≤ C₃ * C₄ * C₅ := by positivity
  refine ⟨max C₁ 0 * (C₃ * C₄ * C₅) ^ A₁ * max C₂ 0, (a₅ + 2) * A₁ + A₂, fun h h₀ h₁ => ?_⟩
  have p0 : 1 ≤ height J.W₀ h₀ := GlobalTheory.Grow.one_le_height _ _
  have p1 : 1 ≤ height B.A h₁ := GlobalTheory.Grow.one_le_height _ _
  have p2 : 1 ≤ height B.V h := GlobalTheory.Grow.one_le_height _ _
  generalize hX : height J.W₀ h₀ * height B.A h₁ * height B.V h = X
  have n01 : 0 ≤ height J.W₀ h₀ * height B.A h₁ := mul_nonneg (by linarith) (by linarith)
  have q0 : height J.W₀ h₀ ≤ X := by
    rw [← hX]; exact (le_mul_of_one_le_right (by linarith) p1).trans (le_mul_of_one_le_right n01 p2)
  have q1 : height B.A h₁ ≤ X := by
    rw [← hX]; exact (le_mul_of_one_le_left (by linarith) p0).trans (le_mul_of_one_le_right n01 p2)
  have q2 : height B.V h ≤ X := by
    rw [← hX]; exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le p0 p1)
  have hX1 : 1 ≤ X := p2.trans q2
  have hX0 : 0 ≤ X := by linarith
  have e1 : height J.W (J.d.emb0 h₀) ≤ C₃ * X := (hC₃ h₀).trans (mul_le_mul_of_nonneg_left q0 (by linarith))
  have e2 : height B.V (embA B.d B.o h₁ * h) ≤ C₄ * C₅ * X ^ (a₅ + 1) := by
    have f1 : height B.V (embA B.d B.o h₁) ≤ C₄ * (C₅ * X ^ a₅) := by
      rw [embA_apply]
      refine (hC₄ _).trans (mul_le_mul_of_nonneg_left ((hC₅ h₁).trans ?_) (by linarith))
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) q1 _) (by linarith)
    calc _ ≤ height B.V (embA B.d B.o h₁) * height B.V h := GlobalTheory.Grow.height_mul_le _ _ _
      _ ≤ (C₄ * (C₅ * X ^ a₅)) * X := mul_le_mul f1 q2 (by linarith) (by positivity)
      _ = C₄ * C₅ * X ^ (a₅ + 1) := by ring
  have hP : height J.W (J.d.emb0 h₀) * height B.V (embA B.d B.o h₁ * h) ≤ C₃ * C₄ * C₅ * X ^ (a₅ + 2) := by
    calc _ ≤ (C₃ * X) * (C₄ * C₅ * X ^ (a₅ + 1)) :=
          mul_le_mul e1 e2 (zero_le_one.trans (GlobalTheory.Grow.one_le_height _ _)) (by positivity)
      _ = _ := by ring
  have hf : ∀ w, ‖flatS J.d B.d s (rat x) 0 (s.om (J.d.emb0 h₀, embA B.d B.o h₁ * h) Φ) w‖ ≤
      max C₁ 0 * (C₃ * C₄ * C₅) ^ A₁ * X ^ ((a₅ + 2) * A₁) := by
    intro w
    have hP0 : 0 ≤ height J.W (J.d.emb0 h₀) * height B.V (embA B.d B.o h₁ * h) :=
      mul_nonneg (zero_le_one.trans (GlobalTheory.Grow.one_le_height _ _)) (zero_le_one.trans (GlobalTheory.Grow.one_le_height _ _))
    calc _ ≤ C₁ * (height J.W (J.d.emb0 h₀) * height B.V (embA B.d B.o h₁ * h)) ^ A₁ := hC₁ _ _ 0 w
      _ ≤ max C₁ 0 * (height J.W (J.d.emb0 h₀) * height B.V (embA B.d B.o h₁ * h)) ^ A₁ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hP0 _)
      _ ≤ max C₁ 0 * (C₃ * C₄ * C₅ * X ^ (a₅ + 2)) ^ A₁ :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP0 hP _) hM₁
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  have hg : ∀ v, ‖omz (h₀, 1) Φ₀ v‖ ≤ max C₂ 0 * X ^ A₂ := by
    intro v
    have := hC₂ h₀ 1 v
    rw [GlobalTheory.Grow.height_one, mul_one] at this
    refine this.trans ?_
    calc C₂ * height J.W₀ h₀ ^ A₂ ≤ max C₂ 0 * height J.W₀ h₀ ^ A₂ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) q0 _) hM₂
  unfold contractT thPair
  have hvol := vL.covol.2.2
  refine (norm_setIntegral_le_of_norm_le_const (C := max C₁ 0 * (C₃ * C₄ * C₅) ^ A₁ * X ^ ((a₅ + 2) * A₁) *
    (max C₂ 0 * X ^ A₂)) (by rw [hvol]; exact ENNReal.one_lt_top) fun v _ => ?_).trans ?_
  · beta_reduce
    rw [norm_mul, norm_star, key]
    exact mul_le_mul (hf _) (hg _) (norm_nonneg _) (by positivity)
  · rw [measureReal_def, hvol, ENNReal.toReal_one, mul_one, pow_add]
    exact le_of_eq (by ring)

end GlobalTheory.PairKerBound
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselPairedKernelHeightBoundStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.fourierJacobiToBessel_pairedKernel_heightBound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → ∃ (C : ℝ) (a : ℕ), ∀ h h₀ h₁, ‖contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0‖ ≤ C * (height J.W₀ h₀ * height B.A h₁ * height B.V h) ^ a := by
  first | exact @GlobalTheory.PairKerBound.kernel_bound | exact GlobalTheory.PairKerBound.kernel_bound | (intros; apply GlobalTheory.PairKerBound.kernel_bound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodHandedFunctionConvergesContinuous

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
namespace GlobalTheory.JacMean

theorem handP_law : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B)
    (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz →
    ∀ (φ : GA D J.W₀ → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), RapidDec J.W₀ φ → IsThetaFunO ψ J.W₀ B.L Φ₀ →
    IsThetaFunO ψ J.W B.V Φ →
    (∃ (C : ℝ) (a : ℕ), ∀ h h₁, ‖handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ)) h₁‖ ≤ C * (quotHeight B.A h₁ * height B.V h) ^ a) ∧
    Continuous fun q : GA D B.V × GA D B.A => handP s vL omz φ Φ₀ (flFB s (s.om (1, q.1) Φ)) q.2 := by
  intro D ψ σ J B s vL χ χz omz homz φ Φ₀ Φ hφ hΦ₀ hΦ
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  haveI : ∀ V : HSp D, BorelSpace (GA D V) := fun V => ⟨rfl⟩
  have hfin : J.v0.μ J.v0.𝓕 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol J.W₀ _ _ J.v0.haar J.v0.fund
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.2 hfin.ne
  obtain ⟨K, hK⟩ : ∃ K : GA D B.V → GA D J.W₀ → GA D B.A → ℂ, K = fun h h₀ h₁ => contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 := ⟨_, rfl⟩
  have hKc : Continuous fun q : GA D B.V × GA D J.W₀ × GA D B.A => K q.1 q.2.1 q.2.2 := by
    subst hK; exact GlobalTheory.T.continuous_pairedKernel_flatMap_weilTranslate D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  obtain ⟨C, a, hKp⟩ : ∃ (C : ℝ) (a : ℕ), ∀ h h₀ h₁, ‖K h h₀ h₁‖ ≤ C * (height J.W₀ h₀ * height B.A h₁ * height B.V h) ^ a := by
    subst hK; exact GlobalTheory.T.fourierJacobiToBessel_pairedKernel_heightBound D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  have hKi : ∀ h, (∀ γ ∈ GQ J.W₀, ∀ h₀ h₁, K h (γ * h₀) h₁ = K h h₀ h₁) ∧ ∀ γ ∈ GQ B.A, ∀ h₀ h₁, K h h₀ (γ * h₁) = K h h₀ h₁ := by
    subst hK; exact GlobalTheory.T.flatKernelPairing_rationalPoints_invariant D ψ σ J B s vL χ χz omz homz Φ₀ Φ hΦ₀ hΦ
  have hKq : ∀ h h₀ h₁, ‖K h h₀ h₁‖ ≤ |C| * 4 ^ a * (quotHeight J.W₀ h₀ * (quotHeight B.A h₁ * height B.V h)) ^ a := by
    intro h h₀ h₁
    obtain ⟨γ, hγ, e1⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight J.W₀ h₀
    obtain ⟨δ, hδ, e2⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight B.A h₁
    have k1 : K h h₀ h₁ = K h (γ * h₀) (δ * h₁) := by
      rw [(hKi h).2 δ hδ (γ * h₀) h₁, (hKi h).1 γ hγ h₀ h₁]
    rw [k1]
    have p1 := height_pos J.W₀ (γ * h₀)
    have p2 := height_pos B.A (δ * h₁)
    have p3 := height_pos B.V h
    have q0 := quotHeight_pos J.W₀ h₀
    have q1 := quotHeight_pos B.A h₁
    calc ‖K h (γ * h₀) (δ * h₁)‖ ≤ C * (height J.W₀ (γ * h₀) * height B.A (δ * h₁) * height B.V h) ^ a := hKp _ _ _
      _ ≤ |C| * ((2 * quotHeight J.W₀ h₀) * (2 * quotHeight B.A h₁) * height B.V h) ^ a :=
          mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (mul_pos (mul_pos p1 p2) p3).le
            (mul_le_mul_of_nonneg_right (mul_le_mul e1 e2 p2.le (by linarith)) p3.le) a)
            (pow_pos (mul_pos (mul_pos (by linarith) (by linarith)) p3) a).le (abs_nonneg C)
      _ = _ := by
          rw [show 2 * quotHeight J.W₀ h₀ * (2 * quotHeight B.A h₁) * height B.V h =
            4 * (quotHeight J.W₀ h₀ * (quotHeight B.A h₁ * height B.V h)) by ring, mul_pow]; ring
  obtain ⟨Cφ, hCφ⟩ := GlobalTheory.Grow.RapidDec.decay hφ a
  have hpt : ∀ h h₀ h₁, ‖φ h₀ * K h h₀ h₁‖ ≤ |Cφ| * (|C| * 4 ^ a) * (quotHeight B.A h₁ * height B.V h) ^ a := by
    intro h h₀ h₁
    rw [norm_mul]
    calc ‖φ h₀‖ * ‖K h h₀ h₁‖ ≤ ‖φ h₀‖ * (|C| * 4 ^ a * (quotHeight J.W₀ h₀ * (quotHeight B.A h₁ * height B.V h)) ^ a) :=
          mul_le_mul_of_nonneg_left (hKq h h₀ h₁) (norm_nonneg _)
      _ = (‖φ h₀‖ * quotHeight J.W₀ h₀ ^ a) * (|C| * 4 ^ a) * (quotHeight B.A h₁ * height B.V h) ^ a := by
          rw [mul_pow]; ring
      _ ≤ |Cφ| * (|C| * 4 ^ a) * (quotHeight B.A h₁ * height B.V h) ^ a :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((hCφ h₀).trans (le_abs_self _)) (by positivity))
            (pow_pos (mul_pos (quotHeight_pos B.A h₁) (height_pos B.V h)) a).le
  have hPeq : ∀ h h₁, handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ)) h₁ = ∫ h₀ in J.v0.𝓕, φ h₀ * K h h₀ h₁ ∂J.v0.μ := by
    subst hK; intro _ _; rfl
  refine ⟨⟨|Cφ| * (|C| * 4 ^ a) * (J.v0.μ J.v0.𝓕).toReal, a, fun h h₁ => ?_⟩, ?_⟩
  · rw [hPeq]
    have := norm_setIntegral_le_of_norm_le_const hfin fun h₀ _ => hpt h h₀ h₁
    refine this.trans (le_of_eq ?_)
    simp only [Measure.real]
    ring
  · have hmeas : ∀ q : GA D B.V × GA D B.A, AEStronglyMeasurable (fun h₀ => φ h₀ * K q.1 h₀ q.2) (J.v0.μ.restrict J.v0.𝓕) :=
      fun q => (hφ.continuous.mul (hKc.comp ((continuous_const.prodMk (continuous_id.prodMk continuous_const))))).aestronglyMeasurable
    have hc2 : Continuous fun q : GA D B.V × GA D B.A => (height B.A q.2 * height B.V q.1) ^ a :=
      (((continuous_height B.A).comp continuous_snd).mul ((continuous_height B.V).comp continuous_fst)).pow a
    refine (continuous_congr fun q : GA D B.V × GA D B.A => hPeq q.1 q.2).2 ?_
    refine continuous_iff_continuousAt.2 fun q₀ => ?_
    refine continuousAt_of_dominated (bound := fun _ => |Cφ| * (|C| * 4 ^ a) * ((height B.A q₀.2 * height B.V q₀.1) ^ a + 1))
      (.of_forall hmeas) ?_ (integrable_const _) ?_
    · filter_upwards [hc2.continuousAt.eventually (gt_mem_nhds (lt_add_one _))] with q hq
      refine .of_forall fun h₀ => (hpt q.1 h₀ q.2).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact (pow_le_pow_left₀ (mul_pos (quotHeight_pos B.A q.2) (height_pos B.V q.1)).le
        (mul_le_mul_of_nonneg_right (quotHeight_le_height B.A q.2) (height_pos B.V q.1).le) a).trans hq.le
    · exact .of_forall fun h₀ => (continuous_const.mul (hKc.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)))).continuousAt

theorem conclusion₂ : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (φ : GA D J.W₀ → ℂ) (G : GA D B.V → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), RapidDec J.W₀ φ → RapidDec B.V G → IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → (∀ h, AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 (besFun ψ 1 B.d B.o B.ζ (handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ))) (rTrans h G))) ∧ Continuous fun h => B.per ψ (handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ))) (rTrans h G) := by
  intro D ψ σ J B s vL χ χz omz homz φ G Φ₀ Φ hφ hG hΦ₀ hΦ
  have hψ := homz.std
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  haveI : ∀ V : HSp D, BorelSpace (GA D V) := fun V => ⟨rfl⟩
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B.A _ _ B.vA.haar B.vA.fund).ne
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 (by rw [B.vN.unit.2.2]; exact ENNReal.one_ne_top)
  obtain ⟨⟨C, a, hP⟩, hPc⟩ := GlobalTheory.JacMean.handP_law D ψ σ J B s vL χ χz omz homz φ Φ₀ Φ hφ hΦ₀ hΦ
  set P : GA D B.V → GA D B.A → ℂ := fun h h₁ => handP s vL omz φ Φ₀ (flFB s (s.om (1, h) Φ)) h₁ with hPdef
  obtain ⟨C1, a1, h1⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D B.V B.V₀ σ B.d
  obtain ⟨C2, a2, h2⟩ := GlobalTheory.T.unitaryQuotientHeight_orthogonalSum_comparable D B.V₀ B.A B.L B.o
  obtain ⟨C3, h3⟩ := (GlobalTheory.RTransDecay.rapidDec_rTrans D B.V G hG).2 (a1 * a2 * a)

  set bd : GA D B.V → ℝ := fun h => |C| * height B.V h ^ a * ((|C2| * |C1| ^ a2) ^ a * (|C3| * height B.V h ^ (a1 * a2 * a))) with hbd
  have hbound : ∀ h (h₁ : GA D B.A) (n : flagN B.d), ‖besFun ψ 1 B.d B.o B.ζ (P h) (rTrans h G) h₁ n‖ ≤ bd h := by
    intro h h₁ n
    have hg := h1 n.1 n.2 (B.o.emb (h₁, 1))
    have hq := (h2 h₁).1
    set g : GA D B.V := n.1 * embA B.d B.o h₁ with hgdef
    have hge : n.1 * B.d.emb0 (B.o.emb (h₁, 1)) = g := rfl
    rw [hge] at hg
    have q0 := quotHeight_pos B.V₀ (B.o.emb (h₁, 1))
    have qg := quotHeight_pos B.V g
    have qa := quotHeight_pos B.A h₁
    have ht := height_pos B.V h
    have hA : quotHeight B.A h₁ ≤ |C2| * |C1| ^ a2 * quotHeight B.V g ^ (a1 * a2) := by
      calc quotHeight B.A h₁ ≤ C2 * quotHeight B.V₀ (B.o.emb (h₁, 1)) ^ a2 := hq
        _ ≤ |C2| * (|C1| * quotHeight B.V g ^ a1) ^ a2 :=
            mul_le_mul (le_abs_self _) (pow_le_pow_left₀ q0.le (hg.1.trans
              (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_pos qg a1).le)) _) (pow_pos q0 a2).le (abs_nonneg _)
        _ = _ := by rw [mul_pow, ← pow_mul]; ring
    have hGg := h3 g h
    have hPb := hP h h₁
    have hnpsi : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) n.1‖ = 1 := hψ.1.2.1 _
    have e1 : ‖besFun ψ 1 B.d B.o B.ζ (P h) (rTrans h G) h₁ n‖ = ‖P h h₁‖ * ‖G (g * h)‖ := by
      simp only [besFun, rTrans, norm_mul, norm_star, hnpsi, mul_one]; rfl
    rw [e1]
    calc ‖P h h₁‖ * ‖G (g * h)‖ ≤ (|C| * (quotHeight B.A h₁ * height B.V h) ^ a) * ‖G (g * h)‖ :=
          mul_le_mul_of_nonneg_right (hPb.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
            (pow_pos (mul_pos qa ht) a).le)) (norm_nonneg _)
      _ ≤ (|C| * ((|C2| * |C1| ^ a2 * quotHeight B.V g ^ (a1 * a2)) * height B.V h) ^ a) * ‖G (g * h)‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos qa ht).le
            (mul_le_mul_of_nonneg_right hA ht.le) a) (abs_nonneg C)) (norm_nonneg _)
      _ = |C| * height B.V h ^ a * ((|C2| * |C1| ^ a2) ^ a * (‖G (g * h)‖ * quotHeight B.V g ^ (a1 * a2 * a))) := by
          rw [mul_pow, mul_pow, mul_pow, ← pow_mul]; ring
      _ ≤ bd h :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hGg.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
            (pow_pos ht _).le)) (by positivity)) (mul_nonneg (abs_nonneg _) (pow_pos ht a).le)
  have hcont : Continuous fun q : GA D B.V × (GA D B.A × flagN B.d) => besFun ψ 1 B.d B.o B.ζ (P q.1) (rTrans q.1 G) q.2.1 q.2.2 := by
    have hn : Continuous fun q : GA D B.V × (GA D B.A × flagN B.d) => (q.2.2 : GA D B.V) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    exact ((hPc.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).mul
      (hG.continuous.comp ((hn.mul (B.d.continuous_embed.comp (B.o.continuous_emb.comp ((continuous_fst.comp continuous_snd).prodMk continuous_const)))).mul continuous_fst))).mul
      (continuous_star.comp ((GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψ.1.1 1 _).comp hn))
  have hint : ∀ h, AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 (besFun ψ 1 B.d B.o B.ζ (P h) (rTrans h G)) := by
    intro h
    refine Integrable.of_bound ?_ (bd h) (.of_forall fun p => hbound h p.1 p.2)
    exact (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  refine ⟨hint, ?_⟩
  have heq : ∀ h, B.per ψ (P h) (rTrans h G) = ∫ p, Function.uncurry (besFun ψ 1 B.d B.o B.ζ (P h) (rTrans h G)) p
      ∂((B.vA.μ.restrict B.vA.𝓕).prod (B.vN.ν.restrict B.vN.𝓝)) := fun h => by
    rw [integral_prod _ (hint h)]; rfl
  refine (continuous_congr heq).2 ?_
  refine continuous_iff_continuousAt.2 fun h₀ => ?_
  have hbc : Continuous bd := by
    exact (continuous_const.mul ((continuous_height B.V).pow a)).mul (continuous_const.mul (continuous_const.mul ((continuous_height B.V).pow _)))
  refine continuousAt_of_dominated (bound := fun _ => bd h₀ + 1) ?_ ?_ (integrable_const _) ?_
  · exact .of_forall fun h => (hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [hbc.continuousAt.eventually (gt_mem_nhds (lt_add_one (bd h₀)))] with h hh
    exact .of_forall fun p => (hbound h p.1 p.2).trans hh.le
  · exact .of_forall fun p => (hcont.comp (continuous_id.prodMk continuous_const)).continuousAt

end GlobalTheory.JacMean
end
end
end
