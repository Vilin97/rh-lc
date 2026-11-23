module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeilStatement
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfiniteStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelSetCompactReductionStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsoluteThetaIntegralLeContinuousSeminorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbits
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WittIdxOfParallelSig
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FirstClauseRankZero

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeIntegralZeroVarsLtTop

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelCone

theorem cone_integral_zero_vars_lt_top :
    ∀ (F : Type) [Field F] [NumberField F] (n d : ℕ) (c : ℝ),
      ∫⁻ t in GlobalTheory.SiegelSet.cone 0 c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
        ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  intro F _ _ n d c
  have h : ∀ t : Fin 0 → ℝ, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) = 1 := by
    intro t
    simp [GlobalTheory.SiegelSet.modulus]
  simp_rw [h]
  rw [setLIntegral_const, one_mul]
  exact measure_lt_top _ _

end GlobalTheory.CompanionTheory.SiegelCone
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLeFundamentalSet

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilConv

theorem absThetaInt_le_of_meets_orbits (D : D7) (V : HSp D) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) {n : ℕ}
    (φ : Mx D V.rank n → ℂ) (hφ : Continuous φ) (S : Set (GA D V)) (hS : MeasurableSet S)
    (hcov : ∀ g, ∃ γ ∈ GQ V, γ * g ∈ S) : absThetaInt V ν φ ≤ ∫⁻ g in S, absTheta V φ g ∂ν := by
  have hinv := leftInv_absTheta V φ
  have hfd : IsFundamentalDomain (GQ V) (stdDom (GQ V)) ν := isFundamentalDomain_stdDom _ ν
  have e : absThetaInt V ν φ = ∫⁻ g in stdDom (GQ V), absTheta V φ g ∂ν := by
    unfold absThetaInt
    show ∫⁻ q, descend (GQ V) (absTheta V φ) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν = _
    rw [GlobalTheory.AutomorphicL2Unitary.lintegral_quotMeasure hfd]
    exact lintegral_congr fun g => congrFun hinv.lift_descend g
  rw [e]
  exact GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits (GQ V) ν hfd hS hcov (GlobalTheory.AbsThetaSemi.measurable_absTheta V hφ) hinv

end GlobalTheory.CompanionTheory.WeilConv

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLeFundamentalSetStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_integral_le_fundamental_set : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ {n : ℕ} (φ : Mx D V.rank n → ℂ), Continuous φ → ∀ S : Set (GA D V), MeasurableSet S → (∀ g, ∃ γ ∈ GQ V, γ * g ∈ S) → absThetaInt V ν φ ≤ ∫⁻ g in S, absTheta V φ g ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.WeilConv.absThetaInt_le_of_meets_orbits | exact GlobalTheory.CompanionTheory.WeilConv.absThetaInt_le_of_meets_orbits | (intros; apply GlobalTheory.CompanionTheory.WeilConv.absThetaInt_le_of_meets_orbits <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittFrameRankLeWittIndex

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WittFrame

open Matrix

theorem length_le_wittIdx (D : D7) (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf) : r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  have hc : ∀ {a : ℕ} (A : Matrix (Fin V.rank) (Fin a) D.host.E),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A = Aᴴ := by
    intro a A
    exact Matrix.ext fun i j => rfl
  have hxx : Xfᴴ * V.gram * Xf = 0 := by rw [← hc]; exact hW.xx
  have hxy : Xfᴴ * V.gram * Yf = 1 := by rw [← hc]; exact hW.xy
  have hG : V.gramᴴ = V.gram := by
    refine Matrix.ext fun a b => ?_
    exact V.herm.eq _ _
  have hyx : Yfᴴ * V.gram * Xf = 1 := by
    have h := congrArg conjTranspose hxy
    simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using h
  let f : (Fin r → D.host.E) →ₗ[D.host.E] V.V := V.frame.equivFun.symm.toLinearMap.comp Xf.mulVecLin
  have hf : Function.Injective f := by
    refine V.frame.equivFun.symm.injective.comp (g := V.frame.equivFun.symm) (f := Xf.mulVec) fun v w hvw => ?_
    have := congrArg (Yfᴴ * V.gram).mulVec hvw
    simpa [mulVec_mulVec, hyx] using this
  refine le_csSup (GlobalTheory.SiegelFormula.Model.bddAbove_witt V) ⟨LinearMap.range f, by simpa using LinearMap.finrank_range_of_inj hf, ?_⟩
  rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
  change V.hT (V.frame.equivFun.symm (Xf *ᵥ v)) (V.frame.equivFun.symm (Xf *ᵥ w)) = 0
  rw [GlobalTheory.ParallelWitt.form_eq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hxx]
  simp

end GlobalTheory.CompanionTheory.WittFrame
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittFrameRankLeWittIndexStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.witt_frame_rank_le_witt_index : ∀ (D : D7) (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  first | exact @GlobalTheory.CompanionTheory.WittFrame.length_le_wittIdx | exact GlobalTheory.CompanionTheory.WittFrame.length_le_wittIdx | (intros; apply GlobalTheory.CompanionTheory.WittFrame.length_le_wittIdx <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaConvergenceOfSiegelSet

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilTheta

theorem weilThetaConvergence_of_siegelSet (hRT : GlobalTheory.Published.SiegelSetUnitary) : GlobalTheory.Published.WeilThetaConvergence := by
  intro D n V _hn hV θ hθ ν hν Φ
  obtain ⟨hcontΦ, -⟩ := GlobalTheory.T.schwartz_bound_finite_infinite D θ hθ V.rank n Φ.1 Φ.2
  obtain ⟨r, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame (GlobalTheory.AdelicU.isCMExt_host D) (isHermND_gram V)
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hRT D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) V.rank V.gram (isHermND_gram V) r Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas ν hν
  obtain ⟨C, hC⟩ := GlobalTheory.T.siegel_set_compact_reduction D θ hθ V n Φ.1 Φ.2 Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hconj
  set S := GlobalTheory.SiegelSet.siegelSet D.sp.cm.sig V.gram Xf Yf Ω c K with hSdef
  have hSm : MeasurableSet S := hcl.measurableSet
  have hScov : ∀ g, ∃ γ ∈ GQ V, γ * g ∈ S := fun g => by
    obtain ⟨γ, hγ, s, hs, e⟩ := hcov g
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    rw [e, inv_mul_cancel_left]
    exact hs
  have hI : ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
      ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
        ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹) < ⊤ := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      exact GlobalTheory.CompanionTheory.SiegelCone.cone_integral_zero_vars_lt_top D.host.F V.rank (2 * n) c
    · have hw := GlobalTheory.T.witt_frame_rank_le_witt_index D V Xf Yf hW
      have h2 : n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank := hV.resolve_left (by omega)
      exact GlobalTheory.T.lintegral_siegelCone_inv_modulus_lt_top_weil D.host.F V.rank r (2 * n) hc (by omega)
  calc absThetaInt V ν Φ.1 ≤ ∫⁻ g in S, absTheta V Φ.1 g ∂ν :=
        GlobalTheory.T.theta_integral_le_fundamental_set D V ν hν Φ.1 hcontΦ S hSm hScov
    _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
          ENNReal.ofReal (max C 0 * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
            ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹) := by
        refine hC₁ (absTheta V Φ.1) _ (by fun_prop) fun p hp t ht a ha k hk => ?_
        have ht0 : ∀ i, 0 < t i := ht.1
        have hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n)) :=
          Finset.prod_nonneg fun i _ => pow_nonneg (ht0 i).le _
        refine (hC p hp t ht a ha k hk).trans (ENNReal.ofReal_le_ofReal ?_)
        gcongr
        exact le_max_left _ _
    _ = C₁ * (ENNReal.ofReal (max C 0) * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
          ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
            ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_congr fun t => by rw [ENNReal.ofReal_mul (le_max_right _ _), mul_assoc]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI)

end GlobalTheory.CompanionTheory.WeilTheta

end
end
end
