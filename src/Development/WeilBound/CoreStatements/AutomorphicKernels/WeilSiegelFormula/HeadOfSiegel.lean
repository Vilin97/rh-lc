module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.PullSchLI
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilEisensteinSiegelConvergence
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisCells
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfHermEBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLatticeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinCoefficientsSummable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLocallySummableBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackSchwartzLinearIndependent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOfTsumEnormLtTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaConvergenceOfSiegelSet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilSiegelFormulaOfChaptersLI
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
public import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.SiegelND

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEisensteinSiegelConvergence

section

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec)

namespace GlobalTheory.WeilEisConv

theorem weilEisensteinSiegelConvergence : GlobalTheory.Published.WeilEisensteinSiegelConvergence := by
  intro D n V hn hV ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω Φ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, _, _, hκ, hW, hT⟩ :=
    GlobalTheory.StdUnn.SchDatum.exists_datum D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hstd θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have key : ∀ g : G D n, (ω g Φ).1 0 = swSec A V omh μ 𝓕 f (κ.symm g) := by
    intro g
    have h := hT (κ.symm g) f hf Φ hfΦ.symm
    have e : κ (κ.symm g) = g := κ.apply_symm_apply g
    rw [e] at h
    exact (congrFun h 0).trans (mixS_dblDec_zero A V ψ₀ μ 𝓕 _ 0)
  obtain ⟨a, ha⟩ := exists_isMaj A
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  obtain ⟨C, hC, h₁⟩ := GlobalTheory.SWAbsGrowth.norm_swSec_le hW hμ hf a ha
  have hc := GlobalTheory.AdelicU.isCMExt_host D
  have hs : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hc.2.2.2, hc.2.2.2, star_star])
  have hP := GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P D A μ' hsk κ hκ
  have hG := GlobalTheory.StdUnn.chart_mem_GF_iff D A μ' hsk κ hκ
  have hb : (A.rank : ℝ) < (V.rank : ℝ) / 2 := by
    have : (2 * n : ℝ) < V.rank := by exact_mod_cast hV
    change (n : ℝ) < _
    linarith
  have hsum : Summable fun q : GlobalTheory.Eis.Cosets (P D n) (GF D n) =>
      (hgt A a (κ.symm (Subtype.val (q.out : GF D n))) : ℝ) ^ ((V.rank : ℝ) / 2) := by
    refine GlobalTheory.Eis.Conv.summable_hgt hc hs (GlobalTheory.Doubling.gram_hdbl A) (GlobalTheory.Doubling.isHermND_gram A)
      (GlobalTheory.Doubling.isCompact_Khat A a) hI (γ := fun q : GlobalTheory.Eis.Cosets (P D n) (GF D n) => κ.symm (Subtype.val (q.out : GF D n)))
      (fun q => (hG _).2 (by rw [MulEquiv.apply_symm_apply]; exact q.out.2)) (fun q q' h => ?_) hb
    have h' := (hP _).1 h
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
    rw [← q.out_eq, ← q'.out_eq]
    exact GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨q'.out * q.out⁻¹, h'⟩, inv_mul_cancel_right _ _⟩
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_) (hsum.mul_left C)
  simp only [GlobalTheory.Eis.term, mul_one]
  rw [key]
  exact h₁ _

end GlobalTheory.WeilEisConv
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellOfPoissonSiegel

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilSiegel

theorem bigCell_of_poisson_siegel :
    (∀ (D : Formalism.BasicNotions.D7) (r : ℕ), ∃ (lam : Measure (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)) (𝓖 : Set (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)), PositivityTheory.GramSchwartzFunctions.BC.IsCovolOneH lam 𝓖) → PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm → (∀ (D : Formalism.BasicNotions.D7) (r : ℕ) (V : Formalism.BasicNotions.TH.HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ → HasSum (fun β : PositivityTheory.GramSchwartzFunctions.HermE D r => PositivityTheory.GramSchwartzFunctions.BC.IfrB V ν φ β) (PositivityTheory.GramSchwartzFunctions.Ifr V ν φ)) → PositivityTheory.GramSchwartzFunctions.BC.SiegelND → PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg → PositivityTheory.GramSchwartzFunctions.BigCell := by
  intro hlam hP hG hND hDeg D r V h2r ψ hψ θ hθ μ 𝓕 h𝓕 ν hν φ hφ habs hsum
  obtain ⟨lam, 𝓖, hlg⟩ := hlam D r
  have hyp : Hyp D r V ψ θ μ lam ν φ :=
    ⟨h2r, hψ, hθ, ⟨𝓕, h𝓕⟩, ⟨𝓖, hlg⟩, hν, hφ, habs⟩
  have h1 := hP D r V ψ θ μ lam ν φ hyp hsum
  have h2 := hG D r V θ hθ ν hν φ hφ habs
  have h3 : (fun β : HermE D r => IfrB V ν φ β) = fun β : HermE D r => W ψ V μ lam φ β := by
    funext β
    by_cases hβ : β.1.det = 0
    · exact hDeg D r V ψ θ μ lam ν φ hyp β hβ
    · exact hND D r V ψ θ μ lam ν φ hyp β hβ
  rw [h3] at h2
  have h4 := h1.unique h2
  have h5 := hsum.hasSum
  rwa [h4] at h5

end GlobalTheory.CompanionTheory.WeilSiegel
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinCoefficientsSummableStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.siegel_eisenstein_coefficients_summable : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)) (φ : Mx D V.rank r → ℂ), 2 * r < V.rank → IsCharAF D.host.F ψ → IsInfFam θ → (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → IsCovolOneH lam 𝓖 → φ ∈ schwartzA θ V.rank r → Summable (fun β : HermE D r => W ψ V μ lam φ β) := by
  first | exact @GlobalTheory.CompanionTheory.WSum.summable_W_of_two_mul_lt_rank | exact GlobalTheory.CompanionTheory.WSum.summable_W_of_two_mul_lt_rank | (intros; apply GlobalTheory.CompanionTheory.WSum.summable_W_of_two_mul_lt_rank <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonHermMain

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermPoisson

theorem poissonHerm_main : PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm := by
  intro D r V ψ θ μ lam ν φ hH hJ
  obtain ⟨hm, hψ, hθ, hμ, ⟨𝓖, hlam⟩, -, hφ, -⟩ := hH
  have hc := GlobalTheory.T.theta_integral_continuous D r V ψ θ μ φ hψ hθ hμ hφ
  have hu := GlobalTheory.T.theta_integral_locally_summable_bound D r V ψ θ μ φ hm hψ hθ hμ hφ
  have hW := GlobalTheory.T.siegel_eisenstein_coefficients_summable D r V ψ θ μ lam 𝓖 φ hm hψ hθ hμ hlam hφ
  obtain ⟨-, hP⟩ := GlobalTheory.T.poisson_summation_hermitian_lattice D r ψ hψ lam 𝓖 hlam _ hc hu
  have hgW : ∀ β : HermE D r, (fun t : ratHerm D r => ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) ((hermEquiv (D := D) (r := r)) β) = W ψ V μ lam φ β :=
    fun β => (W_eq ψ V μ lam φ β).symm
  have hS : Summable (fun t : ratHerm D r => ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) := by
    refine (hermEquiv (D := D) (r := r)).summable_iff.1 ?_
    exact hW.congr fun β => (hgW β).symm
  have e := hP hS
  have hsumJ : ∑' b : HermE D r, J ψ V μ φ b = ∑' c : ratHerm D r, Jt ψ V μ φ c.1 :=
    (hermEquiv (D := D) (r := r)).tsum_eq (fun c => Jt ψ V μ φ c.1)
  have hsumW : ∑' β : HermE D r, W ψ V μ lam φ β = ∑' t : ratHerm D r, ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam := by
    rw [← (hermEquiv (D := D) (r := r)).tsum_eq]
    exact tsum_congr fun β => (hgW β).symm
  rw [hsumJ, e, ← hsumW]
  exact hW.hasSum

end GlobalTheory.CompanionTheory.HermPoisson
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.HeadOfSiegel

section

@[expose] public section

namespace PositivityTheory.PfWsf.Top

theorem pull : PositivityTheory.GramSchwartzFunctions.PullSchLI := GlobalTheory.CompanionTheory.PullSch.pullSchLI
theorem orb : PositivityTheory.GramSchwartzFunctions.ThetaOrbits := GlobalTheory.CompanionTheory.ThetaOrbit.thetaOrbits

theorem head_of_two (hE : PositivityTheory.GramSchwartzFunctions.EisCells) (hB : PositivityTheory.GramSchwartzFunctions.BigCell) : GlobalTheory.Published.WeilSiegelFormula :=
  GlobalTheory.CompanionTheory.SiegelAssemblyLI.weilSiegelFormula_of_chapters_LI
    (GlobalTheory.CompanionTheory.WeilTheta.weilThetaConvergence_of_siegelSet GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary)
    GlobalTheory.WeilEisConv.weilEisensteinSiegelConvergence pull hE orb hB

theorem big_of_three (h1 : PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm) (h2 : PositivityTheory.GramSchwartzFunctions.BC.SiegelND) (h3 : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg) :
    PositivityTheory.GramSchwartzFunctions.BigCell :=
  GlobalTheory.CompanionTheory.WeilSiegel.bigCell_of_poisson_siegel GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH h1 GlobalTheory.CompanionTheory.SplitGram.hasSum_IfrB h2 h3

end PositivityTheory.PfWsf.Top

namespace PositivityTheory.PfWsf.Top

end PositivityTheory.PfWsf.Top

namespace PositivityTheory.PfWsf.Top

theorem head_of_three (h4 : PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm) (h5 : PositivityTheory.GramSchwartzFunctions.BC.SiegelND)
    (h6 : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg) : GlobalTheory.Published.WeilSiegelFormula :=
  head_of_two GlobalTheory.CompanionTheory.EisCellsChapter.eisCells (big_of_three h4 h5 h6)
end PositivityTheory.PfWsf.Top

namespace PositivityTheory.PfWsf.Top

theorem head_of_siegel (h5 : PositivityTheory.GramSchwartzFunctions.BC.SiegelND) (h6 : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg) : GlobalTheory.Published.WeilSiegelFormula :=
  head_of_three GlobalTheory.CompanionTheory.HermPoisson.poissonHerm_main h5 h6
end PositivityTheory.PfWsf.Top

namespace PositivityTheory.PfWsf.Top

theorem head_of_deg (h6 : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg) : GlobalTheory.Published.WeilSiegelFormula :=
  head_of_siegel PositivityTheory.PfWsf.Hand.Merge.siegelND h6
end PositivityTheory.PfWsf.Top
end
end
