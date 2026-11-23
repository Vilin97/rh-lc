module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatchedFlipThetaIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTranslatesKernelRouteSmallVertex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelLeftInvariantRationalUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPlacesPrimeToLevel
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleHypothesesOfStandingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedKernelLeThetaFunctionRouteBigVertexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicHeightBlockDiagonalEmbeddingLeMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelIntegrableOnUnitaryQuotientStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigThetaKernelIntegrable

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DominantTermNeZero

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.BigNZ
open Formalism.IndefR GlobalTheory.RowTest GlobalTheory.RowClaim
theorem large_term_nonzero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → Big fun ch => ∀ i j t, ∃ M : Vol ch.G, M.Is t ∧ ∃ a τ τ' n Φ,
    (∀ w ∈ locPl ch.G t, depthAt ch.G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) ∧ HasFlip ch.S.B t ch.rm i j n Φ τ τ' ∧
    ∃ g g₁, ∫ u in M.fd _, kerBig ch.W (tensT ch.W a τ) g g₁ u ∂M.ν _ ≠ 0 := by
  intro hP hK hLM _ _ _
  obtain ⟨CF0, hH⟩ := standing
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc i j t => ?_⟩
  exact exists_integral_ne_zero hP.strongApproxSU hK hLM hS.core.lev ch.W ch.S.B ch.rm t i j
    (hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc t)
end GlobalTheory.BigNZ
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.dominant_term_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → Big fun ch => ∀ i j t, ∃ M : Vol ch.G, M.Is t ∧ ∃ a τ τ' n Φ,
    (∀ w ∈ locPl ch.G t, depthAt ch.G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) ∧ HasFlip ch.S.B t ch.rm i j n Φ τ τ' ∧
    ∃ g g₁, ∫ u in M.fd _, kerBig ch.W (tensT ch.W a τ) g g₁ u ∂M.ν _ ≠ 0 := by
  first | exact @_root_.GlobalTheory.BigNZ.large_term_nonzero | exact _root_.GlobalTheory.BigNZ.large_term_nonzero | (intros; apply _root_.GlobalTheory.BigNZ.large_term_nonzero <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPlacesPrimeToLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.test_places_prime_to_level : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ w ∈ ch.G.pl.W0,
    ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  first | exact @GlobalTheory.PlacesPrime.places_prime_to_level | exact GlobalTheory.PlacesPrime.places_prime_to_level | (intros; apply GlobalTheory.PlacesPrime.places_prime_to_level <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallThetaKernelTranslateIntegrable

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallConv

theorem splitBound_ge : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ _ => 11 ≤ D.host.splitBound := by
  exact ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS _ _ _ => hS.size.2.1.eleven_le⟩⟩

theorem standing : Big fun ch => ∀ t, SquareStanding ch.G t := by
  obtain ⟨CF0, hH⟩ := splitBound_ge.and GlobalTheory.T.test_places_prime_to_level
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc t => ?_⟩
  obtain ⟨h11, hW⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc
  refine ⟨h11, fun w hw => ?_⟩
  classical
  unfold locPl at hw
  rcases Finset.mem_union.1 hw with hw | hw
  · exact hW w hw
  · intro hmem
    have h1 := (hS.core.lev.Q_off t w hw).1
    have h2 := hS.guard.2 t w hw
    push_cast at hmem h1 h2
    rcases w.isPrime.mem_or_mem hmem with h | h
    · exact h1 (Ideal.mul_mem_right _ _ h)
    · exact h2 (Ideal.mul_mem_left _ _ h)

end GlobalTheory.SmallConv

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SmallConvolutionExistsIntegrableTranslates

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.SmallConv
theorem small_convolution_exists_integrable_translates : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence →
    GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → Big fun ch => ∀ i j t (M : Vol ch.G), M.Is t → ∀ Θ Θ',
      IsMatched ch.S.B t ch.rm i j Θ Θ' → ∀ g g₁,
    ∃ z, zdeg z ≠ 0 ∧ IntegrableOn (translates z (kerSmall ch.W Θ' g g₁)) (M.fd _) (M.ν _) := by
  intro _ hK _ _ _
  obtain ⟨CF0, hH⟩ := standing
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  have hst := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc
  intro i j t M hM Θ Θ' hΘ g g₁
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  obtain ⟨e, Bs, Γ', X, om, om', h, hTr, hv⟩ := GlobalTheory.T.squareThetaTripleHypotheses_of_standing hL ch.W t i j (hst t) M hM
  obtain ⟨z, Φ, a, C₀, hz, hΦ, hid⟩ :=
    GlobalTheory.T.translatedKernel_le_thetaFunction_routeBigVertex hL ch.W ch.S.B ch.rm t i j M hM Θ Θ' hΘ g₁ e Bs Γ' X om om' h hTr hv
  have dec := (hK.1 D.host.F D.host.E D.sp.cm.sig Bs _ _ Γ' X om om' hTr).1
  obtain ⟨C, k, hC⟩ := (dec.2 Φ hΦ).1 0
  have hbd : ∀ u, ‖translates z (kerSmall ch.W Θ' g g₁) u‖ ≤
      |C₀| * |C| * (2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁) ^ k := by
    intro u
    obtain ⟨γ, hγ, hle⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight _ g
    have e1 : translates z (kerSmall ch.W Θ' g g₁) u = translates z (kerSmall ch.W Θ' (γ * g) g₁) u := by
      simp only [translates, GlobalTheory.ZConvLeft.kerSmall_rat_left hL ch.W ch.S.B ch.rm t i j Θ Θ' hΘ g₁ γ hγ]
    rw [e1]
    have h1 := hC (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))
    rw [pow_zero, mul_one] at h1
    have h2 := GlobalTheory.BlockHeight.ht_blkU_le _ _ e h.JWW (γ * g) g₁
    have h3 : (0 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) := NNReal.coe_nonneg _
    have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ≤
        2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁ :=
      h2.trans (mul_le_mul_of_nonneg_right hle (GlobalTheory.Grow.height_pos _ _).le)
    calc _ ≤ C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ := hid _ _
      _ ≤ |C₀| * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self C₀) (norm_nonneg _)
      _ ≤ |C₀| * (|C| * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h3 k)))
            (abs_nonneg C₀)
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h4 k) (mul_nonneg (abs_nonneg C₀) (abs_nonneg C))
  have hWl := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  haveI : IsFiniteMeasure ((M.ν (.grid i j)).restrict (M.fd (.grid i j))) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hWl.1 hWl.2).ne
  have hcont := GlobalTheory.SmallRoute.continuous_translates_kerSmall hL ch.W ch.S.B ch.rm t i j Θ Θ' hΘ g₁ z
  exact ⟨z, hz, Integrable.of_bound ((hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable) _
    (.of_forall hbd)⟩
end GlobalTheory.SmallConv
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.exists_integrable_translates_small_convolution : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → Big fun ch => ∀ i j t (M : Vol ch.G), M.Is t → ∀ Θ Θ', IsMatched ch.S.B t ch.rm i j Θ Θ' → ∀ g g₁,
    ∃ z, zdeg z ≠ 0 ∧ IntegrableOn (translates z (kerSmall ch.W Θ' g g₁)) (M.fd _) (M.ν _) := by
  first | exact @_root_.GlobalTheory.SmallConv.small_convolution_exists_integrable_translates | exact _root_.GlobalTheory.SmallConv.small_convolution_exists_integrable_translates | (intros; apply _root_.GlobalTheory.SmallConv.small_convolution_exists_integrable_translates <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SquareConvolutionLargeBound

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.SquareConv
theorem square_convolution_large_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → Big fun ch => ∀ i j t (M : Vol ch.G), M.Is t → ∀ Θ Θ', IsMatched ch.S.B t ch.rm i j Θ Θ' → ∀ g g₁,
    IntegrableOn (kerBig ch.W Θ g g₁) (M.fd _) (M.ν _) := by
  intro _ _ hWC _ _
  refine ⟨0, fun ε CF _ => ⟨(12:ℝ) ^ (5/ε), fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩⟩
  intro i j t M hM Θ Θ' hΘ g g₁
  have hst : SquareStanding ch.G t := standing hS (splitBound_ge he hx) ch.G t
  exact GlobalTheory.T.bigRoute_kernel_integrableOn_unitary_quotient hWC hS.core.lev ch.W ch.S.B ch.rm t i j (GlobalTheory.T.squareThetaTripleHypotheses_of_standing hS.core.lev ch.W t i j hst) M hM Θ Θ' hΘ g₁ g
end GlobalTheory.SquareConv
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.square_convolution_estimate : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → Big fun ch => ∀ i j t (M : Vol ch.G), M.Is t → ∀ Θ Θ', IsMatched ch.S.B t ch.rm i j Θ Θ' → ∀ g g₁,
    IntegrableOn (kerBig ch.W Θ g g₁) (M.fd _) (M.ν _) := by
  first | exact @_root_.GlobalTheory.SquareConv.square_convolution_large_bound | exact _root_.GlobalTheory.SquareConv.square_convolution_large_bound | (intros; apply _root_.GlobalTheory.SquareConv.square_convolution_large_bound <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConstK

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ConstNZ
theorem constK_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.RowClaim.ConstK := by
  intro h1 h2 hLM h3 h4 h5
  obtain ⟨CF0, hH⟩ := ((_root_.GlobalTheory.T.square_convolution_estimate h1 h2 h3 h4 h5).and (_root_.GlobalTheory.T.exists_integrable_translates_small_convolution h1 h2 h3 h4 h5)).and (_root_.GlobalTheory.T.dominant_term_ne_zero h1 h2 hLM h3 h4 h5)
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  obtain ⟨⟨hb, hs⟩, hn⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc
  intro i j t
  obtain ⟨M, hM, a, τ, τ', n, Φ, hnat, hfl, g, g₁, hI⟩ := hn i j t
  obtain ⟨b', hb'⟩ := ch.rm.onto_big i j (toTens a)
  obtain ⟨b, rfl⟩ := toTens_surjective b'
  have hΘ : IsMatched ch.S.B t ch.rm i j (tensT ch.W a τ) (tensT ch.W b τ') := ⟨a, b, τ, τ', n, Φ, hb', hnat, hfl, rfl, rfl⟩
  obtain ⟨z, hz, hzi⟩ := hs i j t M hM _ _ hΘ g g₁
  have hconv : SquareConv ch.W M _ _ z g g₁ := ⟨hb i j t M hM _ _ hΘ g g₁, hzi⟩
  have hc := hch.const i j t M hM _ _ hΘ z g g₁ hconv
  have hL : zdeg z * ∫ u in M.fd _, kerBig ch.W (tensT ch.W a τ) g g₁ u ∂M.ν _ ≠ 0 := mul_ne_zero hz hI
  rw [hc] at hL
  exact ⟨⟨M, hM, _, _, hΘ, z, g, g₁, hconv, right_ne_zero_of_mul hL⟩, left_ne_zero_of_mul hL⟩
end GlobalTheory.ConstNZ
end
end
end
end
