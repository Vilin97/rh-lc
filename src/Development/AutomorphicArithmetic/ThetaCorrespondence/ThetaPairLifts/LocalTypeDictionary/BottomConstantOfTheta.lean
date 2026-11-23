module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomConstantOfTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationProportionalityRatioLeBottomPairsStatement
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomConstantTransferAlongTower
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomTripleIntegralEqConstMulLocal
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOneStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsBottomBasisChange
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomFormulaLargeRank
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomFormulaSmallRank
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomMinorMatching

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantAt

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotRatio

theorem gBig_of_two {Q₁ Q₂ Q₃ : GlobalTheory.SqTop.GP} (h₁ : GlobalTheory.SqTop.GBig Q₁) (h₂ : GlobalTheory.SqTop.GBig Q₂)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b) : GlobalTheory.SqTop.GBig Q₃ := by
  obtain ⟨a₁, h₁⟩ := h₁
  obtain ⟨a₂, h₂⟩ := h₂
  refine ⟨max a₁ a₂, fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, h₁⟩ := h₁ ε CF (le_of_max_le_left hCF)
  obtain ⟨C₂, x₂, h₂⟩ := h₂ ε CF (le_of_max_le_right hCF)
  exact ⟨max C₁ C₂, max x₁ x₂, fun C hC D large₂ he hx r T Lc μ hLc G =>
    H G μ C _ _ (h₁ C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) r T Lc μ hLc G)
      (h₂ C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) r T Lc μ hLc G)⟩

end GlobalTheory.BotRatio
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomConstantRatioEqLocalFactorRatio

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BotRatio
theorem bottom_theta_constant_ratio_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall → GlobalTheory.SqTop.LNe →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ),
      IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      c0 t ≠ 0 ∧ c0 μ₀ ≠ 0 ∧ ∃ γ : D.what₂.LL, D.what₂.embLL γ * c0 μ₀ = c0 t := by
  intro hPr hK hM _ _ hL
  refine GlobalTheory.BotRatio.gBig_of_two (_root_.GlobalTheory.T.bottom_triple_integral_eq_const_mul_local hPr hK hM hL) (_root_.GlobalTheory.T.witt_tower_bottom_constant_transfer hPr hK hM) fun {D T Lc sc} G μ₀ C x b ha hb => ?_
  intro W S hψ hN i j t A A' WW X c0 hX hc
  obtain ⟨B, B', WW₁, Y, hY, hS⟩ := hN.bottom i j ⟨A, A', WW, X, hX⟩
  have hr := hS.rationalSums (fun t => (hY.integrable t).1) fun t => (hY.integrable t).2
  obtain ⟨u, hu⟩ := hb W S hψ hN i j B B' WW₁ Y A A' WW X c0 hY hX hc
  obtain ⟨lam, hl⟩ := ha W hψ i j B B' WW₁ Y hY
  have hR := GlobalTheory.ConstRatio.ratIn_of_definite hY.is (GlobalTheory.ConstRatio.posDef_of_std hY.std)
    (GlobalTheory.ConstRatio.posDef_of_std hY.std') (GlobalTheory.ConstRatio.posDef_of_std hY.stdW) hl hr μ₀
  obtain ⟨κ, hκ, e⟩ := hl.eq_mul hu
  have h1 : GlobalTheory.ConstRatio.RatIn D.what₂.embLL μ₀ fun t => D.what₂.embLL (u t) * c0 t := by
    rw [show (fun t => D.what₂.embLL (u t) * c0 t) = fun t => κ * lam t from funext e]
    exact (GlobalTheory.ConstRatio.ratIn_const hκ).mul hR
  have h2 : GlobalTheory.ConstRatio.RatIn D.what₂.embLL μ₀ c0 :=
    GlobalTheory.ConstRatio.RatIn.of_mul h1 (GlobalTheory.ConstRatio.ratIn_of_unit fun t => ⟨u t, rfl⟩) fun t => mul_comm _ _
  obtain ⟨h3, y, hy⟩ := h2 t
  refine ⟨h3, (h2 μ₀).1, y, ?_⟩
  rw [hy, div_mul_cancel₀ _ (h2 μ₀).1]
end GlobalTheory.BotRatio
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bottom_constant_ratio_eq_local_factor_ratio : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall → GlobalTheory.SqTop.LNe →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ),
      IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      c0 t ≠ 0 ∧ c0 μ₀ ≠ 0 ∧ ∃ γ : D.what₂.LL, D.what₂.embLL γ * c0 μ₀ = c0 t := by
  first | exact @_root_.GlobalTheory.BotRatio.bottom_theta_constant_ratio_eq | exact _root_.GlobalTheory.BotRatio.bottom_theta_constant_ratio_eq | (intros; apply _root_.GlobalTheory.BotRatio.bottom_theta_constant_ratio_eq <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantNormalized

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.BotFormula.root_unit {ζ : ℂ} {n : ℕ} (hn : 0 < n) (h : ζ ^ n = 1) :
    ζ ≠ 0 ∧ ζ ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam ζ‖ = 1 := by
  have hQ : ζ ∈ Qbar := by
    have : IsIntegral ℚ ζ := IsIntegral.of_pow hn (h ▸ isIntegral_one)
    exact mem_algebraicClosure_iff.2 this.isAlgebraic
  refine ⟨fun e => by simp [e, hn.ne'] at h, hQ, fun p _ lam => ?_⟩
  have h2 : (⟨ζ, hQ⟩ : Qbar) ^ n = 1 := Subtype.ext (by simpa using h)
  have h3 : lamC lam ζ = lam ⟨ζ, hQ⟩ := by simp [lamC, hQ]
  have h4 : ‖lam ⟨ζ, hQ⟩‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, h2, map_one, norm_one]
  rw [h3]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h4
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisInnerProductFormulaFirstOccurrence

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.BotFormula.bottom_theta_petersson_norm_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ),
      IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ) (δ t0 : ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ (u : ℂ) (M : Tup D P.a P.d P.n → Tup D P'.a P'.d P'.n → ℤ) (M' : Tup D P'.a P'.d P'.n → Tup D P.a P.d P.n → ℤ),
          u ≠ 0 ∧ u ∈ Qbar ∧
          (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (hd : P'.d = P.d) (h : GA D P.d),
            (∀ T, starRingEnd ℂ (P.coord h T) = κ * u * c0 s * ∑ T', (M T T' : ℂ) * P'.coord (hd ▸ h) T') ∧
            ∀ T', P'.coord (hd ▸ h) T' * (κ * u * c0 s) = ∑ T, (M' T' T : ℂ) * starRingEnd ℂ (P.coord h T) := by
  intro hPr hK hM hI hB
  obtain ⟨cA, hA⟩ := _root_.GlobalTheory.T.theta_bottom_formula_large hPr hK hM hI hB
  obtain ⟨cB, hB'⟩ := _root_.GlobalTheory.T.theta_bottom_formula_small hPr hK hM hI hB
  obtain ⟨cC, hC⟩ := _root_.GlobalTheory.T.rallis_bottom_minor_matching hPr hK hM hI hB
  obtain ⟨cD, hD⟩ := _root_.GlobalTheory.T.exists_bottom_basis_change hPr
  refine ⟨max (max (max cA cB) cC) cD, fun ε CF hCF => ?_⟩
  simp only [max_le_iff] at hCF
  obtain ⟨CA, xA, hA⟩ := hA ε CF hCF.1.1.1
  obtain ⟨CB, xB, hB'⟩ := hB' ε CF hCF.1.1.2
  obtain ⟨CC, xC, hC⟩ := hC ε CF hCF.1.2
  obtain ⟨CD, xD, hD⟩ := hD ε CF hCF.2
  refine ⟨max (max (max CA CB) CC) CD, max (max (max xA xB) xC) xD, fun C hC0 D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  simp only [max_le_iff] at hC0 hx
  have hA := hA C hC0.1.1.1 D large₂ he hx.1.1.1 hR T Lc μ₀ hL G
  have hB' := hB' C hC0.1.1.2 D large₂ he hx.1.1.2 hR T Lc μ₀ hL G
  have hC := hC C hC0.1.2 D large₂ he hx.1.2 hR T Lc μ₀ hL G
  have hD := hD C hC0.2 D large₂ he hx.2 hR T Lc μ₀ hL G
  intro W S hψ _ i j A A' WW X₀ c0 δ t0 hX₀ hc₀
  obtain ⟨X, ζ, hX, hβ, hζ, hc⟩ := hD W hψ i j A A' WW X₀ c0 hX₀ hc₀
  obtain ⟨Ω, hΩ, HA⟩ := hA W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨Ω', hΩ', HB⟩ := hB' W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨κ₀, hκ₀, HC⟩ := hC W hψ i j A A' WW X _ hX hc
  refine ⟨Ω * κ₀ * Ω', mul_ne_zero (mul_ne_zero hΩ hκ₀) hΩ', fun s Q P P' hP => ?_⟩
  obtain ⟨uA, huA, huAQ, huAu, HA⟩ := HA s Q P P' hP
  obtain ⟨uB, huB, huBQ, huBu, HB⟩ := HB s Q P P' hP
  obtain ⟨n, hn, hζn⟩ := hζ s
  obtain ⟨hz0, hzQ, hzu⟩ := GlobalTheory.BotFormula.root_unit hn hζn
  have ea : P.a = A.rank := hP.rank.1.trans hX.rank.symm
  have ea' : P'.a = A'.rank := hP.rank.2.1.trans hX.rank'.symm
  have ed : P.d = WW.rank := by rw [hP.rank.2.2.1, ← hX.is.rank, hX.rank, hX.rank']
  have ed' : P'.d = WW.rank := hP.rank.2.2.2.trans ed
  obtain ⟨M, M', hMM, HC⟩ := HC s Q δ t0 P P' hP ea ea' ed ed'
  refine ⟨uA * uB * ζ s, M, M', mul_ne_zero (mul_ne_zero huA huB) hz0, Qbar.mul_mem (Qbar.mul_mem huAQ huBQ) hzQ, fun p _ hp lam => ?_, fun hd h => ?_⟩
  · rw [GlobalTheory.BotFormula.lamC_mul lam (Qbar.mul_mem huAQ huBQ) hzQ, GlobalTheory.BotFormula.lamC_mul lam huAQ huBQ, norm_mul, norm_mul,
      huAu p hp lam, huBu p hp lam, hzu p lam, one_mul, one_mul]
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_finiteAdelicPoint_unitaryGroup_gramOne WW hX.stdW.1 h ed.symm
  have hg' := hg.cast hd
  have key : ∀ T, starRingEnd ℂ (P.coord h T) =
      Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * ∑ T', (M T T' : ℂ) * P'.coord (hd ▸ h) T' := by
    intro T
    rw [HA ea ed h g hg T, HC g T]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T' _ => ?_
    rw [HB ea' ed' (hd ▸ h) g hg' T']
    ring
  refine ⟨key, fun T' => ?_⟩
  simp_rw [key, Finset.mul_sum]
  rw [Finset.sum_comm]
  have e1 : ∀ T'' T, (M' T' T : ℂ) * (Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * ((M T T'' : ℂ) * P'.coord (hd ▸ h) T'')) =
      ((M' T' T * M T T'' : ℤ) : ℂ) * (Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * P'.coord (hd ▸ h) T'') := by
    intro T'' T; push_cast; ring
  simp_rw [e1, ← Finset.sum_mul, ← Int.cast_sum, hMM]
  simp [mul_comm]
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rallis_inner_product_formula_first_occurrence : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ),
      IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ) (δ t0 : ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ (u : ℂ) (M : Tup D P.a P.d P.n → Tup D P'.a P'.d P'.n → ℤ) (M' : Tup D P'.a P'.d P'.n → Tup D P.a P.d P.n → ℤ),
          u ≠ 0 ∧ u ∈ Qbar ∧
          (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (hd : P'.d = P.d) (h : GA D P.d),
            (∀ T, starRingEnd ℂ (P.coord h T) = κ * u * c0 s * ∑ T', (M T T' : ℂ) * P'.coord (hd ▸ h) T') ∧
            ∀ T', P'.coord (hd ▸ h) T' * (κ * u * c0 s) = ∑ T, (M' T' T : ℂ) * starRingEnd ℂ (P.coord h T) := by
  first | exact @_root_.GlobalTheory.BotFormula.bottom_theta_petersson_norm_formula | exact _root_.GlobalTheory.BotFormula.bottom_theta_petersson_norm_formula | (intros; apply _root_.GlobalTheory.BotFormula.bottom_theta_petersson_norm_formula <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomConstantOfTheta

section

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SqTop.BotConstPf
end GlobalTheory.SqTop.BotConstPf
namespace GlobalTheory.SqTop
open BotConstPf
theorem botConst_of_inputs_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → BotSmall → LNe → BotConst := by
  intro hPr hK hM hInp hS hL
  refine gBig_imp (Model.gBig_and (Model.gBig_and (_root_.GlobalTheory.T.bottom_constant_ratio_eq_local_factor_ratio hPr hK hM hInp hS hL) (_root_.GlobalTheory.T.rallis_inner_product_formula_first_occurrence hPr hK hM hInp hS)) hS) ?_
  intro D T Lc sc G μ₀ C x b hμ H
  obtain ⟨⟨H1, H2⟩, hGood, htw, hSm⟩ := H
  intro W S hψ hN i j t A A' WW X c0 δ t0 P₀ P₀' P P' z z' C' dl hX hc hB₀ hB hz hz' hz0 hz'0 hI
  obtain ⟨hct, hc0, γ, hγ⟩ := H1 W S hψ hN i j t A A' WW X c0 hX hc
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hγ
    exact hct hγ.symm
  refine ⟨γ, hγ0, hc0, hγ, fun w hw => ?_⟩
  obtain ⟨κ, hκ, H⟩ := H2 W S hψ hN i j A A' WW X c0 δ t0 hX hc
  obtain ⟨-, hQn1, hmod⟩ := Model.base_tuple G hμ
  obtain ⟨u₁, M, M', hu₁, hu₁q, hu₁n, hr₁⟩ := H t _ P P' hB
  obtain ⟨u₂, N₁, N₂, hu₂, hu₂q, hu₂n, hr₂⟩ := H μ₀ _ P₀ P₀' (hmod ▸ hB₀)
  obtain ⟨S', del, hE, hCo, -, rfl⟩ := hI
  obtain ⟨p, hp, hpw⟩ := exists_prime_under w
  haveI : Fact p.Prime := ⟨hp⟩
  have hpQ : ¬ p ∣ Qn G t := fun hd => hw (by
    obtain ⟨k, hk⟩ := hd
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hpw)
  have hp1 : ¬ p ∣ Qn G μ₀ := by rw [hQn1]; exact hp.not_dvd_one
  obtain ⟨hv, hvn⟩ := lamC_div_norm hu₁q hu₂q (hu₁n p hpQ) (hu₂n p hp1)
  have hlev : padicValNat p (levQ G.pl * Qn G t) ≤ padicValNat p (levQ G.pl) := by
    have h0 : levQ G.pl ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ =>
      pow_ne_zero _ (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
    have hzQ : padicValNat p (Qn G t) = 0 := by
      simpa only [← Nat.padicValNat_def] using (multiplicity_eq_zero_of_not_dvd hpQ)
    rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) h0 (Model.Qn_ne_zero G t), hzQ, add_zero]
  have e1 := hB.rank
  have e2 := hB₀.rank
  have s1 := hSm δ t0 _ P P' t i j _ hB
  have s2 := hSm δ t0 _ P₀ P₀' μ₀ i j _ hB₀
  refine GlobalTheory.T.valuation_proportionalityRatio_le_bottomPairs D (bigN D) (maxWt D sc.cGap) (levQ G.pl) S' del _ (hInp D) hE hCo D.what₂.LL D.what₂.embLL w p hpw δ t0
    (levQ G.pl * Qn G t) (levQ G.pl) hlev le_rfl P P' P₀ P₀' s1.1 s1.2 s2.1 s2.2 e1.2.2.2 e2.2.2.2
    (κ * u₁ * c0 t) (κ * u₂ * c0 μ₀) (u₁ / u₂) M N₂ (fun h T => (hr₁ e1.2.2.2 h).1 T)
    (fun h T' => (hr₂ e2.2.2.2 h).2 T') (mul_ne_zero (mul_ne_zero hκ hu₂) hc0) hv hvn γ z z' ?_ hz hz' hz0 hz'0
  rw [← hγ]
  field_simp
end GlobalTheory.SqTop
end
end

section
open GlobalTheory.SqTop

theorem _root_.GlobalTheory.T.botConst_of_theta_matching : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → (∀ D, GlobalTheory.NormSum.Inp D) → BotSmall → LNe → BotConst := by
  first | exact @_root_.GlobalTheory.SqTop.botConst_of_inputs_alt | exact _root_.GlobalTheory.SqTop.botConst_of_inputs_alt | (intros; apply _root_.GlobalTheory.SqTop.botConst_of_inputs_alt <;> assumption)
end
end
end
