module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormDifferentEqProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStrips
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMemBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AtDatRowTestOfExField
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjKOfSeparates
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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftExtensionFieldExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftRowPropertiesConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaPairLiftCuspidalOfHypotheses
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TowerOfThetaMatching
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleExistenceOfTheta
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLinearBound
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralDefiniteSourceConvergesContinuousInStatement
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Parity
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomTripleIntegralEqConstMulLocal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareThetaIntegralsEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedWeilRepresentationConvergence

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjKOfSeparatesLinB

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowEx

theorem injK_of_separates_linB (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate) (hL : LinB) : InjK := by
  refine GlobalTheory.RowTest.injK_of_separates hS ?_
  rcases hL with ⟨C0, hL⟩
  refine ⟨C0, fun ε CF hCF => ?_⟩
  obtain ⟨x0, hL⟩ := hL ε CF hCF
  refine ⟨x0, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hset ch hch hsc ρ ξ a u => ?_⟩
  exact hL D large₂ hε hx Γ Pl0 T A Ks R F hset (ch.withReal ρ ξ) hsc (hch.toIsBase.withReal ρ ξ) a u


end GlobalTheory.RowEx

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatioOfLocalMatchingTowers

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

open Finset GlobalTheory.FunObj.SqNum

namespace GlobalTheory.RowClaim

theorem sqRatio_mem_grid {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T)
    (W : G.Weil) (S : GridChoice W Set.univ) (ρ : RealMatch W) (c : Fin D.R.m → Fin D.R.m → T → ℂ)
    (hN : NumbersIn D.what₂.embLL S μ₀)
    (hC : ∀ i j t, SquareNonzero W S.B ρ t i j ∧ c i j t ≠ 0) (hK : ∀ i j t, IsSquareConst W S.B ρ t i j (c i j t))
    (hLN : ∀ i j : Fin D.R.m, (∀ t, ∃ Λ, GlobalTheory.CMVal.IsHeckeL (SqNum.nuH G t i j) Λ ∧
      ∀ s : ℤ, 1 - (GlobalTheory.SqTop.e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → Λ s ≠ 0))
    (hTX : ∀ i j : Fin D.R.m, ∃ (A A' WW : HSp D) (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X ∧ X.IsConst W.ψ W.θ c0)
    (hTW : ∀ (i j : Fin D.R.m) (t : T) (c c₀ : ℂ) (A A' WW : HSp D) (X : Tri T A A' WW)
      (c0 : T → ℂ) (Λ Λ₀ : ℂ → ℂ), SquareNonzero W S.B ρ t i j → IsSquareConst W S.B ρ t i j c → SquareNonzero W S.B ρ μ₀ i j →
      IsSquareConst W S.B ρ μ₀ i j c₀ → IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 → GlobalTheory.CMVal.IsHeckeL (SqNum.nuH G t i j) Λ →
      GlobalTheory.CMVal.IsHeckeL (SqNum.nuH G μ₀ i j) Λ₀ → ∃ u : Fin (GlobalTheory.SqTop.pp D j + GlobalTheory.SqTop.qq D j) → ℂ,
        (∀ k, GlobalTheory.Square.StepRatio D.what₂.embLL (GlobalTheory.SqTop.Qn G t) G.pl.S0 (SqNum.condExp G.pl)
          (fun v => Ideal.absNorm v.asIdeal) (u k) 1) ∧
        ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (GlobalTheory.SqTop.Qn G t) ζ ∧
          c / c₀ * ∏ k ∈ range (GlobalTheory.SqTop.qq D j), Λ (GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) / Λ₀ (GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) =
            D.what₂.embLL ζ * (∏ k, u k) * (c0 t / c0 μ₀) *
              ∏ k ∈ range (GlobalTheory.SqTop.pp D j), Λ (GlobalTheory.SqTop.eTop D i j + GlobalTheory.SqTop.qq D j - k : ℕ) /
                Λ₀ (GlobalTheory.SqTop.eTop D i j + GlobalTheory.SqTop.qq D j - k : ℕ))
    (hBF : ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X →
      ∃ lam : T → ℂ, GlobalTheory.ConstRatio.Factor X W.ψ W.θ lam)
    (i j : Fin D.R.m) (t : T) : c i j t / c i j μ₀ ∈ Set.range D.what₂.embLL := by
  have hF : ∀ z : ℂ, z ∈ Set.range D.what₂.embLL ↔ z ∈ D.what₂.embLL.fieldRange := fun z => Iff.rfl

  obtain ⟨A₀, A₀', WW₀, X₀, -, hX₀, -⟩ := hTX i j
  obtain ⟨A, A', WW, X, hX, hS⟩ := hN.bottom i j ⟨A₀, A₀', WW₀, X₀, hX₀⟩
  obtain ⟨lam, hlam⟩ := hBF i j A A' WW X hX
  have hI := hX.is
  have hi' : ∀ t P g, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P g) X.fd' X.m' := fun t P g =>
    (GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D W.ψ false A' WW _ _ (X.ω' t) X.m' X.fd' _ (hI.weil' t) (GlobalTheory.ConstRatio.posDef_of_std hX.std')
      hI.meas'.1 hI.meas'.2 (GlobalTheory.Chain.InnerSteps.theta_pureTensorO hI.isVac.1 hI.isVac.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
        (GlobalTheory.ConstRatio.theta_f hI t).2 P)).1 g
  have hr := hS.rationalSums (fun t P g => hlam.2.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1 t P g) hi'
  have hrat := GlobalTheory.ConstRatio.ratIn_of_definite hI (GlobalTheory.ConstRatio.posDef_of_std hX.std) (GlobalTheory.ConstRatio.posDef_of_std hX.std')
    (GlobalTheory.ConstRatio.posDef_of_std hX.stdW) hlam hr μ₀
  haveI : Nonempty T := ⟨μ₀⟩
  have hcst : X.IsConst W.ψ W.θ lam := hlam.isConst

  obtain ⟨Λ, hΛ, hΛne⟩ := hLN i j t
  obtain ⟨Λ₀, hΛ₀, hΛ₀ne⟩ := hLN i j μ₀
  obtain ⟨u, hu, ζ, -, heq⟩ := hTW i j t (c i j t) (c i j μ₀) A A' WW X lam Λ Λ₀ (hC i j t).1 (hK i j t) (hC i j μ₀).1
    (hK i j μ₀) hX hcst hΛ hΛ₀
  rw [hF]
  obtain ⟨hn1, -, -, hn4, -, -, -, hn8, hn9⟩ := GlobalTheory.SqTop.Model.tower_numbers (D := D) i j
  have hne : ∀ L : ℂ → ℂ, (∀ s : ℤ, 1 - (GlobalTheory.SqTop.e0 D i j : ℤ) ≤ s → s ≤ halfRank D i j → L s ≠ 0) →
      ∀ n : ℕ, 1 ≤ n → n ≤ halfRank D i j → L (n : ℂ) ≠ 0 := fun L h n h1 h2 => by
    have := h n (by omega) (by exact_mod_cast h2)
    simpa using this
  have hs : ∀ n : ℕ, 1 ≤ n → n ≤ halfRank D i j →
      Λ (n : ℂ) / Λ₀ (n : ℂ) ∈ D.what₂.embLL.fieldRange ∧ Λ (n : ℂ) / Λ₀ (n : ℂ) ≠ 0 := fun n h1 h2 =>
    ⟨(hF _).1 (hN.ratios i j t Λ Λ₀ hΛ hΛ₀ n h1 (by omega) (hne Λ₀ hΛ₀ne n h1 h2)),
      div_ne_zero (hne Λ hΛne n h1 h2) (hne Λ₀ hΛ₀ne n h1 h2)⟩
  have hP1 : ∀ k ∈ range (GlobalTheory.SqTop.qq D j), Λ ((GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) : ℂ) /
      Λ₀ ((GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) : ℂ) ∈ D.what₂.embLL.fieldRange ∧
      Λ ((GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) : ℂ) / Λ₀ ((GlobalTheory.SqTop.eTop D i j + k + 1 : ℕ) : ℂ) ≠ 0 := fun k hk =>
    hs _ (by omega) (by have := mem_range.1 hk; omega)
  have hP2 : ∀ k ∈ range (GlobalTheory.SqTop.pp D j), Λ ((GlobalTheory.SqTop.eTop D i j + GlobalTheory.SqTop.qq D j - k : ℕ) : ℂ) /
      Λ₀ ((GlobalTheory.SqTop.eTop D i j + GlobalTheory.SqTop.qq D j - k : ℕ) : ℂ) ∈ D.what₂.embLL.fieldRange := fun k hk =>
    (hs _ (by have := mem_range.1 hk; omega) (by omega)).1
  have hU : (∏ k, u k) ∈ D.what₂.embLL.fieldRange := prod_mem fun k _ => by
    obtain ⟨b, g, g', -, -, h⟩ := hu k
    rw [h, mul_one]
    exact RingHom.mem_fieldRange.2 ⟨_, rfl⟩
  have hl : lam t / lam μ₀ ∈ D.what₂.embLL.fieldRange := by
    obtain ⟨-, y, hy⟩ := hrat t
    exact RingHom.mem_fieldRange.2 ⟨_, hy⟩
  rw [eq_div_of_mul_eq (prod_ne_zero_iff.2 fun k hk => (hP1 k hk).2) heq]
  exact div_mem (mul_mem (mul_mem (mul_mem (RingHom.mem_fieldRange.2 ⟨ζ, rfl⟩) hU) hl) (prod_mem hP2))
    (prod_mem fun k hk => (hP1 k hk).1)


end GlobalTheory.RowClaim

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLocalFactorRatioHolds

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
noncomputable section
open Finset GlobalTheory.FunObj.SqNum
namespace GlobalTheory.RowClaim

theorem twisted_local_factor_ratio_holds : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → ConstK →
    GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.TriEx → GlobalTheory.SqTop.Tower → RatioK := by
  intro hP hTA hLM hC hLN hTX hTW
  have hBF := _root_.GlobalTheory.T.bottom_triple_integral_eq_const_mul_local hP hTA hLM hLN
  obtain ⟨c1, h1⟩ := hC
  obtain ⟨c5, h5⟩ := GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and hLN hTX) (GlobalTheory.SqTop.Model.gBig_and hTW hBF)
  refine ⟨max c1 c5, fun ε CF hCF => ?_⟩
  obtain ⟨x1, g1⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C0, x5, g5⟩ := h5 ε CF (le_of_max_le_right hCF)
  refine ⟨max x1 x5, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hs ch hi hsc => ?_⟩
  have hc := g1 D large₂ he (le_of_max_le_left hx) Γ Pl0 T A Ks R F hs ch hi hsc
  have hrec : GlobalTheory.SqTop.Rec large₂ := (GlobalTheory.SqTop.Model.rec_iff large₂).2 ⟨hs.size, hs.host⟩
  have hL : R.toLevCh.Is A.μ0 := hs.core.lev
  intro hfield
  obtain ⟨sc, G, W, M, ρ, ξ, cv, rm, S, rp, n, e, c⟩ := ch
  change sc = _ at hsc
  subst hsc
  obtain ⟨⟨hLN', hTX'⟩, hTW', hBF'⟩ := g5 C0 le_rfl D large₂ he (le_of_max_le_right hx) hrec T R.toLevCh A.μ0 hL G
  have hstd : IsStdChar D W.ψ (-1) := (hi.weil.ψ : W.ψ = _) ▸ hs.std
  exact fun i j t => sqRatio_mem_grid G A.μ0 W S.toGridChoice rm c hfield hc hi.const (fun i j => (hLN' i j).1)
    (hTX' W hstd) (hTW' W S.toGridChoice rm hstd hfield) (hBF' W hstd) i j t
end GlobalTheory.RowClaim
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TestVectorAtDatumOfJoin

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
theorem GlobalTheory.RowTestAssembly.test_vector_at_datum_of_join : GlobalTheory.Published.SiegelSetUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) :=
  fun sg hw g P hJ a12 K LM T3 =>
    have s1 := _root_.GlobalTheory.WeilConv.twisted_weil_representation_convergence sg P
    have s2 := _root_.GlobalTheory.SquareLM.twisted_square_local_matching hw P K LM
    have s3 := _root_.GlobalTheory.SquareAgree.twisted_theta_integrals_agree P K LM
    have j := _root_.GlobalTheory.RowClaim.Join.thetaLift_row_properties_conj P K LM s1 s2 s3
    have l := GlobalTheory.SqTop.lNe_of_functionalEquation a12.abs GlobalTheory.HeckeStrip.completedLBoundedInStrips GlobalTheory.SqTop.fieldDat
    GlobalTheory.Twist.atDat_rowTest_of_exField g P.cuspRapidDecay j.2.2.1
      (GlobalTheory.RowEx.injK_of_separates_linB T3 (_root_.GlobalTheory.RowEx.twisted_linear_bound P (_root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses P)))
      j.2.1 j.1 j.2.2.2.1 j.2.2.2.2
      (_root_.GlobalTheory.RowClaim.twisted_local_factor_ratio_holds P K LM j.2.1 l (_root_.GlobalTheory.SqTop.triEx_holds_alt hw P K LM l) (_root_.GlobalTheory.SqTower.tower_alt_bis P K LM l))
      (_root_.GlobalTheory.T.theta_lift_extension_field_exists hw LM P hJ a12 K s1 s2 s3 T3)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.test_vector_assembly_holds : GlobalTheory.Published.SiegelSetUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) := by
  first | exact @_root_.GlobalTheory.RowTestAssembly.test_vector_at_datum_of_join | exact _root_.GlobalTheory.RowTestAssembly.test_vector_at_datum_of_join | (intros; apply _root_.GlobalTheory.RowTestAssembly.test_vector_at_datum_of_join <;> assumption)
end
end
end
