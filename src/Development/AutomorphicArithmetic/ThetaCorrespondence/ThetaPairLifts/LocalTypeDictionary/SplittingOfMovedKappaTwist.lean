module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuum
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitCharValueSplitCharacters
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLatticesFormSelfDualTriples
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SphericalPair
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlaces
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DifferentiableMovedOperatorEval
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaFunctionInfiniteRationalLaw
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMovedSeriesDecomposition
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistNormKappaMovedPlace
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarIdempotentValue

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.SplitMoveKappa

theorem qbar_of_root {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : ζ ∈ TaylorLogMetric.Qbar := by
  have halg : IsAlgebraic ℚ ζ := by
    refine ⟨Polynomial.X ^ n - Polynomial.C 1, ?_, ?_⟩
    · exact Polynomial.X_pow_sub_C_ne_zero hn 1
    · simp [hζ]
  exact mem_algebraicClosure_iff.2 halg

theorem mod1All_root {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : Mod1All ζ := by
  refine ⟨qbar_of_root hn hζ, fun σ => ?_⟩
  have h1 : (⟨ζ, qbar_of_root hn hζ⟩ : TaylorLogMetric.Qbar) ^ n = 1 := by ext; simpa using hζ
  have h2 : (σ ⟨ζ, qbar_of_root hn hζ⟩) ^ n = 1 := by rw [← map_pow, h1, map_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, h2, norm_one])

theorem lamC_mem {q : ℕ} [Fact q.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[q]) {x : ℂ} (h : x ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam x = lam ⟨x, h⟩ := dif_pos h

theorem unitAt_mul {q : ℕ} [Fact q.Prime] {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar)
    (ux : GlobalTheory.MovedKappaEx.UnitAt q x) (uy : GlobalTheory.MovedKappaEx.UnitAt q y) : GlobalTheory.MovedKappaEx.UnitAt q (x * y) := by
  intro lam
  have e : (⟨x * y, mul_mem hx hy⟩ : TaylorLogMetric.Qbar) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  have hx' := ux lam
  have hy' := uy lam
  rw [lamC_mem lam hx] at hx'
  rw [lamC_mem lam hy] at hy'
  rw [lamC_mem lam (mul_mem hx hy), e, map_mul, norm_mul, hx', hy', one_mul]

theorem unitAt_inv {q : ℕ} [Fact q.Prime] {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar)
    (ux : GlobalTheory.MovedKappaEx.UnitAt q x) : GlobalTheory.MovedKappaEx.UnitAt q x⁻¹ := by
  intro lam
  have e : (⟨x⁻¹, inv_mem hx⟩ : TaylorLogMetric.Qbar) = (⟨x, hx⟩ : TaylorLogMetric.Qbar)⁻¹ := rfl
  have hx' := ux lam
  rw [lamC_mem lam hx] at hx'
  rw [lamC_mem lam (inv_mem hx), e, map_inv₀, norm_inv, hx', inv_one]

theorem unitAt_root (q : ℕ) [Fact q.Prime] {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) :
    GlobalTheory.MovedKappaEx.UnitAt q ζ := by
  intro lam
  have h1 : (⟨ζ, qbar_of_root hn hζ⟩ : TaylorLogMetric.Qbar) ^ n = 1 := by ext; simpa using hζ
  have h2 : (lam ⟨ζ, qbar_of_root hn hζ⟩) ^ n = 1 := by rw [← map_pow, h1, map_one]
  rw [lamC_mem lam (qbar_of_root hn hζ)]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, h2, norm_one])

end GlobalTheory.SplitMoveKappa
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarLocalIdentity

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.SplitMoveKappa

theorem om_toPair_mul : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R) (p : Pair T) (s x : FinPt ch.G p.small) (s' y : FinPt ch.G p.big) (v : WO (ch.G.pS p) (ch.G.pT p) → ℂ),
    ch.W.om p (ch.G.toPair p ((s * x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((s' * y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) v =
      ch.W.om p (ch.G.toPair p (s : Formalism.L2.Theta.GA D (ch.G.V p.small)) (s' : Formalism.L2.Theta.GA D (ch.G.V p.big)))
        (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) v) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch p s x s' y v
  have e1 : ((s * x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) =
      (s : Formalism.L2.Theta.GA D (ch.G.V p.small)) * ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) := by
    rw [mul_assoc]; rfl
  have e2 : ((s' * y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big)) =
      (s' : Formalism.L2.Theta.GA D (ch.G.V p.big)) * ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big)) := by
    rw [mul_assoc]; rfl
  have e3 : ∀ (a b : Formalism.L2.Theta.GA D (ch.G.V p.small)) (c d : Formalism.L2.Theta.GA D (ch.G.V p.big)),
      ch.G.toPair p (a * b) (c * d) = ch.G.toPair p a c * ch.G.toPair p b d := by
    intro a b c d
    cases p <;> simp [GlobalTheory.ChiGrid.GridData.toPair, map_mul]
  rw [e1, e2, e3, map_mul]
  rfl

end GlobalTheory.SplitMoveKappa
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistJetKappaSplitMove

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.SplitMoveKappa
theorem jetKappa_split_move : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ (s : FinPt ch.G p.small) (s' : FinPt ch.G p.big),
    SuppAt e _ (s : GA D (ch.G.V p.small)) → SuppAt e _ (s' : GA D (ch.G.V p.big)) →
    ∃ x₀ y₀ : (Formalism.L2.Theta.AE D)ˣ,
      (∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e) ∨ (x₀ : Formalism.L2.Theta.AE D) = cA D e * a + (1 - cA D e)) ∧
      (∃ b : Formalism.L2.Theta.AE D, (y₀ : Formalism.L2.Theta.AE D) = e * b + (1 - e) ∨ (y₀ : Formalism.L2.Theta.AE D) = cA D e * b + (1 - cA D e)) ∧
      ∃ ζ : ℂ, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧ ∃ r : ℝ, 0 < r ∧
        GlobalTheory.MovedKappaEx.JetKap ch p (s * x) (s' * y)
          ((r : ℂ) * ζ * ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ) * κ) := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y κ hκ e he s s' hs hs'
  obtain ⟨x₀, y₀, hx₀, hy₀, ζ, ⟨n, hn, hζ⟩, r, hr, hread⟩ := _root_.GlobalTheory.T.twist_splitMoveFrames_jets hP hI ch hch p hp x y e he s s' hs hs'
  have hC := ch.S.Z.crv
  have he0 := ch.S.Z.e0_is p hp
  have hsd := _root_.GlobalTheory.T.twisted_moved_series_decomposition hP hI ch hch p hp x y
  have hsd' := _root_.GlobalTheory.T.twisted_moved_series_decomposition hP hI ch hch p hp (s * x) (s' * y)
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have he0ne : ch.S.Z.e0 p ≠ 0 := by
    intro h
    have hn := he0.2.2.1
    rw [h] at hn
    have h0 : Formalism.MainNotions.TaylorLogMetric.normSq D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) (ch.G.pS p).rank (ch.G.pT p).rank) (0 : Formalism.MainNotions.TaylorLogMetric.VC D (ch.G.pS p).rank (ch.G.pT p).rank → ℂ) = 0 := by
      simp [Formalism.MainNotions.TaylorLogMetric.normSq]
    rw [h0] at hn
    exact pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hG D.host.ccK ch.S.Z.δ _ hC ch.S.Z.pt0) hn.symm
  have hK0 : Formalism.MainNotions.StandardLatticesGL3.KLat D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) (ch.G.pS p).rank (ch.G.pT p).rank) :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacInt.sd_std D _, GlobalTheory.NormSum.VacInt.sd_std D _, rfl⟩
  have hK1 : Formalism.MainNotions.StandardLatticesGL3.KLat D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) := Or.inr ⟨_, _, hsd.1, hsd.2, rfl⟩
  have hK2 : Formalism.MainNotions.StandardLatticesGL3.KLat D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p (s * x) (s' * y)) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p (s * x) (s' * y))) := Or.inr ⟨_, _, hsd'.1, hsd'.2, rfl⟩
  obtain ⟨-, -, -, htrip⟩ := GlobalTheory.ThetaTriple.klat_triples D D.host.ccK ch.S.Z.δ hC (ch.G.pS p).rank (ch.G.pT p).rank
  obtain ⟨μ, hμ⟩ := htrip _ _ _ hK0 hK1 hK2 _ he0.1 he0ne
  have hμ8 : μ ^ 8 = 1 := hμ.2.2.2.2.2.2.2.2.1
  have hμI := hμ.2.2.2.2.2.2.2.2.2
  refine ⟨x₀, y₀, hx₀, hy₀, ζ * μ, ⟨8 * n, by omega, by rw [mul_pow, pow_mul', hζ, pow_mul, hμ8, one_pow, one_pow, one_mul]⟩, r, hr, ?_⟩
  have hd := _root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval hP hI ch hch p hp x y
  have h1 := hread (fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) (hd.const_mul κ) hκ
  intro k
  rw [om_toPair_mul, h1 k]
  congr 3
  refine congrArg _ (funext fun z => ?_)
  have hs1 : (fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) =
      κ • Iop D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) := rfl
  rw [hs1, GlobalTheory.InertSign.Iop_smul, hμI]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
end GlobalTheory.SplitMoveKappa
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

theorem _root_.GlobalTheory.T.twist_jetKappa_split_move : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ (s : FinPt ch.G p.small) (s' : FinPt ch.G p.big),
    SuppAt e _ (s : GA D (ch.G.V p.small)) → SuppAt e _ (s' : GA D (ch.G.V p.big)) →
    ∃ x₀ y₀ : (Formalism.L2.Theta.AE D)ˣ,
      (∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e) ∨ (x₀ : Formalism.L2.Theta.AE D) = cA D e * a + (1 - cA D e)) ∧
      (∃ b : Formalism.L2.Theta.AE D, (y₀ : Formalism.L2.Theta.AE D) = e * b + (1 - e) ∨ (y₀ : Formalism.L2.Theta.AE D) = cA D e * b + (1 - cA D e)) ∧
      ∃ ζ : ℂ, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧ ∃ r : ℝ, 0 < r ∧
        GlobalTheory.MovedKappaEx.JetKap ch p (s * x) (s' * y)
          ((r : ℂ) * ζ * ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ) * κ) := by
  first | exact @_root_.GlobalTheory.SplitMoveKappa.jetKappa_split_move | exact _root_.GlobalTheory.SplitMoveKappa.jetKappa_split_move | (intros; apply _root_.GlobalTheory.SplitMoveKappa.jetKappa_split_move <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplittingOfMovedKappaTwist

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.SplitMoveKappa
theorem movedKappa_split : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ (s : FinPt ch.G p.small) (s' : FinPt ch.G p.big),
    SuppAt e _ (s : GA D (ch.G.V p.small)) → SuppAt e _ (s' : GA D (ch.G.V p.big)) →
    ∃ c : ℂ, Mod1All c ∧ (∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q → GlobalTheory.MovedKappaEx.UnitAt q c) ∧
      GlobalTheory.MovedKappaEx.JetKap ch p (s * x) (s' * y) (c * κ) := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y κ hJ e he s s' hs hs'
  obtain ⟨x₀, y₀, hx₀, hy₀, ζ, ⟨n, hn, hζ⟩, r, hr, hJ'⟩ := _root_.GlobalTheory.T.twist_jetKappa_split_move hP hI ch hch p hp x y κ hJ e he s s' hs hs'
  have h1 := _root_.GlobalTheory.T.twist_norm_kappa_moved_place hP hI ch hch p hp x y κ hJ
  have h2 := _root_.GlobalTheory.T.twist_norm_kappa_moved_place hP hI ch hch p hp _ _ _ hJ'
  have hζn : ‖ζ‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, hζ, norm_one])
  have hχn : ‖((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ)‖ = 1 := Circle.norm_coe _
  have hr1 : (r : ℂ) = 1 := by
    rw [norm_mul, norm_mul, norm_mul, hζn, hχn, h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h2
    simp only [mul_one] at h2
    rw [h2]; simp
  rw [hr1, one_mul] at hJ'
  have hA := _root_.GlobalTheory.T.twist_split_character_values hP hI ch hch p hp e he x₀ hx₀
  have hB := _root_.GlobalTheory.T.twist_split_character_values hP hI ch hch p hp e he y₀ hy₀
  have hco : ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ) =
      ((ch.G.chrT p x₀ : Circle) : ℂ)⁻¹ * ((ch.G.chrS p y₀ : Circle) : ℂ) := by
    rw [Circle.coe_mul, Circle.coe_inv]
  have hm : Mod1All ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ) := by
    rw [hco]
    exact GlobalTheory.FamilyTieProof.mod1All_mul' (GlobalTheory.FamilyTieProof.mod1All_inv hA.1.2) hB.1.1
  refine ⟨ζ * ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ), GlobalTheory.FamilyTieProof.mod1All_mul' (mod1All_root hn hζ) hm,
    fun q _ hq => ?_, hJ'⟩
  refine unitAt_mul (qbar_of_root hn hζ) hm.1 (unitAt_root q hn hζ) ?_
  rw [hco]
  exact unitAt_mul (inv_mem hA.1.2.1) hB.1.1.1 (unitAt_inv hA.1.2.1 ((hA.2 q hq).2)) ((hB.2 q hq).1)
end GlobalTheory.SplitMoveKappa
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

theorem _root_.GlobalTheory.T.splitting_of_moved_kappa_twist : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ (s : FinPt ch.G p.small) (s' : FinPt ch.G p.big),
    SuppAt e _ (s : GA D (ch.G.V p.small)) → SuppAt e _ (s' : GA D (ch.G.V p.big)) →
    ∃ c : ℂ, Mod1All c ∧ (∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q → GlobalTheory.MovedKappaEx.UnitAt q c) ∧
      GlobalTheory.MovedKappaEx.JetKap ch p (s * x) (s' * y) (c * κ) := by
  first | exact @_root_.GlobalTheory.SplitMoveKappa.movedKappa_split | exact _root_.GlobalTheory.SplitMoveKappa.movedKappa_split | (intros; apply _root_.GlobalTheory.SplitMoveKappa.movedKappa_split <;> assumption)
end
end
end
