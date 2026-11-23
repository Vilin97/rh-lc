module

public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTwistedGeneratorsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameViaTwistedGeneratorsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartYvEqAlgebraMapXb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlkFProperStepInjectiveBlockDiagStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetFacGMatEqOne
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNonzeroXbOfLeftInverse
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GMatIsGenericFlag
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBaseChangeCompatible
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBasesLinearIndependentSpan
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeDeterminantStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeRegularStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDegreeFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDivisorFormula
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameGenericRankStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameHeightFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameLeadingTermStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameMinorValuation
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameOrderBoundStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameUnitCriterion
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptIsVectorBundleRankStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.YvEqSumMinorsGMatStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartYvEqAlgebraMapXbStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.basePart_yv_eq_algebraMap_xb : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), ∀ r, basePart (blkF Ψ p q K₀) (yv A x₀) r = algebraMap Ω (GenField Ω (rk Ψ p q)) (xb A x₀ r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.basePart_yv | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.basePart_yv | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.basePart_yv <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.DetFacGMatEqOneStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.detFac_gMat_eq_one : ∀ (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ) (i : Fin (p + q)), detFac p i (gMat p q Ω τ) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNonzeroXbOfLeftInverseStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.exists_nonzero_xb_of_left_inverse : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), (∀ k, ∃ i, x₀ ⟨k, i⟩ ≠ 0) → (∀ s, ∃ B : Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω, B * A s = 1) → ∀ k, ∃ i, xb A x₀ ⟨k, i⟩ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt.xb_block_ne | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt.xb_block_ne | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt.xb_block_ne <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.GMatIsGenericFlagStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.isGenericFlag_gMat : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω], GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag Ω p (gMat (Ψ := Ψ) p q Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBaseChangeCompatibleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_base_change_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω') ⟶ Z) (h : Z ⟶ A.X), (∀ q : Z, genPt ξ' ⤳ q) → CoordTie ℤ ξ' (seg y') → IsNormalScheme Z → GlobalTheory.CompanionTheory.Ar.Dominates ξ' A.ξ h i → Smooth h → ∃ (A' : HodgeCpt Y S y') (e : A'.X ≅ Z) (j : A.Li →+ A'.Li), A'.ξ ≫ e.hom = ξ' ∧ HodgeOver A' A (e.hom ≫ h) i j ∧ A'.R = A.R ∧ Submodule.span Ω' (Set.range j) = ⊤ ∧ ∀ s, A'.V s = (A.V s).pull A'.ξ (e.hom ≫ h) j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HcptFlat.hodgeCpt_pull_smooth | exact GlobalTheory.CompanionTheory.Ar.HcptFlat.hodgeCpt_pull_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.HcptFlat.hodgeCpt_pull_smooth <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBasesLinearIndependentSpanStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_bases_linearIndependent_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐), ∀ s, LinearIndependent Ω (cc 𝔐 bW bO s) ∧ Submodule.span Ω (Set.range (cc 𝔐 bW bO s)) = VV 𝔐 s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases.cc_basis | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases.cc_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases.cc_basis <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDivisorFormulaStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_frame_divisor_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → 𝔐.IsCover d → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → Submodule.span (GenField Ω (rk (CMType H) D.p D.q)) (Set.range j) = ⊤ → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ∃ Fl : 𝔐'.Flag, Fl.deg = d ∧ ColFlags 𝔐 bW bO j Fl := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.exists_colFlags | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.exists_colFlags | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.exists_colFlags <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameMinorValuationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_frame_minor_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → ∀ h : ModelOK (aOf 𝔐 bW bO φ) x₀ m, ∀ (q : Cpt 𝔐.ξ) (F : FrameData (idx (p := D.p) (q := D.q) J₀ n) (CMType H) (D.p + D.q) Ω (blkF (CMType H) D.p D.q K₀)), (model (aOf 𝔐 bW bO φ) x₀ m h).IsFrame F → (model (aOf 𝔐 bW bO φ) x₀ m h).GoodAt F (ptIdeal 𝔐.ξ (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) q) → ∀ τ, (𝔐.V (.inl τ)).IsFrameAt (colFrame (fun a => (bW τ a : 𝔐.Li)) (wBlock (F.T τ))) q ∧ (omBundle 𝔐 τ).IsFrameAt (colFrame (bO τ) (omBlock (F.T τ))) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt.isFrameAt_of_goodAt | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt.isFrameAt_of_goodAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt.isFrameAt_of_goodAt <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameUnitCriterionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.hodgeCpt_frame_unit_criterion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → IsArithVar (mCoordIdeal x₀) (d + 1) → IsArithVar (mCoordIdeal (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (d + Fintype.card (CMType H) * (D.p.choose 2 + D.q.choose 2) + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_flagModel | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_flagModel | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_flagModel <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelExistsOfGiven

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.PB.FMX.flagModelExists : GlobalTheory.CompanionTheory.Ar.Top.Given → PB.FlagModelExists := by
  intro _ E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 nd d bW bO hv hd
  classical
  have hVB := GlobalTheory.T.hodgeCpt_isVectorBundle_rank E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐
  have hcc := GlobalTheory.T.hodgeCpt_bases_linearIndependent_span E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO
  have hg : ∀ s, ∃ (m n : ℕ) (φ : Fin n → Module.Dual Ω (EE 𝔐)), IsTwistGen 𝔐.ξ (seg x₀) (LL 𝔐 s) m φ := fun s =>
    GlobalTheory.T.exists_twisted_generators 𝔐.X Ω 𝔐.ξ (EE 𝔐) ((k : K₀) → J₀ k) (seg x₀) (LL 𝔐 s) _ (VV 𝔐 s) 𝔐.tie 𝔐.all (hVB s)
  choose m n φ hφ using hg
  have hB : ∀ s, ∃ B : Matrix (Fin (rk (CMType H) D.p D.q s)) (Fin (n s)) Ω, B * aOf 𝔐 bW bO φ s = 1 := fun s =>
    GlobalTheory.T.frame_via_twisted_generators 𝔐.X Ω 𝔐.ξ (EE 𝔐) _ (seg x₀) (LL 𝔐 s) _ (VV 𝔐 s) (m s) (n s) (φ s) (cc 𝔐 bW bO s) 𝔐.tie (hVB s)
      (hφ s) (hcc s).1 (hcc s).2
  have hF : FormsOK 𝔐 bW bO m φ := ⟨hVB, hcc, hφ, hB⟩
  have hx₀ : ∀ k, ∃ i, x₀ ⟨k, i⟩ ≠ 0 := by
    obtain ⟨c₀, hc₀⟩ := exists_inBlockChart 𝔐.tie ⟨genPt 𝔐.ξ, specializes_refl _⟩
    exact fun k => ⟨c₀ k, (hc₀ k).1⟩
  have ht := GlobalTheory.T.hodgeCpt_frame_change_determinant E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF
  have hP := GlobalTheory.T.blkF_properStep_injective_blockDiag (CMType H) D.p D.q Ω K₀
  have hmod : ModelOK (aOf 𝔐 bW bO φ) x₀ m :=
    ⟨hP.1, hP.2.1, GlobalTheory.T.exists_nonzero_xb_of_left_inverse _ _ _ Ω _ _ K₀ J₀ x₀ hx₀ hB,
      GlobalTheory.T.basePart_yv_eq_algebraMap_xb _ _ _ Ω _ _ K₀ J₀ x₀, hP.2.2, GlobalTheory.T.isGenericFlag_gMat _ _ _ Ω, GlobalTheory.T.yv_eq_sum_minors_gMat _ _ _ Ω _ _ K₀ J₀ x₀,
      GlobalTheory.T.hodgeCpt_frame_change_regular E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF ht⟩
  have hT := GlobalTheory.T.hodgeCpt_frame_minor_valuation E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF ht hmod
  obtain ⟨Z, ξ', f, htie, hall, hdom, hsm⟩ := GlobalTheory.T.hodgeCpt_frame_leading_term E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF
  have hnorm := GlobalTheory.T.hodgeCpt_frame_degree_formula E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF Z ξ' f htie hall hdom hsm
  obtain ⟨𝔐', e, j, -, hov, hR, hsp, hV⟩ := GlobalTheory.T.hodgeCpt_base_change_compatible E H D l Xo c Y S Ω _ (algebraMap Ω _) K₀ _ J₀ _ x₀ _ 𝔐 Z ξ' f hall htie hnorm hdom hsm
  obtain ⟨Fl, hdeg, hfl⟩ := GlobalTheory.T.hodgeCpt_frame_divisor_formula E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ d hF hd 𝔐' _ j hov hsp hV
  obtain ⟨xdeg, hroot, hdy⟩ := GlobalTheory.T.hodgeCpt_frame_height_formula E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF ht hmod 𝔐' _ j Fl hov hsp hV hfl
  let M := model (aOf 𝔐 bW bO φ) x₀ m hmod
  let 𝔐₁ : HodgeCpt Y S M.x := reTie 𝔐 (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) ht
  let tie : FlagTie M 𝔐₁ :=
    { eW := bW, eO := bO, frameW := fun q F h h' τ => (hT q F h h' τ).1, frameO := fun q F h h' τ => (hT q F h h' τ).2 }
  have hκ : ∀ k : K₀, ∀ r, M.blk r ≠ some (.inl k) := fun k r h => by
    change blkF (CMType H) D.p D.q K₀ r = _ at h
    unfold blkF at h
    split_ifs at h
    simpa using h
  let κ : K₀ → NonPluckerBlocks M.blk := fun k => ⟨.inl k, hκ k⟩
  let v : (Σ k, J₀ k) → Σ k, baseIdx (idx (p := D.p) (q := D.q) J₀ n) M.blk k := fun r => ⟨κ r.1, r.2⟩
  refine ⟨K₀ ⊕ StepIx (CMType H) D.p D.q, inferInstance, idx J₀ n, inferInstance, GenField Ω (rk (CMType H) D.p D.q),
    inferInstance, yv (aOf 𝔐 bW bO φ) x₀, M, 𝔐₁, tie, κ, v, RingHom.id Ω, 𝟙 𝔐.X, AddMonoidHom.id 𝔐.Li, 𝔐', Fl, xdeg,
    fun _ => 1, ⟨?_, fun _ => rfl, Function.bijective_id, inferInstanceAs (IsIso (𝟙 𝔐.X)), ?_, rfl, ?_⟩,
    ⟨hd, GlobalTheory.T.hodgeCpt_frame_order_bound E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ nd hF ht hv, GlobalTheory.T.hodgeCpt_frame_generic_rank E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ ht⟩,
    GlobalTheory.T.hodgeCpt_frame_unit_criterion E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ nd hF hv, ?_, hdeg⟩
  · refine ⟨fun a b h => Sum.inl_injective (congrArg (fun k => k.1) h), ?_, fun _ => rfl, ?_⟩
    · rintro ⟨k, i⟩ ⟨k', i'⟩ h
      have h1 : k = k' := Sum.inl_injective (congrArg (fun r => r.1.1) h)
      subst h1
      have h2 : HEq i i' := (Sigma.mk.inj_iff.1 h).2
      rw [eq_of_heq h2]
    · rintro ⟨_, i⟩ ⟨k, rfl⟩
      exact ⟨⟨k, i⟩, rfl⟩
  · exact HodgeOver.refl 𝔐
  · exact BasesOver.refl bW bO
  · refine ⟨⟨e.hom ≫ f, j, hov, hR, hV, hfl.1, hfl.2⟩, hroot, hdy, fun τ i => ?_⟩
    have h1 : detFac D.p i (M.g τ) = 1 := GlobalTheory.T.detFac_gMat_eq_one (CMType H) D.p D.q Ω τ i
    have h2 : M.lam (τ, i) = 1 := rfl
    rw [h1, h2]
    rcases M.blk (τ, i) with _ | b <;> simp
end
end
end
