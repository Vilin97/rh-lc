module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Formalism.SharpRestriction.Divisibility.PrinLevClass
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
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices

-- Source module: Formalism.SharpRestriction.Divisibility.LatticeTransfer

section

@[expose] public section

noncomputable section

open NumberField MvPolynomial Finset
open scoped BigOperators

namespace Formalism.MainNotions.LatticeTransfer

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

def wt (Tau : Type) [Fintype Tau] (N : ℕ) : Vm Tau N → ℕ
  | Sum.inl _ => 1
  | Sum.inr (_, k) => k

structure Loc (D : D7) (XD : DivX D) where

  rt : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev) (p : ℕ) [Fact p.Prime]
    (la : XD.PlP p) (z : XD.Mp S κ p la), Bool × Rt D.what₂.Tau (XD.shv S κ).N → (XD.md S κ p la z).Z.LB

  rt_lie : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
    ∀ (i : Fin (rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ)) (i' : Fin (XD.shv S κ).N),
      (i' : ℕ) = i →
      rt S κ p la z (false, (τ0, i')) = ((XD.md S κ p la z).lie τ).x i ∧
      rt S κ p la z (true, (τ0, i')) = ((XD.md S κ p la z).lie τ).x' i

  rt_om : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la) (τ0 : D.what₂.Tau) (τ : Emb D p), (XD.jC p la).comp τ = tauEmb D τ0 →
    ∀ (i : Fin ((XD.shv S κ).N - rkOf (PsiOf D (XD.jC p la)) (XD.shv S κ).N (XD.shv S κ).j τ))
      (i' : Fin (XD.shv S κ).N), (i' : ℕ) = (XD.shv S κ).j + i →
      rt S κ p la z (false, (τ0, i')) = ((XD.md S κ p la z).om τ).x i ∧
      rt S κ p la z (true, (τ0, i')) = ((XD.md S κ p la z).om τ).x' i

  lieW_gen : letI := D.host.cmStar; ∀ (S : HSpace D.host.E) (κ : XD.Lev), HidaSetting D XD S κ →
    ∀ (p : ℕ) [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la), ∃ (e : Fin (D.R.f * (XD.shv S κ).N) ≃ Rt D.what₂.Tau (XD.shv S κ).N)
      (V : Fin (D.R.f * (XD.shv S κ).N) → (XD.md S κ p la z).Z.VDiv), ∀ l,
      (XD.md S κ p la z).Z.c1 ((XD.md S κ p la z).lieW.x l) =
        (if ((e l).2 : ℕ) < (XD.shv S κ).j then (1 : ℚ) else -1) •
            (XD.md S κ p la z).Z.c1 (rt S κ p la z (false, e l)) +
          (XD.md S κ p la z).Z.cD (V l)

section One
variable (D : D7) (XD : DivX D) (T : Loc D XD)
  (S : letI := D.host.cmStar; HSpace D.host.E) (κ : XD.Lev)

def adm1 : Prop :=
  ∀ p : ℕ, p.Prime → ∀ c : (XD.shv S κ).FibComp p, ¬ (XD.shv S κ).fibInBd p c

end One

def PointsLemma (D : D7) (XD : DivX D) (P : DIV.Align.PrinLev XD) : Prop :=
  ∀ S κ, HidaSetting D XD S κ → DIV.Align.LevB P κ → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ),
  p.Prime → p ≠ 2 → UnramE D p → p ∉ (XD.shv S κ).lev → ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau (XD.shv S κ).N + 1 →
  ∀ Q : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℝ,
    Q.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) m →
    (XD.shv S κ).arMix Sx R p
        ((tagDR D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k) -
          tagHT D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k)) * Q) =
      Real.log p * ((∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          (XD.shv S κ).chern (chLie (XD.shv S κ).j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) *
            collapse D _ Q)) -
        (XD.shv S κ).chern (chLie (XD.shv S κ).j (k - 1) (Sum.inl τ) * collapse D _ Q) /
          ((p : ℝ) - 1))

section One1
variable (D : D7) (XD : DivX D) (T : Loc D XD)
  (S : letI := D.host.cmStar; HSpace D.host.E) (κ : XD.Lev)

end One1

end Formalism.MainNotions.LatticeTransfer

end
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive

section

@[expose] public section

set_option autoImplicit false


noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop
open scoped ENNReal

namespace GlobalTheory.CovHt

def cost {K : Type} [Field K] [NumberField K] (e : HeightOneSpectrum (𝓞 K) →₀ ℝ) (t : (K →+* ℂ) → ℝ) : ℝ :=
  ((e.sum fun la a => a * Real.log (Ideal.absNorm la.asIdeal : ℝ)) + ∑ σ, t σ) / (Module.finrank ℚ K : ℝ)

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7}
  (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

def depthOn (Z : Comp Xo c) (G : WTZ E) (v : Rul Xo c → EReal) : EReal := ⨅ w ∈ latOn U Z G, v (w : Rul Xo c)

def smallL (Z : Comp Xo c) (G : WTZ E) (τ : ℕ) (t : ℝ) : Set (cuspOn U Z (τ • G)) :=
  {f | (∀ la, ∀ v ∈ (recVals Xo c).1 la, (τ : EReal) * depthOn U Z G v ≤ v (f : Rul Xo c)) ∧
    ∀ σ, GoodEmb c σ → ∀ y : FPt (U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
      ENNReal.ofReal (homN (U σ) x (τ • G) f ⟨y.1, y.2.1⟩) ^ 2 ≤
        ENNReal.ofReal (Real.exp (2 * τ * t)) * bergOn (U σ) (V σ) (dict σ) Z G y ^ τ}

def volL (a : ℕ) (Z : Comp Xo c) (G : WTZ E) (t : ℝ) : ℝ≥0∞ :=
  countVol (dimFlag Dw) (Module.finrank ℚ c.F) a fun τ => (smallL U x V dict Z G τ t).encard

def FinBd (Z : Comp Xo c) (G : WTZ E) (a : ℕ) (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) : Prop :=
  ∀ la, ∀ v ∈ (recVals Xo c).1 la, (∃ w ∈ latOn U Z G, v (w : Rul Xo c) ≠ ⊤) →
    (a : EReal) * depthOn U Z G v ≤ v θ + ((a * e la : ℝ) : EReal)

def NoBase (Z : Comp Xo c) (G : WTZ E) : Prop :=
  ∀ la, ∀ v ∈ (recVals Xo c).1 la, ∀ G' : WTZ E, ∀ f ∈ cuspOn U Z G', v f ≠ ⊤ → ∃ w ∈ latOn U Z G, v (w : Rul Xo c) ≠ ⊤

def InfBd (Z : Comp Xo c) (G G₀ : WTZ E) (a : ℕ) (θ : Rul Xo c) (t : (c.F →+* ℂ) → ℝ) : Prop :=
  (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) ∧
  ∀ σ, GoodEmb c σ → ∀ y : FPt (U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
    ENNReal.ofReal (homN (U σ) x G₀ θ ⟨y.1, y.2.1⟩) ^ 2 ≤
      ENNReal.ofReal (Real.exp (2 * a * t σ)) * bergOn (U σ) (V σ) (dict σ) Z G y ^ a

def Carries (Z : Comp Xo c) (u u' : AllWt.Weight Dw) (θ : Rul Xo c) : Prop :=
  θ ∈ secZ Xo c (exOf Dw ((8 : ℤ) • (u - u')) 0) ∧ genVal Z θ ≠ 0 ∧
    ∀ (k : ℕ), ∀ f ∈ cuspOn U Z ((8 * k) • wtOf Dw u' 0), θ ^ k * f ∈ cuspOn U Z ((8 * k) • wtOf Dw u 0)

def Mult (Z : Comp Xo c) (u u' : AllWt.Weight Dw) (cc : ℝ) : Prop :=
  NoBase U Z (wtOf Dw u 0) ∧ ∃ (θ : Rul Xo c) (e : HeightOneSpectrum (𝓞 c.F) →₀ ℝ) (t : (c.F →+* ℂ) → ℝ),
    Carries U Z u u' θ ∧ FinBd U Z (wtOf Dw u 0) 8 θ e ∧
    InfBd U x V dict Z (wtOf Dw u 0) (wtOf Dw ((8 : ℤ) • (u - u')) 0) 8 θ t ∧ cost e t ≤ cc

def l1 (u : AllWt.Weight Dw) : ℝ := ∑ τ, ∑ i, |(u τ i : ℝ)|


variable (E) in
def htEx (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1) + 40 * ((padicValNat p (discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ))


variable (Xo c) in
def HTCmp : Prop := ∀ (p : ℕ) (la : HeightOneSpectrum (𝓞 c.F)), p.Prime → ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal →
  ∀ v ∈ (recVals Xo c).1 la, ∃ w ∈ (htVals Xo c).1 la, ∀ (u : AllWt.Weight Dw), ∀ f ∈ secZ Xo c (exOf Dw u 0),
    w f ≤ v f + (((vLa la (p : c.F) : ℝ) * htEx E p * l1 u : ℝ) : EReal)


variable (l) in
def htCost (B : ℝ) : ℝ := ∑ᶠ p ∈ htPrimes l B, htEx E p * Real.log p

def WtGap (u : AllWt.Weight Dw) (g : ℝ) : Prop :=
  0 < g ∧ (∀ τ, StrictAnti (u τ)) ∧ ∀ τ (a b : Fin (Dw.p + Dw.q)), Dw.p ≤ (a : ℕ) → a ≠ b → g ≤ |(u τ a : ℝ) - u τ b|

def bndB (u : AllWt.Weight Dw) (g : ℝ) : ℝ :=
  4 * (Fintype.card (Psi H) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 * (1 + (⨆ k : Psi H × Fin (Dw.p + Dw.q), |(u k.1 k.2 : ℝ)|) / g)

def errX (s : ℝ) (u : AllWt.Weight Dw) (g : ℝ) : ℝ :=
  (Real.log (bndB u g) + s) * l1 u + (Dw.q : ℝ) * ∑ τ, ((⨆ i, (u τ i : ℝ)) - ⨅ i, (u τ i : ℝ))

def MeanGe (u : AllWt.Weight Dw) (B X : ℝ) : Prop :=
  ∃ sl : Comp Xo c → ℝ, (∀ Z, (sl Z : EReal) ≤ compVolSlope U x 8 (mixVals Xo c B) Z u) ∧
    -X ≤ (∑ᶠ Z, sl Z) / (Nat.card (Comp Xo c) : ℝ)

def MeanAll (s C : ℝ) : Prop := ∀ (u : AllWt.Weight Dw) (g : ℝ), WtGap u g → MeanGe U x u (bndB u g) (C * errX s u g)

end Generic

def ell (D : D7) : ℝ := Real.log D.host.rdE + |dlogL D 1|

section One

open MvPolynomial Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs

variable {D : D7} (Y : ShimX D.what₂.Tau)

def DeRhamMinusHodgeTateGoodPrimesAt : Prop := ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ),
  p.Prime → p ≠ 2 → UnramE D p → p ∉ Y.lev → ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k →
  ∀ (m : ℕ), m + k = dimFl D.what₂.Tau Y.N + 1 → ∀ Q : MvPolynomial (Vm D.what₂.Tau Y.N) ℝ,
    Q.IsWeightedHomogeneous (wt D.what₂.Tau Y.N) m →
    Y.arMix Sx R p ((tagDR D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k) -
          tagHT D.what₂.Tau _ (C ((Nat.factorial k : ℝ)⁻¹) * pk D _ τ k)) * Q) =
      Real.log p * ((∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          Y.chern (chLie Y.j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) * collapse D _ Q)) -
        Y.chern (chLie Y.j (k - 1) (Sum.inl τ) * collapse D _ Q) / ((p : ℝ) - 1))

def DeRhamHodgeTateDifferenceKilledAt : Prop := ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ), p.Prime →
  ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k → ∀ Q : MvPolynomial (Rt D.what₂.Tau Y.N) ℝ,
    Y.arMix Sx R p (tagHT D.what₂.Tau _ (pk D _ τ k) * (tagDR D.what₂.Tau _ Q - tagHT D.what₂.Tau _ Q)) = 0

end One



section Obj

open GlobalTheory.Mean4 GlobalTheory.Mean4O Formalism.BasicNotions.DV


structure HypothesesH : Prop where
  sieg : GlobalTheory.Published.SiegelToroidalIntegral
  fan : GlobalTheory.Published.ToroidalChartsForFan
  charts : GlobalTheory.Published.ToroidalCharts
  deg : GlobalTheory.Published.ArDegree

end Obj

end GlobalTheory.CovHt

end
end
end
