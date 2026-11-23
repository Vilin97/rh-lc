module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionRankLowerBoundOfHilbertSamuelStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsIdealSpMapClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageDegEqDel
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelRankDegreeShareLe

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

theorem share_le_of_rankLow (h : RankLow) (F : Type) [Field F] [NumberField F] (X : Data F)
    (hn : IsNef F X.LA) (hb : IsBig F X.LA) : (X.R : ℤ) * X.del ≤ X.d := by
  refine (h F X.toGeo hn hb X.T).trans ?_
  rw [X.d_eq_finrank]
  exact_mod_cast Submodule.finrank_mono (X.global_le X.T le_rfl)

theorem share_le : Quoted → ∀ (F : Type) [Field F] [NumberField F] (X : Data F),
    IsNef F X.LA → IsBig F X.LA → (X.R : ℤ) * X.del ≤ X.d :=
  fun q => share_le_of_rankLow (GlobalTheory.T.globalSectionRankLowerBound_of_hilbertSamuel q)

end GlobalTheory.HSCore
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelRankDegreeShareLeStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

theorem _root_.GlobalTheory.T.arithHilbertSamuel_rankDegree_share_le : Quoted → ∀ (F : Type) [Field F] [NumberField F] (X : Data F), IsNef F X.LA → IsBig F X.LA → (X.R : ℤ) * X.del ≤ X.d := by
  first | exact @GlobalTheory.HSCore.share_le | exact GlobalTheory.HSCore.share_le | (intros; apply GlobalTheory.HSCore.share_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseMulComponentDegreeLeDimension

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

set_option autoImplicit false

namespace GlobalTheory.HSCore.CompShare

theorem share_of_data {F : Type} [Field F] [NumberField F] (X : Data F) {D δ T d : ℕ} (hD : X.D = D) (hT : X.T = T)
    (hd : X.d = d) (hδ : (δ : ℤ) = X.del) (h : (X.R : ℤ) * X.del ≤ X.d) : (T - 1).choose D * δ ≤ d := by
  subst hD hT hd
  rw [← hδ] at h
  exact_mod_cast h

theorem choose_mul_compDeg_le : Quoted → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : CompHS.WtPar Dw) (R : CompHS.Choice X Z U P) (ω : CompHS.CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : CompHS.Ready R ω x V dict) (f₁ : CompHS.CuspFrame Z U x V dict P.u₁) (f₂ : CompHS.CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : CompHS.Consts), IsNef c.F (h.data f₁ f₂ th k).LA → IsBig c.F (h.data f₁ f₂ th k).LA → (h.data f₁ f₂ th k).Birational → (P.T - 1).choose (CompHt.dimFlag Dw) * CompHt.compDeg U Z (AllWt.wtOf Dw P.u₁ 0) ≤ Module.finrank c.F (AllWt.cuspOn U Z (AllWt.wtOf Dw (P.wt P.T) 0)) := by
  intro hQ E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k hn hb hB
  have hp := GlobalTheory.CompHS.compPresents_data E H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k
  have hD : (h.data f₁ f₂ th k).D = CompHt.dimFlag Dw := hp.1
  have e := GlobalTheory.HSCore.ImageDegree.imageDeg_eq_del hQ c.F (h.data f₁ f₂ th k).toTuple _ _ _ _ _
    (h.data f₁ f₂ th k).geom hB hp.2
  refine share_of_data (h.data f₁ f₂ th k) hD rfl (h.d_eq f₁ f₂ th k) ?_ (GlobalTheory.T.arithHilbertSamuel_rankDegree_share_le hQ c.F _ hn hb)
  rw [← e, CompHt.compDeg, ← hD]

end GlobalTheory.HSCore.CompShare
end
end
