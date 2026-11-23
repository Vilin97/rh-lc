module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralGeneratorOfChartPointCdvr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FramedPointVectorsIntegralInCell
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralGeneratorOfChartPointCdvrStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.exists_integralGenerator_of_chartPoint_cdvr : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V), letI := io.toAlgebra; ∀ (x : Sp T.Fr ⟶ Xo.X) (s : LB.Sec (PPx x)) (Λ : M.Lift ((algebraMap T.V T.Fr).comp f₀) x), Λ.ThTie s → ∀ (G : SAB H (Sp T.V)) (m : SABMap G Y.t (spMap f₀ ≫ M.hU.fromSpec)) (m2 : SABMap Λ.t' G (spMap (algebraMap T.V T.Fr))), m2.φ ≫ m.φ = Λ.m2.φ → ∃ θ : LB.Sec G.PP.L, (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left (le_top : G.PP.L.U i ≤ ⊤) ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧ ∃ (w1 : LB.Iso Λ.t'.PP.L (Xo.univ.t.PP.L.pull Λ.m1.φ)) (w2 : LB.Iso Λ.t'.PP.L (G.PP.L.pull m2.φ)) (σ : LB.Sec Λ.t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull Λ.m1.φ)) (θ2 : LB.Sec (G.PP.L.pull m2.φ)), RigIso Λ.m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧ ∀ g : Λ.t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = Λ.m1.φ → g ≫ (fst (Over.mk x) Xo.univ.t.G).left = Λ.t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit)) := by
  first | exact @GlobalTheory.Reg.exists_generator_of_thTie | exact GlobalTheory.Reg.exists_generator_of_thTie | (intros; apply GlobalTheory.Reg.exists_generator_of_thTie <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.FramedPointVectorsIntegralInCellStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.framedPoint_vectors_integral_in_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ (z : FrPt Xo c T.Fr) (Λ : M.Lift ((algebraMap T.V T.Fr).comp f₀) z.x), Λ.LieTie (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z.u → ∀ (G : SAB H (Sp T.V)) (m : SABMap G Y.t (spMap f₀ ≫ M.hU.fromSpec)) (m2 : SABMap Λ.t' G (spMap (algebraMap T.V T.Fr))), m2.φ ≫ m.φ = Λ.m2.φ → ∃ ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G), (∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ Λ.t'.G.left, u' ≫ Λ.m1.φ = z.u τ i ∧ u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left := by
  first | exact @GlobalTheory.Reg.tie_vectors_integral | exact GlobalTheory.Reg.tie_vectors_integral | (intros; apply GlobalTheory.Reg.tie_vectors_integral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.TieIntegral

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem tie_integral : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ z : FrPt Xo c T.Fr, M.Comparison₂ ((algebraMap T.V T.Fr).comp f₀) (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z → Integral T io z := by
  intro hS E _ _ _ H Dw l Xo c O _ β Y M hP T io f₀ ix u₀ hu
  letI := io.toAlgebra
  intro z ⟨Λ, hL, hT⟩
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap f₀ ≫ M.hU.fromSpec) Y.t
  have e : spMap ((algebraMap T.V T.Fr).comp f₀) ≫ M.hU.fromSpec =
      spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec := by
    rw [← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    rfl
  have key : ∀ (g : Sp T.Fr ⟶ Y.X) (n : SABMap Λ.t' Y.t g),
      g = spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec →
      ∃ m2 : SABMap Λ.t' _ (spMap (algebraMap T.V T.Fr)), m2.φ ≫ m.φ = n.φ := by
    intro g n hg
    subst hg
    obtain ⟨m2, h⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n
    exact ⟨m2, h.symm⟩
  obtain ⟨m2, h2⟩ := key _ Λ.m2 e
  exact ⟨_, Λ.t', Λ.m1, m2,
    GlobalTheory.T.framedPoint_vectors_integral_in_cell E H Dw l Xo c O β Y M T io f₀ ix u₀ hu z Λ hL _ m m2 h2,
    GlobalTheory.T.exists_integralGenerator_of_chartPoint_cdvr hS E H Dw l Xo c O β Y M hP T io f₀ z.x z.s Λ hT _ m m2 h2⟩

end GlobalTheory.Reg
end
end
end
