module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteCombinationMulLiftByDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
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
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelIntegrableOnUnitaryQuotientStatement
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthIntegralNormKernelBigVertexRouteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AestronglyMeasurableKernelRouteBigVertex

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.BigRoute

theorem theta_of_matched_big : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)} (_ : IsMatched B t ρ i j Θ Θ')
    {d : PureT G (routeBig t i j)} (_ : d ∈ Θ.support),
    IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) d.2 := by
  intro D T L sc G W B ρ t i j Θ Θ' hΘ d hd
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, -, ⟨φ₁, φ₂, hloc, -⟩⟩, rfl, -⟩ := hΘ
  obtain ⟨d₀, hd₀, P, rfl⟩ := GlobalTheory.SmallRoute.mem_support_tensT W hd
  obtain ⟨h1, h2⟩ := hloc d₀ hd₀
  have v1 := ρ.vX_is i (j + 1) i.2 j.2
  have v2 := ρ.vT_is t (i + 1) j i.2 j.2
  have t1 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h1.2 v1.2.theta
  have t2 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h2.2 v2.2.theta
  exact ⟨GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _,
    GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _⟩

theorem continuous_kerBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (_ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    Continuous (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
      kerBig W Θ p.1 g₁ p.2) := by
  intro D T L sc G W B ρ t i j Θ Θ' hΘ g₁
  have hc := W.om_is (.chi (i : ℕ) (j + 1)) ⟨i.2, j.2⟩
  have hm := W.om_is (.mu t ((i : ℕ) + 1) j) ⟨i.2, j.2⟩
  have hK : ∀ d ∈ Θ.support, Continuous (fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
      W.kerA (.right i (j + 1)) d.1.2 q.1 q.2 * W.kerA (.down t (i + 1) j) d.2 q.2 g₁) := by
    intro d hd
    obtain ⟨h1, h2⟩ := theta_of_matched_big hΘ hd
    refine Continuous.mul ?_ ?_
    · show Continuous fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
        thetaKO (W.om (.chi (i : ℕ) (j + 1))) (negGA _ q.2) q.1 d.1.2
      exact (hc.om_cont _ h1 0).comp (((continuous_negGA _).comp continuous_snd).prodMk continuous_fst)
    · show Continuous fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
        thetaKO (W.om (.mu t ((i : ℕ) + 1) j)) g₁ q.2 d.2
      exact (hm.om_cont _ h2 0).comp (continuous_const.prodMk continuous_snd)
  unfold kerBig
  simp only [Finsupp.sum]
  exact continuous_finsetSum _ fun d hd => continuous_const.mul (hK d hd)

theorem aestronglyMeasurable_kerBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) => kerBig W Θ p.1 g₁ p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁
  exact (continuous_kerBig W B ρ t i j Θ Θ' hΘ g₁).aestronglyMeasurable

end GlobalTheory.BigRoute
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AestronglyMeasurableKernelRouteBigVertexStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.aestronglyMeasurable_kernel_route_big_vertex : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) => kerBig W Θ p.1 g₁ p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := by
  first | exact @GlobalTheory.BigRoute.aestronglyMeasurable_kerBig | exact GlobalTheory.BigRoute.aestronglyMeasurable_kerBig | (intros; apply GlobalTheory.BigRoute.aestronglyMeasurable_kerBig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRouteBigVertexRationalLeftInvariant

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigRouteInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem theta_first_of_matched {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)} (hΘ : IsMatched B t ρ i j Θ Θ')
    {d : PureT G (routeBig t i j)} (hd : d ∈ Θ.support) :
    IsThetaFunO W.ψ (G.pS (.chi (i : ℕ) ((j : ℕ) + 1))) (G.pT (.chi (i : ℕ) ((j : ℕ) + 1))) d.1.2 := by
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, -, ⟨φ₁, φ₂, hloc, -⟩⟩, rfl, -⟩ := hΘ
  obtain ⟨d₀, hd₀, P, rfl⟩ := GlobalTheory.SmallRoute.mem_support_tensT W hd
  obtain ⟨h1, -⟩ := hloc d₀ hd₀
  have v1 := ρ.vX_is i (j + 1) i.2 j.2
  have t1 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h1.2 v1.2.theta
  exact GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _

theorem kerBig_rat_mul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g : GA D (G.V (.grid i (j + 1))), kerBig W Θ (γ * g) g₁ = kerBig W Θ g g₁ := by
  intro D T L sc G μ₀ hL W B ρ t i j Θ Θ' hΘ g₁ γ hγ g
  have hc := W.om_is (.chi (i : ℕ) ((j : ℕ) + 1)) ⟨i.2, j.2⟩
  funext u
  unfold kerBig
  refine Finsupp.sum_congr fun d hd => ?_
  have h1 := theta_first_of_matched hΘ hd
  congr 2
  show thetaKO (W.om (.chi (i : ℕ) ((j : ℕ) + 1))) (negGA _ u) (γ * g) d.1.2 =
    thetaKO (W.om (.chi (i : ℕ) ((j : ℕ) + 1))) (negGA _ u) g d.1.2
  unfold thetaKO
  have e : ((negGA _ u, γ * g) : GA D (G.pS (.chi (i : ℕ) ((j : ℕ) + 1))) × GA D (G.pT (.chi (i : ℕ) ((j : ℕ) + 1)))) =
      (1, γ) * (negGA _ u, g) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hc.om_aut 1 (one_mem _) γ hγ _ (hc.om_pres _ _ h1)

end GlobalTheory.BigRouteInv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRouteBigVertexRationalLeftInvariantStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.kernel_route_big_vertex_rational_left_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g : GA D (G.V (.grid i (j + 1))), kerBig W Θ (γ * g) g₁ = kerBig W Θ g g₁ := by
  first | exact @GlobalTheory.BigRouteInv.kerBig_rat_mul | exact GlobalTheory.BigRouteInv.kerBig_rat_mul | (intros; apply GlobalTheory.BigRouteInv.kerBig_rat_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEqIntegralRouteKernelFubini

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigRoute

theorem lift_eq_integral_kerBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hA : TotConv W M _ Θ F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    (∀ᵐ g ∂(M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1))),
      IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1)))) ∧
    liftT W M (routeBig t i j) Θ F g₁ = ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid (i + 1) (j + 1)),
      kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1)) ∂M.ν (.grid i (j + 1)) := by
  intro D T L sc G hWC hK hP μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hA g₁
  classical
  have hσ : ∀ X : Node, X.InRange D.R.m → SigmaFinite (M.ν X) := fun X hX => by
    obtain ⟨h1, h2, -⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D (G.V X)
    haveI := (hM.vtx X hX).haar_fund.1
    infer_instance
  haveI := hσ (.grid i (j + 1)) ⟨i.2.le, j.2⟩
  haveI := hσ (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩
  have hK1 : ∀ g, IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1))) := GlobalTheory.T.bigRoute_kernel_integrableOn_unitary_quotient hWC hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  have hmeas : AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
      kerBig W Θ p.1 g₁ p.2) (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
        ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := GlobalTheory.T.aestronglyMeasurable_kernel_route_big_vertex hL W B ρ t i j M hM Θ Θ' hΘ g₁
  have hinv : ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g, kerBig W Θ (γ * g) g₁ = kerBig W Θ g g₁ := GlobalTheory.T.kernel_route_big_vertex_rational_left_invariant hL W B ρ t i j Θ Θ' hΘ g₁
  have hgrow : GlobalTheory.Grow.ModGrowth (G.V (.grid i (j + 1))) (fun g => ∫ u in M.fd (.grid (i + 1) (j + 1)),
      ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1))) := GlobalTheory.T.moderateGrowth_integral_norm_kernel_bigVertexRoute hWC hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  have hRD : GlobalTheory.Grow.RapidDec _ F := GlobalTheory.Grow.rapidDec_of_cuspForm (GlobalTheory.Grow.cuspRapidDecay_of_bound hP) W.θ_is hF hFc
  obtain ⟨hH, hfd⟩ := (hM.vtx (.grid i (j + 1)) ⟨i.2.le, j.2⟩).haar_fund
  have hkm : AEStronglyMeasurable (fun g => ((∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖
      ∂M.ν (.grid (i + 1) (j + 1)) : ℝ) : ℂ)) ((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hmeas.norm.integral_prod_right'
  obtain ⟨C, A, hCA⟩ := hgrow
  have hkb : ∀ g, ‖((∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1)) : ℝ) : ℂ)‖ ≤
      C * 2 ^ A * GlobalTheory.Grow.quotHeight _ g ^ A := fun g => by
    rw [Complex.norm_real]
    exact GlobalTheory.Grow.norm_le_quotHeight_pow (fun γ hγ g => by simp only [hinv γ hγ g]) hCA g
  have hkF := hRD.integrableOn_mul_of_le hH hfd hkm hkb
  have hJ : Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) => F p.1 * kerBig W Θ p.1 g₁ p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
        ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := by
    have hFm : AEStronglyMeasurable F ((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))) :=
      hRD.continuous.aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
        F p.1 * kerBig W Θ p.1 g₁ p.2) (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
          ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) :=
      hFm.comp_fst.mul hmeas
    refine (integrable_prod_iff hm2).2
      ⟨.of_forall fun g => (hK1 g).const_mul (F g), ?_⟩
    refine hkF.norm.congr (.of_forall fun g => ?_)
    simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, integral_const_mul]
    rw [abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), mul_comm]
  refine ⟨Filter.Eventually.of_forall hK1, ?_⟩
  have hpt : ∀ u, ∫ g in M.fd (.grid i (j + 1)), F g * kerBig W Θ g g₁ u ∂M.ν (.grid i (j + 1)) =
      Θ.sum fun d c => c * (W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1))) := by
    intro u
    have hint : ∀ d ∈ Θ.support, IntegrableOn (fun g => W.kerA (.right i (j + 1)) d.1.2 g u * F g)
        (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1))) := fun d hd => (hA d hd).1.2 u
    have e : ∀ g, F g * kerBig W Θ g g₁ u = ∑ d ∈ Θ.support,
        Θ d * (W.kerA (.down t (i + 1) j) d.2 u g₁ * (W.kerA (.right i (j + 1)) d.1.2 g u * F g)) := by
      intro g
      simp only [kerBig, Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    simp_rw [e]
    rw [integral_finsetSum _ fun d hd => ((hint d hd).const_mul _).const_mul _]
    simp only [integral_const_mul, Finsupp.sum]
  have hint2 : ∀ d ∈ Θ.support, Integrable (fun u => W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1)))
      ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1)))) := fun d hd => (hA d hd).2 g₁
  symm
  calc ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid (i + 1) (j + 1)), kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1))
        ∂M.ν (.grid i (j + 1))
      = ∫ g in M.fd (.grid i (j + 1)), ∫ u in M.fd (.grid (i + 1) (j + 1)), F g * kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1))
        ∂M.ν (.grid i (j + 1)) := by simp_rw [integral_const_mul]
    _ = ∫ u in M.fd (.grid (i + 1) (j + 1)), ∫ g in M.fd (.grid i (j + 1)), F g * kerBig W Θ g g₁ u
        ∂M.ν (.grid i (j + 1)) ∂M.ν (.grid (i + 1) (j + 1)) := integral_integral_swap hJ
    _ = ∫ u in M.fd (.grid (i + 1) (j + 1)), (Θ.sum fun d c => c * (W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1))))
        ∂M.ν (.grid (i + 1) (j + 1)) := by
        simp_rw [hpt]
    _ = _ := by
        simp only [Finsupp.sum]
        rw [integral_finsetSum _ fun d hd => (hint2 d hd).const_mul _]
        simp_rw [integral_const_mul]
        simp only [liftT, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rfl

end GlobalTheory.BigRoute

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEqIntegralRouteKernelFubiniStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.thetaLift_eq_integral_routeKernel_fubini : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hA : TotConv W M _ Θ F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    (∀ᵐ g ∂(M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1))),
      IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1)))) ∧
    liftT W M (routeBig t i j) Θ F g₁ = ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid (i + 1) (j + 1)),
      kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1)) ∂M.ν (.grid i (j + 1)) := by
  first | exact @GlobalTheory.BigRoute.lift_eq_integral_kerBig | exact GlobalTheory.BigRoute.lift_eq_integral_kerBig | (intros; apply GlobalTheory.BigRoute.lift_eq_integral_kerBig <;> assumption)
end
end
