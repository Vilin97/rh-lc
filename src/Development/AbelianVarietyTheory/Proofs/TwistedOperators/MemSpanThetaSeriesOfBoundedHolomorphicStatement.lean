module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAdelicMatrix
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTrivialAtLevelUnitaryTransportSelfDualStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaAndMultipliers
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLawsStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeriesStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelDatumVectorEqThetaOfTestFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariantStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelThetaSpan
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVectorStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfRationalLevelInvariantAgreeChosenStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormsOfBoundedAdelicFunctionNormBoundedStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReadOffFormsAutomorphicInverseMultiplier
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
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructureStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevelStatement
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReadOffFormsAutomorphicInverseMultiplierStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.readOffForms_automorphic_inverse_multiplier : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g) (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → (∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ, (∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom) → (∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B))) → ∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, F (mapL γ L) (lact γ x) = (μ γ L)⁻¹ * F L x := by
  first | exact @GlobalTheory.Ker.AutRead.read_off_automorphic | exact GlobalTheory.Ker.AutRead.read_off_automorphic | (intros; apply GlobalTheory.Ker.AutRead.read_off_automorphic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesEvalLevelTrivialMulReal

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.EvalAt

theorem theta_eval : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → ∀ B, C.IsB B → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ z : GA D T → ℂ, (∀ a ∈ GinfC T, RealScal C om B a (z a)) → ∀ (t : ℂ) (h : GA D S) (Λ : Lt D.host.E S.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → ∀ (g : GA D T) (L : Lt D.host.E T.rank), g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ∀ a ∈ GinfC T, ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (h, g * a) (C.fvec B (t • C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) Q) 0 = t * ep h * cf g * z a * thP C.X C.hr C.bas C.idx (Lv.phi C.bas hn v₀ L Λ) (C.toH Q) (C.xB (C.mvB a B)) := by
  intro D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB ep cf hep z hz t h Λ hh hht hΛf hhm g L hg hgt hLf hgm a ha Q
  have hΛ0 : C.X.Λ.FG := C.X.Λ_fg
  have hm1 : IsMov (fmt T 1) C.X.Λ C.X.Λ := by rw [GlobalTheory.Ker.Red.fmt_one]; exact GlobalTheory.Ker.Red.isMov_one _
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [GlobalTheory.Ker.Red.fmtC_one]; exact GlobalTheory.Ker.Red.isMov_one _
  obtain ⟨hV, hL⟩ := GlobalTheory.T.self_dual_lattices_at_level D S T C
  have hΛl : C.X.Λ ∈ Lv.lats := (hL Lv 1 _ hΛ0 hm1).2.1 (GlobalTheory.Ker.Red.trivAt_one _ _)
  have hLl : L ∈ Lv.lats := (hL Lv g L hLf hgm).2.1 hgt
  have hsb : ∀ L ∈ Lv.lats, ∀ Λ ∈ Vset D.host.E S.rank M, SW.IsSB (Lv.phi C.bas hn v₀ L Λ) :=
    fun L hL Λ hΛ => (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv
      L hL Λ hΛ).1
  have hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M :=
    hV M 1 _ hM (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1
  have hφ0 := hsb _ hΛl _ hstd
  have hφ := hsb L hLl Λ (hV M h Λ hM hht hΛf hhm)
  have hJ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2
  have hth : ∀ B', C.IsB B' → ∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsTh (C.Th (C.xB B') φ) :=
    fun B' hB' φ hφ => (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ (hJ B' hB').2.1 φ hφ).1.1
  have hmv := (hJ B hB).2.2.2.2.2
  have hBa : C.IsB (C.mvB a B) := (hmv a).1
  have hgB : C.mvB g B = B := (hmv g).2.2.1 hg
  have hcomm : a * g = g * a := (((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T).2.2.2.1 a ha).2.2 g hg
  have p1 : ((h, g * a) : GA D S × GA D T) = (1, a) * (h, g) := by
    rw [Prod.mk_mul_mk, one_mul, hcomm]
  obtain ⟨-, -, e3⟩ := hep h Λ g L hh hht hΛf hhm hg hgt hLf hgm
  rw [(GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) _ (hth B hB _ hφ0) Q).2.2.2.2.1, p1, map_mul, Module.End.mul_apply,
    map_smul, GlobalTheory.Ker.Red.om_fvec C om hW h hh g _ (hth B hB _ hφ0) B hB Q, hgB, e3,
    (GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) _ (hth B hB _ hφ) Q).2.2.2.2.1, map_smul, map_smul,
    GlobalTheory.Ker.Red.om_fvec C om hW 1 (one_mem _) a _ (hth B hB _ hφ) B hB Q, hz a ha _ hφ,
    (GlobalTheory.T.fockPolynomialVector_laws D S T C _ hBa (fun _ => 1) _ (hth _ hBa _ hφ) Q).2.2.2.2.1]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [((GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).2 _ hBa _ hφ).2 Q]
  ring

end GlobalTheory.AdSpan.EvalAt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesEvalLevelTrivialMulRealStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaSeries_eval_levelTrivial_mul_real : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → ∀ B, C.IsB B → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ z : GA D T → ℂ, (∀ a ∈ GinfC T, RealScal C om B a (z a)) → ∀ (t : ℂ) (h : GA D S) (Λ : Lt D.host.E S.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → ∀ (g : GA D T) (L : Lt D.host.E T.rank), g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ∀ a ∈ GinfC T, ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (h, g * a) (C.fvec B (t • C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) Q) 0 = t * ep h * cf g * z a * thP C.X C.hr C.bas C.idx (Lv.phi C.bas hn v₀ L Λ) (C.toH Q) (C.xB (C.mvB a B)) := by
  first | exact @GlobalTheory.AdSpan.EvalAt.theta_eval | exact GlobalTheory.AdSpan.EvalAt.theta_eval | (intros; apply GlobalTheory.AdSpan.EvalAt.theta_eval <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesFockVectorInvariance

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.ThInv

theorem fvec_val_inv : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (h : GA D S) (B : C.Bas), C.IsB B → ∀ u : WO S T → ℂ, C.IsTh u → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, (∀ γ ∈ GQ T, ∀ g, om (h, γ * g) (C.fvec B u Q) 0 = om (h, g) (C.fvec B u Q) 0) ∧ ((∀ k, C.LevK Lv k 1 → om (1, k) u = u) → ∀ k, C.LevK Lv k 1 → ∀ g, om (h, g * k) (C.fvec B u Q) 0 = om (h, g) (C.fvec B u Q) 0) := by
  intro D S T C om hW Lv h B hB u hu Q
  have hth : C.IsTh (C.fvec B u Q) := (GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) u hu Q).1
  refine ⟨fun γ hγ g => ?_, fun hk k hkL g => ?_⟩
  · have p : ((h, γ * g) : GA D S × GA D T) = (1, γ) * (h, g) := by
      rw [Prod.mk_mul_mk, one_mul]
    rw [p, map_mul, Module.End.mul_apply]
    exact hW.om_aut 1 (one_mem _) γ hγ _ (hW.om_pres _ _ hth)
  · have p : ((h, g * k) : GA D S × GA D T) = (h, g) * (1, k) := by
      rw [Prod.mk_mul_mk, mul_one]
    have hmv := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.2.2.2.2 k
    rw [p, map_mul, Module.End.mul_apply, GlobalTheory.Ker.Red.om_fvec C om hW 1 (one_mem _) k u hu B hB Q,
      hmv.2.2.1 hkL.1, hk k hkL]

end GlobalTheory.Ker.ThInv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesFockVectorInvarianceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_series_fock_vector_invariance : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (h : GA D S) (B : C.Bas), C.IsB B → ∀ u : WO S T → ℂ, C.IsTh u → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, (∀ γ ∈ GQ T, ∀ g, om (h, γ * g) (C.fvec B u Q) 0 = om (h, g) (C.fvec B u Q) 0) ∧ ((∀ k, C.LevK Lv k 1 → om (1, k) u = u) → ∀ k, C.LevK Lv k 1 → ∀ g, om (h, g * k) (C.fvec B u Q) 0 = om (h, g) (C.fvec B u Q) 0) := by
  first | exact @GlobalTheory.Ker.ThInv.fvec_val_inv | exact GlobalTheory.Ker.ThInv.fvec_val_inv | (intros; apply GlobalTheory.Ker.ThInv.fvec_val_inv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSpanThetaSeriesOfBoundedHolomorphic

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → 4 * (Module.finrank ℚ D.host.E * T.rank) + 4 ≤ S.rank → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → HolUpTo C B (ThFr.wtOf C.X C.hr c c' S.rank) z φ → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → φ ∈ Submodule.span ℂ (thetaSet C om B (C.uVec Lv hn f') c c') := by
  intro D S T C om hW hsz Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hhol hγ hk hbdd
  obtain ⟨v₀, μ, hv, hμ⟩ := GlobalTheory.SW.exists_vacua_and_multipliers D.host.E T.rank C.X C.g C.bas C.idx S.rank
    C.sympl C.even Lv
  obtain ⟨ep, cf, hep⟩ := GlobalTheory.T.weilPair_levelTrivial_maps_levelVector D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB
  have hm1 : IsMov (fmt T 1) C.X.Λ C.X.Λ := by rw [GlobalTheory.Ker.Red.fmt_one]; exact GlobalTheory.Ker.Red.isMov_one _
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [GlobalTheory.Ker.Red.fmtC_one]; exact GlobalTheory.Ker.Red.isMov_one _
  obtain ⟨hV, hL⟩ := GlobalTheory.T.self_dual_lattices_at_level D S T C
  have hΛl : C.X.Λ ∈ Lv.lats := (hL Lv 1 _ C.X.Λ_fg hm1).2.1 (GlobalTheory.Ker.Red.trivAt_one _ _)
  obtain ⟨t, ht0, hft⟩ := (GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).1 f' hbase (v₀ C.X.Λ) (hv _ hΛl)
  have hu : C.uVec Lv hn f' = t • C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank)) := by
    rw [hft]; exact ((GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).2 v₀ hv).2 t
  have hex : ∀ L : Lt D.host.E T.rank, ∃ g : GA D T, L ∈ Lv.lats →
      g ∈ GfC T ∧ TrivAt T (C.under Lv) g ∧ IsMov (fmt T g) C.X.Λ L := by
    intro L
    by_cases hL' : L ∈ Lv.lats
    · obtain ⟨g, hg, h1, h2⟩ := GlobalTheory.Ker.OntoLat.exists_trivAt_mov D S T C Lv L hL'
      exact ⟨g, fun _ => ⟨hg, h1, h2⟩⟩
    · exact ⟨1, fun h => absurd h hL'⟩
  choose gL hgL using hex
  choose Qf hQd hQb hQv using fun L => hhol (gL L)
  have hne : ∀ L ∈ Lv.lats, ep 1 * cf (gL L) ≠ 0 := by
    intro L hL'
    obtain ⟨g1, g2, -⟩ := hep 1 _ (gL L) L (one_mem _) (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1
      (hgL L hL').1 (hgL L hL').2.1 hL'.1.1 (hgL L hL').2.2
    refine mul_ne_zero ?_ ?_ <;> intro h0
    · rw [h0, norm_zero] at g1; exact zero_ne_one g1
    · rw [h0, norm_zero] at g2; exact zero_ne_one g2
  let F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ := fun L x => Qf L x / (ep 1 * cf (gL L))
  have hFhol : ∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom := fun L _ => by
    show DifferentiableOn ℂ (fun x => Qf L x / (ep 1 * cf (gL L))) C.X.dom
    simpa only [div_eq_mul_inv] using (hQd L).mul_const (ep 1 * cf (gL L))⁻¹
  have hFbor : ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank,
      F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x := by
    intro L _ x hx b hb
    show Qf L (rmul x b) / _ = _ * (Qf L x / _)
    rw [hQb L x hx b hb, mul_div_assoc]
  have hFv : ∀ L ∈ Lv.lats, ∀ a ∈ GinfC T,
      φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B)) := by
    intro L hL' a ha
    show _ = _ * (Qf L _ / _)
    rw [hQv L a ha, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (hne L hL')]
  have hForm : IsForm C.X Lv.grp Lv.lats μ (wtOf C.X C.hr c c' S.rank) F :=
    ⟨hFhol, hFbor, GlobalTheory.T.readOffForms_automorphic_inverse_multiplier D S T C om hW Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hγ hk v₀ μ hv hμ ep cf hep
      gL hgL F hFhol hFbor hFv,
     GlobalTheory.T.forms_of_bounded_adelic_function_norm_bounded D S T C om hW Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hγ hk v₀ μ hv hμ ep cf hep
      gL hgL F hFhol hFbor hFv hbdd⟩
  obtain ⟨m, Λs, P, a, hΛP, hsp⟩ := GlobalTheory.SW.level_theta_span D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx
    S.rank C.sympl C.even hsz Lv hn M hM hM𝔪 v₀ hv μ hμ c c' F hForm
  choose hs hsf hst hsm using fun i => GlobalTheory.T.exists_trivialAtLevel_unitary_transport_selfDual D S T C M hM (Λs i) (hΛP i).1
  have hbij := (GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).1
  let Qs : Fin m → MvPolynomial (FVar D T.rank S.rank) ℂ := fun i => Function.surjInv hbij.2 (P i)
  have hQs : ∀ i, C.toH (Qs i) = P i := fun i => Function.surjInv_eq hbij.2 (P i)
  have hepn : ∀ i, ep (hs i) ≠ 0 := by
    intro i h0
    obtain ⟨g1, -⟩ := hep (hs i) (Λs i) 1 C.X.Λ (hsf i) (hst i) (hΛP i).1.1 (hsm i) (one_mem _)
      (GlobalTheory.Ker.Red.trivAt_one _ _) C.X.Λ_fg hm1
    rw [h0, norm_zero] at g1; exact zero_ne_one g1
  let Θ : Fin m → GA D T → ℂ := fun i g => om (hs i, g) (C.fvec B (C.uVec Lv hn f') (Qs i)) 0
  let ψ : GA D T → ℂ := ∑ i, (a i * ep 1 / (t * ep (hs i))) • Θ i
  have hψ : ∀ g, ψ g = ∑ i, (a i * ep 1 / (t * ep (hs i))) * Θ i g := by
    intro g; simp only [ψ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hψmem : ψ ∈ Submodule.span ℂ (thetaSet C om B (C.uVec Lv hn f') c c') :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨hs i, Qs i, by rw [hQs i]; exact (hΛP i).2, rfl⟩)
  suffices hφψ : φ = ψ by rw [hφψ]; exact hψmem
  set u0 := C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank)) with hu0
  have hJ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2
  have hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M :=
    hV M 1 _ hM (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1
  have hth0 : C.IsTh u0 := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ (hJ B hB).2.1 _
    (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv
      C.X.Λ hΛl _ hstd).1).1.1
  have hΘ : ∀ i g, Θ i g = t * om (hs i, g) (C.fvec B u0 (Qs i)) 0 := by
    intro i g
    show om (hs i, g) (C.fvec B (C.uVec Lv hn f') (Qs i)) 0 = _
    rw [hu, (GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) u0 hth0 (Qs i)).2.2.2.2.1 t, map_smul, Pi.smul_apply,
      smul_eq_mul]
  have hk0 : ∀ k, C.LevK Lv k 1 → om (1, k) u0 = u0 := by
    intro k hk'
    have e := (hk k 1 hk').1
    rw [hu, map_smul] at e
    exact smul_right_injective _ ht0 e
  have hinv := fun i => GlobalTheory.T.theta_series_fock_vector_invariance D S T C om hW Lv (hs i) B hB u0 hth0 (Qs i)
  have hψγ : ∀ γ ∈ GQ T, ∀ g, ψ (γ * g) = ψ g := by
    intro γ hγ' g
    rw [hψ, hψ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΘ, hΘ, (hinv i).1 γ hγ' g]
  have hψk : ∀ k, C.LevK Lv k 1 → ∀ g, ψ (g * k) = ψ g := by
    intro k hk' g
    rw [hψ, hψ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΘ, hΘ, (hinv i).2 hk0 k hk' g]
  have hag : ∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = ψ (gL L * a) := by
    intro L hL' a ha
    have hx : C.xB (C.mvB a B) ∈ C.X.dom := (hJ _ ((hJ B hB).2.2.2.2.2 a).1).2.1
    have hev : ∀ i, Θ i (gL L * a) = t * ep (hs i) * cf (gL L) * z a *
        thP C.X C.hr C.bas C.idx (Lv.phi C.bas hn v₀ L (Λs i)) (P i) (C.xB (C.mvB a B)) := by
      intro i
      show om _ (C.fvec B (C.uVec Lv hn f') _) 0 = _
      rw [hu, GlobalTheory.T.thetaSeries_eval_levelTrivial_mul_real D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB ep cf hep z hz t (hs i) (Λs i) (hsf i) (hst i)
        (hΛP i).1.1 (hsm i) (gL L) L (hgL L hL').1 (hgL L hL').2.1 hL'.1.1 (hgL L hL').2.2 a ha (Qs i), hQs i]
    rw [hFv L hL' a ha, hψ, hsp L hL' _ hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hev i]
    have h1 := hepn i
    field_simp
  exact GlobalTheory.T.eq_of_rational_level_invariant_agree_chosen D S T C Lv M hM hM𝔪 gL hgL φ ψ hγ hψγ (fun k hk' => (hk k 1 hk').2) hψk hag
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSpanThetaSeriesOfBoundedHolomorphicStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_span_thetaSeries_of_boundedHolomorphic : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → 4 * (Module.finrank ℚ D.host.E * T.rank) + 4 ≤ S.rank → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → HolUpTo C B (ThFr.wtOf C.X C.hr c c' S.rank) z φ → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → φ ∈ Submodule.span ℂ (thetaSet C om B (C.uVec Lv hn f') c c') := by
  first | exact @GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo | exact GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo | (intros; apply GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo <;> assumption)
end
end
