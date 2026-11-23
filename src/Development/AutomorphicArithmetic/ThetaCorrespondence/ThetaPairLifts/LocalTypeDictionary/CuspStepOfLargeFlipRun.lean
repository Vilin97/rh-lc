module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryPrimeLtFirstTypePrimeOfSizes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumLatticeSameLatticedSpace
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalAlongRightGridArrows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspTypedTestGridIffSenderGridConjStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorDownwardArrow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridMeasureDomainDownwardEqSenderStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspidalLiftSmoothAtOfCuspidalLift

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalAlongDownGridArrows

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipRun

theorem ga_eq_of_match {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
    {G' : GridData R.toLevCh sc} {W : G'.Weil} {G : GlobalTheory.Grid.GridPre R} (hM : GlobalTheory.GridJoin.Match G W) {i j : ℕ}
    (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : GA D (G.V i j).V = GA D (G'.V (.grid i j)) := by
  obtain ⟨L, h1, h2, e⟩ := (hM.1.vert i j hi hj).sp
  rw [e]; rfl

end GlobalTheory.FlipRun
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaFunctionFockVectorDownwardArrowStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.isThetaFunction_fock_vector_downward_arrow : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (ρ : RealMatch W)
    (t : T) (i j : ℕ), i ≤ D.R.m → j < D.R.m → ∀ {e : AE D}, IsIdemSum e (locPl G t) →
    ∀ {φ f : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ}, IsLocVec W (.mu t i j) e (vacOf ρ (.down t i j)) φ f →
    ∀ Q : PolF D (G.pT (.mu t i j)).rank (G.pS (.mu t i j)).rank,
      IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) (W.fock (.mu t i j) f Q) := by
  first | exact @GlobalTheory.DownFock.isThetaFunO_fock_down | exact GlobalTheory.DownFock.isThetaFunO_fock_down | (intros; apply GlobalTheory.DownFock.isThetaFunO_fock_down <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardArrowLeftInvariant

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.DownKer

theorem kerA_down_left_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : ℕ),
    i ≤ D.R.m → j < D.R.m → ∀ Ψ : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ,
    IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) Ψ → ∀ h : GA D (G.V (.grid i j)),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g, W.kerA (.down t i j) Ψ (γ * g) h = W.kerA (.down t i j) Ψ g h := by
  intro D T L sc G W t i j hi hj Ψ hΨ h γ hγ g
  have hR : (Pair.mu t i j : Pair T).InRange D.R.m := ⟨hi, hj⟩
  have hw := W.om_is (.mu t i j) hR
  show (W.om (.mu t i j)) (h, γ * g) Ψ 0 = (W.om (.mu t i j)) (h, g) Ψ 0
  have e : ((h, γ * g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (1, γ) * (h, g) := by
    simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hw.om_aut 1 (one_mem _) γ hγ _ (hw.om_pres _ _ hΨ)

end GlobalTheory.DownKer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardArrowLeftInvariantStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.thetaKernel_downward_arrow_left_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : ℕ),
    i ≤ D.R.m → j < D.R.m → ∀ Ψ : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ,
    IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) Ψ → ∀ h : GA D (G.V (.grid i j)),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g, W.kerA (.down t i j) Ψ (γ * g) h = W.kerA (.down t i j) Ψ g h := by
  first | exact @GlobalTheory.DownKer.kerA_down_left_inv | exact GlobalTheory.DownKer.kerA_down_left_inv | (intros; apply GlobalTheory.DownKer.kerA_down_left_inv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardTestGridEqSenderGrid

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipDown

theorem kernel_down : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
    {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (t : T) (i j : ℕ), i ≤ D.R.m → j < D.R.m →
    ∀ (eA : GA D (G.V i (j + 1)).V = GA D (G'.V (.grid i (j + 1)))) (eB : GA D (G.V i j).V = GA D (G'.V (.grid i j)))
    (Ψ : WO (G'.pS (.mu t i j)) (G'.pT (.mu t i j)) → ℂ), IsThetaFunO W.ψ (G'.pS (.mu t i j)) (G'.pT (.mu t i j)) Ψ →
    ∃ Φ : WO (G.V i j).V (G.V i (j + 1)).V → ℂ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ ∧
      ∀ h g, thetaKO (G.th t i j).ω h g Φ = W.kerA (.down t i j) Ψ (cast eA g) (cast eB h) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W hW G hG hM t i j hi hj eA eB Ψ hΨ
  obtain ⟨L1, a1, b1, e1⟩ := (hM.1.vert i j hi (by omega)).sp
  obtain ⟨L2, a2, b2, e2⟩ := (hM.1.vert i (j + 1) hi (by omega)).sp
  have hω := hM.2.omT t i j hi hj
  revert eA eB hω
  generalize (G.th t i j).ω = ω
  revert ω
  generalize (G.V i j).V = S at e1 ⊢
  generalize (G.V i (j + 1)).V = U at e2 ⊢
  subst e1 e2
  intro ω eA eB hω
  have hω' : ω = W.om (.mu t i j) := eq_of_heq hω
  subst hω'
  refine ⟨Ψ, ?_, fun h g => rfl⟩
  rw [← hW.ψ]
  exact ⟨hΨ.1, hΨ.2, hΨ.3, hΨ.4⟩

end GlobalTheory.FlipDown
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelDownwardTestGridEqSenderGridStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.thetaKernel_downward_testGrid_eq_sender_grid : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
    {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → GlobalTheory.GridJoin.Match G W →
    ∀ (t : T) (i j : ℕ), i ≤ D.R.m → j < D.R.m →
    ∀ (eA : GA D (G.V i (j + 1)).V = GA D (G'.V (.grid i (j + 1)))) (eB : GA D (G.V i j).V = GA D (G'.V (.grid i j)))
    (Ψ : WO (G'.pS (.mu t i j)) (G'.pT (.mu t i j)) → ℂ), IsThetaFunO W.ψ (G'.pS (.mu t i j)) (G'.pT (.mu t i j)) Ψ →
    ∃ Φ : WO (G.V i j).V (G.V i (j + 1)).V → ℂ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ ∧
      ∀ h g, thetaKO (G.th t i j).ω h g Φ = W.kerA (.down t i j) Ψ (cast eA g) (cast eB h) := by
  first | exact @GlobalTheory.FlipDown.kernel_down | exact GlobalTheory.FlipDown.kernel_down | (intros; apply GlobalTheory.FlipDown.kernel_down <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspStepOfLargeFlipRun

section

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FlipRun
theorem cuspStep_of_large_flipRun : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (M : Vol ch.G), M.Is t → GlobalTheory.FlipRun.CuspStep ch.W M ch.rm t := by
  intro hLC hP
  have hS := _root_.GlobalTheory.T.cuspidal_lift_smooth_at_cusps hLC hP
  have hRight : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
    ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.right i j) →
      ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
      ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
        LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
    intro hLS hP
    refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch hch hsc => ?_⟩⟩
    intro t M hM a ha hr e he φ f hf Q F' hF
    obtain ⟨i, j, rfl⟩ := hr
    obtain ⟨i', j', hi, hj, h'⟩ | ⟨_, _, _, _, _, h'⟩ := ha
    · cases h'
      have hcg : ch.sc.cGap = 1 := by rw [hsc]
      obtain ⟨G, hG, hMa⟩ := GlobalTheory.GridJoin.exists_gridPre hP.discreteSeriesUpqExists hP.discreteSeriesCover
        hP.harishChandraModules hSet.host hSet.size hSet.core hcg ch.W hch.weil
      have hRB : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R :=
        ⟨hSet.core.lev, hSet.core.models.inf, hSet.core.models.νY, hSet.core.models.νY', hSet.core.models.νX⟩
      have hSm := (hLS D (GlobalTheory.RowSizes.sizes_of_sizeRows large₂ hSet.size) Γ Pl0 T A Ks R G hRB hG).X t i j hi hj
      have hgm := GlobalTheory.RightArrowCusp.meas_haar_fund hSet.core G hG t i j hi.le hj
      exact GlobalTheory.RightArrowCusp.lift_right_of_smooth hcg ch.W hch.weil ch.rm hch.vac M t hM i j hi hj (G.V i j) (G.V (i + 1) j)
        (hMa.1.vert i j hi.le hj).sp (hMa.1.vert (i + 1) j hi hj).sp (GlobalTheory.RightArrowCusp.vert_par hSet.core G hG i j hi.le hj)
        (GlobalTheory.RightArrowCusp.vert_par hSet.core G hG (i + 1) j hi hj) (G.meas t i j) hgm.1 hgm.2 (G.X i j).ω (hMa.2.omX i j hi hj) hSm
        e he φ f hf Q F' hF
  have hDown : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
    ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.down t i j) →
      ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
      ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
        LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
    intro hS hP
    refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
    intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hset ch hch hsc t M hMt a ha hdown e he φ f hf Q Fn hFn
    obtain ⟨i, j, rfl⟩ := hdown
    have hgap : ch.sc.cGap = 1 := by rw [hsc]
    obtain ⟨hi, hj⟩ : i ≤ D.R.m ∧ j < D.R.m := by
      rcases ha with ⟨_, _, _, _, h⟩ | ⟨i', j', h1, h2, h⟩
      · cases h
      · cases h; exact ⟨h1, h2⟩
    obtain ⟨G, hG, hMa⟩ := GlobalTheory.GridJoin.exists_gridPre hP.discreteSeriesUpqExists hP.discreteSeriesCover
      hP.harishChandraModules hset.host hset.size hset.core hgap ch.W hch.weil
    have hRB : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R :=
      ⟨hset.core.lev, hset.core.models.inf, hset.core.models.νY, hset.core.models.νY', hset.core.models.νX⟩
    have hCS := hS D (GlobalTheory.RowSizes.sizes_of_sizeRows large₂ hset.size) Γ Pl0 T A Ks R G hRB hG
    have eA := ga_eq_of_match hMa hi (Nat.succ_le_of_lt hj)
    have eB := ga_eq_of_match hMa hi hj.le
    have hΨ := GlobalTheory.T.isThetaFunction_fock_vector_downward_arrow ch.rm t i j hi hj he hf Q
    obtain ⟨Φ, hΦ, hK⟩ := GlobalTheory.T.thetaKernel_downward_testGrid_eq_sender_grid ch.W hch.weil G hG hMa t i j hi hj eA eB _ hΨ
    have hF' := (GlobalTheory.T.isCuspTyped_testGrid_iff_sender_grid_conj hset hgap ch.W hch.weil G hG hMa i (j + 1) hi (Nat.succ_le_of_lt hj) eA Fn).1 hFn
    obtain ⟨hint, hcusp⟩ := hCS.th t i j hi hj Φ hΦ _ hF'
    have hθ : ch.W.θ = R.θ := hch.weil.θ
    have hinv : ∀ h, ∀ γ ∈ GQ (ch.G.V (.grid i (j + 1))), ∀ g,
        (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) (γ * g) =
        (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) g := fun h γ hγ g => by
      simp only [GlobalTheory.T.thetaKernel_downward_arrow_left_invariant ch.W t i j hi hj _ hΨ h γ hγ g, hFn.1.toIsAutFun.left γ hγ g]
    have key := fun h => GlobalTheory.T.testGrid_measure_domain_downward_eq_sender hset hgap ch.W hch.weil G hG hMa M t hMt i j hi hj eA
      (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) (hinv h)
    have hcb : ∀ h : GA D (ch.G.V (.grid i j)), cast eB (cast eB.symm h) = h := fun h => cast_cast _ _ h
    refine ⟨fun h => ?_, ?_⟩
    · rw [← hcb h]
      refine (key _).1.1 ?_
      simpa only [hK] using hint (cast eB.symm h)
    · refine (GlobalTheory.T.isCuspTyped_testGrid_iff_sender_grid_conj hset hgap ch.W hch.weil G hG hMa i j hi hj.le eB _).2 ?_
      convert hcusp using 2 with h
      rw [liftA_apply, ← (key _).2]
      simp only [hK]
  refine (GlobalTheory.RowClaim.Big.and (hRight hS hP) (hDown hS hP)).imp fun CF0 h ε CF hC => ?_
  obtain ⟨x₀, h⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc t M hM a ha e' he φ f hf Q F' hF => ?_⟩
  have H := h D large₂ e hx Γ Pl0 T A Ks R F s ch hch hsc
  rcases ha with ⟨i, j, hi, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · exact H.1 t M hM _ (Or.inl ⟨i, j, hi, hj, rfl⟩) ⟨i, j, rfl⟩ e' he φ f hf Q F' hF
  · exact H.2 t M hM _ (Or.inr ⟨i, j, hi, hj, rfl⟩) ⟨i, j, rfl⟩ e' he φ f hf Q F' hF
end GlobalTheory.FlipRun
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.flipRun_cusp_transition : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (M : Vol ch.G), M.Is t → GlobalTheory.FlipRun.CuspStep ch.W M ch.rm t := by
  first | exact @_root_.GlobalTheory.FlipRun.cuspStep_of_large_flipRun | exact _root_.GlobalTheory.FlipRun.cuspStep_of_large_flipRun | (intros; apply _root_.GlobalTheory.FlipRun.cuspStep_of_large_flipRun <;> assumption)
end
end
end
