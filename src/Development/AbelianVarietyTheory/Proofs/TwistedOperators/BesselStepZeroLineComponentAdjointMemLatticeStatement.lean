module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewAdjointMemAdjointHomLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapPreservesVacuumProof
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepLineComponentMemHomLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLeSelfDualHomLatticeShift
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLeSelfDualHomLatticeShiftStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSelfDualLatticeOfMemAllLatticeCompletions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarSmulMemSpanModulusDivConjugateLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittCoreProjectionMemLatticeOfSplits
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarAdjointMemHatLattice
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFirstStepAdjointLineComponentMemLatO

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin



noncomputable section

namespace GlobalTheory.LineAdjZero

open GlobalTheory.AdjLatO GlobalTheory.LineCompLat

variable {D : D7}

theorem genT_smul_left (T : HSp D) {n : ℕ} (x : AF D.host.F) (c : D.host.E) (t : Fin T.rank → D.host.E)
    (u : Fin n → D.host.E) : genT T x (c • t) u = genT T x t (star c • u) := by
  ext p q
  simp only [genT, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem genT_add_left (T : HSp D) {n : ℕ} (x : AF D.host.F) (t t' : Fin T.rank → D.host.E)
    (u : Fin n → D.host.E) : genT T x (t + t') u = genT T x t u + genT T x t' u := by
  ext p q
  simp only [genT, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib, mul_add,
    TensorProduct.tmul_add]

theorem genT_zero_left (T : HSp D) {n : ℕ} (x : AF D.host.F) (u : Fin n → D.host.E) :
    genT T x 0 u = 0 := by
  ext p q
  simp [genT]

theorem latO_idLat_le (S T : HSp D) (LS : Lat S) (LT : Lat T) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (hI : ∀ σ ∈ I, ∀ τ ∈ I, ∃ c : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E c = star σ * τ) (P : GlobalTheory.FinPl.Pl D → Prop) :
    latO S T (idLat I LS : Set _) (idLat I LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  have hσ : ∀ σ ∈ I, ∀ t ∈ idLat I LT, star σ • t ∈ LT := by
    intro σ hσ t ht
    unfold idLat at ht
    induction ht using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨τ, hτ, y, hy, rfl⟩ := hz
      obtain ⟨c, hc⟩ := hI σ hσ τ hτ
      rw [smul_smul, ← hc, algebraMap_smul]
      exact LT.smul_mem c hy
    | zero => rw [smul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [smul_comm]; exact LT.smul_mem r hy
  have key : ∀ t ∈ idLat I LT, genT S (pairA D.host.F 0 α) s (a • t) ∈ latO S T (LS : Set _) (LT : Set _) P := by
    have hs' : s ∈ Submodule.span (𝓞 D.host.E) {z | ∃ s ∈ I, ∃ y ∈ LS, z = s • y} := hs
    clear hs
    induction hs' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨σ, hσI, y, hy, rfl⟩ := hz
      intro t ht
      rw [genT_smul_left, smul_comm]
      exact genT_mem_of_mem_span T S LT LS P α hα hP y hy _
        (Submodule.subset_span ⟨a, ha, _, hσ σ hσI t ht, rfl⟩)
    | zero => intro t _; rw [genT_zero_left]; exact zero_mem _
    | add y z _ _ hy hz => intro t ht; rw [genT_add_left]; exact add_mem (hy t ht) (hz t ht)
    | smul r y _ hy =>
      intro t ht
      obtain ⟨r', hr'⟩ := GlobalTheory.FinPl.LatMem.star_int r
      have e1 : r • y = (r : D.host.E) • y := (algebraMap_smul D.host.E r y).symm
      have e2 : (r' : D.host.E) • t = r' • t := algebraMap_smul D.host.E r' t
      rw [e1, genT_smul_left, smul_comm, ← hr', e2]
      exact hy _ (Submodule.smul_mem _ r' ht)
  exact key t ht

theorem star_mul_shiftId {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    ∀ σ ∈ shiftId G, ∀ τ ∈ shiftId G, ∃ c : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E c = star σ * τ := by
  intro σ hσ τ hτ
  have h1 : star σ ∈ (shiftId G)⁻¹ := by
    rw [← GlobalTheory.RowBig.conjFI_shiftId, GlobalTheory.SeeSaw.mem_conjFI, ← Formalism.BasicNotions.bridge_star_holds D.R D.host, star_star]
    exact hσ
  have h2 := FractionalIdeal.mul_mem_mul h1 hτ
  rw [inv_mul_cancel₀ (GlobalTheory.RowBig.shiftId_ne_zero G)] at h2
  exact (FractionalIdeal.mem_one_iff _).1 h2

theorem mulVec_idLat {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (hM : ∀ x ∈ Λ, M *ᵥ x ∈ Λ')
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ∀ x ∈ idLat I Λ, M *ᵥ x ∈ idLat I Λ' := by
  intro x hx
  unfold idLat at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨τ, hτ, y, hy, rfl⟩ := hz
    rw [Matrix.mulVec_smul]
    exact Submodule.subset_span ⟨τ, hτ, _, hM y hy, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | smul r y _ hy => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ r hy

theorem lineComp_mem_shift : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 ∈ latO (negSp F.Lz) (G.V (.core (2 * ρ + 1))) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) : Set _) (idLat (shiftId G) (G.Λ (.core (2 * ρ + 1))) : Set _) fun _ => True := by
  intro D hD T L μ0 hL sc G W Mv hM F hF ρ h u hu
  obtain ⟨hsd0, hloc, hsdM, horth⟩ := (GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W Mv hM F hF).2.1 ρ h
  have sdV : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) :=
    (G.sp.V_is (2 * ρ + 1 + 1) 0 (by omega) h (by omega)).sd
  have sdC : IsSelfDualC (G.V (.core (2 * ρ + 1))) (G.Λ (.core (2 * ρ + 1))) :=
    (G.sp.P_is (2 * ρ + 1) (by omega)).sd
  have sdC' := GlobalTheory.RowBig.isSelfDualC_idLat_shiftId G _ sdC
  have hU1 : (F.dJ ρ h).j0 * u * (F.dB ρ h).p0 ∈ latRow G (2 * ρ + 1) := hu
  have hU : (F.dJ ρ h).j0 * u * (F.dB ρ h).p0 ∈ latO (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 1 + 1) 0) : Set _) (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) fun _ => True :=
    GlobalTheory.T.depthLatticeGridRow_le_selfDualHomLatticeShift D hD T L μ0 hL sc G W Mv hM (2 * ρ + 1) (by omega) (by omega) hU1
  clear hU1 hu
  have hq : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), (F.dJ ρ h).q0 *ᵥ t ∈ G.Λ (.core (2 * ρ + 1)) :=
    GlobalTheory.FinPl.CoreProj.wittCoreProjection_mem_lattice_of_splits (F.dJ ρ h) (GlobalTheory.FinPl.LocGlob.mem_of_mem_latV_all sdC) fun v => (hloc v).2
  have hu' : u = (F.dJ ρ h).p0 * ((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) * (F.dB ρ h).j0 := by
    simp only [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    rw [Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [OrthDec.resS_apply]
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ hsdM sdC' _ _).2 ⟨?_, fun z hz => ?_⟩
  · rw [hu']
    exact mxAt_mul_right (mxAt_mul_right (mxAt_mul_left _ (GlobalTheory.FinPl.LatMem.latO_mxAt hU)) _) _
  have h1 : (F.oB ρ h).jB *ᵥ z ∈ latV (F.V₀ ρ) (lat0 F ρ h) fun _ => True := by
    refine GlobalTheory.FinPl.FlatVacuum.mulVec_latV_of_local hsdM.1 hsd0.1 (F.oB ρ h).jB (fun v _ y hy => ?_) hz
    refine ((horth v) _).2 ⟨?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, OrthDec.pA_jB, Matrix.zero_mulVec]; exact zero_mem _
    · rw [Matrix.mulVec_mulVec, OrthDec.pB_jB, Matrix.one_mulVec]; exact hy
  have h2 : (F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z) ∈
      latV (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) fun _ => True :=
    rat_mulVec_latV (F.dB ρ h).i₀ (fun x hx => hx) h1
  have h3 := GlobalTheory.FinPl.LatMem.latO_maps sdV hU h2
  have h4 : (F.dJ ρ h).p0 *ᵥ (((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) *ᵥ ((F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z))) ∈
      latA _ (idLat (shiftId G) (G.Λ (.core (2 * ρ + 1)))) fun _ => True := by
    refine GlobalTheory.FinPl.FlatVacuum.mulVec_latA (F.dJ ρ h).p0 (fun y hy => ?_) h3
    exact rat_mulVec_latV (F.dJ ρ h).q0 (mulVec_idLat _ hq _) hy
  have e : (F.dJ ρ h).p0 *ᵥ (((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) *ᵥ ((F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z))) =
      (u * (F.oB ρ h).jB) *ᵥ z := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    rw [Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [← e]
  exact h4

theorem adj_lineComp_mem_latO : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2) ∈ latO (G.V (.core (2 * 0 + 1))) (negSp F.Lz) (G.Λ (.core (2 * 0 + 1)) : Set _) (Submodule.span (𝓞 D.host.E) {F.ζ 0} : Set _) fun _ => True := by
  intro D hD T L μ0 hL sc G W Mv hM F hF h u hu
  have hx := lineComp_mem_shift D hD T L μ0 hL sc G W Mv hM F hF 0 h u hu
  exact latO_idLat_le _ _ _ _ (shiftId G) (star_mul_shiftId G) _
    (incA_inv_xi0_smul_starAdj_mem_latO D (negSp F.Lz) (G.V (.core (2 * 0 + 1))) _ _ _ _
      (GlobalTheory.AdjSrcZero.star_smul_mem_span G _) _ hx)

end GlobalTheory.LineAdjZero
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFirstStepAdjointLineComponentMemLatOStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.besselFirstStep_adjointLineComponent_mem_latO : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2) ∈ latO (G.V (.core (2 * 0 + 1))) (negSp F.Lz) (G.Λ (.core (2 * 0 + 1)) : Set _) (Submodule.span (𝓞 D.host.E) {F.ζ 0} : Set _) fun _ => True := by
  first | exact @GlobalTheory.LineAdjZero.adj_lineComp_mem_latO | exact GlobalTheory.LineAdjZero.adj_lineComp_mem_latO | (intros; apply GlobalTheory.LineAdjZero.adj_lineComp_mem_latO <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarAdjointMemHatLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.star_adjoint_mem_hat_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, ∀ e : AE D, IsIdemSum e G.pl.W0 → e • (incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2)) ∈ hatMx (G.modul • homLat (G.Λ (.core (2 * 0 + 1))) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
  first | exact @GlobalTheory.AscFin.BoxBF.lineAdj_zero_dep | exact GlobalTheory.AscFin.BoxBF.lineAdj_zero_dep | (intros; apply GlobalTheory.AscFin.BoxBF.lineAdj_zero_dep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepZeroLineComponentAdjointMemLattice

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


namespace GlobalTheory.LineZero

variable {D : D7}

noncomputable def mulL {k m n : ℕ} (A : Mx D k m) : Mx D m n →+ Mx D k n where
  toFun y := A * y
  map_zero' := Matrix.mul_zero _
  map_add' y y' := Matrix.mul_add _ _ _

theorem rat_mul_mem_latO {S B T : HSp D} (M : Matrix (Fin T.rank) (Fin B.rank) D.host.E)
    {LS : Set (Fin S.rank → D.host.E)} {LB : Set (Fin B.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : GlobalTheory.FinPl.Pl D → Prop} (hM : ∀ t ∈ LB, M *ᵥ t ∈ LT) {y : WO S B} (hy : y ∈ latO S B LS LB P) :
    (rat M : Mx D T.rank B.rank) * y ∈ latO S T LS LT P := by
  suffices h : latO S B LS LB P ≤ (latO S T LS LT P).comap (mulL (rat M : Mx D T.rank B.rank)) from h hy
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩
  refine AddSubgroup.subset_closure ⟨α, hα, hαP, a, ha, s, hs, M *ᵥ t, hM t ht, ?_⟩
  ext i j
  simp only [mulL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, incA, inclR,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [← TensorProduct.tmul_sum]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  first
    | exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
    | (rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring)

end GlobalTheory.LineZero

namespace GlobalTheory.LineZero

variable {D : D7}

theorem latO_le_negSp {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : GlobalTheory.FinPl.Pl D → Prop} : latO S T LS LT P ≤ latO (negSp S) T LS LT P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩
  have e : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
      -(Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * (negSp S).gram k j)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.neg_apply, negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib,
      TensorProduct.tmul_neg, neg_neg]
  rw [e]
  exact neg_mem (AddSubgroup.subset_closure ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩)

theorem rat_mul_mem_hatMx {k m n : ℕ} (A : Matrix (Fin k) (Fin m) D.host.E)
    {N : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)} {N' : Submodule (𝓞 D.host.E) (Matrix (Fin k) (Fin n) D.host.E)}
    (hA : ∀ x ∈ N, A * x ∈ N') {y : Mx D m n} (hy : y ∈ hatMx N) : (rat A : Mx D k m) * y ∈ hatMx N' := by
  suffices h : hatMx N ≤ (hatMx N').comap (mulL (rat A : Mx D k m)) from h hy
  refine (AddSubgroup.closure_le _).2 ?_
  rintro w ⟨α, hα, x, hx, rfl⟩
  refine AddSubgroup.subset_closure ⟨α, hα, A * x, hA x hx, ?_⟩
  ext i j
  simp only [mulL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, incA, inclR,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul]
  rw [← TensorProduct.tmul_sum]

theorem mul_mem_smul_homLat {k m n : ℕ} (A : Matrix (Fin k) (Fin m) D.host.E) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    (hA : ∀ t ∈ Λ', A *ᵥ t ∈ Λ'') (I : Ideal (𝓞 D.host.E)) {x : Matrix (Fin m) (Fin n) D.host.E}
    (hx : x ∈ I • homLat Λ Λ') : A * x ∈ I • homLat Λ Λ'' := by
  refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun _ _ hy hy' => ?_)
  · rw [Matrix.mul_smul]
    refine Submodule.smul_mem_smul hr fun z hz => ?_
    rw [← Matrix.mulVec_mulVec]
    exact hA _ (hy z hz)
  · rw [Matrix.mul_add]
    exact add_mem hy hy'

end GlobalTheory.LineZero


open GlobalTheory.LineZero in
theorem GlobalTheory.LineZero.adj_mem_lineLat : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2) ∈ lineLat F 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF h u hu
  have h1 := GlobalTheory.T.besselFirstStep_adjointLineComponent_mem_latO D hq T L μ0 hL sc G W M hM F hF h u hu
  have h2 := GlobalTheory.T.star_adjoint_mem_hat_lattice D hq T L μ0 hL sc G W M hM F hF h u hu
  have hz : ∀ t ∈ Submodule.span (𝓞 D.host.E) {F.ζ 0}, F.oz.iB *ᵥ t ∈ G.Λ (.core 0) := by
    intro t ht
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ht
    rw [Matrix.mulVec_smul, hF.zB]
    refine Submodule.smul_mem _ c ?_
    show _ ∈ (G.sp.P 0).lat
    rw [G.sp.lat0]
    refine ⟨0, zero_mem _, fun _ => 1, fun _ => FractionalIdeal.one_mem_one _, ?_⟩
    funext i
    simp [Matrix.mulVec, dotProduct]
  show _ ∈ (latCore G 0).comap _
  rw [AddSubgroup.mem_comap]
  simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply,
    AddMonoidHom.inr_apply]
  rw [GlobalTheory.MixModel.OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add (F.oz.jB * _)]
  refine ⟨?_, fun e he => ?_⟩
  · exact latO_le_negSp (rat_mul_mem_latO F.oz.iB hz h1)
  · rw [← Matrix.mul_smul]
    exact rat_mul_mem_hatMx F.oz.iB (fun x hx => mul_mem_smul_homLat F.oz.iB hz _ hx) (h2 e he)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepZeroLineComponentAdjointMemLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.besselStepZero_lineComponent_adjoint_mem_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2) ∈ lineLat F 0 := by
  first | exact @GlobalTheory.LineZero.adj_mem_lineLat | exact GlobalTheory.LineZero.adj_mem_lineLat | (intros; apply GlobalTheory.LineZero.adj_mem_lineLat <;> assumption)
end
end
