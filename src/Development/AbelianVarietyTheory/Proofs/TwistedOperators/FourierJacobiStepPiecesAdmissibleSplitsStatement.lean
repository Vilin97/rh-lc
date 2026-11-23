module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselLatticeSplitsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselPiecesMutualAnnihilatorsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialFourierJacobiStepStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtZeroIncZeroMemLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlace
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroLatticeVacuumSelfDualStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.InstIsModTopTens
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselPiecesMutualAnnihilatorsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XZeroColumnLattice

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ColSplitA

variable {D : D7}

theorem mulVec_mem_latA {S T : HSp D} {L : Lat S} {L' : Lat T} {P : Pl D → Prop} (M : Mx D T.rank S.rank)
    (hM : ∀ y ∈ latV S L P, M *ᵥ y ∈ latV T L' P) {z : Fin S.rank → AE D} (hz : z ∈ latA S L P) :
    M *ᵥ z ∈ latA T L' P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    set u : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hu
    have hu' : u ∈ latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have heq : M *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
        fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (M *ᵥ u) k := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hu]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
      rw [h1]; ring
    rw [heq]
    exact VacFlat.smul_mem_latA ha (hM u hu')
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

end GlobalTheory.FinPl.ColSplitA

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselCorePieceNonzeroVacuum

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

namespace GlobalTheory.AscFin.PcFBVac

variable {D : D7}

theorem mxAt_mul_mul {P : GlobalTheory.FinPl.Pl D → Prop} {k l m n : ℕ} (b : Mx D k l) {a : Mx D l m} (c : Mx D m n)
    (ha : MxAt P a) : MxAt P (b * a * c) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun r _ => Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun s _ => Ideal.mul_mem_left _ _ (ha s r))

theorem pcFB_vac : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∃ f, VacG W.ψ _ _ (pcFB W F σ h h').Γ₀ f ∧ f ≠ 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨-, H2, -⟩ := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF
  have sdT : IsSelfDualC (F.V₀ σ) (lat0 F σ h') := (H2 σ h').1
  have monoB : ∀ v, MonoAt (F.dB σ h') (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v := fun v => ((H2 σ h').2.1 v).1
  have monoJ : ∀ v, MonoAt (F.dJ (σ + 1) h) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.core (2 * (σ + 1) + 1))) v :=
    fun v => ((H2 (σ + 1) h).2.1 v).2
  have sdC := GlobalTheory.CosetRow.selfDual_chi hL G (2 * σ + 2) (by omega)
  have sdS : IsSelfDualC (G.V (.core (2 * (σ + 1) + 1))) (G.Λ (.core (2 * (σ + 1) + 1))) :=
    (node_isV G hL (X := .core (2 * (σ + 1) + 1)) (show 2 * (σ + 1) + 1 ≤ D.R.m by omega)).sd
  have sdV : IsSelfDualC (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
    (node_isV G hL (X := .grid (2 * (σ + 1) + 1) 0) (show 2 * (σ + 1) + 1 ≤ D.R.m ∧ 0 ≤ D.R.m by omega)).sd
  refine GlobalTheory.T.exists_ne_zero_latticeVacuum_selfDual D W.ψ W.ψ_std _ _ (G.Λ (.core (2 * (σ + 1) + 1))) (lat0 F σ h') sdS sdT _ ?_
  intro u hu
  have hw := (GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ sdC.1 sdC.2 (fun _ => True) _).1 hu.1
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ sdS sdT]
  have hu' : u = (F.dB σ h').p0 * ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) * (F.dJ (σ + 1) h).j0 := by
    simp only [Matrix.mul_assoc, HypDec.p0_j0, Matrix.mul_one]
    rw [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
  refine ⟨?_, fun y hy => ?_⟩
  · rw [hu']
    exact mxAt_mul_mul _ _ hw.1
  · have hj : (F.dJ (σ + 1) h).j0 *ᵥ y ∈ latV (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) fun _ => True :=
      GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace (F.dJ (σ + 1) h) sdV.1 (fun v _ => monoJ v) hy
    have h2 := hw.2 _ hj
    have e : ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) *ᵥ ((F.dJ (σ + 1) h).j0 *ᵥ y) = (F.dB σ h').j0 *ᵥ (u *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, HypDec.p0_j0, Matrix.mul_one, ← Matrix.mulVec_mulVec]
    change ((F.dB σ h').j0 * u * (F.dJ (σ + 1) h).p0) *ᵥ ((F.dJ (σ + 1) h).j0 *ᵥ y) ∈ _ at h2
    rw [e] at h2
    have h3 := GlobalTheory.FinPl.ColSplitA.mulVec_mem_latA (F.dB σ h').p0
      (fun z hz => GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits _ sdT.1 (fun v _ => monoB v) hz) h2
    rw [Matrix.mulVec_mulVec, HypDec.p0_j0, Matrix.one_mulVec] at h3
    exact h3

end GlobalTheory.AscFin.PcFBVac

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselCorePieceNonzeroVacuumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.jacobi_to_bessel_core_piece_nonzero_vacuum : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∃ f, VacG W.ψ _ _ (pcFB W F σ h h').Γ₀ f ∧ f ≠ 0 := by
  first | exact @GlobalTheory.AscFin.PcFBVac.pcFB_vac | exact GlobalTheory.AscFin.PcFBVac.pcFB_vac | (intros; apply GlobalTheory.AscFin.PcFBVac.pcFB_vac <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselPiecesFiniteAdelicLattices

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

section Transfer

variable {D : D7}

theorem mxAt_mul_right {m n k : ℕ} {x : Mx D m n} (hx : MxAt (fun _ => True) x) (M : Mx D n k) :
    MxAt (fun _ => True) (x ⬝ M) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

theorem mxAt_mul_left {m n k : ℕ} {x : Mx D m n} (hx : MxAt (fun _ => True) x) (M : Mx D k m) :
    MxAt (fun _ => True) (M ⬝ x) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

theorem finLat_comap {m n m' n' : ℕ} {Γ : AddSubgroup (Mx D m' n')} (hΓ : FinLat Γ) (f : Mx D m n →+ Mx D m' n')
    (g : Mx D m' n' → Mx D m n) (hf : Continuous f) (hg : Continuous g) (hgf : ∀ a, g (f a) = a)
    (hfM : ∀ a, MxAt (fun _ => True) a → MxAt (fun _ => True) (f a))
    (hgM : ∀ b, MxAt (fun _ => True) b → MxAt (fun _ => True) (g b)) : FinLat (Γ.comap f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [← hgf a]
    exact hgM _ (hΓ.fin _ ha)
  · haveI : T2Space (Mx D m' n') := (GlobalTheory.MixModel.lattice_Mx D m' n').2.2.2.1
    have hc : IsClosed ((Γ.comap f : AddSubgroup _) : Set (Mx D m n)) := hΓ.cpt.isClosed.preimage hf
    refine (hΓ.cpt.image hg).of_isClosed_subset hc ?_
    intro a ha
    exact ⟨f a, ha, hgf a⟩
  · obtain ⟨U, hU, h0, hUΓ⟩ := hΓ.opn
    exact ⟨f ⁻¹' U, hU.preimage hf, by simpa using h0, fun a ha hA => hUΓ _ ha (hfM a hA)⟩

end Transfer

theorem pcFB_fin : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    FinLat (pcFB W F σ h h').A₁ ∧ FinLat (pcFB W F σ h h').B₁ ∧ FinLat (pcFB W F σ h h').B₂ ∧
      ∀ u ∈ (pcFB W F σ h h').Γ₀, MxAt (fun _ => True) u := by
  intro D hOff T L μ0 hL sc G W M hM F hF σ h h'
  have hlat := (GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hOff T L μ0 hL sc G W M hM F hF).1 (2 * σ + 2) (by omega)
  have hRow : FinLat (latRow G (2 * σ + 2)) := hlat.1
  have hBig : FinLat (latBig G (2 * σ + 2)) := hlat.2.2.1
  set dV := F.dJ (σ + 1) h
  set dW := F.dB σ h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact finLat_comap hRow (dV.extX _) (fun w => w ⬝ dV.jX) (continuous_id.matrix_mul continuous_const)
      (continuous_id.matrix_mul continuous_const)
      (fun a => by simp only [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one])
      (fun a ha => mxAt_mul_right ha _) (fun b hb => mxAt_mul_right hb _)
  · exact finLat_comap hBig ((dV.ext0 _).comp (dW.incX _)) (fun w => dW.pX ⬝ (w ⬝ dV.j0))
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
      (continuous_const.matrix_mul (continuous_id.matrix_mul continuous_const))
      (fun a => by simp only [AddMonoidHom.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.incX_apply, Matrix.mul_assoc,
        HypDec.p0_j0, Matrix.mul_one, ← Matrix.mul_assoc dW.pX, HypDec.pX_jX, Matrix.one_mul])
      (fun a ha => mxAt_mul_right (mxAt_mul_left ha _) _) (fun b hb => mxAt_mul_left (mxAt_mul_right hb _) _)
  · exact finLat_comap hBig ((dV.ext0 _).comp (dW.incY _)) (fun w => dW.pY ⬝ (w ⬝ dV.j0))
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
      (continuous_const.matrix_mul (continuous_id.matrix_mul continuous_const))
      (fun a => by simp only [AddMonoidHom.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.incY_apply, Matrix.mul_assoc,
        HypDec.p0_j0, Matrix.mul_one, ← Matrix.mul_assoc dW.pY, HypDec.pY_jY, Matrix.one_mul])
      (fun a ha => mxAt_mul_right (mxAt_mul_left ha _) _) (fun b hb => mxAt_mul_left (mxAt_mul_right hb _) _)
  · intro u hu
    have h1 := hRow.fin _ hu
    have h2 : dW.p0 ⬝ (((dV.ext0 _).comp (dW.inc0 _)) u ⬝ dV.j0) = u := by
      simp only [AddMonoidHom.comp_apply, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_assoc,
        HypDec.p0_j0, Matrix.mul_one, ← Matrix.mul_assoc dW.p0, Matrix.one_mul]
    rw [← h2]
    exact mxAt_mul_left (mxAt_mul_right h1 _) _

end GlobalTheory.AscFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselPiecesFiniteAdelicLatticesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.jacobi_to_bessel_pieces_finite_adelic_lattices : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), FinLat (pcFB W F σ h h').A₁ ∧ FinLat (pcFB W F σ h h').B₁ ∧ FinLat (pcFB W F σ h h').B₂ ∧ ∀ u ∈ (pcFB W F σ h h').Γ₀, MxAt (fun _ => True) u := by
  first | exact @GlobalTheory.AscFin.pcFB_fin | exact GlobalTheory.AscFin.pcFB_fin | (intros; apply GlobalTheory.AscFin.pcFB_fin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepPiecesAdmissibleSplits

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

theorem piecesFB_is_and_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), (pcFB W F σ h h').Is (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ ∧ Splits (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (latRow G (2 * σ + 2)) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨f1, f2, f3, f4⟩ := GlobalTheory.T.jacobi_to_bessel_pieces_finite_adelic_lattices D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨g1, g2, g3⟩ := GlobalTheory.T.fourierJacobiToBessel_pieces_mutual_annihilators D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨b1, b2⟩ := GlobalTheory.T.jacobi_to_bessel_pieces_mutual_annihilators D hq T L μ0 hL sc G W M hM F hF σ h h'
  exact ⟨⟨f1, g1, f2, f3, g2, g3, b1, b2, GlobalTheory.T.genericCharacter_trivial_fourierJacobi_step D hq T L μ0 hL sc G W M hM F hF σ h h', f4, GlobalTheory.T.jacobi_to_bessel_core_piece_nonzero_vacuum D hq T L μ0 hL sc G W M hM F hF σ h h'⟩,
    GlobalTheory.T.fourierJacobiToBessel_lattice_splits D hq T L μ0 hL sc G W M hM F hF σ h h'⟩

end GlobalTheory.AscFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepPiecesAdmissibleSplitsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.fourierJacobi_step_pieces_admissible_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), (pcFB W F σ h h').Is (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ ∧ Splits (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (latRow G (2 * σ + 2)) := by
  first | exact @GlobalTheory.AscFin.piecesFB_is_and_splits | exact GlobalTheory.AscFin.piecesFB_is_and_splits | (intros; apply GlobalTheory.AscFin.piecesFB_is_and_splits <;> assumption)
end
end
