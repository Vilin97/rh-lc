module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepCorePieceFiniteNonzeroVacuumStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.InstIsModTopTens
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepPiecesBMutualAnnihilatorsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiAnnihilatorPieceCompactOpenStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiDepthLatticeSplitsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BidualityDepthLatticePieceBesselStepStatement
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialBesselStepUnitriangular
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepPiecesBFiniteAdelicLattices

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BesselPieceB

variable {D : D7}

theorem mxAt_mul_left {P : GlobalTheory.FinPl.Pl D → Prop} {k m n : ℕ} (M : Mx D k m) {x : Mx D m n} (hx : MxAt P x) :
    MxAt P (M ⬝ x) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

theorem mxAt_mul_right {P : GlobalTheory.FinPl.Pl D → Prop} {k m n : ℕ} {x : Mx D k m} (hx : MxAt P x) (M : Mx D m n) :
    MxAt P (x ⬝ M) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

theorem finLat_comap_mul {k n k' m' : ℕ} {A : AddSubgroup (Mx D k' m')} (hA : FinLat A) (f : Mx D k n →+ Mx D k' m')
    (M : Mx D k' k) (N : Mx D n m') (M' : Mx D k k') (N' : Mx D m' n) (hf : ∀ x : Mx D k n, f x = M ⬝ x ⬝ N)
    (hM : M' ⬝ M = 1) (hN : N ⬝ N' = 1) : FinLat (A.comap f) := by
  haveI : T2Space (Mx D k' m') := (lattice_Mx D k' m').2.2.2.1
  have hfc : Continuous f := by
    have : (f : Mx D k n → Mx D k' m') = fun x : Mx D k n => M ⬝ x ⬝ N := funext hf
    rw [this]; exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hgc : Continuous fun y : Mx D k' m' => M' ⬝ y ⬝ N' :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hgf : ∀ x, M' ⬝ f x ⬝ N' = x := fun x => by
    have e : M' ⬝ f x ⬝ N' = (M' ⬝ M) ⬝ x ⬝ (N ⬝ N') := by rw [hf]; simp only [Matrix.mul_assoc]
    rw [e, hM, hN, Matrix.one_mul, Matrix.mul_one]
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · rw [← hgf a]; exact mxAt_mul_right (mxAt_mul_left _ (hA.fin _ ha)) _
  · refine (hA.cpt.image hgc).of_isClosed_subset (hA.cpt.isClosed.preimage hfc) fun a ha => ⟨f a, ha, hgf a⟩
  · obtain ⟨U, hU, h0, hUA⟩ := hA.opn
    refine ⟨f ⁻¹' U, hU.preimage hfc, by simpa using h0, fun a ha hfin => hUA _ ha ?_⟩
    rw [hf]; exact mxAt_mul_right (mxAt_mul_left _ hfin) _

end GlobalTheory.BesselPieceB


open GlobalTheory.BesselPieceB in
theorem GlobalTheory.BesselPieceB.finLat_pcBF_B : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m),
    FinLat (pcBF W F ρ h).B₁ ∧ FinLat (pcBF W F ρ h).B₂ := by
  intro D hD T L μ0 hL sc G W M hM F hF ρ h
  have hB : FinLat (latBig G (2 * ρ + 1)) :=
    ((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W M hM F hF).1 (2 * ρ + 1) (by omega)).2.2.1
  exact ⟨finLat_comap_mul hB _ (F.dJ ρ h).jX (F.dB ρ h).p0 (F.dJ ρ h).pX (F.dB ρ h).j0 (fun _ => rfl)
      (F.dJ ρ h).pX_jX (F.dB ρ h).p0_j0,
    finLat_comap_mul hB _ (F.dJ ρ h).jY (F.dB ρ h).p0 (F.dJ ρ h).pY (F.dB ρ h).j0 (fun _ => rfl)
      (F.dJ ρ h).pY_jY (F.dB ρ h).p0_j0⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepPiecesBFiniteAdelicLatticesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.bessel_step_pieces_B_finite_adelic_lattices : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), FinLat (pcBF W F ρ h).B₁ ∧ FinLat (pcBF W F ρ h).B₂ := by
  first | exact @GlobalTheory.BesselPieceB.finLat_pcBF_B | exact GlobalTheory.BesselPieceB.finLat_pcBF_B | (intros; apply GlobalTheory.BesselPieceB.finLat_pcBF_B <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLatticeStandardParabolic

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.PieceA

variable {D : D7}

theorem mxAt_mul_right {m n k : ℕ} {a : Mx D m n} (ha : MxAt (fun _ => True) a) (M : Mx D n k) :
    MxAt (fun _ => True) (a ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)

theorem finLat_comap_extX {V V₀ W : HSp D} {ρ : ℕ} (d : GlobalTheory.MixModel.HypDec V V₀ ρ) {Γ : AddSubgroup (WO V W)}
    (hΓ : FinLat Γ) : FinLat (Γ.comap (d.extX W)) := by
  haveI : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1
  have hc : Continuous (d.extX W) := by
    show Continuous fun a : Mx D W.rank ρ => a ⬝ d.pX
    exact continuous_id.matrix_mul continuous_const
  have hinv : ∀ a : Mx D W.rank ρ, d.extX W a ⬝ d.jX = a := fun a => by
    rw [GlobalTheory.MixModel.HypDec.extX_apply, Matrix.mul_assoc, GlobalTheory.MixModel.HypDec.pX_jX, Matrix.mul_one]
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · rw [← hinv a]
    exact mxAt_mul_right (hΓ.fin _ ha) _
  · have hK : IsCompact ((fun w : WO V W => w ⬝ d.jX) '' (Γ : Set (WO V W))) :=
      hΓ.cpt.image (continuous_id.matrix_mul continuous_const)
    refine hK.of_isClosed_subset (hΓ.cpt.isClosed.preimage hc) ?_
    intro a ha
    exact ⟨_, ha, hinv a⟩
  · obtain ⟨U, hU, h0, hUA⟩ := hΓ.opn
    refine ⟨d.extX W ⁻¹' U, hU.preimage hc, by simpa using h0, fun a ha haf => ?_⟩
    exact hUA _ ha (by rw [GlobalTheory.MixModel.HypDec.extX_apply]; exact mxAt_mul_right haf _)

end GlobalTheory.AscFin.PieceA

namespace GlobalTheory.AscFin

open GlobalTheory.AscFin.PieceA

theorem finLat_pcBF_A₁ : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), FinLat (pcBF W F ρ h).A₁ := by
  have H := GlobalTheory.T.grid_lattices_compact_selfDual_splitting
  unfold OnStd at H ⊢
  delta All at H ⊢
  intro D hD T L μ0 hL sc G W M hM F hF ρ h
  exact finLat_comap_extX _ ((H D hD T L μ0 hL sc G W M hM F hF).1 (2 * ρ + 1) (by omega)).1

end GlobalTheory.AscFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLatticeStandardParabolicStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.finite_lattice_standard_parabolic : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), FinLat (pcBF W F ρ h).A₁ := by
  first | exact @GlobalTheory.AscFin.finLat_pcBF_A₁ | exact GlobalTheory.AscFin.finLat_pcBF_A₁ | (intros; apply GlobalTheory.AscFin.finLat_pcBF_A₁ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialBesselStepUnitriangularStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.genericCharacter_trivial_besselStep_unitriangular : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u : UX D ρ, MxAt (fun _ => True) (u.1.1 - 1) → xZero (F.dJ ρ h) ⬝ u.1.1 - xZero (F.dJ ρ h) ∈ (pcBF W F ρ h).A₁ → psiUni W.ψ u.1 = 1 := by
  first | exact @GlobalTheory.AscFin.UniBF.psiUni_pcBF | exact GlobalTheory.AscFin.UniBF.psiUni_pcBF | (intros; apply GlobalTheory.AscFin.UniBF.psiUni_pcBF <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiMixedPiecesAdmissible

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PcBF

variable {D : D7}

theorem symplO_add_right' (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO, hO, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

theorem symplO_neg_right' (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = - symplO S T x y := by
  have := symplO_add_right' S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right'] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem ann_of_mem {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    (ψ : AddChar (AF D.host.F) ℂ) (Γ Γ' : AddSubgroup (WO V W)) {a' : Mx D W.rank ρ}
    (ha' : a' ∈ (piecesOf (W₀ := W₀) dV dW ψ Γ Γ').A₂) :
    ∀ a ∈ (piecesOf (W₀ := W₀) dV dW ψ Γ Γ').A₁, ψ (symplO V W (dV.extX W a) (dV.extY W a')) = 1 := by
  intro a ha
  induction ha' using AddSubgroup.closure_induction with
  | mem b hb => exact hb.2 a ha
  | zero => rw [map_zero, symplO_zero_right', AddChar.map_zero_eq_one]
  | add b c _ _ hb hc => rw [map_add (f := _), symplO_add_right', AddChar.map_add_eq_mul, hb, hc, one_mul]
  | neg b _ hb => rw [map_neg, symplO_neg_right', AddChar.map_neg_eq_inv, hb, inv_one]

end GlobalTheory.PcBF

namespace GlobalTheory.PcBF

theorem pieces_bf : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), (pcBF W F ρ h).Is (F.dB ρ h) (F.dJ ρ h) (xZero (F.dJ ρ h)) W.ψ ∧ Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  set_option maxHeartbeats 0 in
    intro D hD T L μ0 hL sc G W M hM F hF ρ h
    refine ⟨⟨GlobalTheory.T.finite_lattice_standard_parabolic D hD T L μ0 hL sc G W M hM F hF ρ h, ⟨?_, (GlobalTheory.T.besselToFourierJacobi_annihilatorPiece_compactOpen D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.besselToFourierJacobi_annihilatorPiece_compactOpen D hD T L μ0 hL sc G W M hM F hF ρ h).2⟩,
      (GlobalTheory.T.bessel_step_pieces_B_finite_adelic_lattices D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.bessel_step_pieces_B_finite_adelic_lattices D hD T L μ0 hL sc G W M hM F hF ρ h).2, ?_, ?_,
      (GlobalTheory.T.bessel_step_pieces_B_mutual_annihilators D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.bessel_step_pieces_B_mutual_annihilators D hD T L μ0 hL sc G W M hM F hF ρ h).2,
      GlobalTheory.T.genericCharacter_trivial_besselStep_unitriangular D hD T L μ0 hL sc G W M hM F hF ρ h, (GlobalTheory.T.bessel_step_core_piece_finite_nonzero_vacuum D hD T L μ0 hL sc G W M hM F hF ρ h).1, (GlobalTheory.T.bessel_step_core_piece_finite_nonzero_vacuum D hD T L μ0 hL sc G W M hM F hF ρ h).2⟩,
      GlobalTheory.T.besselToFourierJacobi_depthLattice_splits D hD T L μ0 hL sc G W M hM F hF ρ h⟩
    · intro a' ha'
      induction ha' using AddSubgroup.closure_induction with
      | mem b hb => exact hb.1
      | zero => intro i j; simp only [Matrix.zero_apply]; exact zero_mem _
      | add b c _ _ hb hc => intro i j; simp only [Matrix.add_apply]; exact add_mem (hb i j) (hc i j)
      | neg b _ hb => intro i j; simp only [Matrix.neg_apply]; exact neg_mem (hb i j)
    · intro a ha
      exact ⟨fun h1 a' h2 => ann_of_mem _ _ _ _ _ h2 a h1, GlobalTheory.T.biduality_depth_lattice_piece_bessel_step D hD T L μ0 hL sc G W M hM F hF ρ h a ha⟩
    · intro a' ha'
      exact ⟨fun h2 a h1 => ann_of_mem _ _ _ _ _ h2 a h1, fun H => AddSubgroup.subset_closure ⟨ha', fun a h1 => H a h1⟩⟩

end GlobalTheory.PcBF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiMixedPiecesAdmissibleStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.besselToFourierJacobi_mixedPieces_admissible : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), (pcBF W F ρ h).Is (F.dB ρ h) (F.dJ ρ h) (xZero (F.dJ ρ h)) W.ψ ∧ Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  first | exact @GlobalTheory.PcBF.pieces_bf | exact GlobalTheory.PcBF.pieces_bf | (intros; apply GlobalTheory.PcBF.pieces_bf <;> assumption)
end
end
