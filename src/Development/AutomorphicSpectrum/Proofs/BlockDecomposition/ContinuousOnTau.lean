module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InCell
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellConditionsOfSmulEq
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InCell
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSymplecticFormSqNegOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitOfRetract
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnipotentBlockFamily

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

theorem continuous_unipotent_block_family {X R : Type} [TopologicalSpace X] [TopologicalSpace R] [Zero R] [One R] {n : ℕ}
    {f : X → Matrix (Fin n) (Fin n) R} (hf : Continuous f) :
    Continuous fun x => blk4 (1 : Matrix (Fin n) (Fin n) R) (f x) 0 1 := by
  unfold blk4
  exact (continuous_const.matrix_fromBlocks hf continuous_const continuous_const).matrix_submatrix _ _

theorem unipotent_block_mul_add {R : Type} [CommRing R] {n : ℕ} (b c : Matrix (Fin n) (Fin n) R) :
    blk4 (1 : Matrix (Fin n) (Fin n) R) b 0 1 * blk4 1 c 0 1 = blk4 1 (b + c) 0 1 := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [add_comm]

theorem continuous_nb {D : D7} {p : ℕ} {nb : hermA D p → G D p} (hnb : IsNMap nb) : Continuous nb := by
  have emb := isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D p)
  rw [emb.continuous_iff, Units.continuous_iff]
  have hv : Continuous fun b : hermA D p => (b.1 : Mx D p p) := continuous_subtype_val
  have hm : ∀ b, (AdelicU.matHom _ D.sp.cm.sig (Jst D p) (nb b)).1 = blk4 1 b.1 0 1 := hnb
  constructor
  · refine (continuous_unipotent_block_family hv).congr fun b => ?_
    exact (hm b).symm
  · refine (continuous_unipotent_block_family hv.neg).congr fun b => ?_
    symm
    refine Units.inv_eq_of_mul_eq_one_right ?_
    simp only [Function.comp]
    rw [hm b, unipotent_block_mul_add]
    simp [blk4]

end GlobalTheory.CompanionTheory.MuC
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBUnique

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

theorem isB_unique : ∀ {D : D7} {p : ℕ} {e : AE D} {g : G D p} {x x' : hermS D p e} (h : IsB e g x) (h' : IsB e g x'), x = x' := by
  intro D p e g x x' h h'
  obtain ⟨⟨y, hy⟩, hx⟩ := h
  obtain ⟨-, hx'⟩ := h'
  have key : ∀ z : hermS D p e, mm (lowC g) z.1.1 = e • lowD g → z.1.1 = mm y (e • lowD g) := by
    intro z hz
    have hs : e • z.1.1 = z.1.1 := z.2
    rw [← hz]
    show z.1.1 = y * (lowC g * z.1.1)
    rw [← Matrix.mul_assoc]
    have hy' : y * lowC g = e • (1 : Mx D p p) := hy
    rw [hy', Matrix.smul_mul, Matrix.one_mul, hs]
  exact Subtype.ext (Subtype.ext ((key x hx).trans (key x' hx').symm))

end GlobalTheory.CompanionTheory.MuC
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsNMapAdd

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
noncomputable section

namespace GlobalTheory.CompanionTheory.MuC

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

theorem isNMap_add : ∀ {D : D7} {p : ℕ} {nb : hermA D p → G D p} (hnb : IsNMap nb) (x y : hermA D p), nb (x + y) = nb x * nb y := by
  intro D p nb hnb x y
  apply mat_inj
  rw [mat_mul, hnb, hnb, hnb, submatrix_fromBlocks_mul]
  simp [add_comm]

end GlobalTheory.CompanionTheory.MuC
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerDiagonalOfUpperTriangularBlock

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC.LeftCell

variable {D : D7} {p : ℕ}

theorem upper_triangular_block_mul_lower_rows (a b d : Mx D p p) (N : Mx D (p + p) (p + p)) (k : Fin p → Fin (p + p)) :
    (blk4 a b 0 d * N).submatrix (fun i : Fin p => finSumFinEquiv (Sum.inr i)) k =
      d * N.submatrix (fun i : Fin p => finSumFinEquiv (Sum.inr i)) k := by
  ext i j
  rw [Matrix.submatrix_apply, Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  simp only [blk4, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]

theorem lowerDiagonal_of_upper_triangular_block {a b d : Mx D p p} {q : G D p} (h : mat q = blk4 a b 0 d) : lowD q = d := by
  ext i j
  simp only [lowD, h, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]

theorem low_mul {q : G D p} (hq : q ∈ P D p) (g : G D p) :
    lowC (q * g) = lowD q * lowC g ∧ lowD (q * g) = lowD q * lowD g := by
  obtain ⟨b, d, hm⟩ := GlobalTheory.StdUnn.LeftInvSect.siegelParabolicUnn_matrix_blockUpperTriangular hq
  have hd := lowerDiagonal_of_upper_triangular_block hm
  rw [hd]
  constructor
  · change (mat (q * g)).submatrix _ _ = _
    rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, hm]
    exact upper_triangular_block_mul_lower_rows _ _ _ _ _
  · change (mat (q * g)).submatrix _ _ = _
    rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, hm]
    exact upper_triangular_block_mul_lower_rows _ _ _ _ _

theorem lowD_one : lowD (1 : G D p) = 1 := by
  ext i j
  simp [lowD, GlobalTheory.StdUnn.LeftInvSect.mat_one, Matrix.one_apply]

theorem lowD_inv_mul {q : G D p} (hq : q ∈ P D p) : lowD q⁻¹ * lowD q = 1 := by
  have h := (low_mul ((P D p).inv_mem hq) q).2
  rw [inv_mul_cancel, lowD_one] at h
  exact h.symm

theorem isB_mul {e : AE D} {q g : G D p} (hq : q ∈ P D p) {x : hermS D p e} (h : IsB e g x) :
    IsB e (q * g) x := by
  obtain ⟨⟨y, hy⟩, hx⟩ := h
  obtain ⟨hC, hD⟩ := low_mul hq g
  refine ⟨⟨mm y (lowD q⁻¹), ?_⟩, ?_⟩
  · change (y * lowD q⁻¹) * lowC (q * g) = _
    change y * lowC g = _ at hy
    rw [hC, Matrix.mul_assoc, ← Matrix.mul_assoc (lowD q⁻¹), lowD_inv_mul hq, Matrix.one_mul, hy]
  · change lowC (q * g) * x.1.1 = _
    change lowC g * x.1.1 = _ at hx
    rw [hC, hD, Matrix.mul_assoc, hx, Matrix.mul_smul]

theorem isB_left : ∀ {D : D7} {p : ℕ} {e : AE D} {q g : G D p} (hq : q ∈ P D p) (x : hermS D p e),
    IsB e (q * g) x ↔ IsB e g x := by
  intro D p e q g hq x
  refine ⟨fun h => ?_, isB_mul hq⟩
  have h' := isB_mul ((P D p).inv_mem hq) h
  rwa [inv_mul_cancel_left] at h'

end GlobalTheory.CompanionTheory.MuC.LeftCell
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulNBlockInr

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.MuC

variable {D : D7} {p : ℕ}

theorem mul_nBlock_inl {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (y : Matrix (Fin n) (Fin n) R) (i : Fin (n + n)) (j : Fin n) :
    (A * blk4 1 y 0 1) i (finSumFinEquiv (Sum.inl j)) = A i (finSumFinEquiv (Sum.inl j)) := by
  simp [Matrix.mul_apply, blk4, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.one_apply]

theorem mul_nBlock_inr {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (y : Matrix (Fin n) (Fin n) R) (i : Fin (n + n)) (j : Fin n) :
    (A * blk4 1 y 0 1) i (finSumFinEquiv (Sum.inr j)) =
      ∑ k, A i (finSumFinEquiv (Sum.inl k)) * y k j + A i (finSumFinEquiv (Sum.inr j)) := by
  rw [Matrix.mul_apply, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₂]
  simp [Matrix.one_apply]

theorem lowC_mul_nb {nb : hermA D p → G D p} (hnb : IsNMap nb) (g : G D p) (y : hermA D p) :
    lowC (g * nb y) = lowC g := by
  have hm : mat (g * nb y) = mat g * blk4 1 y.1 0 1 := by
    rw [← hnb y]; rfl
  ext i j
  simp only [lowC, Matrix.submatrix_apply, hm]
  exact mul_nBlock_inl _ _ _ _

theorem lowD_mul_nb {nb : hermA D p → G D p} (hnb : IsNMap nb) (g : G D p) (y : hermA D p) :
    lowD (g * nb y) = lowC g * y.1 + lowD g := by
  have hm : mat (g * nb y) = mat g * blk4 1 y.1 0 1 := by
    rw [← hnb y]; rfl
  ext i j
  simp only [lowC, lowD, Matrix.submatrix_apply, hm, Matrix.add_apply, Matrix.mul_apply]
  exact mul_nBlock_inr _ _ _ _

theorem isB_mul_nb {D : D7} {p : ℕ} {e : AE D} {nb : hermA D p → G D p} (hnb : IsNMap nb) {g : G D p}
    (y x : hermS D p e) : IsB e (g * nb y.1) (x + y) ↔ IsB e g x := by
  have hy : e • y.1.1 = y.1.1 := y.2
  have hc : e • (lowC g * y.1.1) = lowC g * y.1.1 := by rw [← Matrix.mul_smul, hy]
  have hs : (x + y).1.1 = x.1.1 + y.1.1 := rfl
  unfold IsB InCell
  rw [lowC_mul_nb hnb, lowD_mul_nb hnb, hs]
  refine and_congr_right fun _ => ?_
  simp only [mm]
  rw [mul_add, smul_add, hc, add_comm (lowC g * y.1.1) (e • lowD g), add_left_inj]

end GlobalTheory.CompanionTheory.MuC

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnTau

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CellTop

open GlobalTheory.CompanionTheory.MuC

variable {D : D7} {p : ℕ}

theorem mem_cell_iff {e : AE D} (hee : e * e = e) (g : G D p) : g ∈ cell e ↔ InCell e g :=
  isUnit_mix_iff hee (cB g)

theorem continuous_cB : Continuous (cB : G D p → Mx D p p) := by
  have hm : Continuous (mat : G D p → Mx D (p + p) (p + p)) := Units.continuous_val.comp continuous_subtype_val
  exact continuous_matrix fun i j => hm.matrix_elem _ _

theorem continuous_dB : Continuous (dB : G D p → Mx D p p) := by
  have hm : Continuous (mat : G D p → Mx D (p + p) (p + p)) := Units.continuous_val.comp continuous_subtype_val
  exact continuous_matrix fun i j => hm.matrix_elem _ _

theorem cell_eq {e : AE D} (hee : e * e = e) :
    cell e = (fun g : G D p => (cB g).det) ⁻¹' {z : AE D | IsUnit (1 - e + e * z)} := by
  ext g
  change IsUnit _ ↔ IsUnit _
  rw [det_mix_one hee]


open Classical in
def tau (e : AE D) (g : G D p) : hermS D p e := if h : ∃ x, IsB e g x then h.choose else 0

theorem isB_tau {e : AE D} {g : G D p} (h : ∃ x, IsB e g x) : IsB e g (tau e g) := by
  rw [tau, dite_eq_left h]
  exact h.choose_spec

theorem tau_eq {e : AE D} {g : G D p} {x : hermS D p e} (h : IsB e g x) : tau e g = x :=
  isB_unique (isB_tau ⟨x, h⟩) h

theorem tau_formula {e : AE D} (hee : e * e = e) {g : G D p} {x : hermS D p e} (hu : g ∈ cell e) (h : IsB e g x) :
    Ring.inverse (1 - e + e * (cB g).det) • (((1 - e) • (1 : Mx D p p) + e • cB g).adjugate * (e • dB g)) = x.1.1 := by
  have hu' : IsUnit (1 - e + e * (cB g).det) := by
    have := hu
    rw [cell_eq hee] at this
    exact this
  exact mix_solve hee hu' x.2 h.2

theorem continuousOn_tau {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) (hee : e * e = e) (hce : cA D e = e) :
    ContinuousOn (tau e : G D p → hermS D p e) (cell e) := by
  have : IsTopologicalRing (AE D) := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hd : Continuous fun g : G D p => (cB g).det := continuous_cB.matrix_det
  have h1 : ContinuousOn (fun g : G D p => Ring.inverse (1 - e + e * (cB g).det)) (cell e) := by
    refine (unit_AE he).2.comp hd.continuousOn ?_
    intro g hg
    rw [cell_eq hee] at hg
    exact hg
  have h2 : Continuous fun g : G D p => ((1 - e) • (1 : Mx D p p) + e • cB g).adjugate * (e • dB g) := by
    refine Continuous.matrix_mul (Continuous.matrix_adjugate ?_) (continuous_dB.const_smul e)
    exact continuous_const.add (continuous_cB.const_smul e)
  have h3 : ContinuousOn (fun g : G D p => ((tau e g).1.1 : Mx D p p)) (cell e) := by
    refine (h1.smul h2.continuousOn).congr fun g hg => ?_
    have hB : IsB e g (tau e g) := isB_tau (exists_isB hee hce ((mem_cell_iff hee g).1 hg))
    exact (tau_formula hee hg hB).symm
  have i1 : Topology.IsInducing (Subtype.val : hermS D p e → hermA D p) := Topology.IsInducing.subtypeVal
  have i2 : Topology.IsInducing (Subtype.val : hermA D p → Mx D p p) := Topology.IsInducing.subtypeVal
  exact (i2.comp i1).continuousOn_iff.2 h3

theorem cellAlg : IdemEx → CellAlg := by
  intro hI D p nb hnb w hw S e he
  obtain ⟨hee, hce⟩ := (hI D S).2 e he
  have hex : ∀ g ∈ cell (p := p) e, IsB e g (tau e g) := fun g hg =>
    isB_tau (exists_isB hee hce ((mem_cell_iff hee g).1 hg))
  have hcell : ∀ {g : G D p} {x : hermS D p e}, IsB e g x → g ∈ cell e := fun h => (mem_cell_iff hee _).2 h.1
  refine ⟨tau e, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, continuousOn_tau he hee hce, (continuous_nb hnb).comp continuous_subtype_val,
      fun x y => isNMap_add hnb x.1 y.1⟩
    · rw [cell_eq hee]
      exact (unit_AE he).1.preimage (continuous_cB.matrix_det (R := AE D))
    · intro q hq x hx
      have h := (LeftCell.isB_left hq (tau e x)).2 (hex x hx)
      exact ⟨hcell h, (tau_eq h)⟩
    · intro y x hx
      have h := (isB_mul_nb hnb y (tau e x)).2 (hex x hx)
      exact ⟨hcell h, tau_eq h⟩
  · intro g hg u hu
    exact hcell ((isB_mul_right_iff he hu (tau e g)).2 (hex g hg))
  · intro g hg
    have h := hex g hg
    change (e • cB g) * _ = _
    rw [smul_mul_assoc]
    have h2 : cB g * (tau e g).1.1 = e • dB g := h.2
    rw [h2, smul_smul, hee]

end GlobalTheory.CompanionTheory.CellTop
end
end
end
