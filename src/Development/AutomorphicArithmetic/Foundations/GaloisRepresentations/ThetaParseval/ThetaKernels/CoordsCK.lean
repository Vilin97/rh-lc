module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PadMatrixLowerBlockZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SecondOrbitSectionIntegral
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousCA
import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSecondTerm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BlockDiagonalPreservesFormIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinTermLeftInvariant
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayDecG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentNilpotentMulEqZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.ContinuousFrameUM
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinTermLeftInvariant
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LamMapK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PhzEqFlatK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentFirstMatrix
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.CountableProdSub
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.VaddInvBotProd
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HandsCoordkTau

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5.CoordK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
variable (L) in
def kom_k (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (p : (Fin L.n → AE F E) × nA σ L.Y L.b) : d.G :=
  L.j (nb' p.2) * uM p.1 * (L.j (nb' p.2))⁻¹ * (uM p.1)⁻¹
variable (L) in
def tau_k (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (δ : E) (p : (Fin L.n → AE F E) × nA σ L.Y L.b) :
    (Fin L.n → AE F E) × AF F :=
  (fun k => inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' p) (Sum.inl L.i₀) (Sum.inr (L.em k)),
    ellA δ (inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' p) (Sum.inl L.i₀) (Sum.inr L.i₀)))
variable (L) in
def Du_k (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u))ᵀ.map (cA σ)
theorem frame_uM_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u) 0 0 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L u) := by
  obtain ⟨a', ha⟩ := h.uM u
  rw [ha, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.lr_of_k ha (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k L u)]
  rfl
theorem Du_mul_k (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k (σ := σ) L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L (-u) = 1 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k
  rw [← Matrix.map_mul, ← Matrix.transpose_mul, neg_neg, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k L u]
  ext i j
  simp [Matrix.one_apply, Matrix.map_apply]
theorem uM_neg'_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) : uM (-u) = (uM u)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right (_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d ?_)
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h, GlobalTheory.EisBL.DoubledParabolic.inFrame_one, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_mul_k, Matrix.fromBlocks_one]
theorem continuous_uA_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k (σ := σ) L) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k
  refine continuous_const.add (continuous_finsetSum _ fun j _ => ?_)
  have e : (fun b : Fin L.n → AE F E => Matrix.single L.i₀ (L.em j) (b j)) =
      fun b => b j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
    funext b; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]; exact (continuous_apply j).smul continuous_const
theorem continuous_frame_uM_k : Continuous fun u : Fin L.n → AE F E =>
    (Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u) 0 0 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k (σ := σ) L u) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) := by
  refine Continuous.matrix_fromBlocks _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_uA_k continuous_const continuous_const ?_
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k
  exact ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_uA_k.comp continuous_neg).matrix_transpose).matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)
theorem frame_kom_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (p : (Fin L.n → AE F E) × nA σ L.Y L.b) :
    inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' p) = inFrame d.b (L.j (nb' p.2)) * Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L p.1) 0 0 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L p.1) *
      inFrame d.b (L.j (nb' (-p.2))) * Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-p.1)) 0 0 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L (-p.1)) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k
  rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.uM_neg'_k h, ← map_inv, ← kunf.nb_neg h.nb', GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul,
    GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h]
theorem continuous_kom_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) : Continuous fun p => inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' p) := by
  have hj : Continuous fun β : nA σ L.Y L.b => inFrame d.b (L.j (nb' β)) :=
    (GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame d.b).comp (L.cont.comp (kunf.continuous_nb h.nb'))
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_kom_k h]
  exact (((hj.comp continuous_snd).matrix_mul (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_frame_uM_k.comp continuous_fst)).matrix_mul
    ((hj.comp continuous_neg).comp continuous_snd)).matrix_mul ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_frame_uM_k.comp continuous_neg).comp continuous_fst)
theorem continuous_tau_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ) := by
  have hk := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_kom_k h
  refine Continuous.prodMk (continuous_pi fun k => hk.matrix_elem _ _) ?_
  exact (IsModuleTopology.continuous_of_linearMap (R := AF F) (ellA δ)).comp (hk.matrix_elem _ _)
theorem Du_neg_row_k (u : Fin L.n → AE F E) (k : Fin d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k (σ := σ) L (-u) L.i₀ k = if k = L.i₀ then 1 else 0 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k
  rw [neg_neg, Matrix.map_apply, Matrix.transpose_apply]
  by_cases hk : k = L.i₀
  · subst hk
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, fun j => _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j]
  · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, hk, Ne.symm hk]
theorem sM_zero'_k : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L 0 = 1 := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L 0 = 0 := by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k]
  rw [this, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k, Matrix.fromBlocks_one]
theorem cM_zero'_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) : cM (u, 0) = uM u := by
  apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h]
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k]
theorem move_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (β'' : nA σ L.Y L.b) (b : Fin L.n → AE F E) (a : AF F) :
    L.j (nb' β'') * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) =
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (b + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, β'')).1) * cM (u, a + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, β'')).2) * L.j (nb' β'') := by
  obtain ⟨B, A, hBA⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.j_move_k (R := R) h u β''
  suffices hτ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, β'') = (B, A) by rw [hτ]; exact hBA b a
  have e0 := hBA 0 0
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.sM_zero'_k, one_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.cM_zero'_k h, zero_add, zero_add] at e0
  have hk : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' (u, β'') = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L B * cM (u, A) * (uM u)⁻¹ := by
    show L.j (nb' β'') * uM u * (L.j (nb' β''))⁻¹ * (uM u)⁻¹ = _
    rw [e0, mul_inv_cancel_right]
  have hf : inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' (u, β'')) =
      Matrix.fromBlocks 1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ A * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L (-u) + _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L B) 0 1 := by
    rw [hk, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.uM_neg'_k h, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.frame_uM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k]
    rw [show (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u))ᵀ.map (cA σ) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k L u from rfl]
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul,
      Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_mul_k]
    rw [Matrix.add_mul, Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_mul_k, Matrix.mul_one]
  have hrow : ∀ k, (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ A * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_k (σ := σ) L (-u)) L.i₀ k = if k = L.i₀ then A • inclR (F := F) (AF F) δ else 0 := by
    intro k
    rw [Matrix.mul_apply, Finset.sum_eq_single L.i₀]
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.Du_neg_row_k]; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k]
    · intro m _ hm; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.single_apply, Ne.symm hm]
    · simp
  refine Prod.ext (funext fun k => ?_) ?_
  · show inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' (u, β'')) (Sum.inl L.i₀) (Sum.inr (L.em k)) = B k
    rw [hf, Matrix.fromBlocks_apply₁₂, Matrix.add_apply, hrow, if_neg (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L k), zero_add, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_i0em_k]
  · show ellA δ (inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.kom_k L uM nb' (u, β'')) (Sum.inl L.i₀) (Sum.inr L.i₀)) = A
    rw [hf, Matrix.fromBlocks_apply₁₂, Matrix.add_apply, hrow, if_pos rfl, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_i0i0_k, add_zero, map_smul, ellA_self h.δ0,
      smul_eq_mul, mul_one]
end PositivityTheory.SiegelWeilFormula.Act.C5.CoordK
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CountableRatVK

section

@[expose] public section



section
set_option linter.unusedSectionVars false
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5.CoordK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem fix_mul_k {x y : d.G}
    (hx : ∀ k, inFrame d.b x k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (hy : ∀ k, inFrame d.b y k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (k) : inFrame d.b (x * y) k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply]
  simp only [hy]
  rw [← Matrix.mul_apply, Matrix.mul_one, hx]
theorem perF_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (Ψ : d.G → ℂ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g)
    (T : nF σ d.Y d.b) (x : d.G) (γ : nA σ d.Y d.b) (hγ : γ ∈ nF σ d.Y d.b) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Ψ (nb (γ + β) * (uM u * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T (γ + β) = Ψ (nb β * (uM u * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T β := by
  have e2 : ((γ + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = γ.1 + β.1 := rfl
  rw [kunf.nb_add h.nb, mul_assoc, hΨ _ (kunf.nb_rat h.nb hγ) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.fix_nb_k h γ)]
  congr 1
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k
  rw [e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    kunf.psi_rat d.ok.good.std T ⟨γ, hγ⟩, inv_one, one_mul]
theorem perFE_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (Ψ : d.G → ℝ≥0∞) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g)
    (T : nF σ d.Y d.b) (x : d.G) (γ : nA σ d.Y d.b) (hγ : γ ∈ nF σ d.Y d.b) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Ψ (nb (γ + β) * (uM u * x)) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T (γ + β)‖ₑ = Ψ (nb β * (uM u * x)) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T β‖ₑ := by
  have e2 : ((γ + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = γ.1 + β.1 := rfl
  rw [kunf.nb_add h.nb, mul_assoc, hΨ _ (kunf.nb_rat h.nb hγ) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.fix_nb_k h γ)]
  congr 2
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k
  rw [e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    kunf.psi_rat d.ok.good.std T ⟨γ, hγ⟩, inv_one, one_mul]
theorem shift_eq_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (r b u : Fin L.n → AE F E) (s a : AF F) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (r + b) * cM (u, s + a) = (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L r * cM (0, s)) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) := by
  have e1 : cM (u, s + a) = cM (0, s) * cM (u, a) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_split_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.centre_additive h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_split_k h u a, ← mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_comm_k h, mul_assoc]
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_add_k, e1]
  simp only [mul_assoc]
  rw [← mul_assoc (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b) (cM (0, s)), _root_.PositivityTheory.SiegelWeilFormula.Act.C5.unipotent_commutes_centre h, mul_assoc]
theorem rr_rat_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {r : Fin L.n → AE F E} (hr : r ∈ L.ratV) {s : AF F}
    (hs : s ∈ (algebraMap F (AF F)).range) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L r * cM (0, s) ∈ rat2 σ d.Y :=
  mul_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_rat_k hr) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_rat_k h (c := (0, s)) (zero_mem _) hs)
theorem rr_fix_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (r : Fin L.n → AE F E) (s : AF F) (k) :
    inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L r * cM (0, s)) k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.fix_mul_k (L := L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.fix_sM_k r) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.fix_cM_k h (0, s)) k
theorem pt_eq_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (x : d.G) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    nb β * (uM u * x) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).1) *
      (cM (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).2) * (L.j (nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * x)) := by
  calc nb β * (uM u * x) = (L.j (nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β) * cM (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β))) * x := by
        rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.nb_split_k (R := R) h β]
        simp only [mul_assoc]
        rw [← mul_assoc (cM (0, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β)) (uM u), ← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_comm_k h, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cM_split_k h]
    _ = _ := by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.move_k h]; simp only [mul_assoc]
instance countable_ratV_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : Countable L.ratV := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have h : ((L.ratV : AddSubgroup (Fin L.n → AE F E)) : Set (Fin L.n → AE F E)).Countable := by
    refine (Set.countable_range (GlobalTheory.ThK.incV F : (Fin L.n → E) → _)).mono fun u hu => ?_
    obtain ⟨v, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k hu
    exact ⟨v, rfl⟩
  exact h.to_subtype
theorem coordsC_ck_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β, P β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℂ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g) (x : d.G) :
    ∫ p, Ψ (nb p.2 * (uM p.1 * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2 ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      c.toReal • ∫ p, Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' p.1
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) := by
  haveI : Fact (IsFrame2 σ d.Y d.b) := ⟨d.ok.frame⟩
  haveI : Fact (IsFrame2 σ L.Y L.b) := ⟨L.ok.frame⟩
  haveI := hc.2.1
  haveI := hc'.2.1
  haveI := hU.2.1
  obtain ⟨-, -, hiff⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pEquiv_k h
  let PM : (nA σ d.Y d.b) ≃ᵐ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b) := P.toHomeomorph.toMeasurableEquiv
  have hPM : ∀ β, PM β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) := hP
  have hPc' : lam.map PM = c • ((ν.prod (lamA F)).prod lam') := hPc
  have hZ : IsAddFundamentalDomain (L.ratV.prod (fA F)) (𝓤 ×ˢ 𝓐) (ν.prod (lamA F)) := fd_prod' hU.2.2.1 h𝓐
  have key := chainC (νu := ν.restrict 𝓤) (ΓN := nF σ d.Y d.b) (ΓZ := L.ratV.prod (fA F)) (ΓN' := nF σ L.Y L.b)
    hPc' (fun a b => map_add P a b) (fun β => by rw [hPM, hiff, AddSubgroup.mem_prod]) hc.2.2.1 hZ hc'.2.2.1
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_tau_k h).measurable
    (fun p => Ψ (nb p.2 * (uM p.1 * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2)
    (fun q => Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L q.2.2.1 * (cM (q.2.1, q.2.2.2) * (L.j (nb' q.1) * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' q.1)
    (fun γ hγ u β => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.perF_k h Ψ hΨ T x γ hγ u β)
    (fun g hg w => by
      obtain ⟨hg1, hg2⟩ := AddSubgroup.mem_prod.1 hg
      obtain ⟨β'', u, b, a⟩ := w
      show Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (g.1 + b) * (cM (u, g.2 + a) * _)) * _ = Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * (cM (u, a) * _)) * _
      rw [← mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.shift_eq_k h, mul_assoc (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L g.1 * cM (0, g.2)), hΨ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.rr_rat_k h hg1 hg2) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.rr_fix_k h g.1 g.2)]
      simp only [mul_assoc])
    (fun u β => by
      rw [hPM]
      show Ψ (nb β * (uM u * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T β = Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).1) *
        (cM (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).2) * (L.j (nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.pt_eq_k (R := R) h x u β]
      congr 1
      unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.tr_sub_k L hT β])
  rw [key, ← Measure.prod_restrict]
theorem coordsE_ck_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β, P β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℝ≥0∞) (hΨm : Measurable Ψ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g) (x : d.G) :
    ∫⁻ p, Ψ (nb p.2 * (uM p.1 * x)) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      c * ∫⁻ p, Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' p.1‖ₑ
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) := by
  haveI : Fact (IsFrame2 σ d.Y d.b) := ⟨d.ok.frame⟩
  haveI : Fact (IsFrame2 σ L.Y L.b) := ⟨L.ok.frame⟩
  haveI := hc.2.1
  haveI := hc'.2.1
  haveI := hU.2.1
  obtain ⟨-, -, hiff⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pEquiv_k h
  let PM : (nA σ d.Y d.b) ≃ᵐ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b) := P.toHomeomorph.toMeasurableEquiv
  have hPM : ∀ β, PM β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) := hP
  have hPc' : lam.map PM = c • ((ν.prod (lamA F)).prod lam') := hPc
  have hZ : IsAddFundamentalDomain (L.ratV.prod (fA F)) (𝓤 ×ˢ 𝓐) (ν.prod (lamA F)) := fd_prod' hU.2.2.1 h𝓐
  have key := chainE (νu := ν.restrict 𝓤) (ΓN := nF σ d.Y d.b) (ΓZ := L.ratV.prod (fA F)) (ΓN' := nF σ L.Y L.b)
    hPc' (fun a b => map_add P a b) (fun β => by rw [hPM, hiff, AddSubgroup.mem_prod]) hc.2.2.1 hZ hc'.2.2.1
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.continuous_tau_k h).measurable
    (fun p => Ψ (nb p.2 * (uM p.1 * x)) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ)
    (fun q => Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L q.2.2.1 * (cM (q.2.1, q.2.2.2) * (L.j (nb' q.1) * x))) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' q.1‖ₑ)
    (fun γ hγ u β => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.perFE_k h Ψ hΨ T x γ hγ u β)
    (fun g hg w => by
      obtain ⟨hg1, hg2⟩ := AddSubgroup.mem_prod.1 hg
      obtain ⟨β'', u, b, a⟩ := w
      show Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (g.1 + b) * (cM (u, g.2 + a) * _)) * _ = Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * (cM (u, a) * _)) * _
      rw [← mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.shift_eq_k h, mul_assoc (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L g.1 * cM (0, g.2)), hΨ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.rr_rat_k h hg1 hg2) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.rr_fix_k h g.1 g.2)]
      simp only [mul_assoc])
    (fun u β => by
      rw [hPM]
      show Ψ (nb β * (uM u * x)) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T β‖ₑ = Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).1) *
        (cM (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β + (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.tau_k L uM nb' δ (u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)).2) * (L.j (nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * x))) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)‖ₑ
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.pt_eq_k (R := R) h x u β]
      congr 2
      unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.tr_sub_k L hT β])
  rw [key, ← Measure.prod_restrict]
end PositivityTheory.SiegelWeilFormula.Act.C5.CoordK
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CoordsCK

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem coordsC_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β, P β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℂ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g) (x : d.G) :
    ∫ p, Ψ (nb p.2 * (uM p.1 * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2 ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      c.toReal • ∫ p, Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' p.1
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) := by
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.coordsC_ck_k h hc hU hc' hT h𝓐 hP hPc Ψ hΨ x
theorem coordsE_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β, P β = ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.pb_k L β, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.pa_k L δ β), _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℝ≥0∞) (hΨm : Measurable Ψ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g) (x : d.G) :
    ∫⁻ p, Ψ (nb p.2 * (uM p.1 * x)) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      c * ∫⁻ p, Ψ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * ‖_root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k T' p.1‖ₑ
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) := by
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C5.CoordK.coordsE_ck_k h hc hU hc' hT h𝓐 hP hPc Ψ hΨm hΨ x
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end
end
