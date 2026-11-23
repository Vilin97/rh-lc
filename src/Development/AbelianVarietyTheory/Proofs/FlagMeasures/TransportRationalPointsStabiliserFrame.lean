module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGram
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
public import Formalism.LocalToGlobal.HermitianForms.TiedStep
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemUnitaryGroupGramMatrixIffMapSymm
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Mathlib.Tactic.Linter.Style
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryExtendByIdentityOnFixSetStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryFixingActsOnComplementFrameStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryFixingMemRationalStabiliserStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlacesFrameMatrixEqRationalOfRationalStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnitaryFirstHermitianSpaceIsUnit

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem GlobalTheory.St.gramN_unitary_isUnit : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, (y₀.map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * y₀ = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm → ∃ g : GL (Fin (D.R.N 0)) D.host.E, (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = y₀.map X.ιE := by
  intro D X u wt hW y₀ hy
  obtain ⟨Q, Qi, G', hQQi, hQiQ, -, -, -, -, -, hM⟩ := GlobalTheory.St.qFrame_basis_gram D X u wt hW
  set G := (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm with hG
  have hJ := X.B.I.J_det
  have hJJ : X.B.I.J * X.B.I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hJ)
  have h1 : (Q.map (starRingEnd X.B.I.E))ᵀ * (Qi.map (starRingEnd X.B.I.E))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hQiQ]; simp
  have hdetM : IsUnit (Matrix.fromBlocks G 0 0 G').det := by
    rw [← hM]
    apply Matrix.isUnit_det_of_right_inverse (B := Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ)
    calc (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * Q * (Qi * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ)
        = (Q.map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * (Q * Qi) * X.B.I.J⁻¹ * (Qi.map (starRingEnd X.B.I.E))ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = (Q.map (starRingEnd X.B.I.E))ᵀ * (X.B.I.J * X.B.I.J⁻¹) * (Qi.map (starRingEnd X.B.I.E))ᵀ := by
          rw [hQQi]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hJJ, Matrix.mul_one, h1]
  rw [Matrix.det_fromBlocks_zero₂₁] at hdetM
  have hGdet : G.det ≠ 0 := (isUnit_of_mul_isUnit_left hdetM).ne_zero
  have hy0 : y₀.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hy
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact hGdet this.symm
  have hd : (y₀.map X.ιE).det = X.ιE y₀.det := by
    simpa using (RingHom.map_det X.ιE.toRingHom y₀).symm
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (y₀.map X.ιE) ?_, rfl⟩
  rw [hd]; exact (map_ne_zero X.ιE).mpr hy0
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnitaryFirstHermitianSpaceIsUnitStatement

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.gramUnitary_firstHermitianSpace_isUnit : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, (y₀.map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * y₀ = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm → ∃ g : GL (Fin (D.R.N 0)) D.host.E, (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = y₀.map X.ιE := by
  first | exact @GlobalTheory.St.gramN_unitary_isUnit | exact GlobalTheory.St.gramN_unitary_isUnit | (intros; apply GlobalTheory.St.gramN_unitary_isUnit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemUnitaryGroupGramMatrixIffMapSymmStatement

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_unitaryGroup_gramMatrix_iff_map_symm : ∀ (D : D7) (X : HidaSetting D) (g : GL (Fin (D.R.N 0)) D.host.E), g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) ↔ (((g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map X.ιE.symm).map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map X.ιE.symm = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm := by
  first | exact @GlobalTheory.St.mem_UJ_gramN_iff_map_symm | exact GlobalTheory.St.mem_UJ_gramN_iff_map_symm | (intros; apply GlobalTheory.St.mem_UJ_gramN_iff_map_symm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalMatrixRepresentsAdelicPointInFrame

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.St

theorem repF_of_rational : ∀ (D : D7) (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), IsAdeleIso X ιA → ∀ (h : X.B.I.Gf) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E), X.B.I.fmat h = γ₀.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), y.1.1 = (y₀.map X.ιE).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) → RepF X wt ιA h y := by
  intro D X wt ιA hA h γ₀ y₀ hf hq y hy j
  have hs : ∀ i, ιA.symm (y.1.1 i j) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (y₀ i j) := by
    intro i
    rw [hy, RingEquiv.symm_apply_eq, Matrix.map_apply, Matrix.map_apply, hA.1]
  simp_rw [hs]
  have hl : X.B.I.fmat h *ᵥ qA X wt j =
      fun k => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((γ₀ *ᵥ X.crd (qFr wt j)) k) := by
    rw [hf]
    funext k
    show (γ₀.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ
      ((Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) ∘ X.crd (qFr wt j))) k = _
    rw [← RingHom.map_mulVec]
  rw [hl, hq j]
  funext k

  simp [qA, incl, Finset.sum_apply, map_sum, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.St
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalMatrixRepresentsAdelicPointInFrameStatement

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rational_matrix_represents_adelic_point_in_frame : ∀ (D : D7) (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), IsAdeleIso X ιA → ∀ (h : X.B.I.Gf) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E), X.B.I.fmat h = γ₀.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), y.1.1 = (y₀.map X.ιE).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) → RepF X wt ιA h y := by
  first | exact @GlobalTheory.St.repF_of_rational | exact GlobalTheory.St.repF_of_rational | (intros; apply GlobalTheory.St.repF_of_rational <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalStabiliserPointFromUnitaryFixingFrame

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GamRat

theorem gam_rat : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ : Gam X u), ∃ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧ (∀ v, uMat ((γ : X.B.I.GA).1 v) = (X.B.I.P v)⁻¹ * (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v) ∧ X.B.I.fmat (γ : X.B.I.GA).2 = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) ∧ ∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x := by
  intro D X u γ
  obtain ⟨hGF, hH⟩ := Subgroup.mem_inf.1 γ.2
  obtain ⟨γ₀, hU, h1, h2⟩ := (Formalism.MainNotions.LeviCoordinates.rr_mem_GF _ _).1 hGF
  refine ⟨γ₀, hU, h1, h2, ?_⟩
  intro x hx
  have hf := (Subgroup.mem_prod.1 hH).2 x hx
  rw [h2] at hf
  have : Nontrivial (Af X.B.I.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 X.B.I.F)
    let w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.F) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h0 : (0 : w.adicCompletion X.B.I.F) = 1 := congrArg (fun a : Af X.B.I.F => a w) h
    exact zero_ne_one h0
  funext i
  apply Formalism.UG.P.inclE_injective X.B.I.F X.B.I.E (Af X.B.I.F)
  calc Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (((γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x) i)
      = ((γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ
          (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ∘ x)) i := RingHom.map_mulVec _ _ _ _
    _ = _ := congrFun hf i

end GlobalTheory.GamRat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalStabiliserPointFromUnitaryFixingFrameStatement

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalStabiliser_point_from_unitary_fixing_frame : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ : Gam X u), ∃ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J ∧ (∀ v, uMat ((γ : X.B.I.GA).1 v) = (X.B.I.P v)⁻¹ * (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v) ∧ X.B.I.fmat (γ : X.B.I.GA).2 = (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) ∧ ∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x := by
  first | exact @GlobalTheory.GamRat.gam_rat | exact GlobalTheory.GamRat.gam_rat | (intros; apply GlobalTheory.GamRat.gam_rat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRationalPointsStabiliserFrame

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.transport_rational_points : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (Φ : Hfin X u ≃* Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ (h : Hfin X u) y, RepF X wt ιA (h : X.B.I.Gf) y ↔ Φ h = y) → (∀ γ : Gam X u, ∃ g : GL (Fin (D.R.N 0)) D.host.E, g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) ∧ (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g) ∧ (∀ g : GL (Fin (D.R.N 0)) D.host.E, g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → ∃ γ : Gam X u, (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g) ∧ ∀ (γ : Gam X u) (g : GL (Fin (D.R.N 0)) D.host.E), (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g → sTil X wt (iotaI X u γ : X.B.I.Ginf) = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) g.1 := by
  intro D X u wt ιA hW hA Φ hΦ
  have hmem : ∀ g : GL (Fin (D.R.N 0)) D.host.E, g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g ∈ Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    intro g hg
    refine Formalism.UG.P.bc_mem _ _ _ ?_ _ g hg
    ext x
    simp [Formalism.UG.sigR, Formalism.UG.inclE]
  have key : ∀ (h : Hfin X u) (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E) (g : GL (Fin (D.R.N 0)) D.host.E), X.B.I.fmat (h : X.B.I.Gf) = γ₀.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) → (∀ j, γ₀ *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i)) → (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = y₀.map X.ιE → ∀ hg : g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)), (Φ h).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g := by
    intro h γ₀ y₀ g hf hq hgy hg
    have hr := GlobalTheory.T.rational_matrix_represents_adelic_point_in_frame D X wt ιA hA h γ₀ y₀ hf hq ⟨_, hmem g hg⟩ (by
      show (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map _ = _
      rw [hgy])
    rw [(hΦ h _).1 hr]
  have hinj : ∀ g g' : GL (Fin (D.R.N 0)) D.host.E, Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g' → g = g' := by
    intro g g' h
    haveI : Nontrivial (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      let v : HeightOneSpectrum (𝓞 D.host.F) :=
        ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField D.host.F)⟩
      exact ⟨⟨0, 1, fun h => by
        have := congrArg (fun x : FiniteAdeleRing (𝓞 D.host.F) D.host.F => x v) h
        exact zero_ne_one (α := v.adicCompletion D.host.F) this⟩⟩
    have hc := congrArg Units.val h
    rw [Formalism.UG.P.bc_coe, Formalism.UG.P.bc_coe] at hc
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact Formalism.UG.P.inclE_injective D.host.F D.host.E _ (congrFun (congrFun hc i) j)
  refine ⟨fun γ => ?_, fun g hg => ?_, fun γ g hγg => ?_⟩
  · obtain ⟨γ₀, hu, -, hf, hfix⟩ := GlobalTheory.T.rationalStabiliser_point_from_unitary_fixing_frame D X u γ
    obtain ⟨y₀, hy, hq⟩ := GlobalTheory.T.rational_unitary_fixing_acts_on_complement_frame D X u wt hW γ₀ hu hfix
    obtain ⟨g, hgy⟩ := GlobalTheory.T.gramUnitary_firstHermitianSpace_isUnit D X u wt hW y₀ hy
    have hg : g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) :=
      (GlobalTheory.T.mem_unitaryGroup_gramMatrix_iff_map_symm D X g).2 (by
        have e : (y₀.map X.ιE).map X.ιE.symm = y₀ := Matrix.ext fun i j => by simp
        rw [hgy, e]; exact hy)
    exact ⟨g, hg, key (iotaF X u γ) γ₀ y₀ g hf hq hgy hg⟩
  · obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, y₀ = (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map X.ιE.symm := ⟨_, rfl⟩
    have hy := (GlobalTheory.T.mem_unitaryGroup_gramMatrix_iff_map_symm D X g).1 hg
    rw [← hy₀] at hy
    obtain ⟨γ₀, hu, hfix, hq⟩ := GlobalTheory.T.rational_unitary_extend_by_identity_on_fixSet D X u wt hW y₀ hy
    obtain ⟨γ, -, hf⟩ := GlobalTheory.T.rational_unitary_fixing_mem_rationalStabiliser D X u γ₀ hu hfix
    have hgy : (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) = y₀.map X.ιE :=
      Matrix.ext fun i j => by simp [hy₀]
    exact ⟨γ, key (iotaF X u γ) γ₀ y₀ g hf hq hgy hg⟩
  · obtain ⟨γ₀, hu, hinf, hf, hfix⟩ := GlobalTheory.T.rationalStabiliser_point_from_unitary_fixing_frame D X u γ
    obtain ⟨y₀, hy, hq⟩ := GlobalTheory.T.rational_unitary_fixing_acts_on_complement_frame D X u wt hW γ₀ hu hfix
    obtain ⟨g', hgy⟩ := GlobalTheory.T.gramUnitary_firstHermitianSpace_isUnit D X u wt hW y₀ hy
    have hg' : g' ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) :=
      (GlobalTheory.T.mem_unitaryGroup_gramMatrix_iff_map_symm D X g').2 (by
        have e : (y₀.map X.ιE).map X.ιE.symm = y₀ := Matrix.ext fun i j => by simp
        rw [hgy, e]; exact hy)
    have e1 := key (iotaF X u γ) γ₀ y₀ g' hf hq hgy hg'
    have e2 : g = g' := hinj g g' (hγg.symm.trans e1)
    subst e2
    rw [hgy]
    exact GlobalTheory.T.realPlaces_frameMatrix_eq_rational_of_rational D X u wt hW _ γ₀ y₀ hinf hq
end
end
