module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfLeaves
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CayleyAlgebraicHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction0
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ClassicalToWeakSolution
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymbolLevi
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeActionHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFixesTailCoords

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CayleySmoothnessHolds

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def MC (m : ℕ) : Type := Matrix (Fin m) (Fin m) ℂ

noncomputable instance instNRMC (m : ℕ) : NormedRing (MC m) := Matrix.linftyOpNormedRing

noncomputable instance instNAMC (m : ℕ) : NormedAlgebra ℝ (MC m) := Matrix.linftyOpNormedAlgebra

instance instFDMC (m : ℕ) : FiniteDimensional ℝ (MC m) :=
  inferInstanceAs (FiniteDimensional ℝ (Matrix (Fin m) (Fin m) ℂ))

instance instCSMC (m : ℕ) : CompleteSpace (MC m) := FiniteDimensional.complete ℝ (MC m)

def toMC (m : ℕ) : Matrix (Fin m) (Fin m) ℂ ≃L[ℝ] MC m :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.refl ℝ (Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ ≃ₗ[ℝ] MC m)

def cayMC {m : ℕ} (g₀ X : MC m) : MC m := g₀ * ((1 + X) * Ring.inverse (1 - X))

def cinvMC {m : ℕ} (a Y : MC m) : MC m := (a * Y - 1) * Ring.inverse (a * Y + 1)

theorem cay_eq_MC {k r : ℕ} (g₀ : B.Mat k r) :
    (fun X : B.Mat k r => g₀ * cay X) = fun X => (toMC _).symm (cayMC (toMC _ g₀) (toMC _ X)) := by
  funext X
  show g₀ * ((1 + X) * (1 - X)⁻¹) = g₀ * ((1 + X) * Ring.inverse (1 - X))
  rw [Matrix.nonsing_inv_eq_ringInverse]

theorem cayInv_eq_MC {k r : ℕ} (g₀ : B.Mat k r) :
    (fun m : B.Mat k r => cayInv (g₀⁻¹ * m)) = fun m => (toMC _).symm (cinvMC (toMC _ g₀⁻¹) (toMC _ m)) := by
  funext m
  show (g₀⁻¹ * m - 1) * (g₀⁻¹ * m + 1)⁻¹ = (g₀⁻¹ * m - 1) * Ring.inverse (g₀⁻¹ * m + 1)
  rw [Matrix.nonsing_inv_eq_ringInverse (g₀⁻¹ * m + 1)]

theorem cayMC_contDiffAt {m : ℕ} (g₀ X : MC m) (hX : IsUnit (1 - X)) : ContDiffAt ℝ ∞ (cayMC g₀) X := by
  obtain ⟨u, hu⟩ := hX
  have h1 : ContDiffAt ℝ ∞ (fun Y : MC m => Ring.inverse (1 - Y)) X := by
    have := contDiffAt_ringInverse (𝕜 := ℝ) (n := ∞) u
    rw [hu] at this
    exact this.comp X (contDiffAt_const.sub contDiffAt_id)
  exact contDiffAt_const.mul ((contDiffAt_const.add contDiffAt_id).mul h1)

theorem cinvMC_contDiffAt {m : ℕ} (a Y : MC m) (hY : IsUnit (a * Y + 1)) : ContDiffAt ℝ ∞ (cinvMC a) Y := by
  obtain ⟨u, hu⟩ := hY
  have h1 : ContDiffAt ℝ ∞ (fun Z : MC m => Ring.inverse (a * Z + 1)) Y := by
    have := contDiffAt_ringInverse (𝕜 := ℝ) (n := ∞) u
    rw [hu] at this
    exact this.comp Y ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const)
  exact ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const).mul h1

theorem cayley_smoothness_holds : CaySmooth := by
  intro k r g₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((Units.isOpen (R := MC (2 * r + k + 1))).preimage
      (continuous_const.sub continuous_id)).preimage (toMC _).continuous
  · exact ((Units.isOpen (R := MC (2 * r + k + 1))).preimage
      ((continuous_const.mul continuous_id).add continuous_const)).preimage (toMC _).continuous
  · rw [cay_eq_MC g₀]
    intro X hX
    have hX' : IsUnit (1 - toMC _ X) := hX
    exact ((toMC _).symm.contDiff.contDiffAt.comp X
      ((cayMC_contDiffAt (toMC _ g₀) _ hX').comp X (toMC _).contDiff.contDiffAt)).contDiffWithinAt
  · rw [cayInv_eq_MC g₀]
    intro m hm
    have hm' : IsUnit (toMC _ g₀⁻¹ * toMC _ m + 1) := hm
    exact ((toMC _).symm.contDiff.contDiffAt.comp m
      ((cinvMC_contDiffAt (toMC _ g₀⁻¹) _ hm').comp m (toMC _).contDiff.contDiffAt)).contDiffWithinAt

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupVectorSpace

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem group_vector_space : GVGrp := by
  intro k r
  refine ⟨⟨⟨1 + 1, (1 / 2 : ℂ) • 1, ?_, ?_⟩, rfl⟩, fun g₀ hg₀ => ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_one, smul_add, ← add_smul]
    norm_num
  · rw [Matrix.smul_mul, Matrix.one_mul, smul_add, ← add_smul]
    norm_num
  · have hdet : IsUnit g₀.det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH hg₀
    refine ⟨Matrix.nonsing_inv_mul g₀ hdet, fun h hh => ⟨Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul hg₀ hh,
      Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul (Formalism.FourierDecayAlt.P.PBM.GV_inv_mem g₀ hg₀) hh, ?_⟩⟩
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv g₀ hdet, Matrix.one_mul]

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftTypeActionHolds

section

@[expose] public section

open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LeftTypeActionHermitianCurvature

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)} {i : Fin (r + 1)} {mm : ℕ∞}

theorem mem_left (hD : IsDom k r z z' i D) {g h : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hh : h ∈ UWset k r z) : h * g ∈ Glev k r i ∩ D := by
  have := Qx8.dom_mem hD hg hh (Qx8.nlev_one _) (Qx8.uw_one z') (Qx8.nlev_one _)
  simpa using this

theorem J_left (hπ : IsCRepOn (UWset k r z) π) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D) {g h : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) (hh : h ∈ UWset k r z) : J (h * g) = (π h).comp (J g) := by
  have e1 := hJ.2.2.2 g hg 1 (Qx8.uw_one z) 1 (Qx8.uw_one z')
  have e2 := hJ.2.2.2 g hg h hh 1 (Qx8.uw_one z')
  rw [Matrix.one_mul, Matrix.mul_one, hπ.1] at e1
  rw [Matrix.mul_one] at e2
  have e3 : (1 : Wp →L[ℂ] Wp).comp ((J g).comp (π' 1)) = (J g).comp (π' 1) := ContinuousLinearMap.id_comp _
  rw [e3] at e1
  rw [e2, ← e1]

theorem ld_left (hD : IsDom k r z z' i D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = B.comp (J g)) {X : Mx k r} (hX : QrD.InLieW k r z X)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : LdV X F g = (B.comp (QrD.dOp π X)).comp (J g) := by
  have h := QrD.dOp_hasDeriv hπ hc hX
  let L : (Wp →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
    (ContinuousLinearMap.compL ℂ Wq Wp Wp B).comp ((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip (J g))
  have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have h3 : (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * g)) =
      (L.restrictScalars ℝ) ∘ fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    rw [hF _ (mem_left hD hg (QrD.exp_uw hX t)), J_left hπ hJ hg (QrD.exp_uw hX t)]
    rfl
  unfold LdV
  rw [h3]
  exact h2.deriv

theorem lz_left (hD : IsDom k r z z' i D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = B.comp (J g)) {Z : Mx k r}
    (h1 : QrD.InLieW k r z (hpart1 (Hpk k r) Z)) (h2 : QrD.InLieW k r z (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    LZ (Hpk k r) Z F g = (B.comp (QrD.ecOp π Z)).comp (J g) := by
  unfold LZ QrD.ecOp
  rw [ld_left hD hπ hc hJ hF h1 hg, ld_left hD hπ hc hJ hF h2 hg]
  ext v
  simp

theorem fold_left (hD : IsDom k r z z' i D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, QrD.InLieW k r z (hpart1 (Hpk k r) p.2) ∧ QrD.InLieW k r z (hpart2 (Hpk k r) p.2)) :
    ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (B : Wp →L[ℂ] Wp), (∀ g ∈ Glev k r i ∩ D, F g = B.comp (J g)) →
      ∀ g ∈ Glev k r i ∩ D, ∀ v,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + LZ (Hpk k r) p.2 y).foldl (fun h T => T h) F g v =
          B ((L.map fun p => fun y : Wp => p.1 • y + EcRep (Hpk k r) π p.2 y).foldr (fun T h => T h) (J g v)) := by
  induction L with
  | nil =>
    intro F B hF g hg v
    simp only [List.map_nil, List.foldl_nil, List.foldr_nil]
    rw [hF g hg]
    rfl
  | cons p L ih =>
    intro F B hF g hg v
    have hp := hL p (by simp)
    simp only [List.map_cons, List.foldl_cons, List.foldr_cons]
    rw [ih (fun q hq => hL q (by simp [hq])) (p.1 • F + LZ (Hpk k r) p.2 F) (p.1 • B + B.comp (QrD.ecOp π p.2))
      (fun x hx => by
        simp only [Pi.add_apply, Pi.smul_apply]
        rw [lz_left hD hπ hc hJ hF hp.1 hp.2 hx, hF x hx]
        ext v
        simp) g hg v, QrD.ecRep_eq hπ hc hp.1 hp.2]
    simp

end LeftTypeActionHermitianCurvature

theorem left_type_action_holds : LeftTypeAction0 := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D mm _ _ hD hπ hc J hJ g hg Bs hB w v
  unfold capLft capRep qmFrev qmF
  simp only [Finset.sum_apply, Pi.smul_apply, _root_.sum_apply, _root_.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have e1 := LeftTypeActionHermitianCurvature.fold_left hD hπ hc hJ
    (List.ofFn fun j : Fin m => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0 : ℂ), unitB (Hpk k r) Bs (σ j) j))
    (by
      intro p hp
      rw [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j) J 1 (fun x _ => (ContinuousLinearMap.id_comp _).symm) g hg v
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul] at e1
  simp only [id]
  rw [e1]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBasisHolds

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LieBasisConstruction

def lieSubR (k r : ℕ) : Submodule ℝ (B.Mat k r) where
  carrier := {X | B.inLie k r X}
  add_mem' := by
    intro X Y hX hY
    unfold B.inLie at *
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc _ = (Xᴴ * _ + _ * X) + (Yᴴ * _ + _ * Y) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  zero_mem' := by
    unfold B.inLie
    simp
  smul_mem' := by
    intro c X hX
    unfold B.inLie at *
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

end LieBasisConstruction

theorem lie_basis_holds : LieBasis := by
  intro k r
  let S := LieBasisConstruction.lieSubR k r
  let b := Module.finBasis ℝ S
  let L0 : (Fin (Module.finrank ℝ S) → ℝ) →ₗ[ℝ] B.Mat k r := S.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hinj : LinearMap.ker L0 = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact S.injective_subtype.comp b.equivFun.symm.injective
  obtain ⟨M0, hM0⟩ := L0.exists_leftInverse_of_injective hinj
  have hML : ∀ y, M0 (L0 y) = y := fun y => LinearMap.congr_fun hM0 y
  refine ⟨Module.finrank ℝ S, LinearMap.toContinuousLinearMap L0, LinearMap.toContinuousLinearMap M0,
    fun x => (b.equivFun.symm x).2, fun x => hML x, fun X hX => ?_⟩
  have e : L0 (b.equivFun ⟨X, hX⟩) = X := by simp [L0]
  show L0 (M0 X) = X
  calc L0 (M0 X) = L0 (M0 (L0 (b.equivFun ⟨X, hX⟩))) := by rw [e]
    _ = X := by rw [hML, e]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDomainIsDomain

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem positive_domain_is_domain : IsDomOmPlus := fun _ _ _ _ hz hz' =>
  Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus hz hz'

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfRest

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem group_chart_holds : GChart := gChart_of lie_basis_holds cayley_algebraic_holds group_vector_space cayley_smoothness_holds

theorem unitary_capelli_holds : UCap := uCap_of positive_domain_is_domain right_type_action_holds left_type_action_holds

theorem jfSmoothBuilt_of_rest (hN : NDiff) (hP : GEqsPost) (hC : SmoothOfCoeffs) (hE : ChartEqs) (hR : EllRegW) :
    JfSmoothBuilt :=
  jfSmoothBuilt_of_leaves hN unitary_capelli_holds hP hC group_chart_holds hE classical_to_weak_solution hR JfS.symbol_nilpotent_holds lie_stabilizer_splitting

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
end
