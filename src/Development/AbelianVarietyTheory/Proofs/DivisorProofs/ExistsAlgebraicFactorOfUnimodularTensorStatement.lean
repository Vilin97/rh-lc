module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionProps
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataLatticeFactorProps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataMatrixActionRingHomProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorPairingFactorInclusionPeriodsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorActionCompatibleWithDegeneration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationTauBalancedOfAdjointIntMatriceStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionPropsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mumfordTensorData_factorInclusion_projection_props : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (i₀ : Fin r), IsMonHom (T.inc i₀) ∧ T.inc i₀ ≫ T.pr i₀ = 𝟙 _ ∧ T.pr i₀ ≫ T.inc i₀ = T.act (Matrix.single i₀ i₀ 1) ∧ ∀ y, D'.c (T.xi i₀ y) = D.c y ≫ T.inc i₀ := by
  first | exact @GlobalTheory.Mum.tens_inc_pr_facts | exact GlobalTheory.Mum.tens_inc_pr_facts | (intros; apply GlobalTheory.Mum.tens_inc_pr_facts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataLatticeFactorPropsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mumfordTensorData_latticeFactor_props : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (s : SymUnit r) (i₀ : Fin r), letI := T.mod s; (∀ y, T.xp i₀ (T.xi i₀ y) = y) ∧ (∀ z, T.xi i₀ (T.xp i₀ z) = TensO.idem s i₀ • z) ∧ Function.Injective (fun y => star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y) ∧ ∀ z, ∃ y, star (TensO.idem s i₀) • z = star (TensO.idem s i₀) • TensO.binv s • T.xi i₀ y := by
  first | exact @GlobalTheory.Mum.tens_factor_latt | exact GlobalTheory.Mum.tens_factor_latt | (intros; apply GlobalTheory.Mum.tens_factor_latt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataMatrixActionRingHomPropertiesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mumfordTensorData_matrixAction_ringHom_properties : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W), (∀ a, IsMonHom (T.act a)) ∧ T.act 1 = 𝟙 _ ∧ (∀ a b, T.act (a * b) = T.act b ≫ T.act a) ∧ ∀ a b, T.act (a + b) = padd D'.P.A (T.act a) (T.act b) := by
  first | exact @GlobalTheory.Mum.TensAct.act_ring | exact GlobalTheory.Mum.TensAct.act_ring | (intros; apply GlobalTheory.Mum.TensAct.act_ring <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDefStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.rosatiAdj_mumfordTensorPower_of_posDef : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W) (a : TensO (symUnitOf W h)), RosatiAdj D'.toPre.P.A D'.toPre.P.L (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) := by
  first | exact @GlobalTheory.Mum.rosatiAdj_tens | exact GlobalTheory.Mum.rosatiAdj_tens | (intros; apply GlobalTheory.Mum.rosatiAdj_tens <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorActionCompatibleWithDegenerationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.tensor_action_compatible_with_degeneration : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (s : SymUnit r), letI := T.mod s; ∀ (a : TensO s) (y : D'.X), D'.c (a • y) = D'.c y ≫ T.act (TensO.mat s a) := by
  first | exact @GlobalTheory.Mum.Tens.c_smul | exact GlobalTheory.Mum.Tens.c_smul | (intros; apply GlobalTheory.Mum.Tens.c_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegDataPeriodsBalancedMatrixAction

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TensBal

theorem transpose_mul_eq {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det)
    (a : TensO (symUnitOf W h)) :
    (TensO.mat _ a).transpose * (W + W.transpose) = (W + W.transpose) * TensO.mat _ (star a) := by
  have hb : ((symUnitOf W h).1 : Matrix (Fin r) (Fin r) ℤ) = W + W.transpose := rfl
  rw [TensO.star_def]
  show _ = (W + W.transpose) * (((((symUnitOf W h).1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
    (TensO.mat _ a).transpose * ((symUnitOf W h).1 : Matrix (Fin r) (Fin r) ℤ)))
  rw [hb.symm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem tauBal_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W), letI := T.mod (symUnitOf W h); ∀ a : TensO (symUnitOf W h), D'.toPre.TauBal (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) (fun y => a • y) (fun y => star a • y) := by
  intro R _ _ _ _ D D' r W h _ T a
  exact GlobalTheory.T.tensorDegeneration_tauBalanced_of_adjointIntMatrices R _ D D' W T (TensO.mat _ a) (TensO.mat _ (star a)) (transpose_mul_eq W h a)

end GlobalTheory.Mum.TensBal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegDataPeriodsBalancedMatrixActionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.tensorDegData_periods_balanced_matrixAction : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W), letI := T.mod (symUnitOf W h); ∀ a : TensO (symUnitOf W h), D'.toPre.TauBal (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) (fun y => a • y) (fun y => star a • y) := by
  first | exact @GlobalTheory.Mum.TensBal.tauBal_tens | exact GlobalTheory.Mum.TensBal.tauBal_tens | (intros; apply GlobalTheory.Mum.TensBal.tauBal_tens <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicFactorOfUnimodularTensor

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem TensO.idem_binv_alg {r : ℕ} (s : SymUnit r) (i₀ : Fin r)
    (hp : 0 < (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀) :
    (∃ b : ℕ, 0 < b ∧ Star.star (TensO.idem s i₀) * TensO.idem s i₀ =
        b • (Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀)) ∧
      Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀ =
        Star.star (TensO.idem s i₀) * Star.star (TensO.binv s) * TensO.idem s i₀ ∧
      ∃ g : TensO s, g * (Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀) = TensO.idem s i₀ := by
  have hf : Star.star (TensO.binv s) = TensO.binv s := by
    show ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ).transpose *
        (s.1 : Matrix (Fin r) (Fin r) ℤ) = ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ)
    rw [TensO.inv_transpose, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hEE : (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ 1 =
      Matrix.single i₀ i₀ 1 := by simp
  have hET : (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ).transpose = Matrix.single i₀ i₀ 1 := by simp
  have hmain : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
      (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ).transpose * (s.1 : Matrix (Fin r) (Fin r) ℤ) *
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ) =
      ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ) := by
    rw [hET, Matrix.mul_assoc _ (s.1 : Matrix (Fin r) (Fin r) ℤ), Units.mul_inv, Matrix.mul_one, Matrix.mul_assoc, hEE]
  have hefe : Star.star (TensO.idem s i₀) * TensO.binv s * TensO.idem s i₀ = TensO.binv s * TensO.idem s i₀ := hmain
  refine ⟨⟨((s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀).toNat, by omega, ?_⟩, by rw [hf], TensO.ofMat s s.1, ?_⟩
  · rw [hefe]
    have h : ((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) *
        (Matrix.single i₀ i₀ (1 : ℤ) : Matrix (Fin r) (Fin r) ℤ).transpose * (s.1 : Matrix (Fin r) (Fin r) ℤ) *
        Matrix.single i₀ i₀ (1 : ℤ) = ((s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀).toNat •
        (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ)) := by
      rw [hET, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.single i₀ i₀ (1 : ℤ)),
        Matrix.single_mul_mul_single, ← Matrix.mul_smul]
      congr 1
      rw [Matrix.smul_single, nsmul_eq_mul, Int.toNat_of_nonneg hp.le]
      simp
    exact h
  · rw [hefe]
    have h : (s.1 : Matrix (Fin r) (Fin r) ℤ) *
        (((s.1⁻¹ : (Matrix (Fin r) (Fin r) ℤ)ˣ) : Matrix (Fin r) (Fin r) ℤ) * Matrix.single i₀ i₀ (1 : ℤ)) =
        Matrix.single i₀ i₀ (1 : ℤ) := by
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    exact h

theorem Tens.nonempty_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ),
      ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det →
      ∀ T : Tens D.toPre D'.toPre W, 1 ≤ r → (∃ F : Factor D.toPre D'.toPre, F.Alg) := by
  intro R _ _ _ hR D D' r W hpos hdet T hr
  let s := symUnitOf W hdet
  let i₀ : Fin r := ⟨0, hr⟩
  letI := T.mod s
  obtain ⟨hhom, h1, hmul, hadd⟩ := GlobalTheory.T.mumfordTensorData_matrixAction_ringHom_properties R D.toPre D'.toPre W T
  obtain ⟨hinc, hip, hpi, hcx⟩ := GlobalTheory.T.mumfordTensorData_factorInclusion_projection_props R D.toPre D'.toPre W T i₀
  obtain ⟨hxx, hxe, hinj, honto⟩ := GlobalTheory.T.mumfordTensorData_latticeFactor_props R D.toPre D'.toPre W T s i₀
  obtain ⟨w, hw, htau⟩ := GlobalTheory.T.mumfordTensorPairing_factorInclusion_periods R hR D D' W hdet hpos T i₀
  have hp : 0 < (s.1 : Matrix (Fin r) (Fin r) ℤ) i₀ i₀ := by
    have h := hpos.diag_pos (i := i₀)
    have h' : (0 : ℝ) < (((W + W.transpose) i₀ i₀ : ℤ) : ℝ) := h
    exact_mod_cast h'
  exact ⟨{
    O := TensO s
    mod := T.mod s
    o := { onB := { act := fun a => T.act (TensO.mat s a)
                    hom := fun a => hhom _
                    map_one := h1
                    map_mul := fun a b => hmul _ _
                    map_add := fun a b => hadd _ _
                    rosati := GlobalTheory.T.rosatiAdj_mumfordTensorPower_of_posDef R hR D D' W hdet hpos T }
           c_lin := GlobalTheory.T.tensor_action_compatible_with_degeneration R D.toPre D'.toPre W T s
           tau_bal := GlobalTheory.T.tensorDegData_periods_balanced_matrixAction R hR D D' W hdet hpos T }
    e := TensO.idem s i₀
    f := TensO.binv s
    inc := T.inc i₀
    pr := T.pr i₀
    xi := T.xi i₀
    xp := T.xp i₀
    w := w
    idem := TensO.idem_mul_idem s i₀
    inc_hom := hinc
    pr_hom := T.pr_hom i₀
    inc_pr := hip
    pr_inc := hpi
    xp_xi := hxx
    xi_xp := hxe
    c_xi := hcx
    inj := hinj
    onto := honto
    w_gen := hw
    tau := htau }, TensO.idem_binv_alg s i₀ hp⟩

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicFactorOfUnimodularTensorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_algebraic_factor_of_unimodular_tensor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, 1 ≤ r → (∃ F : Factor D.toPre D'.toPre, F.Alg) := by
  first | exact @GlobalTheory.Mum.Tens.nonempty_factor | exact GlobalTheory.Mum.Tens.nonempty_factor | (intros; apply GlobalTheory.Mum.Tens.nonempty_factor <;> assumption)
end
end
