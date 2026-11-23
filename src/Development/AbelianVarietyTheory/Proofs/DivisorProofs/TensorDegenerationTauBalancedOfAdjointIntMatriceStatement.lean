module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfMulComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialCubicalThetaFinsuppTensor
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiBalanceFormalSumMemSpanCubicalThetaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiBalanceFormalSumPsiValuesEqTauProductStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorTensorPowerCorrespondsFormalSumStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialCubicalThetaFinsuppTensorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isStronglyTrivial_cubicalThetaFinsupp_tensor : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W), D.TauBimult → ∀ a b c : GlobalTheory.TensBal.Vec r, GlobalTheory.TensBal.Triv T (GlobalTheory.TensBal.theta a b c) := by
  first | exact @GlobalTheory.TensBal.triv_theta | exact GlobalTheory.TensBal.triv_theta | (intros; apply GlobalTheory.TensBal.triv_theta <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialFormalSumTensorAdd

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBal

theorem prod_support_eq {U : Type} [CommGroup U] {r : ℕ} (g : Vec r → ℤ → U) (d : Vec r →₀ ℤ) :
    ∏ v : d.support, g v.1 (d v.1) = d.prod g :=
  Finset.prod_coe_sort d.support (fun v => g v (d v))

theorem triv_add : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W) (c c' : GlobalTheory.TensBal.Vec r →₀ ℤ), GlobalTheory.TensBal.Triv T c → GlobalTheory.TensBal.Triv T c' →
    GlobalTheory.TensBal.Triv T (c + c') := by
  intro R _ _ D D' r W T c c' ⟨Ξ, hΞ, h1, h2⟩ ⟨Ξ', hΞ', h1', h2'⟩
  have hform : FormEq (Sum.elim (fun v : c.support => (vecHom T v.1).left) (fun v : c'.support => (vecHom T v.1).left))
      (Sum.elim (fun v : c.support => c v.1) (fun v : c'.support => c' v.1))
      (fun v : (c + c').support => (vecHom T v.1).left) (fun v => (c + c') v.1) := by
    intro U _ h
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [prod_support_eq (fun v n => h (vecHom T v).left ^ n) c,
      prod_support_eq (fun v n => h (vecHom T v).left ^ n) c',
      prod_support_eq (fun v n => h (vecHom T v).left ^ n) (c + c'),
      Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)]
  obtain ⟨Ξ'', hΞ'', hv⟩ := exists_gen D.P.isLB hform _
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ hΞ hΞ')
  refine ⟨Ξ'', hΞ'', fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · rw [hv _ _ z J hJ, val_mul hJ, h1 z J hJ, h1' z J hJ, _root_.mul_one]
  · rw [hv _ _ z J hJ, val_mul hJ, h2 z J hJ y y', h2' z J hJ y y']
    exact (Finsupp.prod_add_index' (f := c) (g := c')
      (h := fun v n => val (D.psi (vecLat T v y y')) (𝟙 _) z J ^ (-n))
      (fun _ => by simp only [neg_zero, zpow_zero]) (fun _ _ _ => by simp only [neg_add, zpow_add])).symm

end GlobalTheory.TensBal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialFormalSumTensorAddStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isStronglyTrivialFormalSumTensor_add : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (c c' : GlobalTheory.TensBal.Vec r →₀ ℤ), GlobalTheory.TensBal.Triv T c → GlobalTheory.TensBal.Triv T c' → GlobalTheory.TensBal.Triv T (c + c') := by
  first | exact @GlobalTheory.TensBal.triv_add | exact GlobalTheory.TensBal.triv_add | (intros; apply GlobalTheory.TensBal.triv_add <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialFormalSumTensorNeg

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBalNeg

theorem triv_neg : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W) (c : GlobalTheory.TensBal.Vec r →₀ ℤ), GlobalTheory.TensBal.Triv T c → GlobalTheory.TensBal.Triv T (-c) := by
  intro R _ _ D D' r W T c ⟨Ξ, hΞ, h1, h2⟩
  have hF : FormEq (fun v : c.support => (GlobalTheory.TensBal.vecHom T v.1).left) (fun v => -(c v.1))
      (fun v : (-c).support => (GlobalTheory.TensBal.vecHom T v.1).left) (fun v => (-c) v.1) := by
    intro U _ h
    rw [Finset.prod_coe_sort c.support (fun v => h (GlobalTheory.TensBal.vecHom T v).left ^ (-(c v))),
      Finset.prod_coe_sort (-c).support (fun v => h (GlobalTheory.TensBal.vecHom T v).left ^ ((-c) v)),
      Finsupp.support_neg]
    simp only [Finsupp.neg_apply]
  obtain ⟨Ξ', hΞ', hv⟩ := exists_gen D.P.isLB hF (LB.invGen D.P.L _ _ Ξ) (LB.isGen_invGen D.P.L _ _ Ξ hΞ)
  refine ⟨Ξ', hΞ', fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · rw [hv _ _ z J hJ, val_inv, h1 z J hJ, inv_one]
  · rw [hv _ _ z J hJ, val_inv, h2 z J hJ y y', Finsupp.support_neg, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Finsupp.neg_apply, neg_neg, zpow_neg, inv_inv]

end GlobalTheory.TensBalNeg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialFormalSumTensorNegStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isStronglyTrivialFormalSumTensor_neg : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (c : GlobalTheory.TensBal.Vec r →₀ ℤ), GlobalTheory.TensBal.Triv T c → GlobalTheory.TensBal.Triv T (-c) := by
  first | exact @GlobalTheory.TensBalNeg.triv_neg | exact GlobalTheory.TensBalNeg.triv_neg | (intros; apply GlobalTheory.TensBalNeg.triv_neg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialFormalSumTensorZero

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBal

theorem triv_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W), GlobalTheory.TensBal.Triv T 0 := by
  intro R _ _ D D' r W T
  obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB
    (φ' := fun v : (0 : Vec r →₀ ℤ).support => (vecHom T v.1).left) (ε' := fun v => (0 : Vec r →₀ ℤ) v.1)
    (fun U _ h => by simp) (LB.oneGen D.P.L (Y := (D'.P.A ⊗ D'.P.A).left)) (LB.isGen_oneGen _)
  refine ⟨t, ht, fun z J hJ => (hv _ _ z J hJ).trans (val_one _), fun z J hJ y y' => ?_⟩
  rw [hv _ _ z J hJ, val_one]
  simp

end GlobalTheory.TensBal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialFormalSumTensorZeroStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isStronglyTrivialFormalSumTensor_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W), GlobalTheory.TensBal.Triv T 0 := by
  first | exact @GlobalTheory.TensBal.triv_zero | exact GlobalTheory.TensBal.triv_zero | (intros; apply GlobalTheory.TensBal.triv_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationTauBalancedOfAdjointIntMatrice

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBal
open GlobalTheory.TensAct
open ReciprocityTheory.ChartRestriction.G.DVR (cP cPoint_add)

theorem triv_span {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (hB : D.TauBimult) {c : Vec r →₀ ℤ}
    (hc : c ∈ Submodule.span ℤ (Set.range fun p : Vec r × Vec r × Vec r => theta p.1 p.2.1 p.2.2)) : Triv T c := by
  induction hc using Submodule.span_induction with
  | mem x hx => obtain ⟨p, rfl⟩ := hx; exact GlobalTheory.T.isStronglyTrivial_cubicalThetaFinsupp_tensor R D D' W T hB _ _ _
  | zero => exact GlobalTheory.T.isStronglyTrivialFormalSumTensor_zero R D D' W T
  | add x y _ _ hx hy => exact GlobalTheory.T.isStronglyTrivialFormalSumTensor_add R D D' W T _ _ hx hy
  | smul n x _ hx =>
    induction n using Int.induction_on with
    | zero => rw [zero_smul]; exact GlobalTheory.T.isStronglyTrivialFormalSumTensor_zero R D D' W T
    | succ k ih => rw [add_smul, one_smul]; exact GlobalTheory.T.isStronglyTrivialFormalSumTensor_add R D D' W T _ _ ih hx
    | pred k ih =>
      rw [sub_smul, one_smul, sub_eq_add_neg]
      exact GlobalTheory.T.isStronglyTrivialFormalSumTensor_add R D D' W T _ _ ih (GlobalTheory.T.isStronglyTrivialFormalSumTensor_neg R D D' W T _ hx)

theorem tau_tens {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) {z : (TK R).left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (p q : D'.X) :
    val (D'.tau p q) (𝟙 _) z J' = isoV T.w z J J' (cP D' (TK R) (p + q)).left * qv T z J (p + q) *
      (isoV T.w z J J' (cP D' (TK R) p).left * qv T z J p)⁻¹ *
      (isoV T.w z J J' (cP D' (TK R) q).left * qv T z J q)⁻¹ * (val D'.rigK (𝟙 _) z J')⁻¹ := by
  rw [GlobalTheory.TauBalBox.tau_val D' hJ', T.psi _ z J J' hJ hJ', T.psi _ z J J' hJ hJ', T.psi _ z J J' hJ hJ']
  rfl

theorem tauBal_tens : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (A A' : Matrix (Fin r) (Fin r) ℤ), A.transpose * (W + W.transpose) = (W + W.transpose) * A' → D'.toPre.TauBal (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A') (GlobalTheory.TensAct.latAct T A) (GlobalTheory.TensAct.latAct T A') := by
  intro R _ _ I D D' r W T A A' hA u' hu' hn' y y'
  obtain ⟨Ξ, hΞ, hΞ0, hΞv⟩ := triv_span T D.tau_bimult (GlobalTheory.T.rosatiBalanceFormalSum_mem_span_cubicalTheta W A A' hA)
  refine corr_of_val D'.toPre.P.isLB fun z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := GlobalTheory.BoxFamily.exists_good_at D.toPre.P.isLB z
  have key := GlobalTheory.T.rosatiGenerator_tensorPower_corresponds_formalSum R D.toPre D'.toPre W T A A' u' hu' hn' Ξ hΞ hΞ0 z J J' hJ hJ' y y'
  rw [hΞv z J hJ y y', GlobalTheory.T.rosatiBalanceFormalSum_psiValues_eq_tauProduct R D.toPre D'.toPre W T D.tau_bimult A A' z J hJ y y'] at key
  have pr := prod_ros (matAct T A) (matAct T A') (cP D'.toPre (TK R) y) (cP D'.toPre (TK R) y')
    (isoV T.w z J J')
  have l₁ : cP D'.toPre (TK R) y ≫ matAct T A = cP D'.toPre (TK R) (latAct T A y) := by
    rw [cP, cP, c_lin, Category.assoc]
  have l₂ : cP D'.toPre (TK R) y' ≫ matAct T A' = cP D'.toPre (TK R) (latAct T A' y') := by
    rw [cP, cP, c_lin, Category.assoc]
  rw [l₁, l₂, ← cPoint_add, ← cPoint_add] at pr
  change ∏ a, isoV T.w z J J' (D'.toPre.pt2 y y' ≫ rosatiφ D'.toPre.P.A (matAct T A) (matAct T A') a) ^ rosatiε a = _ at pr
  rw [pr] at key
  rw [val_mul hJ', val_pull hJ', Category.id_comp, tau_tens T hJ hJ', tau_tens T hJ hJ']
  have e0 : rosatiε 0 = 1 := rfl
  have e1 : rosatiε 1 = -1 := rfl
  have e2 : rosatiε 2 = -1 := rfl
  have e3 : rosatiε 3 = -1 := rfl
  have e4 : rosatiε 4 = 1 := rfl
  have e5 : rosatiε 5 = 1 := rfl
  have r0 : rosLat T A A' y y' 0 = latAct T A y + y' := rfl
  have r1 : rosLat T A A' y y' 1 = latAct T A y := rfl
  have r2 : rosLat T A A' y y' 2 = y' := rfl
  have r3 : rosLat T A A' y y' 3 = y + latAct T A' y' := rfl
  have r4 : rosLat T A A' y y' 4 = y := rfl
  have r5 : rosLat T A A' y y' 5 = latAct T A' y' := rfl
  simp only [Fin.prod_univ_six, e0, e1, e2, e3, e4, e5, r0, r1, r2, r3, r4, r5] at key
  apply Additive.ofMul.injective
  have k' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at k' ⊢
  linear_combination (norm := abel) k'

end GlobalTheory.TensBal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationTauBalancedOfAdjointIntMatriceStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.tensorDegeneration_tauBalanced_of_adjointIntMatrices : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (A A' : Matrix (Fin r) (Fin r) ℤ), A.transpose * (W + W.transpose) = (W + W.transpose) * A' → D'.toPre.TauBal (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A') (GlobalTheory.TensAct.latAct T A) (GlobalTheory.TensAct.latAct T A') := by
  first | exact @GlobalTheory.TensBal.tauBal_tens | exact GlobalTheory.TensBal.tauBal_tens | (intros; apply GlobalTheory.TensBal.tauBal_tens <;> assumption)
end
end
