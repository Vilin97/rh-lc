module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.NefEffectiveCones.EventuallyEvalNegOfCoeffNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleClassCechPicardClassIffAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntersectionEqLineBundleIntersectiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrHomEqAndIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqDim
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberMultilinearSymmStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionPullbackEqDegreeMulIntersection
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegOneLeftCompSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassBilinearStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordClassSymmetricPullbackQuadraticStatement
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.Basify
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyTopSelfIntersectionAmplePos

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AV.AmpleTopPos

theorem inter_comp_equiv {K : Type} [Field K] (A : AbVar K) {J J' : Type} [Fintype J] [Fintype J']
    (e : J' ≃ J) (c : J → Pic A.X.left) : inter A (c ∘ e) = inter A c := by
  unfold inter
  rw [GlobalTheory.multiDiff_comp_equiv]

theorem inter_top_pos : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left), IsAmpleCls c →
    ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → 0 < inter A (fun _ : J => c) := by
  intro K _ A c hc J _ hJ
  obtain ⟨L, hL, hr, rfl⟩ := hc
  have hA : IsAmpleLB L := (GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff K A L hL).1 ⟨L, hL, hr, rfl⟩
  have e : Fin A.dim ≃ J := (Fintype.equivFinOfCardEq hJ).symm
  have h1 : inter A (fun _ : J => cls L hL) = inter A (fun _ : Fin A.dim => cls L hL) :=
    (inter_comp_equiv A e (fun _ : J => cls L hL)).symm
  rw [h1, GlobalTheory.T.abelianVariety_intersection_eq_lineBundleIntersection K A (Fin A.dim) (fun _ => L) (fun _ => hL)]
  letI := A.algΓ
  obtain ⟨hI, -, -⟩ := GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace K A
  obtain ⟨hs, hp⟩ := GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K A
  have hp' : IsProjOver (strHom K (X := A.X.left)) := by rw [hs]; exact hp
  exact GlobalTheory.CompanionTheory.NefKleiman.interNum_top_pos_of_isAmpleLB K A.X.left hp' A.dim
    (GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K A) L hA

end GlobalTheory.AV.AmpleTopPos
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyTopSelfIntersectionAmplePosStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVariety_topSelfIntersection_ample_pos : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left), IsAmpleCls c → ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → 0 < inter A (fun _ : J => c) := by
  first | (exact @GlobalTheory.AV.AmpleTopPos.inter_top_pos) | (exact GlobalTheory.AV.AmpleTopPos.inter_top_pos) | (intros; apply GlobalTheory.AV.AmpleTopPos.inter_top_pos  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionPullbackEqDegreeMulIntersectionStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.intersection_pullback_eq_degree_mul_intersection : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left, inter A (fun j => CechPic.pull f.hom.left (c j)) = deg f * inter B c := by
  first | (exact @GlobalTheory.AV.AbVar.inter_pull_eq_deg_mul_inter) | (exact GlobalTheory.AV.AbVar.inter_pull_eq_deg_mul_inter) | (intros; apply GlobalTheory.AV.AbVar.inter_pull_eq_deg_mul_inter  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultilinearQuadraticIsHomogeneous

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem multilinear_quadratic_isHomogeneous : ∀ (P : Type) [AddCommGroup P] (g n : ℕ) (M : (Fin g → P) →ₘₗ[ℤ] ℤ) (a : Fin n → Fin n → P), ∃ F : MvPolynomial (Fin n) ℤ, F.IsHomogeneous (2 * g) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval m F = M (fun _ => ∑ i, ∑ j, (m i * m j) • a i j) := by
  intro P _ g n M a
  refine ⟨∑ r : Fin g → Fin n × Fin n, MvPolynomial.C (M (fun k => a (r k).1 (r k).2)) *
      ∏ k, (MvPolynomial.X (r k).1 * MvPolynomial.X (r k).2), ?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum
    intro r _
    have hX : ∀ k, (MvPolynomial.X (R := ℤ) (r k).1 * MvPolynomial.X (r k).2).IsHomogeneous 2 :=
      fun k => (MvPolynomial.isHomogeneous_X ℤ _).mul (MvPolynomial.isHomogeneous_X ℤ _)
    have h := (MvPolynomial.isHomogeneous_C (Fin n) (M fun k => a (r k).1 (r k).2)).mul
      (MvPolynomial.IsHomogeneous.prod Finset.univ _ (fun _ => 2) (fun k _ => hX k))
    convert h using 1
    simp [mul_comm]
  · intro m
    have hx : (fun _ : Fin g => ∑ i, ∑ j, (m i * m j) • a i j) =
        fun _ => ∑ p : Fin n × Fin n, (m p.1 * m p.2) • a p.1 p.2 := by
      funext _; exact (Fintype.sum_prod_type' (fun i j => (m i * m j) • a i j)).symm

    rw [hx, MultilinearMap.map_sum]

    simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]
    simp only [RingHom.id_apply]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPullbackSymmetricClassIntegralCombination

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.QuadSum

variable {K : Type} [Field K]

theorem hom_finset_sum {B A : AbVar K} {J : Type} (s : Finset J) (g : J → (B ⟶ A)) :
    Hom.hom (A := B) (B := A) (show B ⟶ A from ∑ i ∈ s, g i) = ∏ i ∈ s, (g i).hom := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, add_hom, ih]

theorem lam_symm {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) :
    AbVar.lam c x y = AbVar.lam c y x := by
  unfold AbVar.lam
  rw [mul_comm x y]
  abel

theorem lam_prod_right {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x : Y ⟶ A.X) {J : Type}
    (s : Finset J) (y : J → (Y ⟶ A.X)) :
    AbVar.lam c x (∏ j ∈ s, y j) = ∑ j ∈ s, AbVar.lam c x (y j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x 1 1 0).2.2.1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x (y a) _ 0).1, ih]

theorem lam_prod_left {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} {J : Type}
    (s : Finset J) (x : J → (Y ⟶ A.X)) (y : Y ⟶ A.X) :
    AbVar.lam c (∏ i ∈ s, x i) y = ∑ i ∈ s, AbVar.lam c (x i) y := by
  rw [lam_symm, lam_prod_right]
  exact Finset.sum_congr rfl (fun i _ => lam_symm c y (x i))

theorem lam_zpow_zpow {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) (m n : ℤ) :
    AbVar.lam c (x ^ m) (y ^ n) = (m * n) • AbVar.lam c x y := by
  rw [(GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y (x ^ m) y y n).2.2.2.2, (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x y y m).2.2.2.1, smul_smul,
    mul_comm n m]

end GlobalTheory.AV.QuadSum

theorem GlobalTheory.AV.QuadSum.pull_sum_smul : ∀ (K : Type) [Field K] (B A : AbVar K) (c : Pic A.X.left), CechPic.pull (Hom.hom (-(𝟙 A))).left c = c → ∀ (n : ℕ) (f : Fin n → (B ⟶ A)) (m : Fin n → ℤ), 2 • CechPic.pull (Hom.hom (A := B) (B := A) (show B ⟶ A from ∑ i, m i • f i)).left c = ∑ i, ∑ j, (m i * m j) • AbVar.lam c (f i).hom (f j).hom := by
  intro K _ B A c hc n f m
  rw [← (GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic K B A c hc (∑ i, m i • f i) 1).1, QuadSum.hom_finset_sum, QuadSum.lam_prod_left]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [QuadSum.lam_prod_right]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [zsmul_hom, zsmul_hom, QuadSum.lam_zpow_zpow]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPullbackSymmetricClassIntegralCombinationStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.two_smul_pullback_symmetric_class_integral_combination : ∀ (K : Type) [Field K] (B A : AbVar K) (c : Pic A.X.left), CechPic.pull (Hom.hom (-(𝟙 A))).left c = c → ∀ (n : ℕ) (f : Fin n → (B ⟶ A)) (m : Fin n → ℤ), 2 • CechPic.pull (Hom.hom (A := B) (B := A) (show B ⟶ A from ∑ i, m i • f i)).left c = ∑ i, ∑ j, (m i * m j) • AbVar.lam c (f i).hom (f j).hom := by
  first | (exact @GlobalTheory.AV.QuadSum.pull_sum_smul) | (exact GlobalTheory.AV.QuadSum.pull_sum_smul) | (intros; apply GlobalTheory.AV.QuadSum.pull_sum_smul  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDegreeIntegerCombinationIsHomogeneous

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AV.AbVar.multilinear_quadratic_isHomogeneous' (P : Type*) [AddCommGroup P] (g n : ℕ)
    (M : (Fin g → P) →ₘₗ[ℤ] ℤ) (a : Fin n → Fin n → P) :
    ∃ F : MvPolynomial (Fin n) ℤ, F.IsHomogeneous (2 * g) ∧
      ∀ m : Fin n → ℤ, MvPolynomial.eval m F = M (fun _ => ∑ i, ∑ j, (m i * m j) • a i j) := by
  let φ : (Fin n → Fin n → ℤ) →ₗ[ℤ] P :=
    { toFun := fun x => ∑ i, ∑ j, x i j • a i j
      map_add' := fun x y => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  let e : Fin n → Fin n → (Fin n → Fin n → ℤ) := fun i j => Pi.single i (Pi.single j 1)
  have he : ∀ i j, φ (e i j) = a i j := by
    intro i j
    simp only [φ, e, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
    simp
  obtain ⟨F, hF, hFe⟩ := GlobalTheory.multilinear_quadratic_isHomogeneous (Fin n → Fin n → ℤ) g n
    (M.compLinearMap (fun _ => φ)) e
  refine ⟨F, hF, fun m => ?_⟩
  rw [hFe m, MultilinearMap.compLinearMap_apply]
  congr 1
  simp only [map_sum, map_smul, he]

theorem GlobalTheory.AV.AbVar.deg_isHomogeneousPoly : ∀ (K : Type) [Field K] (A B : AbVar K), A.dim = B.dim → ∀ (n : ℕ) (f : Fin n → (A ⟶ B)), ∃ F : MvPolynomial (Fin n) ℚ, F.IsHomogeneous (2 * A.dim) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) F = (deg (∑ i, m i • f i) : ℚ) := by
  intro K _ A B hAB n f
  obtain ⟨c, hamp, hsym⟩ := GlobalTheory.AV.AbVar.exists_symm_ample K B
  obtain ⟨⟨M, hM⟩, -⟩ := GlobalTheory.T.intersection_number_multilinear_symm K A (Fin A.dim) (Fintype.card_fin _)
  set D : ℤ := inter B (fun _ : Fin A.dim => c) with hD
  have hDpos : 0 < D := GlobalTheory.T.abelianVariety_topSelfIntersection_ample_pos K B c hamp (Fin A.dim) (by rw [Fintype.card_fin, hAB])
  obtain ⟨F, hFh, hFe⟩ := GlobalTheory.AV.AbVar.multilinear_quadratic_isHomogeneous' (Pic A.X.left) A.dim n M
    (fun i j => AbVar.lam c (f i).hom (f j).hom)
  refine ⟨MvPolynomial.C ((1 : ℚ) / ((2 : ℚ) ^ A.dim * D)) * MvPolynomial.map (Int.castRingHom ℚ) F, ?_, ?_⟩
  · have := (MvPolynomial.isHomogeneous_C (Fin n) ((1 : ℚ) / ((2 : ℚ) ^ A.dim * D))).mul (hFh.map (Int.castRingHom ℚ))
    rwa [zero_add] at this
  · intro m
    have hq := GlobalTheory.T.two_smul_pullback_symmetric_class_integral_combination K A B c hsym n f m
    have hp := GlobalTheory.T.intersection_pullback_eq_degree_mul_intersection K A B (show A ⟶ B from ∑ i, m i • f i) hAB (Fin A.dim) (Fintype.card_fin _) (fun _ => c)
    have key : MvPolynomial.eval m F = 2 ^ A.dim * ((deg (show A ⟶ B from ∑ i, m i • f i) : ℤ) * D) := by
      rw [hFe m, ← hq, ← hp, ← hM]
      simpa only [RingHom.id_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, two_smul ℕ, two_smul ℤ] using
        M.map_smul_univ (fun _ => (2 : ℤ))
          (fun _ => CechPic.pull (Hom.hom (show A ⟶ B from ∑ i, m i • f i)).left c)
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_map]
    have e2 : MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (m i : ℚ)) F = ((MvPolynomial.eval m F : ℤ) : ℚ) := by
      rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, ← eq_intCast (Int.castRingHom ℚ), MvPolynomial.eval₂_comp_left]
      rfl
    rw [e2, key]
    have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    push_cast
    field_simp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDegreeIntegerCombinationIsHomogeneousStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.homDegree_integerCombination_isHomogeneous : ∀ (K : Type) [Field K] (A B : AbVar K), A.dim = B.dim → ∀ (n : ℕ) (f : Fin n → (A ⟶ B)), ∃ F : MvPolynomial (Fin n) ℚ, F.IsHomogeneous (2 * A.dim) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) F = (deg (∑ i, m i • f i) : ℚ) := by
  first | (exact @GlobalTheory.AV.AbVar.deg_isHomogeneousPoly) | (exact GlobalTheory.AV.AbVar.deg_isHomogeneousPoly) | (intros; apply GlobalTheory.AV.AbVar.deg_isHomogeneousPoly  <;> assumption)
end
end
