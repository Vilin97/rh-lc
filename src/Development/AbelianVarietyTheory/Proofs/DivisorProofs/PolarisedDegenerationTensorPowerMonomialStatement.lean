module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosSemidefOfIntForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefiningDegenerationDataTauCoordinateUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosSemidefOfIntFormStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.gram_posSemidef_of_symm_nonneg_int_bilinForm : ∀ {X : Type} [AddCommGroup X] {r : ℕ} (b : LinearMap.BilinForm ℤ X), (∀ y z, b y z = b z y) → (∀ y, 0 ≤ b y y) → ∀ v : Fin r → X, (Matrix.of fun i j => (b (v i) (v j) : ℝ)).PosSemidef := by
  first | exact @GlobalTheory.gram_posSemidef_of_int_form | exact GlobalTheory.gram_posSemidef_of_int_form | (intros; apply GlobalTheory.gram_posSemidef_of_int_form <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumHadamardPosDefPosSemidef

section

@[expose] public section

namespace GlobalTheory


open Matrix in
theorem sum_hadamard_posDef_posSemidef :
    ∀ {r : ℕ} (S G : Matrix (Fin r) (Fin r) ℝ), S.PosDef → G.PosSemidef →
      0 ≤ ∑ i, ∑ j, S i j * G i j ∧ (G ≠ 0 → 0 < ∑ i, ∑ j, S i j * G i j) := by
  intro r S G hS hG
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hG
  have key : ∑ i, ∑ j, S i j * (∑ k, vecMulVec (v k) (star (v k))) i j
      = ∑ k, star (v k) ⬝ᵥ (S *ᵥ v k) := by
    simp only [Matrix.sum_apply, Finset.sum_apply, vecMulVec_apply, Pi.star_apply, star_trivial, dotProduct,
      mulVec, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have term : ∀ k, 0 ≤ star (v k) ⬝ᵥ (S *ᵥ v k) := fun k =>
    hS.posSemidef.dotProduct_mulVec_nonneg _
  rw [key]
  refine ⟨Finset.sum_nonneg fun k _ => term k, fun hne => ?_⟩
  have : ∃ k, v k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    simp [h]
  obtain ⟨k, hk⟩ := this
  exact Finset.sum_pos' (fun k _ => term k) ⟨k, Finset.mem_univ _, hS.dotProduct_mulVec_pos hk⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumHadamardPosDefPosSemidefStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.sum_mul_nonneg_and_pos_of_posDef_of_posSemidef : ∀ {r : ℕ} (S G : Matrix (Fin r) (Fin r) ℝ), S.PosDef → G.PosSemidef → 0 ≤ ∑ i, ∑ j, S i j * G i j ∧ (G ≠ 0 → 0 < ∑ i, ∑ j, S i j * G i j) := by
  first | exact @GlobalTheory.sum_hadamard_posDef_posSemidef | exact GlobalTheory.sum_hadamard_posDef_posSemidef | (intros; apply GlobalTheory.sum_hadamard_posDef_posSemidef <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationPsiCoordEqUnitMulProd

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.TensPsiCoord

open GlobalTheory.PsiTauCoordRel GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), IsTens Q D' W pr xe → ∀ (y : D'.X) (k : Fin r → Fin r → (FractionRing R)ˣ), (∀ i j, Q.TauCoord (xe y i) (xe y j) (k i j)) → ∀ x : (FractionRing R)ˣ, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord D' y x → ∃ u : Rˣ, x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * ∏ i, ∏ j, k i j ^ W i j := by
  intro R _ _ _ Q D' r W pr xe hT y k hk x hx
  obtain ⟨-, -, -, w, -, hpsi⟩ := hT
  haveI : IsProper D'.P.A.hom := D'.P.isAb.proper
  haveI : IsProper Q.B.hom := Q.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J', hJ', hc'⟩ := GlobalTheory.PeriodBalance.exists_good_integral ξ D'.P.isLB D'.P.A.hom
  obtain ⟨J, hJ, hc⟩ := GlobalTheory.PeriodBalance.exists_good_integral ξ Q.M.isLB Q.B.hom
  have E := hpsi y ξ J J' hJ hJ'

  obtain ⟨j, h, hj, rfl⟩ := hx
  obtain ⟨u₁, g₁⟩ := val_psi_chart D' ξ hJ' hc' y j hj (h trivial)
  have eP := gm_genVal ξ (D'.psi y) j h

  obtain ⟨u₂, e₂⟩ : ∃ u : Rˣ, (gm (D'.xK y) ξ _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y)))).val =
      GlobalTheory.PeriodBalance.cst ξ u := by
    refine GlobalTheory.PeriodBalance.unit_gm' ξ (D'.c y).left _ (And.intro (Set.mem_iInter.2 fun I => ?_) ?_) _
    · obtain ⟨q, hq⟩ : ∃ q : D'.P.A ⟶ Q.B, tensφ pr I = q.left := by
        obtain ⟨⟨a, b⟩, c⟩ := I
        fin_cases c <;> exact ⟨_, rfl⟩
      have := hc ((D'.c y).left ≫ tensφ pr I) (by
        rw [hq, Category.assoc, Over.w q, Over.w]; rfl)
      rw [← Category.assoc] at this
      exact this
    · exact hc' _ (Over.w _)

  have hv : ∀ i j, ∃ v : Rˣ, val (Q.tau (xe y i) (xe y j)) (𝟙 _) ξ J =
      GlobalTheory.TauShift.kK ξ (k i j) * GlobalTheory.TauShift.cK ξ v := by
    intro i j
    obtain ⟨u, -, hu⟩ := hk i j
    obtain ⟨v, hv⟩ : ∃ v : Rˣ, val u (jK R ≫ 𝟙 _) ξ J = Units.map (GlobalTheory.PeriodBalance.cst ξ).toMonoidHom v := by
      refine val_int ξ hc u (𝟙 _) fun l => ?_
      obtain ⟨q, hq⟩ : ∃ q : 𝟙_ (Over (Sp R)) ⟶ Q.B,
          GlobalTheory.PolDeg.lamPts (Q.c (xe y i)) (Q.c (xe y j)) l = q.left := by
        fin_cases l <;> exact ⟨_, rfl⟩
      rw [Category.id_comp, hq, Over.w q]; rfl
    refine ⟨v, (hu ξ J hJ).trans (congrArg₂ (· * ·) ?_ ?_)⟩
    · have := GlobalTheory.RefTauCoord.gm_unitOn (RingHom.id (FractionRing R)) ξ (k i j)
      rw [show spMap (RingHom.id (FractionRing R)) = 𝟙 _ by simp] at this
      exact Units.ext this
    · rw [toUnit_left, ← Category.comp_id (jK R)]; exact hv
  choose v hv using hv
  have hc2 : ∀ z : Rˣ, GlobalTheory.TauShift.kK ξ (Units.map (algebraMap R (FractionRing R)).toMonoidHom z) =
      GlobalTheory.TauShift.cK ξ z := fun z => Units.ext rfl
  refine ⟨u₁⁻¹ * u₂ * ∏ i, ∏ j, v i j ^ W i j, Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ) ?_⟩
  change GlobalTheory.TauShift.kK ξ _ = GlobalTheory.TauShift.kK ξ _
  have eP' : gm (𝟙 _) ξ (LB.wchart D'.P.L (fun _ : PUnit => D'.xK y) j) ((D'.psi y).s j) =
      GlobalTheory.TauShift.kK ξ (genVal (D'.psi y) j h) := Units.ext eP
  have e₂' : gm (D'.xK y) ξ _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) = GlobalTheory.TauShift.cK ξ u₂ :=
    Units.ext e₂
  have G := g₁.symm.trans (E.trans (by rw [e₂']))
  rw [eP'] at G
  simp only [hv] at G
  simp only [map_mul, map_inv, map_prod, map_zpow, mul_zpow, Finset.prod_mul_distrib, hc2] at G ⊢
  have G' := congrArg ((GlobalTheory.TauShift.cK ξ u₁)⁻¹ * ·) G
  simp only [inv_mul_cancel_left] at G'
  rw [G']
  ac_rfl

end GlobalTheory.TensPsiCoord
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationPsiCoordEqUnitMulProdStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam


theorem _root_.GlobalTheory.T.tensorDegeneration_psiCoord_eq_unit_mul_prod : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), IsTens Q D' W pr xe → ∀ (y : D'.X) (k : Fin r → Fin r → (FractionRing R)ˣ), (∀ i j, Q.TauCoord (xe y i) (xe y j) (k i j)) → ∀ x : (FractionRing R)ˣ, GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord D' y x → ∃ u : Rˣ, x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * ∏ i, ∏ j, k i j ^ W i j := by
  first | exact @GlobalTheory.TensPsiCoord.main | exact GlobalTheory.TensPsiCoord.main | (intros; apply GlobalTheory.TensPsiCoord.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedDegenerationTensorPowerMonomial

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.TensMono

def tensForm {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {r : ℕ} (S : Matrix (Fin r) (Fin r) ℤ) (xe : Y ≃+ (Fin r → X))
    (b : LinearMap.BilinForm ℤ X) : LinearMap.BilinForm ℤ Y :=
  ∑ i, ∑ j, S i j • b.compl₁₂ ((LinearMap.proj i).comp xe.toIntLinearEquiv.toLinearMap)
    ((LinearMap.proj j).comp xe.toIntLinearEquiv.toLinearMap)

theorem tensForm_apply {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {r : ℕ} (S : Matrix (Fin r) (Fin r) ℤ)
    (xe : Y ≃+ (Fin r → X)) (b : LinearMap.BilinForm ℤ X) (y z : Y) :
    tensForm S xe b y z = ∑ i, ∑ j, S i j * b (xe y i) (xe z j) := by
  simp [tensForm, LinearMap.sum_apply]

theorem zpow_sum_local {G κ : Type} [CommGroup G] (a : G) (s : Finset κ) (f : κ → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem tensForm_self {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (xe : Y ≃+ (Fin r → X)) (b : LinearMap.BilinForm ℤ X) (hb : ∀ y z, b y z = b z y) (y : Y) :
    tensForm (W + W.transpose) xe b y y = 2 * ∑ i, ∑ j, W i j * b (xe y i) (xe y j) := by
  rw [tensForm_apply]
  simp only [Matrix.add_apply, Matrix.transpose_apply, add_mul, Finset.sum_add_distrib]
  rw [two_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hb]

theorem tensForm_symm {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (xe : Y ≃+ (Fin r → X)) (b : LinearMap.BilinForm ℤ X) (hb : ∀ y z, b y z = b z y) (y z : Y) :
    tensForm (W + W.transpose) xe b y z = tensForm (W + W.transpose) xe b z y := by
  rw [tensForm_apply, tensForm_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hb]; simp only [Matrix.add_apply, Matrix.transpose_apply]; ring

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsTens Q D' W pr xe → ∀ (m : ℕ) (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ Q.X), Q.IsMonomialTau t β → (∀ i, t i ≠ 0) → (∀ i y z, β i y z = β i z y) → (∀ i y, 0 ≤ β i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ β' : Fin m → LinearMap.BilinForm ℤ D'.X, IsMonomial D' t β' ∧ (∀ i y z, β' i y z = β' i z y) ∧ ∀ y, y ≠ 0 → ∃ i, 0 < β' i y y := by
  intro R _ _ _ Q D' r W pr xe hW hT m t β hmono ht hsym hnn hdef
  have hreal : ∀ l y, ((tensForm (W + W.transpose) xe (β l) y y : ℤ) : ℝ) =
      ∑ i, ∑ j, ((W + W.transpose).map (Int.cast : ℤ → ℝ)) i j *
        (Matrix.of fun i j => (β l (xe y i) (xe y j) : ℝ)) i j := by
    intro l y; rw [tensForm_apply]; push_cast; simp [Matrix.map_apply]
  have hpos : ∀ l y, 0 ≤ tensForm (W + W.transpose) xe (β l) y y := fun l y => by
    have := (GlobalTheory.T.sum_mul_nonneg_and_pos_of_posDef_of_posSemidef _ _ hW (GlobalTheory.T.gram_posSemidef_of_symm_nonneg_int_bilinForm (β l) (hsym l) (hnn l) (fun i => xe y i))).1
    rw [← hreal] at this; exact_mod_cast this
  refine ⟨fun l => tensForm (W + W.transpose) xe (β l), ?_, fun l y z => tensForm_symm W xe (β l) (hsym l) y z, ?_⟩
  · intro y
    have hn : ∀ l, (∑ i, ∑ j, W i j * β l (xe y i) (xe y j)) = ((∑ i, ∑ j, W i j * β l (xe y i) (xe y j)).toNat : ℤ) :=
      fun l => (Int.toNat_of_nonneg (by have := hpos l y; rw [tensForm_self W xe (β l) (hsym l)] at this; omega)).symm
    choose k hk hkc using fun i j => hmono (xe y i) (xe y j)
    obtain ⟨x, hx⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord D' y
    obtain ⟨u, hu⟩ := GlobalTheory.T.tensorDegeneration_psiCoord_eq_unit_mul_prod R Q D' W pr xe hT y k hkc x hx
    have ht' : ∀ l, algebraMap R (FractionRing R) (t l) ≠ 0 := fun l =>
      (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (ht l)
    let a : Fin m → (FractionRing R)ˣ := fun l => Units.mk0 _ (ht' l)
    have hk' : ∀ i j, k i j = ∏ l, a l ^ β l (xe y i) (xe y j) := fun i j => Units.ext (by
      rw [hk, Units.coe_prod]
      exact Finset.prod_congr rfl fun l _ => by rw [Units.val_zpow_eq_zpow_val]; rfl)
    have hprod : ∏ i, ∏ j, k i j ^ W i j = ∏ l, a l ^ (∑ i, ∑ j, W i j * β l (xe y i) (xe y j)) := by
      calc ∏ i, ∏ j, k i j ^ W i j = ∏ i, ∏ j, ∏ l, a l ^ (β l (xe y i) (xe y j) * W i j) := by
            refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
            rw [hk', ← Finset.prod_zpow]
            exact Finset.prod_congr rfl fun l _ => (zpow_mul _ _ _).symm
        _ = ∏ i, ∏ l, ∏ j, a l ^ (β l (xe y i) (xe y j) * W i j) :=
            Finset.prod_congr rfl fun i _ => Finset.prod_comm
        _ = ∏ l, ∏ i, ∏ j, a l ^ (β l (xe y i) (xe y j) * W i j) := Finset.prod_comm
        _ = _ := Finset.prod_congr rfl fun l _ => by
            rw [zpow_sum_local]
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [zpow_sum_local]
            exact Finset.prod_congr rfl fun j _ => by rw [mul_comm]
    refine ⟨u, fun l => (∑ i, ∑ j, W i j * β l (xe y i) (xe y j)).toNat, fun l => by
      rw [tensForm_self W xe (β l) (hsym l), hn l], (GlobalTheory.PeriodFormCompare.psiCoord_iff D' y _).2 ⟨x, hx, ?_⟩⟩
    rw [hu, hprod]
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Units.coe_prod, map_mul, map_prod, map_pow]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [hn l, zpow_natCast, Units.val_pow_eq_pow_val]; rfl
  · intro y hy
    obtain ⟨j, hj⟩ : ∃ j, xe y j ≠ 0 := by
      by_contra h; push_neg at h
      exact hy (xe.injective (by rw [map_zero]; exact funext h))
    obtain ⟨l, hl⟩ := hdef _ hj
    refine ⟨l, ?_⟩
    have hG : (Matrix.of fun i j => (β l (xe y i) (xe y j) : ℝ)) ≠ 0 := fun h => by
      have := congrFun (congrFun h j) j
      simp at this; omega
    have := (GlobalTheory.T.sum_mul_nonneg_and_pos_of_posDef_of_posSemidef _ _ hW (GlobalTheory.T.gram_posSemidef_of_symm_nonneg_int_bilinForm (β l) (hsym l) (hnn l) (fun i => xe y i))).2 hG
    rw [← hreal] at this; exact_mod_cast this

end GlobalTheory.TensMono
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedDegenerationTensorPowerMonomialStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

theorem _root_.GlobalTheory.T.polarisedDegeneration_tensorPower_monomial : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsTens Q D' W pr xe → ∀ (m : ℕ) (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ Q.X), Q.IsMonomialTau t β → (∀ i, t i ≠ 0) → (∀ i y z, β i y z = β i z y) → (∀ i y, 0 ≤ β i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ β' : Fin m → LinearMap.BilinForm ℤ D'.X, IsMonomial D' t β' ∧ (∀ i y z, β' i y z = β' i z y) ∧ ∀ y, y ≠ 0 → ∃ i, 0 < β' i y y := by
  first | exact @GlobalTheory.TensMono.main | exact GlobalTheory.TensMono.main | (intros; apply GlobalTheory.TensMono.main <;> assumption)
end
end
