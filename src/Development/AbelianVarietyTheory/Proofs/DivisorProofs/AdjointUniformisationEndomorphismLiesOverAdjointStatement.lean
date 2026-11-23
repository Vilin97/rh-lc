module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.LinEndOfOLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndDataSymmAndOfOAct
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformizationEndomorphismOfLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceThickening
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismActionUniformizationData
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctorialOfUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfIsClosedImmersionOfThickeningsOfIsProper
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemOfNonempty
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointUniqueDegenerationData

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Mum.RosUniq
open GlobalTheory.CechPic GlobalTheory.EndRosati

theorem pt_eq_of_cls {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (hK : KTriv A L) {R' : Type} [CommRing R'] {t : Spec (CommRingCat.of R') ⟶ S} (a b : Over.mk t ⟶ A)
    (H : pull (snd (Over.mk t) A * (fst (Over.mk t) A ≫ a)⁻¹ * (fst (Over.mk t) A ≫ b)).left (cls L hL) -
        pull (fst (Over.mk t) A ≫ b).left (cls L hL) =
      pull (snd (Over.mk t) A * (fst (Over.mk t) A ≫ a)⁻¹ * (fst (Over.mk t) A ≫ a)).left (cls L hL) -
        pull (fst (Over.mk t) A ≫ a).left (cls L hL)) : b = a := by
  let T : Over S := Over.mk t
  let x : T ⟶ A := b * a⁻¹
  have hx : lift (fst T A ≫ x) (snd T A) ≫ μ[A] = snd T A * (fst T A ≫ a)⁻¹ * (fst T A ≫ b) := by
    rw [← Hom.mul_def]
    simp only [x, MonObj.comp_mul, GrpObj.comp_inv]
    ac_rfl
  have hy : snd T A * (fst T A ≫ a)⁻¹ * (fst T A ≫ a) = snd T A := inv_mul_cancel_right _ _
  rw [hy, ← hx] at H
  have h1 : x = 1 := hK R' t x fun s => by
    obtain ⟨i, hi⟩ := exists_chart hL (a.left s)
    obtain ⟨i', hi'⟩ := exists_chart hL (b.left s)
    let V : (Spec (CommRingCat.of R')).Opens := a.left ⁻¹ᵁ L.U i ⊓ b.left ⁻¹ᵁ L.U i'
    refine ⟨V, ⟨hi, hi'⟩, ?_⟩
    have z : ∀ (c : T ⟶ A) (l : L.ι), V ≤ c.left ⁻¹ᵁ L.U l →
        pull ((fst T A).left ⁻¹ᵁ V).ι (pull (fst T A ≫ c).left (cls L hL)) = 0 := fun c l hl => by
      rw [← pull_comp]
      exact (cls_eq_zero_iff (LB.isLB_pull hL _)).2 (BoxKernel.gen_of_chart (LB.isLB_pull hL _) (fun _ => l)
        fun y => mem_pull.2 (hl y.2))
    have hT : (translDiff A L x).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_zero_iff (LB.isLB_pull hT _)).1 ?_
    refine (cls_pull hT _ _).trans ((congrArg _ (cls_linComb hL _ _ hT)).trans ?_)
    have e : ∑ k : Fin 2, (![1, -1] : Fin 2 → ℤ) k • pull ((![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left,
        (snd T A).left] : Fin 2 → _) k) (cls L hL) =
        pull (fst T A ≫ b).left (cls L hL) - pull (fst T A ≫ a).left (cls L hL) := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
      linear_combination (norm := abel) H
    refine (congrArg _ e).trans ?_
    exact (map_sub _ _ _).trans ((congrArg₂ (· - ·) (z b i' inf_le_right) (z a i inf_le_left)).trans (sub_zero _))
  exact mul_inv_eq_one.1 h1

end GlobalTheory.Mum.RosUniq


open GlobalTheory.CechPic GlobalTheory.EndRosati GlobalTheory.Mum.RosUniq in
theorem GlobalTheory.Mum.rosatiAdj_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (f g g' : D.toPre.P.A ⟶ D.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom g' → RosatiAdj D.toPre.P.A D.toPre.P.L f g → RosatiAdj D.toPre.P.A D.toPre.P.L f g' → g = g' := by
  intro R _ _ _ _ D f g g' hf hg hg' Hg Hg'
  have hGF := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨r, hr, -⟩ := exists_ros hGF D.toPre.P.isAb D.toPre.P.isLB f g Hg
  obtain ⟨r', hr', -⟩ := exists_ros hGF D.toPre.P.isAb D.toPre.P.isLB f g' Hg'
  have key : ∀ {T : Over (Spec (CommRingCat.of R))} (x y : T ⟶ D.toPre.P.A),
      pull (x * (y ≫ g)).left (cls _ D.toPre.P.isLB) - pull (y ≫ g).left (cls _ D.toPre.P.isLB) =
      pull (x * (y ≫ g')).left (cls _ D.toPre.P.isLB) - pull (y ≫ g').left (cls _ D.toPre.P.isLB) :=
    fun x y => by
      have h₁ := cls_of_rosati D.toPre.P.isLB r hr x y
      have h₂ := cls_of_rosati D.toPre.P.isLB r' hr' x y
      linear_combination (norm := abel) h₂ - h₁
  let cv := D.toPre.P.A.left.affineOpenCover
  refine Over.OverMorphism.ext (Scheme.Cover.hom_ext cv.openCover _ _ fun j => ?_)
  let t : Spec (CommRingCat.of (cv.X j)) ⟶ Spec (CommRingCat.of R) := cv.f j ≫ D.toPre.P.A.hom
  let y : Over.mk t ⟶ D.toPre.P.A := Over.homMk (cv.f j) rfl
  have k := key (snd (Over.mk t) D.toPre.P.A * (fst _ _ ≫ y ≫ g')⁻¹) (fst (Over.mk t) D.toPre.P.A ≫ y)
  simp only [Category.assoc] at k
  have e := pt_eq_of_cls D.toPre.P.isLB D.toPre.P.ktriv (y ≫ g') (y ≫ g) k
  exact congrArg (·.left) e
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointUniqueDegenerationDataStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.rosatiAdjoint_unique_degenerationData : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (f g g' : D.toPre.P.A ⟶ D.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom g' → RosatiAdj D.toPre.P.A D.toPre.P.L f g → RosatiAdj D.toPre.P.A D.toPre.P.L f g' → g = g' := by
  first | exact @GlobalTheory.Mum.rosatiAdj_unique | exact GlobalTheory.Mum.rosatiAdj_unique | (intros; apply GlobalTheory.Mum.rosatiAdj_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismCarriesPeriodPointBala

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.Mum.KeepsIota

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_v (hG : GlobalFnsSt) (D : DegPre R) (f g : D.P.A ⟶ D.P.A) [IsMonHom f] [IsMonHom g]
    (k : D.X → D.X) (hk : ∀ χ, D.c (k χ) = D.c χ ≫ f)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) (χ : D.X) :
    ∃ v : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) (k χ)) (D.Oφ g χ)) (Sum.elim Oε Oinvε)),
      Normd v ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
        Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := by
  have cf : ∀ T, cP D T (k χ) = cP D T χ ≫ f := fun T => by
    rw [cP, hk, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) (k χ)) (D.Oφ g χ)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (prod_ros _ _ (cP D _ χ) (𝟙 D.P.A) h).trans (Eq.symm ?_)
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (GlobalTheory.UT.OLinEnd.prod_Oφ D (𝟙 _) (k χ) h)
        (GlobalTheory.UT.OLinEnd.prod_Oφ_inv D g χ h)).trans ?_
      rw [cf, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.pullGen D.P.L _ _ u (lift (cP D D.P.A χ) (𝟙 D.P.A)).left) (pullGen_isGen _ _ _ _ hu _)
  have key : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
      Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := fun T x Z r z J hJ => by
    rw [vv Z _ z J hJ, val_pull hJ, Category.assoc, ← Over.comp_left, comp_lift, comp_cP, Category.comp_id]
  refine ⟨v, ⟨hv, corr_of_val D.P.isLB fun y J hJ => ?_⟩, key⟩
  have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) hJ 1 1 (cP D _ χ)).2
  rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J (cP D _ χ) 1 = 1 := mul_eq_left.1 e.symm
  have k' := key (𝟙_ (Over (Spec (CommRingCat.of R)))) 1 _ (𝟙 _) y J hJ
  have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  rw [o] at k'
  refine (val_pull hJ _ _ _).trans (k'.trans (Eq.trans ?_ (val_one _).symm))
  rw [Category.id_comp]
  exact e'

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := by
  intro R _ _ _ _ D A G _ _ _ U a a' h h' hd E hEa hEh F _ _ _ y g g' hg hact
  subst hEa hEh
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  have hs := (endData_symm_and_ofOAct R D.toPre).1 _ _ _ _ hd
  obtain ⟨ha, ha', -, hc, hc', -⟩ := hd
  obtain ⟨-, -, hr', -, -, hbal'⟩ := hs
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hr'
  obtain ⟨gb, gv⟩ := (isIota_iff _ _).1 hg
  refine (isIota_iff _ _).2 ⟨?_, fun χ z J hJ => ?_⟩
  · rw [hact.1, gb, cP, cP, hc, ← Category.assoc]
  · obtain ⟨v, hv, vv⟩ := exists_v hG D.toPre a' E.aB E.h hc' u hu u₀ χ
    have k1 : val (E.u χ) g.b.left z J = val u (lift (cP D.toPre _ χ) g.b).left z J := by
      have := vv _ g.b _ (𝟙 _) z J hJ
      rw [Category.id_comp, Category.id_comp] at this
      exact (GlobalTheory.UT.SymFrame.normd_unique hG (E.u_norm χ) hv _ z J hJ).trans this
    rw [hact.2 χ z J hJ, gv _ z J hJ, k1, gb]
    let κ : TF (R := R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by rw [Category.id_comp]; rfl)
    have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal' u hu u₀ χ y) κ.left)
    have e' : val (LB.pullGen D.toPre.P.L _ _ u (D.toPre.pt2 χ y)) κ.left z J =
        val u (lift (cP D.toPre _ χ) (cP D.toPre _ y)).left z J := by
      rw [val_pull hJ, ← comp_cP D.toPre κ, ← comp_cP D.toPre κ y, ← comp_lift]; rfl
    rw [← e']
    exact (congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) rfl).trans
      (e.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))

end GlobalTheory.Mum.KeepsIota

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismCarriesPeriodPointBalaStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.uniformisationEndomorphism_carries_periodPoint_balanced : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := by
  first | exact @GlobalTheory.Mum.KeepsIota.main | exact GlobalTheory.Mum.KeepsIota.main | (intros; apply GlobalTheory.Mum.KeepsIota.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointUniformisationEndomorphismLiesOverAdjoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Mum.AdjEnd

theorem rosati_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (f g g' : D.toPre.P.A ⟶ D.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom g' → RosatiAdj D.toPre.P.A D.toPre.P.L f g → RosatiAdj D.toPre.P.A D.toPre.P.L f g' → g = g' := GlobalTheory.T.rosatiAdjoint_unique_degenerationData

theorem keepsIota : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ E : EndU U.toUnifPre, E.aB = a → E.h = h' → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (y : D.toPre.X) (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (h y) g' := GlobalTheory.T.uniformisationEndomorphism_carries_periodPoint_balanced

theorem aB_h_eq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : AdmBase R (maximalIdeal R))
    (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D A G) (E : EndU U) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X)
    (ha : IsMonHom a) (hE : FormalEnd U a h' fun e => (Over.pullback (thick R (maximalIdeal R) e)).map E.aG) :
    E.aB = a ∧ E.h = h' := by
  have := E.homG
  have := E.homB
  have hu := fun e => gtCoord_end_torus_abelian GlobalTheory.firstFiveLaws R (maximalIdeal R) hR D.toPre e G (U.gt e)
    ((Over.pullback (thick R (maximalIdeal R) e)).map E.aG) inferInstance
  have hm : ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map E.aB =
      (Over.pullback (thick R (maximalIdeal R) e)).map a := fun e =>
    (hu e).2.unique ⟨inferInstance, (E.q_lin e)⟩ ⟨inferInstance, hE.2.2.1 e⟩
  have := D.toPre.P.isAb.proper
  haveI : IsNoetherianRing R := hR.1
  refine ⟨GlobalTheory.hom_eq_of_thickenings_of_isProper R (maximalIdeal R) (IsLocalRing.maximalIdeal_le_jacobson _)
    D.toPre.P.A D.toPre.P.A _ _ fun e => ?_, ?_⟩
  · have k := congrArg (fun m => m.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) (hm e)
    simp only [GlobalTheory.EndData.map_fst] at k
    exact k
  · obtain ⟨t, ht, hi⟩ := hE.2.2.2 0
    obtain ⟨t', ht', hi'⟩ := E.i_lin 0
    exact (hu 0).1.unique ⟨t', ht', hi'⟩ ⟨t, ht, hi⟩

theorem linEnd_of_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → IsMonHom g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) → LinEnd U.toUnifPre a' h g' := by
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hD g g' hg hg' hL
  obtain ⟨hadm, hc⟩ := hB
  have hF := GlobalTheory.UT.functorial_of_unif R (maximalIdeal R) hadm D A G hG U
  have := U.gen_hom
  have := hg.1
  have ex : ∀ b : G ⟶ G, IsMonHom b → ∃ E : EndU U.toUnifPre, E.aG = b := fun b hb => by
    obtain ⟨E, e1, -⟩ := hF.1 b (U.gen.inv ≫ (Over.pullback (jK R)).map b ≫ U.gen.hom) hb inferInstance (by simp)
    exact ⟨E, e1⟩
  obtain ⟨E, rfl⟩ := ex g hg.1
  obtain ⟨E', rfl⟩ := ex g' hg'
  obtain ⟨⟨-, hRB, -, -⟩, hFp⟩ := hF.2 E E' hL
  obtain ⟨haB, hh⟩ := aB_h_eq R hadm D A G U.toUnifPre E a h' hD.1 hg.2
  have ha' : E'.aB = a' := rosati_unique R ⟨hadm, hc⟩ D a E'.aB a' hD.1 E'.homB hD.2.1 (haB ▸ hRB) hD.2.2.1
  have hh2 : E'.h = h := by
    ext y
    let F := AlgebraicClosure (FractionRing R)
    obtain ⟨g₀, hg₀⟩ := GlobalTheory.TorusExt.exists_iota (F := F) D.tau_bimult y
    obtain ⟨g₁, hg₁, -⟩ := ((hFp F).1 g₀)
    exact GlobalTheory.IotaInj.main GlobalTheory.firstFiveLaws R (maximalIdeal R) hadm D F _ _ g₁ ((hFp F).2.1 y g₀ g₁ hg₀ hg₁)
      (keepsIota R ⟨hadm, hc⟩ D A G hG U a a' h h' hD E haB hh F y g₀ g₁ hg₀ hg₁)
  have := E'.homG
  exact ⟨inferInstance, fun e => inferInstance, fun e => GlobalTheory.Mum.EndModel.thickMap_map _ e,
    fun e => ha' ▸ E'.q_lin e, fun e => hh2 ▸ E'.i_lin e⟩

end GlobalTheory.Mum.AdjEnd
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointUniformisationEndomorphismLiesOverAdjointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.adjoint_uniformisationEndomorphism_lies_over_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → IsMonHom g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L) → LinEnd U.toUnifPre a' h g' := by
  first | exact @GlobalTheory.Mum.AdjEnd.linEnd_of_adjoint | exact GlobalTheory.Mum.AdjEnd.linEnd_of_adjoint | (intros; apply GlobalTheory.Mum.AdjEnd.linEnd_of_adjoint <;> assumption)
end
end
