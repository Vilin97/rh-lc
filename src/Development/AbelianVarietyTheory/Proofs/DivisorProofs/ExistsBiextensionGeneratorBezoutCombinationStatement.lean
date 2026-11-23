module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLambdaGeneratorZpowWithPeriods

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.TauTwist ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem degenerationPointOfLattice_zsmul (T : Over (Spec (CommRingCat.of R))) (n : ℤ) (b : D.X) : cP D T (n • b) = cP D T b ^ n := by
  let f : Multiplicative D.X →* (T ⟶ D.P.A) :=
    { toFun := fun x => cP D T x.toAdd
      map_one' := by simpa using cPoint_nsmul D T 0 0
      map_mul' := fun x y => cPoint_add D T _ _ }
  have := map_zpow f (Multiplicative.ofAdd b) n
  simpa [f] using this

theorem overSpec_comp_zpow_grpObj {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (y : T ⟶ D.P.A) (n : ℤ) :
    ρ ≫ y ^ n = (ρ ≫ y) ^ n := by
  let f : (T ⟶ D.P.A) →* (T' ⟶ D.P.A) :=
    { toFun := fun x => ρ ≫ x
      map_one' := MonObj.comp_one _
      map_mul' := fun x y => MonObj.comp_mul _ _ _ }
  exact map_zpow f y n

theorem value_tau_add_nsmul_mul_iteratedCube (hB : D.TauBimult) {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) (a₀ m v : D.X) (k : ℕ) :
    val (D.tau (a₀ + k • m) v) (𝟙 (TK R).left) z J *
        cubN (th D z J) k (cP D (TK R) a₀) (cP D (TK R) m) (cP D (TK R) v) =
      val (D.tau a₀ v) (𝟙 (TK R).left) z J * val (D.tau m v) (𝟙 (TK R).left) z J ^ k := by
  induction k with
  | zero => rw [zero_nsmul, add_zero]; simp [cubN]
  | succ k ih =>
    have e := val_tau_add (𝟙 (TK R)) hJ hB (a₀ + k • m) m v
    rw [cPoint_add, cPoint_nsmul] at e
    simp only [Over.id_left] at e
    rw [succ_nsmul, ← add_assoc, cubN, Finset.prod_range_succ]
    simp only [cubN] at ih
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    have ih' := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_pow] at e' ih' ⊢
    rw [succ_nsmul]
    linear_combination (norm := abel) e' + ih'

theorem exists_lamGen_zpow : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (n : ℤ),
    ∃ g : LB.Gen (LB.LinComb D.P.L (Sum.elim (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ n))
        (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A))) (Sum.elim Oε (fun l => -n * Oε l))), g.IsGen ∧
      ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val (D.tau a (n • b)) (𝟙 _) z J *
          val g (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J = val (D.tau a b) (𝟙 _) z J ^ n := by
  intro R _ _ D hB n
  have hL := D.P.isLB
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · obtain ⟨t, ht, hv⟩ := exists_cubN D.cub (1 : D.P.A ⊗ D.P.A ⟶ D.P.A) (snd D.P.A D.P.A) (fst D.P.A D.P.A) k
    have hF : FormEq
        ![(1 * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A).left, (1 * snd D.P.A D.P.A ^ k).left,
          (1 * fst D.P.A D.P.A).left, (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left, (snd D.P.A D.P.A * fst D.P.A D.P.A).left,
          (snd D.P.A D.P.A).left, (fst D.P.A D.P.A).left, (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left]
        ![1, -1, -1, 1, -(k : ℤ), k, k, -(k : ℤ)]
        (Sum.elim (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ (k : ℤ)))
          (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A)))
        (Sum.elim Oε (fun l => -(k : ℤ) * Oε l)) := by
      intro U _ h
      have e1 : (1 * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) =
          fst D.P.A D.P.A * snd D.P.A D.P.A ^ (k : ℤ) := by rw [_root_.one_mul, zpow_natCast, mul_comm]
      have e2 : (1 * snd D.P.A D.P.A ^ k : D.P.A ⊗ D.P.A ⟶ D.P.A) = snd D.P.A D.P.A ^ (k : ℤ) := by
        rw [_root_.one_mul, zpow_natCast]
      have e3 : (1 * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A := _root_.one_mul _
      have e4 : (snd D.P.A D.P.A * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A * snd D.P.A D.P.A :=
        mul_comm _ _
      rw [e1, e2, e3, e4, Fintype.prod_sum_type]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, GlobalTheory.PolDeg.lamPts, Oε, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      abel
    obtain ⟨g, hg, hgv⟩ := exists_gen hL hF t ht
    refine ⟨g, hg, fun a b z J hJ => ?_⟩
    rw [hgv _ _ z J hJ, hv (TK R) _ z J hJ, MonObj.comp_one, lift_fst, lift_snd]
    have e := val_tau_nsmul (𝟙 (TK R)) hJ hB k b a
    rw [val_tau_symm _ hJ (k • b) a, val_tau_symm _ hJ b a] at e
    simp only [Over.id_left] at e
    rw [natCast_zsmul, zpow_natCast]
    exact e
  · obtain ⟨t, ht, hv⟩ := exists_cubN D.cub (snd D.P.A D.P.A ^ (-(k : ℤ))) (snd D.P.A D.P.A) (fst D.P.A D.P.A) k
    have hF : FormEq
        ![(snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k * fst D.P.A D.P.A).left,
          (snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k).left,
          (snd D.P.A D.P.A ^ (-(k : ℤ)) * fst D.P.A D.P.A).left, (snd D.P.A D.P.A ^ (-(k : ℤ))).left,
          (snd D.P.A D.P.A * fst D.P.A D.P.A).left,
          (snd D.P.A D.P.A).left, (fst D.P.A D.P.A).left, (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left]
        (fun i => -(![1, -1, -1, 1, -(k : ℤ), k, k, -(k : ℤ)] : Fin 8 → ℤ) i)
        (Sum.elim (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ (-(k : ℤ))))
          (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A)))
        (Sum.elim Oε (fun l => -(-(k : ℤ)) * Oε l)) := by
      intro U _ h
      have e0 : (snd D.P.A D.P.A ^ (-(k : ℤ)) * snd D.P.A D.P.A ^ k : D.P.A ⊗ D.P.A ⟶ D.P.A) = 1 := by
        rw [zpow_neg, zpow_natCast, inv_mul_cancel]
      have e4 : (snd D.P.A D.P.A * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) = fst D.P.A D.P.A * snd D.P.A D.P.A :=
        mul_comm _ _
      have e5 : (snd D.P.A D.P.A ^ (-(k : ℤ)) * fst D.P.A D.P.A : D.P.A ⊗ D.P.A ⟶ D.P.A) =
          fst D.P.A D.P.A * snd D.P.A D.P.A ^ (-(k : ℤ)) := mul_comm _ _
      rw [e0, _root_.one_mul, e4, e5, Fintype.prod_sum_type]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, GlobalTheory.PolDeg.lamPts, Oε, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      abel
    obtain ⟨g, hg, hgv⟩ := exists_gen hL hF (LB.invGen _ _ _ t) (DVR.invGen_isGen _ _ _ _ ht)
    refine ⟨g, hg, fun a b z J hJ => ?_⟩
    rw [hgv _ _ z J hJ, val_inv, hv (TK R) _ z J hJ, overSpec_comp_zpow_grpObj, lift_fst, lift_snd]
    have c1 : (toUnit (TK R) ≫ D.c b) ^ (-(k : ℤ)) = cP D (TK R) ((-(k : ℤ)) • b) := (degenerationPointOfLattice_zsmul _ _ _).symm
    rw [c1]
    have e := value_tau_add_nsmul_mul_iteratedCube hB hJ ((-(k : ℤ)) • b) b a k
    have z0 := val_tau_nsmul (𝟙 (TK R)) hJ hB 0 b a
    rw [zero_nsmul] at z0
    simp only [Over.id_left, pow_zero, cubN, Finset.range_zero, Finset.prod_empty, _root_.mul_one] at z0
    have s0 : (-(k : ℤ)) • b + k • b = 0 := by rw [← natCast_zsmul, ← add_smul, neg_add_cancel, zero_smul]
    rw [s0, z0, _root_.one_mul] at e
    have s1 := val_tau_symm (𝟙 (TK R)) hJ a ((-(k : ℤ)) • b)
    have s2 := val_tau_symm (𝟙 (TK R)) hJ a b
    simp only [Over.id_left] at s1 s2
    rw [s1, s2]
    rw [show cubN (th D z J) k (cP D (TK R) ((-(k : ℤ)) • b)) (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c a) =
      cubN (th D z J) k (cP D (TK R) ((-(k : ℤ)) • b)) (cP D (TK R) b) (cP D (TK R) a) from rfl, e,
      mul_inv_rev, zpow_neg, zpow_natCast, mul_comm (_ ^ k)⁻¹, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLambdaGeneratorZpowWithPeriodsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_lambdaGenerator_zpow_with_periods : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (n : ℤ),
    ∃ g : LB.Gen (LB.LinComb D.P.L (Sum.elim (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ n))
        (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A))) (Sum.elim Oε (fun l => -n * Oε l))), g.IsGen ∧
      ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val (D.tau a (n • b)) (𝟙 _) z J *
          val g (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J = val (D.tau a b) (𝟙 _) z J ^ n := by
  first | exact @GlobalTheory.Mum.exists_lamGen_zpow | exact GlobalTheory.Mum.exists_lamGen_zpow | (intros; apply GlobalTheory.Mum.exists_lamGen_zpow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBiextensionGeneratorBezoutCombination

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LamComb

section Generators

variable {X Y Z : Scheme.{0}} {L : LB X} {J K : Type} [Fintype J] [Fintype K]

omit [Fintype J] in
theorem wchart_le (φ : J → K → (Y ⟶ X)) [Fintype J] (jj : J × K → L.ι) (i : J) :
    LB.wchart L (fun q : J × K => φ q.1 q.2) jj ≤ LB.wchart L (φ i) (fun k => jj (i, k)) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)

def prodGen (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ) (δ : J → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) :
    LB.Gen (LB.LinComb L (fun q : J × K => φ q.1 q.2) (fun q => δ q.1 * ε q.1 q.2)) where
  s := fun jj => ∏ i, res (wchart_le φ jj i) ((t i).s (fun k => jj (i, k))) ^ δ i

theorem gm_prodGen (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ) (δ : J → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i)))
    (r : Z ⟶ Y) (z : Z) (jj : J × K → L.ι) (h : r z ∈ LB.wchart L (fun q : J × K => φ q.1 q.2) jj) :
    gm r z (LB.wchart L (fun q : J × K => φ q.1 q.2) jj) ((prodGen φ ε δ t).s jj) =
      ∏ i, gm r z (LB.wchart L (φ i) (fun k => jj (i, k))) ((t i).s (fun k => jj (i, k))) ^ δ i :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    (map_zpow _ _ _).trans (congrArg (· ^ δ i) (gm_res r z _ h _)))

theorem isGen_prodGen (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ) (δ : J → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i)))
    (ht : ∀ i, (t i).IsGen) : (prodGen φ ε δ t).IsGen := by
  intro jj jj'
  refine unit_ext fun y hy => ?_
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun q : J × K => φ q.1 q.2) jj ⊓
    LB.wchart L (fun q : J × K => φ q.1 q.2) jj' := hy
  refine (gm_res (𝟙 Y) y _ hm _).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y jj jj' hm.1 hm.2) (gm_res (𝟙 Y) y _ hm _))).symm)
  refine (gm_prodGen φ ε δ t (𝟙 Y) y jj hm.1).trans
    (Eq.trans ?_ (congrArg _ (gm_prodGen φ ε δ t (𝟙 Y) y jj' hm.2)).symm)
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gen_trans (ht i) (𝟙 Y) y (wchart_le φ jj i hm.1) (wchart_le φ jj' i hm.2), mul_zpow]
  congr 1
  rw [trF, ← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_mul, mul_comm]

theorem val_prodGen (φ : J → K → (Y ⟶ X)) (ε : J → K → ℤ) (δ : J → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i)))
    (r : Z ⟶ Y) {z : Z} {I : (Z ⟶ X) → L.ι} (hI : Good L z I) :
    val (prodGen φ ε δ t) r z I = ∏ i, val (t i) r z I ^ δ i :=
  gm_prodGen φ ε δ t r z _ (hI.mem _ r)

end Generators

theorem prod_zpow_sum {U J : Type} [CommGroup U] (s : Finset J) (a : U) (f : J → ℤ) :
    ∏ j ∈ s, a ^ f j = a ^ ∑ j ∈ s, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

theorem exists_gen_lam_comb : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ {r : ℕ}
    (e c : Fin r → ℤ), ∑ j, e j * c j = 1 →
    ∃ u : LB.Gen (LB.LinComb D.P.L
        (Sum.elim (fun q : Fin r × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ c q.1) q.2)
          (fun I : ULift (Finset (Fin 2)) => (psum D.P.A (x2 D.P.A) I.down).left))
        (Sum.elim (fun q => e q.1 * Oε q.2) (fun I => -((-1) ^ (2 - I.down.card))))), u.IsGen ∧
      ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val (D.tau a b) (𝟙 _) z J = val u (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J *
          ∏ j, val (D.tau a (c j • b)) (𝟙 _) z J ^ e j := by
  intro R _ _ D hD r e c hec
  choose g hg hv using fun j => GlobalTheory.T.exists_lambdaGenerator_zpow_with_periods D hD (c j)
  have hF : FormEq (fun q : Fin r × (Fin 4 ⊕ Fin 4) => Sum.elim
        (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ c q.1))
        (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A)) q.2)
      (fun q => e q.1 * Sum.elim Oε (fun l => -c q.1 * Oε l) q.2)
      (Sum.elim (fun q : Fin r × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ c q.1) q.2)
          (fun I : ULift (Finset (Fin 2)) => (psum D.P.A (x2 D.P.A) I.down).left))
      (Sum.elim (fun q => e q.1 * Oε q.2) (fun I => -((-1) ^ (2 - I.down.card)))) := by
    intro U _ h
    simp only [Fintype.prod_prod_type, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_comm]
    have k : ∀ l, ∏ j, h (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A) l) ^ (e j * (-c j * Oε l)) =
        h (GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A) l) ^ (-Oε l) := fun l => by
      rw [prod_zpow_sum]
      congr 1
      calc ∑ j, e j * (-c j * Oε l) = (∑ j, e j * c j) * (-Oε l) := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = -Oε l := by rw [hec, _root_.one_mul]
    simp only [k]
    rw [← Equiv.ulift.symm.prod_comp, show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} from by decide,
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
      Fin.prod_univ_four]
    have q0 : psum D.P.A (x2 D.P.A) ∅ = 1 := rfl
    have q1 : psum D.P.A (x2 D.P.A) {0} = fst D.P.A D.P.A := _root_.mul_one _
    have q2 : psum D.P.A (x2 D.P.A) {1} = snd D.P.A D.P.A := _root_.mul_one _
    have q3 : psum D.P.A (x2 D.P.A) {0, 1} = fst D.P.A D.P.A * snd D.P.A D.P.A :=
      congrArg (fst D.P.A D.P.A * ·) (_root_.mul_one _)
    simp [q0, q1, q2, q3, GlobalTheory.PolDeg.lamPts, Oε]
    generalize h (fst D.P.A D.P.A * snd D.P.A D.P.A).left = A, h (fst D.P.A D.P.A).left = A₁,
      h (snd D.P.A D.P.A).left = A₂, h (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left = A₀
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨u, hu, hval⟩ := exists_gen D.P.isLB hF (prodGen _ _ e g) (isGen_prodGen _ _ e g hg)
  refine ⟨u, hu, fun a b z J hJ => ?_⟩
  rw [hval _ _ z J hJ, val_prodGen _ _ e g _ hJ, ← Finset.prod_mul_distrib]
  have : ∀ j, val (g j) (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J ^ e j *
      val (D.tau a (c j • b)) (𝟙 _) z J ^ e j = val (D.tau a b) (𝟙 _) z J ^ (e j * c j) := fun j => by
    rw [← mul_zpow, mul_comm, hv j a b z J hJ, ← zpow_mul, mul_comm]
  rw [Finset.prod_congr rfl fun j _ => this j, prod_zpow_sum, hec, zpow_one]

end GlobalTheory.Mum.LamComb
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBiextensionGeneratorBezoutCombinationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_biextension_generator_bezout_combination : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ {r : ℕ}
    (e c : Fin r → ℤ), ∑ j, e j * c j = 1 →
    ∃ u : LB.Gen (LB.LinComb D.P.L
        (Sum.elim (fun q : Fin r × Fin 4 => GlobalTheory.PolDeg.lamPts (fst D.P.A D.P.A) (snd D.P.A D.P.A ^ c q.1) q.2)
          (fun I : ULift (Finset (Fin 2)) => (psum D.P.A (x2 D.P.A) I.down).left))
        (Sum.elim (fun q => e q.1 * Oε q.2) (fun I => -((-1) ^ (2 - I.down.card))))), u.IsGen ∧
      ∀ (a b : D.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val (D.tau a b) (𝟙 _) z J = val u (lift (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)).left z J *
          ∏ j, val (D.tau a (c j • b)) (𝟙 _) z J ^ e j := by
  exact @GlobalTheory.Mum.LamComb.exists_gen_lam_comb
end
end
