module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumTwistedSectionFamilyTendsToZeroStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBaseStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFunctionalEquationOfAdicSumTermwiseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRelationMulOfRelatedPairsStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeProductTwistedSectionsVanishing

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem prod_tφ_eq {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n j : ℤ) (β : D.X)
    {U : Type} [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U) :
    ∏ k, h (tφ D a β k) ^ tε n j k =
      h (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ (n - 1) * h ((toUnit D.P.A ≫ D.c β) * 𝟙 D.P.A : D.P.A ⟶ D.P.A).left *
        (h (toUnit D.P.A ≫ D.c β).left)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left * h a.left ^ j := by
  rw [Fin.prod_univ_five, _root_.mul_comm (toUnit D.P.A ≫ D.c β)]
  simp only [← zpow_neg_one]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (zpow_one _)) rfl)
    (zpow_one _)) rfl

theorem exists_isProdT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n j n' j' : ℤ)
    (β β' : D.X) (f : SecT D a n j β) (g : SecT D a n' j' β') :
    ∃ p : SecT D a (n + n') (j + j') (β + β'), IsProdT f g p := by
  have hadd : toUnit D.P.A ≫ D.c (β + β') = (toUnit D.P.A ≫ D.c β) * (toUnit D.P.A ≫ D.c β') := by
    rw [D.c_add]; exact MonObj.comp_mul _ _ _
  have hu := DVR.pullGen_isGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t D.cub.isGen
    (lift (toUnit _ ≫ D.c β) (lift (toUnit _ ≫ D.c β') (𝟙 D.P.A)) : D.P.A ⟶ G3 D.P.A).left
  obtain ⟨p, hp⟩ := exists_sec D.P.isLB (φ' := tφ D a (β + β')) (ε' := tε (n + n') (j + j')) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans
        (congrArg₂ (· * ·) (prod_tφ_eq D a n j β h) (prod_tφ_eq D a n' j' β' h)))
        (prod_cub (toUnit D.P.A ≫ D.c β) (toUnit D.P.A ≫ D.c β') (𝟙 D.P.A) h))).trans ?_
      rw [prod_tφ_eq, hadd]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec f g) (genSec _ hu))
  refine ⟨p, fun Z x z J hJ => (hp Z x z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    (H1.SectionArithmetic.sval_mulSec _ _ _ z hJ) ((sval_genSec _ hu _ z hJ).trans (congrArg Units.val (val_pull hJ _ _ _)))))⟩

theorem exists_prodT_van : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (β β' : D.toPre.X) (f : SecT D.toPre a n j β) (g : SecT D.toPre a n' j' β'), ∃ p : SecT D.toPre a n'' j'' (β + β'), IsProdT f g p ∧ ∀ e, (Van (maximalIdeal R) f e ∨ Van (maximalIdeal R) g e) → Van (maximalIdeal R) p e := by
  intro R _ _ _ _ D a n j n' j' n'' j'' hn hj β β' f g
  subst hn hj
  obtain ⟨p, hp⟩ := exists_isProdT D.toPre a n j n' j' β β' f g
  refine ⟨p, hp, fun e he Z x z J hJ => ?_⟩
  rw [hp Z _ z J hJ]
  rcases he with he | he
  · rw [he Z x z J hJ, zero_mul, zero_mul]
  · rw [he Z x z J hJ, mul_zero, zero_mul]

end GlobalTheory.TwFam
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeProductTwistedSectionsVanishingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.exists_cubeProduct_twistedSections_vanishing : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (β β' : D.toPre.X) (f : SecT D.toPre a n j β) (g : SecT D.toPre a n' j' β'), ∃ p : SecT D.toPre a n'' j'' (β + β'), IsProdT f g p ∧ ∀ e, (Van (maximalIdeal R) f e ∨ Van (maximalIdeal R) g e) → Van (maximalIdeal R) p e := by
  first | exact @GlobalTheory.TwFam.exists_prodT_van | exact GlobalTheory.TwFam.exists_prodT_van | (intros; apply GlobalTheory.TwFam.exists_prodT_van <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionMulOfMemberProducts

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem texp_mul_of_prod : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (f : ∀ β, SecT D.toPre a n j β) (g : ∀ β, SecT D.toPre a n' j' β) (p : ∀ q : D.toPre.X × D.toPre.X, SecT D.toPre a n'' j'' (q.1 + q.2)) (τ : SecE U.toUnifPre b n j) (τ' : SecE U.toUnifPre b n' j') (τ'' : SecE U.toUnifPre b n'' j''), Small (maximalIdeal R) (w := id) f → Small (maximalIdeal R) (w := id) g → (∀ q : D.toPre.X × D.toPre.X, IsProdT (f q.1) (g q.2) (p q)) → TExp U.toUnifPre τ (w := id) f → TExp U.toUnifPre τ' (w := id) g → (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' * sval τ' x z J') → TExp U.toUnifPre τ'' (w := fun q : D.toPre.X × D.toPre.X => q.1 + q.2) p := by
  intro R _ _ _ _ D a A G _ _ _ U e b n j n' j' n'' j'' hn hj f g p τ τ' τ'' hf hg hp hτ hτ' hτ''
  classical
  subst hn hj
  intro S hS Z x z J J' hJ hJ'
  have hy : x ≫ (U.gt e).pG.left = (x ≫ (U.gt e).q.left) ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) := by
    simp [GtCoord.pG, DegPre.prBe, Over.comp_left, Over.map_map_left, Over.homMk_left]
  have vanAt : ∀ {n j : ℤ} {β : D.toPre.X} (s : SecT D.toPre a n j β), Van (maximalIdeal R) s e →
      sval s (x ≫ (U.gt e).pG.left) z J = 0 := fun s hs => by rw [hy]; exact hs Z _ z J hJ
  have h1 : evalE U.toUnifPre τ'' x z J J' = evalE U.toUnifPre τ x z J J' * evalE U.toUnifPre τ' x z J J' := by
    simp only [evalE, zpow_add, Units.val_mul]; rw [hτ'' Z x z J' hJ']; ring
  have hL : ∀ χ χ' : D.toPre.X, x ≫ (lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (U.gt e).pG)).left =
      (x ≫ (U.gt e).pG.left) ≫ (lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (𝟙 D.toPre.P.A)) :
        D.toPre.P.A ⟶ G3 D.toPre.P.A).left := by
    intro χ χ'
    rw [Category.assoc, ← Over.comp_left]
    congr 2
    simp [comp_lift]
  have hT : ∀ χ χ' : D.toPre.X, (val ((U.gt e).t (χ + χ')) x z J).val *
      (val D.toPre.cub.t ((x ≫ (U.gt e).pG.left) ≫ (lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (𝟙 D.toPre.P.A)) :
        D.toPre.P.A ⟶ G3 D.toPre.P.A).left) z J).val =
      (val ((U.gt e).t χ) x z J).val * (val ((U.gt e).t χ') x z J).val := by
    intro χ χ'
    have h := (val_mul hJ _ _ x).symm.trans ((val_corr hJ ((U.gt e).t_mul χ χ') x).trans (val_mul hJ _ _ x))
    have h' := (congrArg (val ((U.gt e).t (χ + χ')) x z J * ·) (val_pull hJ _ _ x)).symm.trans h
    rw [← hL χ χ']
    exact (Units.val_mul _ _).symm.trans ((congrArg Units.val h').trans (Units.val_mul _ _))
  have hSf : ∀ i ∉ (hf e).toFinset, Van (maximalIdeal R) (f i) e := fun i hi =>
    by_contra fun hc => hi ((hf e).mem_toFinset.2 hc)
  have hSg : ∀ i ∉ (hg e).toFinset, Van (maximalIdeal R) (g i) e := fun i hi =>
    by_contra fun hc => hi ((hg e).mem_toFinset.2 hc)
  have ef : evalE U.toUnifPre τ x z J J' = ∑ i ∈ (hf e).toFinset,
      sval (f i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t i) x z J).val := hτ _ hSf Z x z J J' hJ hJ'
  have eg : evalE U.toUnifPre τ' x z J J' = ∑ i ∈ (hg e).toFinset,
      sval (g i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t i) x z J).val := hτ' _ hSg Z x z J J' hJ hJ'
  have hP := fun q => hp q Z (x ≫ (U.gt e).pG.left) z J hJ
  have z₁ : ∀ q ∉ S, sval (p q) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (q.1 + q.2)) x z J).val = 0 :=
    fun q hq => by rw [vanAt _ (hS q hq), zero_mul]
  have z₂ : ∀ q ∉ (hf e).toFinset ×ˢ (hg e).toFinset,
      sval (p q) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (q.1 + q.2)) x z J).val = 0 := by
    intro q hq
    rw [Finset.mem_product, not_and_or] at hq
    rw [hP q]
    rcases hq with h | h
    · rw [vanAt _ (hSf _ h), zero_mul, zero_mul, zero_mul]
    · rw [vanAt _ (hSg _ h), mul_zero, zero_mul, zero_mul]
  show _ = ∑ q ∈ S, sval (p q) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (q.1 + q.2)) x z J).val
  rw [h1, ef, eg, Finset.sum_mul_sum, ← Finset.sum_product',
    Finset.sum_subset (Finset.subset_union_right (s₁ := (hf e).toFinset ×ˢ (hg e).toFinset)) (fun q _ hq => z₁ q hq),
    ← Finset.sum_subset (Finset.subset_union_left (s₂ := S)) (fun q _ hq => z₂ q hq)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hP q]
  linear_combination (-(sval (f q.1) (x ≫ (U.gt e).pG.left) z J * sval (g q.2) (x ≫ (U.gt e).pG.left) z J)) * hT q.1 q.2

end GlobalTheory.TwFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionMulOfMemberProductsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.twistedExpansion_mul_of_memberProducts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (f : ∀ β, SecT D.toPre a n j β) (g : ∀ β, SecT D.toPre a n' j' β) (p : ∀ q : D.toPre.X × D.toPre.X, SecT D.toPre a n'' j'' (q.1 + q.2)) (τ : SecE U.toUnifPre b n j) (τ' : SecE U.toUnifPre b n' j') (τ'' : SecE U.toUnifPre b n'' j''), Small (maximalIdeal R) (w := id) f → Small (maximalIdeal R) (w := id) g → (∀ q : D.toPre.X × D.toPre.X, IsProdT (f q.1) (g q.2) (p q)) → TExp U.toUnifPre τ (w := id) f → TExp U.toUnifPre τ' (w := id) g → (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' * sval τ' x z J') → TExp U.toUnifPre τ'' (w := fun q : D.toPre.X × D.toPre.X => q.1 + q.2) p := by
  first | exact @GlobalTheory.TwFam.texp_mul_of_prod | exact GlobalTheory.TwFam.texp_mul_of_prod | (intros; apply GlobalTheory.TwFam.texp_mul_of_prod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductSmallTwistedFunctionalEqnFamily

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem GlobalTheory.TwFam.exists_prod_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (f : ∀ β, SecT D.toPre a n j β) (g : ∀ β, SecT D.toPre a n' j' β), Small (maximalIdeal R) (w := id) f → Small (maximalIdeal R) (w := id) g → TFE h h' f → TFE h h' g → ∃ F : ∀ β, SecT D.toPre a n'' j'' β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧ ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) n j) (τ' : SecE U.toUnifPre (b e) n' j'), TExp U.toUnifPre τ (w := id) f → TExp U.toUnifPre τ' (w := id) g → ∃ τ'' : SecE U.toUnifPre (b e) n'' j'', (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' * sval τ' x z J') ∧ TExp U.toUnifPre τ'' (w := id) F := by
  intro R _ _ _ hadm D a a' h h' hED A G _ _ hG U b hb n j n' j' n'' j'' hn hj f g hfs hgs hf hg
  have hP := GlobalTheory.T.exists_cubeProduct_twistedSections_vanishing R hadm D a n j n' j' n'' j'' hn hj
  choose p hpP hpV using fun q : D.toPre.X × D.toPre.X => hP q.1 q.2 (f q.1) (g q.2)
  have hps : Small (maximalIdeal R) (w := fun q : D.toPre.X × D.toPre.X => q.1 + q.2) p := by
    intro e
    refine ((hfs e).prod (hgs e)).subset ?_
    intro q hq
    by_contra hc
    simp only [Set.mem_prod, Set.mem_setOf_eq, not_and_or, not_not] at hc
    exact hq (hpV q e hc)
  obtain ⟨F, hFs, hFsm⟩ := GlobalTheory.T.exists_adicSum_twistedSectionFamily_tendsToZero R hadm D a n'' j'' (D.toPre.X × D.toPre.X) (fun q => q.1 + q.2) p hps
  refine ⟨F, hFsm, ?_, ?_⟩
  · let σ : D.toPre.X → (D.toPre.X × D.toPre.X) ≃ (D.toPre.X × D.toPre.X) := fun mu =>
      Equiv.prodCongr (Equiv.addRight (shift h h' n j mu)) (Equiv.addRight (shift h h' n' j' mu))
    have hσw : ∀ mu q, (σ mu q).1 + (σ mu q).2 = q.1 + q.2 + shift h h' n'' j'' mu := by
      intro mu q
      subst hn hj
      simp only [σ, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.coe_addRight, shift, add_smul]
      abel
    have hσr : ∀ (mu : D.toPre.X) (q : D.toPre.X × D.toPre.X), TRel h mu (p q) (p (σ mu q)) := fun mu q =>
      GlobalTheory.T.twistedRelation_mul_of_related_pairs R hadm D a a' h h' hED n j n' j' n'' j'' hn hj mu q.1 q.2 (σ mu q).1 (σ mu q).2
        (f q.1) (g q.2) (p q) (f _) (g _) (p (σ mu q)) rfl rfl (hpP q) (hpP (σ mu q)) (hf mu q.1) (hg mu q.2)
    exact GlobalTheory.T.twistedFunctionalEquation_of_adicSum_termwise R hadm D a a' h h' hED n'' j'' (D.toPre.X × D.toPre.X) (fun q => q.1 + q.2) p F σ
      hps hFs hσw hσr
  · intro e τ τ' hτ hτ'
    have hform : FormEq
        (Sum.elim ![(fstG (maximalIdeal R) e G).left, (b e).left ≫ (fstG (maximalIdeal R) e G).left]
          ![(fstG (maximalIdeal R) e G).left, (b e).left ≫ (fstG (maximalIdeal R) e G).left])
        (Sum.elim ![n, j] ![n', j'])
        ![(fstG (maximalIdeal R) e G).left, (b e).left ≫ (fstG (maximalIdeal R) e G).left] ![n'', j''] := by
      intro V _ k
      rw [Fintype.prod_sum_type]
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Sum.elim_inl,
        Sum.elim_inr, hn, hj, zpow_add]
      exact mul_mul_mul_comm _ _ _ _
    obtain ⟨τ'', hτ''⟩ := exists_sec U.LG.isLB hform (H1.SectionArithmetic.mulSec τ τ')
    have hmul : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'),
        Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' * sval τ' x z J' := fun Z x z J' hJ =>
      (hτ'' Z x z J' hJ).trans (H1.SectionArithmetic.sval_mulSec τ τ' x z hJ)
    exact ⟨τ'', hmul, GlobalTheory.T.twistedExpansion_adicSums_admissibleBase R hadm D a A G hG U e (b e) n'' j'' τ'' (D.toPre.X × D.toPre.X)
      (fun q => q.1 + q.2) p F hps hFs
      (GlobalTheory.T.twistedExpansion_mul_of_memberProducts R hadm D a A G hG U e (b e) n j n' j' n'' j'' hn hj f g p τ τ' τ'' hfs hgs hpP hτ hτ' hmul)⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductSmallTwistedFunctionalEqnFamilyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.exists_product_small_twistedFunctionalEqn_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (f : ∀ β, SecT D.toPre a n j β) (g : ∀ β, SecT D.toPre a n' j' β), Small (maximalIdeal R) (w := id) f → Small (maximalIdeal R) (w := id) g → TFE h h' f → TFE h h' g → ∃ F : ∀ β, SecT D.toPre a n'' j'' β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧ ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) n j) (τ' : SecE U.toUnifPre (b e) n' j'), TExp U.toUnifPre τ (w := id) f → TExp U.toUnifPre τ' (w := id) g → ∃ τ'' : SecE U.toUnifPre (b e) n'' j'', (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' * sval τ' x z J') ∧ TExp U.toUnifPre τ'' (w := id) F := by
  first | exact @GlobalTheory.TwFam.exists_prod_family | exact GlobalTheory.TwFam.exists_prod_family | (intros; apply GlobalTheory.TwFam.exists_prod_family <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplierPowerMulPullbackSmallFamily

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.ZmPow

theorem pow_mul_small : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N k : ℕ) (g : ∀ β, SecT D.toPre a N (-1) β) (ρ : ∀ β, SecT D.toPre a 0 k β), Small (maximalIdeal R) (w := id) g → Small (maximalIdeal R) (w := id) ρ → TFE h h' g → TFE h h' ρ → ∃ F : ∀ β, SecT D.toPre a ((N * k : ℕ) : ℤ) 0 β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧ ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) N (-1)) (τ' : SecE U.toUnifPre (b e) 0 k), TExp U.toUnifPre τ (w := id) g → TExp U.toUnifPre τ' (w := id) ρ → ∃ τ'' : SecE U.toUnifPre (b e) ((N * k : ℕ) : ℤ) 0, (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' ^ k * sval τ' x z J') ∧ TExp U.toUnifPre τ'' (w := id) F := by
  intro R _ _ _ hAdm D a a' h h' hE A G _ _ hG U b hb N k g ρ hgS hρS hgT hρT
  have key : ∀ m : ℕ, ∀ n j : ℤ, n = (N : ℤ) * m → j = (k : ℤ) - m →
      ∃ F : ∀ β, SecT D.toPre a n j β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧
        ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) N (-1)) (τ' : SecE U.toUnifPre (b e) 0 k),
          TExp U.toUnifPre τ (w := id) g → TExp U.toUnifPre τ' (w := id) ρ →
          ∃ τ'' : SecE U.toUnifPre (b e) n j,
            (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'),
              Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' ^ m * sval τ' x z J') ∧
            TExp U.toUnifPre τ'' (w := id) F := by
    intro m
    induction m with
    | zero =>
      intro n j hn hj
      have hn' : n = 0 := by simp [hn]
      have hj' : j = (k : ℤ) := by simp [hj]
      subst hn' hj'
      refine ⟨ρ, hρS, hρT, fun e τ τ' _ hτ' => ⟨τ', fun Z x z J' _ => by simp, hτ'⟩⟩
    | succ m ih =>
      intro n j hn hj
      obtain ⟨Fm, hFS, hFT, hFm⟩ := ih ((N : ℤ) * m) ((k : ℤ) - m) rfl rfl
      obtain ⟨F, hS, hT, hP⟩ := GlobalTheory.T.exists_product_small_twistedFunctionalEqn_family R hAdm D a a' h h' hE A G hG U b hb
        (N : ℤ) (-1) ((N : ℤ) * m) ((k : ℤ) - m) n j (by rw [hn]; push_cast; ring)
        (by rw [hj]; push_cast; ring) g Fm hgS hFS hgT hFT
      refine ⟨F, hS, hT, fun e τ τ' hτ hτ' => ?_⟩
      obtain ⟨τm, hτmv, hτmE⟩ := hFm e τ τ' hτ hτ'
      obtain ⟨τ'', hv, hE''⟩ := hP e τ τm hτ hτmE
      refine ⟨τ'', fun Z x z J' hJ => ?_, hE''⟩
      rw [hv Z x z J' hJ, hτmv Z x z J' hJ]
      ring
  exact key k _ _ (by push_cast; ring) (by simp)

end GlobalTheory.ZmPow
end
end
