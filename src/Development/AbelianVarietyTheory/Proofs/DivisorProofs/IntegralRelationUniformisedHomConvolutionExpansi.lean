module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyPerfectSectionsComplexOfNoetherianStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicSumSectionsOfFiniteSumsOnThickenings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedBundleFrameFromPartFramesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationUniformisedHomConvolutionExpansiAlt
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationKillsMixedSectionSumsLevelStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationUniformisedHomConvolutionExpansiAlt

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumSectionsPullbacksValueAbelianPart

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

noncomputable section
namespace GlobalTheory.SecAdicSumAny

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw GlobalTheory.SecAdicSum

theorem sumF_of_sum_on_thickenings_any : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (X : Scheme.{0}) (N : LB X), N.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ X)) (ε : K → ℤ) (Ix : Type) (n : Ix → LB.Sec (LB.LinComb N φ ε)) (n₀ : LB.Sec (LB.LinComb N φ ε)), (∀ e : ℕ, ∃ S : Finset Ix, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J), Good N z J → (∀ i ∉ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J = 0) ∧ sval n₀ (r ≫ (D.toPre.prBe I e).left) z J = ∑ i ∈ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J) → ∀ (b : TF (R := R) F ⟶ D.toPre.P.A) (τ : LB.Gen (LB.LinComb N (fun i => b.left ≫ φ i) ε)), τ.IsGen → ∀ (x : Ix → F) (x₀ : F), (∀ z J, Good N z J → (∀ i, sval (n i) b.left z J = cst F z (x i) * (val τ (𝟙 _) z J).val) ∧ sval n₀ b.left z J = cst F z x₀ * (val τ (𝟙 _) z J).val) → SumF I F x x₀ := by
  intro R _ _ _ I hR D F _ _ _ X N hL K _ φ ε Ix n n₀ hS b τ _ x x₀ hx
  have := hR.1
  have := D.toPre.P.isAb.smooth
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_noetherian R _ D.toPre.P.A.hom inferInstance
    (GlobalTheory.AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ (LB.isLB_linComb hL φ ε)
  choose v hv hv' using fun i => exists_vec P (n i)
  obtain ⟨v₀, hv₀, hv₀'⟩ := exists_vec P n₀
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' hL z
  obtain ⟨i₀, hi₀⟩ := exists_mem P (b.left z)
  let t := trF φ ε b.left z (P.ch i₀) (fun k => J (b.left ≫ φ k)) * val τ (𝟙 _) z J
  choose y hy using fun k => CoefBasic.cstH_surj z (gs b.left z _ (P.u k i₀) * (t⁻¹).val)
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  let ev : (Fin P.a → R) →ₗ[R] F := Fintype.linearCombination R y
  have key : ∀ (s : LB.Sec (LB.LinComb N φ ε)) (w : Fin P.a → R) (c : F),
      (∀ i, AbLaw.rs _ (P.le i) (s.f (P.ch i)) = loc₀ P w i) →
      sval s b.left z J = UT.cst F z c * (val τ (𝟙 _) z J).val → c = ev w := fun s w c h₁ h₂ => by
    have e := gs_loc₀ P h₁ b.left z hi₀ hJ
    rw [h₂, mul_left_comm, ← Units.val_mul, CoefBasic.cst_eq] at e
    refine CoefBasic.cstH_inj (R := R) z ?_
    have e' : CoefBasic.cstH z c = gs b.left z _ (loc₀ P w i₀) * (t⁻¹).val :=
      (Units.eq_mul_inv_iff_mul_eq t).2 e.symm
    have hs : ∀ a : Fin P.a → Γ(D.toPre.P.A.left, P.W i₀), gs b.left z _ (∑ k, a k) = ∑ k, gs b.left z _ (a k) :=
      fun a => by simp only [gs_eq b.left z _ hi₀, map_sum]
    rw [e', loc₀, hs, Finset.sum_mul]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (map_sum _ (fun k => w k • y k) _).symm
    rw [gs_mul b.left z _ hi₀, gs_cst_point b z _ hi₀, _root_.mul_assoc, ← hy, ← map_mul, ← Algebra.smul_def]
    rfl
  obtain rfl : x = fun i => ev (v i) := funext fun i => key _ _ _ (hv' i) ((hx z J hJ).1 i)
  obtain rfl : x₀ = ev v₀ := key _ _ _ hv₀' (hx z J hJ).2
  refine sumI_of_ker I P.D₀ ev v v₀ hv hv₀ fun e => ?_
  obtain ⟨S, hS⟩ := hS e
  refine ⟨S, fun T hT k => Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (comp_eq_zero P
    (IsPullback.of_hasPullback D.toPre.P.A.hom (thick R I e)) (v₀ - ∑ i ∈ T, v i) ?_ fun i p hp => ?_) k)⟩
  · simp only [Matrix.mulVec_sub, Matrix.mulVec_sum, hv, hv₀, Finset.sum_const_zero, sub_zero]
  · obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' hL p
    obtain ⟨h₁, h₂⟩ := hS _ (𝟙 _) p J' hJ'
    rw [Category.id_comp] at h₁ h₂
    have h₃ := h₂.trans (Finset.sum_subset hT fun j _ hj => h₁ j hj)
    have e₀ := gs_loc₀ P hv₀' _ p hp hJ'
    have e₁ := fun j => gs_loc₀ P (hv' j) _ p hp hJ'
    rw [gs_eq _ p _ hp] at e₀
    simp only [gs_eq _ p _ hp] at e₁

    rw [loc₀_sub_sum, gs_eq _ p _ hp, map_sub, map_sub, map_sum, map_sum, e₀, Finset.sum_congr rfl fun j _ => e₁ j,
    ← Finset.mul_sum]
    exact sub_eq_zero.2 (congrArg _ h₃)

end GlobalTheory.SecAdicSumAny
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumSectionsPullbacksValueAbelianPartStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

theorem _root_.GlobalTheory.T.adicSum_sections_pullbacks_value_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (X : Scheme.{0}) (N : LB X), N.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ X)) (ε : K → ℤ) (Ix : Type) (n : Ix → LB.Sec (LB.LinComb N φ ε)) (n₀ : LB.Sec (LB.LinComb N φ ε)), (∀ e : ℕ, ∃ S : Finset Ix, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J), Good N z J → (∀ i ∉ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J = 0) ∧ sval n₀ (r ≫ (D.toPre.prBe I e).left) z J = ∑ i ∈ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J) → ∀ (b : TF (R := R) F ⟶ D.toPre.P.A) (τ : LB.Gen (LB.LinComb N (fun i => b.left ≫ φ i) ε)), τ.IsGen → ∀ (x : Ix → F) (x₀ : F), (∀ z J, Good N z J → (∀ i, sval (n i) b.left z J = cst F z (x i) * (val τ (𝟙 _) z J).val) ∧ sval n₀ b.left z J = cst F z x₀ * (val τ (𝟙 _) z J).val) → SumF I F x x₀ := by
  first | exact @GlobalTheory.SecAdicSumAny.sumF_of_sum_on_thickenings_any | exact GlobalTheory.SecAdicSumAny.sumF_of_sum_on_thickenings_any | (intros; apply GlobalTheory.SecAdicSumAny.sumF_of_sum_on_thickenings_any <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedSectionJoinBundles

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix

noncomputable section
namespace GlobalTheory.Mum.Two.Mix

theorem prod_mix_hom {R : Type} [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (b : D₁.P.A ⟶ D₂.P.A) (α : D₁.X)
    (j j' : ℕ) {U : Type} [CommGroup U] (h : (D₁.P.A.left ⟶ D₁.P.A.left ⨿ D₂.P.A.left) → U) :
    ∏ i, h (mixφ D₁ D₂ b α i) ^ MixedConv.mixε j j' i = h (b.left ≫ coprod.inr) ^ (j : ℤ) *
      (h (Over.Hom.left (𝟙 D₁.P.A) ≫ coprod.inl) ^ ((j' : ℤ) - 1) * h ((cP D₁ D₁.P.A α * 𝟙 D₁.P.A).left ≫ coprod.inl) *
        (h ((cP D₁ D₁.P.A α).left ≫ coprod.inl))⁻¹ * h ((1 : D₁.P.A ⟶ D₁.P.A).left ≫ coprod.inl)) :=
  DVR.prod_sum₂ (K := PUnit.{1}) (K' := Fin 4) (U := U) _ (Fintype.prod_unique _)
    (MixedConv.prod_comp D₁ (𝟙 _) α j' (fun q => h (q ≫ coprod.inl)))

theorem exists_mix_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (b : D₁.P.A ⟶ D₂.P.A) (j j' : ℕ) (χ : D₂.X) (χ' β α : D₁.X), χ' + β = α → ∀ (u : LB.Gen (CmpLB D₁ D₂ b χ' χ)), u.IsGen → ∀ (f : D₂.SecB j χ) (f' : D₁.SecB j' β), ∃ n : LB.Sec (LB.LinComb (JN D₁ D₂) (mixφ D₁ D₂ b α) (MixedConv.mixε j j')), ∀ (Z : Scheme.{0}) (r : Z ⟶ D₁.P.A.left) (z : Z) (J), Good (JN D₁ D₂) z J → sval n r z J = sval f (r ≫ b.left) z (rr J) * sval f' r z (rl J) * (val u r z J * val (MixedConv.cubB D₁ χ' β) r z (rl J)).val := by
  intro R _ _ D₁ D₂ b j j' χ χ' β α hα u hu f f'
  subst hα
  have p₁ := isPart_inl D₁.P.L D₂.P.L
  have p₂ := isPart_inr D₁.P.L D₂.P.L
  obtain ⟨t, ht⟩ := exists_sec (jn_isLB D₁ D₂) (φ' := mixφ D₁ D₂ b (χ' + β)) (ε' := MixedConv.mixε j j')
    (fun U _ h => by
      have q₁ := prod_cub (cP D₁ D₁.P.A χ') (cP D₁ D₁.P.A β) (𝟙 D₁.P.A) (fun q => h (q ≫ coprod.inl))
      have q₂ := MixedConv.prod_comp D₂ b χ j (fun q => h (q ≫ coprod.inr))
      have q₃ := MixedConv.prod_comp D₁ (𝟙 _) β j' (fun q => h (q ≫ coprod.inl))
      have q₄ := prod_mix_hom D₁ D₂ b (χ' + β) j j' h
      have q₅ := MixedConv.prod_coord D₁ (𝟙 _) χ' (fun q => h (q ≫ coprod.inl))
      have q₆ := MixedConv.prod_coord_inv D₂ b χ (fun q => h (q ≫ coprod.inr))
      rw [DVR.cPoint_add] at q₄
      simp only [Over.id_left, Category.id_comp] at q₃ q₄
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := (Fin 4 ⊕ Fin 4) ⊕ thK) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ q₂ q₃)
        (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
          (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ q₅ q₆) q₁)) (Eq.trans ?_ q₄.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Over.id_left, Category.id_comp]
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec (p₂.sec (H1.SectionArithmetic.pullSec f b.left)) (p₁.sec f'))
      (Geo.Tor.genSec (LB.mulGen (JN D₁ D₂) _ _ _ _ u (p₁.gen (MixedConv.cubB D₁ χ' β)))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (p₁.gen_isGen (MixedConv.cubB_isGen D₁ χ' β)))))
  refine ⟨t, fun Z r z J hJ => ?_⟩
  exact (ht _ _ z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
      ((p₂.sval_sec _ _ z hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ z (p₂.good hJ))) (p₁.sval_sec _ _ z hJ)))
    ((sval_genSec _ _ _ z hJ).trans (congrArg Units.val ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (p₁.val_gen _ _ z hJ)))))))

end GlobalTheory.Mum.Two.Mix
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedSectionJoinBundlesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix

theorem _root_.GlobalTheory.T.exists_mixed_section_join_bundles : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (b : D₁.P.A ⟶ D₂.P.A) (j j' : ℕ) (χ : D₂.X) (χ' β α : D₁.X), χ' + β = α → ∀ (u : LB.Gen (CmpLB D₁ D₂ b χ' χ)), u.IsGen → ∀ (f : D₂.SecB j χ) (f' : D₁.SecB j' β), ∃ n : LB.Sec (LB.LinComb (JN D₁ D₂) (mixφ D₁ D₂ b α) (MixedConv.mixε j j')), ∀ (Z : Scheme.{0}) (r : Z ⟶ D₁.P.A.left) (z : Z) (J), Good (JN D₁ D₂) z J → sval n r z J = sval f (r ≫ b.left) z (rr J) * sval f' r z (rl J) * (val u r z J * val (MixedConv.cubB D₁ χ' β) r z (rl J)).val := by
  first | exact @GlobalTheory.Mum.Two.Mix.exists_mix_hom | exact GlobalTheory.Mum.Two.Mix.exists_mix_hom | (intros; apply GlobalTheory.Mum.Two.Mix.exists_mix_hom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSectionValueProductExpansionTerms

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix
namespace GlobalTheory.Mum.Two.Mix
open GlobalTheory.UT.MixedConv

theorem val_mixed_eval : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) (g : GtPtF D₁ F) (g' : GtPtF D₂ F), Act D₁ D₂ b h g g' → ∀ (j j' : ℕ) (w : Frm D₂ F j g'.b) (w' : Frm D₁ F j' g.b) (χ : D₂.X) (δ : D₁.X) (u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ)), Nrm u → ∀ (f : D₂.SecB j χ) (f' : D₁.SecB j' δ) (y y' : F), MixedConv.IsCoefB j g' w χ f y → MixedConv.IsCoefB j' g w' δ f' y' → ∀ (z : (TF (R := R) F).left) (J), Good (JN D₁ D₂) z J → sval f (g.b.left ≫ b.left) z (rr J) * sval f' g.b.left z (rl J) * (val u g.b.left z J * val (MixedConv.cubB D₁ (h χ) δ) g.b.left z (rl J)).val = cst F z (y * y') * (rigV D₂ (TF (R := R) F).hom z (rr J) ^ j * rigV D₁ (TF (R := R) F).hom z (rl J) ^ j' * (val (g.s (h χ + δ)) (𝟙 _) z (rl J) * (val w (𝟙 _) z (rr J) * val w' (𝟙 _) z (rl J)))⁻¹).val := by
  intro R _ _ D₁ D₂ F _ _ b h g g' hg j j' w w' χ δ u hu f f' y y' hy hy' z J hJ
  have h₁ : Good D₁.P.L z (rl J) := (isPart_inl D₁.P.L D₂.P.L).good hJ
  have h₂ : Good D₂.P.L z (rr J) := (isPart_inr D₁.P.L D₂.P.L).good hJ
  have c₂ : val (MixedConv.cubB D₁ (h χ) δ) g.b.left z (rl J) =
      th D₁ z (rl J) (cP D₁ _ (h χ)) (cP D₁ _ δ) g.b := by
    refine (val_cub D₁.cub g.b h₁ _ _ _).trans ?_
    rw [comp_cP, comp_cP, Category.comp_id]
  have c₃ := gt_mul (𝟙 (TF (R := R) F)) h₁ g (h χ) δ
  have c₄ := hy z (rr J) h₂
  have c₅ := hy' z (rl J) h₁
  have c₆ : g.b.left ≫ b.left = g'.b.left := (congrArg (fun q => q.left) hg.1).symm
  have c₉ := hg.2 χ u hu z J hJ
  rw [Category.id_comp, Over.id_left] at c₃
  rw [c₉, CoefBasic.cst_eq] at c₄
  rw [CoefBasic.cst_eq] at c₅
  rw [c₂, c₆, CoefBasic.cst_eq, map_mul, eq_comm, Units.val_mul, ← _root_.mul_assoc, Units.mul_inv_eq_iff_eq_mul]
  have c₇ := congrArg Units.val c₃
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at c₄ c₅ c₇ ⊢
  have c₈ := congrArg₂ (· * ·) c₄ c₅
  linear_combination c₈ - sval f (Over.Hom.left g'.b) z (rr J) * sval f' g.b.left z (rl J) * (val u g.b.left z J).val *
    (val w (𝟙 _) z (rr J)).val * (val w' (𝟙 _) z (rl J)).val * c₇

end GlobalTheory.Mum.Two.Mix
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSectionValueProductExpansionTermsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix

theorem _root_.GlobalTheory.T.mixed_section_value_product_expansion_terms : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) (g : GtPtF D₁ F) (g' : GtPtF D₂ F), Act D₁ D₂ b h g g' → ∀ (j j' : ℕ) (w : Frm D₂ F j g'.b) (w' : Frm D₁ F j' g.b) (χ : D₂.X) (δ : D₁.X) (u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ)), Nrm u → ∀ (f : D₂.SecB j χ) (f' : D₁.SecB j' δ) (y y' : F), MixedConv.IsCoefB j g' w χ f y → MixedConv.IsCoefB j' g w' δ f' y' → ∀ (z : (TF (R := R) F).left) (J), Good (JN D₁ D₂) z J → sval f (g.b.left ≫ b.left) z (rr J) * sval f' g.b.left z (rl J) * (val u g.b.left z J * val (MixedConv.cubB D₁ (h χ) δ) g.b.left z (rl J)).val = cst F z (y * y') * (rigV D₂ (TF (R := R) F).hom z (rr J) ^ j * rigV D₁ (TF (R := R) F).hom z (rl J) ^ j' * (val (g.s (h χ + δ)) (𝟙 _) z (rl J) * (val w (𝟙 _) z (rr J) * val w' (𝟙 _) z (rl J)))⁻¹).val := by
  first | exact @GlobalTheory.Mum.Two.Mix.val_mixed_eval | exact GlobalTheory.Mum.Two.Mix.val_mixed_eval | (intros; apply GlobalTheory.Mum.Two.Mix.val_mixed_eval <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationUniformisedHomConvolutionExpansi

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange
open GlobalTheory.Mum.Two.Mix

noncomputable section
namespace GlobalTheory.Mum.Two.Mix

theorem core : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁ U₂ a b h → Coord U₁ U₂ a b h → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (j j' : ℕ) (N : Type) [Fintype N] (ρ : N → R) (σ : N → H0 U₂.LG.L j) (σ' : N → H0 U₁.LG.L j') (f : N → ∀ α : D₂.toPre.X, D₂.toPre.SecB j α) (f' : N → ∀ α : D₁.toPre.X, D₁.toPre.SecB j' α), (∀ ν e, U₂.ExpandsAt e j (σ ν) (f ν)) → (∀ ν e, U₁.ExpandsAt e j' (σ' ν) (f' ν)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ G₁.left) (z : Z) (J₁ J₂), Good U₁.LG.L z J₁ → Good U₂.LG.L z J₂ → ∑ ν, constVal (r ≫ G₁.hom) z (ρ ν) * (sval (σ ν) (r ≫ a.left) z J₂ * sval (σ' ν) r z J₁) = 0) → ∀ (g : GtPtF D₁.toPre F) (g' : GtPtF D₂.toPre F), Act D₁.toPre D₂.toPre b h g g' → ∀ (w : Frm D₂.toPre F j g'.b) (w' : Frm D₁.toPre F j' g.b), w.IsGen → w'.IsGen → ∀ (x : N → D₂.toPre.X → F) (x' : N → D₁.toPre.X → F), (∀ ν χ, MixedConv.IsCoefB j g' w χ (f ν χ) (x ν χ)) → (∀ ν χ, MixedConv.IsCoefB j' g w' χ (f' ν χ) (x' ν χ)) → ∀ α : D₁.toPre.X, SumF I F (fun p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} => ∑ ν, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (ρ ν)) * (x ν p.1.1 * x' ν p.1.2)) 0 := by
  intro hL R _ _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a b h hLin hCo F _ _ _ j j' N _ ρ σ σ' f f' hE hE' hrel
    g g' hg w w' hw hw' x x' hx hx' α
  choose u hu using hCo
  choose n hn using fun (ν : N) (α : D₁.toPre.X) (p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α}) =>
    GlobalTheory.T.exists_mixed_section_join_bundles R D₁.toPre D₂.toPre b j j' p.1.1 (h p.1.1) p.1.2 α p.2 (u p.1.1) (hu p.1.1).1.1 (f ν p.1.1) (f' ν p.1.2)
  let m : ∀ α, {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} →
      SecOver D₁.toPre.P.A.hom (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j')) :=
    fun α p => ∑ ν, ρ ν • (show SecOver D₁.toPre.P.A.hom _ from n ν α p)
  have hm : ∀ α p (Z : Scheme.{0}) (r : Z ⟶ D₁.toPre.P.A.left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J →
      sval (m α p) r z J = ∑ ν, constVal (r ≫ D₁.toPre.P.A.hom) z (ρ ν) *
        (sval (f ν p.1.1) (r ≫ b.left) z (rr J) * sval (f' ν p.1.2) r z (rl J) *
          (val (u p.1.1) r z J * val (MixedConv.cubB D₁.toPre (h p.1.1) p.1.2) r z (rl J)).val) :=
    fun α p Z r z J hJ =>
      (sval_sum' (π := D₁.toPre.P.A.hom) hJ _ _ _).trans (Finset.sum_congr rfl fun ν _ =>
        (sval_smul' (π := D₁.toPre.P.A.hom) hJ _ _ _).trans (congrArg _ (hn ν α p Z r z J hJ)))
  obtain ⟨τ, hτ, hv⟩ := GlobalTheory.T.exists_mixed_bundle_frame_from_part_frames R D₁.toPre D₂.toPre F b α j j' g _ hg.1 w w' hw hw'
  refine GlobalTheory.T.adicSum_sections_pullbacks_value_abelianPart R I hR D₁ F _ (JN D₁.toPre D₂.toPre) (jn_isLB D₁.toPre D₂.toPre) _ (mixφ D₁.toPre D₂.toPre b α)
    (MixedConv.mixε j j') _ (m α) (0 : SecOver D₁.toPre.P.A.hom _) (fun e => ?_) g.b τ hτ _ 0 fun z J hJ => ⟨fun p => ?_, ?_⟩
  · obtain ⟨S, hS⟩ := GlobalTheory.T.integral_relation_kills_mixed_section_sums_level R I D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a b h hLin.2.2.1 u (fun χ => (hu χ).2) j j' e N ρ σ σ' f f' (fun ν => hE ν e)
      (fun ν => hE' ν e) hrel m hm α
    exact ⟨S, fun Z r z J hJ => ⟨(hS Z r z J hJ).1,
      (sval_zero' (π := D₁.toPre.P.A.hom) hJ _).trans (hS Z r z J hJ).2.symm⟩⟩
  · obtain ⟨⟨χ, δ⟩, hp⟩ := p

    rw [hm _ _ _ _ z J hJ, CoefBasic.cst_eq, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have c₁ : constVal (g.b.left ≫ D₁.toPre.P.A.hom) z (ρ ν) =
        CoefBasic.cstH z (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (ρ ν))) := by
      refine Eq.trans ?_ (CoefBasic.cst_eq z _)
      rw [Over.w g.b]
      refine (constVal_specMap (jFK (R := R) F) _ z _).trans ?_
      exact (congrArg (fun q => constVal q z _) (Category.id_comp _).symm).trans (constVal_specMap (𝟙 _) _ z _)
    have e₁ := GlobalTheory.T.mixed_section_value_product_expansion_terms R D₁.toPre D₂.toPre F b h g g' hg j j' w w' χ δ (u χ) (hu χ).1 (f ν χ) (f' ν δ) _ _ (hx ν χ) (hx' ν δ) z J hJ
    have e₂ := hv z J hJ
    dsimp only at hp
    subst hp
    rw [c₁, e₁, e₂, CoefBasic.cst_eq]
    simp only [map_mul]
    ring
  · rw [CoefBasic.cst_eq, map_zero, zero_mul]
    exact sval_zero' (π := D₁.toPre.P.A.hom) hJ _

end GlobalTheory.Mum.Two.Mix
end
end
end
