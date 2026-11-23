module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqvDown
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqvRational
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFamPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowSectionTransportPullbackIsoStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowSectionTransportPullbackIsoStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantBijectionsFamiliesSectionsDifferBySca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantBijectionLargerClosedFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueFieldExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitInverseExpansionEquivariantLabelsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorFieldPointThroughGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullFib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionDescendsFromAlgClosedField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitInverseExpansionEquivariantLabelsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSectionExpandingThetaFamily

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem Trait.exists_expBy_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W)
      (F₀ : IntFam (maximalIdeal R) D.toPre k), ∃ σ : SecK C.P.L.L T.β k, T.ExpBy 1 σ F₀ := by
  intro R _ _ _ hR D C k hk W _ _ _ T F₀
  have := hR.2
  have hW := T.cdvr
  have := hW.1
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have cW : CharZero W := charZero_of_injective_ringHom T.inj
  have hGs : IsSemiAbelian T.G := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso T.cart (isGrpPullback_pullback C.G T.ξ)
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback T.ξ C.G C.semi)
  obtain ⟨F', hF'⟩ := GlobalTheory.Mum.exists_intFam_pull R hR D W T.φ T.D' T.hD T.inj T.loc k F₀
  obtain ⟨σ', hσ'⟩ := GlobalTheory.Mum.IntFam.exists_expandsAt W ⟨bW, cW⟩ T.D' T.A T.G T.U hGs k hk F'
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_lineBundlePowSection_transport_pullbackIso C.P.L.L T.U.LG.L T.β T.ℓ C.P.L.isLB T.U.LG.isLB T.ℓ_gen k σ'
  refine ⟨σ, σ', F'.f, fun Z r z J J' hJ hJ' => ?_, hF', hσ'⟩
  have h1 : scal T.G.hom (1 : W) = 1 := by unfold scal; rw [map_one, map_one]
  rw [hσ Z r z J J' hJ hJ', h1, gs_eq r z ⊤ (by trivial), map_one, map_one, _root_.one_mul]

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSectionExpandingThetaFamilyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_integralSection_expanding_thetaFamily : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F₀ : IntFam (maximalIdeal R) D.toPre k), ∃ σ : SecK C.P.L.L T.β k, T.ExpBy 1 σ F₀ := by
  first | exact @GlobalTheory.Mum.Trait.exists_expBy_one | exact GlobalTheory.Mum.Trait.exists_expBy_one | (intros; apply GlobalTheory.Mum.Trait.exists_expBy_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFamilyExpansionEqConstMulAlgClosure

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem gs_liftFun_top {S0 : Scheme.{0}} (A : Over S0) {T : Over S0} (W : (T ⊗ A).left.Opens) (r : Γ(T.left, ⊤))
    {Z : Scheme.{0}} (q : Z ⟶ (T ⊗ A).left) (z : Z) (hz : q z ∈ W) :
    gs q z W (liftFun A W r) = gs (q ≫ (fst T A).left) z ⊤ r :=
  (gs_res q z le_top hz _).trans (gs_pull q (fst T A).left z ⊤ trivial r)

theorem fvalue_const : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ E₀ (Φ₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → H0 C.A.L (C.n ^ j)), Eqv D.toPre C.A (Kb R) (C.n ^ j) (C.lab j) E₀ → (∀ F₀ s, F₀.Over s → Agree C.A.L (E₀ s) (Φ₀ F₀)) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j)), (∀ F₀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J J', Good C.P.L.L z J → Good C.A.L z J' → sval (Φ F₀) p z J = (gw wA p z (J (p ≫ C.α)) (J' p) ^ (C.n ^ j)).val * sval (Φ₀ F₀) p z J') → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ c : F, c ≠ 0 ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J := by
  intro R _ _ _ hR D C j wA hwA E₀ Φ₀ hE₀ hΦ₀ Φ hΦ W _ _ _ T F _ _ _ _ em hem
  obtain ⟨lab, E, hlab, hE, hT⟩ := GlobalTheory.T.trait_inverse_expansion_equivariant_labels R hR D C j wA hwA W T F em hem
  have hodd : Odd (C.n ^ j) := C.n_odd.pow
  obtain ⟨E', hE', hAg⟩ := GlobalTheory.T.exists_equivariant_bijection_larger_closed_field R hR D C.A (C.n ^ j) hodd (C.lab j) E₀ Φ₀ hE₀ hΦ₀ F em lab hlab
  haveI : CharZero R := hR.2
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.Mum.eqv_eq_smul R (maximalIdeal R) D C.A F (C.n ^ j) hodd lab E E' hE hE'
  refine ⟨(c₀ : F)⁻¹, inv_ne_zero c₀.ne_zero, ?_⟩
  intro F₀ σ hσ Z p p' h1 h2 z J hJ
  obtain ⟨s, hs, -⟩ := GlobalTheory.Mum.IntFam.existsUnique_over R (maximalIdeal R) D.toPre (C.n ^ j) F₀ F
  obtain ⟨J', hJ', -⟩ := exists_good C.A.L C.A.isLB z (K := Empty) (fun e => e.elim) (fun e => e.elim)
    (fun a => a.elim) (fun k => k.elim)
  set q := p' ≫ (snd (TFK (R := R) F) C.A.A).left with hq
  have e1 := hT F₀ s σ hs hσ Z p p' h1 h2 z J J' hJ hJ'
  have e2 : sval (E' s) p' z J' = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)) * sval (E s) p' z J' := by
    unfold sval
    refine (congrArg (gs p' z _) (hc₀ s _)).trans ?_
    exact (gs_mul p' z _ (hJ'.mem _ p') _ _).trans (congrArg (· * _) (gs_liftFun_top _ _ _ _ _ (hJ'.mem _ p')))
  have e3 := hAg F₀ s hs Z p' q (Category.comp_id _).symm z J' hJ'
  have e4 := hΦ F₀ Z q z J J' hJ hJ'
  have hβ : J (q ≫ C.α) = J (p ≫ T.β) := by rw [h1, hq, Category.assoc]
  rw [hβ] at e4
  have huv : gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)⁻¹) *
      gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)) = 1 := by
    rw [← gs_mul (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ trivial, fnF, fnF, ← map_mul, inv_mul_cancel₀ c₀.ne_zero,
      map_one, gs_eq (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ trivial, map_one, map_one]
  rw [e1, e4, ← e3, e2]
  linear_combination (-(gw wA q z (J (p ≫ T.β)) (J' q) ^ (C.n ^ j)).val * sval (E s) p' z J') * huv

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFamilyExpansionEqConstMulAlgClosureStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.integral_family_expansion_eq_const_mul_algClosure : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ E₀ (Φ₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → H0 C.A.L (C.n ^ j)), Eqv D.toPre C.A (Kb R) (C.n ^ j) (C.lab j) E₀ → (∀ F₀ s, F₀.Over s → Agree C.A.L (E₀ s) (Φ₀ F₀)) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j)), (∀ F₀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J J', Good C.P.L.L z J → Good C.A.L z J' → sval (Φ F₀) p z J = (gw wA p z (J (p ≫ C.α)) (J' p) ^ (C.n ^ j)).val * sval (Φ₀ F₀) p z J') → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ c : F, c ≠ 0 ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J := by
  first | exact @GlobalTheory.Mum.fvalue_const | exact GlobalTheory.Mum.fvalue_const | (intros; apply GlobalTheory.Mum.fvalue_const <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabExtOfTrait

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}

theorem Trait.exists_lift {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W)
    (F : Type) [Field F] [Algebra (FractionRing W) F] (z : Sp F ⟶ C.G.left)
    (hz : z ≫ C.G.hom = jFK (R := W) F ≫ jK W ≫ T.ξ) :
    ∃ x : TFK (R := W) F ⟶ T.A.A, x.left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = z := by
  have w₁ : z ≫ C.G.hom = (jFK (R := W) F ≫ jK W) ≫ T.ξ := by rw [hz, Category.assoc]
  have w₂ : T.cart.1.lift z (jFK (R := W) F ≫ jK W) w₁ ≫ T.G.hom = jFK (R := W) F ≫ jK W :=
    T.cart.1.lift_snd _ _ _
  let g₂ : Sp F ⟶ pullback T.G.hom (jK W) := pullback.lift (T.cart.1.lift z (jFK (R := W) F ≫ jK W) w₁) (jFK (R := W) F) w₂
  have hs : T.U.gen.hom.left ≫ T.A.A.hom = pullback.snd T.G.hom (jK W) := Over.w T.U.gen.hom
  have hgi : T.U.gen.hom.left ≫ T.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  refine ⟨Over.homMk (g₂ ≫ T.U.gen.hom.left) (by
    show (g₂ ≫ T.U.gen.hom.left) ≫ T.A.A.hom = jFK (R := W) F
    rw [Category.assoc, hs]
    exact pullback.lift_snd _ _ _), ?_⟩
  show (g₂ ≫ T.U.gen.hom.left) ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = z
  rw [Category.assoc, reassoc_of% hgi, pullback.lift_fst_assoc]
  exact T.cart.1.lift_fst _ _ _

end GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull

theorem labExt_of_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], Nonempty (Trait C W) →
    ∀ σ : Kb R →ₐ[FractionRing R] Kb R, LabExt σ (C.lab j) (C.lab j) := by
  intro R _ _ _ hR D C j W _ _ _ ⟨T⟩ σ p q hpq
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  have hGF := hL.globalFns
  have := hR.2
  have hB := D.tau_bimult
  have hW := T.cdvr
  have := hW.1
  have := hW.2.2
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hk : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  letI : Algebra (FractionRing R) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp (fracMap T.inj)).toAlgebra
  have cF : Compat T.φ (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (fracMap_algebraMap T.inj r)
  obtain ⟨em⟩ := nonempty_lift (FractionRing R) (Kb W)
  obtain ⟨r, hr⟩ := exists_ext hB em q
  have hr' : QkExt (em.comp σ).toRingHom p r := qkExt_trans hpq hr
  have hr₁ := isPullGtF_pullGt T.hD hGF cF r.g

  have hgp : jFK (R := W) (Kb W) ≫ jK W ≫ T.ξ = jFK (R := R) (Kb W) ≫ C.gp := by
    let ρ : R →+* Kb W := (algebraMap (FractionRing W) (Kb W)).comp ((algebraMap W (FractionRing W)).comp T.φ)
    have hρ : Function.Injective ρ :=
      (algebraMap (FractionRing W) (Kb W)).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp T.inj)
    have hy : (jFK (R := W) (Kb W) ≫ jK W ≫ T.ξ) ≫ C.π = spMap ρ := by
      rw [Category.assoc, Category.assoc, T.ξ_π, spMap_comp, spMap_comp]
    obtain ⟨ga, hga, e⟩ := Modif.factor_gp R C.toModif (Kb W) ρ _ hρ hy
    have hga' : ga = algebraMap (FractionRing R) (Kb W) :=
      IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun s => (hga s).trans (cF s).symm)
    rw [e, hga']
  have hz : ∀ (τ : Kb R →ₐ[FractionRing R] Kb W) (x : TFK (R := R) (Kb R) ⟶ C.A.A),
      (spMap τ.toRingHom ≫ x.left ≫ C.α) ≫ C.G.hom = jFK (R := W) (Kb W) ≫ jK W ≫ T.ξ := by
    intro τ x
    rw [hgp, Category.assoc, Category.assoc, C.α_cart.1.w, ← Category.assoc x.left, Over.w x, ← Category.assoc]
    show (spMap τ.toRingHom ≫ spMap (algebraMap (FractionRing R) (Kb R))) ≫ C.gp = _
    rw [← spMap_comp]; exact congrArg (fun f => spMap f ≫ C.gp) τ.comp_algebraMap
  obtain ⟨x₁, hx₁⟩ := T.exists_lift (Kb W) _ (hz em (C.lab j q))
  obtain ⟨x₂, hx₂⟩ := T.exists_lift (Kb W) _ (hz (em.comp σ) (C.lab j p))
  have t₁ := T.lab (Kb W) em cF j q r (pullQk T.hD hGF cF hB T.D'.tau_bimult r) x₁ hr rfl hr₁ hx₁
  have t₂ := T.lab (Kb W) (em.comp σ) cF j p r (pullQk T.hD hGF cF hB T.D'.tau_bimult r) x₂ hr' rfl hr₁ hx₂
  have hGs : IsSemiAbelian T.G := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso T.cart (isGrpPullback_pullback C.G T.ξ)
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback T.ξ C.G C.semi)
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause W _ bW T.D' T.A T.G hGs T.U (Kb W) (C.n ^ j) hk
  have e : x₁ = x₂ := ((hf.1 _ _).1 t₁).trans ((hf.1 _ _).1 t₂).symm
  subst e
  have e' := hx₁.symm.trans hx₂
  haveI : Epi (spMap em.toRingHom) := Flat.epi_of_flat_of_surjective _
  refine (cancel_epi (spMap em.toRingHom)).1 (C.α_cart.1.hom_ext ?_ ?_)
  · rw [Category.assoc, Category.assoc, e', Category.assoc, ← Category.assoc (spMap em.toRingHom), ← spMap_comp]
    rfl
  · rw [Category.assoc, Over.w (C.lab j q), Category.assoc, Category.assoc, Over.w (C.lab j p)]
    exact congrArg (spMap em.toRingHom ≫ ·) ((spMap_comp _ _).symm.trans (congrArg spMap σ.comp_algebraMap)).symm

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionDescendsFromAlgClosedFieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.traitExpansion_descends_from_algClosed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k) (c : F), c ≠ 0 → (∀ F₀, ∃ σ : SecK C.P.L.L T.β k, T.ExpBy 1 σ F₀) → (∀ (F₀ : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F₀, T.Exp a b (Φ F₀) F₀ := by
  first | exact @GlobalTheory.Mum.TraitDescent.exp_of_values | exact GlobalTheory.Mum.TraitDescent.exp_of_values | (intros; apply GlobalTheory.Mum.TraitDescent.exp_of_values <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapThetaExpansionAllTraits

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_field_over_trait : ∀ (R : Type) [CommRing R] [IsDomain R] (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : Algebra (FractionRing R) F) (_ : Algebra (FractionRing W) F) (_ : Kb R →ₐ[FractionRing R] F), ∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (φ r)) := by
  intro R _ _ W _ _ φ hφ
  let g : R →+* Kb W := (algebraMap (FractionRing W) (Kb W)).comp ((algebraMap W (FractionRing W)).comp φ)
  have hg : Function.Injective g :=
    (algebraMap (FractionRing W) (Kb W)).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp hφ)
  letI : Algebra (FractionRing R) (Kb W) := (IsFractionRing.lift (K := FractionRing R) hg).toAlgebra
  refine ⟨Kb W, inferInstance, inferInstance, inferInstance, inferInstance, IsAlgClosed.lift, fun r => ?_⟩
  exact IsFractionRing.lift_algebraMap hg r

theorem exists_map_exp_all_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ), ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F := by
  intro R _ _ _ hR D C j
  have hodd : Odd (C.n ^ j) := C.n_odd.pow
  have h1 : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  obtain ⟨wA, hwA⟩ := C.α_lb
  have hL : C.P.L.L.IsLB := by first | exact C.P.L.isLB | exact C.P.L.hL | exact C.P.L.lb
  have hL' : C.A.L.IsLB := C.A.isLB
  by_cases hT : ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W), Nonempty (Trait C W)
  · obtain ⟨W₀, _, _, _, ⟨T₀⟩⟩ := hT
    obtain ⟨K₀, _, _, _, _, em₀, hK₀⟩ := exists_field_over_trait R W₀ T₀.φ T₀.inj
    obtain ⟨lab, E, hlab, hE, -⟩ := GlobalTheory.T.trait_inverse_expansion_equivariant_labels R hR D C j wA hwA W₀ T₀ K₀ em₀ hK₀
    obtain ⟨Eb, hEb⟩ := GlobalTheory.Mum.Desc.eqv_down R hR D C.A (C.n ^ j) hodd (C.lab j) K₀ em₀ lab E hlab hE
    have hgal := GlobalTheory.Mum.labExt_of_trait R hR D C j W₀ ⟨T₀⟩
    obtain ⟨Φ₀, E₀, hE₀, hΦ₀⟩ := GlobalTheory.Mum.exists_eqv_rational R hR D C.A (C.n ^ j) hodd (C.lab j) Eb hEb hgal
    choose Φ hΦ using fun F₀ => GlobalTheory.T.exists_lineBundlePowSection_transport_pullbackIso C.P.L.L C.A.L C.α wA hL hL' hwA (C.n ^ j) (Φ₀ F₀)
    refine ⟨Φ, fun W _ _ _ T => ?_⟩
    obtain ⟨K, _, _, _, _, em, hK⟩ := exists_field_over_trait R W T.φ T.inj
    obtain ⟨c, hc, hcv⟩ := GlobalTheory.T.integral_family_expansion_eq_const_mul_algClosure R hR D C j wA hwA E₀ Φ₀ hE₀ hΦ₀ Φ hΦ W T K em hK
    exact GlobalTheory.T.traitExpansion_descends_from_algClosed_field R hR D C (C.n ^ j) W T K hK Φ c hc (fun F₀ => GlobalTheory.T.exists_integralSection_expanding_thetaFamily R hR D C (C.n ^ j) h1 W T F₀) hcv
  · exact ⟨fun _ => ⟨fun _ => 0, fun _ _ => by simp⟩, fun W _ _ _ T => (hT ⟨W, _, _, _, ⟨T⟩⟩).elim⟩

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapThetaExpansionAllTraitsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_map_thetaExpansion_all_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ), ∃ Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j), ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F, T.Exp a b (Φ F) F := by
  first | exact @GlobalTheory.Mum.exists_map_exp_all_traits | exact GlobalTheory.Mum.exists_map_exp_all_traits | (intros; apply GlobalTheory.Mum.exists_map_exp_all_traits <;> assumption)
end
end
