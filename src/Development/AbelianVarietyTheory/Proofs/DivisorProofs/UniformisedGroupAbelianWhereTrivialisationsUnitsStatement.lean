module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointMemAbelianLocusOfFixedTorsionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointsFirstCoordinateUnramifiedSubringStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UwRQeIsNsmul
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairsFixedOverUnramifiedExtensionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFixedOfQuotientClassesFixed

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TorsFixed

theorem fixed_of_classes_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] (φ : R →+* V) [Algebra (FractionRing R) (AlgebraicClosure (FractionRing V))], (∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r))) → ∀ k : ℕ, 1 ≤ k → ∀ σ : (AlgebraicClosure (FractionRing V)) ≃+* (AlgebraicClosure (FractionRing V)), (∀ v : V, σ (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) → (∀ p q : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, QkExt σ.toRingHom p q → QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing V)) p q) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ k = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro R _ _ _ hB D A G _ _ hG U V _ _ φ _ hc k hk σ hσ hQ x hx
  haveI : CharZero R := hB.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws

  have sq : (jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V) ≫ spMap φ =
      jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R := by
    show (spMap _ ≫ spMap _) ≫ spMap φ = spMap _ ≫ spMap _
    rw [← spMap_comp, ← spMap_comp, ← spMap_comp]
    congr 1
    ext r
    exact (hc r).symm
  have wx : x.left ≫ pullback.snd G.hom (spMap φ) = jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V := Over.w x
  have w₁ : (x.left ≫ pullback.fst G.hom (spMap φ)) ≫ G.hom = jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, wx, sq]
  let xG : Over.mk (jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R) ⟶ G :=
    Over.homMk (x.left ≫ pullback.fst G.hom (spMap φ)) w₁
  have hxG : xG ^ k = 1 :=
    (GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull sq (isGrpPullback_pullback G (spMap φ)) (x := xG) (x' := x) rfl).1 hx

  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gp : IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  let x₀ : TFK (R := R) (AlgebraicClosure (FractionRing V)) ⟶ A.A :=
    Over.homMk (gp.1.lift (x.left ≫ pullback.fst G.hom (spMap φ)) (jFK (R := R) (AlgebraicClosure (FractionRing V))) w₁)
      (gp.1.lift_snd _ _ _)
  have e₀ : x₀.left ≫ (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) = x.left ≫ pullback.fst G.hom (spMap φ) :=
    gp.1.lift_fst _ _ _
  have hx₀ : x₀ ^ k = 1 := (GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull rfl gp (x := xG) (x' := x₀) e₀).2 hxG

  have hσR : ∀ r : R, σ (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r)) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) := fun r => by
    rw [hc r, hσ]
  let σ' : AlgebraicClosure (FractionRing V) →ₐ[FractionRing R] AlgebraicClosure (FractionRing V) :=
    ⟨σ.toRingHom, fun a => RingHom.congr_fun
      (IsLocalization.ringHom_ext (nonZeroDivisors R)
        (j := σ.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))))
        (k := algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))) (RingHom.ext hσR)) a⟩
  have hσf : σ.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) := RingHom.ext σ'.commutes

  obtain ⟨f, hf, hsurj, hfi, -, -⟩ :=
    GlobalTheory.TorsionIso.torsion_eq hL R (maximalIdeal R) hB.1 D A G hG U (AlgebraicClosure (FractionRing V)) k hk
  obtain ⟨p, hp⟩ := hsurj x₀ hx₀
  obtain ⟨q, hpq⟩ := qkExtExists R D.toPre (AlgebraicClosure (FractionRing V))
    (AlgebraicClosure (FractionRing V)) σ.toRingHom σ'.commutes k p
  have heq : f q = x₀ := ((hfi p q).2 (hQ p q hpq)).symm.trans hp
  have s₂ : spMap σ.toRingHom ≫ jFK (R := R) (AlgebraicClosure (FractionRing V)) =
      jFK (R := R) (AlgebraicClosure (FractionRing V)) := by
    refine (spMap_comp _ _).symm.trans ?_
    exact congrArg spMap hσf
  have wx₀ : x₀.left ≫ A.A.hom = jFK (R := R) (AlgebraicClosure (FractionRing V)) := Over.w x₀
  let x' : TFK (R := R) (AlgebraicClosure (FractionRing V)) ⟶ A.A :=
    Over.homMk (spMap σ.toRingHom ≫ x₀.left) (by rw [Category.assoc, wx₀, s₂]; rfl)
  have hq : QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) k q x' :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt hL R (maximalIdeal R) hB.1 D A G hG U (AlgebraicClosure (FractionRing V))
      (AlgebraicClosure (FractionRing V)) σ' k hk p q x₀ x' hpq rfl).1 ((hf p x₀).2 hp.symm)
  have fix : spMap σ.toRingHom ≫ x₀.left = x₀.left := congrArg (fun z => z.left) (((hf q x').1 hq).trans heq)

  have sV : spMap σ.toRingHom ≫ jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V =
      jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V := by
    show spMap _ ≫ spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [← spMap_comp, ← spMap_comp]
    congr 1
    ext v
    exact hσ v
  refine pullback.hom_ext (f := G.hom) (g := spMap φ) ?_ ?_
  · rw [Category.assoc, ← e₀, ← Category.assoc, fix]
  · rw [Category.assoc, wx, sV]

end GlobalTheory.Mum.TorsFixed
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFixedOfQuotientClassesFixedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torsion_fixed_of_quotientClasses_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] (φ : R →+* V) [Algebra (FractionRing R) (AlgebraicClosure (FractionRing V))], (∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r))) → ∀ k : ℕ, 1 ≤ k → ∀ σ : (AlgebraicClosure (FractionRing V)) ≃+* (AlgebraicClosure (FractionRing V)), (∀ v : V, σ (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) → (∀ p q : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, QkExt σ.toRingHom p q → QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing V)) p q) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ k = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  first | exact @GlobalTheory.Mum.TorsFixed.fixed_of_classes_fixed | exact GlobalTheory.Mum.TorsFixed.fixed_of_classes_fixed | (intros; apply GlobalTheory.Mum.TorsFixed.fixed_of_classes_fixed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFixedUnramifiedCompleteTrait

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.UnramTorsPull

theorem torsion_fixed_unramified : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → spMap φ (closedPoint V) ∈ W → ∀ n : ℕ, 2 ≤ n → IsUnit (n : V) → ∀ j : ℕ, ∃ (T' : Subring (AlgebraicClosure (FractionRing V))) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v : V, (f v : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ σ : AlgebraicClosure (FractionRing V) ≃+* AlgebraicClosure (FractionRing V), (∀ z ∈ T', σ z = z) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro R _ _ _ hR D A G _ _ hG U W hW V _ _ _ φ hV hφ hcl n hn hnu j
  obtain ⟨hdvr, -, -⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  letI : Algebra (FractionRing R) (AlgebraicClosure (FractionRing V)) :=
    ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (IsLocalization.map (FractionRing V) φ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφ) :
        FractionRing R →+* FractionRing V)).toAlgebra
  have hc : ∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) =
      algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r)) := fun r => by
    show algebraMap (FractionRing V) _ (IsLocalization.map _ _ _ (algebraMap R _ r)) = _
    rw [IsLocalization.map_eq]
  have hk : IsUnit ((n ^ j : ℕ) : V) := by rw [Nat.cast_pow]; exact hnu.pow j
  obtain ⟨T₁, h₁, hb⟩ := GlobalTheory.T.quotientPoints_firstCoordinate_unramified_subring R D.toPre V φ hV hc (n ^ j) hk
  obtain ⟨T', h₂, hQ⟩ := GlobalTheory.T.torsionPairs_fixed_over_unramified_extension R hR D W hW V φ hV hφ hcl hc (n ^ j) hk T₁ h₁ hb
  have hT := h₁.trans h₂
  have hmem := hT.mem
  obtain ⟨hdvr', f, hf, hirr⟩ := hT
  refine ⟨T', hdvr', f, hf, hirr, fun σ hσ x hx => ?_⟩
  exact GlobalTheory.T.torsion_fixed_of_quotientClasses_fixed R hR D A G hG U V φ hc (n ^ j) (Nat.one_le_pow _ _ (by omega)) σ (fun v => hσ _ (hmem v)) (hQ σ hσ) x hx

end GlobalTheory.UnramTorsPull
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFixedUnramifiedCompleteTraitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.torsion_fixed_unramified_complete_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → spMap φ (closedPoint V) ∈ W → ∀ n : ℕ, 2 ≤ n → IsUnit (n : V) → ∀ j : ℕ, ∃ (T' : Subring (AlgebraicClosure (FractionRing V))) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v : V, (f v : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ σ : AlgebraicClosure (FractionRing V) ≃+* AlgebraicClosure (FractionRing V), (∀ z ∈ T', σ z = z) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  first | exact @GlobalTheory.UnramTorsPull.torsion_fixed_unramified | exact GlobalTheory.UnramTorsPull.torsion_fixed_unramified | (intros; apply GlobalTheory.UnramTorsPull.torsion_fixed_unramified <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupAbelianWhereTrivialisationsUnits

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.PsiUnitAb

theorem subset_abLocus_of_psiUnitOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → (W : Set (Sp R)) ⊆ abLocus G := by
  have hI1 := @GlobalTheory.T.torsion_fixed_unramified_complete_trait
  have hI2 := @GlobalTheory.T.closedPoint_mem_abelianLocus_of_fixedTorsion
  intro R _ _ _ hR D A G _ _ hG U W hW x hx
  have := hR.1.1
  have := hR.2
  obtain ⟨n, hn, hu⟩ : ∃ n : ℕ, 2 ≤ n ∧ IsUnit (n : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by exact_mod_cast h⟩
    · exact ⟨2, le_rfl, by exact_mod_cast (IsUnit.neg_iff _).1 h⟩
  have := x.isPrime
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R x.asIdeal
  have hcx : spMap φ (closedPoint V) = x := PrimeSpectrum.ext hc
  have huV : IsUnit (n : V) := by simpa using hu.map φ
  have h1 := hI1 R hR D A G hG U W hW V φ hV hφ (hcx ▸ hx) n hn huV
  have h2 := hI2 R hR D A G hG U V φ hV hφ n hn huV h1
  have key := abLocus_pullback (G' := (Over.pullback (spMap φ)).obj G) abLocusOne hG (isGrpPullback_pullback G (spMap φ)).1 (closedPoint V)
  rw [← hcx]
  exact key.2 h2

end GlobalTheory.Mum.PsiUnitAb
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupAbelianWhereTrivialisationsUnitsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformised_group_abelian_where_trivialisations_units : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → (W : Set (Sp R)) ⊆ abLocus G := by
  first | exact @GlobalTheory.Mum.PsiUnitAb.subset_abLocus_of_psiUnitOn | exact GlobalTheory.Mum.PsiUnitAb.subset_abLocus_of_psiUnitOn | (intros; apply GlobalTheory.Mum.PsiUnitAb.subset_abLocus_of_psiUnitOn <;> assumption)
end
end
