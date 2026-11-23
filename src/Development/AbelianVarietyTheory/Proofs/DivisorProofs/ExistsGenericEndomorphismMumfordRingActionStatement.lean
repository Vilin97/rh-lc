module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndDataSymmAndOfOAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointEndomorphismsActionUniformisedThick
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OverExtOfPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordFormalEndomorphismAlgebraicStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointEndomorphismsActionUniformisedThickStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_adjointEndomorphisms_action_uniformisedThickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ b, FormalEnd U.toUnifPre a h' b := by
  first | exact @GlobalTheory.Mum.EndThick.formalEnd_exists | exact GlobalTheory.Mum.EndThick.formalEnd_exists | (intros; apply GlobalTheory.Mum.EndThick.formalEnd_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericOfFormal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.GenericEnd

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem eq_of_generic (U : UnifPre I D A G) {g g' : G ⟶ G}
    (h : (Over.pullback (jK R)).map g = (Over.pullback (jK R)).map g') : g = g' := by
  have := U.smooth
  have := U.separated
  have : IsSchemeTheoreticallyDominant (jK R) :=
    schDom_spec_map _ (IsFractionRing.injective R (FractionRing R))
  have : QuasiCompact (jK R) :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK R)) :=
    .of_isPullback (IsPullback.of_hasPullback G.hom (jK R)).flip
  ext1
  refine ext_of_schDom G.hom (by rw [Over.w g, Over.w g']) (pullback.fst G.hom (jK R)) ?_
  have e := congrArg (fun k => k.left ≫ pullback.fst G.hom (jK R)) h
  simp only [Over.pullback_map_left, pullback.lift_fst] at e
  exact e

theorem exists_generic_of_formal (U : UnifPre I D A G) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X)
    (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G) (hb : FormalEnd U a h' b) (g : G ⟶ G) (hg : IsMonHom g)
    (hgb : ∀ e, (Over.pullback (thick R I e)).map g = b e) :
    ∃ f : A.A ⟶ A.A, IsMonHom f ∧ ∀ g' : G ⟶ G, IsMonHom g' →
      (Over.pullback (jK R)).map g' ≫ U.gen.hom = U.gen.hom ≫ f → ActsAs U a h' g' := by
  have := U.gen_hom
  refine ⟨U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom, inferInstance, fun g' _ hg' => ?_⟩
  obtain rfl : g' = g := eq_of_generic U (by
    rw [← cancel_mono U.gen.hom, hg', Iso.hom_inv_id_assoc])
  intro e
  obtain ⟨t, ht, hi⟩ := hb.2.2.2 e
  exact ⟨by rw [hgb]; exact hb.2.2.1 e, t, ht, by rw [hgb]; exact hi⟩

end GlobalTheory.Mum.GenericEnd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericEndomorphismMumfordRingAction

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.GenericEnd.main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O), ∃ f : A.A ⟶ A.A, IsMonHom f ∧ ∀ g : G ⟶ G, IsMonHom g → (Over.pullback (jK R)).map g ≫ U.gen.hom = U.gen.hom ≫ f → ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g := by
  intro R _ _ _ hB D A G _ _ hG U O _ _ _ o a
  have hE := (GlobalTheory.Mum.endData_symm_and_ofOAct R D.toPre).2 O o a
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_adjointEndomorphisms_action_uniformisedThickenings R hB.1 D A G hG U _ _ _ _ hE
  obtain ⟨g, hg, hgb⟩ := GlobalTheory.T.mumford_formalEndomorphism_algebraic R hB D A G hG U _ _ _ _ hE b hb
  obtain ⟨f, hf, hact⟩ := GlobalTheory.Mum.GenericEnd.exists_generic_of_formal U.toUnifPre (o.onB.act a)
    (DistribSMul.toAddMonoidHom D.toPre.X (star a)) b hb g hg hgb
  have hfun : (⇑(DistribSMul.toAddMonoidHom D.toPre.X (star a)) : D.toPre.X → D.toPre.X) = fun χ => star a • χ :=
    funext fun χ => DistribSMul.toAddMonoidHom_apply _ _ χ
  rw [hfun] at hact
  exact ⟨f, hf, hact⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericEndomorphismMumfordRingActionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_genericEndomorphism_mumford_ringAction : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O), ∃ f : A.A ⟶ A.A, IsMonHom f ∧ ∀ g : G ⟶ G, IsMonHom g → (Over.pullback (jK R)).map g ≫ U.gen.hom = U.gen.hom ≫ f → ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g := by
  first | exact @GlobalTheory.Mum.GenericEnd.main | exact GlobalTheory.Mum.GenericEnd.main | (intros; apply GlobalTheory.Mum.GenericEnd.main <;> assumption)
end
end
