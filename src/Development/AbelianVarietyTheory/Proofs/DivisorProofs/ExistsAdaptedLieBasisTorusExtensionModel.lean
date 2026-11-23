module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPointsAddPullTangent
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisOfCompatibleTangentRelationStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingFrameUnitChangeToChart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisTorusExtensionOfLiftsAndDualsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentRelationAdditiveScaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorLiftsToDegenerationPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentPullbackComplexDualNumbersStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPointOfIffThick
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
import Mathlib.Algebra.Module.Torsion.Prod
import Mathlib.RingTheory.Etale.Weakly
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationTangentPointUniqueLift

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

section General

variable {R : Type} [CommRing R] (I : Ideal R)

theorem dualMap_mk_struct (e : ℕ) :
    spMap (algebraMap (R ⧸ I ^ (e + 1)) (DualNumber (R ⧸ I ^ (e + 1)))) ≫ thick R I e =
      spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ (epsR R).hom := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  refine congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun r => ?_)
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_factor_dualMap (e : ℕ) :
    ∃ l, l ≫ spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) =
      adicLevelι (I.map (algebraMap R (DualNumber R))) (e + 1) := by
  have hs : Function.Surjective (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) := fun x => by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.fst
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective x.snd
    refine ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, TrivSqZeroExt.ext ?_ ?_⟩ <;> simp [dualMap, ha, hb]
  have hk : RingHom.ker (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≤
      RingHom.ker (Ideal.Quotient.mk ((I.map (algebraMap R (DualNumber R))) ^ (e + 1))) := fun x hx => by
    rw [RingHom.mem_ker] at hx
    have h1 : x.fst ∈ I ^ (e + 1) := by
      have := congrArg TrivSqZeroExt.fst hx
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [dualMap] using this
    have h2 : x.snd ∈ I ^ (e + 1) := by
      have := congrArg TrivSqZeroExt.snd hx
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [dualMap] using this
    have ex : x = algebraMap R (DualNumber R) x.fst + algebraMap R (DualNumber R) x.snd * DualNumber.eps := by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [Ideal.mk_ker, ← Ideal.map_pow, ex]
    exact add_mem (Ideal.mem_map_of_mem _ h1) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h2))
  refine ⟨spMap (RingHom.liftOfSurjective _ hs ⟨_, hk⟩), ?_⟩
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.liftOfSurjective_comp]

variable {I} [IsDomain R] {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem tanRel_iff_isPointOf (y : epsR R ⟶ G) (gm : GtPt D.toPre (epsR R)) :
    TanRel U y gm ↔ FormalPoint.IsPointOf U gm y := by
  constructor
  · intro h
    refine (FormalPoint.isPointOf_iff_reduction U gm y).2 fun e => ?_
    obtain ⟨ye, h1, h2⟩ := h e
    obtain ⟨l, hl⟩ := exists_factor_dualMap I e
    have h3 : FormalPoint.HasCoords U e gm _ ye := h2
    have h4 := h3.comp l
    have h5 : FormalPoint.reduction I y e = l ≫ ye := by
      rw [← cancel_mono (fstG I e G).left, FormalPoint.reduction_fstG, Category.assoc, h1, ← hl]
      exact Category.assoc _ _ _
    rw [h5, ← hl]
    exact h4
  · intro h e
    obtain ⟨ye, hy⟩ := FormalPoint.exists_hasCoords U e gm _ _ (dualMap_mk_struct I e)
    exact ⟨ye, h.comp_fstG_eq hy, hy⟩

theorem isTangent_of_isPointOf [IsLocalRing R] [IsAdicComplete I R] {y : epsR R ⟶ G} {gm : GtPt D.toPre (epsR R)}
    (hg : GtTan gm) (h : FormalPoint.IsPointOf U gm y) : IsTangent y := by
  obtain ⟨o, ho, hp⟩ := hg
  let k : baseOver (Sp R) ⟶ epsR R := Over.homMk (redE R) (by
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h3 : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
      RingHom.ext fun r => (TrivSqZeroExt.fstHom R R R).commutes r
    rw [h3]
    exact Spec.map_id _)
  have h1 : k ≫ y = 1 := (FormalPoint.existsUnique_isPointOf_unit U o).unique (h.pull k hp)
    (FormalPoint.isPointOf_one U ho)
  refine (congrArg (·.left) h1).trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

end General

theorem existsUnique_tangent_of_gtTan : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ gm : GtPt D.toPre (epsR V), GtTan gm → ∃! y : epsR V ⟶ G, IsTangent y ∧ TanRel U.toUnifPre y gm := by
  intro V _ _ _ _ hV D A G _ _ _ U gm hg
  have : Module.Finite V (DualNumber V) := inferInstanceAs (Module.Finite V (V × V))
  have := isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal V) (DualNumber V)
  have : Nontrivial (DualNumber V) := (TrivSqZeroExt.inl_injective (R := V) (M := V)).nontrivial
  have : IsLocalRing (DualNumber V) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  obtain ⟨y, hy, hu⟩ := FormalPoint.existsUnique_isPointOf U.toUnifPre gm
  exact ⟨y, ⟨isTangent_of_isPointOf _ hg hy, (tanRel_iff_isPointOf _ _ _).2 hy⟩,
    fun y' h' => hu y' ((tanRel_iff_isPointOf _ _ _).1 h'.2)⟩

end GlobalTheory.MBLow

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusExtensionTangentOfAdditiveMap

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TorVec

theorem exists_torus_tangent : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (l : D.X →+ R), ∃ gm : GtPt D (epsR R), GtTan gm ∧ gm.b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  intro R _ _ D l
  obtain ⟨ν, hb, hv⟩ := GlobalTheory.TorusTangent.exists_pt (D := D) (T := epsR R)
    (fun x => GlobalTheory.TorusTangent.oneAdd (l x)) fun x y => by rw [map_add (f := _), GlobalTheory.TorusTangent.oneAdd_add]
  refine ⟨ν, ?_, hb, fun χ Z q z J hJ => ?_⟩
  · obtain ⟨g₀, h₀, v₀⟩ := GlobalTheory.TorusTangent.exists_pt (D := D) (T := baseOver (Sp R)) (fun _ => 1)
      fun _ _ => (_root_.mul_one _).symm
    refine ⟨g₀, ⟨h₀, fun x => corr_of_val D.P.isLB fun y J hJ => ?_⟩, ?_, fun x => corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · rw [v₀ x _ _ y J hJ, map_one, val_one]
    · rw [h₀, hb, GlobalTheory.TorusTangent.zeroT_left, GlobalTheory.TorusTangent.zeroT_left, ← Category.assoc]
      exact congrArg (· ≫ eSec D.P.A) GlobalTheory.TorusTangent.fst_inl.symm
    · refine (v₀ x _ _ y J hJ).trans (Units.ext (Eq.trans ?_
        (GlobalTheory.TorusTangent.hasVal_spMap (hv x) (TrivSqZeroExt.fstHom R R R).toRingHom hJ).symm))
      rw [GlobalTheory.TorusTangent.valR_oneAdd, map_one]
      simp
  · rw [hv χ Z q z J hJ, ← gs_unit q z ⊤ trivial]
    rfl

end GlobalTheory.MBLow.TorVec

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusExtensionTangentOfAdditiveMapStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_torusExtensionTangent_of_additiveMap : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (l : D.X →+ R), ∃ gm : GtPt D (epsR R), GtTan gm ∧ gm.b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  first | exact @GlobalTheory.MBLow.TorVec.exists_torus_tangent | exact GlobalTheory.MBLow.TorVec.exists_torus_tangent | (intros; apply GlobalTheory.MBLow.TorVec.exists_torus_tangent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisCardEqDimUniformisationDvr

section

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieRankUnif

theorem card_eq_g : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (IsLocalRing.maximalIdeal V) D A G) (n : ℕ) (y : Fin n → (epsR V ⟶ G)), IsLieBasis y → n = A.g := by
  intro V _ _ _ D A G _ _ U n y hy
  have := U.smooth
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  obtain ⟨φ, gp⟩ : ∃ φ : A.A.left ⟶ G.left, IsGrpPullback A.A G (jK V) φ :=
    ⟨_, ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK V))).congr (Category.id_comp _) rfl⟩
  obtain ⟨v, hv, -⟩ := GlobalTheory.exists_isLieBasis_baseChange V (FractionRing V) (algebraMap V _) G A.A φ gp U.smooth n y hy
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.KeyPow.exists_isLieBasis A.A A.smoothDim
  exact GlobalTheory.KeyFramePoint.card_eq_of_isLieBasis gp hv hv₀

end GlobalTheory.LieRankUnif
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBasisCardEqDimUniformisationDvrStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.lieBasis_card_eq_dim_uniformisation_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (IsLocalRing.maximalIdeal V) D A G) (n : ℕ) (y : Fin n → (epsR V ⟶ G)), IsLieBasis y → n = A.g := by
  first | exact @GlobalTheory.LieRankUnif.card_eq_g | exact GlobalTheory.LieRankUnif.card_eq_g | (intros; apply GlobalTheory.LieRankUnif.card_eq_g <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedLieBasisTorusExtensionModel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Adapt


theorem main : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∃ (vB : Fin D.toPre.P.g → (epsR V ⟶ D.toPre.P.A)) (r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin A.g ≃ Fin D.toPre.P.g ⊕ Fin r) (y : Fin A.g → (epsR V ⟶ G)) (gm₀ : Fin A.g → GtPt D.toPre (epsR V)) (gm : Fin A.g → GtPt D.toPre (TE V C)), IsLieBasis y ∧ Adapted ν vB bX σ gm ∧ ∀ j, TanRel U.toUnifPre (y j) (gm₀ j) ∧ GtTan (gm₀ j) ∧ GtPt.IsPull (spMap (dualMap (toF V C))) (gm₀ j) (gm j) := by
  intro V _ _ _ _ hV D A G _ _ hS U C _ _ _ _ _ _ hC N ν hν
  haveI := hV
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  obtain ⟨H, _, _, hH⟩ := GlobalTheory.TorusModel.exists_isGt hG (GlobalTheory.TorusModel.splitExt D.toPre)
  obtain ⟨Φ, hp, ha⟩ := GlobalTheory.TorusModel.exists_points hG hH
  have hΦ : GlobalTheory.TorusModel.Represents Φ := ⟨hp, ha⟩
  obtain ⟨vB, hvB⟩ := GlobalTheory.KeyPow.exists_isLieBasis D.toPre.P.A D.toPre.P.smoothDim
  let r := Module.finrank ℤ N.X
  let bX : Module.Basis (Fin r) ℤ N.X := Module.finBasis ℤ N.X
  let bD : Module.Basis (Fin r) ℤ D.toPre.X := bX.map ν.eX.toIntLinearEquiv
  choose lf hlf using fun i => (GlobalTheory.MBLow.GtVec.main V D.toPre).1 (vB i) (hvB.1 i)
  choose tv htv using fun l : Fin r => GlobalTheory.T.exists_torusExtensionTangent_of_additiveMap V D.toPre ((Int.castAddHom V).comp (bD.coord l).toAddMonoidHom)
  have hco : ∀ (l : Fin r) (χ : D.toPre.X), ((Int.castAddHom V).comp (bD.coord l).toAddMonoidHom) χ = ((bD.repr χ l : ℤ) : V) :=
    fun l χ => by simp [Module.Basis.coord_apply]
  let gm₀ : Fin D.toPre.P.g ⊕ Fin r → GtPt D.toPre (epsR V) := Sum.elim lf tv
  have hgt : ∀ j, GtTan (gm₀ j) := fun j => by
    cases j with
    | inl i => exact (hlf i).1
    | inr l => exact (htv l).1
  let x : Fin D.toPre.P.g ⊕ Fin r → (epsR V ⟶ H) := fun j => (Φ _).symm (gm₀ j)
  have hx : ∀ j, Φ _ (x j) = gm₀ j := fun j => Equiv.apply_symm_apply _ _
  have hxB : ∀ (n : ℕ) (σ : Fin n ≃ Fin D.toPre.P.g ⊕ Fin r), IsLieBasis (fun k => x (σ k)) := fun n σ =>
    GlobalTheory.T.lieBasis_torusExtension_of_lifts_and_duals V D.toPre H Φ hΦ r vB bD x hvB (fun j => by rw [hx]; exact hgt j) (fun i => by rw [hx]; exact (hlf i).2)
      (fun l => by
        rw [hx]
        refine ⟨(htv l).2.1, fun χ Z q z J hJ => ?_⟩
        rw [← hco]
        exact (htv l).2.2 χ Z q z J hJ) n σ
  have hz : ∀ T, (Φ T 1).IsZero := fun T => GlobalTheory.MBLow.GtVec.isZero_of_isAdd (by simpa using ha T 1 1)
  let red : baseOver (Sp V) ⟶ epsR V := Over.homMk (redE V) GlobalTheory.MBLow.GtVec.red_comp
  have tanG : ∀ w : epsR V ⟶ H, GtTan (Φ _ w) ↔ red ≫ w = 1 := fun w =>
    ⟨fun ⟨o, ho, h⟩ => (Φ _).injective ((GlobalTheory.TorusModel.isPull_unique (hp _ _ red w) h).trans
      (GlobalTheory.MBLow.GtVec.isZero_unique ho (hz _))), fun h => ⟨Φ _ 1, hz _, h ▸ hp _ _ red w⟩⟩
  have tanH : ∀ w : epsR V ⟶ H, IsTangent w ↔ red ≫ w = 1 := fun w => by
    constructor
    · intro h
      apply Over.OverMorphism.ext
      refine h.trans ?_
      show _ = (toUnit _ ≫ η[H]).left
      simp
    · intro h
      have := congrArg (·.left) h
      refine this.trans ?_
      show (toUnit _ ≫ η[H]).left = _
      simp
  have : Module.Finite V (DualNumber V) := inferInstanceAs (Module.Finite V (V × V))
  have : Module.Flat V (DualNumber V) := inferInstanceAs (Module.Flat V (V × V))
  have := isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal V) (DualNumber V)
  have := GlobalTheory.MBLow.TanLift.isLocalRing_dualNumber V
  have hT : GlobalTheory.AdicColimit.IsAdicColimit (IsLocalRing.maximalIdeal V) (epsR V) :=
    GlobalTheory.TorusModel.isAdicColimit_of_finite_flat (IsLocalRing.maximalIdeal V) (RingHom.id V) (by rwa [Ideal.map_id])
      (fun a ha => ⟨1, by rw [Ideal.map_id, pow_one]; exact ha⟩) (DualNumber V)
  let Rel : (epsR V ⟶ G) → (epsR V ⟶ H) → Prop := fun y w => TanRel U.toUnifPre y (Φ _ w)
  have h1 : Rel 1 1 := (tanRel_iff_isPointOf U.toUnifPre 1 (Φ _ 1)).2 (GlobalTheory.FormalPoint.isPointOf_one U.toUnifPre (hz _))
  have hmul : ∀ y y' w w', Rel y w → Rel y' w' → Rel (y * y') (w * w') := fun y y' w w' h h' =>
    GlobalTheory.MBLow.TanAdd.tanRel_mul U.toUnifPre y y' _ _ _ h h' (ha _ w w')
  have hsc : ∀ (c : V) (y : epsR V ⟶ G) (w : epsR V ⟶ H) (y' : epsR V ⟶ G) (w' : epsR V ⟶ H),
      y'.left = spMap (epsScaleR c) ≫ y.left → w'.left = spMap (epsScaleR c) ≫ w.left → Rel y w → Rel y' w' := by
    intro c y w y' w' e e' h
    obtain rfl : y' = GlobalTheory.SecJet.epsScale V c ≫ y := Over.OverMorphism.ext e
    obtain rfl : w' = GlobalTheory.SecJet.epsScale V c ≫ w := Over.OverMorphism.ext e'
    exact GlobalTheory.MBLow.TanAdd.tanRel_scale U.toUnifPre c y _ _ h (hp _ _ _ w)
  have hex : ∀ y, IsTangent y → ∃ w, IsTangent w ∧ Rel y w := fun y hy => by
    obtain ⟨gm, h₁, h₂, -⟩ := GlobalTheory.MBLow.TanLift.exists_tan U.toUnifPre y hy
    refine ⟨(Φ _).symm gm, (tanH _).2 ((tanG _).1 (by rw [Equiv.apply_symm_apply]; exact h₂)), ?_⟩
    show TanRel _ _ _
    rw [Equiv.apply_symm_apply]; exact h₁
  have huy : ∀ y y' w, IsTangent y → IsTangent y' → Rel y w → Rel y' w → y = y' := fun y y' w _ _ h h' =>
    ((tanRel_iff_isPointOf _ _ _).1 h).unique ((tanRel_iff_isPointOf _ _ _).1 h')
  have hux : ∀ y w w', Rel y w → Rel y w' → w = w' := fun y w w' h h' =>
    (GlobalTheory.TorusModel.existsUnique_lift U.toUnifPre hΦ hT y).unique ((tanRel_iff_isPointOf _ _ _).1 h)
      ((tanRel_iff_isPointOf _ _ _).1 h')
  choose yy hyy using fun j => (existsUnique_tangent_of_gtTan V hV D A G hS U (gm₀ j) (hgt j)).exists
  have hyB : ∀ (n : ℕ) (σ : Fin n ≃ Fin D.toPre.P.g ⊕ Fin r), IsLieBasis (fun k => yy (σ k)) := fun n σ =>
    GlobalTheory.T.isLieBasis_of_compatible_tangentRelation V G H Rel h1 hmul hsc hex huy hux n _ _ (hxB n σ) fun k => ⟨(hyy _).1, by
      show TanRel _ _ _
      rw [hx]; exact (hyy _).2⟩
  have hdim : D.toPre.P.g + r = A.g := GlobalTheory.T.lieBasis_card_eq_dim_uniformisation_dvr V D A G U.toUnifPre _ _ (hyB _ finSumFinEquiv.symm)
  let σ : Fin A.g ≃ Fin D.toPre.P.g ⊕ Fin r := (finCongr hdim.symm).trans finSumFinEquiv.symm
  choose gmC hgmC using fun j => GlobalTheory.T.torusExtensionTangent_pullback_complexDualNumbers V D.toPre C N ν (gm₀ j) (hgt j)
  refine ⟨vB, r, bX, σ, fun k => yy (σ k), fun k => gm₀ (σ k), fun k => gmC (σ k), hyB _ σ,
    ⟨hvB, fun j => (hgmC _).2.1, fun i => ?_, fun l => ?_⟩, fun k => ⟨(hyy _).2, hgt _, (hgmC _).1⟩⟩
  · dsimp only
    rw [σ.apply_symm_apply (Sum.inl i), (hgmC _).1.1]
    show _ ≫ (lf i).b.left = _
    rw [(hlf i).2]
  · dsimp only
    rw [σ.apply_symm_apply (Sum.inr l)]
    refine ⟨(hgmC _).2.2.1 (htv l).2.1, fun χ => ?_⟩
    refine ((hgmC _).2.2.2 (((bD.repr (ν.eX χ) l : ℤ) : V)) (ν.eX χ) fun Z q z J hJ => ?_).trans ?_
    · have hv := (htv l).2.2 (ν.eX χ) Z q z J hJ
      rw [hco] at hv
      exact hv
    · have e : bD.repr (ν.eX χ) l = bX.repr χ l := by
        show (bX.map ν.eX.toIntLinearEquiv).repr (ν.eX χ) l = _
        rw [Module.Basis.map_repr]
        simp
      rw [e, map_intCast]

end GlobalTheory.MBLow.Adapt

end
end
end
