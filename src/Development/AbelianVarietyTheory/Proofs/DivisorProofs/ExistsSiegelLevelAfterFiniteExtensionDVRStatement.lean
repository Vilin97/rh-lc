module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfSymplecticLevelPointsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelRootsFiniteExtCharZeroStatement
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueExtendPointAbelianSchemeDVR

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DVRExt

theorem exists_unique_extend : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (f : R →+* W) (x : Over.mk (spMap ((algebraMap W L).comp f)) ⟶ P.A), ∃! y : Over.mk (spMap f) ⟶ P.A, spMap (algebraMap W L) ≫ y.left = x.left := by
  intro R _ P W L _ _ _ _ _ _ f x
  haveI : ValuationRing W := inferInstance
  have hv : ValuativeCriterion P.A.hom := by
    have h : IsProper P.A.hom := P.isAb.proper
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hsq : x.left ≫ P.A.hom = spMap (algebraMap W L) ≫ spMap f := by
    rw [Over.w x]
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let S : ValuativeCommSq P.A.hom :=
    { R := W, K := L, i₁ := x.left, i₂ := spMap f, commSq := ⟨hsq⟩ }
  have hU := (hv S).some
  refine ⟨Over.homMk hU.default.l hU.default.fac_right, hU.default.fac_left, ?_⟩
  intro y hy
  have hy2 : y.left ≫ P.A.hom = spMap f := Over.w y
  let T : S.commSq.LiftStruct := ⟨y.left, hy, hy2⟩
  have hT : T = hU.default := hU.uniq T
  apply Over.OverMorphism.ext
  change T.l = hU.default.l
  rw [hT]

end GlobalTheory.DVRExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueExtendPointAbelianSchemeDVRStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_unique_extend_point_abelianScheme_DVR : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (f : R →+* W) (x : Over.mk (spMap ((algebraMap W L).comp f)) ⟶ P.A), ∃! y : Over.mk (spMap f) ⟶ P.A, spMap (algebraMap W L) ≫ y.left = x.left := by
  first | exact @GlobalTheory.DVRExt.exists_unique_extend | exact GlobalTheory.DVRExt.exists_unique_extend | (intros; apply GlobalTheory.DVRExt.exists_unique_extend <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqOfFractionFieldDomain

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilDomain

theorem appTop_spMap_inv {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (a : A) :
    (spMap g).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (g a) :=
  (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))).symm

theorem weilIs_of_fractionField : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) (W L : Type) [CommRing W] [IsDomain W] [Field L] [Algebra W L] [IsFractionRing W L] (f : R →+* W) (e : Over.mk (spMap ((algebraMap W L).comp f)) ⟶ Over.mk (spMap f)), e.left = spMap (algebraMap W L) → ∀ (n : ℕ) (x y : Over.mk (spMap f) ⟶ P.A), x ^ n = 1 → y ^ n = 1 → ∀ (w : Wˣ), Out.WeilIs P.A P.L n (e ≫ x) (e ≫ y) (unitOn (Units.map (algebraMap W L).toMonoidHom w)) → Out.WeilIs P.A P.L n x y (unitOn w) := by
  intro R _ _ P W L _ _ _ _ _ f e he n x y hx hy w H
  have hL := (GlobalTheory.firstFiveLaws).1
  obtain ⟨c, hc, -⟩ := (hL.weil _ P n (Over.mk (spMap f))).1 x y hx hy
  have H' := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB e hc
  have hu := CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB H' H
  have hinj : Function.Injective e.left.appTop.hom := by
    rw [he]
    intro a b hab
    have ia := CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of W)) a
    have ib := CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of W)) b
    rw [← ia, ← ib, appTop_spMap_inv, appTop_spMap_inv] at hab
    have h1 := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of L)).inv).1 hab
    have h2 := IsFractionRing.injective W L h1
    rw [← ia, ← ib, h2]
  have hc' : c = unitOn w := by
    apply Units.ext
    apply hinj
    have := congrArg Units.val hu
    refine this.trans ?_
    show (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom (algebraMap W L w) = _
    rw [he]
    exact (appTop_spMap_inv (algebraMap W L) (w : W)).symm
  exact hc' ▸ hc

end GlobalTheory.WeilDomain
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqOfFractionFieldDomainStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.weilPairing_eq_of_fractionField_domain : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) (W L : Type) [CommRing W] [IsDomain W] [Field L] [Algebra W L] [IsFractionRing W L] (f : R →+* W) (e : Over.mk (spMap ((algebraMap W L).comp f)) ⟶ Over.mk (spMap f)), e.left = spMap (algebraMap W L) → ∀ (n : ℕ) (x y : Over.mk (spMap f) ⟶ P.A), x ^ n = 1 → y ^ n = 1 → ∀ (w : Wˣ), Out.WeilIs P.A P.L n (e ≫ x) (e ≫ y) (unitOn (Units.map (algebraMap W L).toMonoidHom w)) → Out.WeilIs P.A P.L n x y (unitOn w) := by
  first | exact @GlobalTheory.WeilDomain.weilIs_of_fractionField | exact GlobalTheory.WeilDomain.weilIs_of_fractionField | (intros; apply GlobalTheory.WeilDomain.weilIs_of_fractionField <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelLevelAfterFiniteExtensionDVR

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelAfterExt

theorem exists_siegPre_divPoints : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f₁ : V →+* V₁) (s : SiegPre PB.g n (zetaAway n) (spMap (f₁.comp b))) (β₁ : s.A.left ⟶ PB.A.left) (β₁₂ : (G2 s.A).left ⟶ (G2 PB.A).left) (d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A)), IsCN V₁ ∧ IsDiscreteValuationRing V₁ ∧ Function.Injective f₁ ∧ f₁.Finite ∧ IsLocalHom f₁ ∧ s.Principal ∧ IsGrpPullback s.A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso s.P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ i, (d i ^ n).left ≫ β₁ = spMap f₁ ≫ (c (Pi.single i 1)).left := by
  intro n hn3 _ V _ _ _ hV _ b PB r c
  have hn0 : n ≠ 0 := by omega
  haveI := hV.2.2.1
  haveI := hV.2.2.2
  haveI : CharZero (FractionRing V) := charZero_of_injective_ringHom (IsFractionRing.injective V (FractionRing V))
  let ze : (cycAway n)ˣ := (GlobalTheory.LowChart.isUnit_zetaAway n hn3).unit
  let ζ : (FractionRing V)ˣ := Units.map ((algebraMap V (FractionRing V)).comp b).toMonoidHom ze
  have hζ : IsPrimitiveRoot ζ n :=
    IsPrimitiveRoot.coe_units_iff.1 (isPrimitiveRoot_map hn0 ((algebraMap V (FractionRing V)).comp b))
  obtain ⟨L, _, _, _, lev, d, hadd, htor, hweil, hd⟩ :=
    GlobalTheory.T.exists_symplecticLevel_roots_finite_ext_charZero V PB (FractionRing V) (algebraMap V (FractionRing V)) n (by omega) ζ hζ r (fun i => c (Pi.single i 1))
  obtain ⟨W, _, _, _, hcW, _, _, _, hcomp, hfin, hinj, hloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L
  generalize hT : (algebraMap (FractionRing V) L).comp (algebraMap V (FractionRing V)) = T at lev d hadd htor hweil hd
  have hT' : (algebraMap W L).comp (algebraMap V W) = T := hcomp.trans hT
  subst hT'
  let f₁ : V →+* W := algebraMap V W
  let e : Over.mk (spMap ((algebraMap W L).comp f₁)) ⟶ Over.mk (spMap f₁) :=
    Over.homMk (spMap (algebraMap W L)) (by show Spec.map _ ≫ Spec.map _ = Spec.map _; rw [← Spec.map_comp]; rfl)
  have hel : e.left = spMap (algebraMap W L) := rfl
  have uniq : ∀ y y' : Over.mk (spMap f₁) ⟶ PB.A, e ≫ y = e ≫ y' → y = y' := fun y y' h =>
    (GlobalTheory.T.exists_unique_extend_point_abelianScheme_DVR V PB W L f₁ (e ≫ y)).unique (rfl : spMap (algebraMap W L) ≫ y.left = (e ≫ y).left)
      (show spMap (algebraMap W L) ≫ y'.left = (e ≫ y).left by rw [h]; rfl)
  have lift : ∀ x : Over.mk (spMap ((algebraMap W L).comp f₁)) ⟶ PB.A, ∃ y, e ≫ y = x := fun x => by
    obtain ⟨y, hy, -⟩ := GlobalTheory.T.exists_unique_extend_point_abelianScheme_DVR V PB W L f₁ x
    exact ⟨y, Over.OverMorphism.ext hy⟩
  choose lev₁ hlev₁ using fun a => lift (lev a)
  choose d₁ hd₁ using fun i => lift (d i)
  have add₁ : ∀ x y, lev₁ (x + y) = lev₁ x * lev₁ y := fun x y =>
    uniq _ _ (by rw [MonObj.comp_mul, hlev₁, hlev₁, hlev₁, hadd])
  have tor₁ : ∀ x, lev₁ x ^ n = 1 := fun x =>
    uniq _ _ (by rw [MonObj.comp_pow, hlev₁, htor, MonObj.comp_one])
  have div₁ : ∀ i, d₁ i ^ n = toUnit _ ≫ c (Pi.single i 1) := fun i =>
    uniq _ _ (by rw [MonObj.comp_pow, hd₁, hd, ← Category.assoc, toUnit_unique (e ≫ toUnit _) (toUnit _)])
  have weil₁ : ∀ x y, Out.WeilIs PB.A PB.L n (lev₁ x) (lev₁ y)
      (unitOn (Units.map (f₁.comp b).toMonoidHom ze ^ omegaStd x y)) := fun x y => by
    refine GlobalTheory.T.weilPairing_eq_of_fractionField_domain V PB W L f₁ e hel n _ _ (tor₁ x) (tor₁ y) _ ?_
    rw [hlev₁, hlev₁, map_zpow]
    have hz : Units.map (algebraMap W L).toMonoidHom (Units.map (f₁.comp b).toMonoidHom ze) =
        Units.map (algebraMap (FractionRing V) L).toMonoidHom ζ := Units.ext (by
      show (algebraMap W L) (f₁ (b (zetaAway n))) = (algebraMap (FractionRing V) L) ((algebraMap V (FractionRing V)) (b (zetaAway n)))
      exact congrArg (fun q : V →+* L => q (b (zetaAway n))) hcomp)
    rw [hz]
    exact hweil x y
  obtain ⟨s, β₁, β₁₂, d', hP, hpb, hsq, hlb, hdd⟩ :=
    GlobalTheory.T.exists_siegelObject_of_symplecticLevel_points n hn3 V W f₁ b PB lev₁ r d₁ (fun i => c (Pi.single i 1)) add₁ tor₁ weil₁ div₁
  refine ⟨W, inferInstance, inferInstance, inferInstance, f₁, s, β₁, β₁₂, d',
    ⟨inferInstance, inferInstance, hcW, charZero_of_injective_ringHom hinj⟩, inferInstance, hinj,
    RingHom.finite_algebraMap.2 hfin, hloc, hP, hpb, hsq, hlb, hdd⟩

end GlobalTheory.LevelAfterExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelLevelAfterFiniteExtensionDVRStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_siegelLevel_after_finiteExtension_DVR : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f₁ : V →+* V₁) (s : SiegPre PB.g n (zetaAway n) (spMap (f₁.comp b))) (β₁ : s.A.left ⟶ PB.A.left) (β₁₂ : (G2 s.A).left ⟶ (G2 PB.A).left) (d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A)), IsCN V₁ ∧ IsDiscreteValuationRing V₁ ∧ Function.Injective f₁ ∧ f₁.Finite ∧ IsLocalHom f₁ ∧ s.Principal ∧ IsGrpPullback s.A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso s.P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ i, (d i ^ n).left ≫ β₁ = spMap f₁ ≫ (c (Pi.single i 1)).left := by
  first | exact @GlobalTheory.LevelAfterExt.exists_siegPre_divPoints | exact GlobalTheory.LevelAfterExt.exists_siegPre_divPoints | (intros; apply GlobalTheory.LevelAfterExt.exists_siegPre_divPoints <;> assumption)
end
end
