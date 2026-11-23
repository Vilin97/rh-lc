module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleMapOfSameUniformisedCoordsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModuliObjectSpreadNormalDomainStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QkPointGaloisFixedUpToEquivDividedData
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GaloisHolds
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperRelAmpleKTrivOfTrivialisationsGenerateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnBasicOpenOfComesFromBaseStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAbelianLocusToroidalChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelQuotientRepresentsReduced

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QkPointGaloisFixedUpToEquivDividedDataStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.qkPoint_galois_fixed_up_to_equiv_divided_data : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p p' : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M'), QkExt σ.toAlgHom.toRingHom p p' → QkPt.Equiv P.D.toPre (AlgebraicClosure (FractionRing R)) p p' := by
  first | exact @GlobalTheory.DivGalFix.qkExt_equiv_of_divFrom | exact GlobalTheory.DivGalFix.qkExt_equiv_of_divFrom | (intros; apply GlobalTheory.DivGalFix.qkExt_equiv_of_divFrom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreTorsionRationalOfBase

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

theorem torsRat_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → GlobalTheory.TChart.TorsRat t.G l.M' := by
  intro E _ _ _ H D' l c L R _ _ _ hR t P iw I _ s ε e hε hs hD
  haveI : CharZero R := hR.2
  have hadm : AdmBase R (maximalIdeal R) := hR.1
  have hn : 1 ≤ l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  haveI := P.U.gen_hom
  refine GlobalTheory.TorsDescent.torsRat_of_retract_galoisFixed t.G t.G P.A P.U.gen (𝟙 _) (𝟙 _) l.M' P.U.gen_hom
    inferInstance inferInstance (Category.comp_id _) hn ?_
  intro σ x hx
  obtain ⟨y, hy0⟩ : ∃ y : (Over.map (jK R)).obj (TFK (R := R) (AlgebraicClosure (FractionRing R))) ⟶ t.G, y = x := ⟨_, rfl⟩
  obtain ⟨h, hh0⟩ : ∃ h : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ (Over.pullback (jK R)).obj t.G,
    h = (Over.mapPullbackAdj (jK R)).unit.app _ ≫ (Over.pullback (jK R)).map y := ⟨_, rfl⟩
  have hy : y ^ l.M' = 1 := by rw [hy0]; exact hx
  have hmp : ∀ m : ℕ, (Over.pullback (jK R)).map (y ^ m) = ((Over.pullback (jK R)).map y) ^ m := by
    intro m
    induction m with
    | zero => simp [Functor.map_one]
    | succ m ih => rw [pow_succ, Functor.map_mul, ih, pow_succ]
  have hh : h ^ l.M' = 1 := by
    rw [hh0, ← MonObj.comp_pow, ← hmp, hy, Functor.map_one, MonObj.comp_one]
  obtain ⟨a, ha0⟩ : ∃ a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ P.A.A, a = h ≫ P.U.gen.hom := ⟨_, rfl⟩
  have ha : a ^ l.M' = 1 := by
    rw [ha0, ← MonObj.pow_comp, hh, MonObj.one_comp]
  obtain ⟨f, hT, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hadm P.D P.A t.G t.semi P.U
    (AlgebraicClosure (FractionRing R)) l.M' hn
  obtain ⟨p, hp⟩ := hT.2.1 a ha
  obtain ⟨⟨p', hext⟩, hpt, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hadm P.D P.A t.G t.semi P.U
    (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing R)) σ.toAlgHom l.M' hn p
  obtain ⟨a', ha'⟩ := hpt a
  have h2 := (hiff p' a a' hext ha').1 ((hT.1 p a).2 hp.symm)
  have heq := GlobalTheory.T.qkPoint_galois_fixed_up_to_equiv_divided_data L R hR t P iw s ε e hε hs hD σ p p' hext
  have haa : a' = a := ((hT.1 p' a').1 h2).trans (((hT.2.2.1 p p').2 heq).symm.trans hp)
  rw [haa] at ha'
  have e1 : (Over.mapPullbackAdj (jK R)).homEquiv _ _ y = h := by rw [Adjunction.homEquiv_unit, hh0]
  have hyl : y.left = h.left ≫ ((Over.mapPullbackAdj (jK R)).counit.app t.G).left := by
    have e2 : y = (Over.map (jK R)).map h ≫ (Over.mapPullbackAdj (jK R)).counit.app t.G := by
      conv_lhs => rw [← ((Over.mapPullbackAdj (jK R)).homEquiv _ _).symm_apply_apply y, e1]
      exact Adjunction.homEquiv_counit _ _ _ _
    rw [e2, Over.comp_left]
    rfl
  have hhl : spMap σ.toAlgHom.toRingHom ≫ h.left = h.left := by
    have := congrArg (· ≫ P.U.gen.inv.left) ha'
    simp only [ha0, Over.comp_left, Category.assoc] at this
    rw [← Over.comp_left _ _ _ P.U.gen.hom P.U.gen.inv, Iso.hom_inv_id, Over.id_left, Category.comp_id] at this
    exact this.symm
  have hyx : spMap σ.toAlgHom.toRingHom ≫ y.left = y.left := by
    rw [hyl, ← Category.assoc, hhl]
  rw [hy0] at hyx
  simpa using hyx

end GlobalTheory.UCanon
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreTorsionRationalOfBaseStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.genericFibre_torsion_rational_of_base : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → GlobalTheory.TChart.TorsRat t.G l.M' := by
  first | exact @GlobalTheory.UCanon.torsRat_of_divFrom | exact GlobalTheory.UCanon.torsRat_of_divFrom | (intros; apply GlobalTheory.UCanon.torsRat_of_divFrom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsRatAwayIff

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorsAway

theorem torsRat_away_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (f : R) [IsDomain (Localization.Away f)] (G : Over (Sp R))
    [GrpObj G] (G' : Over (Sp (Localization.Away f))) [GrpObj G'] (π : G'.left ⟶ G.left),
    IsGrpPullback G' G (spMap (algebraMap R (Localization.Away f))) π → ∀ n : ℕ,
      GlobalTheory.TChart.TorsRat G n ↔ GlobalTheory.TChart.TorsRat G' n := by
  intro R _ _ f _ G _ G' _ π hπ n
  have hf : f ≠ 0 := by
    rintro rfl
    have : Subsingleton (Localization.Away (0 : R)) :=
      IsLocalization.subsingleton (M := Submonoid.powers (0 : R)) ⟨1, pow_one _⟩
    exact not_subsingleton (Localization.Away (0 : R)) this
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have hinj : Function.Injective (algebraMap R (Localization.Away f)) := IsLocalization.injective _ hle
  constructor
  · exact GlobalTheory.TChart.AbLevel.torsRat_of_isGrpPullback _ hinj hπ
  · intro h K _ _ κ x hx
    letI : Algebra (Localization.Away f) (FractionRing R) :=
      IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.Away f) (FractionRing R) _ _ hle
    haveI : IsScalarTower R (Localization.Away f) (FractionRing R) :=
      IsLocalization.localization_isScalarTower_of_submonoid_le (Localization.Away f) (FractionRing R) _ _ hle
    haveI : IsFractionRing (Localization.Away f) (FractionRing R) :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) (Localization.Away f)
        (FractionRing R)
    let e := FractionRing.algEquiv (Localization.Away f) (FractionRing R)
    let j : FractionRing (Localization.Away f) →+* FractionRing R := e.toAlgHom.toRingHom
    have hj : ∀ r : R, j (algebraMap _ (FractionRing (Localization.Away f)) (algebraMap R (Localization.Away f) r)) =
        algebraMap R (FractionRing R) r := by
      intro r
      exact (e.commutes _).trans (IsScalarTower.algebraMap_apply R (Localization.Away f) (FractionRing R) r).symm
    have hsq : spMap j ≫ jK (Localization.Away f) ≫ spMap (algebraMap R (Localization.Away f)) = jK R := by
      show spMap j ≫ spMap (algebraMap _ (FractionRing (Localization.Away f))) ≫ spMap (algebraMap R (Localization.Away f)) =
        spMap (algebraMap R (FractionRing R))
      rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
      exact congrArg spMap (RingHom.ext hj)
    let T : Over (Sp (Localization.Away f)) := Over.mk (spMap (κ.comp j) ≫ jK (Localization.Away f))
    have hT : T.hom ≫ spMap (algebraMap R (Localization.Away f)) = spMap κ ≫ jK R := by
      show (spMap (κ.comp j) ≫ jK (Localization.Away f)) ≫ spMap (algebraMap R (Localization.Away f)) = _
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc, Category.assoc, hsq]
    let e0 : Over.mk (T.hom ≫ spMap (algebraMap R (Localization.Away f))) ⟶ Over.mk (spMap κ ≫ jK R) :=
      Over.homMk (𝟙 _) ((Category.id_comp _).trans hT.symm)
    let x' := (GlobalTheory.ObjPull.pushEquiv hπ T).symm (e0 ≫ x)
    have hx' : x' ^ n = 1 := by
      simp only [x']
      rw [← map_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, map_one]
    obtain ⟨y, hy⟩ := h K (κ.comp j) x' hx'
    have hyw : y.left ≫ G'.hom = jK (Localization.Away f) := Over.w y
    refine ⟨Over.homMk (spMap j ≫ y.left ≫ π) ?_, ?_⟩
    · show (spMap j ≫ y.left ≫ π) ≫ G.hom = jK R
      rw [Category.assoc, Category.assoc, hπ.1.w, ← Category.assoc y.left, hyw]
      exact hsq
    · show x.left = spMap κ ≫ spMap j ≫ y.left ≫ π
      have h1 : x'.left ≫ π = x.left :=
        (GlobalTheory.ObjPull.pushEquiv_symm_left hπ T (e0 ≫ x)).trans (Category.id_comp _)
      rw [← h1, hy, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
      simp only [Category.assoc]

end GlobalTheory.TorsAway
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifiedOnOpenOfSpecialisesToClassified

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ClsOpen

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.ClsOpen


open GlobalTheory.ClsOpen in
theorem GlobalTheory.clsOpen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (D' : Datum H) (L : LowBase D' c) (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (C : Fam Xo c V) (t₁ : SAB H (Sp R)) (P₁ : PELUnif (maximalIdeal R) t₁) (iw : L.W →+* R) (θ : R →+* V), IsLocalHom θ → θ.comp (iw.comp L.b) = C.b → ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → R) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ L.D.X) (e₁ : P₁.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ i, θ (s (.inl i)) ≠ 0) → (∀ j, IsUnit (s (.inr j))) → DivFrom L P₁.D.toPre P₁.oD iw s ε e₁ → DivFrom L C.P.D.toPre C.P.oD (θ.comp iw) (fun k => θ (s k)) ε e → ∃ (y₁ : Sp (FractionRing R) ⟶ Xo.XF c) (yo : Sp (Localization.Away (∏ i, s (.inl i))) ⟶ Xo.XF c) (κ : Sp (FractionRing V) ⟶ Sp (Localization.Away (∏ i, s (.inl i)))), y₁ ≫ pullback.snd _ _ = jK R ≫ spMap (iw.comp L.b) ∧ GlobalTheory.UPoinc.GenOf Xo c y₁ t₁ ∧ (∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away (∏ i, s (.inl i))), g ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK R → g ≫ yo = y₁) ∧ κ ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK V ≫ spMap θ ∧ κ ≫ yo = C.y := by
  intro E _ _ _ H Dw l Xo c φ D' L R V _ _ _ _ _ _ hR hV C t₁ P₁ iw θ hθ hb m N s ε e₁ e hε hs hu hD₁ hD
  set f : R := ∏ i, s (.inl i) with hf_def
  have hθf : θ f ≠ 0 := by rw [hf_def, map_prod]; exact Finset.prod_ne_zero_iff.2 fun i _ => hs i
  have hf0 : f ≠ 0 := fun h => hθf (by rw [h, map_zero])
  have hsk : ∀ k, s k ≠ 0 := by
    rintro (i | j)
    · exact fun h => hs i (by rw [h, map_zero])
    · exact (hu j).ne_zero
  have hθk : ∀ k, θ (s k) ≠ 0 := by
    rintro (i | j)
    · exact hs i
    · exact ((hu j).map θ).ne_zero
  let A := Localization.Away f
  have hpow : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI : IsDomain A := IsLocalization.isDomain_localization hpow
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing (Submonoid.powers f) A hR.1.1
  haveI : IsIntegrallyClosed R := hR.1.2.2.1
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A (Submonoid.powers f) hpow
  have hψ := GlobalTheory.T.psiUnitOn_basicOpen_of_comesFromBase L P₁.D.toPre P₁.oD iw s ε e₁ hD₁ f (by
    rintro (i | j)
    · exact ⟨1, by rw [pow_one, hf_def]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)⟩
    · exact ⟨0, (hu j).dvd⟩)
  obtain ⟨tO, ⟨mO⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap (algebraMap R A)) t₁
  obtain ⟨hpr, ham, hkt⟩ := GlobalTheory.T.isProper_relAmple_kTriv_of_trivialisations_generate R hR t₁ P₁ f hψ tO mO
  have htors : GlobalTheory.TChart.TorsRat tO.G l.M' :=
    (GlobalTheory.TorsAway.torsRat_away_iff R f t₁.G tO.G mO.φ mO.cart l.M').1 (GlobalTheory.T.genericFibre_torsion_rational_of_base L R hR t₁ P₁ iw s ε e₁ hε hsk hD₁)
  let K := FractionRing V
  have hunitK : IsUnit (((algebraMap V K).comp θ) f) := by
    rw [RingHom.comp_apply]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hθf)
  let g : A →+* K := IsLocalization.Away.lift f hunitK
  have hg : g.comp (algebraMap R A) = (algebraMap V K).comp θ := IsLocalization.lift_comp _
  let bA : c.F →+* A := (algebraMap R A).comp (iw.comp L.b)
  let incl := (IntermediateField.inclusion c.le).toRingHom
  have hgb : g.comp bA = (algebraMap V K).comp C.b := by
    show g.comp ((algebraMap R A).comp (iw.comp L.b)) = _
    rw [← RingHom.comp_assoc, hg, RingHom.comp_assoc, hb]
  have E1 : spMap g ≫ spMap (algebraMap R A) = jK V ≫ spMap θ :=
    (spMap_comp' _ _).symm.trans ((congrArg spMap hg).trans (spMap_comp' _ _))
  obtain ⟨oK, ⟨mK⟩⟩ := GlobalTheory.LevelQuotRep.obj_pull_same Xo.univ (C.y ≫ pullback.fst _ _)
  have hsK : (C.y ≫ pullback.fst _ _) ≫ Xo.s = spMap g ≫ spMap (bA.comp incl) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, C.y_over, spMap_comp' incl bA, ← Category.assoc,
      ← spMap_comp' bA g, hgb, spMap_comp']
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := (genOf_iff Xo c C.y C.t).1 C.gen
  obtain ⟨bc⟩ := GlobalTheory.T.exists_tripleMap_of_same_uniformised_coords L R V hR hV t₁ P₁ C.t C.P iw θ hθ s ε e₁ e hθk hD₁ hD
  obtain ⟨n₁⟩ := GlobalTheory.TraitOrder.cancel (Category.id_comp _) m₂ mK.toSABMap
  obtain ⟨n₂⟩ := GlobalTheory.TraitOrder.comp rfl bc m₁
  obtain ⟨n₃⟩ := GlobalTheory.TraitOrder.comp (Category.id_comp _) n₂ n₁
  obtain ⟨n₄⟩ := GlobalTheory.TraitOrder.cancel E1 mO n₃
  obtain ⟨o, ho, ⟨mo⟩⟩ := GlobalTheory.T.exists_unitaryModuliObject_spread_normal_domain Dw l c A bA tO hpr ham hkt htors K g _ oK hsK n₄
  obtain ⟨f₀, ⟨hf₀s, ⟨mf₀⟩⟩, -⟩ := Xo.rep (Sp A) (spMap (bA.comp incl)) inferInstance o
  have hf₀ : f₀ ≫ Xo.s = spMap bA ≫ spMap incl := by rw [hf₀s, spMap_comp']
  let yo : Sp A ⟶ Xo.XF c := pullback.lift f₀ (spMap bA) hf₀
  have hκ : spMap g ≫ yo = C.y := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      obtain ⟨mk'⟩ := GlobalTheory.LevelQuotRep.obj_comp mo mf₀
      exact (Xo.rep (Sp K) _ inferInstance oK).unique ⟨by rw [Category.assoc, hf₀s, hsK], ⟨mk'⟩⟩ ⟨rfl, ⟨mK⟩⟩
    · rw [Category.assoc, pullback.lift_snd, C.y_over, ← spMap_comp', hgb, spMap_comp']
  have hunitR : IsUnit ((algebraMap R (FractionRing R)) f) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf0)
  let jA : A →+* FractionRing R := IsLocalization.Away.lift f hunitR
  have hjA : jA.comp (algebraMap R A) = algebraMap R (FractionRing R) := IsLocalization.lift_comp _
  have hg₀ : spMap jA ≫ spMap (algebraMap R A) = jK R := by rw [← spMap_comp', hjA]
  have mo' : SABMap tO Xo.univ.t f₀ := ho ▸ mf₀.toSABMap
  refine ⟨spMap jA ≫ yo, yo, spMap g, ?_, ?_, ?_, E1, hκ⟩
  · rw [Category.assoc, pullback.lift_snd, ← hg₀, Category.assoc]
    show spMap jA ≫ spMap ((algebraMap R A).comp (iw.comp L.b)) = _
    rw [spMap_comp']
  · refine (genOf_iff Xo c _ t₁).2 ?_
    obtain ⟨t', ⟨n⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap jA) tO
    exact ⟨t', GlobalTheory.TraitOrder.comp hg₀ mO n,
      GlobalTheory.TraitOrder.comp (by rw [Category.assoc, pullback.lift_fst]) mo' n⟩
  · intro g' hg'
    obtain ⟨φ', rfl⟩ := Spec.map_surjective g'
    have h2 : CommRingCat.ofHom (algebraMap R A) ≫ φ' = CommRingCat.ofHom (algebraMap R (FractionRing R)) :=
      Spec.map_injective (by rw [Spec.map_comp]; exact hg')
    have h3 : φ'.hom = jA := IsLocalization.ringHom_ext (Submonoid.powers f)
      ((congrArg CommRingCat.Hom.hom h2).trans hjA.symm)
    have h4 : φ' = CommRingCat.ofHom jA := by ext1; exact h3
    rw [h4]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifiedOnOpenOfSpecialisesToClassifiedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.classified_on_open_of_specialises_to_classified : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (D' : Datum H) (L : LowBase D' c) (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (C : Fam Xo c V) (t₁ : SAB H (Sp R)) (P₁ : PELUnif (maximalIdeal R) t₁) (iw : L.W →+* R) (θ : R →+* V), IsLocalHom θ → θ.comp (iw.comp L.b) = C.b → ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → R) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ L.D.X) (e₁ : P₁.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ i, θ (s (.inl i)) ≠ 0) → (∀ j, IsUnit (s (.inr j))) → DivFrom L P₁.D.toPre P₁.oD iw s ε e₁ → DivFrom L C.P.D.toPre C.P.oD (θ.comp iw) (fun k => θ (s k)) ε e → ∃ (y₁ : Sp (FractionRing R) ⟶ Xo.XF c) (yo : Sp (Localization.Away (∏ i, s (.inl i))) ⟶ Xo.XF c) (κ : Sp (FractionRing V) ⟶ Sp (Localization.Away (∏ i, s (.inl i)))), y₁ ≫ pullback.snd _ _ = jK R ≫ spMap (iw.comp L.b) ∧ GlobalTheory.UPoinc.GenOf Xo c y₁ t₁ ∧ (∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away (∏ i, s (.inl i))), g ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK R → g ≫ yo = y₁) ∧ κ ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK V ≫ spMap θ ∧ κ ≫ yo = C.y := by
  first | exact @GlobalTheory.clsOpen | exact GlobalTheory.clsOpen | (intros; apply GlobalTheory.clsOpen <;> assumption)
end
end
