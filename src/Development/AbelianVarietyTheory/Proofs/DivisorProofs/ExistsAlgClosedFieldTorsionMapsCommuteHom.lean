module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationAdjointEndomorphismsCommute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinatesCompareNormalisedGeneratorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPullbackDataStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitTorsionPointMapCommutesCharInjectiveHom
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
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLinearOfIsPullUniformisation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvrStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairingStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitTorsionPointMapCommutesCharInjectiveHomStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.trait_torsion_point_map_commutes_char_injective_hom : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (A₁ A₂ : PolAV (Sp (FractionRing V))) (G₁ G₂ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif (maximalIdeal V) D₁ A₁ G₁) (U₂ : Unif (maximalIdeal V) D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → Function.Injective h → Key U₁.toUnifPre U₂.toUnifPre c b h F := by
  first | exact @GlobalTheory.Mum.Two.KeyDvr.main | exact GlobalTheory.Mum.Two.KeyDvr.main | (intros; apply GlobalTheory.Mum.Two.KeyDvr.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomPullbackMaps

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two.PullLin

open GlobalTheory.ArcPull GlobalTheory.PullLinear
open GlobalTheory.PsiEvenPull (proj)

theorem act_proj₂ {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} {A' B' : Over S'}
    (e : A' ⟶ (Over.pullback f).obj A) (e₂ : B' ⟶ (Over.pullback f).obj B) {u : A ⟶ B} {u' : A' ⟶ B'}
    (h : u' ≫ e₂ = e ≫ (Over.pullback f).map u) :
    u'.left ≫ e₂.left ≫ pullback.fst B.hom f = (e.left ≫ pullback.fst A.hom f) ≫ u.left := by
  have h1 : u'.left ≫ e₂.left = e.left ≫ ((Over.pullback f).map u).left := congrArg (·.left) h
  rw [← Category.assoc, h1, Category.assoc, map_left_fst, Category.assoc]

theorem torusHomOf_iff' {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') :
    TorusHomOf h t ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ (splitTorus S X).left) (z : Z) (χ : X'),
      gm (r ≫ t.left) z ⊤ (charUnit S X' χ) = gm r z ⊤ (charUnit S X (h χ)) := by
  constructor
  · intro H Z r z χ
    rw [← H χ]
    exact ((gm_res r z (V := ⊤) _ trivial _).trans (gm_pull r t.left z ⊤ trivial _)).symm
  · intro H χ
    refine unit_ext fun z _ => ?_
    rw [← H]
    exact (gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t.left z ⊤ trivial _)



theorem linPull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (D₁' D₂' : DegData R' I') (A₁' A₂' : PolAV (Sp (FractionRing R'))) (hD₁ : IsPullDeg φ D₁.toPre D₁'.toPre) (hD₂ : IsPullDeg φ D₂.toPre D₂'.toPre) (U₁' : Unif I' D₁' A₁' ((Over.pullback (specOf φ)).obj G₁)) (U₂' : Unif I' D₂' A₂' ((Over.pullback (specOf φ)).obj G₂)), IsPullUnif φ hD₁ (Iso.refl _) U₁ U₁' → IsPullUnif φ hD₂ (Iso.refl _) U₂ U₂' → ∀ (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁.toUnifPre U₂.toUnifPre a b h → ∃ (b' : D₁'.toPre.P.A ⟶ D₂'.toPre.P.A) (h' : D₂'.toPre.X →+ D₁'.toPre.X), Lin U₁'.toUnifPre U₂'.toUnifPre ((Over.pullback (specOf φ)).map a) b' h' ∧ b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b ∧ ∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ) := by
  intro R R' _ _ _ _ I I' φ D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ D₁' D₂' A₁' A₂' hD₁ hD₂ U₁' U₂' hU₁ hU₂ a b h hL
  obtain ⟨homA, homB, hq0, hi0⟩ := hL
  obtain ⟨_wL₁, -, _he₁, -, H₁⟩ := (isPullUnif_iff_stalks R R' I I' φ D₁ D₁' hD₁ A₁ A₁' G₁ _ (Iso.refl _) U₁ U₁').1 hU₁
  obtain ⟨_wL₂, -, _he₂, -, H₂⟩ := (isPullUnif_iff_stalks R R' I I' φ D₂ D₂' hD₂ A₂ A₂' G₂ _ (Iso.refl _) U₂ U₂').1 hU₂
  choose h₁ hf₁ hpt₁ _hw₁ using H₁
  choose h₂ hf₂ hpt₂ _hw₂ using H₂
  have := hD₁.e_hom
  have := hD₂.e_hom
  obtain ⟨b', homB', hB⟩ : ∃ b' : D₁'.toPre.P.A ⟶ D₂'.toPre.P.A, IsMonHom b' ∧
      b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b :=
    ⟨hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b ≫ hD₂.e.inv, inferInstance, by simp⟩
  obtain ⟨h', hx⟩ : ∃ h' : D₂'.toPre.X →+ D₁'.toPre.X, ∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ) :=
    ⟨hD₁.xe.symm.toAddMonoidHom.comp (h.comp hD₂.xe.toAddMonoidHom), fun χ => hD₁.xe.apply_symm_apply _⟩
  have hG : (Over.pullback (specOf φ)).map a ≫ (Iso.refl ((Over.pullback (specOf φ)).obj G₂)).hom =
      (Iso.refl ((Over.pullback (specOf φ)).obj G₁)).hom ≫ (Over.pullback (specOf φ)).map a := by simp
  have hact : ∀ e : ℕ, ((Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)).left ≫ h₂ e =
      h₁ e ≫ ((Over.pullback (thick R I e)).map a).left := by
    intro e
    have hf' : h₂ e ≫ pullback.fst G₂.hom (thick R I e) =
        pullback.fst ((Over.pullback (specOf φ)).obj G₂).hom (thick R' I' e) ≫
          (Iso.refl ((Over.pullback (specOf φ)).obj G₂)).hom.left ≫ pullback.fst G₂.hom (specOf φ) := hf₂ e
    have hf₁' : h₁ e ≫ pullback.fst G₁.hom (thick R I e) =
        pullback.fst ((Over.pullback (specOf φ)).obj G₁).hom (thick R' I' e) ≫
          (Iso.refl ((Over.pullback (specOf φ)).obj G₁)).hom.left ≫ pullback.fst G₁.hom (specOf φ) := hf₁ e
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hmono : Mono (pullback.fst G₂.hom (thick R I e)) := inferInstance
    rw [← cancel_mono (pullback.fst G₂.hom (thick R I e)), Category.assoc, hf', Category.assoc, map_left_fst,
      ← Category.assoc (h₁ e), hf₁',
      ← Category.assoc (((Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)).left), map_left_fst,
      Category.assoc, act_proj₂ _ (Iso.refl _).hom (Iso.refl _).hom hG]
    simp only [Category.assoc]
  have k : ∀ {S : Type} [CommRing S] [IsDomain S] {J : Ideal S} {E : DegPre S} {e : ℕ}
      {K : Over (Spec (CommRingCat.of S))} [GrpObj K] [IsCommMonObj K] (g : GtCoord J E e K)
      {B : Over (Spec (CommRingCat.of S))} (u : E.P.A ⟶ B), (g.q ≫ (Over.pullback (thick S J e)).map u).left ≫
        pullback.fst B.hom (thick S J e) = g.pG.left ≫ u.left := by
    intro S _ _ J E e K _ _ g B u
    rw [Over.comp_left, Category.assoc, map_left_fst, pG_left, Category.assoc]
  have hB' := act_proj₂ (specOf φ) hD₁.e.hom hD₂.e.hom hB
  have k₂ : ∀ e, (Over.map (thick R' I' e)).map ((Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)) ≫
      (U₂'.gt e).pG = (U₁'.gt e).pG ≫ b' := by
    intro e
    have k₁ : ((Over.pullback (thick R I e)).map a).left ≫ (U₂.gt e).pG.left =
        (U₁.gt e).pG.left ≫ b.left := by
      rw [← k, ← hq0 e]
      exact (Category.assoc _ _ _).symm
    refine ext_of_iso_pullback _ hD₂.e ?_
    change (((Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)).left ≫ (U₂'.gt e).pG.left) ≫ _ =
      ((U₁'.gt e).pG.left ≫ b'.left) ≫ _
    rw [Category.assoc, Category.assoc, hB', (hpt₂ e).1,
      ← Category.assoc (U₁'.gt e).pG.left, (hpt₁ e).1, ← Category.assoc, hact, Category.assoc,
      Category.assoc, k₁]
  have hq : ∀ e : ℕ, (Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a) ≫ (U₂'.gt e).q =
      (U₁'.gt e).q ≫ (Over.pullback (thick R' I' e)).map b' := by
    intro e
    refine ext_of_pullback _ ?_
    rw [k, Over.comp_left, Category.assoc]
    exact congrArg (·.left) (k₂ e)
  refine ⟨b', h', ⟨inferInstance, homB', hq, fun e => ?_⟩, hB, hx⟩
  obtain ⟨t, ht, hi⟩ := hi0 e
  have hk : ((U₁'.gt e).i ≫ (Over.pullback (thick R' I' e)).map ((Over.pullback (specOf φ)).map a)) ≫ (U₂'.gt e).q =
      toUnit _ ≫ η[thickObj R' I' e D₂'.toPre.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, (U₁'.gt e).isKernel.w, Category.assoc,
      IsMonHom.one_hom]
  have hi' := (U₂'.gt e).isKernel.lift_fst _ _ hk
  generalize (U₂'.gt e).isKernel.lift _ _ hk = t' at hi'
  refine ⟨t', ?_, hi'.symm⟩
  obtain ⟨s, τ, hτ⟩ := exists_point (U₁.gt e) (U₁'.gt e) (hpt₁ e).1 ((hpt₁ e).2 0).1 (𝟙 _)
  have hτ' : ((τ ≫ t) ≫ (U₂.gt e).i).left = (t' ≫ (U₂'.gt e).i).left ≫ h₂ e := by
    rw [Category.assoc, ← hi, ← Category.assoc, Over.comp_left, hτ, hi', Category.id_comp,
      Over.comp_left, Category.assoc, Category.assoc, hact]
  intro χ
  refine unit_ext fun z _ => ?_
  have e₁ := char_eq (U₂.gt e) (U₂'.gt e) hD₂.w ((hpt₂ e).2 χ).1 ((hpt₂ e).2 χ).2 t' (τ ≫ t) hτ' z
  have e₂ := char_eq (U₁.gt e) (U₁'.gt e) hD₁.w ((hpt₁ e).2 (h' χ)).1 ((hpt₁ e).2 (h' χ)).2 (𝟙 _) τ hτ z
  have e₃ := (torusHomOf_iff' _ t).1 ht _ τ.left z (hD₂.xe χ)
  rw [hx] at e₂
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t'.left z ⊤ trivial _)).trans ?_
  rw [Category.id_comp]
  exact e₁.symm.trans (e₃.trans e₂)

end GlobalTheory.Mum.Two.PullLin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomPullbackMapsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.uniformisedGroupHom_pullback_maps : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (D₁' D₂' : DegData R' I') (A₁' A₂' : PolAV (Sp (FractionRing R'))) (hD₁ : IsPullDeg φ D₁.toPre D₁'.toPre) (hD₂ : IsPullDeg φ D₂.toPre D₂'.toPre) (U₁' : Unif I' D₁' A₁' ((Over.pullback (specOf φ)).obj G₁)) (U₂' : Unif I' D₂' A₂' ((Over.pullback (specOf φ)).obj G₂)), IsPullUnif φ hD₁ (Iso.refl _) U₁ U₁' → IsPullUnif φ hD₂ (Iso.refl _) U₂ U₂' → ∀ (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁.toUnifPre U₂.toUnifPre a b h → ∃ (b' : D₁'.toPre.P.A ⟶ D₂'.toPre.P.A) (h' : D₂'.toPre.X →+ D₁'.toPre.X), Lin U₁'.toUnifPre U₂'.toUnifPre ((Over.pullback (specOf φ)).map a) b' h' ∧ b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b ∧ ∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ) := by
  first | exact @GlobalTheory.Mum.Two.PullLin.linPull | exact GlobalTheory.Mum.Two.PullLin.linPull | (intros; apply GlobalTheory.Mum.Two.PullLin.linPull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgClosedFieldTorsionMapsCommuteHom

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.Two

open GlobalTheory.Balanced

section Gen
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I}
  {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂]
  [IsCommMonObj G₂] {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂}

theorem toG_gen₀ {a : G₁ ⟶ G₂} {c : A₁.A ⟶ A₂.A} (hc : Gen₀ U₁ U₂ a c) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ A₁.A) : toG U₂ (x ≫ c) = toG U₁ x ≫ a.left := by
  have e : c ≫ U₂.gen.inv = U₁.gen.inv ≫ (Over.pullback (jK R)).map a := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e' : c.left ≫ U₂.gen.inv.left = U₁.gen.inv.left ≫ ((Over.pullback (jK R)).map a).left :=
    congrArg (fun q => q.left) e
  have e₂ : ((Over.pullback (jK R)).map a).left ≫ pullback.fst G₂.hom (jK R) = pullback.fst G₁.hom (jK R) ≫ a.left :=
    pullback.lift_fst _ _ _
  calc toG U₂ (x ≫ c) = x.left ≫ (c.left ≫ U₂.gen.inv.left) ≫ pullback.fst G₂.hom (jK R) := by
        simp only [toG, Over.comp_left, Category.assoc]
    _ = _ := by rw [e', Category.assoc, e₂, toG, Category.assoc, Category.assoc]

end Gen

theorem exists_toG_pull {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V}
    (φ : R →+* V) {D : DegData R I} {D' : DegData V I'} {A : PolAV (Sp (FractionRing R))}
    {A' : PolAV (Sp (FractionRing V))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (U' : UnifPre I' D' A' ((Over.pullback (specOf φ)).obj G))
    {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F]
    (hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) =
      algebraMap (FractionRing V) F (algebraMap V _ (φ r))) (z : TFK (R := R) F ⟶ A.A) :
    ∃ z' : TFK (R := V) F ⟶ A'.A, toG U' z' ≫ pullback.fst G.hom (specOf φ) = toG U z := by
  have w : toG U z ≫ G.hom = (jFK (R := V) F ≫ jK V) ≫ specOf φ := by
    rw [toG_over]
    simp only [jFK, jK, specOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hF
  obtain ⟨z', hz'⟩ := exists_toG U' (pullback.lift _ _ w) (pullback.lift_snd _ _ _)
  exact ⟨z', by rw [hz']; exact pullback.lift_fst _ _ _⟩



theorem exists_key : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → Function.Injective h → ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : Algebra (FractionRing R) F), Key U₁.toUnifPre U₂.toUnifPre c b h F := by
  intro R _ _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ hG₁ hG₂ U₁ U₂ a c b h _ hgen hlin hcoord hinj
  have hL := GlobalTheory.firstFiveLaws
  obtain ⟨V, _, _, _, φ, hV, hφ, hI⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.1 R I hR
  have : CharZero V := charZero_of_injective_ringHom hφ
  have hR' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨v, hv⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 V ϖ hϖ
  obtain ⟨D₁', hD₁, A₁', U₁', hG₁', hU₁, hpt₁, -⟩ := GlobalTheory.T.uniformisation_endomorphisms_to_complete_dvr hL R I hR D₁ A₁ G₁ hG₁ U₁ V φ hV hφ hI
  obtain ⟨D₂', hD₂, A₂', U₂', hG₂', hU₂, hpt₂, -⟩ := GlobalTheory.T.uniformisation_endomorphisms_to_complete_dvr hL R I hR D₂ A₂ G₂ hG₂ U₂ V φ hV hφ hI
  let Ω := AlgebraicClosure (FractionRing V)
  let ψ : R →+* Ω := ((algebraMap (FractionRing V) Ω).comp (algebraMap V (FractionRing V))).comp φ
  have hψ : Function.Injective ψ :=
    ((algebraMap (FractionRing V) Ω).injective.comp (IsFractionRing.injective V (FractionRing V))).comp hφ
  let _ : Algebra (FractionRing R) Ω := (IsFractionRing.lift hψ).toAlgebra
  have hF : ∀ r : R, algebraMap (FractionRing R) Ω (algebraMap R _ r) =
      algebraMap (FractionRing V) Ω (algebraMap V _ (φ r)) := fun r => IsFractionRing.lift_algebraMap hψ r
  obtain ⟨ex₁, -, io₁, ns₁⟩ := hpt₁ Ω hF
  obtain ⟨ex₂, sur₂, io₂, ns₂⟩ := hpt₂ Ω hF
  obtain ⟨b', h', hlin', hb', hh'⟩ := GlobalTheory.T.uniformisedGroupHom_pullback_maps R V I (maximalIdeal V) φ D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ D₁' D₂' A₁' A₂'
    hD₁ hD₂ U₁' U₂' hU₁ hU₂ a b h hlin
  have hcoord' := GlobalTheory.T.torusCoordinates_compare_normalisedGenerators V (maximalIdeal V) hR' D₁' D₂' A₁' A₂' _ _ U₁'.toUnifPre U₂'.toUnifPre
    ((Over.pullback (specOf φ)).map a) b' h' hlin'
  let c' : A₁'.A ⟶ A₂'.A := U₁'.gen.inv ≫ (Over.pullback (jK V)).map ((Over.pullback (specOf φ)).map a) ≫ U₂'.gen.hom
  have hgen' : Gen₀ U₁'.toUnifPre U₂'.toUnifPre ((Over.pullback (specOf φ)).map a) c' := by
    simp only [Gen₀, c', Iso.hom_inv_id_assoc]
  have hc' : IsMonHom c' := by
    have := U₁'.gen_hom
    have := U₂'.gen_hom
    have := hlin'.1
    dsimp only [c']
    infer_instance
  have hinj' : Function.Injective h' := fun x y hxy => hD₂.xe.injective (hinj (by rw [← hh', ← hh', hxy]))
  have key' := GlobalTheory.T.trait_torsion_point_map_commutes_char_injective_hom V hV ϖ hϖ Ω v hv D₁' D₂' A₁' A₂' _ _ hG₁' hG₂' U₁' U₂' ((Over.pullback (specOf φ)).map a)
    c' b' h' hc' hgen' hlin' hcoord' hinj'
  choose π₁ hπ₁ _ using ex₁
  choose π₂ hπ₂ _ using ex₂
  refine ⟨Ω, inferInstance, inferInstance, inferInstance, fun k hk p x hx g' hact => ?_⟩
  have hact' : Act D₁'.toPre D₂'.toPre b' h' (π₁ p.g) (π₂ g') :=
    (GlobalTheory.T.torusExtensionPointAction_pullback_data R V φ D₁.toPre D₂.toPre D₁'.toPre D₂'.toPre hD₁ hD₂ b h b' h' hlin.2.1 hlin'.2.1 hb' hh'
      (fun χ => (hcoord χ).imp fun _ hu => hu.1) Ω p.g g' (π₁ p.g) (π₂ g') (hπ₁ _) (hπ₂ _)).1 hact
  let ρp : QkPt D₁'.toPre Ω k := ⟨hD₁.xe.symm p.y, π₁ p.g, by
    obtain ⟨s, h1, h2⟩ := p.eq
    exact ⟨π₁ s, (ns₁ k _ _ _ _ (hπ₁ _) (hπ₁ _)).1 h1, (io₁ _ _ _ (hπ₁ _)).1 (by rwa [AddEquiv.apply_symm_apply])⟩⟩
  obtain ⟨x', hx'e⟩ := exists_toG_pull φ U₁.toUnifPre U₁'.toUnifPre hF x
  have hx' : QkToAkU U₁'.toUnifPre Ω k ρp x' :=
    hL.2.2.2.2.qkBaseChange R V I _ hR hR' φ D₁ A₁ G₁ U₁ _ (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 _))) A₁' D₁'
      hD₁ U₁' hU₁ Ω hF k hk p x ρp x' rfl (hπ₁ _)
      (by simpa only [toG, Category.assoc, Iso.refl_hom, Over.id_left, Category.id_comp] using hx'e) hx
  obtain ⟨r, rg, hr⟩ := key' k hk ρp x' hx' (π₂ g') hact'
  let p' : QkPt D₂.toPre Ω k := ⟨hD₂.xe r.y, g', by
    obtain ⟨s', h1, h2⟩ := r.eq
    obtain ⟨s, hs, -⟩ := sur₂ s'
    exact ⟨s, (ns₂ k _ _ _ _ (hπ₂ g') hs).2 (rg ▸ h1), (io₂ _ _ _ hs).2 h2⟩⟩
  refine ⟨p', rfl, ?_⟩
  obtain ⟨f₂, hf₂, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL R I hR D₂ A₂ G₂ hG₂ U₂ Ω k hk
  obtain ⟨f₂', hf₂', -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V _ hR' D₂' A₂' _ hG₂' U₂' Ω k hk
  obtain ⟨z', hz'e⟩ := exists_toG_pull φ U₂.toUnifPre U₂'.toUnifPre hF (f₂ p')
  have hz' : QkToAkU U₂'.toUnifPre Ω k r z' :=
    hL.2.2.2.2.qkBaseChange R V I _ hR hR' φ D₂ A₂ G₂ U₂ _ (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 _))) A₂' D₂'
      hD₂ U₂' hU₂ Ω hF k hk p' (f₂ p') r z' (hD₂.xe.symm_apply_apply r.y).symm (rg ▸ hπ₂ g')
      (by simpa only [toG, Category.assoc, Iso.refl_hom, Over.id_left, Category.id_comp] using hz'e) ((hf₂ _ _).2 rfl)
  have ez : z' = x' ≫ c' := ((hf₂' _ _).1 hz').trans ((hf₂' _ _).1 hr).symm
  have hpa : ((Over.pullback (specOf φ)).map a).left ≫ pullback.fst G₂.hom (specOf φ) =
      pullback.fst G₁.hom (specOf φ) ≫ a.left := pullback.lift_fst _ _ _
  refine (hf₂ _ _).2 (toG_injective U₂.toUnifPre ?_).symm
  rw [← hz'e, ez, toG_gen₀ hgen', toG_gen₀ hgen, ← hx'e, Category.assoc, Category.assoc, hpa]

end GlobalTheory.Mum.Two
end
end
end
