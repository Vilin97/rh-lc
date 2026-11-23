module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegIdentitySelfAdmissible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionTwistOfSamePolarisedData
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegOfSameTorusTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianPartHomUniformisedGroups
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartIsoIsMonHomAndRigidified
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPeriodsTranslatedBundleTwistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationsTranslationPeriodMapsCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionTwistOfSamePolarisedDataStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_twoTorsion_twist_of_same_polarisedData : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)), SamePol D₀.toPre D.toPre → ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧ GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g := by
  first | exact @GlobalTheory.MumCmp.exists_twist_of_samePol | exact GlobalTheory.MumCmp.exists_twist_of_samePol | (intros; apply GlobalTheory.MumCmp.exists_twist_of_samePol <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegOfSameTorusTwistStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.nonempty_isPullDeg_of_same_torus_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D₂ D : DegData R (maximalIdeal R)) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g → GlobalTheory.MumCmp.IsTwist D₂.toPre D.toPre g → Nonempty (IsPullDeg (RingHom.id R) D₀.toPre D₂.toPre) := by
  first | exact @GlobalTheory.MumCmp.Uniq.nonempty_isPullDeg_of_isTwist | exact GlobalTheory.MumCmp.Uniq.nonempty_isPullDeg_of_isTwist | (intros; apply GlobalTheory.MumCmp.Uniq.nonempty_isPullDeg_of_isTwist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartIsoOfTwoUniformisations

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp

theorem abelianPart_iso_of_twoUnif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom ∧ ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left := by
  intro R _ _ _ hBase D A G _ _ hG U g _ a _ _ A₂ D₂ U₂ _
  have hR : AdmBase R (maximalIdeal R) := hBase.1
  have hN : IsNoetherianRing R := hR.1
  have hC : IsAdicComplete (maximalIdeal R) R := hR.2.2.2
  have hJ : maximalIdeal R ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot _
  obtain ⟨b₁, hb₁, h₁⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R (maximalIdeal R) hR D₂ D A₂ A G G
    U₂.toUnifPre U.toUnifPre (𝟙 G) inferInstance
  obtain ⟨b₂, hb₂, h₂⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R (maximalIdeal R) hR D D₂ A A₂ G G
    U.toUnifPre U₂.toUnifPre (𝟙 G) inferInstance

  have q₁ : ∀ e, (U.gt e).q = (U₂.gt e).q ≫ (Over.pullback (thick R (maximalIdeal R) e)).map b₁ := by
    intro e
    have := h₁ e
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at this
    exact this
  have q₂ : ∀ e, (U₂.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R (maximalIdeal R) e)).map b₂ := by
    intro e
    have := h₂ e
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at this
    exact this
  have epi : ∀ {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))}
      (V : UnifPre (maximalIdeal R) D' A' G) (e : ℕ), Epi (V.gt e).q := by
    intro D' A' V e
    have := (V.gt e).q_flat
    have := (V.gt e).q_surj
    have : Epi (V.gt e).q.left := Flat.epi_of_flat_of_surjective _
    exact Over.epi_of_epi_left _
  have k₁ : b₂ ≫ b₁ = 𝟙 _ := by
    have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    have := D.toPre.P.isAb.proper
    refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq hJ _ _ _ fun n => ?_
    have := epi U.toUnifPre n
    rw [← cancel_epi (U.gt n).q, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Category.comp_id, ← Category.assoc, ← q₂, ← q₁]
  have k₂ : b₁ ≫ b₂ = 𝟙 _ := by
    have := D₂.toPre.P.isAb.smooth
    have := D₂.toPre.P.isAb.geomConnected
    have := D₂.toPre.P.isAb.proper
    refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq hJ _ _ _ fun n => ?_
    have := epi U₂.toUnifPre n
    rw [← cancel_epi (U₂.gt n).q, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Category.comp_id, ← Category.assoc, ← q₁, ← q₂]
  refine ⟨⟨b₁, b₂, k₂, k₁⟩, hb₁, fun e => ?_⟩
  show (U₂.gt e).q.left ≫ (fstG (maximalIdeal R) e D₂.toPre.P.A).left ≫ b₁.left =
    (U.gt e).q.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left
  have m : ((Over.pullback (thick R (maximalIdeal R) e)).map b₁).left ≫
      (fstG (maximalIdeal R) e D.toPre.P.A).left = (fstG (maximalIdeal R) e D₂.toPre.P.A).left ≫ b₁.left :=
    pullback.lift_fst _ _ _
  rw [← m, q₁ e, Over.comp_left, Category.assoc]

end GlobalTheory.MumCmp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartIsoOfTwoUniformisationsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.abelianPart_iso_of_two_uniformisations : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom ∧ ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left := by
  first | exact @GlobalTheory.MumCmp.abelianPart_iso_of_twoUnif | exact GlobalTheory.MumCmp.abelianPart_iso_of_twoUnif | (intros; apply GlobalTheory.MumCmp.abelianPart_iso_of_twoUnif <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwoStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_iso_uniformisation_translate_orderTwo : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∃ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen ∧ ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left)) := by
  first | exact @GlobalTheory.MumCmp.exists_iso_twist_of_translate | exact GlobalTheory.MumCmp.exists_iso_twist_of_translate | (intros; apply GlobalTheory.MumCmp.exists_iso_twist_of_translate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDataTranslateOrderTwoIsTwist

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem isTwist_of_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → GlobalTheory.MumCmp.IsTwist D₂.toPre D.toPre g := by
  intro R _ _ _ hB D A G _ _ hG U g hz a ha hlev A₂ D₂ U₂ hL
  obtain ⟨β, hβm, hβq⟩ := GlobalTheory.T.abelianPart_iso_of_two_uniformisations R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL
  obtain ⟨xe, hxe⟩ := GlobalTheory.unifPre_characterGroup_iso R (maximalIdeal R) hB.1 D D₂ A A₂ G hG U.toUnifPre U₂.toUnifPre
  obtain ⟨w, hw, h0⟩ := GlobalTheory.T.exists_iso_uniformisation_translate_orderTwo R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq
  have hc := GlobalTheory.T.uniformisations_translation_period_maps_correspond R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq xe hxe w hw
  exact ⟨β, xe, hβm, hc, w, hw,
    GlobalTheory.T.uniformisation_periods_translatedBundle_twist R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq xe hxe hc w hw h0⟩

end GlobalTheory.MumCmp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDataTranslateOrderTwoIsTwistStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.uniformisationData_translate_orderTwo_isTwist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → GlobalTheory.MumCmp.IsTwist D₂.toPre D.toPre g := by
  first | exact @GlobalTheory.MumCmp.isTwist_of_translate | exact GlobalTheory.MumCmp.isTwist_of_translate | (intros; apply GlobalTheory.MumCmp.isTwist_of_translate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointRefinementsCompareUnif

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem point_and_compare : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧ ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ D₂' : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ Nonempty (IsPullDeg ρ D₂.toPre D₂'.toPre) ∧ Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D₂'.toPre) := by
  have L1 := GlobalTheory.T.exists_twoTorsion_twist_of_same_polarisedData
  have L2 := GlobalTheory.T.uniformisationData_translate_orderTwo_isTwist
  have L3 := GlobalTheory.T.nonempty_isPullDeg_of_same_torus_twist
  intro R _ _ _ hB D₀ D A G _ _ hG U hS
  obtain ⟨g, hz, htw⟩ := L1 R hB D₀ D hS
  refine ⟨g, hz, fun a ha hlev A₂ D₂ U₂ hL => ?_⟩
  have h2 := L2 R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL
  obtain ⟨h3⟩ := L3 R hB D₀ D₂ D g htw h2
  obtain ⟨s₀, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self R (maximalIdeal R) hB.1 D₀
  obtain ⟨s₂, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self R (maximalIdeal R) hB.1 D₂
  exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, D₀, D₂,
    ⟨hB.1, Function.injective_id, RingHom.Finite.id R⟩, inferInstance, ⟨s₀⟩, ⟨s₂⟩, ⟨h3⟩⟩

end GlobalTheory.MumCmp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointRefinementsCompareUnifStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_orderTwo_point_refinements_compare_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧ ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ D₂' : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ Nonempty (IsPullDeg ρ D₂.toPre D₂'.toPre) ∧ Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D₂'.toPre) := by
  first | exact @GlobalTheory.MumCmp.point_and_compare | exact GlobalTheory.MumCmp.point_and_compare | (intros; apply GlobalTheory.MumCmp.point_and_compare <;> assumption)
end
end
