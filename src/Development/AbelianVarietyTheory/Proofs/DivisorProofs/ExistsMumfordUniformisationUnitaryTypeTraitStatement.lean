module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArcDatumRecoveringUnitaryDataCompleteDVRStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrLocalFiniteExtensionStatement
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiser
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DvrAdmissibleBaseAndPowerSeriesEvalUniformiser
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
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
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PartOneOfSemistableReductionPadicPolarized

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointArcDataAtUniformiserCompleteDVR

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_point_hasArcData_uniformiser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (Xo : Moduli Dm l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Y.N4 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (b : O →+* V) (ϖ : V) (a : ArcIn Dm l β V b), Irreducible ϖ → ∃ y : Sp V ⟶ Y.X, Y.HasArcData a (maximalIdeal V) (RingHom.id V) ϖ y := by
  intro E _ _ _ H Dm l Xo c O _ β Y hN V _ _ _ hV b ϖ a hϖ
  obtain ⟨hdvr, hc, hcz⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  obtain ⟨h1, h2, -, h4, h5⟩ := GlobalTheory.lawsAndExpansions.1
  have hT := GlobalTheory.twistBaseChange
  have hm : maximalIdeal V = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  obtain ⟨χ, hχ, -⟩ := hN V b ϖ a (Or.inr ⟨hdvr, hϖ, hm ▸ hc⟩)
  obtain ⟨hs, -, hj, hd⟩ := (hχ χ).1 rfl
  obtain ⟨-, -, ev, hC, hX, -⟩ := GlobalTheory.UniformiserEval.dvr_admissibleBase_and_powerSeries_evalUniformiser V ϖ hϖ hc
  have hr : Set.range (jK V ≫ spMap ev ≫ χ) ⊆ Set.range Y.j := by
    rintro _ ⟨x, rfl⟩
    have e : (jK V ≫ spMap ev ≫ χ) x = χ (spMap ev (jK V x)) := by
      simp only [Scheme.Hom.comp_apply]
    rw [e]
    apply hj
    intro hx
    have hx' : algebraMap V (FractionRing V) (ev (PowerSeries.C ϖ * PowerSeries.X)) ∈ x.asIdeal := hx
    have hu : IsUnit (algebraMap V (FractionRing V) (ev (PowerSeries.C ϖ * PowerSeries.X))) := by
      rw [map_mul, hC, hX]
      refine IsUnit.mk0 _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact mul_ne_zero hϖ.ne_zero hϖ.ne_zero
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx' hu)
  refine ⟨spMap ev ≫ χ, ?_⟩
  rw [hm]
  exact GlobalTheory.hasArcData_specialise h1 h2 hT h4.unifBaseChange h5 E H Dm l Xo c O β Y V b ϖ a hϖ hc ev hC hX χ hs hr hd

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointArcDataAtUniformiserCompleteDVRStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_point_arcData_at_uniformiser_completeDVR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (Xo : Moduli Dm l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Y.N4 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (b : O →+* V) (ϖ : V) (a : ArcIn Dm l β V b), Irreducible ϖ → ∃ y : Sp V ⟶ Y.X, Y.HasArcData a (maximalIdeal V) (RingHom.id V) ϖ y := by
  first | exact @GlobalTheory.Mum.exists_point_hasArcData_uniformiser | exact GlobalTheory.Mum.exists_point_hasArcData_uniformiser | (intros; apply GlobalTheory.Mum.exists_point_hasArcData_uniformiser <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisGenericUnitaryUnifor

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.UTraitHyp

theorem hypS_generic : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif I t), (letI := P.A.isAb.comm; GlobalTheory.ZH.HypS P.A.A P.A.L) := by
  intro V _ _ I E _ _ _ H t P
  letI := P.A.isAb.comm
  obtain ⟨h1, h2, -⟩ := GlobalTheory.Ex.GenericFibre.unif_generic P
  exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ t.G P.A.A (jK V) _ t.PP.L P.A.L t.PP.isLB P.A.isLB h1 h2
    ⟨t.act.act H.w0, t.act.act (H.bar H.w0), t.act.hom _, t.act.hom _,
      by rw [← t.act.add, GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel, t.act.one], t.prim, t.adj _⟩

end GlobalTheory.UTraitHyp

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisGenericUnitaryUniforStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.lineBundleSymmetryHypothesis_generic_unitary_uniformised : ∀ (V : Type) [CommRing V] [IsDomain V] (I : Ideal V) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif I t), (letI := P.A.isAb.comm; GlobalTheory.ZH.HypS P.A.A P.A.L) := by
  first | exact @GlobalTheory.UTraitHyp.hypS_generic | exact GlobalTheory.UTraitHyp.hypS_generic | (intros; apply GlobalTheory.UTraitHyp.hypS_generic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordUniformisationUnitaryTypeTrait

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.MumTrait.exists_unif_of_pelOK : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (G : Over (Sp R₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (A : PolAV (Sp (FractionRing R₁))), GlobalTheory.LN.CDvr R₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsSemiAbelian G ∧ Nonempty (Unif (maximalIdeal R₁) D₁ A G) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) := by
  intro R _ _ _ hR E _ _ _ H Dm D _ o hX hP
  obtain ⟨p, hp, W₀, hW, i, V₁, _, _, _, ρ₁, b₁, hV₁, hρ₁, hf₁, hl₁, hb₁⟩ := GlobalTheory.T.exists_complete_dvr_local_finite_extension R hR E H
  have hpq : 1 ≤ Dm.p + Dm.q := by have := hP.2.1; omega
  let Xo : ∀ l : Level H, Moduli Dm l := fun l => (GlobalTheory.Moduli.moduli_scheme_exists E H Dm l hpq).some
  obtain ⟨Y, hY, -⟩ := (GlobalTheory.partI_of_semistableReduction GlobalTheory.SS.semistableReductionSt).2 E H Dm hpq Xo
  have hFour := ((hY p W₀ hp hW).2 i).2.2
  obtain ⟨V, _, _, _, ρ, b, ϖ, a, hV, hρi, hρf, hϖ, hmatch⟩ := GlobalTheory.T.exists_arcDatum_recovering_unitaryData_completeDVR R hR E H Dm D o hX hP i.l i.c _ (i.c.V W₀).subtype
    Subtype.val_injective V₁ ρ₁ b₁ hV₁ hρ₁ hf₁ hl₁ hb₁
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_point_arcData_at_uniformiser_completeDVR E H Dm i.l (Xo i.l) i.c _ _ (Y p W₀ hp hW i) hFour V hV b ϖ a hϖ
  obtain ⟨t, -, P, hpull⟩ := hmatch (Xo i.l) (Y p W₀ hp hW i) y hy
  exact ⟨V, _, _, _, ρ, P.D, t.G, inferInstance, inferInstance, P.A, hV, hρi, hρf, hpull, t.semi, ⟨P.U⟩,
    GlobalTheory.T.lineBundleSymmetryHypothesis_generic_unitary_uniformised V (maximalIdeal V) E H t P⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordUniformisationUnitaryTypeTraitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_mumfordUniformisation_unitaryTypeTrait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (G : Over (Sp R₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (A : PolAV (Sp (FractionRing R₁))), GlobalTheory.LN.CDvr R₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsSemiAbelian G ∧ Nonempty (Unif (maximalIdeal R₁) D₁ A G) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) := by
  first | exact @GlobalTheory.MumTrait.exists_unif_of_pelOK | exact GlobalTheory.MumTrait.exists_unif_of_pelOK | (intros; apply GlobalTheory.MumTrait.exists_unif_of_pelOK <;> assumption)
end
end
