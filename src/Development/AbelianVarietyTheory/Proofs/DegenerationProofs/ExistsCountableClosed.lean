module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdditivePointsDescendFieldExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationPreDataOverSubfield
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOrderActionDescentFieldExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFields
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioDescendsDegenerationPsiFamily
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolAVDescendsToCountableSubfield
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedRingActionDescendOfGenerators
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiEvenTauBimultDescendOfInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelationDescendsFieldExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdditivePointsDescendFieldExtensionStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem _root_.GlobalTheory.T.additive_points_descend_field_extension : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (P₀ : PolAV (Sp K₀)) (P : PolAV (Sp K)) (Φ : P.A.left ⟶ P₀.A.left), IsGrpPullback P.A P₀.A (spMap i) Φ → ∀ (X : Type) [AddCommGroup X] (I : Type) (b : I → X), AddSubgroup.closure (Set.range b) = ⊤ → ∀ c : X → (𝟙_ (Over (Sp K)) ⟶ P.A), (∀ y z, c (y + z) = padd P.A (c y) (c z)) → ∀ x₀ : I → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ k, (c (b k)).left ≫ Φ = spMap i ≫ (x₀ k).left) → ∃ c₀ : X → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ y z, c₀ (y + z) = padd P₀.A (c₀ y) (c₀ z)) ∧ ∀ y, (c y).left ≫ Φ = spMap i ≫ (c₀ y).left := by
  first | exact @GlobalTheory.PointDescent.additive_points_descend | exact GlobalTheory.PointDescent.additive_points_descend | (intros; apply GlobalTheory.PointDescent.additive_points_descend <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationPreDataOverSubfieldStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem _root_.GlobalTheory.T.exists_degenerationPreData_over_subfield : Laws → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K) (P₀ : PolAV (Sp K₀)) (Φ : D.P.A.left ⟶ P₀.A.left), IsGrpPullback D.P.A P₀.A (spMap i) Φ → LBIso D.P.L (P₀.L.pull Φ) → ∀ c₀ : D.X → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ y z, c₀ (y + z) = padd P₀.A (c₀ y) (c₀ z)) → (∀ y, (D.c y).left ≫ Φ = spMap i ≫ (c₀ y).left) → ∃ (D₀ : DegPre K₀) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) (hD : IsPullDeg i D₀ (TauTwist.withPsi D ψ hψ)), D₀.P = P₀ ∧ HEq (PsiEvenPull.proj hD) Φ := by
  first | exact @GlobalTheory.FieldPull.exists_pre_below | exact GlobalTheory.FieldPull.exists_pre_below | (intros; apply GlobalTheory.FieldPull.exists_pre_below <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFieldsStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem _root_.GlobalTheory.T.exists_pullDeg_cancel_tower_of_fields : ∀ (K₀ K₁ K : Type) [Field K₀] [Field K₁] [Field K] (α : K₀ →+* K₁) (β : K₁ →+* K) (D₀ : DegPre K₀) (D₁ : DegPre K₁) (D : DegPre K) (h₁ : IsPullDeg α D₀ D₁) (h : IsPullDeg (β.comp α) D₀ D), ∃ hD : IsPullDeg β D₁ D, PsiEvenPull.proj hD ≫ PsiEvenPull.proj h₁ = PsiEvenPull.proj h := by
  first | exact @GlobalTheory.FieldPull.exists_isPullDeg_cancel | exact GlobalTheory.FieldPull.exists_isPullDeg_cancel | (intros; apply GlobalTheory.FieldPull.exists_isPullDeg_cancel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioDescendsDegenerationPsiFamilyStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem _root_.GlobalTheory.T.exists_ratio_descends_degenerationPsiFamily : ∀ (K : Type) [Field K] (D : DegPre K) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen), ∃ a : D.X → K, ∀ (K₁ : Type) [Field K₁] (β : K₁ →+* K) (D₁ : DegPre K₁) (h : IsPullDeg β D₁ (TauTwist.withPsi D ψ hψ)), (∀ χ, a χ ∈ Set.range β) → ∃ (ψ₁ : TauTwist.PsiFam D₁) (hψ₁ : ∀ χ, (ψ₁ χ).IsGen) (hD : IsPullDeg β (TauTwist.withPsi D₁ ψ₁ hψ₁) D), PsiEvenPull.proj hD = PsiEvenPull.proj h := by
  first | exact @GlobalTheory.FieldPull.exists_ratio_descends | exact GlobalTheory.FieldPull.exists_ratio_descends | (intros; apply GlobalTheory.FieldPull.exists_ratio_descends <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolAVDescendsToCountableSubfieldStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem _root_.GlobalTheory.T.polAV_descends_to_countable_subfield' : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (J I : Type) [Finite J] [Finite I] (a : J → (P.A ⟶ P.A)) (x : I → (𝟙_ (Over (Sp K)) ⟶ P.A)), ∃ (K₀ : Subfield K) (P₀ : PolAV (Sp K₀)) (Φ : P.A.left ⟶ P₀.A.left) (a₀ : J → (P₀.A ⟶ P₀.A)) (x₀ : I → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A)), Countable K₀ ∧ IsGrpPullback P.A P₀.A (spMap K₀.subtype) Φ ∧ LBIso P.L (P₀.L.pull Φ) ∧ (∀ j, (a j).left ≫ Φ = Φ ≫ (a₀ j).left) ∧ ∀ i, (x i).left ≫ Φ = spMap K₀.subtype ≫ (x₀ i).left := by
  first | exact @GlobalTheory.PolCountableDescent.polAV_descends_to_countable_subfield | exact GlobalTheory.PolCountableDescent.polAV_descends_to_countable_subfield | (intros; apply GlobalTheory.PolCountableDescent.polAV_descends_to_countable_subfield <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedRingActionDescendOfGeneratorsStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem _root_.GlobalTheory.T.polarisedRingAction_descend_of_generators : ∀ (O : Type) [CommRing O] [StarRing O] (J : Type) (gen : J → O), Subring.closure (Set.range gen) = ⊤ → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (P₀ : PolAV (Sp K₀)) (P : PolAV (Sp K)) (Φ : P.A.left ⟶ P₀.A.left), IsGrpPullback P.A P₀.A (spMap i) Φ → LBIso P.L (P₀.L.pull Φ) → ∀ (oa : P.OAct O) (a₀ : J → (P₀.A ⟶ P₀.A)), (∀ j, (oa.act (gen j)).left ≫ Φ = Φ ≫ (a₀ j).left) → ∃ oa₀ : P₀.OAct O, ∀ c, (oa.act c).left ≫ Φ = Φ ≫ (oa₀.act c).left := by
  first | exact @GlobalTheory.polOAct_descend_of_generators | exact GlobalTheory.polOAct_descend_of_generators | (intros; apply GlobalTheory.polOAct_descend_of_generators <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiEvenTauBimultDescendOfInjectiveStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem _root_.GlobalTheory.T.psiEven_tauBimult_descend_of_injective : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R'), Function.Injective φ → ∀ (D : DegPre R) (D' : DegPre R') (_ : IsPullDeg φ D D'), (D'.PsiEven → D.PsiEven) ∧ (D'.TauBimult → D.TauBimult) := by
  first | exact @GlobalTheory.psiEven_tauBimult_of_isPullDeg_injective | exact GlobalTheory.psiEven_tauBimult_of_isPullDeg_injective | (intros; apply GlobalTheory.psiEven_tauBimult_of_isPullDeg_injective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelationDescendsFieldExtensionStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem _root_.GlobalTheory.T.psi_relation_descends_field_extension : GlobalFnsSt → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K) (hD : IsPullDeg i D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (oa : D.OAct O) (oa' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (oa'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (oa.onB.act a).left) → ∀ w : O, TraceFormTwistIso D' oa' w → TraceFormTwistIso D oa w := by
  first | exact @GlobalTheory.psi_relation_descend_field | exact GlobalTheory.psi_relation_descend_field | (intros; apply GlobalTheory.psi_relation_descend_field <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCountableClosed

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull

theorem exists_countable_closed {K : Type} [Field K] [IsAlgClosed K] (K₀ : Subfield K) [Countable K₀] {X : Type}
    [Countable X] (a : X → K) : ∃ (F₁ : Type) (_ : Field F₁) (_ : IsAlgClosed F₁) (_ : Countable F₁) (α : K₀ →+* F₁)
      (β : F₁ →+* K), β.comp α = K₀.subtype ∧ ∀ x, a x ∈ Set.range β := by
  let K₁ : Subfield K := Subfield.closure ((K₀ : Set K) ∪ Set.range a)
  have hc : ((K₀ : Set K) ∪ Set.range a).Countable := (Set.to_countable _).union (Set.countable_range a)
  have c₁ : Cardinal.mk K₁ ≤ Cardinal.aleph0 :=
    (Subfield.cardinalMk_closure_le_max _).trans (max_le (Cardinal.mk_le_aleph0_iff.2 hc.to_subtype) le_rfl)
  have h : K₀ ≤ K₁ := fun x hx => Subfield.subset_closure (Or.inl hx)
  let β : AlgebraicClosure K₁ →ₐ[K₁] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨AlgebraicClosure K₁, inferInstance, inferInstance, ?_, (algebraMap K₁ _).comp (Subfield.inclusion h),
    β.toRingHom, RingHom.ext fun x => β.commutes _, fun x =>
      ⟨algebraMap K₁ _ ⟨a x, Subfield.subset_closure (Or.inr ⟨x, rfl⟩)⟩, β.commutes _⟩⟩
  exact Cardinal.mk_le_aleph0_iff.1 ((Algebra.IsAlgebraic.cardinalMk_le_max K₁ _).trans (max_le c₁ le_rfl))

theorem exists_pre (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] {O : Type} [CommRing O] [StarRing O]
    [Module.Finite ℤ O] (D : DegPre K) (o : D.P.OAct O) :
    ∃ (F₁ : Type) (_ : Field F₁) (_ : IsAlgClosed F₁) (_ : Countable F₁) (β : F₁ →+* K) (D₁ : DegPre F₁)
      (hD : IsPullDeg β D₁ D) (o₁ : D₁.P.OAct O), ∀ a, (o.act a).left ≫ proj hD = proj hD ≫ (o₁.act a).left := by
  obtain ⟨n, gen, hgen⟩ := Module.Finite.exists_fin (R := ℤ) (M := O)
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := D.X)
  have hgen' : Subring.closure (Set.range gen) = ⊤ := top_le_iff.1 fun x _ => by
    have hx : x ∈ Submodule.span ℤ (Set.range gen) := hgen ▸ Submodule.mem_top
    rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure] at hx
    exact (AddSubgroup.closure_le (Subring.closure (Set.range gen)).toAddSubgroup).2 Subring.subset_closure hx
  have hb' : AddSubgroup.closure (Set.range b) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, hb]; rfl
  obtain ⟨K₀, P₀, Φ, a₀, x₀, hc, gp, hw, ha, hx⟩ :=
    GlobalTheory.T.polAV_descends_to_countable_subfield' K D.P (Fin n) (Fin m) (fun j => o.act (gen j)) (fun k => D.c (b k))
  obtain ⟨o₀, ho₀⟩ := GlobalTheory.T.polarisedRingAction_descend_of_generators O _ gen hgen' K₀ K _ P₀ D.P Φ gp hw o a₀ ha
  obtain ⟨c₀, hc₀, hc₁⟩ := GlobalTheory.T.additive_points_descend_field_extension K₀ K _ P₀ D.P Φ gp D.X _ b hb' D.c D.c_add x₀ hx
  obtain ⟨D₀, ψ, hψ, h₀, rfl, e⟩ := GlobalTheory.T.exists_degenerationPreData_over_subfield hL K₀ K _ D P₀ Φ gp hw c₀ hc₀ hc₁
  obtain rfl := eq_of_heq e
  obtain ⟨a, Ha⟩ := GlobalTheory.T.exists_ratio_descends_degenerationPsiFamily K D ψ hψ
  have : Countable D.X := Finsupp.Countable.of_moduleFinite (R := ℤ)
  obtain ⟨F₁, _, _, _, α, β, hαβ, hβ⟩ := exists_countable_closed K₀ a
  obtain ⟨D', h₁, -, -⟩ := DegPull.exists_isPullDeg hL.polBaseChange K₀ F₁ α D₀ ⊤ (nonempty_psiOn_field D₀) trivial
  generalize K₀.subtype = i at h₀ ho₀ hαβ
  subst hαβ
  obtain ⟨h₂, e₂⟩ := GlobalTheory.T.exists_pullDeg_cancel_tower_of_fields K₀ F₁ K α β D₀ D' _ h₁ h₀
  obtain ⟨ψ₁, hψ₁, hD, e₃⟩ := Ha F₁ β D' h₂ hβ
  obtain ⟨o₁, ho₁⟩ := polOActPull _ _ _ D₀.P D'.P _ (pull_grp h₁) (LBIso.symm ⟨h₁.w, h₁.w_gen⟩) O o₀
  refine ⟨F₁, inferInstance, inferInstance, inferInstance, β, _, hD, o₁, fun c => ?_⟩
  rw [e₃]
  refine (pull_grp h₁).1.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₂).trans ((ho₀ c).trans ((congrArg (· ≫ _) e₂.symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ho₁ c).symm).trans (Category.assoc _ _ _).symm)))))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pull_grp h₂).1.w).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (Over.w (o.act c))).trans ((pull_grp h₂).1.w.symm.trans
        ((congrArg (_ ≫ ·) (Over.w (o₁.act c)).symm).trans (Category.assoc _ _ _).symm)))))

theorem exists_data (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] {O : Type} [CommRing O] [StarRing O]
    [Module.Finite ℤ O] (D : DegPre K) [Module O D.X] (oa : D.OAct O) :
    ∃ (F₁ : Type) (_ : Field F₁) (_ : IsAlgClosed F₁) (_ : Countable F₁) (β : F₁ →+* K) (D₁ : DegPre F₁)
      (hD : IsPullDeg β D₁ D) (_ : Module O D₁.X) (oa₁ : D₁.OAct O), (∀ (a : O) y, hD.xe (a • y) = a • hD.xe y) ∧
      (∀ a, (oa.onB.act a).left ≫ proj hD = proj hD ≫ (oa₁.onB.act a).left) ∧ (D.PsiEven → D₁.PsiEven) ∧
      (D.TauBimult → D₁.TauBimult) ∧ ∀ w, TraceFormTwistIso D oa w → TraceFormTwistIso D₁ oa₁ w := by
  obtain ⟨F₁, _, _, _, β, D₁, hD, o₁, ho⟩ := exists_pre hL D oa.onB
  letI : Module O D₁.X := hD.xe.symm.module O
  have hx : ∀ (a : O) y, hD.xe (a • y) = a • hD.xe y := fun a y => by
    show _ = hD.xe (a • hD.xe.symm (hD.xe y))
    rw [AddEquiv.symm_apply_apply]
  obtain ⟨oa₁, rfl⟩ := GlobalTheory.T.exists_orderAction_descent_field_extension hL.globalFns F₁ K β D₁ D hD O o₁ oa hx ho
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.psiEven_tauBimult_descend_of_injective hL.globalFns F₁ K β β.injective D₁ D hD
  exact ⟨F₁, inferInstance, inferInstance, inferInstance, β, D₁, hD, inferInstance, oa₁, hx, ho, h₁, h₂,
    GlobalTheory.T.psi_relation_descends_field_extension hL.globalFns F₁ K β D₁ D hD O oa₁ oa hx ho⟩

end GlobalTheory.FieldPull
end
end
end
