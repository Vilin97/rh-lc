module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsProperSpreadsOutStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchemeModelsSpreadStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSpreadsOutStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameDivisorTrans
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutLineBundleStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothProperModelFinitelyGeneratedSubring

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.SmoothProperModel

theorem exists_smooth_proper_model : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f →
    ∃ (R : Subring k) (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Sp R) (π : X ⟶ X₀), Algebra.FiniteType ℤ R ∧ Smooth f₀ ∧
      IsProper f₀ ∧ IsPullback π f f₀ (spMap R.subtype) := by
  intro k _ X f hsm hpr
  obtain ⟨R₀, _, φ, X₀, f₀, π, hm⟩ := GlobalTheory.T.scheme_models_spread k X f inferInstance inferInstance inferInstance
  obtain ⟨R₁, _, ψ₁, φ₁, e₁, ft₁, sm₁⟩ := GlobalTheory.T.smooth_spreads_out k R₀ φ X X₀ f f₀ π hm hsm
  have m₁ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₁ ft₁ hm
  obtain ⟨R₂, _, ψ₂, φ₂, e₂, ft₂, pr₂⟩ := GlobalTheory.T.isProper_spreads_out k R₁ φ₁ X _ f _ _ m₁ hpr
  have m₂ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₂ ft₂ m₁
  have sm₁' : Smooth (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁))) := sm₁
  have pr₂' : IsProper (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := pr₂
  have sm₂' : Smooth (pullback.snd (pullback.snd f₀ (Spec.map (CommRingCat.ofHom ψ₁)))
      (Spec.map (CommRingCat.ofHom ψ₂))) := inferInstance
  let ψ₃ : R₂ →+* φ₂.range := φ₂.rangeRestrict
  have e₃ : φ₂.range.subtype.comp ψ₃ = φ₂ := by ext x; rfl
  have ft₃ : Algebra.FiniteType ℤ φ₂.range :=
    haveI := ft₂
    Algebra.FiniteType.of_surjective ψ₃.toIntAlgHom φ₂.rangeRestrict_surjective
  have m₃ := GlobalTheory.CompanionTheory.CubeModels.model_refine' e₃ ft₃ m₂
  exact ⟨φ₂.range, _, _, _, ft₃, inferInstance, inferInstance, m₃.2.2.2.2⟩

end GlobalTheory.SmoothProperModel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothProperModelFinitelyGeneratedSubringStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_smooth_proper_model_finitelyGenerated_subring : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f → ∃ (R : Subring k) (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Sp R) (π : X ⟶ X₀), Algebra.FiniteType ℤ R ∧ Smooth f₀ ∧ IsProper f₀ ∧ IsPullback π f f₀ (spMap R.subtype) := by
  first | exact @GlobalTheory.SmoothProperModel.exists_smooth_proper_model | exact GlobalTheory.SmoothProperModel.exists_smooth_proper_model | (intros; apply GlobalTheory.SmoothProperModel.exists_smooth_proper_model <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsHaveSameZeroSchemeOfLineBundleIso

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem exists_sameDiv_of_lbIso : ∀ (X : Scheme.{0}) (L M : LB X) (σ : L.Sec), L.IsLB → M.IsLB → LBIso L M →
    ∃ τ : M.Sec, SameDiv σ τ := by
  intro X L M σ hL hM h
  obtain ⟨u, hu⟩ := LBIso.symm h
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.secOfIso (u := u) σ hu hM hL, fun x => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x))
  refine ⟨M.U j ⊓ L.U i, i, j, inf_le_right, inf_le_left,
    ReciprocityTheory.ChartRestriction.G.Semi.res (ReciprocityTheory.ChartRestriction.G.DVR.divLe j i) (u.s (i, j)), ⟨hj, hi⟩, ?_⟩
  have e := ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec (u := u) σ hu hM hL j i
  unfold ReciprocityTheory.ChartRestriction.G.DVR.isoCand at e
  change _ = _ * (ReciprocityTheory.ChartRestriction.G.DVR.rs (inf_le_left : M.U j ⊓ L.U i ≤ M.U j)
    ((ReciprocityTheory.ChartRestriction.G.DVR.secOfIso (u := u) σ hu hM hL).f j))
  rw [e, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

end GlobalTheory.LogPair
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsHaveSameZeroSchemeOfLineBundleIsoStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_sectionsHaveSameZeroScheme_of_lineBundleIso : ∀ (X : Scheme.{0}) (L M : LB X) (σ : L.Sec), L.IsLB → M.IsLB → LBIso L M → ∃ τ : M.Sec, SameDiv σ τ := by
  first | exact @GlobalTheory.LogPair.exists_sameDiv_of_lbIso | exact GlobalTheory.LogPair.exists_sameDiv_of_lbIso | (intros; apply GlobalTheory.LogPair.exists_sameDiv_of_lbIso <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SameDivisorTrans

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.same_divisor_trans : ∀ (X : Scheme.{0}) (L M N : LB X) (σ : L.Sec) (τ : M.Sec) (υ : N.Sec), M.IsLB → SameDiv σ τ → SameDiv τ υ → SameDiv σ υ := by
  first | exact @_root_.GlobalTheory.LogPair.SameDiv.trans_of_isLB | exact _root_.GlobalTheory.LogPair.SameDiv.trans_of_isLB | (intros; apply _root_.GlobalTheory.LogPair.SameDiv.trans_of_isLB <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutMorphism

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.SecDescent

theorem lbSec_descends_to_subring : ∀ (k : Type) [Field k] (R₀ : Subring k) (X X₀ : Scheme.{0}) (f : X ⟶ Sp k) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [IsProper f₀] (L : LB X) (hL : L.IsLB) (σ : L.Sec), IsPullback π f f₀ (spMap R₀.subtype) → ∃ F : Finset k, ∀ (R₁ : Subring k) (hR : R₀ ≤ R₁), (F : Set k) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hR)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ (L₁ : LB X₁) (h₁ : L₁.IsLB) (σ₁ : L₁.Sec), cls L hL = CechPic.pull j (cls L₁ h₁) ∧ SameDiv σ (Cartier.secPull σ₁ j) := by
  intro k _ R₀ X X₀ f f₀ π _ L hL σ hp
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring k R₀ X X₀ f f₀ π L hp hL
  let R' : Subring k := R₀ ⊔ Subring.closure (S : Set k)
  have h' : R₀ ≤ R' := le_sup_left
  have hs' : (S : Set k) ⊆ R' := fun x hx => (le_sup_right : _ ≤ R') (Subring.subset_closure hx)
  let a : Sp R' ⟶ Sp R₀ := spMap (Subring.inclusion h')
  have e₁ : spMap R'.subtype ≫ a = spMap R₀.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have PX' := IsPullback.of_hasPullback f₀ a
  let j' : X ⟶ pullback f₀ a := PX'.lift π (f ≫ spMap R'.subtype) (by rw [Category.assoc, e₁, hp.w])
  have hj₁ : j' ≫ pullback.fst f₀ a = π := PX'.lift_fst _ _ _
  have hj₂ : j' ≫ pullback.snd f₀ a = f ≫ spMap R'.subtype := PX'.lift_snd _ _ _
  obtain ⟨L', hL', hI⟩ := hS R' h' hs' _ _ _ j' PX' hj₁ hj₂
  have hLj : (L'.pull j').IsLB := LB.isLB_pull hL' j'
  obtain ⟨τ, hστ⟩ := GlobalTheory.T.exists_sectionsHaveSameZeroScheme_of_lineBundleIso X L (L'.pull j') σ hL hLj hI
  have QX : IsPullback j' f (pullback.snd f₀ a) (spMap R'.subtype) :=
    IsPullback.of_right (by rw [hj₁, e₁]; exact hp) hj₂ PX'
  obtain ⟨F₂, hF₂⟩ := GlobalTheory.T.spread_out_line_bundle k R' X (pullback f₀ a) f (pullback.snd f₀ a) j' L' τ QX hL'
  refine ⟨S ∪ F₂, fun R₁ hR hs X₁ f₁ π₁ j hp₁ hjπ hjf => ?_⟩
  rw [Finset.coe_union, Set.union_subset_iff] at hs
  have hle : R' ≤ R₁ := sup_le hR (Subring.closure_le.2 hs.1)
  let b : Sp R₁ ⟶ Sp R' := spMap (Subring.inclusion hle)
  have e₂ : b ≫ a = spMap (Subring.inclusion hR) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have e₃ : spMap R₁.subtype ≫ b = spMap R'.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let q : X₁ ⟶ pullback f₀ a := PX'.lift π₁ (f₁ ≫ b) (by rw [Category.assoc, e₂, hp₁.w])
  have hq₁ : q ≫ pullback.fst f₀ a = π₁ := PX'.lift_fst _ _ _
  have hq₂ : q ≫ pullback.snd f₀ a = f₁ ≫ b := PX'.lift_snd _ _ _
  have QX₁ : IsPullback q f₁ (pullback.snd f₀ a) b :=
    IsPullback.of_right (by rw [hq₁, e₂]; exact hp₁) hq₂ PX'
  have hjq : j ≫ q = j' := by
    apply PX'.hom_ext
    · rw [Category.assoc, hq₁, hjπ, hj₁]
    · rw [Category.assoc, hq₂, reassoc_of% hjf, e₃, hj₂]
  obtain ⟨τ₁, hτ₁⟩ := hF₂ R₁ hle hs.2 X₁ f₁ q j QX₁ hjq hjf
  refine ⟨L'.pull q, LB.isLB_pull hL' q, τ₁, ?_, GlobalTheory.T.same_divisor_trans X L (L'.pull j') _ σ τ _ hLj hστ hτ₁⟩
  rw [(CechPic.cls_eq_iff hL hLj).2 hI, CechPic.cls_pull hL' j' hLj, CechPic.cls_pull hL' q, ← hjq,
    CechPic.pull_comp]

end GlobalTheory.SecDescent
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutMorphismStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.spread_out_line_bundle_section : ∀ (k : Type) [Field k] (R₀ : Subring k) (X X₀ : Scheme.{0}) (f : X ⟶ Sp k) (f₀ : X₀ ⟶ Sp R₀) (π : X ⟶ X₀) [IsProper f₀] (L : LB X) (hL : L.IsLB) (σ : L.Sec), IsPullback π f f₀ (spMap R₀.subtype) → ∃ F : Finset k, ∀ (R₁ : Subring k) (hR : R₀ ≤ R₁), (F : Set k) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hR)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ (L₁ : LB X₁) (h₁ : L₁.IsLB) (σ₁ : L₁.Sec), cls L hL = CechPic.pull j (cls L₁ h₁) ∧ SameDiv σ (Cartier.secPull σ₁ j) := by
  first | exact @_root_.GlobalTheory.SecDescent.lbSec_descends_to_subring | exact _root_.GlobalTheory.SecDescent.lbSec_descends_to_subring | (intros; apply _root_.GlobalTheory.SecDescent.lbSec_descends_to_subring <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutSmoothProper

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem exists_finiteType_subring_ge_finset {k : Type} [CommRing k] (R₀ : Subring k)
    (h : Algebra.FiniteType ℤ R₀) (F : Finset k) :
    ∃ R : Subring k, R₀ ≤ R ∧ (F : Set k) ⊆ R ∧ Algebra.FiniteType ℤ R := by
  have h0 : (subalgebraOfSubring R₀).FG := (Subalgebra.fg_iff_finiteType _).2 h
  have h1 : (subalgebraOfSubring R₀ ⊔ Algebra.adjoin ℤ (F : Set k)).FG :=
    h0.sup (Subalgebra.fg_adjoin_finset F)
  refine ⟨(subalgebraOfSubring R₀ ⊔ Algebra.adjoin ℤ (F : Set k)).toSubring, ?_, ?_,
    (Subalgebra.fg_iff_finiteType _).1 h1⟩
  · intro x hx
    exact (le_sup_left : subalgebraOfSubring R₀ ≤ _) hx
  · intro x hx
    exact (le_sup_right : Algebra.adjoin ℤ (F : Set k) ≤ _) (Algebra.subset_adjoin hx)

theorem exists_model_with_sections : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : ∀ i, (L i).IsLB) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : ∀ i, (L₁ i).IsLB) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ Smooth f₁ ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h i) = CechPic.pull π (cls (L₁ i) (h₁ i))) ∧ (∀ i, SameDiv (σ i) (Cartier.secPull (σ₁ i) π)) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  classical
  intro k _ X f hsm hpr s L σ h M hM
  obtain ⟨R₀, X₀, f₀, π₀, hft, hsm₀, hpr₀, hpb⟩ := GlobalTheory.T.exists_smooth_proper_model_finitelyGenerated_subring k X f hsm hpr
  choose F hF using fun i => GlobalTheory.T.spread_out_line_bundle_section k R₀ X X₀ f f₀ π₀ (L i) (h i) (σ i) hpb
  obtain ⟨G, hG⟩ := GlobalTheory.T.spread_out_line_bundle_section k R₀ X X₀ f f₀ π₀ M hM 0 hpb
  obtain ⟨R, hR, hFR, hRft⟩ :=
    exists_finiteType_subring_ge_finset R₀ hft (G ∪ Finset.univ.biUnion F)
  have hsp : spMap R.subtype ≫ spMap (Subring.inclusion hR) = spMap R₀.subtype := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  have P := IsPullback.of_hasPullback f₀ (spMap (Subring.inclusion hR))
  let j : X ⟶ pullback f₀ (spMap (Subring.inclusion hR)) :=
    pullback.lift π₀ (f ≫ spMap R.subtype) (by rw [Category.assoc, hsp, hpb.w])
  have hj1 : j ≫ pullback.fst _ _ = π₀ := pullback.lift_fst _ _ _
  have hj2 : j ≫ pullback.snd _ _ = f ≫ spMap R.subtype := pullback.lift_snd _ _ _
  have hGR : (G : Set k) ⊆ R := fun x hx => hFR (by
    simp only [Finset.coe_union, Set.mem_union]; exact Or.inl hx)
  have hFi : ∀ i, (F i : Set k) ⊆ R := fun i x hx => hFR (by
    rw [Finset.mem_coe, Finset.mem_union]
    exact Or.inr (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩))
  choose L₁ h₁ σ₁ hc hd using fun i => hF i R hR (hFi i) _ _ _ j P hj1 hj2
  obtain ⟨M₁, hM₁, -, hMc, -⟩ := hG R hR hGR _ _ _ j P hj1 hj2
  refine ⟨R, _, pullback.snd f₀ (spMap (Subring.inclusion hR)), j, L₁, σ₁, h₁, M₁, hM₁, hRft,
    inferInstance, inferInstance, ?_, hc, hd, hMc⟩
  exact IsPullback.of_right (by rw [hj1, hsp]; exact hpb) hj2 P

end GlobalTheory.LogPair
end
end
