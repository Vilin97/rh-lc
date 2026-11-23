module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfRelSncDivisorStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RelativeSncGenericSpreadStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenRestrictAffineOpenStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutSmoothProper
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeSncSameDivisor

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPair

theorem resG_resG' {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (z : Γ(X, U)) :
    resG X h2 (resG X h1 z) = resG X (h2.trans h1) z := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem resG_elim {X : Scheme.{0}} {U W : X.Opens} (h : W ≤ U) {d : ℕ} (t : Fin d → Γ(X, U))
    (o : Option (Fin d)) : resG X h (o.elim 1 t) = o.elim 1 (fun a => resG X h (t a)) := by
  cases o <;> simp

theorem relSnc_of_sameDiv : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (d : ℕ) (s : ℕ)
    (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (L' : Fin s → LB X) (σ' : ∀ i, (L' i).Sec),
    RelSnc f d L σ → (∀ i, (L' i).IsLB) → (∀ i, SameDiv (σ i) (σ' i)) → RelSnc f d L' σ' := by
  intro R _ X f d s L σ L' σ' hR hL' hS
  refine ⟨hL', fun x => ?_⟩
  obtain ⟨C, hxC⟩ := hR.chart x
  choose U a b ha hb v hxU hv using fun i => hS i x
  let V : X.Opens := C.U ⊓ ⟨⋂ i, (U i : Set X), isOpen_iInter_of_finite fun i => (U i).isOpen⟩
  have hxV : x ∈ V := ⟨hxC, Set.mem_iInter.2 hxU⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  have hWC : W ≤ C.U := fun y hy => (hWV hy).1
  have hWU : ∀ i, W ≤ U i := fun i y hy => Set.mem_iInter.1 (hWV hy).2 i
  have hWca : ∀ i, W ≤ (L i).U (C.c i) ⊓ (L i).U (a i) := fun i => le_inf (hWC.trans (C.le i)) ((hWU i).trans (ha i))
  let G : ∀ i, Γ(X, W)ˣ := fun i => Units.map (resG X (hWca i)).toMonoidHom ((L i).g (C.c i) (a i)) *
    Units.map (resG X (hWU i)).toMonoidHom (v i)
  refine ⟨{
    U := W
    affine := hW
    t := fun j => resG X hWC (C.t j)
    etale := GlobalTheory.T.isEtaleCoordinatesOnOpen_restrict_affineOpen R X f C.U W hWC d C.t C.affine hW C.etale
    c := b
    le := fun i => (hWU i).trans (hb i)
    e := C.e
    inj := C.inj
    u := fun i => Units.map (resG X hWC).toMonoidHom (C.u i) * (G i)⁻¹
    eq := fun i => ?_ }, hxW⟩

  have h1 := congrArg (resG X hWC) (C.eq i)
  rw [resG_resG', map_mul, resG_elim] at h1

  have h2 := congrArg (resG X (hWca i)) ((σ i).compat (C.c i) (a i))
  simp only [resG_resG', map_mul] at h2

  have h3 := congrArg (resG X (hWU i)) (hv i)
  simp only [resG_resG', map_mul] at h3
  have hG : (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * (G i : Γ(X, W)) = 1 := Units.inv_mul _
  have hG' : (G i : Γ(X, W)) = resG X (hWca i) ((L i).g (C.c i) (a i) : Γ(X, (L i).U (C.c i) ⊓ (L i).U (a i))) *
      resG X (hWU i) (v i : Γ(X, U i)) := by
    simp only [G, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  show _ = ((Units.map (resG X hWC).toMonoidHom (C.u i) * (G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * _
  rw [Units.val_mul, Units.coe_map]
  rw [hG'] at hG
  linear_combination (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * h1 - (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * h2
    - (((G i)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) * resG X (hWca i) ((L i).g (C.c i) (a i) : Γ(X, (L i).U (C.c i) ⊓ (L i).U (a i))) * h3
    - resG X (le_trans (hWU i) (hb i)) ((σ' i).f (b i)) * hG

end GlobalTheory.LogPair
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RelativeSncSameDivisor

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.relative_snc_same_divisor : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (L' : Fin s → LB X) (σ' : ∀ i, (L' i).Sec), RelSnc f d L σ → (∀ i, (L' i).IsLB) → (∀ i, SameDiv (σ i) (σ' i)) → RelSnc f d L' σ' := by
  first | exact @_root_.GlobalTheory.LogPair.relSnc_of_sameDiv | exact _root_.GlobalTheory.LogPair.relSnc_of_sameDiv | (intros; apply _root_.GlobalTheory.LogPair.relSnc_of_sameDiv <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutSmoothProperStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.spread_out_smooth_proper : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : ∀ i, (L i).IsLB) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : ∀ i, (L₁ i).IsLB) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ Smooth f₁ ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h i) = CechPic.pull π (cls (L₁ i) (h₁ i))) ∧ (∀ i, SameDiv (σ i) (Cartier.secPull (σ₁ i) π)) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  first | exact @_root_.GlobalTheory.LogPair.exists_model_with_sections | exact _root_.GlobalTheory.LogPair.exists_model_with_sections | (intros; apply _root_.GlobalTheory.LogPair.exists_model_with_sections <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutRelativeSnc

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ModelSnc

def adjInv {k : Type} [Field k] (R : Subring k) (a : k) : Subring k :=
  (Polynomial.eval₂RingHom R.subtype a⁻¹).range

def toAdjInv {k : Type} [Field k] (R : Subring k) (a : k) : R →+* adjInv R a :=
  (Polynomial.eval₂RingHom R.subtype a⁻¹).rangeRestrict.comp Polynomial.C

theorem subtype_comp_toAdjInv {k : Type} [Field k] (R : Subring k) (a : k) :
    (adjInv R a).subtype.comp (toAdjInv R a) = R.subtype := by
  ext r
  change Polynomial.eval₂ R.subtype a⁻¹ (Polynomial.C r) = (r : k)
  simp

theorem isUnit_toAdjInv {k : Type} [Field k] (R : Subring k) (a : R) (ha : (a : k) ≠ 0) :
    IsUnit (toAdjInv R (a : k) a) := by
  refine IsUnit.of_mul_eq_one ((Polynomial.eval₂RingHom R.subtype (a : k)⁻¹).rangeRestrict Polynomial.X) ?_
  apply Subtype.ext
  change Polynomial.eval₂ R.subtype (a : k)⁻¹ (Polynomial.C a) * Polynomial.eval₂ R.subtype (a : k)⁻¹ Polynomial.X = 1
  simp [ha]

theorem finiteType_adjInv {k : Type} [Field k] (R : Subring k) (hR : Algebra.FiniteType ℤ R) (a : k) :
    Algebra.FiniteType ℤ (adjInv R a) := by
  haveI := hR
  have hP : Algebra.FiniteType ℤ (Polynomial R) := inferInstance
  exact @Algebra.FiniteType.of_surjective _ _ _ _ _ _ _ _ hP
    (Polynomial.eval₂RingHom R.subtype a⁻¹).rangeRestrict.toIntAlgHom
    (Polynomial.eval₂RingHom R.subtype a⁻¹).rangeRestrict_surjective

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.ModelSnc

end

namespace GlobalTheory.ModelSnc

theorem exists_model_relSnc : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ), IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : RelSnc f₁ d L₁ σ₁) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h.isLB i) = CechPic.pull π (cls (L₁ i) (h₁.isLB i))) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  intro k _ X f d hf s L σ h M hM
  haveI : SmoothOfRelativeDimension d f := GlobalTheory.T.smoothOfRelativeDimension_of_relSncDivisor k X f d s L σ h
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth d f
  obtain ⟨R, X₁, f₁, π, L₁, σ₁, h₁, M₁, hM₁, hR, hsm₁, hpr₁, hpb, hcl, hsame, hclM⟩ :=
    GlobalTheory.T.spread_out_smooth_proper k X f hsm hf s L σ h.isLB M hM
  have hX : RelSnc f d (fun i => (L₁ i).pull π) (fun i => Cartier.secPull (σ₁ i) π) :=
    GlobalTheory.T.relative_snc_same_divisor k X f d s L σ _ _ h (fun i => pull_isLB (h₁ i) π) hsame
  haveI := hsm₁
  haveI := hpr₁
  obtain ⟨a, ha, hsp⟩ := GlobalTheory.T.relative_snc_generic_spread R k R.subtype X₁ X f₁ f π d s L₁ σ₁ hpb h₁ hX
  set R' := adjInv R (a : k)
  set χ := toAdjInv R (a : k)
  have hχ : IsUnit (χ a) := isUnit_toAdjInv R a ha
  let g : pullback f₁ (spMap χ) ⟶ Sp R' := pullback.snd f₁ (spMap χ)
  let ρ : pullback f₁ (spMap χ) ⟶ X₁ := pullback.fst f₁ (spMap χ)
  have hρ : IsPullback ρ g f₁ (spMap χ) := IsPullback.of_hasPullback f₁ (spMap χ)
  have hZ := hsp R' χ hχ _ g ρ hρ
  have hcomp : spMap R.subtype = spMap R'.subtype ≫ spMap χ := by
    rw [← spMap_comp, subtype_comp_toAdjInv]
  have hw : π ≫ f₁ = (f ≫ spMap R'.subtype) ≫ spMap χ := by
    rw [Category.assoc, ← hcomp]; exact hpb.w
  let π' : X ⟶ pullback f₁ (spMap χ) := pullback.lift π (f ≫ spMap R'.subtype) hw
  have hπ' : π' ≫ ρ = π := pullback.lift_fst _ _ _
  have hg' : π' ≫ g = f ≫ spMap R'.subtype := pullback.lift_snd _ _ _
  have hpb' : IsPullback π' f g (spMap R'.subtype) := by
    refine IsPullback.of_right ?_ hg' hρ
    rw [hπ', ← hcomp]; exact hpb
  haveI : IsProper g := inferInstance
  refine ⟨R', pullback f₁ (spMap χ), g, π', fun i => (L₁ i).pull ρ, fun i => Cartier.secPull (σ₁ i) ρ, hZ,
    M₁.pull ρ, pull_isLB hM₁ ρ, finiteType_adjInv R hR _, inferInstance, hpb', fun i => ?_, ?_⟩
  · rw [hcl i, ← hπ', pull_comp]; rfl
  · rw [hclM, ← hπ', pull_comp]; rfl

end GlobalTheory.ModelSnc
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutRelativeSncStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.spread_out_relative_snc : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ), IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : RelSnc f₁ d L₁ σ₁) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h.isLB i) = CechPic.pull π (cls (L₁ i) (h₁.isLB i))) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  first | exact @_root_.GlobalTheory.ModelSnc.exists_model_relSnc | exact _root_.GlobalTheory.ModelSnc.exists_model_relSnc | (intros; apply _root_.GlobalTheory.ModelSnc.exists_model_relSnc <;> assumption)
end
end
