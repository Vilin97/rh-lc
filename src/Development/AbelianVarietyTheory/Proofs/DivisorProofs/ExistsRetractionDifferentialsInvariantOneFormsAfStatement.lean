module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedHomAlgebraMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLawTranslateDerivationInvariantFormsStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInvariantOneFormsAffineOpenAbelianSchemeEqToStatement
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.AlgebraicGeometry.QuasiAffine

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormEqZeroOfAffineCoverRestrictions

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoverForms

open KaehlerDifferential

theorem exists_pow_smul_eq_zero {R C B : Type} [CommRing R] [CommRing C] [CommRing B]
    [Algebra R C] [Algebra R B] (g : C →ₐ[R] B) (f : C)
    (hloc : @IsLocalization.Away C _ f B _ g.toRingHom.toAlgebra)
    (L : Ω[C⁄R] →ₗ[R] Ω[B⁄R]) (hD : ∀ c, L (D R C c) = D R B (g c))
    (hs : ∀ (c : C) (α : Ω[C⁄R]), L (c • α) = g c • L α)
    (α : Ω[C⁄R]) (h : L α = 0) : ∃ m : ℕ, f ^ m • α = 0 := by
  letI : Algebra C B := g.toRingHom.toAlgebra
  haveI : IsScalarTower R C B := IsScalarTower.of_algebraMap_eq (fun r => (g.commutes r).symm)
  have hL : ∀ β, L β = KaehlerDifferential.map R R C B β := by
    intro β
    have hβ : β ∈ Submodule.span C (Set.range (D R C)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hβ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      rw [hD, KaehlerDifferential.map_D]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | smul c x _ hx =>
      rw [hs, hx, (KaehlerDifferential.map R R C B).map_smul]
      exact algebraMap_smul B c _
  haveI := KaehlerDifferential.isLocalizedModule_map R C B (Submonoid.powers f)
  have h' : KaehlerDifferential.map R R C B α = KaehlerDifferential.map R R C B 0 := by
    rw [← hL, h, map_zero]
  obtain ⟨⟨c, hc⟩, hc0⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) h'
  obtain ⟨m, rfl⟩ := hc
  refine ⟨m, ?_⟩
  simpa [Submonoid.smul_def] using hc0

theorem eq_zero_of_cover : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), CompactSpace X → ∃ (n : ℕ) (V : Fin n → AffOp X), ∀ w : GlobForm s, (∀ k, evForm s (V k) w = 0) → w = 0 := by
  intro R _ X s hX
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hxU⟩)
  refine ⟨t.card, fun k => Opposite.op (t.equivFin.symm k).1, fun w hw => ?_⟩
  have hcov : ∀ x : X, ∃ U ∈ t, x ∈ (U.1 : Set X) := fun x => by
    simpa using ht (Set.mem_univ x)
  have hV0 : ∀ U ∈ t, w.1 (Opposite.op U) = 0 := fun U hU => by
    have : evForm s (Opposite.op (t.equivFin.symm (t.equivFin ⟨U, hU⟩)).1) w = 0 := hw _
    have e : t.equivFin.symm (t.equivFin ⟨U, hU⟩) = ⟨U, hU⟩ := Equiv.symm_apply_apply _ _
    rw [e] at this
    exact this
  apply Subtype.ext
  funext W
  obtain ⟨W₀⟩ := W
  have hW : IsAffineOpen W₀.1 := W₀.2
  let S : Set Γ(X, W₀.1) := {f | ∃ U ∈ t, X.basicOpen f ≤ U.1}
  have hS : Ideal.span S = ⊤ := by
    rw [← hW.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun f => X.basicOpen_le _) ?_
    intro x hx
    obtain ⟨U, hU, hxU⟩ := hcov x
    obtain ⟨f, hf, hxf⟩ := hW.exists_basicOpen_le (V := U.1) ⟨x, hxU⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, U, hU, hf⟩, hxf⟩
  let α : Ω[Sec s W₀.1⁄R] := w.1 (Opposite.op W₀)
  let I : Ideal (Sec s W₀.1) := LinearMap.ker (LinearMap.toSpanSingleton (Sec s W₀.1) _ α)
  have hrad : ∀ f ∈ S, f ∈ I.radical := by
    rintro f ⟨U, hU, hf⟩
    let D' : X.affineOpens := ⟨X.basicOpen f, hW.basicOpen f⟩
    let φ : (Opposite.op W₀ : AffOp X) ⟶ Opposite.op D' := (homOfLE (X.basicOpen_le f)).op
    let ψ : (Opposite.op U : AffOp X) ⟶ Opposite.op D' := (homOfLE hf).op
    have h0 : p1 (OAff s) φ α = 0 := by
      have e1 := w.2 φ
      have e2 := w.2 ψ
      rw [hV0 U hU, map_zero] at e2
      exact e1.symm.trans e2
    obtain ⟨m, hm⟩ := exists_pow_smul_eq_zero (mp (OAff s) φ) f
      (hW.isLocalization_basicOpen f) (p1 (OAff s) φ) (p1_D (OAff s) φ) (oneFormsMapOfFunctorMorphism_smul (OAff s) φ) α h0
    exact ⟨m, by simpa [I] using hm⟩
  have hI : I = ⊤ := by
    rw [← Ideal.radical_eq_top, eq_top_iff]
    have h2 := Ideal.span_le.2 hrad
    exact (show (⊤ : Ideal (Sec s W₀.1)) ≤ Ideal.span S from hS.ge).trans h2
  have h1 : (1 : Sec s W₀.1) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

end GlobalTheory.CoverForms
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormEqZeroOfAffineCoverRestrictionsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_finite_affineCover_globalForm_eq_zero_of_restrictions : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), CompactSpace X → ∃ (n : ℕ) (V : Fin n → AffOp X), ∀ w : GlobForm s, (∀ k, evForm s (V k) w = 0) → w = 0 := by
  first | exact @GlobalTheory.CoverForms.eq_zero_of_cover | exact GlobalTheory.CoverForms.eq_zero_of_cover | (intros; apply GlobalTheory.CoverForms.eq_zero_of_cover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorKaehlerEqZeroOfDerivationsVanish

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tensor_kaehler_eq_zero_of_derivations_vanish :
  ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C], Module.Projective C Ω[C⁄R] → ∀ z : B ⊗[R] Ω[C⁄R], (∀ θ : Ω[C⁄R] →ₗ[R] B ⊗[R] C, (∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) → LinearMap.liftBaseChange B θ z = 0) → z = 0 := by
  intro R B C _ _ _ _ _ hP z hz
  classical
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := C) (P := Ω[C⁄R])).1 hP
  let π : (Ω[C⁄R] →₀ C) →ₗ[C] Ω[C⁄R] := Finsupp.linearCombination C id
  have hcomp : (LinearMap.lTensor B (π.restrictScalars R)) ∘ₗ (LinearMap.lTensor B (s.restrictScalars R))
      = LinearMap.id := by
    rw [← LinearMap.lTensor_comp]
    have : (π.restrictScalars R) ∘ₗ (s.restrictScalars R) = LinearMap.id := by
      exact LinearMap.ext fun x => LinearMap.congr_fun hs x
    rw [this, LinearMap.lTensor_id]
  have key : LinearMap.lTensor B (s.restrictScalars R) z = 0 := by
    apply (TensorProduct.finsuppRight R R B C Ω[C⁄R]).injective
    rw [map_zero]
    ext i
    let θ : Ω[C⁄R] →ₗ[R] B ⊗[R] C :=
      (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := C)).toLinearMap ∘ₗ
        ((Finsupp.lapply (R := C) (M := C) i).restrictScalars R ∘ₗ s.restrictScalars R)
    have hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x := by
      intro c x
      simp [θ, Algebra.TensorProduct.tmul_mul_tmul]
    have h1 := hz θ hθ
    have heq : ∀ w : B ⊗[R] Ω[C⁄R], (TensorProduct.finsuppRight R R B C Ω[C⁄R]
        (LinearMap.lTensor B (s.restrictScalars R) w)) i = LinearMap.liftBaseChange B θ w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul b x =>
        simp [θ, TensorProduct.finsuppRight_apply_tmul_apply, LinearMap.liftBaseChange_tmul,
          TensorProduct.smul_tmul']
      | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]
    rw [heq, h1]; rfl
  have := congrArg (fun f => f z) hcomp
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
  rw [← this, key, map_zero]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorKaehlerEqZeroOfDerivationsVanishStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.eq_zero_of_liftBaseChange_derivations_eq_zero : ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C], Module.Projective C Ω[C⁄R] → ∀ z : B ⊗[R] Ω[C⁄R], (∀ θ : Ω[C⁄R] →ₗ[R] B ⊗[R] C, (∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) → LinearMap.liftBaseChange B θ z = 0) → z = 0 := by
  first | exact @GlobalTheory.tensor_kaehler_eq_zero_of_derivations_vanish | exact GlobalTheory.tensor_kaehler_eq_zero_of_derivations_vanish | (intros; apply GlobalTheory.tensor_kaehler_eq_zero_of_derivations_vanish <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionDifferentialsInvariantOneFormsAf

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.InvForm

namespace GlobalTheory.InvFormRetract

theorem dVal_smul {R B D : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing D] [Algebra R D] (φ : B →ₐ[R] DualNumber D) (b : B) (x : Ω[B⁄R]) : dVal φ (b • x) = redHom φ b * dVal φ x := by
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  unfold dVal
  simp only [LinearMap.restrictScalars_apply, LinearMap.map_smul]
  rfl

theorem injective_baseChange {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (hab : IsAbelianScheme A) (U : AffOp A.left) :
    Function.Injective (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype)) := by
  haveI : Smooth A.hom := hab.smooth
  haveI : IsProper A.hom := hab.proper
  haveI : CompactSpace A.left := ⟨by simpa using QuasiCompact.isCompact_preimage (f := A.hom) Set.univ isOpen_univ isCompact_univ⟩
  haveI : Algebra.Smooth R (Sec A.hom U.unop.1) := smooth_sec_affine A.hom U.unop
  haveI : Module.Flat R (Sec A.hom U.unop.1) := Algebra.Smooth.flat R _
  obtain ⟨n, V, hV⟩ := GlobalTheory.T.exists_finite_affineCover_globalForm_eq_zero_of_restrictions R A.left A.hom inferInstance
  let f : ∀ k, InvForm A →ₗ[R] Ω[Sec A.hom (V k).unop.1⁄R] := fun k => evForm A.hom (V k) ∘ₗ (InvForm A).subtype
  let F : InvForm A →ₗ[R] ((k : Fin n) → Ω[Sec A.hom (V k).unop.1⁄R]) := LinearMap.pi f
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (hV w.1 fun k => congrFun hw k)
  have hFB : Function.Injective (LinearMap.lTensor (Sec A.hom U.unop.1) F) :=
    Module.Flat.lTensor_preserves_injective_linearMap F hF
  have hk : ∀ (k : Fin n) (z : Sec A.hom U.unop.1 ⊗[R] InvForm A), TensorProduct.piRight R R (Sec A.hom U.unop.1) (fun k : Fin n => Ω[Sec A.hom (V k).unop.1⁄R])
      (LinearMap.lTensor (Sec A.hom U.unop.1) F z) k = LinearMap.lTensor (Sec A.hom U.unop.1) (f k) z := by
    intro k z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b w => simp [F]
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  apply hFB
  rw [map_zero]
  apply (TensorProduct.piRight R R (Sec A.hom U.unop.1) (fun k : Fin n => Ω[Sec A.hom (V k).unop.1⁄R])).injective
  rw [map_zero]
  funext k
  rw [hk, Pi.zero_apply]
  haveI : Algebra.Smooth R (Sec A.hom (V k).unop.1) := smooth_sec_affine A.hom (V k).unop
  refine GlobalTheory.T.eq_zero_of_liftBaseChange_derivations_eq_zero R (Sec A.hom U.unop.1) _ inferInstance _ (fun θ hθ => ?_)
  obtain ⟨ψ, hfst, hψ⟩ := GlobalTheory.T.exists_groupLawTranslate_derivation_invariantForms R A U (V k) θ hθ
  have key : ∀ y, LinearMap.liftBaseChange (Sec A.hom U.unop.1) θ (LinearMap.lTensor (Sec A.hom U.unop.1) (f k) y) =
      dVal ψ (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b w =>
      rw [LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, dVal_smul]
      have h1 : redHom ψ b = b ⊗ₜ 1 := hfst b
      rw [h1, Algebra.smul_def]
      simp only [f, LinearMap.comp_apply, Submodule.subtype_apply, hψ]
      rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [key, hz, map_zero]

theorem retract : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left, ∃ r : Ω[Sec A.hom U.unop.1⁄R] →ₗ[Sec A.hom U.unop.1] (Sec A.hom U.unop.1 ⊗[R] GlobalTheory.InvForm.InvForm A), ∀ w : GlobalTheory.InvForm.InvForm A, r (evForm A.hom U w.1) = 1 ⊗ₜ w := by
  intro R _ A _ g hab hdim U
  have hsurj : Function.Surjective (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype)) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← GlobalTheory.T.span_invariantOneForms_affineOpen_abelianScheme_eq_top R A g hab hdim U, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact ⟨1 ⊗ₜ w, by simp⟩
  let e := LinearEquiv.ofBijective _ ⟨injective_baseChange A hab U, hsurj⟩
  refine ⟨e.symm.toLinearMap, fun w => ?_⟩
  apply e.injective
  rw [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
  change _ = LinearMap.liftBaseChange _ _ (1 ⊗ₜ w)
  rw [LinearMap.liftBaseChange_tmul, one_smul]
  rfl

end GlobalTheory.InvFormRetract
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionDifferentialsInvariantOneFormsAfStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_retraction_differentials_invariantOneForms_affine : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left, ∃ r : Ω[Sec A.hom U.unop.1⁄R] →ₗ[Sec A.hom U.unop.1] (Sec A.hom U.unop.1 ⊗[R] GlobalTheory.InvForm.InvForm A), ∀ w : GlobalTheory.InvForm.InvForm A, r (evForm A.hom U w.1) = 1 ⊗ₜ w := by
  first | exact @GlobalTheory.InvFormRetract.retract | exact GlobalTheory.InvFormRetract.retract | (intros; apply GlobalTheory.InvFormRetract.retract <;> assumption)
end
end
