module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionComplexAugmentationQuasiIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSheafHomLinearMapsSheafCurryEquivStatement
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftEtaleSheafOfLinearMapsExact

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem lift_linear_of_injective {S : Type*} [Ring S] {N A B C : Type*} [AddCommGroup N] [Module S N]
    [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B] [AddCommGroup C] [Module S C]
    (hN : Module.Baer S N)
    (u : A →ₗ[S] B) (v : B →ₗ[S] C) (hex : ∀ b, v b = 0 → ∃ a, u a = b)
    (f : B →ₗ[S] N) (hf : f ∘ₗ u = 0) : ∃ g : C →ₗ[S] N, g ∘ₗ v = f := by
  have hle : LinearMap.ker v ≤ LinearMap.ker f := by
    intro b hb
    obtain ⟨a, rfl⟩ := hex b hb
    simpa using LinearMap.congr_fun hf a
  let f₁ : (B ⧸ LinearMap.ker v) →ₗ[S] N := (LinearMap.ker v).liftQ f hle
  let f₂ : LinearMap.range v →ₗ[S] N := f₁ ∘ₗ (v.quotKerEquivRange).symm.toLinearMap
  obtain ⟨g, hg⟩ := hN.extension_property (LinearMap.range v).subtype (LinearMap.range v).injective_subtype f₂
  refine ⟨g, LinearMap.ext fun b => ?_⟩
  have h1 := LinearMap.congr_fun hg ⟨v b, b, rfl⟩
  have h2 : (v.quotKerEquivRange).symm ⟨v b, b, rfl⟩ = Submodule.Quotient.mk b := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.comp_apply, Submodule.coe_subtype] at h1
  rw [LinearMap.comp_apply, h1]
  simp only [f₂, f₁, LinearMap.comp_apply, LinearEquiv.coe_coe, h2, Submodule.liftQ_apply]

theorem lift_homSh : ∀ (R : Type) [CommRing R] (J X : Shv R), Module.Injective (ULift.{1} R) (X ⟶ J) → ∀ (A B C : ModuleCat.{1} (ULift.{1} R)) (u : A ⟶ B) (v : B ⟶ C), (∀ b, v.hom b = 0 → ∃ a, u.hom a = b) → ∀ f : X ⟶ (homSh J).obj (op B), f ≫ (homSh J).map u.op = 0 → ∃ g : X ⟶ (homSh J).obj (op C), g ≫ (homSh J).map v.op = f := by
  intro R _ J X hinj A B C u v hex f hf
  obtain ⟨e, hnat, -⟩ := GlobalTheory.T.exists_sheafHom_linearMapsSheaf_curry_equiv R J
  have he0 : ∀ M : ModuleCat.{1} (ULift.{1} R), e X M 0 = 0 := by
    intro M
    have := hnat X M M 0 0
    rw [zero_comp, ModuleCat.hom_zero, LinearMap.comp_zero] at this
    exact this
  have hf' : e X B f ∘ₗ u.hom = 0 := by rw [← hnat, hf, he0]
  obtain ⟨g', hg'⟩ := lift_linear_of_injective (Module.Baer.of_injective hinj) u.hom v.hom hex (e X B f) hf'
  refine ⟨(e X C).symm g', (e X B).injective ?_⟩
  rw [hnat, Equiv.apply_symm_apply, hg']
end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftEtaleSheafOfLinearMapsExactStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_lift_etaleSheafOfLinearMaps_exact : ∀ (R : Type) [CommRing R] (J X : Shv R), Module.Injective (ULift.{1} R) (X ⟶ J) → ∀ (A B C : ModuleCat.{1} (ULift.{1} R)) (u : A ⟶ B) (v : B ⟶ C), (∀ b, v.hom b = 0 → ∃ a, u.hom a = b) → ∀ f : X ⟶ (homSh J).obj (op B), f ≫ (homSh J).map u.op = 0 → ∃ g : X ⟶ (homSh J).obj (op C), g ≫ (homSh J).map v.op = f := by
  first | (exact @GlobalTheory.EtC.lift_homSh) | (exact GlobalTheory.EtC.lift_homSh) | (intros; apply GlobalTheory.EtC.lift_homSh  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveEtaleSheafOfLinearMapsFromModule

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem homSh_injective (R : Type) [CommRing R] (J : Shv R) [Injective J] (M : ModuleCat.{1} (ULift.{1} R)) [Projective M] :
    Injective ((homSh J).obj (op M)) := by
  obtain ⟨e, -, hX⟩ := GlobalTheory.T.exists_sheafHom_linearMapsSheaf_curry_equiv R J
  haveI : Module.Projective (ULift.{1} R) M := (IsProjective.iff_projective (P := M)).2 ‹_›
  constructor
  intro X Y g i _
  have surj : Function.Surjective (Linear.leftComp (ULift.{1} R) J i) :=
    fun k => ⟨Injective.factorThru k i, Injective.comp_factorThru k i⟩
  obtain ⟨h', hh'⟩ := Module.projective_lifting_property _ (e X M g) surj
  refine ⟨(e Y M).symm h', ?_⟩
  apply (e X M).injective
  rw [hX, Equiv.apply_symm_apply, hh']

end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveEtaleSheafOfLinearMapsFromModuleStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.injective_etaleSheafOfLinearMapsFromModule : ∀ (R : Type) [CommRing R] (J : Shv R) [Injective J] (M : ModuleCat.{1} (ULift.{1} R)) [Projective M], Injective ((homSh J).obj (op M)) := by
  first | (exact @GlobalTheory.EtC.homSh_injective) | (exact GlobalTheory.EtC.homSh_injective) | (intros; apply GlobalTheory.EtC.homSh_injective  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoinducedSheafInjectiveResolutionFreeExact

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.EtC.coindRes_exists : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (J : Shv R) [Injective J], (∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) → ∃ (C : Cx R) (ε : sgl ((restr φ).obj ((coind φ).obj J)) ⟶ C), C.IsStrictlyGE 0 ∧ (∀ t, Injective (C.X t)) ∧ QuasiIso ε ∧ ∀ (P : PSh) (n : ℤ), 0 < n → Subsingleton (CohomologyClass (sgl ((free R).obj P)) C n) := by
  intro R S _ _ φ J _ hJ
  haveI := GlobalTheory.T.etaleCoinductionComplexAugmentation_quasiIso R S φ J hJ
  let I : InjectiveResolution ((restr φ).obj ((coind φ).obj J)) :=
    { cocomplex := coindCx φ J
      injective := fun n => GlobalTheory.T.injective_etaleSheafOfLinearMapsFromModule R J ((scalarsRes φ).complex.X n)
      ι := coindAug φ J }
  refine ⟨I.cochainComplex, I.ι', inferInstance, inferInstance, inferInstance, ?_⟩
  intro P n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ x : CohomologyClass (sgl ((free R).obj P)) I.cochainComplex ((k : ℤ) + 1), x = 0 by
    rw [h x, h y]
  intro x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective α ((k : ℤ) + 1) (zero_add _) ((k : ℤ) + 1 + 1) rfl
  rw [CohomologyClass.mk_eq_zero_iff, Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (k : ℤ) rfl]
  have hex : ∀ b, ((scalarsRes φ).complex.d (k + 1) k).hom b = 0 → ∃ a, ((scalarsRes φ).complex.d (k + 2) (k + 1)).hom a = b := by
    intro b hb
    exact ((ShortComplex.moduleCat_exact_iff _).1 ((scalarsRes φ).exact_succ k)) b hb
  have hd1 := I.cochainComplex_d ((k : ℤ) + 1) ((k : ℤ) + 1 + 1) (k + 1) (k + 2) (by simp) (by push_cast; ring)
  rw [hd1] at hf
  have h2 : (f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom) ≫ I.cocomplex.d (k + 1) (k + 2) = 0 := by
    rw [← cancel_mono (I.cochainComplexXIso ((k : ℤ) + 1 + 1) (k + 2) (by push_cast; ring)).inv]
    simpa using hf
  have hf' : (f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom) ≫
      (homSh J).map ((scalarsRes φ).complex.d (k + 2) (k + 1)).op = 0 := by
    rw [← coindCx_d]
    exact h2
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_lift_etaleSheafOfLinearMaps_exact R J ((free R).obj P) (hJ P) _ _ _ _ _ hex _ hf'
  refine ⟨g ≫ (I.cochainComplexXIso (k : ℤ) k rfl).inv, ?_⟩
  rw [I.cochainComplex_d (k : ℤ) ((k : ℤ) + 1) k (k + 1) rfl (by simp)]
  erw [Category.assoc, Iso.inv_hom_id_assoc]
  have hg' : g ≫ I.cocomplex.d k (k + 1) = f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom := by
    rw [← hg, ← coindCx_d]
    rfl
  erw [← Category.assoc, hg', Category.assoc, Iso.hom_inv_id, Category.comp_id]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoinducedSheafInjectiveResolutionFreeExactStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_coinducedSheaf_injectiveResolution_freeExact : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (J : Shv R) [Injective J], (∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) → ∃ (C : Cx R) (ε : sgl ((restr φ).obj ((coind φ).obj J)) ⟶ C), C.IsStrictlyGE 0 ∧ (∀ t, Injective (C.X t)) ∧ QuasiIso ε ∧ ∀ (P : PSh) (n : ℤ), 0 < n → Subsingleton (CohomologyClass (sgl ((free R).obj P)) C n) := by
  first | (exact @GlobalTheory.EtC.coindRes_exists) | (exact GlobalTheory.EtC.coindRes_exists) | (intros; apply GlobalTheory.EtC.coindRes_exists  <;> assumption)
end
end
