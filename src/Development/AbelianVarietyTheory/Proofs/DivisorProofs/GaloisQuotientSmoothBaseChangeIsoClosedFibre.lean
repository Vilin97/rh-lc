module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleMapsModPowMaximalIdealBaseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantMapsAffineOpenSmoothModelStatement
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSmoothAtOfSmoothModIdealPowers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentOpenInvariantSubschemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientAffineOpenSpecInvariantsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantsOfTrivialOnThickenings
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothAwayOfQuotientPowEquiv

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SmoothAdic

open TensorProduct

theorem exists_smooth_away_of_quotient_pow_equiv : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (O C : Type) [CommRing O] [Algebra R O] [CommRing C] [Algebra R C], Algebra.Smooth R O → Algebra.FiniteType R C → (∀ e : ℕ, Nonempty ((O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C)))) → ∀ q : Ideal C, q.IsPrime → q.comap (algebraMap R C) = maximalIdeal R → ∃ g : C, g ∉ q ∧ Algebra.Smooth R (Localization.Away g) := by
  intro R _ _ _ O C _ _ _ _ hO hC hiso q hq hqm
  have hsm : ∀ e : ℕ, Algebra.Smooth (R ⧸ maximalIdeal R ^ (e + 1))
      (TensorProduct R (R ⧸ maximalIdeal R ^ (e + 1)) C) := by
    intro e
    obtain ⟨φ⟩ := hiso e
    let J := maximalIdeal R ^ (e + 1)
    let φ' : (O ⧸ J.map (algebraMap R O)) ≃ₐ[R ⧸ J] (C ⧸ J.map (algebraMap R C)) :=
      AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective φ
    let ψ : ((R ⧸ J) ⊗[R] O) ≃ₐ[R ⧸ J] ((R ⧸ J) ⊗[R] C) :=
      ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor O J).symm.trans φ').trans
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C J)
    exact Algebra.Smooth.of_equiv ψ
  haveI := hq
  haveI : Algebra.IsSmoothAt R q :=
    isSmoothAt_of_smooth_quotient_pow R (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top C hsm q hqm
  haveI : Algebra.FinitePresentation R C := Algebra.FinitePresentation.of_finiteType.mp hC
  obtain ⟨g, hg, hs⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R q
  exact ⟨g, hg, hs⟩

end GlobalTheory.SmoothAdic
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothAwayOfQuotientPowEquivStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_smooth_away_of_quotient_pow_equiv' : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (O C : Type) [CommRing O] [Algebra R O] [CommRing C] [Algebra R C], Algebra.Smooth R O → Algebra.FiniteType R C → (∀ e : ℕ, Nonempty ((O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C)))) → ∀ q : Ideal C, q.IsPrime → q.comap (algebraMap R C) = maximalIdeal R → ∃ g : C, g ∉ q ∧ Algebra.Smooth R (Localization.Away g) := by
  first | exact @GlobalTheory.SmoothAdic.exists_smooth_away_of_quotient_pow_equiv | exact GlobalTheory.SmoothAdic.exists_smooth_away_of_quotient_pow_equiv | (intros; apply GlobalTheory.SmoothAdic.exists_smooth_away_of_quotient_pow_equiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantsOfTrivialOnThickeningsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.invariants_of_trivial_on_thickenings_alt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] [Algebra.FiniteType R' C'] (act : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')), (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) → ∀ (O : Type) [CommRing O] [Algebra R O] [Module.Flat R O] [Algebra.FiniteType R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C')), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ C : Subalgebra R C', (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C ∧ Module.Finite C C' ∧ ∃ f : C, f - 1 ∈ (maximalIdeal R).map (algebraMap R C) ∧ (∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _)) ∧ (∀ t : TensorProduct R C R', Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) ∧ ∀ e, Nonempty ((O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C))) := by
  first | exact @GlobalTheory.InvAlg.invariants_of_trivial_on_thickenings | exact GlobalTheory.InvAlg.invariants_of_trivial_on_thickenings | (intros; apply GlobalTheory.InvAlg.invariants_of_trivial_on_thickenings <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoBaseChangeOverBasicOpenOfTensorBijective

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.LocIso

theorem isPullback_resLE_opensRange {W W' Y Z T S : Scheme.{0}} (π : Z ⟶ Y) (s : Z ⟶ T) (b : Y ⟶ S)
    (c : T ⟶ S) (i : W ⟶ Y) [IsOpenImmersion i] (k : W' ⟶ Z) (p : W' ⟶ W)
    (h₁ : IsPullback k p π i) (h₂ : IsPullback p (k ≫ s) (i ≫ b) c) :
    IsPullback (π.resLE i.opensRange (π ⁻¹ᵁ i.opensRange) le_rfl) ((π ⁻¹ᵁ i.opensRange).ι ≫ s)
      (i.opensRange.ι ≫ b) c := by
  let e : W ≅ i.opensRange.toScheme := IsOpenImmersion.isoOfRangeEq i i.opensRange.ι (by simp)
  have he : e.hom ≫ i.opensRange.ι = i := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hR : IsPullback (π.resLE i.opensRange (π ⁻¹ᵁ i.opensRange) le_rfl) (π ⁻¹ᵁ i.opensRange).ι
      i.opensRange.ι π := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; exact isPullback_morphismRestrict π _
  have hW : IsPullback (p ≫ e.hom) k i.opensRange.ι π := by
    refine IsPullback.of_iso h₁.flip (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp [he]
  let φ := IsPullback.isoIsPullback _ _ hW hR
  refine IsPullback.of_iso h₂ φ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (IsPullback.isoIsPullback_hom_fst _ _ hW hR).symm
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, IsPullback.isoIsPullback_hom_snd]
  · simp [← he]
  · simp

theorem isLocalization_tensor (R R' C' : Type) [CommRing R] [CommRing R'] [CommRing C'] [Algebra R R']
    [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (C : Subalgebra R C') (f g : C)
    (hcok : ∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val
      (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _))
    (hker : ∀ t : TensorProduct R C R', (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C')
      fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) :
    letI : Algebra (TensorProduct R C R') (Localization.Away (algebraMap C C' (f * g))) :=
      ((algebraMap C' _).comp (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C')
        fun _ _ => Commute.all _ _).toRingHom).toAlgebra
    IsLocalization (Submonoid.powers ((f * g) ⊗ₜ[R] (1 : R'))) (Localization.Away (algebraMap C C' (f * g))) := by
  set Φ := Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _ with hΦdef
  letI : Algebra (TensorProduct R C R') (Localization.Away (algebraMap C C' (f * g))) :=
    ((algebraMap C' _).comp Φ.toRingHom).toAlgebra
  have hΦ : ∀ c : C, Φ (c ⊗ₜ[R] (1 : R')) = algebraMap C C' c := fun c => by simp [Φ]
  have halg : ∀ t, algebraMap (TensorProduct R C R') (Localization.Away (algebraMap C C' (f * g))) t =
      algebraMap C' _ (Φ t) := fun t => rfl
  have hpow : ∀ n : ℕ, ((f * g) ⊗ₜ[R] (1 : R')) ^ n = ((g ^ n) ⊗ₜ[R] (1 : R')) * ((f ^ n) ⊗ₜ[R] (1 : R')) := by
    intro n
    rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_pow, one_pow, _root_.mul_one, _root_.mul_comm (g ^ n)]
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [halg, map_pow, hΦ, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit _).pow n
  · intro z
    obtain ⟨⟨a, ⟨_, m, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (algebraMap C C' (f * g))) z
    obtain ⟨k, t, ht⟩ := hcok a
    refine ⟨⟨t * ((g ^ k) ⊗ₜ[R] (1 : R')), ⟨((f * g) ⊗ₜ[R] (1 : R')) ^ (m + k), m + k, rfl⟩⟩, ?_⟩
    rw [halg, halg, map_pow Φ, hΦ, map_mul Φ, hΦ, ht, pow_add, map_mul (algebraMap C' _), ← _root_.mul_assoc, hz,
      ← map_mul (algebraMap C' _)]
    refine congrArg (algebraMap C' _) ?_
    have hco : ∀ c : C, algebraMap C C' c = (c : C') := fun _ => rfl
    simp only [hco, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    ring
  · intro x y hxy
    rw [halg, halg] at hxy
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap C C' (f * g))) hxy
    have h0 : Φ (((f * g) ⊗ₜ[R] (1 : R')) ^ m * (x - y)) = 0 := by
      rw [map_mul, map_pow, hΦ, map_sub, mul_sub]
      exact sub_eq_zero.mpr hm
    obtain ⟨n, hn⟩ := hker _ h0
    refine ⟨⟨((f * g) ⊗ₜ[R] (1 : R')) ^ (n + m), n + m, rfl⟩, ?_⟩
    change ((f * g) ⊗ₜ[R] (1 : R')) ^ (n + m) * x = ((f * g) ⊗ₜ[R] (1 : R')) ^ (n + m) * y
    rw [← sub_eq_zero, ← mul_sub, pow_add, hpow, _root_.mul_assoc, _root_.mul_assoc, hn, mul_zero]

theorem exists_smooth_basicOpen_iso : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X : Over (Sp R)) (Z : Scheme.{0}) (π : Z ⟶ X.left) (s : Z ⟶ Sp R') (hX : π ≫ X.hom = s ≫ spMap (algebraMap R R')) (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (C : Subalgebra R C') (j : Sp C' ⟶ Z) (l : Sp C ⟶ X.left) [IsOpenImmersion l], IsPullback j (spMap (algebraMap C C')) π l → j ≫ s = spMap (algebraMap R' C') → l ≫ X.hom = spMap (algebraMap R C) → ∀ f g : C, (∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _)) → (∀ t : TensorProduct R C R', (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) → Algebra.Smooth R (Localization.Away g) → ∀ q : Sp C, f ∉ q.asIdeal → g ∉ q.asIdeal → ∃ V : X.left.Opens, l q ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ s) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap (algebraMap R R'))) := by
  intro R R' _ _ _ X Z π s hX C' _ _ _ _ C j l _ hP hj hl f g hcok hker hsm q hf hg
  let A := Localization.Away (f * g)
  let A' := Localization.Away (algebraMap C C' (f * g))
  let φ : A →+* A' := IsLocalization.Away.map A A' (algebraMap C C') (f * g)
  have hφ : φ.comp (algebraMap C A) = (algebraMap C' A').comp (algebraMap C C') := IsLocalization.map_comp _
  have hLoc : IsPushout (CommRingCat.ofHom (algebraMap C C')) (CommRingCat.ofHom (algebraMap C A))
      (CommRingCat.ofHom (algebraMap C' A')) (CommRingCat.ofHom φ) := by
    have : IsLocalization ((Submonoid.powers (f * g)).map (algebraMap C C')) A' := by
      rw [Submonoid.map_powers]; infer_instance
    exact CommRingCat.isPushout_of_isLocalization _ _ hφ (Submonoid.powers (f * g))
  haveI : IsOpenImmersion (spMap (algebraMap C A)) := IsOpenImmersion.of_isLocalization (f * g)
  have h₁ : IsPullback (spMap (algebraMap C' A') ≫ j) (spMap φ) π (spMap (algebraMap C A) ≫ l) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ hLoc).paste_horiz hP
  have hRing : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap R' A')) := by
    let Φ := Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _
    letI : Algebra (TensorProduct R C R') A' := ((algebraMap C' A').comp Φ.toRingHom).toAlgebra
    have hL := isLocalization_tensor R R' C' C f g hcok hker
    have Q1 := CommRingCat.isPushout_tensorProduct R C R'
    have : IsLocalization ((Submonoid.powers (f * g)).map
        (Algebra.TensorProduct.includeLeftRingHom : C →+* TensorProduct R C R')) A' := by
      rw [Submonoid.map_powers]; exact hL
    have H : φ.comp (algebraMap C A) = (algebraMap (TensorProduct R C R') A').comp
        Algebra.TensorProduct.includeLeftRingHom := by
      rw [hφ]
      ext c
      simp [RingHom.algebraMap_toAlgebra, Φ]
    have Q2 := CommRingCat.isPushout_of_isLocalization (S := TensorProduct R C R') (Rₘ := A) (Sₘ := A')
      Algebra.TensorProduct.includeLeftRingHom φ H (Submonoid.powers (f * g))
    have Q := (Q1.flip.paste_vert Q2).flip
    convert Q using 1
    · ext r; simp [RingHom.algebraMap_toAlgebra, Φ, ← IsScalarTower.algebraMap_apply]
  have hs : (spMap (algebraMap C' A') ≫ j) ≫ s = spMap (algebraMap R' A') := by
    rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hb : (spMap (algebraMap C A) ≫ l) ≫ X.hom = spMap (algebraMap R A) := by
    rw [Category.assoc, hl, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have h₂ : IsPullback (spMap φ) ((spMap (algebraMap C' A') ≫ j) ≫ s)
      ((spMap (algebraMap C A) ≫ l) ≫ X.hom) (spMap (algebraMap R R')) := by
    rw [hs, hb]; exact isPullback_SpecMap_of_isPushout _ _ _ _ hRing
  have hG := isPullback_resLE_opensRange π s X.hom (spMap (algebraMap R R')) _ _ _ h₁ h₂
  refine ⟨(spMap (algebraMap C A) ≫ l).opensRange, ?_, isAffineOpen_opensRange _, ?_, ?_⟩
  · obtain ⟨w, hw⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap C A)) := by
      rw [PrimeSpectrum.localization_away_comap_range A (f * g)]
      exact fun h => (q.isPrime.mem_or_mem h).elim hf hg
    refine ⟨w, ?_⟩
    first
      | exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg l hw)
      | exact (Scheme.comp_base_apply _ _ _).trans (congrArg l hw)
      | exact congrArg l hw
  · let B := Localization.Away (algebraMap C (Localization.Away g) f)
    haveI : Algebra.Smooth R B := Algebra.Smooth.comp R (Localization.Away g) B
    haveI : Algebra.Smooth R A :=
      Algebra.Smooth.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (f * g)) B A).restrictScalars R)
    haveI : Smooth (spMap (algebraMap R A)) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
    let e := IsOpenImmersion.isoOfRangeEq (spMap (algebraMap C A) ≫ l)
      (spMap (algebraMap C A) ≫ l).opensRange.ι (by simp)
    have hfac : e.hom ≫ (spMap (algebraMap C A) ≫ l).opensRange.ι = spMap (algebraMap C A) ≫ l :=
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    have : (spMap (algebraMap C A) ≫ l).opensRange.ι ≫ X.hom = e.inv ≫ spMap (algebraMap R A) := by
      calc _ = e.inv ≫ (e.hom ≫ (spMap (algebraMap C A) ≫ l).opensRange.ι) ≫ X.hom := by simp
        _ = _ := by rw [hfac, hb]
    rw [this]; infer_instance
  · convert (inferInstance : IsIso hG.isoPullback.hom)
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hG.isoPullback_hom_fst.symm
    · exact (pullback.lift_snd _ _ _).trans hG.isoPullback_hom_snd.symm

end GlobalTheory.Mum.LocIso
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoBaseChangeOverBasicOpenOfTensorBijectiveStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isIso_baseChange_over_basicOpen_of_tensor_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X : Over (Sp R)) (Z : Scheme.{0}) (π : Z ⟶ X.left) (s : Z ⟶ Sp R') (hX : π ≫ X.hom = s ≫ spMap (algebraMap R R')) (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (C : Subalgebra R C') (j : Sp C' ⟶ Z) (l : Sp C ⟶ X.left) [IsOpenImmersion l], IsPullback j (spMap (algebraMap C C')) π l → j ≫ s = spMap (algebraMap R' C') → l ≫ X.hom = spMap (algebraMap R C) → ∀ f g : C, (∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _)) → (∀ t : TensorProduct R C R', (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) → Algebra.Smooth R (Localization.Away g) → ∀ q : Sp C, f ∉ q.asIdeal → g ∉ q.asIdeal → ∃ V : X.left.Opens, l q ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ s) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap (algebraMap R R'))) := by
  first | exact @GlobalTheory.Mum.LocIso.exists_smooth_basicOpen_iso | exact GlobalTheory.Mum.LocIso.exists_smooth_basicOpen_iso | (intros; apply GlobalTheory.Mum.LocIso.exists_smooth_basicOpen_iso <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientSmoothBaseChangeIsoClosedFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem quotient_smooth_and_baseChange_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) → ∀ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left) (hX : π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ), IsAffineHom π → Surjective π → (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ x : H.toScheme, spMap ρ (G'.hom (H.ι x)) = closedPoint R → ∃ V : X.left.Opens, π x ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ H.ι ≫ G'.hom) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap ρ)) := by
  intro R _ _ _ hR R' _ _ _ ρ hρ hΓ D D' hD A' G' _ _ hG U' a H hH _ X π hX hπ _ hinv hfib hsec x hx
  obtain ⟨_, rfl⟩ : ∃ _ : Algebra R R', algebraMap R R' = ρ := ⟨ρ.toAlgebra, rfl⟩
  have hw := fun σ => (a.cart σ).1.w
  obtain ⟨Y, φ, hY, hφ, hsucc, hσ⟩ := @GlobalTheory.FormalModel.exists_model R _ _ _ hR R' _ _ _ _ D D' hD A' G' _ _ U' a
  obtain ⟨V, W, hxV, hV, hW, hVW⟩ := @GlobalTheory.T.galois_descent_open_invariant_subscheme R _ _ _ R' _ _ _ _ hR hρ hΓ G' a.act hw a.act_one a.act_mul H hH X π hX hπ hinv
    hfib hsec Y φ hY hφ hsucc hσ x hx
  obtain ⟨C', _, _, _, _, actC, C, j, l, hj, hl, hlV, hP, hjs, hls, hact, hlin, hC⟩ := @GlobalTheory.T.galoisQuotient_affineOpen_spec_invariants R _ _ _ R' _ _ _ _ hR hρ hΓ G'
    a.act hw a.act_one a.act_mul H hH X π hX hπ hinv hfib hsec V hV
  have hr : Set.range j = π ⁻¹' (V : Set X.left) := by
    rw [← hlV, ← Scheme.Pullback.range_fst π l, ← hP.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, hP.isoPullback.hom.surjective.range_eq, Set.image_univ]
  have hr' : (j ≫ H.ι).opensRange = H.ι ''ᵁ (π ⁻¹ᵁ V) := by
    ext1
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hr]
    rfl
  obtain ⟨O, _, _, i', hO, h₁, h₂, h₃⟩ := @GlobalTheory.T.exists_invariant_maps_affineOpen_smoothModel R _ R' _ _ _ G' a.act Y φ hY hφ hsucc hσ C' _ _ _ _ actC (j ≫ H.ι) _
    (by rw [Category.assoc, hjs]) (fun σ => by rw [hact, Category.assoc]) W hW (by rw [hVW, hr'])
  have : IsNoetherianRing R := hR.1.1
  have : IsNoetherianRing R' := hρ.1.1
  have : Module.Finite R R' := RingHom.finite_algebraMap.1 hρ.2.2
  obtain ⟨i, k₁, k₂, k₃⟩ := @GlobalTheory.T.exists_compatible_maps_mod_pow_maximalIdeal_base_alt R _ _ R' _ _ _ _ _ C' _ _ _ _ _ (fun σ => actC σ) O _ _ i' h₁ h₂ h₃
  have : Algebra.FiniteType R' C' := by
    have := U'.smooth
    have : LocallyOfFiniteType (spMap (algebraMap R' C')) := by rw [← hjs]; infer_instance
    exact RingHom.finiteType_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this)
  obtain ⟨hft, -, f, hf, hf₁, hf₂, hiso⟩ := GlobalTheory.T.invariants_of_trivial_on_thickenings_alt R hR.1 R' hρ.2.1 hΓ C' actC hlin O i k₁ k₂ k₃ C hC
  obtain ⟨p, rfl⟩ : x ∈ Set.range j := by rw [hr]; exact hxV
  let q : Sp C := spMap (algebraMap C C') p
  have hq : l q = π (j p) := by rw [← Scheme.Hom.comp_apply, ← hP.w, Scheme.Hom.comp_apply]
  have hq' : q.asIdeal.comap (algebraMap R C) = maximalIdeal R := by
    have : spMap (algebraMap R C) q = closedPoint R := by
      rw [← hx, ← hls, Scheme.Hom.comp_apply, hq, ← Scheme.Hom.comp_apply, hX]
      simp only [Scheme.Hom.comp_apply]
    exact congrArg PrimeSpectrum.asIdeal this
  obtain ⟨g, hg, hsm⟩ := @GlobalTheory.T.exists_smooth_away_of_quotient_pow_equiv' R _ _ _ O C _ _ _ _ hO hft hiso q.asIdeal q.isPrime hq'
  have hfq : f ∉ q.asIdeal := fun h => q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := q.asIdeal.sub_mem h (Ideal.map_le_iff_le_comap.2 hq'.ge hf)
    rwa [sub_sub_cancel] at this))
  rw [← hq]
  exact @GlobalTheory.T.isIso_baseChange_over_basicOpen_of_tensor_bijective R R' _ _ _ X H.toScheme π (H.ι ≫ G'.hom) (by rw [hX, Category.assoc]) C' _ _ _ _ C j l hl hP hjs hls f g hf₁ hf₂
    hsm q hfq hg

end GlobalTheory.Mum
end
end
