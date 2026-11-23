module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppOfFlatBaseChangeEqualised
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.AlgebraicGeometry.Modules.Sheaf

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormNotMemIff

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem algebraMap_norm_mem_span_singleton (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B] (f : B) :
    algebraMap A B (Algebra.norm A f) ∈ Ideal.span {f} := by
  set g : B →ₗ[A] B := Algebra.lmul A B f with hg
  set p := g.charpoly
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := p)
  have h0 : Polynomial.aeval f p = 0 := by
    have h1 : Polynomial.aeval g p = 0 := LinearMap.aeval_self_charpoly g
    rw [hg, Polynomial.aeval_algHom_apply] at h1
    have h2 := congrArg (fun u : B →ₗ[A] B => u 1) h1
    simpa using h2
  have h3 := congrArg (Polynomial.aeval f) hq
  simp only [map_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X, h0, zero_sub] at h3
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff, map_mul,
    show algebraMap A B (g.charpoly.coeff 0) = -(f * Polynomial.aeval f q) by
      rw [← h3, neg_neg]]
  exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))

theorem norm_not_mem_iff (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B] (f : B) (P : PrimeSpectrum A) :
    Algebra.norm A f ∉ P.asIdeal ↔
      ∀ Q : PrimeSpectrum B, Q.asIdeal.comap (algebraMap A B) = P.asIdeal → f ∉ Q.asIdeal := by
  constructor
  · intro hN Q hQ hf
    apply hN
    rw [← hQ, Ideal.mem_comap]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hf (algebraMap_norm_mem_span_singleton A B f)
  · intro h hN
    let Rₘ := Localization.AtPrime P.asIdeal
    let Sₘ := Localization (Algebra.algebraMapSubmonoid B P.asIdeal.primeCompl)
    have hnu : ¬ IsUnit (algebraMap B Sₘ f) := by
      intro hu
      have h1 := hu.map (Algebra.norm Rₘ (S := Sₘ))
      rw [Algebra.norm_localization A P.asIdeal.primeCompl] at h1
      exact (IsLocalization.AtPrime.isUnit_to_map_iff Rₘ P.asIdeal _).mp h1 hN
    obtain ⟨M, hM, hfM⟩ := exists_max_ideal_of_mem_nonunits hnu
    haveI : Module.Finite Rₘ Sₘ := Module.Finite.of_basis
      ((Module.Free.chooseBasis A B).localizationLocalization Rₘ P.asIdeal.primeCompl Sₘ)
    have hMc : M.comap (algebraMap Rₘ Sₘ) = IsLocalRing.maximalIdeal Rₘ :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := Rₘ) M)
    refine h ⟨M.comap (algebraMap B Sₘ), hM.isPrime.comap _⟩ ?_ hfM
    show (M.comap (algebraMap B Sₘ)).comap (algebraMap A B) = P.asIdeal
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A Rₘ Sₘ,
      ← Ideal.comap_comap, hMc]
    exact Localization.AtPrime.under_maximalIdeal

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormNotMemIffStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.norm_not_mem_iff_forall_over_not_mem : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B] (f : B) (P : PrimeSpectrum A), Algebra.norm A f ∉ P.asIdeal ↔ ∀ Q : PrimeSpectrum B, Q.asIdeal.comap (algebraMap A B) = P.asIdeal → f ∉ Q.asIdeal := by
  first | exact @GlobalTheory.Mum.norm_not_mem_iff | exact GlobalTheory.Mum.norm_not_mem_iff | (intros; apply GlobalTheory.Mum.norm_not_mem_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormBasicOpenFiniteFreeBaseChange

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.NormBC

open TensorProduct

theorem norm_map_of_basis {A A' B B' : Type} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A' B'] (ρ : A →+* A') (ψ : B →+* B')
    (hc : ∀ a, ψ (algebraMap A B a) = algebraMap A' B' (ρ a)) {J : Type} [Fintype J] [DecidableEq J]
    (e : Module.Basis J A B) (e' : Module.Basis J A' B') (he : ∀ i, ψ (e i) = e' i) (f : B) :
    Algebra.norm A' (ψ f) = ρ (Algebra.norm A f) := by
  rw [Algebra.norm_eq_matrix_det e, Algebra.norm_eq_matrix_det e', RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul]
  have h : ψ f * e' j = ∑ k, ρ (e.repr (f * e j) k) • e' k := by
    rw [← he j, ← map_mul]
    conv_lhs => rw [← e.sum_repr (f * e j)]

    simp only [map_sum, Algebra.smul_def, map_mul, hc, he]
  rw [h, e'.repr_sum_self]

theorem exists_basis_of_ringEquiv {S₀ A T₀ B : Type} [CommRing S₀] [CommRing A] [CommRing T₀]
    [CommRing B] [Algebra S₀ A] [Algebra S₀ T₀] [Algebra A B] {J : Type}
    (c : Module.Basis J S₀ T₀) (Φ : A ⊗[S₀] T₀ ≃+* B) (hΦ : ∀ a, Φ (a ⊗ₜ 1) = algebraMap A B a) :
    ∃ e : Module.Basis J A B, ∀ i, e i = Φ (1 ⊗ₜ c i) := by
  let L : A ⊗[S₀] T₀ ≃ₗ[A] B := Φ.toAddEquiv.toLinearEquiv (fun a x => by
    show Φ (a • x) = a • Φ x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← hΦ]
    rfl)
  exact ⟨(Algebra.TensorProduct.basis A c).map L, fun i => by
    simp [L, Algebra.TensorProduct.basis_apply]⟩

theorem exists_basis_Gamma {R R₁ : Type} [CommRing R] [CommRing R₁] [Algebra R R₁] {J : Type}
    [Fintype J] (c' : Module.Basis J R R₁) :
    letI := ((spMap (algebraMap R R₁)).appLE ⊤ ⊤ le_top).hom.toAlgebra
    Nonempty (Module.Basis J Γ(Sp R, ⊤) Γ(Sp R₁, ⊤)) := by
  letI := ((spMap (algebraMap R R₁)).appLE ⊤ ⊤ le_top).hom.toAlgebra
  let σ : Γ(Sp R, ⊤) ≃+* R := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  let σ₁ : Γ(Sp R₁, ⊤) ≃+* R₁ := (Scheme.ΓSpecIso (CommRingCat.of R₁)).commRingCatIsoToRingEquiv
  have hnat : ∀ a, σ₁ (algebraMap Γ(Sp R, ⊤) Γ(Sp R₁, ⊤) a) = algebraMap R R₁ (σ a) := fun a => by
    have h := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R R₁)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    rw [AffDesc.appTop_eq_appLE] at h
    exact h
  let E : Γ(Sp R₁, ⊤) ≃ₗ[Γ(Sp R, ⊤)] (J → Γ(Sp R, ⊤)) :=
    { toFun := fun y i => σ.symm (c'.repr (σ₁ y) i)
      invFun := fun g => σ₁.symm (∑ i, σ (g i) • c' i)
      map_add' := fun y y' => by funext i; simp
      map_smul' := fun a y => by
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [Algebra.smul_def, map_mul, hnat, ← Algebra.smul_def, map_smul, Finsupp.smul_apply,
          smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
      left_inv := fun y => by
        simp only [RingEquiv.apply_symm_apply, c'.sum_repr, RingEquiv.symm_apply_apply]
      right_inv := fun g => by
        funext i
        simp only [RingEquiv.apply_symm_apply, c'.repr_sum_self, RingEquiv.symm_apply_apply] }
  exact ⟨Module.Basis.ofEquivFun E⟩

theorem mem_primeIdealOf_iff' {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (s : Γ(X, U)) : s ∈ (hU.primeIdealOf x).asIdeal ↔ x.1 ∉ X.basicOpen s := by
  have h : (hU.primeIdealOf x : Spec Γ(X, U)) ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen s ↔
      x.1 ∈ X.basicOpen s := by
    conv_rhs => rw [← hU.fromSpec_primeIdealOf x]
    rfl
  rw [← h, hU.fromSpec_preimage_basicOpen]
  exact not_not.symm

end GlobalTheory.Mum.NormBC

namespace GlobalTheory.Mum.NormBC

open TensorProduct

theorem exists_norm_basicOpen : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁]
    [Module.Finite R R₁] [Module.Free R R₁] (X X₁ : Scheme.{0}) (p : X ⟶ Sp R) (p₁ : X₁ ⟶ Sp R₁)
    (b : X₁ ⟶ X), IsPullback b p₁ p (spMap (algebraMap R R₁)) → ∀ (V : X.Opens),
    IsCompact (V : Set X) → IsQuasiSeparated (V : Set X) → ∀ f : Γ(X₁, b ⁻¹ᵁ V), ∃ n : Γ(X, V),
    ∀ x : X, x ∈ X.basicOpen n ↔ x ∈ V ∧ ∀ z : X₁, b z = x → z ∈ X₁.basicOpen f := by
  intro R R₁ _ _ _ _ _ X X₁ p p₁ b H V hVc hVq f
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · refine ⟨0, fun x => ?_⟩
    exact absurd (Subsingleton.elim _ _ : (p x).asIdeal = ⊤) (p x).isPrime.ne_top
  let c' := Module.Free.chooseBasis R R₁
  letI a0 : Algebra Γ(Sp R, ⊤) Γ(Sp R₁, ⊤) :=
    ((spMap (algebraMap R R₁)).appLE ⊤ ⊤ le_top).hom.toAlgebra
  obtain ⟨c⟩ := exists_basis_Gamma c'
  letI aX : ∀ U : X.Opens, Algebra Γ(Sp R, ⊤) Γ(X, U) := fun U => (p.appLE ⊤ U le_top).hom.toAlgebra
  letI aB : ∀ U : X.Opens, Algebra Γ(X, U) Γ(X₁, b ⁻¹ᵁ U) :=
    fun U => (b.appLE U (b ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  have key : ∀ U : X.Opens, IsIso (pushoutSection H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top
      (show b ⁻¹ᵁ U = b ⁻¹ᵁ U ⊓ p₁ ⁻¹ᵁ ⊤ by simp)) →
      ∃ e : Module.Basis (Module.Free.ChooseBasisIndex R R₁) Γ(X, U) Γ(X₁, b ⁻¹ᵁ U),
        ∀ i, e i = (p₁.appLE ⊤ (b ⁻¹ᵁ U) (by simp)).hom (c i) := by
    intro U hU
    let Φ := (CommRingCat.isPushout_tensorProduct Γ(Sp R, ⊤) Γ(X, U) Γ(Sp R₁, ⊤)).isoPushout.hom ≫
      pushoutSection H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top
        (show b ⁻¹ᵁ U = b ⁻¹ᵁ U ⊓ p₁ ⁻¹ᵁ ⊤ by simp)
    have : IsIso Φ := by dsimp only [Φ]; infer_instance
    let Φe : Γ(X, U) ⊗[Γ(Sp R, ⊤)] Γ(Sp R₁, ⊤) ≃+* Γ(X₁, b ⁻¹ᵁ U) :=
      (asIso Φ).commRingCatIsoToRingEquiv
    have fΦ : ∀ a t, Φe (a ⊗ₜ t) =
        (b.appLE U (b ⁻¹ᵁ U) le_rfl).hom a * (p₁.appLE ⊤ (b ⁻¹ᵁ U) (by simp)).hom t :=
      fun a t => AffDesc.isoPushout_desc_tmul _ _ _ a t
    obtain ⟨e, he⟩ := exists_basis_of_ringEquiv c Φe (fun a => by rw [fΦ, map_one, _root_.mul_one]; rfl)
    exact ⟨e, fun i => by rw [he, fΦ, map_one, _root_.one_mul]⟩
  haveI : Module.Flat R R₁ := inferInstance
  haveI : Flat (spMap (algebraMap R R₁)) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  obtain ⟨e, he⟩ := key V (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H le_top le_top _
    (isAffineOpen_top _) (isAffineOpen_top _) hVc hVq)
  refine ⟨Algebra.norm Γ(X, V) f, fun x => ?_⟩
  by_cases hxV : x ∈ V
  swap
  · exact ⟨fun h => absurd (X.basicOpen_le _ h) hxV, fun h => absurd h.1 hxV⟩
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  have hUV' : U ≤ V := hUV
  haveI : IsAffineHom b := MorphismProperty.of_isPullback H.flip inferInstance
  have hU₁ : IsAffineOpen (b ⁻¹ᵁ U) := hU.preimage b
  obtain ⟨e', he'⟩ := key U (isIso_pushoutSection_of_isAffineOpen H le_top le_top _
    (isAffineOpen_top _) (isAffineOpen_top _) hU)
  have hUV₁ : b ⁻¹ᵁ U ≤ b ⁻¹ᵁ V := b.preimage_mono hUV'
  let ρ := X.presheaf.map (homOfLE hUV').op
  let ψ := X₁.presheaf.map (homOfLE hUV₁).op
  have hn : Algebra.norm Γ(X, U) (ψ.hom f) = ρ.hom (Algebra.norm Γ(X, V) f) := by
    refine norm_map_of_basis ρ.hom ψ.hom (fun a => ?_) e e' (fun i => ?_) f
    · change (b.appLE V _ le_rfl ≫ X₁.presheaf.map _).hom a = (X.presheaf.map _ ≫ b.appLE U _ le_rfl).hom a
      rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
    · rw [he, he']
      exact congrArg (fun φ => CommRingCat.Hom.hom φ (c i)) (Scheme.Hom.appLE_map p₁ _ _)
  haveI : Module.Free Γ(X, U) Γ(X₁, b ⁻¹ᵁ U) := Module.Free.of_basis e'
  haveI : Module.Finite Γ(X, U) Γ(X₁, b ⁻¹ᵁ U) := Module.Finite.of_basis e'
  have I := GlobalTheory.T.norm_not_mem_iff_forall_over_not_mem Γ(X, U) Γ(X₁, b ⁻¹ᵁ U) (ψ.hom f) (hU.primeIdealOf ⟨x, hxU⟩)
  have hsq := IsAffineOpen.SpecMap_appLE_fromSpec b hU hU₁ le_rfl
  have hpt : ∀ Q, b (hU₁.fromSpec Q) = hU.fromSpec (Spec.map (b.appLE U (b ⁻¹ᵁ U) le_rfl) Q) :=
    fun Q => by rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
  have hfib : (∀ Q : PrimeSpectrum Γ(X₁, b ⁻¹ᵁ U),
      Q.asIdeal.comap (algebraMap Γ(X, U) Γ(X₁, b ⁻¹ᵁ U)) = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal →
        ψ.hom f ∉ Q.asIdeal) ↔ ∀ z : X₁, b z = x → z ∈ X₁.basicOpen f := by
    constructor
    · intro h z hz
      have hzU : z ∈ b ⁻¹ᵁ U := by show b z ∈ U; rw [hz]; exact hxU
      have hzf : z ∈ X₁.basicOpen (ψ.hom f) := by
        by_contra hcon
        have hm := (mem_primeIdealOf_iff' hU₁ ⟨z, hzU⟩ (ψ.hom f)).2 hcon
        refine h _ ?_ hm
        have e1 : hU.fromSpec (Spec.map (b.appLE U (b ⁻¹ᵁ U) le_rfl) (hU₁.primeIdealOf ⟨z, hzU⟩)) =
            hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) :=
          (hpt _).symm.trans (by rw [hU₁.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf]; exact hz)
        exact congrArg PrimeSpectrum.asIdeal (hU.fromSpec.isOpenEmbedding.injective e1)
      rw [Scheme.basicOpen_res] at hzf
      exact hzf.2
    · intro h Q hQ hfQ
      have hz := h (hU₁.fromSpec Q) ((hpt Q).trans ((congrArg hU.fromSpec (PrimeSpectrum.ext hQ)).trans
        (hU.fromSpec_primeIdealOf ⟨x, hxU⟩)))
      have hzU : hU₁.fromSpec Q ∈ b ⁻¹ᵁ U := by
        have : hU₁.fromSpec Q ∈ Set.range hU₁.fromSpec := ⟨Q, rfl⟩
        rwa [hU₁.range_fromSpec] at this
      have hz' : hU₁.fromSpec Q ∈ X₁.basicOpen (ψ.hom f) := by
        rw [Scheme.basicOpen_res]; exact ⟨hzU, hz⟩
      have hz'' : Q ∈ hU₁.fromSpec ⁻¹ᵁ X₁.basicOpen (ψ.hom f) := hz'
      rw [hU₁.fromSpec_preimage_basicOpen] at hz''
      exact hz'' hfQ
  have hbx : x ∈ X.basicOpen (Algebra.norm Γ(X, V) f) ↔
      Algebra.norm Γ(X, U) (ψ.hom f) ∉ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    rw [mem_primeIdealOf_iff', not_not, hn, Scheme.basicOpen_res]
    exact ⟨fun h => ⟨hxU, h⟩, fun h => h.2⟩
  rw [hbx, I, hfib]
  exact ⟨fun h => ⟨hxV, h⟩, fun h => h.2⟩

end GlobalTheory.Mum.NormBC
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormBasicOpenFiniteFreeBaseChangeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_norm_basicOpen_finiteFree_baseChange : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁] [Module.Finite R R₁] [Module.Free R R₁] (X X₁ : Scheme.{0}) (p : X ⟶ Sp R) (p₁ : X₁ ⟶ Sp R₁) (b : X₁ ⟶ X), IsPullback b p₁ p (spMap (algebraMap R R₁)) → ∀ (V : X.Opens), IsCompact (V : Set X) → IsQuasiSeparated (V : Set X) → ∀ f : Γ(X₁, b ⁻¹ᵁ V), ∃ n : Γ(X, V), ∀ x : X, x ∈ X.basicOpen n ↔ x ∈ V ∧ ∀ z : X₁, b z = x → z ∈ X₁.basicOpen f := by
  first | exact @GlobalTheory.Mum.NormBC.exists_norm_basicOpen | exact GlobalTheory.Mum.NormBC.exists_norm_basicOpen | (intros; apply GlobalTheory.Mum.NormBC.exists_norm_basicOpen <;> assumption)
end
end
