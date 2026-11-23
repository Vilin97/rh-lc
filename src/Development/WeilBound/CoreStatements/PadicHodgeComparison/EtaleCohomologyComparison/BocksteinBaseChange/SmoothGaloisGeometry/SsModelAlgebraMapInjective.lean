module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableGenericFibreLocalizationStatement
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableSpecialFibrePropertyStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntegrallyClosedOfReducedQuotientLocalization

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.IntClosedAway

open Polynomial

theorem mem_span_of_eq_mul_integral {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (t a : A) (hred : IsReduced (A ⧸ Ideal.span {t})) (z : K)
    (hz : IsIntegral A z) (h : algebraMap A K a = algebraMap A K t * z) :
    a ∈ Ideal.span {t} := by
  obtain ⟨p, hp, hpz⟩ := hz
  have hinj := IsFractionRing.injective A K
  have h1 : (p.scaleRoots t).eval a = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_at_apply, h, Polynomial.scaleRoots_eval₂_mul, hpz, mul_zero]
  have h2 : (p.scaleRoots t).map (Ideal.Quotient.mk (Ideal.span {t})) = X ^ p.natDegree := by
    have ht0 : Ideal.Quotient.mk (Ideal.span {t}) t = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)
    ext i
    rw [coeff_map, coeff_scaleRoots, coeff_X_pow, map_mul, map_pow, ht0]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · rw [if_neg hi.ne, zero_pow (by omega), mul_zero]
    · subst hi
      simp [hp.coeff_natDegree]
    · rw [if_neg hi.ne', coeff_eq_zero_of_natDegree_lt hi, map_zero, zero_mul]
  have h3 : Ideal.Quotient.mk (Ideal.span {t}) a ^ p.natDegree = 0 := by
    have h4 := congrArg (Ideal.Quotient.mk (Ideal.span {t})) h1
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, h2] at h4
    simpa using h4
  exact Ideal.Quotient.eq_zero_iff_mem.mp (IsReduced.eq_zero _ ⟨_, h3⟩)

theorem isIntegrallyClosed_of_away :
    ∀ (A : Type) [CommRing A] [IsDomain A] (t : A), t ≠ 0 → IsReduced (A ⧸ Ideal.span {t}) →
      IsIntegrallyClosed (Localization.Away t) → IsIntegrallyClosed A := by
  intro A _ _ t ht hred hcl
  have hle : Submonoid.powers t ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors ht
  haveI : IsDomain (Localization.Away t) := IsLocalization.isDomain_localization hle
  let K := FractionRing A
  letI : Algebra (Localization.Away t) K :=
    (IsLocalization.lift (M := Submonoid.powers t) (g := algebraMap A K)
      (fun y => IsLocalization.map_units K (⟨y, hle y.2⟩ : nonZeroDivisors A))).toAlgebra
  haveI : IsScalarTower A (Localization.Away t) K :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq _ x).symm
  haveI : IsFractionRing (Localization.Away t) K :=
    IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers t) (Localization.Away t) K hle
  rw [isIntegrallyClosed_iff K]
  intro x hx
  have hxB : IsIntegral (Localization.Away t) x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hxB
  obtain ⟨n, a, hna⟩ := IsLocalization.Away.surj t y
  have hxa : algebraMap A K a = x * algebraMap A K t ^ n := by
    have h5 := congrArg (algebraMap (Localization.Away t) K) hna
    rw [map_mul, map_pow, hy, ← IsScalarTower.algebraMap_apply A (Localization.Away t) K,
      ← IsScalarTower.algebraMap_apply A (Localization.Away t) K] at h5
    exact h5.symm
  have ht' : algebraMap A K t ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ht
  clear hna
  induction n generalizing a with
  | zero => exact ⟨a, by simpa using hxa⟩
  | succ n ih =>
    have hz : IsIntegral A (x * algebraMap A K t ^ n) := hx.mul (isIntegral_algebraMap.pow n)
    have hmem : a ∈ Ideal.span {t} :=
      mem_span_of_eq_mul_integral t a hred _ hz (by rw [hxa]; ring)
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ih b (mul_left_injective₀ ht' ?_)
    simp only [map_mul] at hxa
    simp only [hxa]
    ring

end GlobalTheory.CompanionTheory.IntClosedAway
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntegrallyClosedOfReducedQuotientLocalizationStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.isIntegrallyClosed_of_reduced_quotient_localization : ∀ (A : Type) [CommRing A] [IsDomain A] (t : A), t ≠ 0 → IsReduced (A ⧸ Ideal.span {t}) → IsIntegrallyClosed (Localization.Away t) → IsIntegrallyClosed A := by
  first | exact @GlobalTheory.CompanionTheory.IntClosedAway.isIntegrallyClosed_of_away | exact GlobalTheory.CompanionTheory.IntClosedAway.isIntegrallyClosed_of_away | (intros; apply GlobalTheory.CompanionTheory.IntClosedAway.isIntegrallyClosed_of_away <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableModelRingIsDomain

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.SemistableLocal


open MvPolynomial in
theorem irreducible_prod_X_sub_C (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (m' r : ℕ) (hr : 1 ≤ r) :
    Irreducible ((∏ i ∈ Finset.univ.filter (fun i : Fin (m' + 1) => (i : ℕ) < r), X i) - C ϖ :
      MvPolynomial (Fin (m' + 1)) O) := by
  set g : MvPolynomial (Fin m') O :=
    ∏ j ∈ Finset.univ.filter (fun j : Fin m' => (j : ℕ) + 1 < r), MvPolynomial.X j with hgdef
  have hprod : (∏ i ∈ Finset.univ.filter (fun i : Fin (m' + 1) => (i : ℕ) < r),
      (MvPolynomial.X i : MvPolynomial (Fin (m' + 1)) O))
      = MvPolynomial.X 0 * ∏ j ∈ Finset.univ.filter (fun j : Fin m' => (j : ℕ) + 1 < r),
          (MvPolynomial.X (Fin.succ j) : MvPolynomial (Fin (m' + 1)) O) := by
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_succ]
    have h0 : 0 < r := by omega
    simp [Fin.val_succ, h0]
  have hC : MvPolynomial.finSuccEquiv O m' (MvPolynomial.C ϖ) =
      Polynomial.C (MvPolynomial.C ϖ) := by
    have h := (MvPolynomial.finSuccEquiv O m').commutes ϖ
    rw [MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq] at h
    exact h
  have hϖ0 : (MvPolynomial.C ϖ : MvPolynomial (Fin m') O) ≠ 0 := by
    rw [Ne, MvPolynomial.C_eq_zero]; exact hϖ.ne_zero
  have hg0 : g ≠ 0 := by
    intro h
    have h1 := congrArg (MvPolynomial.eval (fun _ : Fin m' => (1 : O))) h
    simp [hgdef] at h1
  have hcop : ∀ a : MvPolynomial (Fin m') O, a ∣ g → a ∣ MvPolynomial.C ϖ → IsUnit a := by
    intro a hag hac
    obtain ⟨s, hs⟩ := hac
    have ha0 : a ≠ 0 := by rintro rfl; rw [zero_mul] at hs; exact hϖ0 hs
    have hs0 : s ≠ 0 := by rintro rfl; rw [mul_zero] at hs; exact hϖ0 hs
    have hdeg := MvPolynomial.totalDegree_mul_of_isDomain ha0 hs0
    rw [← hs, MvPolynomial.totalDegree_C] at hdeg
    have hda : a.totalDegree = 0 := by omega
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hda
    rw [hda] at hag ⊢
    refine IsUnit.map MvPolynomial.C (isUnit_of_dvd_one ?_)
    have h1 := map_dvd (MvPolynomial.eval (fun _ : Fin m' => (1 : O))) hag
    simpa [hgdef] using h1
  have hirr : Irreducible (Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) :
      Polynomial (MvPolynomial (Fin m') O)) := by
    have hdeg : (Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) :
        Polynomial (MvPolynomial (Fin m') O)).natDegree = 1 := Polynomial.natDegree_linear hg0
    have key2 : ∀ c d : Polynomial (MvPolynomial (Fin m') O),
        Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) = c * d →
          c.natDegree = 0 → IsUnit c := by
      intro c d hcd hc
      have hc' := Polynomial.eq_C_of_natDegree_eq_zero hc
      have hdvd : Polynomial.C (c.coeff 0) ∣
          Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) := by
        rw [← hc']; exact ⟨d, hcd⟩
      rw [Polynomial.C_dvd_iff_dvd_coeff] at hdvd
      rw [hc']
      refine IsUnit.map Polynomial.C (hcop _ ?_ ?_)
      · simpa [Polynomial.coeff_C_mul_X, Polynomial.coeff_C] using hdvd 1
      · simpa [Polynomial.coeff_C_mul_X, Polynomial.coeff_C] using hdvd 0
    refine irreducible_iff.mpr ⟨?_, ?_⟩
    · intro hu
      have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    · intro a b hab
      have ha0 : a ≠ 0 := by
        rintro rfl; rw [zero_mul] at hab; rw [hab] at hdeg; simp at hdeg
      have hb0 : b ≠ 0 := by
        rintro rfl; rw [mul_zero] at hab; rw [hab] at hdeg; simp at hdeg
      have hsum := Polynomial.natDegree_mul ha0 hb0
      rw [← hab, hdeg] at hsum
      rcases Nat.eq_zero_or_pos a.natDegree with h | h
      · exact Or.inl (key2 a b hab h)
      · exact Or.inr (key2 b a (by rw [hab, mul_comm]) (by omega))
  refine (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv O m')).mp ?_
  rw [hprod, map_sub, map_mul, map_prod, MvPolynomial.finSuccEquiv_X_zero, hC]
  simp only [MvPolynomial.finSuccEquiv_X_succ]
  convert hirr using 1
  rw [hgdef, map_prod, map_neg]
  ring

theorem isDomain_quotient_prod_X_sub_C :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
      ∀ (m r : ℕ), 1 ≤ r → r ≤ m →
        IsDomain (MvPolynomial (Fin m) O ⧸ Ideal.span
          {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
            MvPolynomial.C ϖ}) := by
  intro O _ _ _ ϖ hϖ m r hr hrm
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hirr := irreducible_prod_X_sub_C O ϖ hϖ m' r hr
  haveI : UniqueFactorizationMonoid (MvPolynomial (Fin (m' + 1)) O) :=
    MvPolynomial.uniqueFactorizationMonoid _
  have hp := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  haveI := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  exact Ideal.Quotient.isDomain _

end GlobalTheory.CompanionTheory.SemistableLocal
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableModelRingIsDomainStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.semistable_model_ring_isDomain : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (m r : ℕ), 1 ≤ r → r ≤ m → IsDomain (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) := by
  first | exact @GlobalTheory.CompanionTheory.SemistableLocal.isDomain_quotient_prod_X_sub_C | exact GlobalTheory.CompanionTheory.SemistableLocal.isDomain_quotient_prod_X_sub_C | (intros; apply GlobalTheory.CompanionTheory.SemistableLocal.isDomain_quotient_prod_X_sub_C <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.SsModelAlgebraMapInjective

section

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison

section Ring

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
  (m r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ m)

include hϖ h1 h2 in
theorem ssModel_isDomain : IsDomain (GlobalTheory.Et.ssModel O ϖ m r) := GlobalTheory.T.semistable_model_ring_isDomain O ϖ hϖ m r h1 h2

include hϖ h1 h2 in
theorem ssModel_algebraMap_ne_zero : algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ ≠ 0 := by
  haveI := ssModel_isDomain O ϖ hϖ m r h1 h2
  intro h
  have h0 : ϖ ∈ nonZeroDivisors O := mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero
  have := GlobalTheory.LogCris.model_mul_eq_zero ϖ h0 (1 : GlobalTheory.Et.ssModel O ϖ m r) (by rw [h, zero_mul])
  exact one_ne_zero this

include hϖ h1 h2 in
theorem ssModel_algebraMap_injective : Function.Injective (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r)) := by
  haveI := ssModel_isDomain O ϖ hϖ m r h1 h2
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra hc0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
  rw [map_mul, map_pow] at hc
  rcases mul_eq_zero.1 hc with h | h
  · exact (u.isUnit.map (algebraMap O _)).ne_zero h
  · exact ssModel_algebraMap_ne_zero O ϖ hϖ m r h1 h2 (pow_eq_zero_iff'.1 h).1

include hϖ h1 h2 in
theorem ssModel_normal (F : Type) [Field F] [Algebra O F] [IsLocalization.Away ϖ F] :
    IsDomain (GlobalTheory.Et.ssModel O ϖ m r) ∧ IsIntegrallyClosed (GlobalTheory.Et.ssModel O ϖ m r) := by
  have hd := ssModel_isDomain O ϖ hϖ m r h1 h2
  refine ⟨hd, ?_⟩
  have ht := ssModel_algebraMap_ne_zero O ϖ hϖ m r h1 h2
  have hred := GlobalTheory.T.semistable_special_fibre_property O ϖ hϖ m r h1 h2
  have hs := GlobalTheory.T.semistable_generic_fibre_localization O ϖ hϖ m r h1 h2 F
  haveI : Smooth (Spec.map (CommRingCat.ofHom (IsLocalization.Away.map F
      (Localization.Away (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ)) (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r)) ϖ))) :=
    HasRingHomProperty.Spec_iff.mpr hs
  have hn := GlobalTheory.isNormalScheme_of_smooth (Spec.map (CommRingCat.ofHom (IsLocalization.Away.map F
      (Localization.Away (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ)) (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r)) ϖ)))
  haveI : IsDomain (Localization.Away (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  have hic := (GlobalTheory.IsNormalScheme.spec_iff_of_isDomain
    (CommRingCat.of (Localization.Away (algebraMap O (GlobalTheory.Et.ssModel O ϖ m r) ϖ)))).mp hn
  exact GlobalTheory.T.isIntegrallyClosed_of_reduced_quotient_localization _ _ ht hred hic

include hϖ h1 h2 in
theorem ssModel_flat : Module.Flat O (GlobalTheory.Et.ssModel O ϖ m r) := by
  haveI := ssModel_isDomain O ϖ hϖ m r h1 h2
  have hi := ssModel_algebraMap_injective O ϖ hϖ m r h1 h2
  haveI : Module.IsTorsionFree O (GlobalTheory.Et.ssModel O ϖ m r) := Module.isTorsionFree_iff_algebraMap_injective.mpr hi
  infer_instance

end Ring

section Scheme

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} [FiniteDimensional ℚ_[l] K]

theorem good_isNormalScheme (M : Model l K) (hM : M.Good) : GlobalTheory.IsNormalScheme M.X := by
  haveI := OK_dvr (l := l) (K := K)
  obtain ⟨-, ϖ, hϖ, hss⟩ := hM
  haveI := OK_away hϖ
  refine GlobalTheory.IsNormalScheme.of_forall_exists_opens fun x => ?_
  obtain ⟨U, hU, hx, m, r, h1, h2, ψ, hψ, -⟩ := hss x
  refine ⟨U, hx, ?_⟩
  rw [GlobalTheory.IsNormalScheme.iff_spec_of_isAffineOpen hU]
  obtain ⟨hd, hic⟩ := ssModel_normal (OK l K) ϖ hϖ m r h1 h2 K
  haveI : Etale (Spec.map (CommRingCat.ofHom ψ)) := HasRingHomProperty.Spec_iff.mpr hψ
  exact GlobalTheory.isNormalScheme_of_smooth (Spec.map (CommRingCat.ofHom ψ))

theorem good_isLocallyNoetherian (M : Model l K) (hM : M.Good) : IsLocallyNoetherian M.X := by
  haveI := OK_dvr (l := l) (K := K)
  obtain ⟨-, ϖ, hϖ, hss⟩ := hM
  choose U hU hx m r h1 h2 ψ hψ _hc using hss
  refine isLocallyNoetherian_of_affine_cover (S := fun x => ⟨U x, hU x⟩) ?_ fun x => ?_
  · refine top_le_iff.mp fun y _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hx y⟩
  · letI := (ψ x).toAlgebra
    haveI : Algebra.Etale _ _ := hψ x
    exact Algebra.FiniteType.isNoetherianRing (GlobalTheory.Et.ssModel (OK l K) ϖ (m x) (r x)) Γ(M.X, U x)

theorem good_flat (M : Model l K) (hM : M.Good) : Flat M.p := by
  haveI := OK_dvr (l := l) (K := K)
  obtain ⟨-, ϖ, hϖ, hss⟩ := hM
  choose U hU hx m r h1 h2 ψ hψ hc using hss
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (U := fun x => ⟨U x, hU x⟩) ?_ fun x => ?_
  · refine top_le_iff.mp fun y _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hx y⟩
  · have e : (M.p.appLE ⊤ (U x) le_top) = (Scheme.ΓSpecIso (CommRingCat.of (OK l K))).hom ≫
        CommRingCat.ofHom ((ψ x).comp (algebraMap (OK l K) _)) := by
      rw [hc x]; simp
    show RingHom.Flat (M.p.appLE ⊤ (U x) le_top).hom
    rw [e, CommRingCat.hom_comp]
    refine RingHom.Flat.comp (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)) ?_
    haveI : Etale (Spec.map (CommRingCat.ofHom (ψ x))) := HasRingHomProperty.Spec_iff.mpr (hψ x)
    have hf : RingHom.Flat (ψ x) := HasRingHomProperty.Spec_iff.mp (inferInstance : Flat (Spec.map (CommRingCat.ofHom (ψ x))))
    refine RingHom.Flat.comp ?_ hf
    exact RingHom.flat_algebraMap_iff.mpr (ssModel_flat (OK l K) ϖ hϖ (m x) (r x) (h1 x) (h2 x))

end Scheme

end CrystallineSemistableComparison
end
end
end
