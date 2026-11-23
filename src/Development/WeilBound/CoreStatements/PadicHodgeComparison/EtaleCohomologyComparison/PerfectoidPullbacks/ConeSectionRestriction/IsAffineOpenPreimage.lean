module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
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
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineOpenFiniteType

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoFT

theorem finiteType_affine {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType q] {W : X.Opens} (hW : IsAffineOpen W) :
    letI := (strV q W).toAlgebra; Algebra.FiniteType K Γ(X, W) := by
  have h1 : (q.appLE ⊤ W le_top).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) q inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
  have h3 : (strV q W).FiniteType := by
    have : strV q W = (q.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom := rfl
    rw [this]
    exact h1.comp h2
  letI := (strV q W).toAlgebra
  exact RingHom.finiteType_algebraMap.1 h3

end GlobalTheory.CompanionTheory.GeoFT
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineOpenFiniteTypeStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.affine_open_finiteType : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q] {W : X.Opens}, IsAffineOpen W → letI := (strV q W).toAlgebra; Algebra.FiniteType K Γ(X, W) := by
  first | exact @GlobalTheory.CompanionTheory.GeoFT.finiteType_affine | exact GlobalTheory.CompanionTheory.GeoFT.finiteType_affine | (intros; apply GlobalTheory.CompanionTheory.GeoFT.finiteType_affine <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenEvalSurjective

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo

theorem evV_surjective : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), IsClosedImmersion i → ∀ {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (hg : g ∈ grK K N e), 0 < e → Function.Surjective (evV i g (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl) := by
  intro K _ X N i hi g e hg he
  have hU : IsAffineOpen (Proj.basicOpen (grK K N) g) := Proj.isAffineOpen_basicOpen (grK K N) g hg he
  have hiso : IsIso (Proj.awayToSection (grK K N) g) := (Proj.basicOpenIsoAway (grK K N) g hg he).isIso_hom
  have h1 : Function.Surjective (Proj.awayToSection (grK K N) g).hom :=
    (ConcreteCategory.bijective_of_isIso (Proj.awayToSection (grK K N) g)).2
  have h2 : Function.Surjective (i.appLE _ (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]
    exact i.app_surjective _ hU
  exact h2.comp h1

end GlobalTheory.CompanionTheory.Geo
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpenEvalSurjectiveStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.basic_open_eval_surjective : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), IsClosedImmersion i → ∀ {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (hg : g ∈ grK K N e), 0 < e → Function.Surjective (evV i g (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl) := by
  first | exact @GlobalTheory.CompanionTheory.Geo.evV_surjective | exact GlobalTheory.CompanionTheory.Geo.evV_surjective | (intros; apply GlobalTheory.CompanionTheory.Geo.evV_surjective <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpensCoverOfFinite

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoCover

theorem X_mem_of_finite {K : Type} [Field K] {n m : ℕ}
    (I P : Ideal (MvPolynomial (Fin n) K)) [hPp : P.IsPrime] (hIP : I ≤ P)
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (y : Fin m → MvPolynomial (Fin n) K) (hy : ∀ k, y k ∈ P)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial (Fin n) K ⧸ I))
    (j : Fin n) : (MvPolynomial.X j : MvPolynomial (Fin n) K) ∈ P := by
  classical
  by_contra hj
  let φ : (MvPolynomial (Fin n) K ⧸ I) →+* (MvPolynomial (Fin n) K ⧸ P) := Ideal.Quotient.factor hIP
  have hφ : ∀ g, φ (Ideal.Quotient.mk I g) = Ideal.Quotient.mk P g := fun g => rfl
  let Q : Ideal (MvPolynomial (Fin n) K ⧸ I) := RingHom.ker φ
  haveI : Q.IsPrime := RingHom.ker_isPrime φ
  haveI : Algebra.IsIntegral (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial (Fin n) K ⧸ I) := Algebra.IsIntegral.of_finite _ _
  have hc0 : ∀ r ∈ Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)),
      ∃ c : K, φ r = Ideal.Quotient.mk P (MvPolynomial.C c) := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨0, by rw [hφ, map_zero, map_zero]; exact Ideal.Quotient.eq_zero_iff_mem.2 (hy k)⟩
    | algebraMap c => exact ⟨c, rfl⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hb
      exact ⟨c + d, by rw [φ.map_add, hc, hd, (MvPolynomial.C : K →+* MvPolynomial (Fin n) K).map_add, (Ideal.Quotient.mk P).map_add]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hb
      exact ⟨c * d, by rw [map_mul, hc, hd, map_mul, map_mul]⟩
  have h1 : (1 : MvPolynomial (Fin n) K ⧸ P) ≠ 0 := by
    intro h
    have : (1 : MvPolynomial (Fin n) K) ∈ P := Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_one]; exact h)
    exact hPp.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hmax : (Q.comap (algebraMap (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial (Fin n) K ⧸ I))).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h => h1 ?_, fun J x hle hx hxJ => ?_⟩
    · have : φ 1 = 0 := by simpa [Q, RingHom.mem_ker, Ideal.mem_comap] using h
      simpa using this
    · obtain ⟨c, hc⟩ := hc0 x.1 x.2
      have hc' : c ≠ 0 := by
        rintro rfl
        apply hx
        rw [Ideal.mem_comap]
        change φ x.1 = 0
        rw [hc, map_zero, map_zero]
      have hm : x * algebraMap K _ c⁻¹ - 1 ∈ J := by
        apply hle
        rw [Ideal.mem_comap]
        change φ (x.1 * algebraMap K _ c⁻¹ - 1) = 0
        rw [φ.map_sub, φ.map_mul, hc, φ.map_one]
        change _ * Ideal.Quotient.mk P (MvPolynomial.C c⁻¹) - 1 = 0
        rw [← map_mul (Ideal.Quotient.mk P), ← map_mul MvPolynomial.C, mul_inv_cancel₀ hc', map_one, map_one, sub_self]
      have := J.sub_mem (J.mul_mem_right (algebraMap K _ c⁻¹) hxJ) hm
      simpa using this
  have hQ : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under
    (R := Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k))) Q hmax
  have hjQ : Ideal.Quotient.mk I (MvPolynomial.X j) ∉ Q := fun h =>
    hj (Ideal.Quotient.eq_zero_iff_mem.1 ((hφ _).symm.trans (RingHom.mem_ker.1 h)))
  obtain ⟨a, b, hb, hab⟩ := hQ.exists_inv hjQ
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h2 : Ideal.Quotient.mk P (g * MvPolynomial.X j - 1) = 0 := by
    have := congrArg φ hab
    rw [φ.map_add, φ.map_mul, hφ, hφ, show φ b = 0 from hb, add_zero, map_one] at this
    rw [(Ideal.Quotient.mk P).map_sub, (Ideal.Quotient.mk P).map_mul, this, (Ideal.Quotient.mk P).map_one, sub_self]
  have h3 : MvPolynomial.homogeneousComponent 0 (g * MvPolynomial.X j - 1) ∈ P := by
    rw [← MvPolynomial.decomposition.decompose'_apply]
    exact hP 0 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
  have h4 : AddMonoidAlgebra.coeff (g * MvPolynomial.X j - 1) 0 = -1 := by
    have : MvPolynomial.constantCoeff (g * MvPolynomial.X j - 1) = -1 := by simp only [(MvPolynomial.constantCoeff : MvPolynomial (Fin n) K →+* K).map_sub, (MvPolynomial.constantCoeff : MvPolynomial (Fin n) K →+* K).map_mul, MvPolynomial.constantCoeff_X, mul_zero, (MvPolynomial.constantCoeff : MvPolynomial (Fin n) K →+* K).map_one, zero_sub]
    rwa [MvPolynomial.constantCoeff_eq] at this
  rw [MvPolynomial.homogeneousComponent_zero, h4, (MvPolynomial.C : K →+* MvPolynomial (Fin n) K).map_neg, (MvPolynomial.C : K →+* MvPolynomial (Fin n) K).map_one] at h3
  exact hPp.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.neg_mem h3))

theorem mem_of_evV_eq_zero {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) (p : X)
    (j : Fin (N + 1)) (hj : i p ∈ Proj.basicOpen (grK K N) (MvPolynomial.X j))
    {d : ℕ} {f : MvPolynomial (Fin (N + 1)) K} (hf : f ∈ grK K N (d • 1))
    (h : evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf) = 0) :
    f ∈ (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal := by
  by_contra hfP
  have hf' : f * MvPolynomial.X j ∈ grK K N (d + 1) := by
    have := SetLike.mul_mem_graded hf (xv_mem K N j)
    simpa using this
  have e : HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf =
      HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hf' := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.Away.val_mk]
    exact Localization.mk_eq_mk_iff.2 (Localization.r_of_eq (by
      change MvPolynomial.X j ^ (d + 1) * f = MvPolynomial.X j ^ d * (f * MvPolynomial.X j)
      ring))
  have hb := GroundTheory.Arith.SchemeCoh.ProjHom.basicOpen_awayToSection_isLocalizationElem (grK K N)
    (xv_mem K N j) one_pos hf' (Nat.succ_pos d)
  have hx : i p ∈ (PSpace K N).basicOpen (Proj.awayToSection (grK K N) (MvPolynomial.X j)
      (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hf')) := by
    erw [hb]
    refine ⟨hj, fun hm => ?_⟩
    exact ((i p : ProjectiveSpectrum (grK K N)).isPrime.mem_or_mem hm).elim hfP hj
  have hp : p ∈ i ⁻¹ᵁ (PSpace K N).basicOpen (Proj.awayToSection (grK K N) (MvPolynomial.X j)
      (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hf')) := hx
  rw [Scheme.preimage_basicOpen, ← e] at hp
  have h0 : i.app _ (Proj.awayToSection (grK K N) (MvPolynomial.X j)
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf)) = 0 := by
    rw [Scheme.Hom.app_eq_appLE]
    exact h
  rw [h0, Scheme.basicOpen_zero] at hp
  exact hp

theorem iSup_preimage_eq_top : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ {m e : ℕ}, 0 < e → ∀ (y : Fin m → MvPolynomial (Fin (N + 1)) K), (∀ k, (y k).IsHomogeneous e) → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ⨆ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) = ⊤ := by
  intro K _ X N i m e _ y _ hfin
  rw [_root_.eq_top_iff]
  intro p _
  by_contra hcon
  obtain ⟨j, hj⟩ : ∃ j, i p ∈ Proj.basicOpen (grK K N) (MvPolynomial.X j) := by
    have : i p ∈ (⨆ j : Fin (N + 1), Proj.basicOpen (grK K N) (MvPolynomial.X j)) := by
      erw [GroundTheory.Arith.SchemeCoh.ProjSpace.iSup_basicOpen_X]
      trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  have hy : ∀ k, y k ∈ (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal := by
    intro k
    by_contra hk
    apply hcon
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨k, hk⟩
  have hle : homIdeal i ≤ (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal := by
    rw [homIdeal, Ideal.span_le]
    rintro f ⟨d, hf, hv⟩
    exact mem_of_evV_eq_zero i p j hj hf (hv j)
  haveI : (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal.IsPrime :=
    (i p : ProjectiveSpectrum (grK K N)).isPrime
  exact hj (X_mem_of_finite _ _ hle
    (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).isHomogeneous y hy hfin j)

end GlobalTheory.CompanionTheory.GeoCover
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpensCoverOfFiniteStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.basic_opens_cover_of_finite : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ {m e : ℕ}, 0 < e → ∀ (y : Fin m → MvPolynomial (Fin (N + 1)) K), (∀ k, (y k).IsHomogeneous e) → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ⨆ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GeoCover.iSup_preimage_eq_top | exact GlobalTheory.CompanionTheory.GeoCover.iSup_preimage_eq_top | (intros; apply GlobalTheory.CompanionTheory.GeoCover.iSup_preimage_eq_top <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsAffineOpenPreimage

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)

theorem biInf_preimage {m : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (S : Finset (Fin m)) :
    ⨅ k ∈ S, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) = i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    ext x
    simp [yS, Proj.basicOpen]
  | insert a S ha ih =>
    rw [Finset.iInf_insert, ih]
    simp only [yS]
    rw [Finset.prod_insert ha, Proj.basicOpen_mul]
    rfl

theorem isAffineOpen_preimage (hci : IsClosedImmersion i) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ}
    (hg : g ∈ grK K N e) (he : 0 < e) : IsAffineOpen (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) := by
  haveI := hci
  exact (Proj.isAffineOpen_basicOpen (grK K N) g hg he).preimage i

theorem evV_surjective (hci : IsClosedImmersion i) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ}
    (hg : g ∈ grK K N e) (he : 0 < e) :
    Function.Surjective (evV i g (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl) := by
  first
    | exact GlobalTheory.T.basic_open_eval_surjective ..
    | (intros; apply GlobalTheory.T.basic_open_eval_surjective <;> assumption)

theorem range_resO_eq (hci : IsClosedImmersion i) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ}
    (hg : g ∈ grK K N e) (he : 0 < e) {V W : X.Opens} (hW : W = i ⁻¹ᵁ Proj.basicOpen (grK K N) g) (h : V ≤ W)
    (h' : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) : Set.range (resO h) = Set.range (evV i g V h') := by
  subst hW
  have e0 : i.appLE _ (i ⁻¹ᵁ Proj.basicOpen (grK K N) g) le_rfl ≫ X.presheaf.map (homOfLE h).op = i.appLE _ V h' :=
    Scheme.Hom.appLE_map i _ _
  have hcomp : evV i g V h' = (resO h).comp (evV i g _ le_rfl) := by
    refine RingHom.ext fun a => ?_
    simp only [evV, resO, RingHom.comp_apply, ← e0]
    rfl
  rw [hcomp, RingHom.coe_comp, Set.range_comp, (evV_surjective i hci hg he).range_eq, Set.image_univ]

theorem iSup_preimage_eq_top {m e : ℕ} (he : 0 < e) (y : Fin m → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k)))
      (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i)) :
    ⨆ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) = ⊤ := by
  first
    | exact GlobalTheory.T.basic_opens_cover_of_finite ..
    | (intros; apply GlobalTheory.T.basic_opens_cover_of_finite <;> assumption)

theorem finiteType_affine (q : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q] {W : X.Opens}
    (hW : IsAffineOpen W) : letI := (strV q W).toAlgebra; Algebra.FiniteType K Γ(X, W) := by
  first
    | exact GlobalTheory.T.affine_open_finiteType ..
    | (intros; apply GlobalTheory.T.affine_open_finiteType <;> assumption)

end CrystallineSemistableComparison.Pb
end
end
end
