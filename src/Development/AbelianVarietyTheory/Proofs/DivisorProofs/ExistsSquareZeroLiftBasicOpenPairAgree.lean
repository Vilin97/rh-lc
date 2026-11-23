module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.OreLocalization.Ring
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartSpecMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfSquareZeroThickeningStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroExtendLocalizationAwayPow

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue

def sqZeroInterp {R B S : Type} [CommRing R] [CommRing B] [CommRing S] [Algebra R B]
    [Algebra R S] (J : Ideal S) (hJ : J ^ 2 = ⊥) (α β : B →ₐ[R] S) (h : ∀ x, β x - α x ∈ J)
    (c : S) : B →ₐ[R] S where
  toFun x := α x + c * (β x - α x)
  map_one' := by simp
  map_mul' x y := by
    have hxy : (β x - α x) * (β y - α y) = 0 := by
      have hm := Ideal.mul_mem_mul (h x) (h y)
      rw [← pow_two, hJ] at hm
      simpa using hm
    simp only [map_mul]
    linear_combination (c - c ^ 2) * hxy
  map_zero' := by simp
  map_add' x y := by simp only [map_add (f := _)]; ring
  commutes' r := by simp

@[simp] theorem sqZeroInterp_apply {R B S : Type} [CommRing R] [CommRing B] [CommRing S]
    [Algebra R B] [Algebra R S] (J : Ideal S) (hJ : J ^ 2 = ⊥) (α β : B →ₐ[R] S)
    (h : ∀ x, β x - α x ∈ J) (c : S) (x : B) :
    sqZeroInterp J hJ α β h c x = α x + c * (β x - α x) := rfl

theorem exists_sqZero_extend_base (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S]
    [Algebra R' A] [Algebra R' S]
    [hfp : Algebra.FinitePresentation R' A] (J : Ideal S) (hJ : J ^ 2 = ⊥) (g : S)
    (φ : A →ₐ[R'] S) (ψ : A →ₐ[R'] Localization.Away g)
    (hψ : ∀ x, ψ x - algebraMap S (Localization.Away g) (φ x) ∈
      J.map (algebraMap S (Localization.Away g))) :
    ∃ N₀ : ℕ, ∃ χ : A →ₐ[R'] S, (∀ x, χ x - φ x ∈ J) ∧
      ∀ x, algebraMap S (Localization.Away g) (χ x) = algebraMap S (Localization.Away g) (φ x) +
        algebraMap S (Localization.Away g) g ^ N₀ *
          (ψ x - algebraMap S (Localization.Away g) (φ x)) := by
  obtain ⟨n, π, hπ, hker⟩ := hfp.out
  have hJg : (J.map (algebraMap S (Localization.Away g))) ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, hJ, Ideal.map_bot]
  have hy : ∀ i : Fin n, ∃ k : ℕ, ∃ y ∈ J, algebraMap S (Localization.Away g) y =
      algebraMap S (Localization.Away g) g ^ k * (ψ (π (MvPolynomial.X i)) -
        algebraMap S (Localization.Away g) (φ (π (MvPolynomial.X i)))) := by
    intro i
    obtain ⟨⟨⟨j, hj⟩, ⟨m, ⟨k, rfl⟩⟩⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff
      (Submonoid.powers g) (Localization.Away g)).1 (hψ (π (MvPolynomial.X i)))
    refine ⟨k, j, hj, ?_⟩
    simp only [map_pow] at e
    rw [← e]; ring
  choose k y hyJ hyeq using hy
  set M := Finset.univ.sup k with hM
  set y' : Fin n → S := fun i => g ^ (M - k i) * y i with hy'
  have hy'J : ∀ i, y' i ∈ J := fun i => J.mul_mem_left _ (hyJ i)
  have hy'eq : ∀ i, algebraMap S (Localization.Away g) (y' i) =
      algebraMap S (Localization.Away g) g ^ M * (ψ (π (MvPolynomial.X i)) -
        algebraMap S (Localization.Away g) (φ (π (MvPolynomial.X i)))) := by
    intro i
    have hk : k i ≤ M := Finset.le_sup (Finset.mem_univ i)
    simp only [y', map_mul, map_pow, hyeq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
  set α₀ : MvPolynomial (Fin n) R' →ₐ[R'] S := φ.comp π with hα₀
  set β₀ : MvPolynomial (Fin n) R' →ₐ[R'] S :=
    MvPolynomial.aeval (fun i => φ (π (MvPolynomial.X i)) + y' i) with hβ₀
  have hβα : ∀ p, β₀ p - α₀ p ∈ J := by
    intro p
    rw [← Ideal.Quotient.eq]
    have e : (Ideal.Quotient.mkₐ R' J).comp β₀ = (Ideal.Quotient.mkₐ R' J).comp α₀ := by
      apply MvPolynomial.algHom_ext; intro i
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, β₀, α₀, MvPolynomial.aeval_X]
      rw [Ideal.Quotient.eq]; simpa using hy'J i
    exact DFunLike.congr_fun e p
  have hloc : ∀ p, algebraMap S (Localization.Away g) (β₀ p) =
      algebraMap S (Localization.Away g) (α₀ p) + algebraMap S (Localization.Away g) g ^ M *
        (ψ (π p) - algebraMap S (Localization.Away g) (α₀ p)) := by
    intro p
    have e : (IsScalarTower.toAlgHom R' S (Localization.Away g)).comp β₀ =
        sqZeroInterp _ hJg ((IsScalarTower.toAlgHom R' S (Localization.Away g)).comp α₀)
          (ψ.comp π) (fun q => hψ (π q)) (algebraMap S (Localization.Away g) g ^ M) := by
      apply MvPolynomial.algHom_ext; intro i
      simp only [AlgHom.comp_apply, sqZeroInterp_apply, IsScalarTower.coe_toAlgHom', β₀, α₀,
        MvPolynomial.aeval_X, map_add, hy'eq]
      rfl
    exact DFunLike.congr_fun e p

  obtain ⟨s, hs⟩ := hker
  have hrel : ∀ r ∈ s, ∃ K : ℕ, g ^ K * (β₀ r - α₀ r) = 0 := by
    intro r hr
    have hrk : r ∈ RingHom.ker π.toRingHom := hs ▸ Ideal.subset_span hr
    have hπr : π r = 0 := hrk
    have hz : algebraMap S (Localization.Away g) (β₀ r - α₀ r) = 0 := by
      rw [map_sub, hloc]; simp [α₀, hπr]
    obtain ⟨⟨m, ⟨K, rfl⟩⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).1 hz
    exact ⟨K, hm⟩
  choose! Kf hKf using hrel
  set K := s.sup Kf with hK
  set θ := sqZeroInterp J hJ α₀ β₀ hβα (g ^ K) with hθ
  have hθker : ∀ r ∈ RingHom.ker π.toRingHom, θ r = 0 := by
    intro r hr
    rw [← hs] at hr
    have hle : Ideal.span (s : Set (MvPolynomial (Fin n) R')) ≤ RingHom.ker θ := by
      rw [Ideal.span_le]
      intro r hr
      have hrk : r ∈ RingHom.ker π.toRingHom := hs ▸ Ideal.subset_span hr
      have hπr : π r = 0 := hrk
      have hle' : Kf r ≤ K := Finset.le_sup hr
      show θ r = 0
      rw [hθ, sqZeroInterp_apply]
      have : α₀ r = 0 := by simp [α₀, hπr]
      have h2 := hKf r hr
      rw [this, sub_zero] at h2
      rw [this, sub_zero, zero_add, ← Nat.sub_add_cancel hle', pow_add, mul_assoc, h2, mul_zero]
    exact hle hr
  let χ₀ : A →ₐ[R'] S := (Ideal.Quotient.liftₐ (RingHom.ker π.toRingHom) θ hθker).comp
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom
  have hχ₀ : ∀ p, χ₀ (π p) = θ p := by
    intro p
    have : (Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    show Ideal.Quotient.liftₐ _ θ hθker ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π p)) = θ p
    rw [this]
    rfl
  refine ⟨K + M, χ₀, ?_, ?_⟩
  · intro x
    obtain ⟨p, rfl⟩ := hπ x
    rw [hχ₀, hθ, sqZeroInterp_apply]
    have : φ (π p) = α₀ p := rfl
    rw [this, add_sub_cancel_left]
    exact J.mul_mem_left _ (hβα p)
  · intro x
    obtain ⟨p, rfl⟩ := hπ x
    rw [hχ₀, hθ, sqZeroInterp_apply]
    have : φ (π p) = α₀ p := rfl
    rw [this, map_add (f := _), map_mul, map_sub, hloc, map_pow, pow_add]
    ring

theorem exists_sqZero_extend_pow : ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FinitePresentation R' A] (J : Ideal S), J ^ 2 = ⊥ → ∀ (g : S) (φ : A →ₐ[R'] S)
    (ψ : A →ₐ[R'] Localization.Away g),
    (∀ x, ψ x - algebraMap S (Localization.Away g) (φ x) ∈ J.map (algebraMap S (Localization.Away g))) →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ χ : A →ₐ[R'] S, (∀ x, χ x - φ x ∈ J) ∧
      ∀ x, algebraMap S (Localization.Away g) (χ x) = algebraMap S (Localization.Away g) (φ x) +
        algebraMap S (Localization.Away g) g ^ N * (ψ x - algebraMap S (Localization.Away g) (φ x)) := by
  intro R' A S _ _ _ _ _ _ J hJ g φ ψ hψ
  obtain ⟨N₀, χ₀, h1, h2⟩ := exists_sqZero_extend_base R' A S J hJ g φ ψ hψ
  refine ⟨N₀, fun N hN => ⟨sqZeroInterp J hJ φ χ₀ h1 (g ^ (N - N₀)), ?_, ?_⟩⟩
  · intro x
    rw [sqZeroInterp_apply, add_sub_cancel_left]
    exact J.mul_mem_left _ (h1 x)
  · intro x
    rw [sqZeroInterp_apply, map_add (f := _), map_mul, map_sub, h2, map_pow, add_sub_cancel_left,
      ← mul_assoc, ← pow_add, Nat.sub_add_cancel hN]

end GlobalTheory.SecGlue
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroExtendLocalizationAwayPowStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_sqZero_extend_localizationAway_pow : ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FinitePresentation R' A] (J : Ideal S), J ^ 2 = ⊥ → ∀ (g : S) (φ : A →ₐ[R'] S)
    (ψ : A →ₐ[R'] Localization.Away g),
    (∀ x, ψ x - algebraMap S (Localization.Away g) (φ x) ∈ J.map (algebraMap S (Localization.Away g))) →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ χ : A →ₐ[R'] S, (∀ x, χ x - φ x ∈ J) ∧
      ∀ x, algebraMap S (Localization.Away g) (χ x) = algebraMap S (Localization.Away g) (φ x) +
        algebraMap S (Localization.Away g) g ^ N * (ψ x - algebraMap S (Localization.Away g) (φ x)) := by
  first | exact @GlobalTheory.SecGlue.exists_sqZero_extend_pow | exact GlobalTheory.SecGlue.exists_sqZero_extend_pow | (intros; apply GlobalTheory.SecGlue.exists_sqZero_extend_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroLiftBasicOpenPairAgree

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue.Pair

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]; rfl

theorem chart_rebuild {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤) : spMap (chartHom V x hx) ≫ hV.fromSpec = x := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hV (isAffineOpen_top (Sp S)) hx.ge
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  have e : CommRingCat.ofHom (chartHom V x hx) =
      x.appLE V ⊤ hx.ge ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom := rfl
  show Spec.map (CommRingCat.ofHom (chartHom V x hx)) ≫ hV.fromSpec = x
  rw [e, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

theorem fromSpec_comp_top {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤ :=
  top_le_iff.1 fun _ _ => hV.range_fromSpec.subset ⟨_, rfl⟩

theorem chartHom_fromSpec {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) (hc : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤) :
    chartHom V (spMap χ ≫ hV.fromSpec) hc = χ := by
  have e := chart_rebuild hV (spMap χ ≫ hV.fromSpec) hc
  rw [cancel_mono] at e
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem chartHom_congr {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {x x' : Sp S ⟶ Y}
    (e : x = x') (h : x ⁻¹ᵁ V = ⊤) (h' : x' ⁻¹ᵁ V = ⊤) : chartHom V x h = chartHom V x' h' := by
  subst e; rfl

def strHom {R : Type} [CommRing R] (X : Over (Sp R)) (V : X.left.Opens) : R →+* Γ(X.left, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appLE ⊤ V (le_top : V ≤ X.hom ⁻¹ᵁ ⊤)).hom

theorem fromSpec_over {R : Type} [CommRing R] (X : Over (Sp R)) {V : X.left.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ X.hom = spMap (strHom X V) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom (isAffineOpen_top (Sp R)) hV
    (le_top : V ≤ X.hom ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, ← Spec.map_comp]; rfl

theorem chartHom_comp_strHom {R : Type} [CommRing R] (X : Over (Sp R)) {V : X.left.Opens}
    (hV : IsAffineOpen V) {S : Type} [CommRing S] (f : R →+* S) (u : Sp S ⟶ X.left) (hu : u ⁻¹ᵁ V = ⊤)
    (hf : u ≫ X.hom = spMap f) : (chartHom V u hu).comp (strHom X V) = f := by
  have e : spMap ((chartHom V u hu).comp (strHom X V)) = spMap f := by
    rw [spMap_comp', ← fromSpec_over X hV, ← Category.assoc, chart_rebuild, hf]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem smooth_strHom {R : Type} [CommRing R] (X : Over (Sp R)) [Smooth X.hom] {V : X.left.Opens}
    (hV : IsAffineOpen V) : (strHom X V).Smooth := by
  have h1 : RingHom.Smooth (X.hom.appLE ⊤ V le_top).hom :=
    X.hom.smooth_appLE (isAffineOpen_top (Sp R)) hV le_top
  have h2 : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective
  exact h2.comp h1

theorem awayMap_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (c : R) : Function.Surjective (Localization.awayMap π c) :=
  (IsLocalization.Away.map_surjective_iff _ _ π c).2 fun y =>
    let ⟨x, hx⟩ := hπ y; ⟨x, 0, by simp [hx]⟩

theorem ker_awayMap {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (c : R) :
    RingHom.ker (Localization.awayMap π c) = (RingHom.ker π).map (algebraMap R (Localization.Away c)) := by
  exact IsLocalization.ker_map (S := Localization.Away c) (Localization.Away (π c)) π
    (M := Submonoid.powers c) (Submonoid.map_powers π c)

theorem ker_awayMap_sq {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hsq : RingHom.ker π ^ 2 = ⊥) (c : R) : RingHom.ker (Localization.awayMap π c) ^ 2 = ⊥ := by
  rw [ker_awayMap, ← Ideal.map_pow, hsq, Ideal.map_bot]

theorem awayMap_comp_algebraMap {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (c : R) :
    (Localization.awayMap π c).comp (algebraMap R (Localization.Away c)) =
      (algebraMap R₀ (Localization.Away (π c))).comp π :=
  IsLocalization.map_comp _

end GlobalTheory.SecGlue.Pair

namespace GlobalTheory.SecGlue.Pair

theorem red_comp {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) {Y : Scheme.{0}} (g₀ : Sp R₀ ⟶ Y)
    (c d : R) (hcd : c ∣ d) (e : Sp (Localization.Away c) ⟶ Y)
    (he : spMap (Localization.awayMap π c) ≫ e = spMap (algebraMap R₀ (Localization.Away (π c))) ≫ g₀)
    (r : Localization.Away c →+* Localization.Away d)
    (hr : r.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.Away d)) :
    spMap (Localization.awayMap π d) ≫ spMap r ≫ e =
      spMap (algebraMap R₀ (Localization.Away (π d))) ≫ g₀ := by
  have hu : IsUnit (algebraMap R₀ (Localization.Away (π d)) (π c)) :=
    isUnit_of_dvd_unit (map_dvd _ (map_dvd π hcd)) (IsLocalization.Away.algebraMap_isUnit (π d))
  let h : Localization.Away (π c) →+* Localization.Away (π d) := IsLocalization.Away.lift (π c) hu
  have e1 : (Localization.awayMap π d).comp r = h.comp (Localization.awayMap π c) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers c)
    rw [RingHom.comp_assoc, hr, awayMap_comp_algebraMap, RingHom.comp_assoc, awayMap_comp_algebraMap,
      ← RingHom.comp_assoc, IsLocalization.Away.lift_comp]
  rw [← Category.assoc, ← spMap_comp', e1, spMap_comp', Category.assoc, he, ← Category.assoc,
    ← spMap_comp', IsLocalization.Away.lift_comp]

end GlobalTheory.SecGlue.Pair

namespace GlobalTheory.SecGlue.Pair

theorem equiv_restrict {R : Type} [CommRing R] (a b : R)
    (eP : Localization.Away (a * b) ≃ₐ[R] Localization.Away (algebraMap R (Localization.Away a) b))
    (ρ : Localization.Away a →+* Localization.Away (a * b))
    (hρ : ρ.comp (algebraMap R (Localization.Away a)) = algebraMap R (Localization.Away (a * b)))
    (y : Localization.Away a) :
    eP (ρ y) = algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) y := by
  have e : (eP.toAlgHom : Localization.Away (a * b) →+* _).comp ρ =
      algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    rw [RingHom.comp_assoc, hρ, eP.toAlgHom.comp_algebraMap]
    exact IsScalarTower.algebraMap_eq _ _ _
  exact RingHom.congr_fun e y

theorem exists_awayEquiv {R : Type} [CommRing R] (a b : R) :
    Nonempty (Localization.Away (a * b) ≃ₐ[R] Localization.Away (algebraMap R (Localization.Away a) b)) :=
  ⟨IsLocalization.algEquiv (Submonoid.powers (a * b)) _ _⟩

end GlobalTheory.SecGlue.Pair

namespace GlobalTheory.SecGlue.Pair

theorem comp_over {Y : Scheme.{0}} {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (e : Sp B ⟶ Y)
    (p : Y ⟶ Sp A) (f : A →+* B) (he : e ≫ p = spMap f) (r : B →+* C) (g : A →+* C) (hr : r.comp f = g) :
    (spMap r ≫ e) ≫ p = spMap g := by
  rw [Category.assoc, he, ← spMap_comp', hr]

end GlobalTheory.SecGlue.Pair

namespace GlobalTheory.SecGlue


open GlobalTheory.SecGlue.Pair in

theorem exists_pair_lift_comb : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (a b : R) (V : X.left.Opens), IsAffineOpen V →
    ∀ (ea : Sp (Localization.Away a) ⟶ X.left), ea ≫ X.hom = spMap (algebraMap R (Localization.Away a)) →
      spMap (Localization.awayMap π a) ≫ ea = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ → ea ⁻¹ᵁ V = ⊤ →
    ∀ (eb : Sp (Localization.Away b) ⟶ X.left), eb ≫ X.hom = spMap (algebraMap R (Localization.Away b)) →
      spMap (Localization.awayMap π b) ≫ eb = spMap (algebraMap R₀ (Localization.Away (π b))) ≫ g₀ →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ t : Sp (Localization.Away a) ⟶ X.left,
      t ≫ X.hom = spMap (algebraMap R (Localization.Away a)) ∧
      spMap (Localization.awayMap π a) ≫ t = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ ∧ t ⁻¹ᵁ V = ⊤ ∧
      GlobalTheory.SecGlue.IsCombIn V
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ ea)
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ t)
        ![spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a) ≫ eb]
        ![algebraMap R (Localization.Away (a * b)) b ^ N] := by
  intro R R₀ _ _ π hπ hsq X hX g₀ hg₀ a b V hV ea hea hea₀ heaV eb heb heb₀
  haveI := hX
  letI : Algebra R Γ(X.left, V) := (strHom X V).toAlgebra
  haveI : Algebra.Smooth R Γ(X.left, V) := smooth_strHom X hV

  have hρ : (IsLocalization.Away.awayToAwayRight (S := Localization.Away a) (P := Localization.Away (a * b))
      a b).comp (algebraMap R (Localization.Away a)) = algebraMap R (Localization.Away (a * b)) :=
    RingHom.ext (IsLocalization.Away.awayToAwayRight_eq a b)
  have hρ' : (IsLocalization.Away.awayToAwayLeft (S := Localization.Away b) (P := Localization.Away (a * b))
      b a).comp (algebraMap R (Localization.Away b)) = algebraMap R (Localization.Away (a * b)) :=
    RingHom.ext (IsLocalization.Away.awayToAwayLeft_eq b a)
  generalize IsLocalization.Away.awayToAwayRight (S := Localization.Away a) (P := Localization.Away (a * b))
      a b = ρ at hρ ⊢
  generalize IsLocalization.Away.awayToAwayLeft (S := Localization.Away b) (P := Localization.Away (a * b))
      b a = ρ' at hρ' ⊢
  have hred : spMap (Localization.awayMap π (a * b)) ≫ spMap ρ' ≫ eb =
      spMap (Localization.awayMap π (a * b)) ≫ spMap ρ ≫ ea :=
    (red_comp π g₀ b (a * b) (dvd_mul_left b a) eb heb₀ ρ' hρ').trans
      (red_comp π g₀ a (a * b) (dvd_mul_right a b) ea hea₀ ρ hρ).symm
  have h2 : (spMap ρ ≫ ea) ⁻¹ᵁ V = ⊤ := preimage_spMap_comp_eq_top ρ heaV
  have hbV : (spMap ρ' ≫ eb) ⁻¹ᵁ V = ⊤ :=
    (GlobalTheory.T.preimage_eq_of_square_zero_thickening (Localization.Away (a * b)) (Localization.Away (π (a * b))) (Localization.awayMap π (a * b))
      (awayMap_surjective π hπ _) (ker_awayMap_sq π hsq _) X.left (spMap ρ' ≫ eb) (spMap ρ ≫ ea) hred V).trans h2

  let φ : Γ(X.left, V) →ₐ[R] Localization.Away a :=
    { chartHom V ea heaV with
      commutes' := fun r => RingHom.congr_fun (chartHom_comp_strHom X hV _ ea heaV hea) r }

  obtain ⟨eP⟩ := exists_awayEquiv a b
  have hePc : (eP.toAlgHom : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)).comp
      (algebraMap R (Localization.Away (a * b))) = algebraMap R (Localization.Away (algebraMap R (Localization.Away a) b)) :=
    eP.toAlgHom.comp_algebraMap
  have heP := equiv_restrict a b eP ρ hρ
  have heb' : (spMap ρ' ≫ eb) ≫ X.hom = spMap (algebraMap R (Localization.Away (a * b))) :=
    comp_over eb X.hom _ heb ρ' _ hρ'
  let ψ : Γ(X.left, V) →ₐ[R] Localization.Away (algebraMap R (Localization.Away a) b) :=
    { (eP : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)).comp (chartHom V (spMap ρ' ≫ eb) hbV) with
      commutes' := fun r => by
        show eP (chartHom V (spMap ρ' ≫ eb) hbV (strHom X V r)) = _
        rw [← RingHom.comp_apply, chartHom_comp_strHom X hV _ _ hbV heb', AlgEquiv.commutes] }
  have hJ : RingHom.ker (Localization.awayMap π a) ^ 2 = ⊥ := ker_awayMap_sq π hsq a
  have hcond : ∀ x, ψ x - algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) (φ x) ∈
      (RingHom.ker (Localization.awayMap π a)).map (algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b))) := by
    intro x
    have hd : chartHom V (spMap ρ' ≫ eb) hbV x - chartHom V (spMap ρ ≫ ea) h2 x ∈
        RingHom.ker (Localization.awayMap π (a * b)) := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero,
        ← chartHom_spMap_comp V _ _ hbV (preimage_spMap_comp_eq_top _ hbV),
        ← chartHom_spMap_comp V _ _ h2 (preimage_spMap_comp_eq_top _ h2)]
      exact RingHom.congr_fun (chartHom_congr V hred _ _) x
    rw [ker_awayMap] at hd
    have h3 := Ideal.mem_map_of_mem (eP : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)) hd
    rw [Ideal.map_map, show (eP : Localization.Away (a * b) →+* Localization.Away (algebraMap R (Localization.Away a) b)).comp
        (algebraMap R (Localization.Away (a * b))) = algebraMap R (Localization.Away (algebraMap R (Localization.Away a) b)) from
        RingHom.ext fun r => eP.commutes r, map_sub] at h3
    rw [ker_awayMap, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    have e2 : algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) (φ x) =
        eP (chartHom V (spMap ρ ≫ ea) h2 x) := by
      rw [chartHom_spMap_comp V ρ ea heaV h2 x, heP]
      rfl
    rw [e2]
    exact h3
  obtain ⟨N₀, hN⟩ := GlobalTheory.T.exists_sqZero_extend_localizationAway_pow R Γ(X.left, V) (Localization.Away a) (RingHom.ker (Localization.awayMap π a)) hJ (algebraMap R (Localization.Away a) b) φ ψ hcond
  refine ⟨N₀, fun N hN' => ?_⟩
  obtain ⟨χ, hχJ, hχ⟩ := hN N hN'
  have htop := fromSpec_comp_top hV (χ : Γ(X.left, V) →+* Localization.Away a)
  refine ⟨spMap (χ : Γ(X.left, V) →+* Localization.Away a) ≫ hV.fromSpec, ?_, ?_, htop, ?_⟩
  · rw [Category.assoc, fromSpec_over, ← spMap_comp']
    exact congrArg spMap (RingHom.ext fun r => χ.commutes r)
  · rw [← hea₀, ← chart_rebuild hV ea heaV, ← Category.assoc, ← Category.assoc, ← spMap_comp',
      ← spMap_comp']
    refine congrArg (fun f => spMap f ≫ hV.fromSpec) (RingHom.ext fun x => ?_)
    have := hχJ x
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  · refine ⟨h2, preimage_spMap_comp_eq_top ρ htop, fun i => by rw [Matrix.cons_val_fin_one]; exact hbV, fun x => ?_⟩
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
    rw [chartHom_spMap_comp V ρ _ htop, chartHom_fromSpec hV _ htop, chartHom_spMap_comp V ρ ea heaV]
    apply eP.injective
    rw [map_add (f := _), map_mul, map_sub, map_pow, heP, heP, AlgEquiv.commutes,
      IsScalarTower.algebraMap_apply R (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b))]
    exact hχ x

end GlobalTheory.SecGlue
end
end
end
