module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianReductionAlongIsogenyStrictHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveBaseChangeTwoDistinctPointsOfFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenGeometricallyConnectedFibresOfGenStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSectionsDistinctInFibresStatement
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSmoothOfRelativeDimensionOfGeneri
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFgSubringDescentGroupSectionsCurve
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Localization.InvSubmonoid
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Int.Basic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VeryDenseClosedPointObjectsOfMinimalPrimes
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSmoothOfRelativeDimensionOfGeneriStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_basicOpen_smoothOfRelativeDimension_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X : Over (Sp R)), Smooth X.hom → QuasiCompact X.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → ∀ g : ℕ, SmoothOfRelativeDimension g (pullback.snd X.hom (spMap e)) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → SmoothOfRelativeDimension g (pullback.snd X.hom (spMap ψ)) := by
  first | exact @GlobalTheory.SmoothRelDim.exists_basicOpen | exact GlobalTheory.SmoothRelDim.exists_basicOpen | (intros; apply GlobalTheory.SmoothRelDim.exists_basicOpen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFgSubringDescentGroupSectionsCurveStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_fg_subring_descent_group_sections_curve : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, 1 ≤ m → (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u → ∃ (R : Subring k) (G₁ : Over (Sp R)) (_ : GrpObj G₁), Algebra.FiniteType ℤ R ∧ IsUnit (m : R) ∧ IsCommMonObj G₁ ∧ Smooth G₁.hom ∧ IsSeparated G₁.hom ∧ QuasiCompact G₁.hom ∧ GeometricallyConnected (pullback.snd G₁.hom (spMap R.subtype)) ∧ SmoothOfRelativeDimension g (pullback.snd G₁.hom (spMap R.subtype)) ∧ (∃ s₁ : Finset (𝟙_ (Over (Sp R)) ⟶ G₁), s₁.card = s.card ∧ (∀ x ∈ s₁, x ^ m = 1) ∧ ∀ x ∈ s₁, ∀ y ∈ s₁, x ≠ y → spMap R.subtype ≫ x.left ≠ spMap R.subtype ≫ y.left) ∧ ∃ (P₁ : Polynomial R) (_ : P₁ ≠ 0) (u₁ : Sp (Localization.Away P₁) ⟶ G₁.left) (α β : R) (hα : IsUnit (Polynomial.evalRingHom α P₁)) (hβ : IsUnit (Polynomial.evalRingHom β P₁)), u₁ ≫ G₁.hom = spMap (algebraMap R (Localization.Away P₁)) ∧ spMap R.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁ ≠ spMap R.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁ := by
  first | exact @GlobalTheory.SpreadCurve.group_sections_curve_descend | exact GlobalTheory.SpreadCurve.group_sections_curve_descend | (intros; apply GlobalTheory.SpreadCurve.group_sections_curve_descend <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalPrimeCharNotMemFiniteTypeInt

section

@[expose] public section

namespace GlobalTheory

theorem isJacobsonRing_integers : IsJacobsonRing ℤ := by
  apply _root_.GlobalTheory.ClosedPts.jacobson_int <;> assumption

theorem closedPt_of_finiteType_int : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (f : R), f ≠ 0 → ∃ M : Ideal R, M.IsMaximal ∧ f ∉ M ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ M := by
  intro R _ _ _ f hf
  haveI := isJacobsonRing_integers
  let S := Localization.Away f
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  haveI : Nontrivial S := hinj.nontrivial
  haveI : Algebra.FiniteType R S := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) S
  haveI : Algebra.FiniteType ℤ S := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  obtain ⟨n, hn⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ n) := Ideal.Quotient.field n
  haveI : Algebra.FiniteType ℤ (S ⧸ n) := inferInstance
  haveI hfin := finite_of_finite_type_of_isJacobsonRing ℤ (S ⧸ n)
  have hZ : (algebraMap ℤ (S ⧸ n)).IsIntegral := fun x => IsIntegral.of_finite ℤ x
  let ψ : R →+* S ⧸ n := (Ideal.Quotient.mk n).comp (algebraMap R S)
  have hcomp : ψ.comp (Int.castRingHom R) = algebraMap ℤ (S ⧸ n) := RingHom.ext_int _ _
  have hψ : ψ.IsIntegral := RingHom.IsIntegral.tower_top (Int.castRingHom R) ψ (hcomp ▸ hZ)
  haveI hbot : (⊥ : Ideal (S ⧸ n)).IsMaximal := Ideal.bot_isMaximal
  let M : Ideal R := (⊥ : Ideal (S ⧸ n)).comap ψ
  have hM : M.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' ψ hψ ⊥
  refine ⟨M, hM, ?_, ?_⟩
  · intro hfM
    have h0 : ψ f = 0 := by simpa [M] using hfM
    have hu : IsUnit (algebraMap R S f) := IsLocalization.Away.algebraMap_isUnit f
    have hu' : IsUnit (ψ f) := hu.map (Ideal.Quotient.mk n)
    rw [h0] at hu'
    exact not_isUnit_zero hu'
  · have hMZ : (M.comap (Int.castRingHom R)).IsMaximal := by
      have : M.comap (Int.castRingHom R) = (⊥ : Ideal (S ⧸ n)).comap (algebraMap ℤ (S ⧸ n)) := by
        rw [← hcomp, ← Ideal.comap_comap]
      rw [this]
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hZ ⊥
    obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal (M.comap (Int.castRingHom R))
    change _ = Ideal.span {a} at ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at ha
      exact Ring.ne_bot_of_isMaximal_of_not_isField hMZ Int.not_isField ha
    have hpr : Prime a := by
      rw [← Ideal.span_singleton_prime ha0, ← ha]
      exact hMZ.isPrime
    refine ⟨a.natAbs, Int.prime_iff_natAbs_prime.1 hpr, ?_⟩
    have hmem : (a.natAbs : ℤ) ∈ M.comap (Int.castRingHom R) := by
      rw [ha, Ideal.mem_span_singleton]
      exact Int.dvd_natAbs.2 dvd_rfl
    have h2 := Ideal.mem_comap.1 hmem
    simpa only [eq_intCast, Int.cast_natCast] using h2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalPrimeCharNotMemFiniteTypeIntStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_maximal_prime_char_not_mem_finiteType_int : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (f : R), f ≠ 0 → ∃ M : Ideal R, M.IsMaximal ∧ f ∉ M ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ M := by
  first | exact @GlobalTheory.closedPt_of_finiteType_int | exact GlobalTheory.closedPt_of_finiteType_int | (intros; apply GlobalTheory.closedPt_of_finiteType_int <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharPSpecialisationSmoothCommGroupCurve

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CharPSpec

theorem spMap_comp_eq' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {f : A →+* B} {g : B →+* C}
    {h : A →+* C} (e : g.comp f = h) : spMap g ≫ spMap f = spMap h := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

theorem exists_charP_specialization : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, 1 ≤ m → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u → ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (p : ℕ) (_ : Fact p.Prime) (_ : CharP k' p) (G' : Over (Sp k')) (_ : GrpObj G'), GlobalTheory.SS.SmConn G' ∧ SmoothOfRelativeDimension g G'.hom ∧ (m : k') ≠ 0 ∧ (∃ s' : Finset (𝟙_ (Over (Sp k')) ⟶ G'), (∀ x ∈ s', x ^ m = 1) ∧ s'.card = s.card) ∧ ∃ (P' : Polynomial k') (_ : P' ≠ 0) (u' : Sp (Localization.Away P') ⟶ G'.left) (a' b' : Localization.Away P' →ₐ[k'] k'), u' ≫ G'.hom = spMap (algebraMap k' (Localization.Away P')) ∧ spMap a'.toRingHom ≫ u' ≠ spMap b'.toRingHom ≫ u' := by
  intro k _ _ _ G _ hG g hg m hm s hs P hP u a b hu hab
  classical
  have hm0 : (m : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨R, G₁, _, hfg, hmR, hcomm, hsm, hsep, hqc, hgc, hrd, ⟨s₁, hcard, hs₁, hdist⟩, P₁, hP₁, u₁, α, β, hα, hβ,
    hu₁, hαβ⟩ := GlobalTheory.T.exists_fg_subring_descent_group_sections_curve k G hG g hg m hm hm0 s hs P hP u a b hu hab
  haveI : Algebra.FiniteType ℤ R := hfg
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hinj : Function.Injective R.subtype := Subtype.val_injective
  obtain ⟨f₁, hf₁, H₁⟩ := GlobalTheory.T.exists_basicOpen_smoothOfRelativeDimension_of_generic R G₁ hsm hqc k R.subtype hinj g hrd
  obtain ⟨f₂, hf₂, H₂⟩ := GlobalTheory.T.exists_basicOpen_geometricallyConnected_fibres_of_generic R G₁ hsm hqc k R.subtype hinj hgc
  obtain ⟨f₃, hf₃, H₃⟩ := GlobalTheory.T.exists_basicOpen_sections_distinct_in_fibres R G₁ hsep k R.subtype hinj (s₁.image fun x => x.left)
    (by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
      exact Over.w y)
    (by
      intro x hx y hy hxy
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
      exact hdist x' hx' y' hy' fun h => hxy (by rw [h]))
  have hsec : ∀ (c₀ : R) (hc₀ : IsUnit (Polynomial.evalRingHom c₀ P₁)),
      spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hc₀) ≫ u₁ ≫ G₁.hom = 𝟙 _ := by
    intro c₀ hc₀
    rw [hu₁, spMap_comp_eq' (h := RingHom.id R)]
    · show Spec.map (CommRingCat.ofHom (RingHom.id R)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    · ext r
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R (Polynomial R) (Localization.Away P₁),
        IsLocalization.Away.lift_eq]
      simp
  obtain ⟨f₄, hf₄, H₄⟩ := GlobalTheory.T.exists_basicOpen_sections_distinct_in_fibres R G₁ hsep k R.subtype hinj
    {spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁,
      spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁}
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [Category.assoc]; exact hsec α hα
      · rw [Finset.mem_singleton.mp hx, Category.assoc]; exact hsec β hβ)
    (by
      intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx <;> rcases Finset.mem_insert.mp hy with rfl | hy
      · exact absurd rfl hxy
      · rw [Finset.mem_singleton.mp hy]; exact hαβ
      · rw [Finset.mem_singleton.mp hx]; exact Ne.symm hαβ
      · rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy] at hxy; exact absurd rfl hxy)
  have hlc : R.subtype P₁.leadingCoeff ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP₁
  set f := f₁ * f₂ * f₃ * f₄ * P₁.leadingCoeff with hfdef
  have hf : f ≠ 0 := by
    intro h
    have := congrArg R.subtype h
    rw [map_zero, hfdef] at this
    simp only [map_mul] at this
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hf₁ hf₂) hf₃) hf₄) hlc) this
  obtain ⟨M, hM, hfM, p, hp, hpM⟩ := GlobalTheory.T.exists_maximal_prime_char_not_mem_finiteType_int R f hf
  letI := Ideal.Quotient.field M
  let ψ : R →+* AlgebraicClosure (R ⧸ M) := (algebraMap (R ⧸ M) _).comp (Ideal.Quotient.mk M)
  have hψ : ∀ r, r ∉ M → IsUnit (ψ r) := by
    intro r hr
    refine isUnit_iff_ne_zero.mpr ?_
    rw [RingHom.comp_apply, map_ne_zero_iff _ (algebraMap (R ⧸ M) _).injective]
    exact fun h => hr (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hu := hψ f hfM
  simp only [hfdef, map_mul, IsUnit.mul_iff] at hu
  obtain ⟨⟨⟨⟨u1, u2⟩, u3⟩, u4⟩, u5⟩ := hu
  haveI : Fact p.Prime := ⟨hp⟩
  have hpF : CharP (AlgebraicClosure (R ⧸ M)) p := by
    rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast ψ, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr hpM, map_zero]
  refine ⟨AlgebraicClosure (R ⧸ M), inferInstance, inferInstance, p, inferInstance, hpF,
    (Over.pullback (spMap ψ)).obj G₁, inferInstance, ?_, H₁ _ ψ u1, ?_, ?_, ?_⟩
  · refine ⟨inferInstance, ?_, ?_, ?_, H₂ _ ψ u2⟩
    · show Smooth (pullback.snd _ _); infer_instance
    · show IsSeparated (pullback.snd _ _); infer_instance
    · show QuasiCompact (pullback.snd _ _); infer_instance
  · rw [← map_natCast ψ]
    exact (hmR.map ψ).ne_zero
  · refine ⟨s₁.image (GlobalTheory.IsogRed.sec (spMap ψ)), ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rw [← GlobalTheory.IsogRed.sec_pow, hs₁ y hy]
      simpa using (GlobalTheory.IsogRed.sec_pow (spMap ψ) y 0).trans (pow_zero _)
    · rw [← hcard]
      refine Finset.card_image_of_injOn fun x hx y hy hxy => ?_
      by_contra hne
      have e := congrArg (fun z => z.left ≫ pullback.fst G₁.hom (spMap ψ)) hxy
      simp only [GlobalTheory.IsogRed.sec_left] at e
      exact H₃ _ ψ u3 x.left (Finset.mem_image_of_mem _ hx) y.left (Finset.mem_image_of_mem _ hy)
        (fun h => hne (Over.OverMorphism.ext h)) e
  · exact GlobalTheory.T.curve_baseChange_two_distinct_points_of_field R _ ψ G₁ P₁ u₁ α β hα hβ hu₁ u5
      (H₄ _ ψ u4 _ (Finset.mem_insert_self _ _) _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        (fun h => hαβ (by rw [h])))

end GlobalTheory.CharPSpec
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharPSpecialisationSmoothCommGroupCurveStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_charP_specialization_smooth_commGroup_curve : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, 1 ≤ m → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u → ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (p : ℕ) (_ : Fact p.Prime) (_ : CharP k' p) (G' : Over (Sp k')) (_ : GrpObj G'), GlobalTheory.SS.SmConn G' ∧ SmoothOfRelativeDimension g G'.hom ∧ (m : k') ≠ 0 ∧ (∃ s' : Finset (𝟙_ (Over (Sp k')) ⟶ G'), (∀ x ∈ s', x ^ m = 1) ∧ s'.card = s.card) ∧ ∃ (P' : Polynomial k') (_ : P' ≠ 0) (u' : Sp (Localization.Away P') ⟶ G'.left) (a' b' : Localization.Away P' →ₐ[k'] k'), u' ≫ G'.hom = spMap (algebraMap k' (Localization.Away P')) ∧ spMap a'.toRingHom ≫ u' ≠ spMap b'.toRingHom ≫ u' := by
  first | exact @GlobalTheory.CharPSpec.exists_charP_specialization | exact GlobalTheory.CharPSpec.exists_charP_specialization | (intros; apply GlobalTheory.CharPSpec.exists_charP_specialization <;> assumption)
end
end
