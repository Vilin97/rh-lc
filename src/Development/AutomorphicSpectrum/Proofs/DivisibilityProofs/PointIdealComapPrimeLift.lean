import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ConstantsMonomialApproximation
import Development.WeilBound.CoreStatements.IdealCycleValues.LengthLocQuot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

section ConstantsCorrespondence

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {A : Type} [CommRing A] [Algebra A Ω]

theorem pointConeMap_map_intCast (y : (Σ k, ι k) → Ω) (g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι) :
    pointConeMap A y (MvPolynomial.map (Int.castRingHom A) g) = ReciprocityTheory.ChartRestriction.G.Geo.mConeMap y g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [pointConeMap, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, map_X]
    simp [pointConeMap, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap]

theorem comap_pointIdeal_eq_mCoordIdeal (y : (Σ k, ι k) → Ω) :
    (pointIdeal A y).comap (MvPolynomial.map (Int.castRingHom A)) = mCoordIdeal y := by
  ext g
  rw [Ideal.mem_comap]
  simp only [pointIdeal, mCoordIdeal, RingHom.mem_ker, pointConeMap_map_intCast]

theorem exists_pow_chartMonomial_mul_sub_map_mem {y : (Σ k, ι k) → Ω} (hA : HasConstants ℤ A y) (c : ∀ k, ι k)
    (r : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver A ι) :
    ∃ (n : ℕ) (g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι),
      (MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι)) ^ n * r -
        MvPolynomial.map (Int.castRingHom A) g ∈ pointIdeal A y := by
  have hs : MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι) =
      (∏ k, X ⟨k, c k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver A ι) := by
    simp [map_prod]
  rw [hs]
  set s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver A ι := ∏ k, X ⟨k, c k⟩ with hsdef
  induction r using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨n, G, -, hG⟩ := const_mul_chartMonomial_pow_form K ι Ω y A hA c a
    refine ⟨n, G, ?_⟩
    rw [mul_comm]
    exact hG
  | add p q hp hq =>
    obtain ⟨n, g, hg⟩ := hp
    obtain ⟨m, k, hk⟩ := hq
    refine ⟨n + m, (∏ k, X ⟨k, c k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι) ^ m * g + (∏ k, X ⟨k, c k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι) ^ n * k, ?_⟩
    have h := (pointIdeal A y).add_mem ((pointIdeal A y).mul_mem_left (s ^ m) hg)
      ((pointIdeal A y).mul_mem_left (s ^ n) hk)
    convert h using 1
    simp only [map_add (f := _), map_mul, map_pow, hs, ← hsdef]
    ring
  | mul_X p i hp =>
    obtain ⟨n, g, hg⟩ := hp
    refine ⟨n, g * X i, ?_⟩
    have h := (pointIdeal A y).mul_mem_right (X i) hg
    convert h using 1
    simp only [map_mul, map_X]
    ring

theorem exists_chart_not_mem {R : Type} [CommRing R] {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)} (hW : W.IsPrime) (hr : IsRelevant W) :
    ∃ c : ∀ k, ι k, (∏ k, X ⟨k, c k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) ∉ W := by
  choose c hc using hr
  refine ⟨c, fun h => ?_⟩
  obtain ⟨k, -, hk⟩ := (hW.prod_mem_iff).1 h
  exact hc k hk

theorem isRelevant_comap_map_intCast {W' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver A ι)} (hr : IsRelevant W') :
    IsRelevant (W'.comap (MvPolynomial.map (Int.castRingHom A)) : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι)) := by
  intro k
  obtain ⟨i, hi⟩ := hr k
  exact ⟨i, by simpa [Ideal.mem_comap] using hi⟩

end ConstantsCorrespondence

theorem pl_corr : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → (pointIdeal A y).comap (MvPolynomial.map (Int.castRingHom A)) = mCoordIdeal y ∧ (∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι), W.IsPrime → IsRelevant W → mCoordIdeal y ≤ W → ∃! W' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver A ι), W'.IsPrime ∧ pointIdeal A y ≤ W' ∧ W'.comap (MvPolynomial.map (Int.castRingHom A)) = W) ∧ ∀ (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι) (W' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver A ι)), W'.IsPrime → IsRelevant W' → pointIdeal A y ≤ W' → ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal A y) (MvPolynomial.map (Int.castRingHom A) f)) W' : ℤ) = ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (mCoordIdeal y) f) (W'.comap (MvPolynomial.map (Int.castRingHom A))) : ℤ) := by
  intro K _ _ ι _ Ω _ y A _ _ hA
  have hcomap := comap_pointIdeal_eq_mCoordIdeal (A := A) y
  refine ⟨hcomap, ?_, ?_⟩
  · intro W hW hr hle
    obtain ⟨c, hc⟩ := exists_chart_not_mem hW hr
    have h := exists_pow_chartMonomial_mul_sub_map_mem hA c
    obtain ⟨W', hW', hPW', hWc⟩ := BaseChangeColon.Corr.exists_lift h hW (by rw [hcomap]; exact hle) hc
    have hc' : MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι) ∉ W' := by
      intro hm
      apply hc
      rw [← hWc]
      exact hm
    refine ⟨W', ⟨hW', hPW', hWc⟩, ?_⟩
    rintro V ⟨hV, hPV, hVc⟩
    have hcV : MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι) ∉ V := by
      intro hm
      apply hc
      rw [← hVc]
      exact hm
    exact le_antisymm (BaseChangeColon.Corr.mono h hW' hPV hPW' hc' (by rw [hVc, hWc]))
      (BaseChangeColon.Corr.mono h hV hPW' hPV hcV (by rw [hVc, hWc]))
  · intro f W' hW' hr hPW'
    obtain ⟨c, hc⟩ : ∃ c : ∀ k, ι k,
        MvPolynomial.map (Int.castRingHom A) (∏ k, X ⟨k, c k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι) ∉ W' := by
      obtain ⟨c, hc⟩ := exists_chart_not_mem hW' hr
      exact ⟨c, by simpa [map_prod] using hc⟩
    have h := exists_pow_chartMonomial_mul_sub_map_mem hA c
    set φ := MvPolynomial.map (σ := (Σ k, ι k)) (Int.castRingHom A) with hφ
    set J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι) := mCoordIdeal y ⊔ Ideal.span {f} with hJdef
    have hJ : (pointIdeal A y).comap φ ≤ J := by rw [hcomap]; exact le_sup_left
    have hJeq : pointIdeal A y ⊔ Ideal.span {φ f} = pointIdeal A y ⊔ J.map φ := by
      rw [hJdef, Ideal.map_sup, Ideal.map_span, Set.image_singleton, ← sup_assoc]
      congr 1
      refine (sup_eq_left.2 ?_).symm
      rw [Ideal.map_le_iff_le_comap, hcomap]
    have hmin := BaseChangeColon.Corr.minimal_iff h J hJ hW' hPW' hc
    have hrel := isRelevant_comap_map_intCast hr
    have hWp : (W'.comap φ).IsPrime := Ideal.comap_isPrime φ W'
    have hlen := BaseChangeColon.Corr.length_eq h J hJ W' (W'.comap φ) rfl hPW' hc
    have hmin' : W' ∈ (pointIdeal A y ⊔ Ideal.span {φ f}).minimalPrimes ↔ W'.comap φ ∈ J.minimalPrimes := by
      rw [hJeq]
      exact hmin
    have hlen' : Module.length (Localization.AtPrime W')
        (LocalizedModule W'.primeCompl (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver A ι ⧸ (pointIdeal A y ⊔ Ideal.span {φ f}))) =
        Module.length (Localization.AtPrime (W'.comap φ))
          (LocalizedModule (W'.comap φ).primeCompl (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι ⧸ J)) := by
      rw [hJeq]
      exact hlen
    unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle
    by_cases hm : W'.comap φ ∈ J.minimalPrimes
    · rw [dite_eq_left ⟨hmin'.2 hm, hr⟩, dite_eq_left ⟨hm, hrel⟩]
      exact congrArg (fun t : ℕ∞ => ((ENat.toNat t : ℕ) : ℤ)) hlen'
    · rw [dite_eq_right (fun hh => hm (hmin'.1 hh.1)), dite_eq_right (fun hh => hm hh.1)]

end GlobalTheory.CompanionTheory.Ar.Num
