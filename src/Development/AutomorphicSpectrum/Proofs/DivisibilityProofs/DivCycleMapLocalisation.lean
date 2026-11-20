import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericCycleCorresp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxSynthPendingDepth 1

attribute [local instance] MvPolynomial.algebraMvPolynomial in

theorem GlobalTheory.CompanionTheory.Ar.Num.divCycle_map_localisation :
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (Mo : Submonoid R) [IsLocalization Mo R'] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (W' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι)), W'.IsPrime → ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (P.map (MvPolynomial.map (algebraMap R R'))) (MvPolynomial.map (algebraMap R R') f)) W' : ℤ) = ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) (W'.comap (MvPolynomial.map (algebraMap R R'))) : ℤ) := by
  intro K _ _ ι _ R R' _ _ _ Mo _ P f W' hW'
  classical
  let φ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι := MvPolynomial.map (algebraMap R R')
  let M : Submonoid (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) := Mo.map (C (σ := (Σ k, ι k)) (R := R))
  haveI : IsLocalization M (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι) := MvPolynomial.isLocalization Mo R'
  have hφ : algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι) = φ := rfl
  set J := P ⊔ Ideal.span {f} with hJdef
  have hJ : P.map φ ⊔ Ideal.span {φ f} = J.map (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι)) := by
    rw [hφ, hJdef, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hdisj : Disjoint (M : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) (W'.comap (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι))) :=
    (IsLocalization.isPrime_iff_isPrime_disjoint M (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι) W').mp hW' |>.2
  have hWp : (W'.comap (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι))).IsPrime := Ideal.comap_isPrime _ _
  have hmap : (W'.comap (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι))).map
      (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι)) = W' := IsLocalization.map_comap M _ W'
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = W'.comap (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι)) := ⟨_, rfl⟩
  rw [← hQ] at hdisj hWp hmap
  subst hmap
  have hmin : Q.map (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι)) ∈ (P.map φ ⊔ Ideal.span {φ f}).minimalPrimes ↔
      Q ∈ J.minimalPrimes := by
    rw [hJ, IsLocalization.minimalPrimes_map M]
    show (Q.map (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι))).comap
      (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι)) ∈ J.minimalPrimes ↔ _
    rw [← hQ]
  have hrel : IsRelevant (Q.map (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι))) ↔ IsRelevant Q := by
    refine forall_congr' fun k => exists_congr fun i => not_congr ?_
    have hX : (X ⟨k, i⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι) =
        algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι) (X ⟨k, i⟩) := (MvPolynomial.map_X _ _).symm
    rw [hX, ← Ideal.mem_comap, ← hQ]
  have hl : ∀ (h₁ : Q.IsPrime) (h₂ : (Q.map (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι))).IsPrime),
      @multAt _ _ _ _ J Q h₁ =
        @multAt _ _ _ _ (P.map φ ⊔ Ideal.span {φ f})
          (Q.map (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι))) h₂ := by
    intro h₁ h₂
    unfold multAt
    rw [hJ]
    exact GenericCycleCorresp.length_eq M J Q hdisj
  have hQ' : Ideal.comap (MvPolynomial.map (algebraMap R R') : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι)
      (Q.map (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι))) = Q := hQ.symm
  rw [hQ']
  change ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (P.map φ) (φ f)) _ : ℤ) = ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) Q : ℤ)
  unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle
  by_cases hc : Q ∈ J.minimalPrimes ∧ IsRelevant Q
  · rw [dite_eq_left ⟨hmin.mpr hc.1, hrel.mpr hc.2⟩, dite_eq_left hc, hl]
  · rw [dite_eq_right (fun h => hc ⟨hmin.mp h.1, hrel.mp h.2⟩), dite_eq_right hc]
