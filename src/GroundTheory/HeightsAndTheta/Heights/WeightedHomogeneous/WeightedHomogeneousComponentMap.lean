module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Objects
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Examples
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DualModel
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConservationOfNumberLE
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericCycleCorresp
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumbersDVR

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace WeightedDegree

section Localization

variable {K : Type} {ι : K → Type} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (M₀ : Submonoid R) [IsLocalization M₀ R']


theorem ringKrullDim_quotient_map_le (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) :
    ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι ⧸ I.map (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι))) ≤
      ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  let f : PrimeSpectrum.zeroLocus (R := ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι) (I.map (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι))) →
      PrimeSpectrum.zeroLocus (R := ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) I :=
    fun Q ↦ ⟨PrimeSpectrum.comap (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι)) Q.1, by
      have h := Q.2
      simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at h ⊢
      exact Ideal.map_le_iff_le_comap.mp h⟩
  refine Order.krullDim_le_of_strictMono f (Monotone.strictMono_of_injective ?_ ?_)
  · intro Q₁ Q₂ h
    exact Ideal.comap_mono (f := algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι)) h
  · intro Q₁ Q₂ h
    apply Subtype.ext
    apply PrimeSpectrum.localization_comap_injective (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι) (M₀.map (C (σ := Σ k, ι k)))
    exact congrArg Subtype.val h

theorem weightedHomogeneousComponent_map [DecidableEq K] (b : K → ℕ) (y : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) :
    weightedHomogeneousComponent (blockWeight ι) b (map (algebraMap R R') y) =
      map (algebraMap R R') (weightedHomogeneousComponent (blockWeight ι) b y) := by
  classical
  ext d
  simp only [coeff_weightedHomogeneousComponent, coeff_map]
  split_ifs <;> simp


theorem isMultiHomogIdeal_map [DecidableEq K] {I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)} (hI : IsMultiHomogIdeal I) :
    IsMultiHomogIdeal (I.map (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι))) := by
  classical
  intro z hz b
  obtain ⟨⟨x, m⟩, hxm⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (M₀.map (C (σ := Σ k, ι k))) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι)).mp hz
  obtain ⟨r, hr, hrm⟩ := Submonoid.mem_map.mp m.2
  have hu : IsUnit (C (algebraMap R R' r) : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι) :=
    (IsLocalization.map_units R' (⟨r, hr⟩ : M₀)).map C
  have hm : algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι) (m : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) = C (algebraMap R R' r) := by
    rw [← hrm]
    exact map_C _ _
  rw [← Ideal.mul_unit_mem_iff_mem _ hu, mul_comm, ← weightedHomogeneousComponent_C_mul, mul_comm,
    ← hm, hxm]
  change weightedHomogeneousComponent _ b (map (algebraMap R R') (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) ∈ _
  rw [weightedHomogeneousComponent_map]
  exact Ideal.mem_map_of_mem _ (hI x x.2 b)


theorem cycEval_divCycle_map (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)
    (hdisj : ∀ W ∈ (P ⊔ Ideal.span {f}).minimalPrimes,
      Disjoint ((M₀.map (C (σ := Σ k, ι k)) : Submonoid (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) W)
    (n : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι) → ℤ) :
    cycEval (fun W ↦ n (W.map (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι)))) ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ))) =
      cycEval n ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (P.map (algebraMap (MRing ι R) (MRing ι R'))) (algebraMap (MRing ι R) (MRing ι R') f)) W : ℤ))) := by
  classical
  set M : Submonoid (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) := M₀.map (C (σ := Σ k, ι k)) with hM
  set φ := algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι) with hφ
  set J := P ⊔ Ideal.span {f} with hJdef
  have hJ : P.map φ ⊔ Ideal.span {φ f} = J.map φ := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hcorr : ∀ W ∈ J.minimalPrimes, (W.map φ).IsPrime ∧ (W.map φ).comap φ = W := fun W hW ↦
    ⟨IsLocalization.isPrime_of_isPrime_disjoint M _ W hW.1.1 (hdisj W hW),
      IsLocalization.under_map_of_isPrime_disjoint M (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι) hW.1.1 (hdisj W hW)⟩
  have hmin : ∀ W ∈ J.minimalPrimes, W.map φ ∈ (P.map φ ⊔ Ideal.span {φ f}).minimalPrimes := by
    intro W hW
    rw [hJ, IsLocalization.minimalPrimes_map M]
    show (W.map φ).comap φ ∈ J.minimalPrimes
    rw [(hcorr W hW).2]
    exact hW
  have hkey : ∀ W ∈ J.minimalPrimes, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ) = ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (P.map φ) (φ f)) (W.map φ) : ℤ) := by
    intro W hW
    have hWp : W.IsPrime := hW.1.1
    obtain ⟨hWp', hcomap⟩ := hcorr W hW
    have hrel : IsRelevant (W.map φ) ↔ IsRelevant W := by
      refine forall_congr' fun k ↦ exists_congr fun i ↦ not_congr ?_
      have hX : (X ⟨k, i⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι) = φ (X ⟨k, i⟩) := (MvPolynomial.map_X _ _).symm
      rw [hX, ← Ideal.mem_comap, hcomap]
    have hl : ∀ (h₁ : W.IsPrime) (h₂ : (W.map φ).IsPrime),
        @multAt _ _ _ _ J W h₁ = @multAt _ _ _ _ (P.map φ ⊔ Ideal.span {φ f}) (W.map φ) h₂ := by
      intro h₁ h₂
      have := h₂
      unfold multAt
      rw [hJ]
      exact GenericCycleCorresp.length_eq M J W (hdisj W hW)
    unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle
    by_cases hr : IsRelevant W
    · rw [dite_eq_left ⟨hW, hr⟩, dite_eq_left ⟨hmin W hW, hrel.mpr hr⟩, hl]
    · rw [dite_eq_right (fun h ↦ hr h.2), dite_eq_right (fun h ↦ hr (hrel.mp h.2))]
  have hsupp : ∀ (Q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι)) (x) (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι)),
      ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle Q x) W : ℤ) ≠ 0 → W ∈ (Q ⊔ Ideal.span {x}).minimalPrimes := by
    intro Q x W h
    unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle at h
    split_ifs at h with hh
    · exact hh.1
    · exact absurd rfl h
  have hsupp0 : ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι), ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ) ≠ 0 → W ∈ J.minimalPrimes := by
    intro W h
    unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle at h
    split_ifs at h with hh
    · exact hh.1
    · exact absurd rfl h
  unfold cycEval
  have hA : (∑ᶠ W, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ) * n (W.map φ)) =
      ∑ᶠ W ∈ J.minimalPrimes, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ) * n (W.map φ) := by
    rw [finsum_mem_def]
    congr 1
    funext W
    symm
    rw [Set.indicator_apply_eq_self]
    intro hW
    have : ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ) = 0 := by
      by_contra h
      exact hW (hsupp0 W h)
    rw [this, zero_mul]
  have hB : (∑ᶠ W, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (P.map φ) (φ f)) W : ℤ) * n W) =
      ∑ᶠ W ∈ (P.map φ ⊔ Ideal.span {φ f}).minimalPrimes, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (P.map φ) (φ f)) W : ℤ) * n W := by
    rw [finsum_mem_def]
    congr 1
    funext W
    symm
    rw [Set.indicator_apply_eq_self]
    intro hW
    have : ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (P.map φ) (φ f)) W : ℤ) = 0 := by
      by_contra h
      exact hW (hsupp _ _ W h)
    rw [this, zero_mul]
  rw [hA, hB]
  refine finsum_mem_eq_of_bijOn (fun W ↦ W.map φ) ⟨fun W hW ↦ hmin W hW, ?_, ?_⟩ ?_
  · intro W₁ hW₁ W₂ hW₂ h
    rw [← (hcorr W₁ hW₁).2, ← (hcorr W₂ hW₂).2]
    exact congrArg _ h
  · intro W' hW'
    have hW'm := hW'
    rw [hJ, IsLocalization.minimalPrimes_map M] at hW'm
    exact ⟨W'.comap φ, hW'm, IsLocalization.map_under M (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R' ι) W'⟩
  · intro W hW
    rw [hkey W hW]

end Localization

theorem charZero_fractionRing (O : Type) [CommRing O] [IsDomain O]
    (h : Function.Injective (Int.castRingHom O)) : CharZero (FractionRing O) := by
  apply charZero_of_injective_algebraMap (R := ℤ)
  rw [RingHom.ext_int (algebraMap ℤ (FractionRing O))
    ((algebraMap O (FractionRing O)).comp (Int.castRingHom O))]
  exact (IsFractionRing.injective O (FractionRing O)).comp h

end WeightedDegree

end

end GroundTheory.Heights₂.Heights
