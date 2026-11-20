import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConservationOfNumberLE
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericCycleCorresp
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumbersDVR

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace WeightedDegree

section Localization

variable {K : Type} {ι : K → Type} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  (M₀ : Submonoid R) [IsLocalization M₀ R']

include M₀ in

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

include M₀ in

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

include M₀ in

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

theorem WeightedDegree.proof : WeightedDegree.Statement := by
  intro ι _ _ n P D hdim a p hp
  classical
  let ι' : ι → Type := fun k ↦ Fin (n k + 1)
  let PI : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι') := P.ideal
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  set 𝔭 : Ideal ℤ := Ideal.span {(p : ℤ)} with h𝔭def
  have h𝔭max : 𝔭.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have h𝔭 : 𝔭.IsPrime := h𝔭max.isPrime
  have h𝔭0 : 𝔭 ≠ ⊥ := by
    rw [h𝔭def, Ne, Ideal.span_singleton_eq_bot]
    exact hpZ.ne_zero
  let O := Localization.AtPrime 𝔭
  have : IsDiscreteValuationRing O :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ h𝔭0 O
  let ϖ : O := (p : O)
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 O]
    change Ideal.map (algebraMap ℤ O) (Ideal.span {(p : ℤ)}) = _
    rw [Ideal.map_span, Set.image_singleton]
    simp [ϖ]
  have hϖ : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hmax
  let M : Submonoid (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι') := 𝔭.primeCompl.map (C (σ := Σ k, ι' k))
  let φ := algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι') (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι')
  let P' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι') := PI.map φ

  have hPdisj : Disjoint (M : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι')) PI := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrP
    have h0 := P.horizontal r hrP
    rw [h0] at hr
    exact hr 𝔭.zero_mem
  have hP'prime : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι') PI P.isPrime hPdisj
  have hP'comap : P'.comap φ = PI :=
    IsLocalization.under_map_of_isPrime_disjoint M (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι') P.isPrime hPdisj
  have hmp : IsMultiProjPrime P' :=
    { isPrime := hP'prime
      multiHomog := WeightedDegree.isMultiHomogIdeal_map 𝔭.primeCompl (fun f hf m ↦ P.homogeneous f hf m)
      relevant := fun k ↦ by
        obtain ⟨i, hi⟩ := P.relevant k
        refine ⟨i, fun h ↦ hi ?_⟩
        have h' : φ (X ⟨k, i⟩) ∈ P' := by
          rw [show φ (X ⟨k, i⟩) = X ⟨k, i⟩ from map_X _ _]
          exact h
        have h'' : (X ⟨k, i⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι') ∈ P'.comap φ := h'
        rw [hP'comap] at h''
        exact h'' }
  have hnt : P'.comap (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι') = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Ideal.mem_comap] at hx
    rw [Ideal.mem_bot]
    obtain ⟨⟨m, s⟩, hms⟩ := IsLocalization.surj 𝔭.primeCompl x
    simp only at hms
    have hmem : φ (C m) ∈ P' := by
      rw [show φ (C m) = C (algebraMap ℤ O m) from map_C _ _, ← hms, map_mul]
      exact P'.mul_mem_right _ hx
    have hmem' : (C m : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι') ∈ P'.comap φ := hmem
    rw [hP'comap] at hmem'
    have hm0 : m = 0 := P.horizontal m hmem'
    rw [hm0, map_zero] at hms
    exact ((IsLocalization.map_units O s).mul_left_eq_zero).mp hms
  have hdimle : ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι' ⧸ P') ≤ ((D + 1 + Fintype.card ι : ℕ) : WithBot ℕ∞) :=
    (WeightedDegree.ringKrullDim_quotient_map_le 𝔭.primeCompl PI).trans_eq hdim

  have key := ConservationOfNumberLE.proof.{0} IntNumAssoc.full SpecialCycleEval.full
    SpecialPieceRank.full GenericPieceRank.full SpecialIdealMultiHomog.full O ϖ hϖ ι ι' P' D hmp hnt
    hdimle a

  have hinjO : Function.Injective (Int.castRingHom O) := by
    rw [RingHom.ext_int (Int.castRingHom O) (algebraMap ℤ O)]
    exact IsLocalization.injective O 𝔭.primeCompl_le_nonZeroDivisors
  have : CharZero (FractionRing O) := WeightedDegree.charZero_fractionRing O hinjO
  have hgen : gNum P' a = intNum ℚ (P.ideal.map (MvPolynomial.map (Int.castRingHom ℚ))) a := by
    have hcomp : genFib P' = (PI.map (MvPolynomial.map (Int.castRingHom ℚ))).map
        (MvPolynomial.map (algebraMap ℚ (FractionRing O))) := by
      unfold genFib
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      refine RingHom.ext fun x ↦ ?_
      change MvPolynomial.map _ (MvPolynomial.map _ x) = MvPolynomial.map _ (MvPolynomial.map _ x)
      rw [MvPolynomial.map_map, MvPolynomial.map_map]
      exact congrArg (fun g ↦ MvPolynomial.map g x) (RingHom.ext_int _ _)
    unfold gNum
    rw [hcomp]
    exact (FieldNumbers.IntNumBaseChange.intersectionNumber_baseChange.1 ℚ (FractionRing O) ι ι' _).2 D a

  have : CharP (IsLocalRing.ResidueField O) p :=
    (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
      rw [show ((p : ℕ) : IsLocalRing.ResidueField O) = IsLocalRing.residue O ϖ by simp [ϖ],
        IsLocalRing.residue_eq_zero_iff, hmax]
      exact Ideal.subset_span rfl)
  let : Algebra (ZMod p) (IsLocalRing.ResidueField O) :=
    (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField O)).toAlgebra
  have hspec : ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι'), vNum (W.map φ) a =
      intNum (ZMod p) (W.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) a := by
    intro W
    have hcomp : specialIdeal (W.map φ) = (W.map (MvPolynomial.map (Int.castRingHom (ZMod p)))).map
        (MvPolynomial.map (algebraMap (ZMod p) (IsLocalRing.ResidueField O))) := by
      unfold specialIdeal
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      refine RingHom.ext fun x ↦ ?_
      change MvPolynomial.map _ (MvPolynomial.map _ x) = MvPolynomial.map _ (MvPolynomial.map _ x)
      rw [MvPolynomial.map_map, MvPolynomial.map_map]
      exact congrArg (fun g ↦ MvPolynomial.map g x) (RingHom.ext_int _ _)
    unfold vNum
    rw [hcomp]
    exact (FieldNumbers.IntNumBaseChange.intersectionNumber_baseChange.1 (ZMod p) (IsLocalRing.ResidueField O) ι ι' _).2 D a

  have hWdisj : ∀ W ∈ (PI ⊔ Ideal.span {(C (p : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι')}).minimalPrimes,
      Disjoint (M : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι')) W := by
    intro W hW
    have : W.IsPrime := hW.1.1
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrW
    have hle : 𝔭 ≤ W.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι') := by
      rw [h𝔭def, Ideal.span_le, Set.singleton_subset_iff]
      exact hW.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have heq := h𝔭max.eq_of_le (Ideal.comap_isPrime (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι') W).ne_top hle
    have hr' : r ∈ W.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι') := hrW
    rw [← heq] at hr'
    exact hr hr'
  have hmain := WeightedDegree.cycEval_divCycle_map (R' := O) 𝔭.primeCompl PI (C (p : ℤ)) hWdisj
    (fun W' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι') ↦ vNum W' a)
  have hCp : (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι') = φ (C (p : ℤ)) := by
    rw [show φ (C (p : ℤ)) = C (algebraMap ℤ O (p : ℤ)) from map_C _ _]
    simp [ϖ]
  calc intNum ℚ (P.ideal.map (MvPolynomial.map (Int.castRingHom ℚ))) a = gNum P' a := hgen.symm
    _ = cycEval (fun W ↦ vNum W a) ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P' (C ϖ)) W : ℤ))) := key.symm
    _ = cycEval (fun W ↦ vNum W a) ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P' (φ (C (p : ℤ)))) W : ℤ))) := by rw [hCp]
    _ = cycEval (fun W ↦ vNum (W.map φ) a) ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle PI (C (p : ℤ))) W : ℤ))) := hmain.symm
    _ = _ := by
      congr 1
      funext W
      exact hspec W

end

end GroundTheory.Heights₂.Heights
