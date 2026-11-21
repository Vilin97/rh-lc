module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocHomAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerEqPowRamificationIdxMulUnitIntegralClStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarExistsLocalKummerElement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarExistsFractionLocalisationNormalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealLocalizationEqSpanOfReducedArtinianA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealSpanImageUniformizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerUnitRadicandQuotientRootIsReduced
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingKummerAdjoinRootQuotientRootStatement

@[expose] public section

open IsLocalRing
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

open IsLocalRing in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
open Polynomial in
private lemma maximalIdeal_eq_span_of_kummer_tower (A W : Type) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing W] [IsLocalRing W] (Φ : A →+* W) (ϖ : A) (u : Aˣ) (m k : ℕ)
    (hϖ : Irreducible ϖ) (hm : IsUnit (m : A)) (hk : 0 < k) (y τ : W) (hy : y ^ m = Φ u)
    (hτ : τ ^ k = Φ ϖ * y) (hτm : τ ∈ maximalIdeal W) (hτnz : τ ∈ nonZeroDivisors W)
    (hfrac : ∀ w : W, ∃ x z, x ∈ Subring.closure (Set.range Φ ∪ {τ}) ∧
      z ∈ Subring.closure (Set.range Φ ∪ {τ}) ∧ z ∈ nonZeroDivisors W ∧ z * w = x) :
    maximalIdeal W = Ideal.span {τ} := by
  obtain ⟨gB, hgB_of, hgB_root⟩ : ∃ gB : AdjoinRoot (X ^ m - C (u : A)) →+* W,
      (∀ a, gB (AdjoinRoot.of _ a) = Φ a) ∧ gB (AdjoinRoot.root _) = y :=
    ⟨AdjoinRoot.lift Φ y (by simp [hy]), fun a => AdjoinRoot.lift_of _, AdjoinRoot.lift_root _⟩
  obtain ⟨g, hg_of, hg_root⟩ : ∃ g : AdjoinRoot (X ^ k - C (AdjoinRoot.of (X ^ m - C (u : A)) ϖ *
        AdjoinRoot.root (X ^ m - C (u : A)))) →+* W,
      (∀ b, g (AdjoinRoot.of _ b) = gB b) ∧ g (AdjoinRoot.root _) = τ :=
    ⟨AdjoinRoot.lift gB τ (by simp [hgB_of, hgB_root, hτ]), fun b => AdjoinRoot.lift_of _,
      AdjoinRoot.lift_root _⟩
  haveI hn : (Ideal.comap g (maximalIdeal W)).IsPrime := Ideal.comap_isPrime g (maximalIdeal W)
  have hTn : AdjoinRoot.root (X ^ k - C (AdjoinRoot.of (X ^ m - C (u : A)) ϖ *
      AdjoinRoot.root (X ^ m - C (u : A)))) ∈ Ideal.comap g (maximalIdeal W) := by
    rw [Ideal.mem_comap, hg_root]
    exact hτm
  have hmaxV := _root_.GlobalTheory.maximalIdeal_localization_eq_span_of_reduced_artinian _ _ (_root_.GlobalTheory.kummerUnit_quotRoot_isReduced A ϖ u m k hϖ hm hk)
    (_root_.GlobalTheory.T.isArtinianRing_kummerAdjoinRoot_quotient_root A ϖ u m k hϖ hm hk) _ hTn
  haveI : IsNoetherianRing (AdjoinRoot (X ^ k - C (AdjoinRoot.of (X ^ m - C (u : A)) ϖ *
      AdjoinRoot.root (X ^ m - C (u : A))))) := inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime (Ideal.comap g (maximalIdeal W))) :=
    IsLocalization.isNoetherianRing (Ideal.comap g (maximalIdeal W)).primeCompl _ inferInstance
  have hunit : ∀ s : (Ideal.comap g (maximalIdeal W)).primeCompl, IsUnit (g s) := by
    intro s
    by_contra h
    exact s.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hlift := fun r => IsLocalization.lift_eq (M := (Ideal.comap g (maximalIdeal W)).primeCompl)
    (S := Localization.AtPrime (Ideal.comap g (maximalIdeal W))) hunit r
  obtain ⟨φ, hφ⟩ : ∃ φ : Localization.AtPrime (Ideal.comap g (maximalIdeal W)) →+* W,
      ∀ r, φ (algebraMap _ _ r) = g r := ⟨IsLocalization.lift hunit, hlift⟩
  have key := _root_.GlobalTheory.maximalIdeal_eq_span_map_of_fractions (Localization.AtPrime (Ideal.comap g (maximalIdeal W))) W φ _ hmaxV (by rw [hφ, hg_root]; exact hτm)
    (by rw [hφ, hg_root]; exact hτnz) ?_
  · rw [key, hφ, hg_root]
  intro w
  obtain ⟨x, z, hx, hz, hznz, hzw⟩ := hfrac w
  have hle : Subring.closure (Set.range Φ ∪ {τ}) ≤ φ.range := by
    rw [Subring.closure_le]
    refine Set.union_subset ?_ ?_
    · rintro _ ⟨a, rfl⟩
      exact ⟨algebraMap _ _ (AdjoinRoot.of _ (AdjoinRoot.of _ a)), by rw [hφ, hg_of, hgB_of]⟩
    · rintro _ rfl
      exact ⟨algebraMap _ _ (AdjoinRoot.root _), by rw [hφ, hg_root]⟩
  obtain ⟨x', rfl⟩ := hle hx
  obtain ⟨z', rfl⟩ := hle hz
  exact ⟨x', z', hznz, hzw⟩


theorem _root_.GlobalTheory.abhyankar_ramificationIdx_eq_one : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ e) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    Q.ramificationIdx D = 1 := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ ⟨ψ⟩ hπ he hdiv _ _ _ Q _
  haveI : Q.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  haveI : IsDedekindDomain (integralClosure S L) := integralClosure.isDedekindDomain S K L
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      simp at he
    · exact h
  let t := ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π))
  have hte : t ^ e = algebraMap S D π := by
    dsimp only [t]
    apply ψ.injective
    rw [map_pow, AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
    have h := AdjoinRoot.eval₂_root (Polynomial.X ^ e - Polynomial.C π)
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
    rw [sub_eq_zero.1 h]
    rfl
  have hunder : Q.under D = maximalIdeal D :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q)
  have htQ : algebraMap D (integralClosure D (TensorProduct S D L)) t ∈ Q := by
    change t ∈ Q.under D
    rw [hunder]
    apply (IsLocalRing.mem_maximalIdeal t).2
    intro h
    have hev : (Polynomial.X ^ e - Polynomial.C π : Polynomial S).eval₂
        (algebraMap S (ResidueField S)) 0 = 0 := by
      simp [Polynomial.eval₂_sub, zero_pow he0.ne']
      exact hπ.not_isUnit
    have hroot : IsUnit (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π)) := by
      simpa [t] using h.map ψ
    have hunit := hroot.map (AdjoinRoot.lift (algebraMap S (ResidueField S)) 0 hev)
    rw [AdjoinRoot.lift_root] at hunit
    exact not_isUnit_zero hunit
  have ht : algebraMap D (Localization.AtPrime Q) t ∈ maximalIdeal (Localization.AtPrime Q) := by
    rw [IsScalarTower.algebraMap_apply D (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q _).2 htQ
  have hπL : algebraMap S L π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply S K L]
    intro h
    rw [map_eq_zero_iff _ (algebraMap K L).injective, IsFractionRing.to_map_eq_zero_iff] at h
    exact hπ.ne_zero h
  have hπTensor : algebraMap D (D ⊗[S] L) (algebraMap S D π) =
      Algebra.TensorProduct.includeRight (algebraMap S L π) :=
    DFunLike.congr_fun Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap π
  have htnz : algebraMap D (Localization.AtPrime Q) t ∈ nonZeroDivisors (Localization.AtPrime Q) := by
    rw [IsScalarTower.algebraMap_apply D (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)]
    apply IsLocalization.nonZeroDivisors_le_comap Q.primeCompl (Localization.AtPrime Q)
    apply mem_nonZeroDivisors_of_injective (f := (integralClosure D (D ⊗[S] L)).val)
      Subtype.val_injective
    change algebraMap D (D ⊗[S] L) t ∈ nonZeroDivisors (D ⊗[S] L)
    apply IsUnit.mem_nonZeroDivisors
    rw [← isUnit_pow_iff he0.ne', ← map_pow, hte, hπTensor]
    exact (Ne.isUnit hπL).map _
  have hπO : algebraMap S (integralClosure S L) π ≠ 0 := by
    intro h
    apply hπL
    rw [IsScalarTower.algebraMap_apply S (integralClosure S L) L, h, map_zero]
  have hπP : algebraMap S (integralClosure S L) π ∈
      Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q := by
    rw [Ideal.mem_comap]
    have hpow : _root_.GlobalTheory.AbhyankarLocal.toNorm S L D (algebraMap S (integralClosure S L) π) =
        (algebraMap D (integralClosure D (TensorProduct S D L)) t) ^ e := by
      apply Subtype.ext
      rw [_root_.GlobalTheory.AbhyankarLocal.toNorm_coe, ← map_pow, hte]
      change (1 : D) ⊗ₜ[S] (algebraMap S L π) = algebraMap D (TensorProduct S D L) (algebraMap S D π)
      exact hπTensor.symm
    rw [hpow]
    exact Ideal.pow_mem_of_mem Q htQ e he0
  haveI hPmax : (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q).IsMaximal := by
    refine Ideal.IsPrime.isMaximal inferInstance ?_
    intro h
    rw [h] at hπP
    exact hπO hπP
  obtain ⟨ϖ, hϖ, u, hu⟩ := _root_.GlobalTheory.pi_eq_pow_ramificationIdx_mul_unit S K L π e D
    (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q) hπ hπP
  obtain ⟨k, hk⟩ := hdiv _ hPmax
  obtain ⟨y, hym, hyk⟩ := _root_.GlobalTheory.AbhyankarLocal.exists_kummer_element S K L π e D ψ hπ he0 Q _ k ϖ u hk.symm hu
  have hP0 : Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q ≠ ⊥ := by
    intro h
    rw [h] at hπP
    exact hπO hπP
  haveI : IsDiscreteValuationRing
      (Localization.AtPrime (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q)) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (integralClosure S L) hP0 _
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      omega
    · exact h
  have hmu : IsUnit (((Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q).ramificationIdx S : ℕ) :
      Localization.AtPrime (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q)) := by
    have h := he.map (algebraMap S
      (Localization.AtPrime (Ideal.comap (_root_.GlobalTheory.AbhyankarLocal.toNorm S L D) Q)))
    rw [map_natCast, hk, Nat.cast_mul] at h
    exact isUnit_of_mul_isUnit_left h
  have hmax := maximalIdeal_eq_span_of_kummer_tower _ (Localization.AtPrime Q)
    (_root_.GlobalTheory.AbhyankarLocal.locHom Q) ϖ u _ k hϖ hmu hk0 y _ hym hyk ht htnz
    (_root_.GlobalTheory.AbhyankarLocal.exists_frac_closure S K L π e D ψ hπ he0 Q)
  have hmapmax : Ideal.map (algebraMap D (Localization.AtPrime Q)) (Ideal.under D Q) =
      maximalIdeal (Localization.AtPrime Q) := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro d hd
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply D (integralClosure D (TensorProduct S D L))
        (Localization.AtPrime Q)]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q _).2 hd
    · rw [hmax, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ htQ
  rw [Ideal.ramificationIdx_def, hmapmax,
    Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.2 (IsLocalRing.maximalIdeal.isMaximal _).out)]
  rfl

end GlobalTheory
