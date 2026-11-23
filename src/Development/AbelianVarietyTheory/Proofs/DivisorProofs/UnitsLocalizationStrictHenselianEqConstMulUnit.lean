module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOriginStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsIntClosedLocalizationAndQuotient
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootSubMemOfEvalMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialClosedPointsOfOriginClosedFibre
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsGenericFibreOfClosedPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
import Mathlib.RingTheory.WittVector.IsPoly

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsAllPrimesOfClosedFibre

section

@[expose] public section

open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits


open GlobalTheory.LocAcyc in
open CategoryTheory in
theorem divConstAll_of_divConstLocal : DivConstLocal → DivConstAll := by
  intro hL T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH
  set p : Ideal T := P.comap (C : T →+* T[X]) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let T' := Localization.AtPrime p
  have hle : p.primeCompl ≤ nonZeroDivisors T := p.primeCompl_le_nonZeroDivisors
  have hAIC' : AbsIntClosed T' :=
    ((absIntClosed_localization_and_quotient T ⟨inferInstance, hAIC⟩).1 p.primeCompl
      (fun h => h (zero_mem p))).2
  have hTO : ∀ a : T, algebraMap T O a = algebraMap T[X] O (C a) := fun a => by
    rw [IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_eq]
  have hunit : ∀ s : p.primeCompl, IsUnit (algebraMap T O s) := by
    intro s
    have hs : C (s : T) ∈ P.primeCompl := s.2
    have hu := (IsLocalization.map_units (Localization.AtPrime P)
      (⟨C (s : T), hs⟩ : P.primeCompl)).map φ
    rw [← RingHom.comp_apply, hφ] at hu
    rwa [hTO]
  letI : Algebra T' O := (IsLocalization.lift (M := p.primeCompl) (S := T') hunit).toAlgebra
  haveI : IsScalarTower T T' O :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunit x).symm)
  letI : Algebra T'[X] O := (eval₂RingHom (algebraMap T' O) (algebraMap T[X] O X)).toAlgebra
  haveI : IsScalarTower T' T'[X] O :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change _ = eval₂ (algebraMap T' O) (algebraMap T[X] O X) (algebraMap T' T'[X] x)
      rw [Polynomial.algebraMap_eq, eval₂_C])
  letI : Algebra T[X] T'[X] := Polynomial.algebra T T'
  haveI : IsLocalization (Submonoid.map C p.primeCompl) T'[X] :=
    Polynomial.isLocalization p.primeCompl T'
  have hdisj : Disjoint (Submonoid.map C p.primeCompl : Set T[X]) (P : Set T[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    exact hs hsP
  set P' : Ideal T'[X] := P.map (algebraMap T[X] T'[X]) with hP'
  haveI hP'prime : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ T'[X] P inferInstance hdisj
  have hcomapP' : P'.comap (algebraMap T[X] T'[X]) = P :=
    IsLocalization.under_map_of_isPrime_disjoint _ T'[X] inferInstance hdisj
  have hCcomm : ∀ a : T, C (algebraMap T T' a) = algebraMap T[X] T'[X] (C a) := fun a => by
    change _ = (C a).map (algebraMap T T')
    rw [Polynomial.map_C]
  have hmax : P'.comap (C : T' →+* T'[X]) = maximalIdeal T' := by
    rw [← IsLocalization.map_under p.primeCompl T' (P'.comap C),
      ← IsLocalization.map_under p.primeCompl T' (maximalIdeal T'),
      IsLocalization.AtPrime.under_maximalIdeal T' p]
    congr 1
    ext a
    change C (algebraMap T T' a) ∈ P' ↔ C a ∈ P
    rw [hCcomm, ← Ideal.mem_comap, hcomapP']
  haveI : IsLocalization.AtPrime (Localization.AtPrime P') P := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.map C p.primeCompl) (Localization.AtPrime P') P'
    have hc : (P'.comap (algebraMap T[X] T'[X])).primeCompl = P.primeCompl := by
      ext x; simp only [Ideal.mem_primeCompl_iff, hcomapP']
    unfold IsLocalization.AtPrime at this ⊢
    rw [hc] at this
    exact this
  let e : Localization.AtPrime P ≃ₐ[T[X]] Localization.AtPrime P' :=
    IsLocalization.algEquiv P.primeCompl _ _
  let φ' : Localization.AtPrime P' →+* O := φ.comp e.symm.toRingEquiv.toRingHom
  have hOO : (algebraMap T'[X] O).comp (algebraMap T[X] T'[X]) = algebraMap T[X] O := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((C a).map (algebraMap T T')) = _
      rw [Polynomial.map_C, eval₂_C, ← IsScalarTower.algebraMap_apply, hTO]
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((X : T[X]).map (algebraMap T T')) = _
      rw [Polynomial.map_X, eval₂_X]
  have hφ' : φ'.comp (algebraMap T'[X] (Localization.AtPrime P')) = algebraMap T'[X] O := by
    refine IsLocalization.ringHom_ext (Submonoid.map C p.primeCompl) ?_
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hOO]
    refine RingHom.ext fun f => ?_
    change φ (e.symm (algebraMap T[X] _ f)) = _
    rw [AlgEquiv.commutes, ← RingHom.comp_apply, hφ]
  have hSH' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hSH
    refine ⟨h1, h2, ?_, ?_⟩
    · refine ⟨fun a ha => ?_⟩
      change IsUnit (φ (e.symm a)) at ha
      have h5 : IsUnit (e.symm a) := h3.map_nonunit _ ha
      simpa using h5.map e
    · haveI : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale at h4 ⊢
      rw [CommRingCat.ofHom_comp]
      haveI : IsIso (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) :=
        inferInstanceAs (IsIso (e.symm.toRingEquiv.toCommRingCatIso).hom)
      exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr h4
  have key : DivConst T' O := hL T' O hAIC' P' φ' hφ' hSH' hmax trivial

  have hinj : Function.Injective (algebraMap T T') := IsLocalization.injective T' hle
  intro b c s hs hbc
  have hs' : algebraMap T T' s ≠ 0 := fun h => hs (hinj (by rw [h, map_zero]))
  rw [IsScalarTower.algebraMap_apply T T' O] at hbc
  obtain ⟨a', w, hb⟩ := key b c _ hs' hbc
  obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a'
  obtain ⟨v, hv⟩ := hunit u
  refine ⟨a, v⁻¹ * w, ?_⟩
  rw [hb, Units.val_mul, ← mul_assoc]
  congr 1
  rw [Units.eq_mul_inv_iff_mul_eq, hv, IsScalarTower.algebraMap_apply T T' O a,
    IsScalarTower.algebraMap_apply T T' O u, ← map_mul, IsLocalization.mk'_spec]

end GlobalTheory.VertUnits
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsAllPrimesOfClosedFibreStatement

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.divisorsOfConstantsAllPrimes_of_closedFibre : GlobalTheory.VertUnits.DivConstLocal → GlobalTheory.VertUnits.DivConstAll := by
  first | exact @GlobalTheory.VertUnits.divConstAll_of_divConstLocal | exact GlobalTheory.VertUnits.divConstAll_of_divConstLocal | (intros; apply GlobalTheory.VertUnits.divConstAll_of_divConstLocal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsClosedPointsOfOrigin

section

@[expose] public section

open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

theorem divConstClosedPts_of_divConstOrigin :
    GlobalTheory.VertUnits.DivConstOrigin → GlobalTheory.VertUnits.DivConstClosedPts := by
  intro hKO
  unfold GlobalTheory.VertUnits.DivConstOrigin GlobalTheory.VertUnits.DivConstWith at hKO
  unfold GlobalTheory.VertUnits.DivConstClosedPts GlobalTheory.VertUnits.DivConstWith
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hPm hne
  have hne' : P ≠ (maximalIdeal T).map (C : T →+* T[X]) := hne
  haveI hac : IsAlgClosed (ResidueField T) :=
    (GlobalTheory.AbsIntClosedLocal.henselian_isAlgClosed_pow_surj T ⟨inferInstance, hT⟩).2.1
  obtain ⟨c, hc⟩ := GlobalTheory.LocAcyc.Translate.exists_X_sub_C_mem T P hPm hne'
  let τ : T[X] ≃ₐ[T] T[X] := algEquivAevalXAddC (-c)
  have hτX : τ X = X - C c := by simp [τ, sub_eq_add_neg]
  have hτC : ∀ a : T, τ (C a) = C a := fun a => τ.commutes a
  let P' : Ideal T[X] := P.comap (τ : T[X] →+* T[X])
  haveI hP'p : P'.IsPrime := Ideal.comap_isPrime _ _
  have hP'C : P'.comap (C : T →+* T[X]) = maximalIdeal T := by
    rw [← hPm]; ext a
    simp only [Ideal.mem_comap, P']
    rw [show ((τ : T[X] →+* T[X]) (C a)) = C a from hτC a]
  have hXP' : (X : T[X]) ∈ P' := by
    simp only [P', Ideal.mem_comap]
    rw [show ((τ : T[X] →+* T[X]) X) = X - C c from hτX]; exact hc
  have hP' : P' = (maximalIdeal T).map (C : T →+* T[X]) ⊔ Ideal.span {X} := by
    apply le_antisymm
    · intro p hp
      have hd : p - C (p.coeff 0) ∈ Ideal.span {(X : T[X])} := Ideal.mem_span_singleton.2 X_dvd_sub_C
      have hc0 : C (p.coeff 0) ∈ P' := by
        have h1 : p - C (p.coeff 0) ∈ P' := by
          obtain ⟨u, hu⟩ := (X_dvd_sub_C : X ∣ p - C (p.coeff 0))
          rw [hu]; exact P'.mul_mem_right _ hXP'
        have := P'.sub_mem hp h1
        simpa using this
      have hc0' : p.coeff 0 ∈ maximalIdeal T := by rw [← hP'C]; exact hc0
      have : p = C (p.coeff 0) + (p - C (p.coeff 0)) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc0')) (Ideal.mem_sup_right hd)
    · refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap, hP'C]
      · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hXP'

  let f' : T[X] →+* O := (algebraMap T[X] O).comp (τ : T[X] →+* T[X])
  let alg' : Algebra T[X] O := f'.toAlgebra
  have tower' : @IsScalarTower T T[X] O _ alg'.toSMul _ := by
    refine @IsScalarTower.of_algebraMap_eq T T[X] O _ _ _ _ alg' _ ?_
    intro x
    change algebraMap T O x = f' (algebraMap T T[X] x)
    simp only [f', RingHom.comp_apply]
    rw [show (τ : T[X] →+* T[X]) (algebraMap T T[X] x) = algebraMap T T[X] x from τ.commutes x,
      ← IsScalarTower.algebraMap_apply]

  have hmap : P'.primeCompl.map (τ : T[X] ≃+* T[X]).toMonoidHom = P.primeCompl := by
    ext x
    rw [Submonoid.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨(τ : T[X] ≃+* T[X]).symm x, ?_, by simp⟩
      change (τ : T[X] →+* T[X]) ((τ : T[X] ≃+* T[X]).symm x) ∉ P
      have hx' : x ∉ P := hx
      convert hx' using 2
      exact (τ : T[X] ≃+* T[X]).apply_symm_apply x
  let Lq : Localization.AtPrime P' ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv _ _ (τ : T[X] ≃+* T[X]) hmap
  let φ' : Localization.AtPrime P' →+* O := φ.comp (Lq : Localization.AtPrime P' →+* Localization.AtPrime P)
  have hφ' : φ'.comp (algebraMap T[X] (Localization.AtPrime P')) = f' := by
    refine RingHom.ext fun x => ?_
    simp only [φ', f', RingHom.comp_apply]
    rw [show (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) (algebraMap T[X] _ x)
        = algebraMap T[X] (Localization.AtPrime P) ((τ : T[X] ≃+* T[X]) x) from
      IsLocalization.ringEquivOfRingEquiv_eq _ x]
    rw [← RingHom.comp_apply φ, hφ]
    rfl
  have hsh' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hsh
    refine ⟨h1, h2, ?_, ?_⟩
    · haveI := h3
      haveI : IsLocalHom (Lq : Localization.AtPrime P' →+* Localization.AtPrime P) :=
        ⟨fun a ha => by simpa using ha.map (Lq.symm : Localization.AtPrime P →+* Localization.AtPrime P')⟩
      exact RingHom.isLocalHom_comp _ _
    · have : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      have h5 := CategoryTheory.MorphismProperty.RespectsIso.precomp
        (CategoryTheory.MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale))
        Lq.toCommRingCatIso.hom (CommRingCat.ofHom φ) h4
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
      convert h5 using 1
      rfl
  exact @hKO T O _ _ _ _ _ _ alg' tower' hT P' hP'p φ' hφ' hsh' hP'C hP'

end GlobalTheory.VertUnits
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsClosedPointsOfOriginStatement

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.divisorsOfConstantsClosedPoints_of_origin : GlobalTheory.VertUnits.DivConstOrigin → GlobalTheory.VertUnits.DivConstClosedPts := by
  first | (exact @GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin) | (exact GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin) | (intros; apply GlobalTheory.VertUnits.divConstClosedPts_of_divConstOrigin  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsGenericFibreOfClosedPointsStatement

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.divisorsOfConstants_genericFibre_of_closedPoints : GlobalTheory.VertUnits.DivConstClosedPts → GlobalTheory.VertUnits.DivConstGeneric := by
  first | exact @GlobalTheory.VertUnits.divConstGeneric_of_divConstClosedPts | exact GlobalTheory.VertUnits.divConstGeneric_of_divConstClosedPts | (intros; apply GlobalTheory.VertUnits.divConstGeneric_of_divConstClosedPts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationStrictHenselianEqConstMulUnit

section

@[expose] public section

open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

theorem units_of_divConst (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O]
    (h : DivConst T O)
    (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ) :
    ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧
      (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) *
          algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))
            (algebraMap T O d) =
        algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))
            (algebraMap T O c) *
          algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) := by
  by_cases hL : Subsingleton (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))
  · exact ⟨1, 1, 1, one_ne_zero, one_ne_zero, Subsingleton.elim _ _⟩
  rw [not_subsingleton_iff_nontrivial] at hL
  obtain ⟨⟨b, s₁⟩, hb⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  obtain ⟨⟨c, s₂⟩, hc⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) ((u⁻¹ : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ) : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  obtain ⟨t₁, ht₁, hs₁⟩ := s₁.2
  obtain ⟨t₂, ht₂, hs₂⟩ := s₂.2
  have h1 : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (b * c) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) ((s₁ : O) * (s₂ : O)) := by
    have hu : (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) * ((u⁻¹ : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ) : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) = 1 := u.mul_inv
    rw [← hb, ← hc, ← IsLocalization.mk'_mul] at hu
    have := IsLocalization.mk'_spec (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (b * c) (s₁ * s₂)
    rw [hu, one_mul] at this
    rw [← this]; rfl
  obtain ⟨m, hm⟩ := (IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).1 h1
  obtain ⟨t₀, ht₀, hm₀⟩ := m.2
  have hmem : t₀ * t₁ * t₂ ∈ nonZeroDivisors T :=
    mul_mem (mul_mem ht₀ ht₁) ht₂
  have hne : t₀ * t₁ * t₂ ≠ 0 := nonZeroDivisors.ne_zero hmem
  obtain ⟨a, w, hbw⟩ := h b ((m : O) * c) (t₀ * t₁ * t₂) hne (by
    rw [map_mul, map_mul, hm₀, hs₁, hs₂]
    calc b * ((m : O) * c) = (m : O) * (b * c) := by ring
      _ = (m : O) * ((s₁ : O) * (s₂ : O)) := hm
      _ = (m : O) * (s₁ : O) * (s₂ : O) := by ring)
  have key : (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (s₁ : O) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) b := by
    rw [← hb]; exact IsLocalization.mk'_spec (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) b s₁
  refine ⟨a, t₁, w, ?_, nonZeroDivisors.ne_zero ht₁, ?_⟩
  · intro ha
    have h0 : (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (s₁ : O) = 0 := by
      rw [key, hbw, ha]; simp
    exact (u.isUnit.mul (IsLocalization.map_units (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) s₁)).ne_zero h0
  · rw [hs₁, key, hbw, map_mul]

theorem main_of_divConstAll (hAll : DivConstAll) : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)], (∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧ (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O d) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O c) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) := by
  intro T O _ _ _ _ _ _ _ _ _ hroot hO u
  obtain ⟨P, hP, φ, hφ, hsh⟩ :=
    GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T O hO
  exact units_of_divConst T O (hAll T O hroot P φ hφ hsh) u

end GlobalTheory.VertUnits

namespace GlobalTheory.VertUnits

theorem units_eq_const_mul_unit : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)], (∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧ (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O d) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O c) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) :=
  main_of_divConstAll (GlobalTheory.T.divisorsOfConstantsAllPrimes_of_closedFibre (divConstLocal_of
    (GlobalTheory.T.divisorsOfConstantsClosedPoints_of_origin GlobalTheory.T.div_const_origin) (GlobalTheory.T.divisorsOfConstants_genericFibre_of_closedPoints (GlobalTheory.T.divisorsOfConstantsClosedPoints_of_origin GlobalTheory.T.div_const_origin))))

end GlobalTheory.VertUnits
end
end
