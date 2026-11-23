module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorDescentFlatNormalDomainsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsFlatNormalStageAtOriginStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFactorOfIndEtAtPrime
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstants

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOriginNoeth

section

@[expose] public section

open IsLocalRing Polynomial

namespace GlobalTheory.VertUnitsNoeth

theorem exists_unit_of_mem_map_comap {A' B' : Type} [CommRing A'] [CommRing B'] [IsDomain B']
    [IsLocalRing B'] (f : A' →+* B') (b : B')
    (h : b ∈ ((Ideal.span {b}).comap f).map f) : ∃ (d : A') (w : B'ˣ), b = f d * w := by
  by_cases hb : b = 0
  · exact ⟨0, 1, by simp [hb]⟩
  by_contra hne
  push_neg at hne
  have hle : ((Ideal.span {b}).comap f).map f ≤ Ideal.span {b} * maximalIdeal B' := by
    rw [Ideal.map_le_iff_le_comap]
    intro d hd
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hd
    obtain ⟨z, hz⟩ := hd
    rw [Ideal.mem_comap, hz]
    by_cases hzu : IsUnit z
    · exact absurd (by rw [hz]; exact (Units.mul_inv_cancel_right b hzu.unit).symm) (hne d hzu.unit⁻¹)
    · exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self b) ((mem_maximalIdeal z).2 hzu)
  obtain ⟨m, hm, hbm⟩ := (Ideal.mem_span_singleton_mul).1 (hle h)
  have h1 : m = 1 := by
    have : b * (m - 1) = 0 := by rw [mul_sub, hbm, mul_one, sub_self]
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hb
    · exact sub_eq_zero.1 h0
  exact (mem_maximalIdeal m).1 hm (h1 ▸ isUnit_one)

theorem divConst_origin_noeth : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (bA cA : Localization.AtPrime QA) (sA : A), sA ≠ 0 →
      bA * cA = algebraMap A (Localization.AtPrime QA) sA →
    ∃ (a : T) (w : Oˣ), jA bA = algebraMap T O a * (w : O) := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP A _ _ _ _ _ _ i hi hil EA _ _ _ _ _ QA _ hQA jA hjA
    bA cA sA hs hbc
  obtain ⟨A', _, _, _, _, B', _, _, _, _, _, _, _, ι, α, β, γ, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.T.divisorsOfConstants_flat_normal_stage_at_origin T O hT P φ hφ hsh hP A i hi hil EA QA hQA jA hjA sA hs
  have hbc' : β bA * β cA = algebraMap A' B' (ι sA) := by
    have e := congrArg (fun g => g sA) h1
    simp only [RingHom.comp_apply] at e
    rw [e, ← hbc, map_mul]
  have hmem := GlobalTheory.T.divisor_descent_flat_normal_domains A' B' (ι sA) h4 h5 (β bA) (β cA) hbc'
  obtain ⟨d, w, hdw⟩ := exists_unit_of_mem_map_comap (algebraMap A' B') (β bA) hmem
  have e3 := congrArg (fun g => g d) h3
  simp only [RingHom.comp_apply] at e3
  refine ⟨α d, Units.map γ.toMonoidHom w, ?_⟩
  rw [← h2, RingHom.comp_apply, hdw, map_mul, e3]
  rfl

end GlobalTheory.VertUnitsNoeth
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOriginNoethStatement

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.divConst_origin_noeth_alt : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (bA cA : Localization.AtPrime QA) (sA : A), sA ≠ 0 →
      bA * cA = algebraMap A (Localization.AtPrime QA) sA →
    ∃ (a : T) (w : Oˣ), jA bA = algebraMap T O a * (w : O) := by
  first | (exact @GlobalTheory.VertUnitsNoeth.divConst_origin_noeth) | (exact GlobalTheory.VertUnitsNoeth.divConst_origin_noeth) | (intros; apply GlobalTheory.VertUnitsNoeth.divConst_origin_noeth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleStageDivisorStrictHenselisationOrigin

section

@[expose] public section

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginCut

theorem exists_stage_divisor : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (b c : O) (s : T), s ≠ 0 → b * c = algebraMap T O s →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (Q : Ideal E) (_ : Q.IsPrime),
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T ∧
      ∃ (j : Localization.AtPrime Q →+* O),
        j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O ∧
      ∃ (b₁ c₁ : Localization.AtPrime Q),
        b₁ * c₁ = algebraMap T (Localization.AtPrime Q) s ∧ j b₁ = b ∧ j c₁ = c := by
  intro T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH hPeq b c s hs hbc
  classical
  let I : Ideal (MvPolynomial (Fin 2) (Polynomial T)) :=
    Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (Polynomial.C s)}
  haveI : Algebra.FinitePresentation (Polynomial T) (MvPolynomial (Fin 2) (Polynomial T) ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_singleton _))
  have hI : ∀ a ∈ I, MvPolynomial.aeval (R := Polynomial T) ![b, c] a = 0 := by
    intro a ha
    have hle : I ≤ RingHom.ker (MvPolynomial.aeval (R := Polynomial T) ![b, c]) := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      simp only [map_sub, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
      show b * c - _ = 0
      rw [hbc, IsScalarTower.algebraMap_apply T (Polynomial T) O, Polynomial.algebraMap_eq, sub_self]
    exact hle ha
  let g : (MvPolynomial (Fin 2) (Polynomial T) ⧸ I) →ₐ[Polynomial T] O :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval ![b, c]) hI
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtFactorLoc.exists_etale_factor_of_indEt_atPrime
    (Polynomial T) O P φ hφ hSH.2.2.2 _ g
  letI : Algebra T W := ((algebraMap (Polynomial T) W).comp (algebraMap T (Polynomial T))).toAlgebra
  haveI : IsScalarTower T (Polynomial T) W := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  set Q : Ideal W := (maximalIdeal O).comap v.toRingHom with hQdef
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  have hloc : (maximalIdeal O).comap φ = maximalIdeal (Localization.AtPrime P) := by
    haveI := hSH.2.2.1
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
    · intro x hx
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit φ x hu)
  have hQP : Q.comap (algebraMap (Polynomial T) W) = P := by
    rw [hQdef, Ideal.comap_comap]
    have h1 : v.toRingHom.comp (algebraMap (Polynomial T) W) = φ.comp (algebraMap (Polynomial T) _) := by
      rw [hφ]; exact v.comp_algebraMap
    rw [h1, ← Ideal.comap_comap, hloc]
    exact Localization.AtPrime.under_maximalIdeal (R := Polynomial T) (I := P)
  have hunit : ∀ y : Q.primeCompl, IsUnit (v.toRingHom (y : W)) := by
    intro y
    by_contra hy
    exact y.2 (show (y : W) ∈ Q from (IsLocalRing.mem_maximalIdeal _).2 hy)
  let j : Localization.AtPrime Q →+* O := IsLocalization.lift (M := Q.primeCompl) hunit
  have hjE : j.comp (algebraMap W (Localization.AtPrime Q)) = v.toRingHom :=
    IsLocalization.lift_comp hunit
  have hjR : j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O := by
    rw [IsScalarTower.algebraMap_eq (Polynomial T) W (Localization.AtPrime Q), ← RingHom.comp_assoc, hjE]
    exact v.comp_algebraMap
  have hjW : ∀ w : W, j (algebraMap W (Localization.AtPrime Q) w) = v w := fun w =>
    congrArg (fun f => f w) hjE
  have hgX : ∀ i : Fin 2, v (u (Ideal.Quotient.mk I (MvPolynomial.X i))) = ![b, c] i := by
    intro i
    rw [← AlgHom.comp_apply, huv]
    show Ideal.Quotient.liftₐ I _ hI (Ideal.Quotient.mk I _) = _
    change MvPolynomial.aeval ![b, c] (MvPolynomial.X i) = _
    rw [MvPolynomial.aeval_X]
  have hprod : Ideal.Quotient.mk I (MvPolynomial.X 0) * Ideal.Quotient.mk I (MvPolynomial.X 1) =
      algebraMap (Polynomial T) _ (Polynomial.C s) := by
    rw [← map_mul, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span rfl)
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q, inferInstance,
    hQP.trans hPeq, j, hjR, algebraMap W _ (u (Ideal.Quotient.mk I (MvPolynomial.X 0))),
    algebraMap W _ (u (Ideal.Quotient.mk I (MvPolynomial.X 1))), ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hprod, AlgHom.commutes,
      IsScalarTower.algebraMap_apply T W (Localization.AtPrime Q)]
    rfl
  · rw [hjW, hgX]; rfl
  · rw [hjW, hgX]; rfl

end GlobalTheory.KeyOriginCut
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleStageDivisorStrictHenselisationOriginStatement

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_etaleStage_divisor_strictHenselisation_origin : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (b c : O) (s : T), s ≠ 0 → b * c = algebraMap T O s →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (Q : Ideal E) (_ : Q.IsPrime),
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T ∧
      ∃ (j : Localization.AtPrime Q →+* O),
        j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O ∧
      ∃ (b₁ c₁ : Localization.AtPrime Q),
        b₁ * c₁ = algebraMap T (Localization.AtPrime Q) s ∧ j b₁ = b ∧ j c₁ = c := by
  first | (exact @GlobalTheory.KeyOriginCut.exists_stage_divisor) | (exact GlobalTheory.KeyOriginCut.exists_stage_divisor) | (intros; apply GlobalTheory.KeyOriginCut.exists_stage_divisor  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstantsStatement

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_noetherian_model_of_divisor_of_constants : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E]
      [IsScalarTower T (Polynomial T) E] [Algebra.Etale (Polynomial T) E]
      (Q : Ideal E) [Q.IsPrime],
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (j : Localization.AtPrime Q →+* O),
      j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O →
    ∀ (b₁ c₁ : Localization.AtPrime Q) (s : T), s ≠ 0 →
      b₁ * c₁ = algebraMap T (Localization.AtPrime Q) s →
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (_ : IsNoetherianRing A)
      (_ : IsIntegrallyClosed A) (_ : Algebra.EssFiniteType ℤ A) (i : A →+* T),
      Function.Injective i ∧ IsLocalHom i ∧
      ∃ (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial A) EA) (_ : Algebra A EA)
        (_ : IsScalarTower A (Polynomial A) EA) (_ : Algebra.Etale (Polynomial A) EA)
        (QA : Ideal EA) (_ : QA.IsPrime),
        QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A ∧
      ∃ (jA : Localization.AtPrime QA →+* O),
        jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
          (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) ∧
      ∃ (bA cA : Localization.AtPrime QA) (sA : A), sA ≠ 0 ∧ i sA = s ∧
        bA * cA = algebraMap A (Localization.AtPrime QA) sA ∧ jA bA = j b₁ := by
  first | (exact @GlobalTheory.VertUnitsNoeth.exists_noetherian_model_of_mul_eq) | (exact GlobalTheory.VertUnitsNoeth.exists_noetherian_model_of_mul_eq) | (intros; apply GlobalTheory.VertUnitsNoeth.exists_noetherian_model_of_mul_eq  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOrigin

section

@[expose] public section

open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

theorem divConstOrigin : GlobalTheory.VertUnits.DivConstOrigin := by
  have h₁ := GlobalTheory.T.exists_etaleStage_divisor_strictHenselisation_origin
  have h₂ := GlobalTheory.T.exists_noetherian_model_of_divisor_of_constants
  have h₃ := GlobalTheory.T.divConst_origin_noeth_alt
  unfold GlobalTheory.VertUnits.DivConstOrigin GlobalTheory.VertUnits.DivConstWith GlobalTheory.VertUnits.DivConst
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh _ hPo b c s hs hbc
  have hPo' : P = GlobalTheory.KeyOriginCut.originIdeal T := hPo
  obtain ⟨E, _, _, _, _, _, Q, _, hQ, j, hj, b₁, c₁, hbc₁, hjb, hjc⟩ :=
    h₁ T O hT P φ hφ hsh hPo' b c s hs hbc
  obtain ⟨A, _, _, _, _, _, _, i, hi, hil, EA, _, _, _, _, _, QA, _, hQA, jA, hjA, bA, cA, sA, hsA, hisA,
    hbcA, hjbA⟩ := h₂ T O hT E Q hQ j hj b₁ c₁ s hs hbc₁
  obtain ⟨a, w, haw⟩ := h₃ T O hT P φ hφ hsh hPo' A i hi hil EA QA hQA jA hjA bA cA sA hsA hbcA
  exact ⟨a, w, by rw [← hjb, ← hjbA, haw]⟩

end GlobalTheory.VertUnits
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOriginStatement

section

@[expose] public section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.div_const_origin : GlobalTheory.VertUnits.DivConstOrigin := by
  first | (exact @GlobalTheory.VertUnits.divConstOrigin) | (exact GlobalTheory.VertUnits.divConstOrigin) | (intros; apply GlobalTheory.VertUnits.divConstOrigin <;> assumption)
end
end
