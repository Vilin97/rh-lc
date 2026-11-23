module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BlowUpPushHypothesesExample
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlowUpFibreSemilocalStatement
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectionFormulaDegree
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
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AevalChartSubstMemOfMemBlowUpOf
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyDimensionInequality
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleFiniteSupport
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import Mathlib.Algebra.Order.Star.Int
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpVerticalFibre
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpVerticalFibre
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.GroupWithZero.Indicator
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFiniteBirationalLength
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHorizontalComponentModel
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersLocalIntegralClosureFinite
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelIrreducibleBasicOpenConnected
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelUnbranchedPartConnected
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.NumbersDVRC3ResidualContractionComponent

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectionFormulaDegreeStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.projection_formula_degree : GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.Statement.{0} := by
  first | exact @GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree | exact GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree | (intros; apply GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree <;> assumption)
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpDivisorPush

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Pullback

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem liftForm_mem_blowUpOf_of_mem (P : Ideal (MRing ι R)) (u : J → MRing ι R) {p : MRing ι R}
    (hp : p ∈ P) : liftForm (J := J) p ∈ blowUpOf P u := by
  let φ : MRing ι R →ₐ[R] Polynomial (MRing ι R ⧸ P) :=
    (Polynomial.CAlgHom (R := R) (A := MRing ι R ⧸ P)).comp (Ideal.Quotient.mkₐ R P)
  have hcomp : (aeval (blowUpSubst P u)).comp (liftForm (ι := ι) (J := J) (R := R)) = φ := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, liftForm, rename_X, aeval_X]
    rfl
  have h := DFunLike.congr_fun hcomp p
  rw [AlgHom.comp_apply] at h
  unfold blowUpOf
  rw [RingHom.mem_ker, h]
  show Polynomial.C (Ideal.Quotient.mk P p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

end Pullback

section Sums

open scoped Classical in
open Classical in
theorem finsum_sub_mul_eq_of_support {α : Type*} (Z₁ Z₂ n : α → ℤ) (p : α → Prop)
    (h₁ : (Function.support Z₁).Finite) (h₂ : (Function.support Z₂).Finite)
    (hv : ∀ W, Z₁ W - Z₂ W ≠ 0 → p W) :
    ∑ᶠ W, (Z₁ W - Z₂ W) * n W =
      ∑ᶠ W, Z₁ W * (if p W then n W else 0) - ∑ᶠ W, Z₂ W * (if p W then n W else 0) := by
  have e : ∀ W, (Z₁ W - Z₂ W) * n W =
      Z₁ W * (if p W then n W else 0) - Z₂ W * (if p W then n W else 0) := by
    intro W
    by_cases h : Z₁ W - Z₂ W = 0
    · rw [h, zero_mul, sub_eq_zero.mp h, sub_self]
    · rw [ite_eq_left (hv W h), ← sub_mul]
  rw [finsum_congr e, finsum_sub_distrib]
  · exact h₁.subset fun W hW => left_ne_zero_of_mul hW
  · exact h₂.subset fun W hW => left_ne_zero_of_mul hW

end Sums

theorem BlowUpDivisorPush.proof (hvert : BlowUpVerticalPush.Statement.{u}) :
    BlowUpDivisorPush.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP b f g hD N u hu hu' a
  have hfin := DivCycleFiniteSupport.proof.{u}
  obtain ⟨bf, bg, hbf, hbg, -⟩ := hD.degrees

  have hvertB : ∀ W, divCycle (blowUpOf P u) (liftForm (J := J) f) W -
      divCycle (blowUpOf P u) (liftForm (J := J) g) W ≠ 0 → (C ϖ : MRing (extIdx ι J) O) ∈ W := by
    intro W hW
    by_contra hϖW
    have hsupp : W.IsPrime ∧ blowUpOf P u ≤ W ∧ IsRelevant W := by
      by_cases h1 : divCycle (blowUpOf P u) (liftForm (J := J) f) W = 0
      · have h2 : divCycle (blowUpOf P u) (liftForm (J := J) g) W ≠ 0 := by
          intro h2; apply hW; rw [h1, h2, sub_zero]
        exact le_and_isRelevant_of_divCycle_ne_zero h2
      · exact le_and_isRelevant_of_divCycle_ne_zero h1
    obtain ⟨hWp, hBW, hWrel⟩ := hsupp
    let W₀ : Ideal (MRing ι O) := W.comap (liftForm (ι := ι) (J := J) (R := O))
    have hW₀ : W₀.IsPrime := Ideal.comap_isPrime _ _
    have hPW₀ : P ≤ W₀ := fun p hp => hBW (liftForm_mem_blowUpOf_of_mem P u hp)
    have hrel₀ : IsRelevant W₀ := by
      intro k
      obtain ⟨i, hi⟩ := hWrel (some k)
      refine ⟨i, fun h => hi ?_⟩
      have h' : liftForm (ι := ι) (J := J) (R := O) (X ⟨k, i⟩) ∈ W := h
      rwa [liftForm, rename_X] at h'
    have hϖ₀ : (C ϖ : MRing ι O) ∉ W₀ := by
      intro h
      have h' : liftForm (ι := ι) (J := J) (R := O) (C ϖ) ∈ W := h
      rw [liftForm, rename_C] at h'
      exact hϖW h'
    obtain ⟨s, t, hs, ht, hst⟩ := hD.unit_off_special W₀ hW₀ hPW₀ hrel₀ hϖ₀
    apply hW
    rw [divCycle_eq_of_mul_sub_mem (u := liftForm (J := J) s) (v := liftForm (J := J) t) hs ht ?_,
      sub_self]
    have := liftForm_mem_blowUpOf_of_mem (J := J) P u hst
    rwa [map_sub, map_mul, map_mul] at this
  have e₁ := hvert O ϖ hϖ K ι J P n hP N u hu hu' bf f hbf hD.num_not_mem a
  have e₂ := hvert O ϖ hϖ K ι J P n hP N u hu hu' bg g hbg hD.den_not_mem a
  unfold cycEval at e₁ e₂
  unfold cycEval ratDiv
  rw [finsum_sub_mul_eq_of_support (divCycle (blowUpOf P u) (liftForm (J := J) f))
      (divCycle (blowUpOf P u) (liftForm (J := J) g)) _ _ (hfin _ _ _ _ _) (hfin _ _ _ _ _) hvertB,
    finsum_sub_mul_eq_of_support (divCycle P f) (divCycle P g) _ _ (hfin _ _ _ _ _)
      (hfin _ _ _ _ _) hD.vertical, e₁, e₂]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpFibreDegree

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpFibreDegree.proof (ha : HomLocRingLocal.Statement.{u}) (hb : DivCycleHomLoc.Statement.{u})
    (hc : FiniteBirationalLength.Statement.{u}) (hd : BlowUpFibreSemilocal.Statement.{u}) :
    BlowUpFibreDegree.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hdiv
  have hsupp : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    exact hdiv (by unfold divCycle; rw [dite_eq_right h])
  have hWp : W.IsPrime := hsupp.1.1.1
  have := hP.multiProj.isPrime
  obtain ⟨i, hi⟩ := powMonomial_not_mem hWp hsupp.2 c
  have hg : IsMultiHomog (powMonomial c i : MRing ι O) c := isMultiHomog_powMonomial c i
  have hz : algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P x) /
      algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P))
        (Ideal.Quotient.mk P (powMonomial c i)) ∈ homLocRing P W :=
    Subring.subset_closure ⟨c, x, _, hx, hg, hi, rfl⟩
  obtain ⟨hloc, hnoeth, hdim⟩ := ha O K ι P hP.multiProj c x hx hxP W hsupp.1 hsupp.2
  have := hloc
  have := hnoeth
  obtain ⟨B, _, _, _, hfin, hinj, hrank, e, he⟩ :=
    hd O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hsupp.1 hsupp.2 _ hg hi hz
  have hz0 : (⟨_, hz⟩ : homLocRing P W) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun w : homLocRing P W => (w : FractionRing (MRing ι O ⧸ P))) h0
    simp only [ZeroMemClass.coe_zero] at h1
    rcases div_eq_zero_iff.mp h1 with h | h
    · exact hxP (Ideal.Quotient.eq_zero_iff_mem.mp
        ((IsFractionRing.injective _ (FractionRing (MRing ι O ⧸ P))) (by rw [h, map_zero])))
    · exact hi (hsupp.1.1.2 (Ideal.mem_sup_left (Ideal.Quotient.eq_zero_iff_mem.mp
        ((IsFractionRing.injective _ (FractionRing (MRing ι O ⧸ P))) (by rw [h, map_zero])))))
  obtain ⟨hfinite, hlen⟩ := hc (homLocRing P W) B hdim hinj hrank _ hz0
  have hmult := hb O K ι P hP.multiProj c x hx hxP W hsupp.1 hsupp.2 _ hg hi hz
  have hdivW : divCycle P x W = ((multAt (P ⊔ Ideal.span {x}) W).toNat : ℤ) := by
    unfold divCycle
    rw [dite_eq_left hsupp]
  have := Fintype.ofFinite {𝔫 : Ideal B // 𝔫.IsMaximal}

  have hterm : ∀ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal},
      (have := 𝔫.2.isPrime;
       Module.length (Localization.AtPrime 𝔫.1)
         (Localization.AtPrime 𝔫.1 ⧸ Ideal.span {(algebraMap B (Localization.AtPrime 𝔫.1)
           (algebraMap (homLocRing P W) B ⟨_, hz⟩))})) * (𝔫.1.inertiaDeg (homLocRing P W) : ℕ∞) =
        (((divCycle (blowUpOf P u) (liftForm x) (e 𝔫).1).toNat * specialRelDeg (e 𝔫).1 : ℕ) : ℕ∞) := by
    intro 𝔫
    rw [(he 𝔫).1, (he 𝔫).2, Nat.cast_mul]
  rw [finsum_congr hterm, finsum_eq_sum_of_fintype, ← Nat.cast_sum] at hlen
  rw [hdivW, hmult, hlen, ENat.toNat_natCast, Nat.cast_sum]

  classical
  let p : Ideal (MRing (extIdx ι J) O) → Prop := fun W' =>
    W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
      W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
  have hite : ∀ W' : Ideal (MRing (extIdx ι J) O),
      (if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
        divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ) else 0) =
      ∑ᶠ (_ : p W'), divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ) := by
    intro W'
    rw [finsum_eq_if]
    by_cases hc' : W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
    · by_cases hp : p W'
      · rw [if_pos hc', if_pos hp]
      · rw [if_pos hc', if_neg hp]
        have h0 : divCycle (blowUpOf P u) (liftForm x) W' = 0 := by
          unfold divCycle
          rw [dite_eq_right]
          exact fun h => hp ⟨h.1, h.2, hc'⟩
        rw [h0, zero_mul]
    · rw [if_neg hc', if_neg (fun h => hc' h.2.2)]
  rw [finsum_congr hite, ← finsum_subtype_eq_finsum_cond p,
    ← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun 𝔫 _ => ?_
  have h0 : 0 ≤ divCycle (blowUpOf P u) (liftForm x) (e 𝔫).1 := by
    unfold divCycle
    split_ifs <;> positivity
  rw [Nat.cast_mul, Int.toNat_of_nonneg h0]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpVerticalPush

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

open Classical in
theorem BlowUpVerticalPush.proof (hfib : BlowUpVerticalFibre.Statement.{u}) :
    BlowUpVerticalPush.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP a
  have hZ : (Function.support (divCycle (blowUpOf P u) (liftForm (J := J) x))).Finite :=
    DivCycleFiniteSupport.proof O (Option K) (extIdx ι J) _ _

  have hC : ∀ W' : Ideal (MRing (extIdx ι J) O), (C ϖ : MRing (extIdx ι J) O) ∈ W' ↔
      (C ϖ : MRing ι O) ∈ W'.comap (liftForm (ι := ι) (J := J) (R := O)) := by
    intro W'
    rw [Ideal.mem_comap]
    simp [liftForm]
  set g : Ideal (MRing (extIdx ι J) O) → ℤ := fun W' =>
    divCycle (blowUpOf P u) (liftForm x) W' *
      (if (C ϖ : MRing (extIdx ι J) O) ∈ W' then vNum W' (liftDegs a) else 0) with hg_def
  have hg : Function.support g ⊆ hZ.toFinset := fun W' hW' =>
    hZ.mem_toFinset.mpr (Function.support_mul_subset_left _ _ hW')

  have key : ∀ W : Ideal (MRing ι O),
      (∑ W' ∈ hZ.toFinset with W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W, g W') =
        divCycle P x W * (if (C ϖ : MRing ι O) ∈ W then vNum W a else 0) := by
    intro W
    by_cases hW : (C ϖ : MRing ι O) ∈ W
    · rw [if_pos hW, ← hfib O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP a W hW,
        finsum_eq_sum_of_support_subset _ (s := hZ.toFinset), Finset.sum_filter]
      · refine Finset.sum_congr rfl fun W' _ => ?_
        by_cases h1 : W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
        · rw [if_pos h1, if_pos h1, hg_def]
          dsimp only
          rw [if_pos ((hC W').mpr (by rw [h1]; exact hW))]
        · rw [if_neg h1, if_neg h1]
      · intro W' hW'
        refine hZ.mem_toFinset.mpr ?_
        rw [Function.mem_support] at hW' ⊢
        intro h0
        apply hW'
        simp [h0]
    · rw [if_neg hW, mul_zero]
      refine Finset.sum_eq_zero fun W' hW' => ?_
      have h1 := (Finset.mem_filter.mp hW').2
      rw [hg_def]
      dsimp only
      rw [if_neg (fun h => hW (h1 ▸ (hC W').mp h)), mul_zero]
  unfold cycEval
  calc (∑ᶠ W', divCycle (blowUpOf P u) (liftForm x) W' *
          (if (C ϖ : MRing (extIdx ι J) O) ∈ W' then vNum W' (liftDegs a) else 0))
      = ∑ W' ∈ hZ.toFinset, g W' := finsum_eq_sum_of_support_subset g hg
    _ = ∑ᶠ W, ∑ W' ∈ hZ.toFinset with W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W, g W' :=
        (finsum_sum_filter _ _ _).symm
    _ = _ := finsum_congr key

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CutEffectiveDivisor

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Num.CutClosed

open GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.AutoClose

theorem verticalPush : BlowUpVerticalPush.Statement.{0} :=
  BlowUpVerticalPush.proof (BlowUpVerticalFibre.proof BlowUpModel.full
    (BlowUpFibreDegree.proof NumbersDVR_HomLocRingLocal NumbersDVR_DivCycleHomLoc
      FiniteBirationalLength.full GlobalTheory.T.blow_up_fibre_semilocal) GlobalTheory.T.projection_formula_degree)

theorem main : CutByEffectiveDivisor.Statement.{0} :=
  CutByEffectiveDivisor.of_steps NumbersDVR_C3NoCommon
    (CommonFactorInduction.of_open ReesAlgebraDim.full BlowUpStrictTransform.proof
      NumbersDVR_C3BlowUpExcessDrop verticalPush (BlowUpDivisorPush.proof verticalPush)
      NumbersDVR_BlowUpHorizontalCorresp HorizontalComponentModel.proof)

end GlobalTheory.CompanionTheory.Ar.Num.CutClosed
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CutEffectiveDivisorStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.cut_effective_divisor : GroundTheory.Heights₂.Heights.NumbersDVR.CutByEffectiveDivisor.Statement.{0} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.CutClosed.main | exact GlobalTheory.CompanionTheory.Ar.Num.CutClosed.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.CutClosed.main <;> assumption)
end
end
