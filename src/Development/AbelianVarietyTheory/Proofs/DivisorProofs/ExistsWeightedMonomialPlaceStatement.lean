module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSpanOfWeightedHomogeneousRelationQuasiReStatement
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Data.Finsupp.Fin
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrLocPrincipalPrime

section

@[expose] public section

noncomputable section

namespace GlobalTheory

theorem dvr_loc_principal_prime : ∀ {L : Type} [Field L] (A : Subring L) (t : A), IsNoetherianRing A → (t : L) ≠ 0 →
    (Ideal.span {t}).IsPrime → (∀ f : L, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (V : ValuationSubring L) (hA : ∀ a ∈ A, a ∈ V),
      IsDiscreteValuationRing V ∧ Irreducible (⟨t, hA _ t.2⟩ : V) ∧
      (∀ s : A, s ∉ Ideal.span {t} → IsUnit (⟨s, hA _ s.2⟩ : V)) ∧
      (∀ f : V, ∃ a s : A, s ∉ Ideal.span {t} ∧ (f : L) * s = a) ∧
      (A.subtype.codRestrict V fun a => hA _ a.2).EssFiniteType := by
  intro L _ A t hN ht hp hfr
  set p : Ideal A := Ideal.span {t} with hpdef
  haveI : IsFractionRing A L := IsFractionRing.of_field A L fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hfr z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by
      show z = a / b
      rw [← h, mul_div_cancel_right₀ _ hb0]⟩
  let V0 : Subalgebra A L := Localization.subalgebra.ofField L p.primeCompl p.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime V0 p := Localization.subalgebra.isLocalization_ofField _ _ _
  haveI : IsLocalRing V0 := IsLocalization.AtPrime.isLocalRing V0 p
  haveI : IsNoetherianRing V0 := IsLocalization.isNoetherianRing p.primeCompl V0 hN
  have hmax : IsLocalRing.maximalIdeal V0 = Ideal.span {algebraMap A V0 t} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p V0, hpdef, Ideal.map_span, Set.image_singleton]
  have ht0 : algebraMap A V0 t ≠ 0 := fun h => ht (congrArg Subtype.val h)
  have hnf : ¬ IsField V0 := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    exact ht0
  have hdvr : IsDiscreteValuationRing V0 :=
    ((IsDiscreteValuationRing.TFAE V0 hnf).out 1 5).2
      (⟨⟨_, hmax⟩⟩ : (IsLocalRing.maximalIdeal V0).IsPrincipal)
  haveI : IsFractionRing V0 L := IsFractionRing.of_field V0 L fun z => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hfr z
    exact ⟨algebraMap A V0 ⟨a, ha⟩, algebraMap A V0 ⟨b, hb⟩, by
      show z = a / b
      rw [← h, mul_div_cancel_right₀ _ hb0]⟩
  let V : ValuationSubring L :=
    { V0.toSubring with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger V0 x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact Or.inl (hy ▸ y.2)
        · exact Or.inr (hy ▸ y.2) }
  have hA : ∀ a ∈ A, a ∈ V := fun a ha => V0.algebraMap_mem (⟨a, ha⟩ : A)
  refine ⟨V, hA, hdvr, ?_, ?_, ?_, ?_⟩
  · exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  · intro s hs
    exact IsLocalization.map_units V0 (⟨s, hs⟩ : p.primeCompl)
  · intro f
    obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective p.primeCompl (show V0 from f)
    refine ⟨x, y, y.2, ?_⟩
    have := congrArg (algebraMap V0 L) (IsLocalization.mk'_spec V0 x y)
    have hxy' : IsLocalization.mk' V0 x y = (show V0 from f) := hxy
    rw [hxy', map_mul] at this
    exact this
  · have h := (RingHom.essFiniteType_algebraMap (R := A) (S := V0)).2
      (Algebra.EssFiniteType.of_isLocalization V0 p.primeCompl)
    exact h

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrLocPrincipalPrimeStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.isDVR_of_principal_prime_localization : ∀ {L : Type} [Field L] (A : Subring L) (t : A), IsNoetherianRing A → (t : L) ≠ 0 →
    (Ideal.span {t}).IsPrime → (∀ f : L, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a) →
    ∃ (V : ValuationSubring L) (hA : ∀ a ∈ A, a ∈ V),
      IsDiscreteValuationRing V ∧ Irreducible (⟨t, hA _ t.2⟩ : V) ∧
      (∀ s : A, s ∉ Ideal.span {t} → IsUnit (⟨s, hA _ s.2⟩ : V)) ∧
      (∀ f : V, ∃ a s : A, s ∉ Ideal.span {t} ∧ (f : L) * s = a) ∧
      (A.subtype.codRestrict V fun a => hA _ a.2).EssFiniteType := by
  first | exact @GlobalTheory.dvr_loc_principal_prime | exact GlobalTheory.dvr_loc_principal_prime | (intros; apply GlobalTheory.dvr_loc_principal_prime <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedHomogenisation

section

@[expose] public section

open MvPolynomial

namespace GlobalTheory

theorem exists_weightedHomogenisation {L : Type} [Field L] (Q : Subring L) (r : ℕ)
    (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ) (hwt : wt 0 = 1) (hz : (z 0 : L) ≠ 0)
    (P : MvPolynomial (Fin r) Q) :
    ∃ (N : ℕ) (F : MvPolynomial (Fin (r + 1)) Q), F.IsWeightedHomogeneous wt N ∧
      ((MvPolynomial.eval z F : Q) : L) = (z 0 : L) ^ N *
        MvPolynomial.eval₂ Q.subtype (fun i => (z i.succ : L) / (z 0 : L) ^ wt i.succ) P ∧
      ∀ α, ∃ β, F.coeff β = P.coeff α := by
  classical
  let d : (Fin r →₀ ℕ) → ℕ := fun α => ∑ i, α i * wt i.succ
  let N : ℕ := P.support.sup d
  let e : (Fin r →₀ ℕ) → (Fin (r + 1) →₀ ℕ) := fun α => Finsupp.cons (N - d α) α
  have he : Function.Injective e := fun a b h => by
    have := congrArg Finsupp.tail h
    simpa [e] using this
  have hd : ∀ α ∈ P.support, d α ≤ N := fun α h => Finset.le_sup (f := d) h
  refine ⟨N, ∑ α ∈ P.support, monomial (e α) (P.coeff α), ?_, ?_, ?_⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun α hα => ?_
    refine isWeightedHomogeneous_monomial _ _ _ ?_
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_succ]
    have := hd α hα
    simp only [e, Finsupp.cons_zero, Finsupp.cons_succ, hwt, smul_eq_mul, mul_one]
    change N - d α + d α = N
    omega
  · rw [eval₂_eq', Finset.mul_sum, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ]
    have h1 : (z 0 : L) ^ N = (z 0 : L) ^ (N - d α) * (z 0 : L) ^ d α := by
      rw [← pow_add, Nat.sub_add_cancel (hd α hα)]
    have h2 : (z 0 : L) ^ d α * ∏ i, ((z i.succ : L) / (z 0 : L) ^ wt i.succ) ^ α i
        = ∏ i, (z i.succ : L) ^ α i := by
      simp only [d]
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [mul_comm (α i), pow_mul, ← mul_pow, mul_div_cancel₀ _ (pow_ne_zero _ hz)]
    simp only [e, Finsupp.cons_zero, Finsupp.cons_succ]
    push_cast
    rw [h1, ← h2, Subring.coe_subtype]
    ring
  · intro α
    refine ⟨e α, ?_⟩
    rw [coeff_sum]
    simp only [coeff_monomial, he.eq_iff]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (notMem_support_iff.mp h).symm

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedHomogenisationStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_weightedHomogeneous_homogenisation : ∀ {L : Type} [Field L] (Q : Subring L) (r : ℕ) (z : Fin (r + 1) → Q)
    (wt : Fin (r + 1) → ℕ), wt 0 = 1 → (z 0 : L) ≠ 0 → ∀ P : MvPolynomial (Fin r) Q,
    ∃ (N : ℕ) (F : MvPolynomial (Fin (r + 1)) Q), F.IsWeightedHomogeneous wt N ∧
      ((MvPolynomial.eval z F : Q) : L) = (z 0 : L) ^ N *
        MvPolynomial.eval₂ Q.subtype (fun i => (z i.succ : L) / (z 0 : L) ^ wt i.succ) P ∧
      ∀ α, ∃ β, F.coeff β = P.coeff α := by
  first | exact @GlobalTheory.exists_weightedHomogenisation | exact GlobalTheory.exists_weightedHomogenisation | (intros; apply GlobalTheory.exists_weightedHomogenisation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialPlace

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

open MvPolynomial

theorem exists_weightedMonomialPlace : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (r : ℕ) (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ),
    IsNoetherianRing Q → Ideal.span (Set.range z) = IsLocalRing.maximalIdeal Q →
    IsQuasiRegularSeq Q z → wt 0 = 1 → (∀ i, 1 ≤ wt i) →
    ∃ (V : Place c) (hC : V.Contains Q) (u : Fin r → V.ring),
      (∀ i, (u i : L) * (z 0 : L) ^ wt i.succ = z i.succ) ∧
      Irreducible (⟨z 0, hC _ (z 0).2⟩ : V.ring) ∧
      (∀ q ∈ IsLocalRing.maximalIdeal Q,
        (⟨q, hC _ q.2⟩ : V.ring) ∈ IsLocalRing.maximalIdeal V.ring) ∧
      (∀ P : MvPolynomial (Fin r) Q, (∃ α, P.coeff α ∉ IsLocalRing.maximalIdeal Q) →
        IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P)) ∧
      ∀ f : V.ring, ∃ P R : MvPolynomial (Fin r) Q,
        IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R) ∧
        f * MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R =
          MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P := by
  intro L _ c Q hQ
  letI := hQ.isLocalRing
  intro r z wt hN hm hz hw0 hw
  haveI := hN
  have hz0 : (z 0 : L) ≠ 0 := by
    intro h
    have h1 : z 0 = 0 := Subtype.ext h
    have := GlobalTheory.T.coeff_mem_span_of_weightedHomogeneous_relation_quasiRegular z wt hw hz (wt 0) (X 0) (isWeightedHomogeneous_X Q wt 0)
      (by simp [h1]) (Finsupp.single 0 1)
    rw [coeff_X, if_pos rfl, hm] at this
    exact (IsLocalRing.maximalIdeal.isMaximal Q).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  set u : Fin r → L := fun i => (z i.succ : L) / (z 0 : L) ^ wt i.succ with hu
  have key0 : ∀ P : MvPolynomial (Fin r) Q, eval₂ Q.subtype u P = 0 →
      ∀ α, P.coeff α ∈ IsLocalRing.maximalIdeal Q := by
    intro P hP α
    obtain ⟨N, F, hF, hFe, hc⟩ := GlobalTheory.T.exists_weightedHomogeneous_homogenisation Q r z wt hw0 hz0 P
    obtain ⟨β, hβ⟩ := hc α
    rw [← hβ, ← hm]
    refine GlobalTheory.T.coeff_mem_span_of_weightedHomogeneous_relation_quasiRegular z wt hw hz N F hF ?_ β
    apply Subtype.ext
    rw [hFe, hP, mul_zero]
    rfl
  set e : MvPolynomial (Fin r) Q →+* L := eval₂Hom Q.subtype u with he
  set A : Subring L := e.range with hA
  set eA : MvPolynomial (Fin r) Q →+* A := e.rangeRestrict with heA
  have heA_surj : Function.Surjective eA := e.rangeRestrict_surjective
  have heA_val : ∀ P, ((eA P : A) : L) = e P := fun P => rfl
  have hQA : ∀ q ∈ Q, q ∈ A := fun q hq => ⟨C ⟨q, hq⟩, by simp [he]⟩
  have huA : ∀ i, u i ∈ A := fun i => ⟨X i, by simp [he]⟩
  let t : A := ⟨z 0, hQA _ (z 0).2⟩
  have hzA : ∀ j, ∃ a : A, ((z j : Q) : L) = (z 0 : L) * a := by
    intro j
    refine Fin.cases ⟨1, by simp⟩ (fun i => ?_) j
    refine ⟨⟨(z 0 : L) ^ (wt i.succ - 1) * u i, A.mul_mem (A.pow_mem (hQA _ (z 0).2) _) (huA i)⟩, ?_⟩
    show ((z i.succ : Q) : L) = (z 0 : L) * ((z 0 : L) ^ (wt i.succ - 1) * ((z i.succ : L) / (z 0 : L) ^ wt i.succ))
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (hw i.succ), mul_div_cancel₀ _ (pow_ne_zero _ hz0)]
  have hmA : Ideal.map (eA.comp C) (IsLocalRing.maximalIdeal Q) ≤ Ideal.span {t} := by
    rw [Ideal.map_le_iff_le_comap, ← hm, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨a, ha⟩ := hzA j
    show eA (C (z j)) ∈ Ideal.span {t}
    rw [Ideal.mem_span_singleton']
    exact ⟨a, Subtype.ext (by rw [heA_val]; simp [he, ha, mul_comm, t])⟩
  have hspan : Ideal.span {t} = Ideal.map eA (Ideal.map C (IsLocalRing.maximalIdeal Q)) := by
    rw [Ideal.map_map]
    refine le_antisymm ?_ hmA
    rw [Ideal.span_le, Set.singleton_subset_iff]
    have : t = (eA.comp C) (z 0) := Subtype.ext (by rw [RingHom.comp_apply, heA_val]; simp [he, t])
    rw [SetLike.mem_coe, this]
    exact Ideal.mem_map_of_mem _ (by rw [← hm]; exact Ideal.subset_span ⟨0, rfl⟩)
  have hker : RingHom.ker eA ≤ Ideal.map C (IsLocalRing.maximalIdeal Q) := by
    intro P hP
    rw [MvPolynomial.mem_map_C_iff]
    refine key0 P ?_
    have := congrArg Subtype.val ((RingHom.mem_ker).mp hP)
    simpa [heA_val, he] using this
  have hprimeC : (Ideal.map (C : Q →+* MvPolynomial (Fin r) Q) (IsLocalRing.maximalIdeal Q)).IsPrime := by
    have := MvPolynomial.ker_map (σ := Fin r) (IsLocalRing.residue Q)
    rw [IsLocalRing.ker_residue] at this
    rw [← this]
    exact RingHom.ker_isPrime _
  have hprime : (Ideal.span {t}).IsPrime := by
    rw [hspan]
    exact Ideal.map_isPrime_of_surjective heA_surj hker
  have key1 : ∀ P : MvPolynomial (Fin r) Q, eA P ∈ Ideal.span {t} →
      P ∈ Ideal.map C (IsLocalRing.maximalIdeal Q) := by
    intro P hP
    rw [hspan] at hP
    obtain ⟨x, hx, hxP⟩ := (Ideal.mem_map_iff_of_surjective eA heA_surj).mp hP
    have : P - x ∈ RingHom.ker eA := by rw [RingHom.mem_ker, map_sub, hxP, sub_self]
    simpa using Ideal.add_mem _ (hker this) hx
  have hNA : IsNoetherianRing A := isNoetherianRing_of_surjective _ _ eA heA_surj
  have hfracA : ∀ f : L, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ f * b = a := by
    intro f
    obtain ⟨a, ha, b, hb, hb0, hab⟩ := hQ.frac f
    exact ⟨a, hQA a ha, b, hQA b hb, hb0, hab⟩
  obtain ⟨V, hAV, hdvr, hirr, hunit, hfrV, hess⟩ :=
    GlobalTheory.T.isDVR_of_principal_prime_localization A t hNA hz0 hprime hfracA
  have hQAf : (Q.subtype.codRestrict A fun q => hQA _ q.2).FiniteType := by
    have h1 : (Q.subtype.codRestrict A fun q => hQA _ q.2) = eA.comp C := by
      ext q; simp [heA_val, he]
    rw [h1]
    exact RingHom.FiniteType.comp_surjective (RingHom.finiteType_algebraMap.mpr inferInstance) heA_surj
  have hconst : ∀ a, c a ∈ V := fun a => hAV _ (hQA _ (hQ.const_mem a))
  have hessV : (c.codRestrict V hconst).EssFiniteType := by
    have h := (hQ.essFiniteType.comp hQAf.essFiniteType).comp hess
    exact h
  let P0 : Place c := ⟨V, hconst, hdvr, hessV⟩
  have hC : P0.Contains Q := fun f hf => hAV _ (hQA _ hf)
  let uV : Fin r → P0.ring := fun i => ⟨u i, hAV _ (huA i)⟩
  have hev : ∀ P : MvPolynomial (Fin r) Q,
      ((MvPolynomial.eval₂ (Q.subtype.codRestrict P0.ring fun q => hC _ q.2) uV P : P0.ring) : L) =
        e P := by
    intro P
    exact MvPolynomial.eval₂_comp_left (P0.ring.subtype)
      (Q.subtype.codRestrict P0.ring fun q => hC _ q.2) uV P
  refine ⟨P0, hC, uV, fun i => ?_, ?_, fun q hq => ?_, fun P hP => ?_, fun f => ?_⟩
  · exact div_mul_cancel₀ _ (pow_ne_zero _ hz0)
  · exact hirr
  · obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton').mp (hmA (Ideal.mem_map_of_mem _ hq))
    have hmt : (⟨(t : L), hAV _ t.2⟩ : V) ∈ IsLocalRing.maximalIdeal V :=
      (IsLocalRing.mem_maximalIdeal _).mpr hirr.not_isUnit
    have : (⟨(q : L), hC _ q.2⟩ : P0.ring) = ⟨(a : L), hAV _ a.2⟩ * ⟨(t : L), hAV _ t.2⟩ :=
      Subtype.ext (by have := congrArg Subtype.val ha; simpa [heA_val, he] using this.symm)
    rw [this]
    exact Ideal.mul_mem_left _ _ hmt
  · have hs : eA P ∉ Ideal.span {t} := fun h => by
      obtain ⟨α, hα⟩ := hP
      exact hα ((MvPolynomial.mem_map_C_iff.mp (key1 P h)) α)
    have := hunit _ hs
    convert this using 1
    exact Subtype.ext (hev P)
  · obtain ⟨a, s, hs, hfs⟩ := hfrV f
    obtain ⟨P, rfl⟩ := heA_surj a
    obtain ⟨R, rfl⟩ := heA_surj s
    refine ⟨P, R, ?_, Subtype.ext ?_⟩
    · convert hunit _ hs using 1
      exact Subtype.ext (hev R)
    · calc ((f * MvPolynomial.eval₂ (Q.subtype.codRestrict P0.ring fun q => hC _ q.2) uV R : P0.ring) : L)
          = (f : L) * e R := by rw [← hev R]; rfl
        _ = e P := hfs
        _ = _ := (hev P).symm

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedMonomialPlaceStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_weightedMonomialPlace_of_isLocModel : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (r : ℕ) (z : Fin (r + 1) → Q) (wt : Fin (r + 1) → ℕ),
    IsNoetherianRing Q → Ideal.span (Set.range z) = IsLocalRing.maximalIdeal Q →
    IsQuasiRegularSeq Q z → wt 0 = 1 → (∀ i, 1 ≤ wt i) →
    ∃ (V : Place c) (hC : V.Contains Q) (u : Fin r → V.ring),
      (∀ i, (u i : L) * (z 0 : L) ^ wt i.succ = z i.succ) ∧
      Irreducible (⟨z 0, hC _ (z 0).2⟩ : V.ring) ∧
      (∀ q ∈ IsLocalRing.maximalIdeal Q,
        (⟨q, hC _ q.2⟩ : V.ring) ∈ IsLocalRing.maximalIdeal V.ring) ∧
      (∀ P : MvPolynomial (Fin r) Q, (∃ α, P.coeff α ∉ IsLocalRing.maximalIdeal Q) →
        IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P)) ∧
      ∀ f : V.ring, ∃ P R : MvPolynomial (Fin r) Q,
        IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R) ∧
        f * MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R =
          MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P := by
  first | exact @GlobalTheory.exists_weightedMonomialPlace | exact GlobalTheory.exists_weightedMonomialPlace | (intros; apply GlobalTheory.exists_weightedMonomialPlace <;> assumption)
end
end
