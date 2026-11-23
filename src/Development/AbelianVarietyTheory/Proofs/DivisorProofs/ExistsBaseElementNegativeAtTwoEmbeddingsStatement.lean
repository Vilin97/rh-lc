module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostNormClassCount
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlmostNormFinDiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaProdEqOfEverywhereNormDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEverywhereNormDivOfEtaProdEqOne
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalIffEtaProd

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.QuadRecip

open GlobalTheory.QuadSymbol

theorem exists_global_iff_etaProd (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (x : FinFam K) (y : InfFam K)
    (hx : AlmostNorm K L x) :
    (∃ t : Kˣ, (∀ v, x v / finDiag K t v ∈ normGroup K L (v.adicCompletion K)) ∧
        ∀ w, y w / infDiag K t w ∈ normGroup K L w.Completion) ↔
      etaProd K L x y = 1 :=
  (exactSequence K L).2.2.1 x y hx

theorem ringEquivReal_infDiag {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}
    (hw : w.IsReal) (t : Kˣ) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infDiag K t w : (w.Completion)ˣ) : w.Completion) =
      InfinitePlace.embedding_of_isReal hw (t : K) :=
  by
    simp [infDiag, QuadSymbol.toUnits, InfinitePlace.Completion.algebraMap_apply]

theorem mem_normGroup_of_pos {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] {w : InfinitePlace K} (hw : w.IsReal) (z : (w.Completion)ˣ)
    (hz : 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (z : w.Completion)) :
    z ∈ normGroup K L w.Completion := by
  obtain ⟨δ, b, -, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  rw [mem_normGroup_iff_form b h0 h1]
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  refine ⟨e.symm (Real.sqrt (e z)), 0, e.injective ?_⟩
  simp [Real.sq_sqrt hz.le]

theorem mem_normGroup_iff_pos {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (hL : IsTotallyComplex L)
    {w : InfinitePlace K} (hw : w.IsReal) (z : (w.Completion)ˣ) :
    z ∈ normGroup K L w.Completion ↔
      0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (z : w.Completion) := by
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  refine ⟨fun hz => ?_, mem_normGroup_of_pos hw z⟩
  have hne : e (z : w.Completion) ≠ 0 := (map_ne_zero e).2 z.ne_zero
  refine lt_of_le_of_ne (not_lt.1 fun hlt => ?_) hne.symm
  have hm : (-z) ∈ normGroup K L w.Completion :=
    mem_normGroup_of_pos hw (-z) (by rw [Units.val_neg, map_neg]; exact neg_pos.2 hlt)
  have h1 : (-1 : (w.Completion)ˣ) = z * (-z)⁻¹ := by rw [inv_neg, mul_neg, mul_inv_cancel]
  exact SignCount.neg_one_not_mem_normGroup hL hw (h1 ▸ mul_mem hz (inv_mem hm))

end GlobalTheory.QuadRecip

namespace GlobalTheory.QuadRecip

open GlobalTheory.QuadSymbol


open Classical in
theorem prod_sign_eq {K : Type} [Field K] [NumberField K] (S : Finset {w : InfinitePlace K // w.IsReal})
    (f : InfinitePlace K → ℤˣ)
    (hf : ∀ w, f w = if (∃ hw : w.IsReal, (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ S) then -1 else 1) :
    ∏ w, f w = (-1) ^ S.card := by
  classical
  simp_rw [hf]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  congr 1
  have : (Finset.univ.filter fun w : InfinitePlace K =>
      ∃ hw : w.IsReal, (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ S) =
      S.map (Function.Embedding.subtype _) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨hw, h⟩
      exact ⟨_, h, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, hu⟩
  rw [this, Finset.card_map]


open Classical in
theorem exists_signs_iff_even (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (hL : IsTotallyComplex L)
    (S : Finset {w : InfinitePlace K // w.IsReal}) :
    (∃ h : Kˣ, (∀ w : {w : InfinitePlace K // w.IsReal},
        (w ∈ S → InfinitePlace.embedding_of_isReal w.2 (h : K) < 0) ∧
        (w ∉ S → 0 < InfinitePlace.embedding_of_isReal w.2 (h : K))) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), finDiag K h v ∈ normGroup K L (v.adicCompletion K)) ↔
      Even S.card := by
  classical
  obtain ⟨δ, b, -, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hneg1 : ((-1 : ℤˣ) ≠ 1) := by decide
  constructor
  · rintro ⟨h, hsgn, hfin⟩
    have hpf := (productFormula K L h).2
    unfold etaProd at hpf
    have hf1 : ∀ v : HeightOneSpectrum (𝓞 K), eta K L (v.adicCompletion K) (finDiag K h v) = 1 :=
      fun v => eta_eq_one_iff.2 (hfin v)
    simp only [hf1, finprod_one, one_mul] at hpf
    rw [prod_sign_eq S _ (fun w => ?_)] at hpf
    · exact (neg_one_pow_eq_one_iff_even hneg1).1 hpf
    · by_cases hw : w.IsReal
      · have key := mem_normGroup_iff_pos hL hw (infDiag K h w)
        rw [ringEquivReal_infDiag hw h] at key
        by_cases hS : (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ S
        · rw [if_pos ⟨hw, hS⟩, eta_eq_neg_one_iff, key]
          exact not_lt.2 ((hsgn ⟨w, hw⟩).1 hS).le
        · rw [if_neg (by rintro ⟨hw', h'⟩; exact hS h'), eta_eq_one_iff, key]
          exact (hsgn ⟨w, hw⟩).2 hS
      · rw [if_neg (by rintro ⟨hw', _⟩; exact hw hw'), eta_eq_one_iff]
        exact Converse.mem_normGroup_of_isComplex b h0 h1 (InfinitePlace.not_isReal_iff_isComplex.1 hw) _
  · intro hS
    let P : InfinitePlace K → Prop := fun w =>
      ∃ hw : w.IsReal, (⟨w, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ S
    let y : InfFam K := fun w => if P w then -1 else 1
    have hy : ∀ w, eta K L w.Completion (y w) = if P w then -1 else 1 := by
      intro w
      by_cases hP : P w
      · simp only [y, if_pos hP]
        exact eta_eq_neg_one_iff.2 (SignCount.neg_one_not_mem_normGroup hL hP.1)
      · simp only [y, if_neg hP]
        exact eta_eq_one_iff.2 (one_mem _)
    have hx : AlmostNorm K L (1 : FinFam K) := by
      refine Set.Finite.subset Set.finite_empty fun v hv => hv ?_
      exact one_mem _
    have hprod : etaProd K L 1 y = 1 := by
      unfold etaProd
      have hf1 : ∀ v : HeightOneSpectrum (𝓞 K),
          eta K L (v.adicCompletion K) ((1 : FinFam K) v) = 1 := fun v => eta_eq_one_iff.2 (one_mem _)
      simp only [hf1, finprod_one, one_mul]
      rw [prod_sign_eq S _ hy]
      exact hS.neg_one_pow
    obtain ⟨t, htf, hti⟩ := (exists_global_iff_etaProd K L 1 y hx).2 hprod
    refine ⟨t, fun w => ?_, fun v => ?_⟩
    · have key := (mem_normGroup_iff_pos hL w.2 _).1 (hti w.1)
      rw [Units.val_div_eq_div_val, map_div₀, ringEquivReal_infDiag w.2 t] at key
      have hP : P w.1 ↔ w ∈ S := ⟨by rintro ⟨_, h⟩; exact h, fun h => ⟨w.2, h⟩⟩
      constructor
      · intro hw
        have hyw : y w.1 = -1 := if_pos (hP.2 hw)
        rw [hyw, Units.val_neg, Units.val_one, map_neg, map_one] at key
        have := (div_pos_iff.1 key)
        rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
        · linarith
        · exact h2
      · intro hw
        have hyw : y w.1 = 1 := if_neg (fun h => hw (hP.1 h))
        rw [hyw, Units.val_one, map_one] at key
        exact (one_div_pos).1 key
    · have := htf v
      rw [Pi.one_apply, one_div, inv_mem_iff] at this
      exact this

theorem exists_signs_of_even (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (hK : IsTotallyReal K) (hL : IsTotallyComplex L)
    (S : Finset (InfinitePlace K)) (hS : Even S.card) :
    ∃ h : Kˣ, (∀ w (hw : w ∈ S), InfinitePlace.embedding_of_isReal (hK.isReal w) (h : K) < 0) ∧
      (∀ w (hw : w ∉ S), 0 < InfinitePlace.embedding_of_isReal (hK.isReal w) (h : K)) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), finDiag K h v ∈ normGroup K L (v.adicCompletion K) := by
  classical
  let S' : Finset {w : InfinitePlace K // w.IsReal} := S.subtype _
  have hc : S'.card = S.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem fun w _ => hK.isReal w
  obtain ⟨h, hsgn, hfin⟩ := (exists_signs_iff_even K L hL S').2 (hc ▸ hS)
  refine ⟨h, fun w hw => (hsgn ⟨w, hK.isReal w⟩).1 ?_, fun w hw => (hsgn ⟨w, hK.isReal w⟩).2 ?_, hfin⟩
  · simpa [S'] using hw
  · simpa [S'] using hw

end GlobalTheory.QuadRecip
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseElementNegativeAtTwoEmbeddings

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.QuadSigns

section Field

variable {L : Type} [Field L] [NumberField L]

theorem conj_involutive (σ : L →+* L)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) (x : L) : σ (σ x) = x := by
  let φ := (Classical.arbitrary (InfinitePlace L)).embedding
  apply φ.injective
  rw [hc, hc, Complex.conj_conj]

theorem isTotallyComplex_of_conj (σ : L →+* L) (hσ : σ ≠ RingHom.id L)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) : IsTotallyComplex L := by
  refine ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.1 fun hr => hσ ?_⟩
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff] at hr
  refine RingHom.ext fun x => w.embedding.injective ?_
  rw [hc, RingHom.id_apply, ← ComplexEmbedding.conjugate_coe_eq, hr]

end Field

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem isReal_comp (σ : L →+* L) (hK : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) (φ : L →+* ℂ) :
    ComplexEmbedding.IsReal (φ.comp (algebraMap K L)) := by
  rw [ComplexEmbedding.isReal_iff]
  refine RingHom.ext fun x => ?_
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hc, hK]

theorem isTotallyReal_of_conj [Algebra.IsAlgebraic K L] (σ : L →+* L)
    (hK : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) : IsTotallyReal K := by
  refine ⟨fun w => ?_⟩
  obtain ⟨W, rfl⟩ := InfinitePlace.comap_surjective (k := K) (K := L) w
  show (W.comap (algebraMap K L)).IsReal
  rw [← W.mk_embedding, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff]
  exact isReal_comp σ hK hc _

theorem eq_or_eq_conjugate (hd : Module.finrank K L = 2) (σ : L →+* L) (hσ : σ ≠ RingHom.id L)
    (hK : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) (φ ε : L →+* ℂ)
    (h : φ.comp (algebraMap K L) = ε.comp (algebraMap K L)) :
    φ = ε ∨ φ = ComplexEmbedding.conjugate ε := by
  have hss := conj_involutive σ hc
  obtain ⟨s, hs⟩ : ∃ s, σ s ≠ s := by
    by_contra hne
    push_neg at hne
    exact hσ (RingHom.ext hne)
  set t := s - σ s with ht
  have hσt : σ t = -t := by rw [ht, map_sub, hss]; ring
  have ht0 : t ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
  have hli : LinearIndependent K ![(1 : L), t] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h2 := congrArg σ hab
    simp only [Algebra.smul_def, map_add (f := _), map_mul, hK, hσt, map_one, map_zero, mul_one] at h2 hab
    have hb2 : (2 : L) * (algebraMap K L b * t) = 0 := by linear_combination hab - h2
    have hb : b = 0 := by simpa [ht0] using hb2
    subst hb
    simp only [map_zero, zero_mul, add_zero, FaithfulSMul.algebraMap_eq_zero_iff] at hab
    exact ⟨hab, rfl⟩
  have hdec : ∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * t := by
    intro x
    let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hd])
    refine ⟨B.repr x 0, B.repr x 1, ?_⟩
    conv_lhs => rw [← B.sum_repr x]
    simp [B, Fin.sum_univ_two, Algebra.smul_def]
  have hφK : ∀ a : K, φ (algebraMap K L a) = ε (algebraMap K L a) := fun a => RingHom.congr_fun h a
  obtain ⟨a, b, hab⟩ := hdec (t * t)
  have hb : b = 0 := by
    have h2 : σ (t * t) = t * t := by rw [map_mul, hσt, neg_mul_neg]
    rw [hab] at h2
    simp only [map_add (f := _), map_mul, hK, hσt] at h2
    have hb2 : (2 : L) * (algebraMap K L b * t) = 0 := by linear_combination -h2
    simpa [ht0] using hb2
  subst hb
  simp only [map_zero, zero_mul, add_zero] at hab
  have hsq : φ t * φ t = ε t * ε t := by rw [← map_mul, ← map_mul, hab, hφK]
  have hfac : (φ t - ε t) * (φ t + ε t) = 0 := by linear_combination hsq
  rcases mul_eq_zero.1 hfac with h1 | h1
  · left
    have hφt : φ t = ε t := sub_eq_zero.1 h1
    refine RingHom.ext fun x => ?_
    obtain ⟨a', b', rfl⟩ := hdec x
    simp only [map_add (f := _), map_mul, hφK, hφt]
  · right
    have hφt : φ t = -ε t := eq_neg_of_add_eq_zero_left h1
    refine RingHom.ext fun x => ?_
    obtain ⟨a', b', rfl⟩ := hdec x
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc]
    simp only [map_add (f := _), map_mul, hφK, hφt, hK, hσt, map_neg]

end GlobalTheory.QuadSigns

namespace GlobalTheory.QuadSigns

open scoped TensorProduct

theorem exists_signs (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hd : Module.finrank K L = 2) (σ : L →+* L) (hσ : σ ≠ RingHom.id L)
    (hK : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    (hc : ∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) (ε ε' : L →+* ℂ)
    (h1 : ε ≠ ε') (h2 : ε ≠ ComplexEmbedding.conjugate ε') :
    ∃ h : K, h ≠ 0 ∧ (ε (algebraMap K L h)).re < 0 ∧ (ε' (algebraMap K L h)).re < 0 ∧
      (∀ φ : L →+* ℂ, φ ≠ ε → φ ≠ ComplexEmbedding.conjugate ε → φ ≠ ε' →
        φ ≠ ComplexEmbedding.conjugate ε' → 0 < (φ (algebraMap K L h)).re) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), ∃ z : v.adicCompletion K ⊗[K] L,
        Algebra.norm (v.adicCompletion K) z = algebraMap K (v.adicCompletion K) h := by
  classical
  haveI : Algebra.IsQuadraticExtension K L := ⟨hd⟩
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  have hKr : IsTotallyReal K := isTotallyReal_of_conj σ hK hc
  have hLc : IsTotallyComplex L := isTotallyComplex_of_conj σ hσ hc
  have hover : ∀ φ ψ : L →+* ℂ, InfinitePlace.mk (φ.comp (algebraMap K L)) =
      InfinitePlace.mk (ψ.comp (algebraMap K L)) → φ = ψ ∨ φ = ComplexEmbedding.conjugate ψ := by
    intro φ ψ hm
    apply eq_or_eq_conjugate hd σ hσ hK hc
    rcases InfinitePlace.mk_eq_iff.1 hm with hh | hh
    · exact hh
    · rwa [ComplexEmbedding.isReal_iff.1 (isReal_comp σ hK hc φ)] at hh
  set w₁ := InfinitePlace.mk (ε.comp (algebraMap K L)) with hw₁
  set w₂ := InfinitePlace.mk (ε'.comp (algebraMap K L)) with hw₂
  have hw : w₁ ≠ w₂ := by
    intro he
    rcases hover ε ε' he with hh | hh
    · exact h1 hh
    · exact h2 hh
  obtain ⟨h, hneg, hpos, hfin⟩ := GlobalTheory.QuadRecip.exists_signs_of_even K L hKr hLc {w₁, w₂}
    (by rw [Finset.card_pair hw]; decide)
  have hsign : ∀ φ : L →+* ℂ, (φ (algebraMap K L (h : K))).re =
      InfinitePlace.embedding_of_isReal (hKr.isReal (InfinitePlace.mk (φ.comp (algebraMap K L))))
        (h : K) := by
    intro φ
    have := InfinitePlace.embedding_of_isReal_apply
      (hKr.isReal (InfinitePlace.mk (φ.comp (algebraMap K L)))) (h : K)
    rw [InfinitePlace.embedding_mk_eq_of_isReal (isReal_comp σ hK hc φ), RingHom.comp_apply] at this
    rw [← this, Complex.ofReal_re]
  refine ⟨h, h.ne_zero, ?_, ?_, ?_, ?_⟩
  · rw [hsign]
    exact hneg _ (by simp [w₁])
  · rw [hsign]
    exact hneg _ (by simp [w₂])
  · intro φ n1 n2 n3 n4
    rw [hsign]
    refine hpos _ ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro he
      rcases hover φ ε he with hh | hh
      · exact n1 hh
      · exact n2 hh
    · intro he
      rcases hover φ ε' he with hh | hh
      · exact n3 hh
      · exact n4 hh
  · intro v
    obtain ⟨z, hz⟩ := GlobalTheory.QuadSymbol.mem_normGroup_iff.1 (hfin v)
    exact ⟨z, hz⟩

end GlobalTheory.QuadSigns
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseElementNegativeAtTwoEmbeddingsStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_base_element_negative_at_two_embeddings : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L], Module.finrank K L = 2 → ∀ σ : L →+* L, σ ≠ RingHom.id L → (∀ x : K, σ (algebraMap K L x) = algebraMap K L x) → (∀ (φ : L →+* ℂ) (x : L), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ ε ε' : L →+* ℂ, ε ≠ ε' → ε ≠ ComplexEmbedding.conjugate ε' → ∃ h : K, h ≠ 0 ∧ (ε (algebraMap K L h)).re < 0 ∧ (ε' (algebraMap K L h)).re < 0 ∧ (∀ φ : L →+* ℂ, φ ≠ ε → φ ≠ ComplexEmbedding.conjugate ε → φ ≠ ε' → φ ≠ ComplexEmbedding.conjugate ε' → 0 < (φ (algebraMap K L h)).re) ∧ ∀ v : HeightOneSpectrum (𝓞 K), ∃ z : v.adicCompletion K ⊗[K] L, Algebra.norm (v.adicCompletion K) z = algebraMap K (v.adicCompletion K) h := by
  first | (exact @GlobalTheory.QuadSigns.exists_signs) | (exact GlobalTheory.QuadSigns.exists_signs) | (intros; apply GlobalTheory.QuadSigns.exists_signs  <;> assumption)
end
end
