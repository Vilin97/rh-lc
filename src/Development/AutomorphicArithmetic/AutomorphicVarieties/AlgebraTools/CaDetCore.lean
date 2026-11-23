module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DetLocus
public import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Ideal.BigOperators
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetDim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetKerIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetKerLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetChartPrime
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetAdj

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.det_mem_of_rel :
    ∀ (P : Type) [CommRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P)
      (Q : Ideal P), Q.IsPrime → relIdeal z m ≤ Q → (∃ j, m j ∉ Q) → detIdeal z m ≤ Q := by
  intro P _ ι _ _ z m Q hQ hrel ⟨j, hj⟩
  have hzm : ∀ k, z.mulVec m k ∈ Q := fun k => hrel (Ideal.subset_span ⟨k, rfl⟩)
  have hdet : z.det * m j ∈ Q := by
    have h1 : (z.adjugate.mulVec (z.mulVec m)) j = z.det * m j := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp
    rw [← h1, Matrix.mulVec, dotProduct]
    exact Q.sum_mem fun k _ => Q.mul_mem_left _ (hzm k)
  have hd : z.det ∈ Q := (hQ.mem_or_mem hdet).resolve_right hj
  exact sup_le hrel ((Ideal.span_singleton_le_iff_mem _).mpr hd)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetKerPrime

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.genKer_isPrime :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ c : ι, (genKer z m c).IsPrime ∧ detIdeal z m ≤ genKer z m c := by
  intro P _ _ ι _ _ z m hind c
  haveI hQ : (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)).IsPrime :=
    isPrime_map_C _
  haveI hJ := chartIdeal_localization_isPrime P ι z m hind c
    (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)) le_rfl
  have key : genKer z m c = Ideal.comap
      ((algebraMap (MvPolynomial ι P) (Localization.AtPrime
        (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)))).comp MvPolynomial.C)
      (Ideal.map (algebraMap (MvPolynomial ι P) (Localization.AtPrime
        (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)))) (chartIdeal z m c)) := by
    ext f
    rw [Ideal.mem_comap, RingHom.comp_apply,
      IsLocalization.algebraMap_mem_map_algebraMap_iff
        (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)).primeCompl]
    exact Iff.rfl
  have sub : ∀ f : P, MvPolynomial.C f ∈ chartIdeal z m c → f ∈ genKer z m c := by
    intro f hf
    rw [key, Ideal.mem_comap, RingHom.comp_apply]
    exact Ideal.mem_map_of_mem _ hf
  have gen : ∀ k, chartGen z m c k ∈ chartIdeal z m c := by
    intro k
    unfold chartIdeal
    exact Ideal.subset_span ⟨k, rfl⟩
  have hinl : ∀ i, ((z.map MvPolynomial.C).mulVec (lam P c)) i ∈ chartIdeal z m c :=
    fun i => gen (Sum.inl i)
  have hinr : ∀ j (h : j ≠ c),
      MvPolynomial.C (m j) - lam P c j * MvPolynomial.C (m c) ∈ chartIdeal z m c :=
    fun j h => gen (Sum.inr ⟨j, h⟩)
  have hdet : MvPolynomial.C z.det ∈ chartIdeal z m c := by
    have e : ((z.map MvPolynomial.C).adjugate.mulVec
        ((z.map MvPolynomial.C).mulVec (lam P c))) c = MvPolynomial.C z.det := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
        RingHom.map_det]
      simp [lam]
    rw [← e]
    show (∑ i, (z.map MvPolynomial.C).adjugate c i *
      ((z.map MvPolynomial.C).mulVec (lam P c)) i) ∈ _
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hinl i)
  refine ⟨by rw [key]; infer_instance, ?_⟩
  unfold detIdeal relIdeal
  refine sup_le (Ideal.span_le.2 ?_) (Ideal.span_le.2 (Set.singleton_subset_iff.2 (sub _ hdet)))
  rintro _ ⟨i, rfl⟩
  apply sub
  have e : MvPolynomial.C ((z.mulVec m) i) =
      ((z.map MvPolynomial.C).mulVec (lam P c)) i * MvPolynomial.C (m c) +
        ∑ j, MvPolynomial.C (z i j) * (MvPolynomial.C (m j) - lam P c j * MvPolynomial.C (m c)) := by

    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul,
    mul_sub, Finset.sum_sub_distrib, mul_assoc]
    ring
  rw [e]
  refine add_mem (Ideal.mul_mem_right _ _ (hinl i)) (Ideal.sum_mem _ fun j _ => ?_)
  by_cases h : j = c
  · simp [h, lam]
  · exact Ideal.mul_mem_left _ _ (hinr j h)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetMin

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.exists_least_prime_detIdeal :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) → Nonempty ι →
      ∃ K : Ideal P, K.IsPrime ∧ detIdeal z m ≤ K ∧ ∀ Q : Ideal P, Q.IsPrime → detIdeal z m ≤ Q → K ≤ Q := by
  intro P _ _ ι _ _ z m h hι
  obtain ⟨c0⟩ := id hι
  refine ⟨genKer z m c0, (genKer_isPrime P ι z m h c0).1, (genKer_isPrime P ι z m h c0).2, ?_⟩
  intro Q hQ hle
  let f : P →+* FractionRing (P ⧸ Q) :=
    (algebraMap (P ⧸ Q) (FractionRing (P ⧸ Q))).comp (Ideal.Quotient.mk Q)
  have hf : ∀ x, f x = 0 ↔ x ∈ Q := by
    intro x
    simp only [f, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective (P ⧸ Q) (FractionRing (P ⧸ Q))),
      Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  have h1 : (z.map f).mulVec (fun j => f (m j)) = 0 := by
    funext i
    have hi : z.mulVec m i ∈ Q :=
      hle (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
    have h2 := (hf _).2 hi

    simpa [Matrix.mulVec, dotProduct, map_sum, map_mul] using h2
  have h2 : (z.map f).det = 0 := by
    have hi : z.det ∈ Q := hle (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have h3 := (hf _).2 hi
    rw [RingHom.map_det] at h3
    exact h3
  obtain ⟨c, l, hc, hl, hz, hm⟩ := exists_kernel_vector _ V ι (z.map f) (fun j => f (m j)) h1 h2
  haveI : IsLocalRing V.toSubring := inferInstanceAs (IsLocalRing V)
  have hk := genKer_le_ker P ι z m h c V.toSubring (f.codRestrict V.toSubring hV)
    (fun j => ⟨l j, hl j⟩) (Subtype.ext hc) (by
      funext i
      apply Subtype.ext
      have h4 := congrFun hz i
      simpa [Matrix.mulVec, dotProduct] using h4) (fun j => Subtype.ext (hm j))
  rw [genKer_eq P ι z m h c0 c]
  intro x hx
  have h5 := hk hx
  rw [RingHom.mem_ker] at h5
  exact (hf x).1 (congrArg Subtype.val h5)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetLocus

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.le_of_detIdeal_le :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ Z : Ideal P, Z.IsPrime → relIdeal z m ≤ Z → (∃ j, m j ∉ Z) →
      ringKrullDim P ≤ ringKrullDim (P ⧸ Z) + (Fintype.card ι : ℕ) →
      ∀ Q : Ideal P, Q.IsPrime → detIdeal z m ≤ Q → Z ≤ Q := by
  intro P _ _ ι _ _ z m hc Z hZ hrel hm hdim Q hQ hdet
  have hdZ : detIdeal z m ≤ Z := det_mem_of_rel P ι z m Z hZ hrel hm
  by_cases hne : Nonempty ι
  swap
  · exfalso
    have : IsEmpty ι := not_nonempty_iff.1 hne
    apply hQ.ne_top
    rw [eq_top_iff]
    refine le_trans ?_ hdet
    simp [detIdeal, Matrix.det_isEmpty]
  obtain ⟨K, hK, hKdet, hKmin⟩ := exists_least_prime_detIdeal P ι z m hc hne
  haveI := hK
  haveI := hZ
  refine le_trans ?_ (hKmin Q hQ hdet)
  have hKZ : K ≤ Z := hKmin Z hZ hdZ
  by_contra hnot
  obtain ⟨x, hxZ, hxK⟩ := Set.not_subset.1 hnot
  have hrK : relIdeal z m ≤ K :=
    le_trans (le_sup_left : relIdeal z m ≤ relIdeal z m ⊔ Ideal.span {z.det}) hKdet
  have h1 : ringKrullDim (P ⧸ Z) + 1 ≤ ringKrullDim (P ⧸ K) := by
    refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hKZ)
      (Ideal.Quotient.factor_surjective hKZ) (r := Ideal.Quotient.mk K x) ?_ ?_
    · exact mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    · simpa [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] using hxZ
  have h2 : ringKrullDim (P ⧸ K) ≤ ringKrullDim (P ⧸ relIdeal z m) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hrK) (Ideal.Quotient.factor_surjective hrK)
  have h3 := dim_relIdeal_le P ι z m hc
  have hfin : ringKrullDim (P ⧸ Z) < ⊤ := lt_of_le_of_lt (ringKrullDim_quotient_le Z) ringKrullDim_lt_top
  have hbot : ringKrullDim (P ⧸ Z) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial
  have h12 := h1.trans h2
  have key : ringKrullDim (P ⧸ Z) + 1 + (Fintype.card ι : ℕ) ≤ ringKrullDim (P ⧸ Z) + (Fintype.card ι : ℕ) := by
    refine le_trans ?_ (h3.trans hdim)
    gcongr
  generalize ringKrullDim (P ⧸ Z) = d at key hfin hbot
  generalize Fintype.card ι = c at key
  induction d using WithBot.recBotCoe with
  | bot => exact hbot rfl
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => simp at hfin
    | coe d =>
      norm_cast at key
      omega
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetCore

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.under_le_of_det_mem :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] [Algebra.IsIntegral B A] [FaithfulSMul B A]
      (π : P →+* A), Function.Surjective π → relIdeal z m ≤ RingHom.ker π →
      ∀ Z : Ideal B, Z.IsPrime → ringKrullDim P ≤ ringKrullDim (B ⧸ Z) + (Fintype.card ι : ℕ) →
      (∀ Z' : Ideal A, Z'.IsPrime → Z'.comap (algebraMap B A) = Z → ∃ j, π (m j) ∉ Z') →
      ∀ Q' : Ideal A, Q'.IsPrime → π z.det ∈ Q' → Z ≤ Q'.comap (algebraMap B A) := by
  intro P _ _ ι _ _ z m hC B A _ _ _ _ _ π hπ hrel Z hZ hdim hm Q' hQ' hdet
  haveI := hZ
  have hinj : Function.Injective (algebraMap B A) := FaithfulSMul.algebraMap_injective B A
  obtain ⟨Z', -, hZ'p, hZ'c⟩ := Ideal.exists_ideal_over_prime_of_isIntegral Z (⊥ : Ideal A) (by
    rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]; exact bot_le)
  change Ideal.comap (algebraMap B A) Z' = Z at hZ'c
  haveI := hZ'p
  haveI := hQ'
  obtain ⟨j, hj⟩ := hm Z' hZ'p hZ'c
  have hker : RingHom.ker ((Ideal.Quotient.mk Z').comp π) = Z'.comap π := by
    ext x
    simp [Ideal.Quotient.eq_zero_iff_mem]
  have e : P ⧸ Z'.comap π ≃+* A ⧸ Z' :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective
      (Ideal.Quotient.mk_surjective.comp hπ))
  have hdimZ : ringKrullDim (P ⧸ Z'.comap π) = ringKrullDim (B ⧸ Z) := by
    rw [ringKrullDim_eq_of_ringEquiv e,
      ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral (A := B) (B := A) Z', hZ'c]
  have hrelQ : ∀ I : Ideal A, relIdeal z m ≤ I.comap π := fun I x hx => by
    have h0 : π x = 0 := RingHom.mem_ker.mp (hrel hx)
    simp [Ideal.mem_comap, h0]
  have key := le_of_detIdeal_le P ι z m hC (Z'.comap π) inferInstance (hrelQ Z') ⟨j, hj⟩
    (by rw [hdimZ]; exact hdim) (Q'.comap π) inferInstance (by
      show relIdeal z m ⊔ Ideal.span {z.det} ≤ _
      refine sup_le (hrelQ Q') ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hdet)
  have hle : Z' ≤ Q' := by
    intro a ha
    obtain ⟨x, rfl⟩ := hπ a
    exact key ha
  rw [← hZ'c]
  exact Ideal.comap_mono hle
end
end
