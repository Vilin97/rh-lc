module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.FormsAR
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.LimitPowMem
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.LatticeDuality

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.bidual :
    ∀ {A M : Type} [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M] [Module.Finite A M]
      (a : Module.Dual A (Module.Dual A M)), ∃ (d : A) (r : M), d ≠ 0 ∧ ∀ l : Module.Dual A M, l r = d * a l := by
  intro A M _ _ _ _ _ a
  classical
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A M).FG)
  let K := FractionRing A
  let ψ : Module.Dual A M → Option S → K := fun l o =>
    o.elim (algebraMap A K (a l)) (fun i => algebraMap A K (l (i : M)))
  have hψs : ∀ (p : A) l o, ψ (p • l) o = algebraMap A K p * ψ l o := by
    intro p l o
    cases o <;> simp [ψ]
  have hψa : ∀ l m o, ψ (l + m) o = ψ l o + ψ m o := by
    intro l m o
    cases o <;> simp [ψ]
  have hψ0 : ∀ o, ψ 0 o = 0 := by
    intro o
    cases o <;> simp [ψ]
  let v : Option S → K := fun j => if none = j then 1 else 0
  have key : ∀ w ∈ Submodule.span K (Set.range ψ),
      ∃ s : A, s ≠ 0 ∧ ∃ l, ∀ o, algebraMap A K s * w o = ψ l o := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact ⟨1, one_ne_zero, l, fun o => by simp⟩
    | zero =>
      exact ⟨1, one_ne_zero, 0, fun o => by simp [hψ0]⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, l, hl⟩ := hx
      obtain ⟨t, ht, m, hm⟩ := hy
      refine ⟨s * t, mul_ne_zero hs ht, t • l + s • m, fun o => ?_⟩
      rw [hψa, hψs, hψs, ← hl o, ← hm o, Pi.add_apply, map_mul]
      ring
    | smul c x _ hx =>
      obtain ⟨s, hs, l, hl⟩ := hx
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := A) c
      have hq0 : algebraMap A K q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
      have hc : algebraMap A K q * (algebraMap A K p / algebraMap A K q) = algebraMap A K p :=
        mul_div_cancel₀ _ hq0
      refine ⟨q * s, mul_ne_zero (nonZeroDivisors.ne_zero hq) hs, p • l, fun o => ?_⟩
      rw [hψs, ← hl o, Pi.smul_apply, smul_eq_mul, map_mul]
      linear_combination (algebraMap A K s * x o) * hc
  have hv : v ∉ Submodule.span K (Set.range ψ) := by
    intro hmem
    obtain ⟨s, hs, l, hl⟩ := key v hmem
    have hl0 : l = 0 := by
      apply LinearMap.ext_on hS
      intro i hi
      have h := hl (some ⟨i, hi⟩)
      simp [v, ψ] at h
      rw [LinearMap.zero_apply]
      exact IsFractionRing.injective A K (by rw [map_zero]; exact h.symm)
    subst hl0
    have h := hl none
    simp [v, ψ] at h
    exact hs h
  obtain ⟨f, hf, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hf0 : ∀ l, f (ψ l) = 0 := by
    intro l
    have h : f (ψ l) ∈ (Submodule.span K (Set.range ψ)).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨l, rfl⟩)
    rw [hfW] at h
    exact (Submodule.mem_bot K).mp h
  let c : Option S → K := fun o => f (fun j => if o = j then 1 else 0)
  obtain ⟨Dn, hDc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) c
  choose b hb using hDc
  have hD0 : algebraMap A K (Dn : A) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors Dn.2
  have hmain : ∀ l : Module.Dual A M, b none * a l + ∑ i : S, b (some i) * l i = 0 := by
    intro l
    have e : ∑ o, ψ l o * c o = 0 := by
      have h := hf0 l
      rw [LinearMap.pi_apply_eq_sum_univ f (ψ l)] at h
      simpa [c, smul_eq_mul] using h
    apply IsFractionRing.injective A K
    rw [map_zero]
    calc algebraMap A K (b none * a l + ∑ i : S, b (some i) * l i)
        = algebraMap A K (Dn : A) * ∑ o, ψ l o * c o := by

          rw [Fintype.sum_option, mul_add, Finset.mul_sum, map_add (f := _), map_mul, map_sum]
          congr 1
          · rw [hb, Algebra.smul_def]
            simp only [ψ, Option.elim_none]
            ring
          · refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [map_mul, hb, Algebra.smul_def]
            simp only [ψ, Option.elim_some]
            ring
      _ = 0 := by rw [e, mul_zero]
  refine ⟨b none, -(∑ i : S, b (some i) • (i : M)), ?_, ?_⟩
  · intro h0
    have h := hb none
    rw [h0, map_zero, Algebra.smul_def] at h
    exact hf ((mul_eq_zero.mp h.symm).resolve_left hD0)
  · intro l
    have h := hmain l

    rw [map_neg, map_sum]
    simp only [map_smul, smul_eq_mul]
    linear_combination -h
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CorePowMem

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem UpperTheory.V.AlgebraTools.Conn.core_pow_mem {R : Type} [CommRing R] (b c : Ideal R) (x : R)
    (hx : x ∈ (b ⊔ c).radical) (M : ℕ) : ∃ K, x ^ K ∈ b ^ M ⊔ c ^ M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · exact ⟨0, by simp⟩
  · have hx' : x ∈ (b ^ M ⊔ c ^ M).radical := by
      rw [Ideal.radical_sup, Ideal.radical_pow _ hM.ne', Ideal.radical_pow _ hM.ne',
        ← Ideal.radical_sup]
      exact hx
    exact hx'

private theorem UpperTheory.V.AlgebraTools.Conn.core_krull {R : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (P : Ideal R) (hP : P.IsPrime) (y r : R) (hy : y ∉ P)
    (h : ∀ n : ℕ, ∃ K : ℕ, y ^ K * r ∈ P ^ n) : r = 0 := by
  haveI := hP
  have hmem : ∀ n : ℕ, algebraMap R (Localization.AtPrime P) r ∈
      (maximalIdeal (Localization.AtPrime P)) ^ n := by
    intro n
    obtain ⟨K, hK⟩ := h n
    have h1 : algebraMap R (Localization.AtPrime P) (y ^ K * r) ∈
        (maximalIdeal (Localization.AtPrime P)) ^ n := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hK
    have hu : IsUnit (algebraMap R (Localization.AtPrime P) (y ^ K)) :=
      IsLocalization.map_units (Localization.AtPrime P)
        (⟨y ^ K, P.primeCompl.pow_mem hy K⟩ : P.primeCompl)
    rw [map_mul] at h1
    exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h1
  have h0 : algebraMap R (Localization.AtPrime P) r = 0 := by
    have hb := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (Localization.AtPrime P))
      (maximalIdeal.isMaximal _).ne_top
    rw [← Ideal.mem_bot, ← hb, Ideal.mem_iInf]
    exact hmem
  exact IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)
    (h0.trans (map_zero _).symm)


theorem UpperTheory.V.AlgebraTools.Conn.core :
    ∀ {A R : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing R] [IsDomain R] [Algebra A R] [Module.Finite A R]
      [FaithfulSMul A R] (I : Ideal A) [IsAdicComplete I A] (J : ℕ → Ideal A) (u v : A) (b c P Q : Ideal R) (y z : A),
      Antitone J → (∀ m, J m ≤ I ^ m) → (∀ m K, Reg2 (J m) (u ^ K) (v ^ K)) → (∀ m, ∃ N, I ^ N ≤ J m) →
      b * c ≤ (I.map (algebraMap A R)).radical →
      algebraMap A R u ∈ (b ⊔ c).radical → algebraMap A R v ∈ (b ⊔ c).radical →
      P.IsPrime → Q.IsPrime → b ≤ P → c ≤ Q → I.map (algebraMap A R) ≤ P → I.map (algebraMap A R) ≤ Q →
      algebraMap A R y ∈ (b ⊔ c).radical → algebraMap A R z ∈ (b ⊔ c).radical →
      algebraMap A R y ∉ P → algebraMap A R z ∉ Q → False := by
  intro A R _ _ _ _ _ _ _ _ I _ J u v b c P Q y z hJ hJI hreg hIJ hbc hu hv hP hQ hbP hcQ hIP hIQ
    hy hz hyP hzQ
  haveI : IsNoetherianRing R := IsNoetherianRing.of_finite A R
  obtain ⟨a, ha⟩ := UpperTheory.V.AlgebraTools.Conn.limit (R := R) I J u v b c hJ hJI hreg hIJ hbc
    (IsNoetherian.noetherian b) (IsNoetherian.noetherian c) hu hv
  obtain ⟨d, r, hd, hr⟩ := UpperTheory.V.AlgebraTools.Conn.bidual (M := R) a
  obtain ⟨k, hk⟩ := UpperTheory.V.AlgebraTools.Conn.formsAR (M := R) I
  have key : ∀ w : A, algebraMap A R w ∈ (b ⊔ c).radical → ∀ n : ℕ, ∃ N, n ≤ N ∧ ∃ K : ℕ,
      ∃ β ∈ b ^ N, ∃ γ ∈ c ^ N, β + γ = (algebraMap A R w) ^ K ∧
      algebraMap A R d * β - (algebraMap A R w) ^ K * r ∈ (I.map (algebraMap A R)) ^ n := by
    intro w hw n
    obtain ⟨N, hnN, hN⟩ := ha (n + k)
    obtain ⟨K, hK⟩ := core_pow_mem b c _ hw N
    obtain ⟨β, hβ, γ, hγ, hβγ⟩ := Submodule.mem_sup.mp hK
    refine ⟨N, le_trans (Nat.le_add_right n k) hnN, K, β, hβ, γ, hγ, hβγ, ?_⟩
    have hforms : ∀ l : Module.Dual A R, l (d • β - w ^ K • r) ∈ I ^ (n + k) := by
      intro l
      have h1 := hN (w ^ K) β γ hβ hγ (by rw [map_pow, hβγ]) l
      have h2 : l (d • β - w ^ K • r) = d * (l β - w ^ K * a l) := by
        rw [map_sub, map_smul, map_smul, hr, smul_eq_mul, smul_eq_mul]
        ring
      rw [h2]
      exact Ideal.mul_mem_left _ _ h1
    have h4 : d • β - w ^ K • r ∈ Ideal.map (algebraMap A R) (I ^ n) := by
      have h3 := hk n _ hforms
      rw [Ideal.smul_top_eq_map] at h3
      exact h3
    rw [← Ideal.map_pow]
    simpa [Algebra.smul_def] using h4
  have hr0 : r = 0 := by
    refine core_krull P hP (algebraMap A R y) r hyP fun n => ?_
    obtain ⟨N, hnN, K, β, hβ, γ, hγ, -, hdiff⟩ := key y hy n
    refine ⟨K, ?_⟩
    have hβP : β ∈ P ^ n := Ideal.pow_right_mono hbP n (Ideal.pow_le_pow_right hnN hβ)
    have hd' : algebraMap A R d * β - (algebraMap A R y) ^ K * r ∈ P ^ n :=
      Ideal.pow_right_mono hIP n hdiff
    have he : (algebraMap A R y) ^ K * r =
        algebraMap A R d * β - (algebraMap A R d * β - (algebraMap A R y) ^ K * r) := by ring
    rw [he]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hβP) hd'
  have hdr : algebraMap A R d - r = 0 := by
    refine core_krull Q hQ (algebraMap A R z) _ hzQ fun n => ?_
    obtain ⟨N, hnN, K, β, hβ, γ, hγ, hβγ, hdiff⟩ := key z hz n
    refine ⟨K, ?_⟩
    have hγQ : γ ∈ Q ^ n := Ideal.pow_right_mono hcQ n (Ideal.pow_le_pow_right hnN hγ)
    have hd' : algebraMap A R d * β - (algebraMap A R z) ^ K * r ∈ Q ^ n :=
      Ideal.pow_right_mono hIQ n hdiff
    have he : (algebraMap A R z) ^ K * (algebraMap A R d - r) =
        (algebraMap A R d * β - (algebraMap A R z) ^ K * r) + algebraMap A R d * γ := by
      rw [← hβγ]
      ring
    rw [he]
    exact Ideal.add_mem _ hd' (Ideal.mul_mem_left _ _ hγQ)
  rw [hr0, sub_zero] at hdr
  exact hd (FaithfulSMul.algebraMap_injective A R (hdr.trans (map_zero _).symm))
end
end
