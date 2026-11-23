module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLen
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.Nakayama
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenComp
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.NilLen

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Imports

section

@[expose] public section

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.frob :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (g : Module.End ℤ_[l] X) (k : ℕ),
      InPow 1 ((g - 1) ^ l ^ k) ↔ InPow 1 (g ^ l ^ k - 1) := by
  intro l _ X _ _ g k
  have hpoly : (Polynomial.C (l : ℤ)) ∣
      ((Polynomial.X - 1) ^ l ^ k - (Polynomial.X ^ l ^ k - 1) : Polynomial ℤ) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have hmap : Polynomial.map (Int.castRingHom (ZMod l))
        ((Polynomial.X - 1) ^ l ^ k - (Polynomial.X ^ l ^ k - 1) : Polynomial ℤ) = 0 := by
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
      rw [sub_pow_char_pow, one_pow, sub_self]
    have hc := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P i) hmap
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1 hc
  obtain ⟨Q, hQ⟩ := hpoly
  have key : (g - 1) ^ l ^ k - (g ^ l ^ k - 1) = (l : Module.End ℤ_[l] X) * Polynomial.aeval g Q := by
    have := congrArg (Polynomial.aeval g) hQ
    simpa using this
  have step : ∀ f f' : Module.End ℤ_[l] X, (∃ h : Module.End ℤ_[l] X, f - f' = (l : Module.End ℤ_[l] X) * h) →
      InPow 1 f' → InPow 1 f := by
    rintro f f' ⟨h, hh⟩ H x
    obtain ⟨y, hy⟩ := H x
    refine ⟨y + h x, ?_⟩
    have hf : f = (l : Module.End ℤ_[l] X) * h + f' := eq_add_of_sub_eq hh
    rw [pow_one] at hy ⊢
    rw [hf, LinearMap.add_apply, Module.End.mul_apply, Module.End.natCast_apply, hy, smul_add,
      Nat.cast_smul_eq_nsmul ℤ_[l] l (h x), add_comm]
  constructor
  · exact step _ _ ⟨-Polynomial.aeval g Q, by rw [mul_neg, ← key, neg_sub]⟩
  · exact step _ _ ⟨Polynomial.aeval g Q, key⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ImportsBis

section

@[expose] public section

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.mono :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (g : Module.End ℤ_[l] X) (a b : ℕ), a ∣ b →
      cokLen (g ^ a - 1) ≤ cokLen (g ^ b - 1) := by
  intro l _ X _ _ g a b hab
  apply cokLen_le_of_range_le
  obtain ⟨k, rfl⟩ := hab
  rw [pow_mul, ← mul_geom_sum]
  exact LinearMap.range_comp_le_range _ _
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ImportsTer

section

@[expose] public section

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.phi :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] [Module.Finite ℤ_[l] X] (w : Module.End ℤ_[l] X), InPow 2 (w - 1) →
      LinearMap.range ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X)) ≤ LinearMap.range (∑ i ∈ Finset.range l, w ^ i) := by
  intro l _ X _ _ _ w hw
  have hpow : ∀ (i : ℕ) (x : X), ∃ y : X, (w ^ i) x = x + (l : ℤ_[l]) ^ 2 • y := by
    intro i
    induction i with
    | zero => intro x; exact ⟨0, by simp⟩
    | succ i ih =>
      intro x
      obtain ⟨y, hy⟩ := ih (w x)
      obtain ⟨z, hz⟩ := hw x
      refine ⟨z + y, ?_⟩
      rw [pow_succ, Module.End.mul_apply, hy, smul_add, ← hz]
      simp only [LinearMap.sub_apply, Module.End.one_apply]
      abel
  have hsum : ∀ (n : ℕ) (x : X), ∃ y : X,
      (∑ i ∈ Finset.range n, w ^ i) x = (n : ℤ_[l]) • x + (l : ℤ_[l]) ^ 2 • y := by
    intro n x
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨z, hz⟩ := hpow n x
      refine ⟨y + z, ?_⟩
      rw [Finset.sum_range_succ, LinearMap.add_apply, hy, hz, smul_add, Nat.cast_succ, add_smul, one_smul]
      abel
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {(l : ℤ_[l])}) ?_ ?_ ?_
  · exact IsNoetherian.noetherian _
  · rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, PadicInt.maximalIdeal_eq_span_p]
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hsum l x
    have e : ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X)) x
        = (∑ i ∈ Finset.range l, w ^ i) x + (l : ℤ_[l]) • (((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X)) (-y)) := by
      rw [hy]
      simp only [LinearMap.smul_apply, Module.End.one_apply, smul_neg, pow_two, mul_smul]
      abel
    rw [e]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _)
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (LinearMap.mem_range_self _ _))
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ImportsMore

section

@[expose] public section

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.step :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (R : ℕ) (w : Module.End ℤ_[l] X), GenBy l R X → InPow 2 (w - 1) →
      cokLen (w ^ l - 1) ≤ cokLen (w - 1) + R := by
  intro l _ X _ _ R w hG hw
  haveI : Module.Finite ℤ_[l] X := by
    obtain ⟨π, hπ⟩ := hG
    exact Module.Finite.of_surjective π hπ
  have h1 := (UpperTheory.V.Base.lenComp ℤ_[l] X (∑ i ∈ Finset.range l, w ^ i) (w - 1)).2
  rw [geom_sum_mul] at h1
  have h2 := cokLen_le_of_range_le (phi l X w hw)
  have h3 := cokL l X R hG
  calc cokLen (w ^ l - 1) ≤ cokLen (∑ i ∈ Finset.range l, w ^ i) + cokLen (w - 1) := h1
    _ ≤ R + cokLen (w - 1) := add_le_add_left (h2.trans h3) _
    _ = cokLen (w - 1) + R := add_comm _ _
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.PowIn

section

@[expose] public section

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.powIn :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (w : Module.End ℤ_[l] X),
      (∀ k n : ℕ, InPow k (w - 1) → InPow k (w ^ n - 1)) ∧ (InPow 1 (w - 1) → InPow 2 (w ^ l - 1)) := by
  intro l _ X _ _ w
  refine ⟨?_, ?_⟩
  · intro k n H x
    obtain ⟨y, hy⟩ := H x
    refine ⟨(∑ i ∈ Finset.range n, w ^ i) y, ?_⟩
    rw [← geom_sum_mul, Module.End.mul_apply, hy, map_smul]
  · intro H x
    obtain ⟨y, hy⟩ := H x
    obtain ⟨y', hy'⟩ := H y
    rw [pow_one] at hy hy'
    refine ⟨y + ∑ i ∈ Finset.range l, (∑ j ∈ Finset.range i, w ^ j) y', ?_⟩
    have hw : ∀ i, (w ^ i) y = y + (l : ℤ_[l]) • (∑ j ∈ Finset.range i, w ^ j) y' := by
      intro i
      have h0 : (w ^ i - 1) y = (∑ j ∈ Finset.range i, w ^ j) ((w - 1) y) := by
        rw [← Module.End.mul_apply, geom_sum_mul]
      rw [hy', map_smul] at h0
      rw [← h0, LinearMap.sub_apply, Module.End.one_apply, add_sub_cancel]
    rw [← geom_sum_mul, Module.End.mul_apply, hy, map_smul, LinearMap.sum_apply]
    simp_rw [hw]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.smul_sum,
      ← Nat.cast_smul_eq_nsmul ℤ_[l], ← smul_add, pow_two, mul_smul]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.UnipPow

section

@[expose] public section

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.unipPow :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (R : ℕ) (g : Module.End ℤ_[l] X), GenBy l R X → Unip g → InPow 1 ((g - 1) ^ R) := by
  intro l _ X _ _ R g hgen hu
  obtain ⟨N, hN⟩ := hu
  let p : Submodule ℤ_[l] X := LinearMap.range ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X))
  have memp : ∀ v : X, v ∈ p ↔ ∃ y, v = (l : ℤ_[l]) ^ 1 • y := by
    intro v
    simp only [p, LinearMap.mem_range, LinearMap.smul_apply, Module.End.one_apply, pow_one]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩
  have hp : p ≤ p.comap (g - 1) := by
    intro v hv
    obtain ⟨y, rfl⟩ := (memp v).mp hv
    rw [Submodule.mem_comap, map_smul]
    exact (memp _).mpr ⟨(g - 1) y, rfl⟩
  let F : Module.End ℤ_[l] (X ⧸ p) := p.mapQ p (g - 1) hp
  have hFx : ∀ x : X, F (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((g - 1) x) :=
    fun x => Submodule.mapQ_apply _ _ _ x
  have key : ∀ (k : ℕ) (x : X), (F ^ k) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (((g - 1) ^ k) x) := by
    intro k
    induction k with
    | zero =>
      intro x
      simp
    | succ k ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, hFx, ih, pow_succ, Module.End.mul_apply]
  have hnil : IsNilpotent F := by
    refine ⟨N, ?_⟩
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective p z
    rw [Submodule.mkQ_apply, key, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero, memp]
    exact hN x
  have hlen : Module.length ℤ_[l] (X ⧸ p) ≤ R := cokL l X R hgen
  have hF0 := nilLen ℤ_[l] (X ⧸ p) F R hnil hlen
  intro x
  have hk := key R x
  rw [hF0, LinearMap.zero_apply, eq_comm, Submodule.Quotient.mk_eq_zero, memp] at hk
  exact hk
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Growth

section

@[expose] public section

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.growth :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (R : ℕ) (g : Module.End ℤ_[l] X), GenBy l R X → Unip g → ∀ m : ℕ,
      cokLen (g ^ l ^ m - 1) ≤ cokLen (g ^ l ^ jZero l R - 1) + ((R * (m - jZero l R) : ℕ) : ℕ∞) := by
  intro l _ X _ _ R g hG hU m
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  obtain ⟨k, hk⟩ : ∃ k, k = Nat.log l R + 1 := ⟨_, rfl⟩
  have hRk : R ≤ l ^ k := by
    rw [hk]
    exact (Nat.lt_pow_succ_log_self hl R).le
  have hA : InPow 1 ((g - 1) ^ l ^ k) := by
    have h0 := unipPow l X R g hG hU
    have hsplit : (g - 1) ^ l ^ k = (g - 1) ^ (l ^ k - R) * (g - 1) ^ R := by
      rw [← pow_add, Nat.sub_add_cancel hRk]
    intro x
    obtain ⟨y, hy⟩ := h0 x
    refine ⟨((g - 1) ^ (l ^ k - R)) y, ?_⟩
    rw [hsplit, Module.End.mul_apply, hy, map_smul]
  have hB : InPow 2 (g ^ l ^ (k + 1) - 1) := by
    have h := (powIn l X (g ^ l ^ k)).2 ((frob l X g k).1 hA)
    rwa [← pow_mul, ← pow_succ] at h
  have hC : ∀ n, k + 1 ≤ n → InPow 2 (g ^ l ^ n - 1) := by
    intro n hn
    have h := (powIn l X (g ^ l ^ (k + 1))).1 2 (l ^ (n - (k + 1))) hB
    rwa [← pow_mul, ← pow_add, Nat.add_sub_cancel' hn] at h
  have hstep : ∀ n, k + 1 ≤ n → cokLen (g ^ l ^ (n + 1) - 1) ≤ cokLen (g ^ l ^ n - 1) + R := by
    intro n hn
    have h := step l X R (g ^ l ^ n) hG (hC n hn)
    rwa [← pow_mul, ← pow_succ] at h
  have main : ∀ d, cokLen (g ^ l ^ (jZero l R + d) - 1) ≤
      cokLen (g ^ l ^ jZero l R - 1) + ((R * d : ℕ) : ℕ∞) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      calc cokLen (g ^ l ^ (jZero l R + (d + 1)) - 1) = cokLen (g ^ l ^ (jZero l R + d + 1) - 1) := rfl
        _ ≤ cokLen (g ^ l ^ (jZero l R + d) - 1) + R := hstep _ (by simp only [jZero]; omega)
        _ ≤ cokLen (g ^ l ^ jZero l R - 1) + ((R * d : ℕ) : ℕ∞) + R := add_le_add_left ih _
        _ = cokLen (g ^ l ^ jZero l R - 1) + ((R * (d + 1) : ℕ) : ℕ∞) := by
            push_cast
            ring
  rcases le_total m (jZero l R) with hm | hm
  · rw [Nat.sub_eq_zero_of_le hm, mul_zero, Nat.cast_zero, add_zero]
    exact mono l X g _ _ (pow_dvd_pow l hm)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [Nat.add_sub_cancel_left]
    exact main d
end
end
