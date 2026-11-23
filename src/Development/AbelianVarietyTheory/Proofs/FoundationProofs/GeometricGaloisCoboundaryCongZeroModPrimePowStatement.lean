module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerParameterPowersOrthogonalGeometricInvariant

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQRootPolyOfFixedGeometricStabilizerTau

section

@[expose] public section

open GlobalTheory.K5

namespace GlobalTheory.K5.Span

theorem sum_range_shift_one {A : Type*} [AddCommGroup A] {M : ℕ} (f : ℕ → A)
    (hf : ∀ i, f (i + M) = f i) :
    ∑ i ∈ Finset.range M, f (i + 1) = ∑ i ∈ Finset.range M, f i := by
  have h1 := Finset.sum_range_succ' f M
  have h2 := Finset.sum_range_succ f M
  have h3 : f M = f 0 := by simpa using hf 0
  rw [h3] at h2
  exact add_right_cancel (h1.symm.trans h2)

theorem sum_range_shift {A : Type*} [AddCommGroup A] {M : ℕ} (f : ℕ → A)
    (hf : ∀ i, f (i + M) = f i) (s : ℕ) :
    ∑ i ∈ Finset.range M, f (i + s) = ∑ i ∈ Finset.range M, f i := by
  induction s generalizing f with
  | zero => simp
  | succ s ih =>
    have := sum_range_shift_one (fun i => f (i + s)) (fun i => by
      show f (i + M + s) = f (i + s)
      rw [add_right_comm, hf])
    rw [← ih f hf, ← this]
    exact Finset.sum_congr rfl fun i _ => by congr 1; omega

theorem span : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo (p := p) Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (z : Ω), (∀ g ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) ∧ z = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
  intro p _ Ω _ _ hΩ T τ hτ hτq N z hz
  haveI : CharZero Ω := charZero_of_injective_algebraMap hΩ.inj
  have hprim : IsPrimitiveRoot (T.ζ N) (p ^ N) := T.prim N
  have hMpos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
  have hq0 : T.qq N ≠ 0 := Basic.qq_ne_zero T N
  have hqpow : T.qq N ^ p ^ N = algebraMap (O0 p) Ω (qO p) := Basic.qq_pow T N
  have hτqN := hτq N
  set M := p ^ N with hMdef
  set ζ := T.ζ N with hζdef
  set q := T.qq N with hqdef
  have hM0 : (M : Ω) ≠ 0 := by exact_mod_cast hMpos.ne'
  have hζ0 : ζ ≠ 0 := hprim.ne_zero hMpos.ne'

  have hζalg : IsAlgZp (p := p) ζ := by
    refine ⟨Polynomial.X ^ M - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero hMpos 1, ?_⟩
    simp [hprim.pow_eq_one]
  have hfixζ : ∀ g ∈ Ggeo (p := p) Ω, g ζ = ζ := fun g hg => hg ζ hζalg
  have hτpow : ∀ i : ℕ, (τ ^ i) q = ζ ^ i * q := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hfixζ τ hτ, hτqN, pow_succ']
      ring
  have hτG : ∀ i : ℕ, τ ^ i ∈ Ggeo (p := p) Ω := fun i => Subgroup.pow_mem _ hτ i
  have hconj : ∀ g ∈ Ggeo (p := p) Ω, g q = q → ∀ i : ℕ, g ((τ ^ i) z) = (τ ^ i) z := by
    intro g hg hgq i
    have hk : (τ ^ i)⁻¹ * g * τ ^ i ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) q := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hτG i)) hg)
        (hτG i), MulAction.mem_stabilizer_iff.2 ?_⟩
      show ((τ ^ i)⁻¹ * g * τ ^ i) q = q
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτpow, map_mul, map_pow, hfixζ g hg, hgq, ← hτpow,
        AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    have hkz := hz _ hk
    have e : τ ^ i * ((τ ^ i)⁻¹ * g * τ ^ i) = g * τ ^ i := by group
    calc g ((τ ^ i) z) = (g * τ ^ i) z := rfl
      _ = (τ ^ i * ((τ ^ i)⁻¹ * g * τ ^ i)) z := by rw [e]
      _ = (τ ^ i) (((τ ^ i)⁻¹ * g * τ ^ i) z) := rfl
      _ = (τ ^ i) z := by rw [hkz]
  have hdec : ∀ g ∈ Ggeo (p := p) Ω, ∃ s : ℕ, g q = ζ ^ s * q ∧ ∀ i : ℕ, g ((τ ^ i) z) = (τ ^ (s + i)) z := by
    intro g hg
    have h1 : (g q / q) ^ M = 1 := by
      rw [div_pow, ← map_pow, hqpow, AlgEquiv.commutes, ← hqpow, div_self (pow_ne_zero _ hq0)]
    obtain ⟨s, -, hse⟩ := hprim.eq_pow_of_pow_eq_one h1
    have hgq : g q = ζ ^ s * q := by rw [hse, div_mul_cancel₀ _ hq0]
    refine ⟨s, hgq, fun i => ?_⟩
    have hh : (τ ^ s)⁻¹ * g ∈ Ggeo (p := p) Ω := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hτG s)) hg
    have hhq : ((τ ^ s)⁻¹ * g) q = q := by
      rw [AlgEquiv.mul_apply, hgq, ← hτpow, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    have e : g = τ ^ s * ((τ ^ s)⁻¹ * g) := by group
    rw [e, AlgEquiv.mul_apply, hconj _ hh hhq i, ← AlgEquiv.mul_apply, ← pow_add]

  have hτMz : (τ ^ M) z = z := by
    refine hz _ (Subgroup.mem_inf.2 ⟨hτG M, MulAction.mem_stabilizer_iff.2 ?_⟩)
    show (τ ^ M) q = q
    rw [hτpow, hprim.pow_eq_one, one_mul]
  set η := ζ⁻¹ with hηdef
  have hηprim : IsPrimitiveRoot η M := hprim.inv
  have hfixη : ∀ g ∈ Ggeo (p := p) Ω, g η = η := by
    intro g hg; rw [hηdef, map_inv₀, hfixζ g hg]
  obtain ⟨P, hP⟩ : ∃ P : ℕ → Ω, ∀ j,
      P j = (M : Ω)⁻¹ * ∑ i ∈ Finset.range M, η ^ (i * j) * (τ ^ i) z := ⟨_, fun _ => rfl⟩
  have hgP : ∀ g ∈ Ggeo (p := p) Ω, ∀ s : ℕ, (∀ i : ℕ, g ((τ ^ i) z) = (τ ^ (s + i)) z) →
      ∀ j, g (P j) = ζ ^ (s * j) * P j := by
    intro g hg s hs j

    rw [hP, map_mul, map_inv₀, map_natCast, map_sum]
    have hper : ∀ i, (fun i => η ^ (i * j) * (τ ^ i) z) (i + M) = (fun i => η ^ (i * j) * (τ ^ i) z) i := by
      intro i
      show η ^ ((i + M) * j) * (τ ^ (i + M)) z = η ^ (i * j) * (τ ^ i) z
      rw [add_mul, pow_add, show η ^ (M * j) = 1 by rw [pow_mul, hηprim.pow_eq_one, one_pow],
        mul_one, pow_add, AlgEquiv.mul_apply, hτMz]
    have hsh := sum_range_shift (M := M) (fun i => η ^ (i * j) * (τ ^ i) z) hper s
    rw [← hsh, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hfixη g hg, hs, add_comm s i]
    have hζη : ζ ^ (s * j) * η ^ (s * j) = 1 := by
      rw [← mul_pow, hηdef, mul_inv_cancel₀ hζ0, one_pow]
    calc (M : Ω)⁻¹ * (η ^ (i * j) * (τ ^ (i + s)) z)
        = (M : Ω)⁻¹ * ((ζ ^ (s * j) * η ^ (s * j)) * η ^ (i * j) * (τ ^ (i + s)) z) := by
          rw [hζη, one_mul]
      _ = ζ ^ (s * j) * ((M : Ω)⁻¹ * (η ^ ((i + s) * j) * (τ ^ (i + s)) z)) := by
          rw [add_mul, pow_add]; ring
  obtain ⟨c, hc⟩ : ∃ c : ℕ → Ω, ∀ j, c j = P j / q ^ j := ⟨_, fun _ => rfl⟩
  refine ⟨c, ?_, ?_⟩
  · intro j g hg
    obtain ⟨s, hgq, hs⟩ := hdec g hg
    rw [hc, map_div₀, map_pow, hgq, hgP g hg s hs j, mul_pow, ← pow_mul,
      mul_div_mul_left _ _ (pow_ne_zero _ hζ0)]
  · have hgeom : ∀ i ∈ Finset.range M,
        ∑ j ∈ Finset.range M, η ^ (i * j) = if i = 0 then (M : Ω) else 0 := by
      intro i hi
      split_ifs with h0
      · simp [h0]
      · have hne : η ^ i ≠ 1 :=
          hηprim.pow_ne_one_of_pos_of_lt h0 (Finset.mem_range.1 hi)
        simp_rw [pow_mul]
        rw [geom_sum_eq hne, pow_right_comm, hηprim.pow_eq_one, one_pow, sub_self, zero_div]
    have e1 : ∑ i ∈ Finset.range M, (∑ j ∈ Finset.range M, η ^ (i * j)) * (τ ^ i) z =
        ∑ i ∈ Finset.range M, (if i = 0 then (M : Ω) else 0) * (τ ^ i) z :=
      Finset.sum_congr rfl fun i hi => by rw [hgeom i hi]
    calc z = (M : Ω)⁻¹ * ∑ i ∈ Finset.range M, (∑ j ∈ Finset.range M, η ^ (i * j)) * (τ ^ i) z := by
          rw [e1, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hMpos) (fun b _ hb => by simp [hb])]
          simp [hM0]
      _ = ∑ j ∈ Finset.range M, P j := by
          simp only [hP]
          rw [← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_mul]
      _ = ∑ j ∈ Finset.range M, c j * q ^ j :=
          Finset.sum_congr rfl fun j _ => by rw [hc, div_mul_cancel₀ _ (pow_ne_zero j hq0)]

end GlobalTheory.K5.Span
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQRootPolyOfFixedGeometricStabilizerTauStatement

section

@[expose] public section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer_tau : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo (p := p) Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (z : Ω), (∀ g ∈ Ggeo (p := p) Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) ∧ z = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j :=
  GlobalTheory.K5.Span.span
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerParameterPowersOrthogonalGeometricInvariantStatement

section

@[expose] public section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.isIntegral_coeffs_of_geometricInvariant_towerParameter_expansion : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) →
  IsInt (p := p) (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) →
  ∀ j < p ^ N, IsInt (p := p) (c j) := by
  first | exact @GlobalTheory.K5.Orth.orth | exact GlobalTheory.K5.Orth.orth | (intros; apply GlobalTheory.K5.Orth.orth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricGaloisCoboundaryCongZeroModPrimePow

section

@[expose] public section

open GlobalTheory.K5

namespace GlobalTheory.K5.KernLoc

theorem kern_of (SPAN : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (z : Ω), (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) ∧ z = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) (ORTH : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) →
  IsInt (p := p) (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) → ∀ j < p ^ N, IsInt (p := p) (c j)) : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (k N : ℕ) (w o : Ω), IsInt (p := p) w → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) →
  (∀ g ∈ Ggeo p Ω, g o = o) → Cong (p := p) k (τ w - w) o → Cong (p := p) k o 0 := by
  intro p _ _ Ω _ _ hΩ T τ hτ hτq k N w o hw hwH ho hc
  haveI : CharZero Ω := charZero_of_injective_algebraMap hΩ.inj
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  have hζalg : IsAlgZp p (T.ζ N) := by
    refine ⟨Polynomial.X ^ (p ^ N) - 1, Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos N) 1, ?_⟩
    simp [(T.prim N).pow_eq_one]
  have hfixζ : ∀ g ∈ Ggeo p Ω, g (T.ζ N) = T.ζ N := fun g hg => hg (T.ζ N) hζalg
  have hτpow : ∀ i : ℕ, (τ ^ i) (T.qq N) = T.ζ N ^ i * T.qq N := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hτq, map_mul, ih, hfixζ _ (Subgroup.pow_mem _ hτ i)]
      ring
  have hτi : ∀ i : ℕ, τ ^ i ∈ Ggeo p Ω := fun i => Subgroup.pow_mem _ hτ i

  have hτN : (τ ^ (p ^ N)) w = w := by
    apply hwH
    refine ⟨hτi _, ?_⟩
    show (τ ^ (p ^ N)) (T.qq N) = T.qq N
    rw [hτpow, (T.prim N).pow_eq_one, one_mul]

  obtain ⟨z, hz, hze⟩ := hc
  have hzH : ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z := by
    intro g hg
    have hg1 : g ∈ Ggeo p Ω := hg.1
    have hg2 : g (T.qq N) = T.qq N := hg.2
    have hconj : τ⁻¹ * g * τ ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N) := by
      refine ⟨(Ggeo p Ω).mul_mem ((Ggeo p Ω).mul_mem ((Ggeo p Ω).inv_mem hτ) hg1) hτ, ?_⟩
      show (τ⁻¹ * g * τ) (T.qq N) = T.qq N
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτq, map_mul, hfixζ g hg1, hg2, ← hτq,
        ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have hgτw : g (τ w) = τ w := by
      have := hwH _ hconj
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at this
      have h2 := congrArg τ this
      rwa [← AlgEquiv.mul_apply τ τ⁻¹, mul_inv_cancel, AlgEquiv.one_apply] at h2
    have e := congrArg g hze
    rw [map_sub, map_sub, hgτw, hwH g hg, ho g hg1, map_mul, map_pow, map_natCast, hze] at e
    exact (mul_left_cancel₀ (pow_ne_zero k hp0) e).symm
  obtain ⟨c, hcfix, hzc⟩ := SPAN p Ω hΩ T τ hτ hτq N z hzH

  have hsumz : ∑ i ∈ Finset.range (p ^ N), (τ ^ i) z = (p : Ω) ^ N * c 0 := by
    have h1 : ∀ i j : ℕ, (τ ^ i) (c j * T.qq N ^ j) = c j * T.qq N ^ j * (T.ζ N ^ j) ^ i := by
      intro i j
      rw [map_mul, map_pow, hcfix j _ (hτi i), hτpow]
      ring
    rw [hzc]

    simp_rw [map_sum, h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_eq_single 0]
    · simp [mul_comm]
    · intro j hj hj0
      have hj' := Finset.mem_range.1 hj
      have hne : T.ζ N ^ j ≠ 1 := (T.prim N).pow_ne_one_of_pos_of_lt hj0 hj'
      rw [geom_sum_eq hne, ← pow_mul, mul_comm j, pow_mul, (T.prim N).pow_eq_one, one_pow, sub_self,
        zero_div, mul_zero]
    · intro h
      exact absurd (Finset.mem_range.2 (pow_pos (Fact.out : p.Prime).pos N)) h
  have hsumL : ∑ i ∈ Finset.range (p ^ N), (τ ^ i) (τ w - w - o) = -((p : Ω) ^ N * o) := by
    have h1 : ∀ i : ℕ, (τ ^ i) (τ w - w - o) = (τ ^ (i + 1)) w - (τ ^ i) w - o := by
      intro i
      rw [map_sub, map_sub, pow_succ, AlgEquiv.mul_apply, ho _ (hτi i)]
    simp_rw [h1]
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => (τ ^ i) w), hτN, pow_zero,
      AlgEquiv.one_apply, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have key : -((p : Ω) ^ N * o) = (p : Ω) ^ k * ((p : Ω) ^ N * c 0) := by
    rw [← hsumL, ← hsumz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hze, map_mul, map_pow, map_natCast]
  have hc0 : IsInt (p := p) (c 0) := ORTH p Ω hΩ T N c hcfix (hzc ▸ hz) 0 (pow_pos (Fact.out : p.Prime).pos N)
  refine ⟨-c 0, hc0.neg, ?_⟩
  have hpN : (p : Ω) ^ N ≠ 0 := pow_ne_zero N hp0
  apply mul_left_cancel₀ hpN
  linear_combination -key

theorem main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (k N : ℕ) (w o : Ω), IsInt (p := p) w → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) →
  (∀ g ∈ Ggeo p Ω, g o = o) → Cong (p := p) k (τ w - w) o → Cong (p := p) k o 0 :=
  kern_of GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer_tau GlobalTheory.T.isIntegral_coeffs_of_geometricInvariant_towerParameter_expansion

end GlobalTheory.K5.KernLoc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricGaloisCoboundaryCongZeroModPrimePowStatement

section

@[expose] public section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.geometricGalois_coboundary_cong_zero_modPrimePow : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (k N : ℕ) (w o : Ω), IsInt (p := p) w → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) →
  (∀ g ∈ Ggeo p Ω, g o = o) → Cong (p := p) k (τ w - w) o → Cong (p := p) k o 0 := by
  first | exact @GlobalTheory.K5.KernLoc.main | exact GlobalTheory.K5.KernLoc.main | (intros; apply GlobalTheory.K5.KernLoc.main <;> assumption)
end
end
