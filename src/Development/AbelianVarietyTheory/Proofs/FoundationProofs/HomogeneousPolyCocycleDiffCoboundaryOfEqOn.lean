module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsScalarGamma1CapGamma0ModLevelStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoVarPolySubstMatrixBasicLawsStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocycleIsCoboundaryOfNegCentralElement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem cocycle_isCoboundary_of_neg_central : ∀ (G : Type) [Group G] (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (ρ : G → V →ₗ[R] V), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → IsUnit (2 : R) → ∀ (S : Submodule R V), (∀ g, ∀ v ∈ S, ρ g v ∈ S) → ∀ (Δ : Subgroup G), Δ.Normal → (∀ δ ∈ Δ, ∀ v, ρ δ v = v) → ∀ c : G, (∀ v ∈ S, ρ c v = -v) → (∀ g, c * g * c⁻¹ * g⁻¹ ∈ Δ) → ∀ z : G → V, (∀ g, z g ∈ S) → (∀ g h, z (g * h) = ρ h (z g) + z h) → (∀ δ ∈ Δ, z δ = 0) → ∃ p ∈ S, ∀ g, z g = ρ g p - p := by
  intro G _ R _ V _ _ ρ hmul hone h2 S hS Δ hΔ hΔρ c hc hcomm z hzS hz hzΔ
  obtain ⟨u, hu⟩ := h2
  refine ⟨-((↑u⁻¹ : R) • z c), S.neg_mem (S.smul_mem _ (hzS c)), fun g => ?_⟩
  have key : ρ g (z c) + z g = -z g + z c := by
    have e1 : z (c * g) = z (g * c) := by
      have : c * g = (c * g * c⁻¹ * g⁻¹) * (g * c) := by group
      rw [this, hz, hzΔ _ (hcomm g), map_zero, zero_add]
    rw [hz, hz, hc _ (hzS g)] at e1
    exact e1
  have h2z : (2 : R) • z g = z c - ρ g (z c) := by
    rw [two_smul, ← sub_eq_zero]
    calc z g + z g - (z c - ρ g (z c)) = (ρ g (z c) + z g) - (-z g + z c) := by abel
      _ = 0 := sub_eq_zero.mpr key
  calc z g = ((↑u⁻¹ : R) * 2) • z g := by rw [← hu, Units.inv_mul, one_smul]
    _ = ρ g (-((↑u⁻¹ : R) • z c)) - -((↑u⁻¹ : R) • z c) := by
      rw [mul_smul, h2z, map_neg, map_smul, smul_sub]; abel

end GlobalTheory.KZ.H3
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocycleIsCoboundaryOfNegCentralElementStatement

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.cocycle_isCoboundary_of_neg_central_element : ∀ (G : Type) [Group G] (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (ρ : G → V →ₗ[R] V), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → IsUnit (2 : R) → ∀ (S : Submodule R V), (∀ g, ∀ v ∈ S, ρ g v ∈ S) → ∀ (Δ : Subgroup G), Δ.Normal → (∀ δ ∈ Δ, ∀ v, ρ δ v = v) → ∀ c : G, (∀ v ∈ S, ρ c v = -v) → (∀ g, c * g * c⁻¹ * g⁻¹ ∈ Δ) → ∀ z : G → V, (∀ g, z g ∈ S) → (∀ g h, z (g * h) = ρ h (z g) + z h) → (∀ δ ∈ Δ, z δ = 0) → ∃ p ∈ S, ∀ g, z g = ρ g p - p := by
  first | exact @GlobalTheory.KZ.H3.cocycle_isCoboundary_of_neg_central | exact GlobalTheory.KZ.H3.cocycle_isCoboundary_of_neg_central | (intros; apply GlobalTheory.KZ.H3.cocycle_isCoboundary_of_neg_central <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomogeneousPolyCocycleDiffCoboundaryOfEqOn

section

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

private theorem ent_gamma {K d : ℕ} (hd : d ∣ K) {δ : SL(2, ℤ)} (h : δ ∈ CongruenceSubgroup.Gamma K)
    (i j : Fin 2) :
    (((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod d) = (((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod d) := by
  rw [CongruenceSubgroup.Gamma_mem] at h
  obtain ⟨h00, h01, h10, h11⟩ := h
  have key : ∀ x : ℤ, ∀ y : ZMod K, (x : ZMod K) = y → (x : ZMod d) = ZMod.castHom hd (ZMod d) y := by
    intro x y hxy; rw [← hxy, map_intCast]
  fin_cases i <;> fin_cases j
  · have := key _ _ h00; rw [map_one] at this; simpa using this
  · simpa using key _ _ h01
  · simpa using key _ _ h10
  · have := key _ _ h11; rw [map_one] at this; simpa using this

private theorem gamma_le {K d : ℕ} (hd : d ∣ K) {δ : SL(2, ℤ)} (h : δ ∈ CongruenceSubgroup.Gamma K) :
    δ ∈ CongruenceSubgroup.Gamma d := by
  rw [CongruenceSubgroup.Gamma_mem]
  have e := ent_gamma hd h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using e 0 0
  · simpa using e 0 1
  · simpa using e 1 0
  · simpa using e 1 1

theorem adj_of_near : ∀ (N l w n : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → Odd w →
    ∀ z z' : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)), IsCoc w (Gam N l) z → IsCoc w (Gam N l) z' →
    Near z z' → ∃ p : MvPolynomial (Fin 2) (ZMod (l ^ n)), p.IsHomogeneous w ∧
      ∀ γ ∈ Gam N l, z γ - z' γ = slP (γ : Matrix (Fin 2) (Fin 2) ℤ) p - p := by
  intro N l w n hN hl hl2 hlN hw z z' hz hz' hnear
  obtain ⟨M', hM', hM'eq⟩ := hnear
  obtain ⟨e, M, hlM, hMe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM'.ne' l hl.one_lt.ne'
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp at hMe; omega
    · exact h
  set a := max e n
  obtain ⟨c, hcG, hcomm, hcmod⟩ := GlobalTheory.T.exists_scalar_gamma1CapGamma0_mod_level N l a M hN hl hl2 hlN hM hlM
  obtain ⟨L1, L2, L3, -, -, L6, L7⟩ := GlobalTheory.T.twoVarPolySubstMatrix_basic_laws (ZMod (l ^ n))
  let R := ZMod (l ^ n)
  let V := MvPolynomial (Fin 2) R
  let G := ↥(Gam N l)
  let ρ : G → V →ₗ[R] V := fun g => (slP ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).toLinearMap
  let S : Submodule R V := MvPolynomial.homogeneousSubmodule (Fin 2) R w
  let K := M * N * l ^ a
  let Δ : Subgroup G := (CongruenceSubgroup.Gamma K).subgroupOf (Gam N l)
  have hρmul : ∀ g h v, ρ (g * h) v = ρ h (ρ g v) := by
    intro g h v
    simp only [ρ, AlgHom.toLinearMap_apply, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact L1 _ _ v
  have hρone : ∀ v, ρ 1 v = v := by
    intro v
    simp only [ρ, AlgHom.toLinearMap_apply, OneMemClass.coe_one, Matrix.SpecialLinearGroup.coe_one]
    exact L2 v
  have h2 : IsUnit (2 : R) := by
    have hc : Nat.Coprime 2 (l ^ n) :=
      Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hl2))
    exact_mod_cast (ZMod.isUnit_iff_coprime 2 (l ^ n)).mpr hc
  have hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S := by
    intro g v hv
    exact L3 _ w v hv
  have hΔn : Δ.Normal := by
    haveI := CongruenceSubgroup.Gamma_normal (M * N * l ^ a)
    exact Subgroup.normal_subgroupOf
  have hM'K : M' ∣ K := by
    rw [hMe]
    have := mul_dvd_mul (pow_dvd_pow l (le_max_left e n)) (dvd_mul_right M N)
    simpa [K, mul_comm, mul_assoc, mul_left_comm] using this
  have hnK : l ^ n ∣ K := Dvd.dvd.mul_left (pow_dvd_pow l (le_max_right e n)) _
  have hΔ : ∀ δ ∈ Δ, ∀ v, ρ δ v = v := by
    intro δ hδ v
    rw [Subgroup.mem_subgroupOf] at hδ
    simp only [ρ, AlgHom.toLinearMap_apply]
    rw [L6 _ 1 v (ent_gamma hnK hδ), L2 v]
  let c' : G := ⟨c, hcG⟩
  have hc1 : ∀ v ∈ S, ρ c' v = -v := by
    intro v hv
    simp only [ρ, AlgHom.toLinearMap_apply, c']
    have hent : ∀ i j, (((c : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : R) = (((-1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : R) := by
      intro i j
      have h1 := congrArg (ZMod.castHom (pow_dvd_pow l (le_max_right e n)) R) (hcmod i j)
      rw [map_intCast] at h1
      rw [h1]
      by_cases hij : i = j
      · subst hij; rw [if_pos rfl, map_neg, map_one]; simp [Matrix.neg_apply]
      · simp [hij, Matrix.neg_apply, Matrix.one_apply]
    rw [L6 _ _ v hent, L7 w v hv, hw.neg_one_pow, neg_one_smul]
  have hc2 : ∀ g, c' * g * c'⁻¹ * g⁻¹ ∈ Δ := by
    intro g
    rw [Subgroup.mem_subgroupOf]
    exact hcomm g
  let zz : G → V := fun g => z g - z' g
  have hzS : ∀ g, zz g ∈ S := by
    intro g
    exact (hz.1 g g.2).sub (hz'.1 g g.2)
  have hzc : ∀ g h, zz (g * h) = ρ h (zz g) + zz h := by
    intro g h
    have hgh : ((g * h : G) : SL(2, ℤ)) = (g : SL(2, ℤ)) * h := rfl
    simp only [zz, ρ, AlgHom.toLinearMap_apply, map_sub]
    rw [hgh, hz.2 g g.2 h h.2, hz'.2 g g.2 h h.2]
    abel
  have hzΔ : ∀ δ ∈ Δ, zz δ = 0 := by
    intro δ hδ
    rw [Subgroup.mem_subgroupOf] at hδ
    simp only [zz]
    rw [hM'eq _ (gamma_le hM'K hδ), sub_self]
  obtain ⟨p, hpS, hp⟩ := GlobalTheory.T.cocycle_isCoboundary_of_neg_central_element G R V ρ hρmul hρone h2 S hS Δ hΔn hΔ c' hc1 hc2 zz hzS hzc hzΔ
  refine ⟨p, hpS, fun γ hγ => ?_⟩
  exact hp ⟨γ, hγ⟩

end GlobalTheory.KZ.H3
end
end
