module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.IsChain
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ChainB
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Algebra.Module.Torsion.Basic

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ChainA

section

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

theorem sigma_fin_eq_iff {ι : Type} {l : ι → ℕ} {b a : ι} {j : Fin (l b)} {i : Fin (l a)} :
    (⟨b, j⟩ : Σ a, Fin (l a)) = ⟨a, i⟩ ↔ b = a ∧ (j : ℕ) = i := by
  constructor
  · intro h
    cases h
    simp
  · rintro ⟨rfl, h⟩
    rw [Fin.ext h]

theorem chain_repr_N {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (z : W) (a : ι) (i : Fin (l a)) :
    B.repr (N z) ⟨a, i⟩ = if h : 0 < (i : ℕ) then B.repr z ⟨a, ⟨i - 1, by omega⟩⟩ else 0 := by
  classical
  have key : (B.coord ⟨a, i⟩).comp N =
      if h : 0 < (i : ℕ) then B.coord ⟨a, ⟨i - 1, by omega⟩⟩ else 0 := by
    apply B.ext
    rintro ⟨b, j⟩
    rw [LinearMap.comp_apply, hB]
    by_cases hi : 0 < (i : ℕ)
    · rw [dite_eq_left hi]
      by_cases hj : (j : ℕ) + 1 < l b
      · rw [dite_eq_left hj, Module.Basis.coord_apply, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
          Module.Basis.repr_self_apply]
        have hiff : ((⟨b, ⟨j + 1, hj⟩⟩ : Σ a, Fin (l a)) = ⟨a, i⟩) ↔
            ((⟨b, j⟩ : Σ a, Fin (l a)) = ⟨a, ⟨i - 1, by omega⟩⟩) := by
          rw [sigma_fin_eq_iff, sigma_fin_eq_iff]
          constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by simp only at h2 ⊢; omega⟩
        exact if_congr hiff rfl rfl
      · rw [dite_eq_right hj, map_zero, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg]
        intro h
        rw [sigma_fin_eq_iff] at h
        obtain ⟨rfl, h2⟩ := h
        simp only at h2
        have := i.2
        omega
    · rw [dite_eq_right hi]
      split_ifs with hj
      · rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg, LinearMap.zero_apply]
        intro h
        rw [sigma_fin_eq_iff] at h
        obtain ⟨rfl, h2⟩ := h
        simp only at h2
        omega
      · simp
  have := LinearMap.congr_fun key z
  rw [LinearMap.comp_apply, Module.Basis.coord_apply] at this
  rw [this]
  split_ifs <;> simp

theorem chain_repr_Npow {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (m : ℕ) (z : W) (a : ι) (i : Fin (l a)) :
    B.repr ((N ^ m) z) ⟨a, i⟩ = if h : m ≤ (i : ℕ) then B.repr z ⟨a, ⟨i - m, by omega⟩⟩ else 0 := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    by_cases h1 : m + 1 ≤ (i : ℕ)
    · rw [dite_eq_left (by omega), dite_eq_left h1, chain_repr_N hB, dite_eq_left (by simp; omega)]
      congr 2
    · rw [dite_eq_right h1]
      split_ifs with h2
      · rw [chain_repr_N hB, dite_eq_right]
        simp
        omega
      · rfl

theorem chain_repr_of_ker {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (m : ℕ) (z : W) (hz : (N ^ m) z = 0) (a : ι) (i : Fin (l a))
    (hi : (i : ℕ) + m < l a) : B.repr z ⟨a, i⟩ = 0 := by
  have h := chain_repr_Npow hB m z a ⟨i + m, hi⟩
  rw [hz, map_zero, dite_eq_left (by simp)] at h
  rw [Finsupp.zero_apply] at h
  rw [h]
  congr 2
  ext
  simp

theorem chain_Npow_zero {N : W →ₗ[E] W} {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (b : ι) (hb : 0 < l b) (j : ℕ) :
    (N ^ j) (B ⟨b, ⟨0, hb⟩⟩) = if h : j < l b then B ⟨b, ⟨j, h⟩⟩ else 0 := by
  induction j with
  | zero => simp [hb]
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    by_cases hj : j < l b
    · rw [dite_eq_left hj, hB]
    · rw [dite_eq_right hj, map_zero, dite_eq_right (by omega)]

theorem repr_centralizer_eq_zero (N : W →ₗ[E] W) {ι : Type} [Fintype ι] (l : ι → ℕ)
    (B : Module.Basis (Σ a, Fin (l a)) E W) (hB : IsChain N l B) (s : ι → ℕ) (_hs : ∀ a, s a ≤ l a)
    (hC : ∀ a b, s a ≤ s b + (l a - l b)) (v : W) (hv : v = ∑ a, if h : s a < l a then B ⟨a, ⟨s a, h⟩⟩ else 0)
    (A : W →ₗ[E] W) (hA : A ∘ₗ N = N ∘ₗ A) (a : ι) (i : Fin (l a)) (hi : (i : ℕ) < s a) :
    B.repr (A v) ⟨a, i⟩ = 0 := by
  have hc : Commute A N := hA

  rw [hv, map_sum, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : s b < l b
  · rw [dite_eq_left hb]
    have hlb : 0 < l b := by omega
    have h1 : B ⟨b, ⟨s b, hb⟩⟩ = (N ^ s b) (B ⟨b, ⟨0, hlb⟩⟩) := by
      rw [chain_Npow_zero hB b hlb, dite_eq_left hb]
    have hcomm : ∀ m : ℕ, ∀ x, A ((N ^ m) x) = (N ^ m) (A x) := fun m x =>
      LinearMap.congr_fun (hc.pow_right m).eq x
    rw [h1, hcomm, chain_repr_Npow hB]
    split_ifs with h2
    · refine chain_repr_of_ker hB (l b) _ ?_ a _ ?_
      · rw [← hcomm, chain_Npow_zero hB b hlb, dite_eq_right (lt_irrefl _), map_zero]
      · have := hC a b
        show (i : ℕ) - s b + l b < l a
        omega
    · rfl
  · rw [dite_eq_right hb, map_zero, map_zero, Finsupp.zero_apply]

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.Normal

section

@[expose] public section

noncomputable section

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

theorem exists_normal [FiniteDimensional E W] (N : W →ₗ[E] W) (hN : IsNilpotent N) (v : W) :
    ∃ (ι : Type) (_ : Fintype ι) (l s : ι → ℕ) (B : Module.Basis (Σ a, Fin (l a)) E W), IsChain N l B ∧
      (∀ a, 0 < l a) ∧ (∀ a, s a ≤ l a) ∧ v = ∑ a, (if h : s a < l a then B ⟨a, ⟨s a, h⟩⟩ else 0) ∧
      ∀ A : W →ₗ[E] W, A ∘ₗ N = N ∘ₗ A → ∀ (a : ι) (i : Fin (l a)), (i : ℕ) < s a → B.repr (A v) ⟨a, i⟩ = 0 := by
  obtain ⟨ι, _, l, s, B, hB, hl, hs, hC, hv⟩ := exists_good N hN v
  exact ⟨ι, inferInstance, l, s, B, hB, hl, hs, hv, fun A hA a i hi =>
    repr_centralizer_eq_zero N l B hB s hs hC v hv A hA a i hi⟩

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.DexBlockFrame

section

@[expose] public section

noncomputable section

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open Module

variable {k : Type} [Field k] {R : Type} [CommRing R] [Algebra k R]

theorem dex_block_frame (I : Ideal R) [I.IsMaximal] {L : Type} [Fintype L] (b : Basis L k (R ⧸ I))
    {W : Type} [AddCommGroup W] [Module R W] [Module k W] [IsScalarTower k R W] [FiniteDimensional k W]
    (hW : ∀ z ∈ I, ∀ y : W, z • y = 0) (N : W →ₗ[R] W) (hN : IsNilpotent N) (v : W) :
    ∃ (ι : Type) (_ : Fintype ι) (l s : ι → ℕ) (β : Basis (L × Σ a : ι, Fin (l a)) k W),
      (∀ a, 0 < l a) ∧ (∀ a, s a ≤ l a) ∧
      (∀ (z : R) (p : L) (j : Σ a : ι, Fin (l a)),
        z • β (p, j) = ∑ q, (b.repr (Ideal.Quotient.mk I z * b p) q) • β (q, j)) ∧
      (∀ (p : L) (a : ι) (i : Fin (l a)), N (β (p, ⟨a, i⟩)) =
        if h : (i : ℕ) + 1 < l a then β (p, ⟨a, ⟨i + 1, h⟩⟩) else 0) ∧
      v = ∑ p, ∑ a, (if h : s a < l a then b.repr 1 p • β (p, ⟨a, ⟨s a, h⟩⟩) else 0) ∧
      ∀ A : W →ₗ[R] W, A ∘ₗ N = N ∘ₗ A → ∀ (p : L) (a : ι) (i : Fin (l a)), (i : ℕ) < s a →
        β.repr (A v) (p, ⟨a, i⟩) = 0 := by
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  have hT : Module.IsTorsionBySet R W I := fun y z => hW z z.2 y
  letI : Module (R ⧸ I) W := hT.module
  have hmk : ∀ (z : R) (y : W), (Ideal.Quotient.mk I z) • y = z • y := fun z y => rfl
  haveI : IsScalarTower k (R ⧸ I) W := ⟨fun c e y => by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective e
    have : c • Ideal.Quotient.mk I z = Ideal.Quotient.mk I (c • z) := (map_smul (Ideal.Quotient.mkₐ k I) c z).symm
    rw [this, hmk, hmk, smul_assoc]⟩
  haveI : FiniteDimensional (R ⧸ I) W := Module.Finite.of_restrictScalars_finite k (R ⧸ I) W
  let toE : (W →ₗ[R] W) → (W →ₗ[R ⧸ I] W) := fun f =>
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c y => by
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective c
        simp only [RingHom.id_apply, hmk]
        exact f.map_smul z y }
  have htoE : ∀ f y, toE f y = f y := fun f y => rfl
  have hNE : IsNilpotent (toE N) := by
    obtain ⟨m, hm⟩ := hN
    refine ⟨m, LinearMap.ext fun y => ?_⟩
    have : ((toE N) ^ m) y = (N ^ m) y := by
      rw [Module.End.pow_apply, Module.End.pow_apply]
      rfl
    rw [this, hm]
    rfl
  obtain ⟨ι, _, l, s, B, hB, hl, hs, hv, hA⟩ := exists_normal (toE N) hNE v
  refine ⟨ι, inferInstance, l, s, b.smulTower B, hl, hs, ?_, ?_, ?_, ?_⟩
  · intro z p j
    rw [Basis.smulTower_apply]
    calc z • (b p • B j) = (Ideal.Quotient.mk I z) • (b p • B j) := rfl
      _ = (Ideal.Quotient.mk I z * b p) • B j := by rw [smul_smul]
      _ = (∑ q, b.repr (Ideal.Quotient.mk I z * b p) q • b q) • B j := by rw [b.sum_repr]
      _ = ∑ q, (b.repr (Ideal.Quotient.mk I z * b p) q) • (b.smulTower B) (q, j) := by
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Basis.smulTower_apply, smul_assoc]
  · intro p a i
    rw [Basis.smulTower_apply]
    have h1 : N (b p • B ⟨a, i⟩) = b p • (toE N) (B ⟨a, i⟩) := (toE N).map_smul (b p) (B ⟨a, i⟩)
    rw [h1, hB a i]
    split_ifs with h
    · rw [Basis.smulTower_apply]
    · rw [smul_zero]
  · rw [Finset.sum_comm]
    conv_lhs => rw [hv]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : s a < l a
    · simp only [h, dif_pos, Basis.smulTower_apply]
      calc B ⟨a, ⟨s a, h⟩⟩ = (1 : R ⧸ I) • B ⟨a, ⟨s a, h⟩⟩ := (one_smul _ _).symm
        _ = (∑ p, b.repr 1 p • b p) • B ⟨a, ⟨s a, h⟩⟩ := by rw [b.sum_repr]
        _ = ∑ p, b.repr 1 p • (b p • B ⟨a, ⟨s a, h⟩⟩) := by
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [smul_assoc]
    · simp only [h, dif_neg, not_false_eq_true, Finset.sum_const_zero]
  · intro A hAN p a i hi
    have hc : toE A ∘ₗ toE N = toE N ∘ₗ toE A := by
      refine LinearMap.ext fun y => ?_
      exact LinearMap.congr_fun hAN y
    rw [Basis.smulTower_repr]
    have := hA (toE A) hc a i hi
    rw [htoE] at this
    rw [this, map_zero, Finsupp.zero_apply]

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end
end
