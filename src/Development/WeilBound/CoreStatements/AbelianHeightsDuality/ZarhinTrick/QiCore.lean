module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCoreDefs
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCharP
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module

-- Source module: Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCartier

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

variable {K H : Type} [Field K] [CommRing H] [Algebra K H]

theorem qc_stable [FiniteDimensional K H] (I : Ideal H) : ∃ k : ℕ, ∀ j, k ≤ j → I ^ j = I ^ k := by
  haveI : IsArtinianRing H := IsArtinianRing.of_finite K H
  let f : ℕ →o (Ideal H)ᵒᵈ := ⟨fun n => OrderDual.toDual (I ^ n), fun _ _ hab => Ideal.pow_le_pow_right hab⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes f
  exact ⟨n, fun j hj => congrArg OrderDual.ofDual (hn j hj).symm⟩

theorem qc_functional (ε : H →ₐ[K] K) {x : H} (hx : x ∈ RingHom.ker ε) (hx2 : x ∉ RingHom.ker ε ^ 2) :
    ∃ l : H →ₗ[K] K, l 1 = 0 ∧ (∀ y ∈ RingHom.ker ε ^ 2, l y = 0) ∧ l x = 1 := by
  let W : Submodule K H := Submodule.span K {(1 : H)} ⊔ (RingHom.ker ε ^ 2).restrictScalars K
  have hxW : x ∉ W := by
    intro h
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hz2 : z ∈ RingHom.ker ε ^ 2 := hz
    have hz' : z ∈ RingHom.ker ε := Ideal.pow_le_self two_ne_zero hz2
    have hc : c = 0 := by
      have h1 : ε x = 0 := hx
      have h2 : ε z = 0 := hz'
      rw [← hyz, map_add (f := _), map_smul, map_one, h2] at h1
      simpa using h1
    subst hc
    apply hx2
    rw [← hyz, zero_smul, zero_add]
    exact hz2
  obtain ⟨f, hf, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxW inferInstance
  have hW : ∀ w ∈ W, f w = 0 := fun w hw => by
    have : f w ∈ W.map f := Submodule.mem_map_of_mem hw
    rw [hfW] at this
    simpa using this
  refine ⟨(f x)⁻¹ • f, ?_, ?_, ?_⟩
  · simp [hW 1 (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))]
  · intro y hy
    simp [hW y (Submodule.mem_sup_right hy)]
  · simp [hf]

theorem qc_leib (ε : H →ₐ[K] K) (l : H →ₗ[K] K) (h1 : l 1 = 0) (h2 : ∀ y ∈ RingHom.ker ε ^ 2, l y = 0)
    (a b : H) : l (a * b) = ε a * l b + l a * ε b := by
  have ha : a - algebraMap K H (ε a) ∈ RingHom.ker ε := by simp [RingHom.mem_ker]
  have hb : b - algebraMap K H (ε b) ∈ RingHom.ker ε := by simp [RingHom.mem_ker]
  have hab : l ((a - algebraMap K H (ε a)) * (b - algebraMap K H (ε b))) = 0 :=
    h2 _ (by rw [pow_two]; exact Ideal.mul_mem_mul ha hb)
  have e : a * b = (a - algebraMap K H (ε a)) * (b - algebraMap K H (ε b)) + ε a • b + ε b • a -
      (ε a * ε b) • (1 : H) := by
    simp only [Algebra.smul_def, map_mul, mul_one]
    ring
  rw [e, map_sub, map_add (f := _), map_add (f := _), hab, map_smul, map_smul, map_smul, h1]
  simp only [smul_eq_mul, mul_zero, sub_zero, zero_add]
  ring

theorem aug_le_sq {K H : Type} [Field K] [CharZero K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) (hL : CounitL Δ ε) (hR : CounitR Δ ε) :
    RingHom.ker ε ≤ RingHom.ker ε ^ 2 := by
  classical
  intro x hx
  by_contra hx2
  obtain ⟨l, hl1, hl2, hlx⟩ := qc_functional ε hx hx2
  let Φ : H ⊗[K] H →ₗ[K] H := (TensorProduct.rid K H).toLinearMap ∘ₗ LinearMap.lTensor H l
  let mR : H ⊗[K] H →ₐ[K] H :=
    (Algebra.TensorProduct.lmul' K).comp (Algebra.TensorProduct.map (AlgHom.id K H) ((Algebra.ofId K H).comp ε))
  let mL : H ⊗[K] H →ₐ[K] H :=
    (Algebra.TensorProduct.lmul' K).comp (Algebra.TensorProduct.map ((Algebra.ofId K H).comp ε) (AlgHom.id K H))
  have hΦ : ∀ s t : H ⊗[K] H, Φ (s * t) = mR s * Φ t + Φ s * mR t := by
    intro s t
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a₁ a₂ =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b₁ b₂ =>
        simp only [Φ, mR, Algebra.TensorProduct.tmul_mul_tmul, LinearMap.comp_apply, LinearMap.lTensor_tmul,
          LinearEquiv.coe_coe, TensorProduct.rid_tmul, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
          AlgHom.coe_id, id_eq, Algebra.TensorProduct.lmul'_apply_tmul, Algebra.ofId_apply,
          qc_leib ε l hl1 hl2, Algebra.smul_def, map_add, map_mul]
        ring
      | add t₁ t₂ h₁ h₂ => simp only [mul_add, map_add (f := _), h₁, h₂]; ring
    | add s₁ s₂ h₁ h₂ => simp only [add_mul, map_add (f := _), h₁, h₂]; ring
  have hεΦ : ∀ t : H ⊗[K] H, ε (Φ t) = l (mL t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [Φ, mL, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
        AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        Algebra.TensorProduct.lmul'_apply_tmul, Algebra.ofId_apply, map_smul, smul_eq_mul]
      rw [← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    | add s t h₁ h₂ => simp only [map_add (f := _), h₁, h₂]
  have hRa : ∀ a, mR (Δ a) = a := fun a => DFunLike.congr_fun hR a
  have hLa : ∀ a, mL (Δ a) = a := fun a => DFunLike.congr_fun hL a
  let D : H →ₗ[K] H := Φ ∘ₗ Δ.toLinearMap
  have hD : ∀ a b, D (a * b) = a * D b + D a * b := by
    intro a b
    simp only [D, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, hΦ, hRa]
  have hεD : ∀ a, ε (D a) = l a := by
    intro a
    simp only [D, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hεΦ, hLa]
  have hDpow : ∀ n : ℕ, D (x ^ (n + 1)) = ((n : H) + 1) * x ^ n * D x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, hD, ih]
      push_cast
      ring
  obtain ⟨k, hk⟩ := qc_stable (K := K) (RingHom.ker ε)
  have hJJ : RingHom.ker ε ^ (k + 2) * RingHom.ker ε ^ (k + 2) = RingHom.ker ε ^ (k + 2) := by
    rw [← pow_add, hk (k + 2 + (k + 2)) (by omega), hk (k + 2) (by omega)]
  have hDJ : ∀ y ∈ RingHom.ker ε ^ (k + 2), D y ∈ RingHom.ker ε ^ (k + 2) := by
    intro y hy
    rw [← hJJ] at hy
    refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [hD]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb)
    · rw [map_add (f := _)]
      exact Ideal.add_mem _ ha hb
  have hJ2 : RingHom.ker ε ^ (k + 2) ≤ RingHom.ker ε ^ 2 := Ideal.pow_le_pow_right (by omega)
  have hJ1 : RingHom.ker ε ^ (k + 2) ≤ RingHom.ker ε := Ideal.pow_le_self (by omega)
  have hex : ∃ n, x ^ n ∈ RingHom.ker ε ^ (k + 2) := ⟨k + 2, Ideal.pow_mem_pow hx _⟩
  have hN : x ^ Nat.find hex ∈ RingHom.ker ε ^ (k + 2) := Nat.find_spec hex
  have hmin : ∀ m < Nat.find hex, x ^ m ∉ RingHom.ker ε ^ (k + 2) := fun m hm => Nat.find_min hex hm
  have hN0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hN
    have : ε 1 = 0 := hJ1 hN
    simp at this
  have hN1 : Nat.find hex ≠ 1 := by
    intro h1
    rw [h1, pow_one] at hN
    exact hx2 (hJ2 hN)
  obtain ⟨M, hM⟩ : ∃ M, Nat.find hex = M + 2 := ⟨Nat.find hex - 2, by omega⟩
  have h1 : D (x ^ (M + 2)) ∈ RingHom.ker ε ^ (k + 2) := hDJ _ (hM ▸ hN)
  rw [hDpow (M + 1)] at h1
  let π := Ideal.Quotient.mk (RingHom.ker ε ^ (k + 2))
  have hu1 : IsUnit (π ((((M + 1 : ℕ) : H)) + 1)) := by
    have e : π ((((M + 1 : ℕ) : H)) + 1) = algebraMap K (H ⧸ RingHom.ker ε ^ (k + 2)) ((M + 2 : ℕ) : K) := by
      simp only [map_add (f := _), map_natCast, map_one]
      push_cast
      ring
    rw [e]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (by omega))).map _
  have hu2 : IsUnit (π (D x)) := by
    have hm : D x - 1 ∈ RingHom.ker ε := by
      change ε (D x - 1) = 0
      rw [map_sub, hεD, hlx, map_one, sub_self]
    have hnil : IsNilpotent (π (D x - 1)) :=
      ⟨k + 2, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hm _⟩
    have := hnil.isUnit_one_add
    rwa [map_sub, map_one, add_sub_cancel] at this
  have h0 : π ((((M + 1 : ℕ) : H) + 1) * x ^ (M + 1) * D x) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h1
  rw [map_mul, map_mul, hu2.mul_left_eq_zero, hu1.mul_right_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h0
  exact hmin (M + 1) (by omega) h0

end PositivityTheory.PrwZar.Qi
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiIdem

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

theorem idem_eq_zero {K H : Type} [Field K] [IsAlgClosed K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    {f : H} (hf : IsIdempotentElem f) (h : ∀ x : H →ₐ[K] K, x f = 0) : f = 0 := by
  by_contra hne
  have hne1 : Ideal.span {1 - f} ≠ ⊤ := by
    intro htop
    rw [Ideal.span_singleton_eq_top] at htop
    apply hne
    have h0 : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hf.eq, sub_self]
    exact htop.mul_left_eq_zero.1 h0
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne1
  letI := Ideal.Quotient.field M
  haveI : Module.Finite K (H ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K M).toLinearMap (Ideal.Quotient.mkₐ_surjective K M)
  haveI : Algebra.IsIntegral K (H ⧸ M) := Algebra.IsIntegral.of_finite K (H ⧸ M)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := H ⧸ M)
  let e : K ≃ₐ[K] H ⧸ M := AlgEquiv.ofBijective (Algebra.ofId K (H ⧸ M)) hb
  let x : H →ₐ[K] K := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K M)
  have h1 : Ideal.Quotient.mk M f = 1 := by
    have hmem : 1 - f ∈ M := hle (Ideal.mem_span_singleton_self _)
    have h2 : Ideal.Quotient.mk M (1 - f) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rw [map_sub, map_one, sub_eq_zero] at h2
    exact h2.symm
  have hx1 : x f = 1 := by
    change e.symm (Ideal.Quotient.mkₐ K M f) = 1
    rw [Ideal.Quotient.mkₐ_eq_mk, h1, map_one]
  have hx := h x
  rw [hx1] at hx
  exact one_ne_zero hx

end PositivityTheory.PrwZar.Qi
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiStab

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

theorem exists_stable_pow {K H : Type} [Field K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    (I : Ideal H) : ∃ (k : ℕ) (e : H), IsIdempotentElem e ∧ I ^ k = Ideal.span {e} ∧ ∀ j, k ≤ j → I ^ j = I ^ k := by
  haveI : IsArtinianRing H := isArtinian_of_tower K inferInstance
  haveI : IsNoetherianRing H := isNoetherian_of_tower K inferInstance
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := H) (M := H)
    ⟨fun n => OrderDual.toDual (I ^ n), fun a b h => Ideal.pow_le_pow_right h⟩
  have hst : ∀ j, n ≤ j → I ^ j = I ^ n := fun j hj => congrArg OrderDual.ofDual (hn j hj).symm
  have hidem : IsIdempotentElem (I ^ n) := by
    unfold IsIdempotentElem
    rw [← pow_add]
    exact hst (n + n) (by omega)
  obtain ⟨e, he, hI⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).1 hidem
  exact ⟨n, e, he, hI.trans Ideal.submodule_span_eq, hst⟩

end PositivityTheory.PrwZar.Qi
end
end
end

-- Source module: Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCore

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

theorem killedCore : KilledCore := by
  intro K H _ _ _ _ _ Δ ε hL hR hmul hpts
  obtain ⟨m, hm, hpt⟩ := hpts
  set I : Ideal H := RingHom.ker ε with hI
  obtain ⟨k, e, he, hIk, hstab⟩ := exists_stable_pow (K := K) I

  have hk1 : I ^ (k + 1) = Ideal.span {e} := by rw [hstab (k + 1) (Nat.le_succ k), hIk]
  have heI : e ∈ I := by
    have : e ∈ I ^ (k + 1) := by rw [hk1]; exact Ideal.subset_span rfl
    exact Ideal.pow_le_self (Nat.succ_ne_zero k) this

  have hs : ∃ s : ℕ, 0 < s ∧ ∀ x ∈ I, pw Δ ε s x ∈ I ^ k := by
    obtain ⟨p, hp⟩ := CharP.exists K
    rcases CharP.char_is_prime_or_zero K p with hpp | hp0
    · have : Fact p.Prime := ⟨hpp⟩
      refine ⟨p ^ k, pow_pos hpp.pos k, fun x hx => ?_⟩
      exact Ideal.pow_le_pow_right (Nat.lt_two_pow_self).le (pw_charP p Δ ε hL hR hmul k hx)
    · subst hp0
      have : CharZero K := CharP.charP_to_charZero K
      have h1 : pw Δ ε 1 = AlgHom.id K H := hL
      have hle : ∀ j : ℕ, I ≤ I ^ (j + 1) := by
        intro j
        induction j with
        | zero => rw [zero_add, pow_one]
        | succ j ih =>
          calc I ≤ I ^ 2 := aug_le_sq Δ ε hL hR
            _ = I * I := pow_two I
            _ ≤ I * I ^ (j + 1) := Ideal.mul_mono_right ih
            _ = I ^ (j + 1 + 1) := (pow_succ' I (j + 1)).symm
      refine ⟨1, one_pos, fun x hx => ?_⟩
      rw [h1]
      exact Ideal.pow_le_pow_right (Nat.le_succ k) (hle k hx)
  obtain ⟨s, hs0, hsI⟩ := hs

  have hme : pw Δ ε m e = 0 := by
    refine idem_eq_zero (K := K) (he.map (pw Δ ε m)) fun x => ?_
    have := congrArg (fun f : H →ₐ[K] K => f e) (hpt x)
    simp only [AlgHom.comp_apply] at this
    rw [this]
    exact heI
  refine ⟨m * s, Nat.mul_pos hm hs0, AlgHom.ext fun x => ?_⟩
  have hy : x - algebraMap K H (ε x) ∈ I := by
    change ε (x - algebraMap K H (ε x)) = 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (hIk ▸ hsI _ hy)
  have key : pw Δ ε (m * s) (x - algebraMap K H (ε x)) = 0 := by
    rw [hmul, AlgHom.comp_apply, ← ha, map_mul, hme, mul_zero]
  have h0 : pw Δ ε 0 (x - algebraMap K H (ε x)) = 0 := by
    change algebraMap K H (ε (x - algebraMap K H (ε x))) = 0
    rw [show ε (x - algebraMap K H (ε x)) = 0 from hy, map_zero]
  have e1 := congrArg (· + algebraMap K H (ε x)) key
  have e2 := congrArg (· + algebraMap K H (ε x)) h0
  simp only [map_sub, AlgHom.commutes, sub_add_cancel, zero_add] at e1 e2
  rw [e1, e2]

end PositivityTheory.PrwZar.Qi
end
end
end
