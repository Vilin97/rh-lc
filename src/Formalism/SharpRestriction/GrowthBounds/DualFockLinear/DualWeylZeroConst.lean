module

public import Formalism.GradedWeylDivisibility.StatementD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetLemmas
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4
public import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.DvdOfAdd
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgeLatticeAdaptedBasis
import Formalism.LocalToGlobal.GroupLattices.FockModels.ElementaryDivisorBasis
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ScaleNegMono
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ScaleZpowMono
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgeLatticeMulOfWeightSum

-- Source module: Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FilterOfSupported

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

section Slice

variable {K : Type} [Field K] {S τ : Type} [DecidableEq S] (A : Finset S)

def slice (γ : MvPolynomial (S × τ) K →ₗ[K] K) : MvPolynomial (S × τ) K →ₗ[K] MvPolynomial (S × τ) K :=
  (MvPolynomial.basisMonomials (S × τ) K).constr K
    (fun e => γ (monomial (e.filter fun v : S × τ => v.1 ∉ A) 1) • monomial (e.filter fun v : S × τ => v.1 ∈ A) 1)

theorem slice_monomial (γ : MvPolynomial (S × τ) K →ₗ[K] K) (e : S × τ →₀ ℕ) (a : K) :
    slice A γ (monomial e a) =
      (a * γ (monomial (e.filter fun v : S × τ => v.1 ∉ A) 1)) • monomial (e.filter fun v : S × τ => v.1 ∈ A) 1 := by
  have h : (monomial e a : MvPolynomial (S × τ) K) = a • MvPolynomial.basisMonomials (S × τ) K e := by
    simp only [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul]
  simp only [slice, Module.Basis.constr_basis, smul_smul]

theorem filter_of_supported {P : MvPolynomial (S × τ) K} {q : S × τ → Prop} [DecidablePred q]
    (hP : P ∈ supported K {v | q v}) {e : S × τ →₀ ℕ} (he : e ∈ P.support) :
    e.filter q = e ∧ e.filter (fun v => ¬ q v) = 0 := by
  rw [mem_supported] at hP
  have key : ∀ v, e v ≠ 0 → q v := fun v hv =>
    hP (Finset.mem_coe.2 ((mem_vars_iff_mem_support v).2 ⟨e, he, Finsupp.mem_support_iff.2 hv⟩))
  refine ⟨(Finsupp.filter_eq_self_iff _ _).2 key, (Finsupp.filter_eq_zero_iff _ _).2 fun v hv => ?_⟩
  by_contra h
  exact hv (key v h)

theorem slice_mul_left (γ : MvPolynomial (S × τ) K →ₗ[K] K) (P R : MvPolynomial (S × τ) K)
    (hP : P ∈ supported K {v : S × τ | v.1 ∈ A}) : slice A γ (P * R) = P * slice A γ R := by
  induction R using MvPolynomial.induction_on' with
  | monomial f b =>
    conv_lhs => rw [P.as_sum]
    conv_rhs => rw [P.as_sum]

    rw [Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have h := filter_of_supported (q := fun v : S × τ => v.1 ∈ A) hP he
    beta_reduce at h
    rw [monomial_mul_monomial, slice_monomial, slice_monomial, Finsupp.filter_add, Finsupp.filter_add, h.1, h.2,
      zero_add, mul_smul_comm, monomial_mul_monomial, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul]
    congr 1
    ring
  | add p q hp hq => rw [mul_add, map_add (f := _), hp, hq, map_add (f := _), mul_add]

theorem slice_spec (γ : MvPolynomial (S × τ) K →ₗ[K] K) (Q : MvPolynomial (S × τ) K)
    (hQ : Q ∈ supported K {v : S × τ | v.1 ∉ A}) : slice A γ Q = γ Q • 1 := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]

  rw [map_sum, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun e he => ?_
  have h := filter_of_supported (q := fun v : S × τ => v.1 ∉ A) hQ he
  beta_reduce at h
  have h2 : e.filter (fun v : S × τ => v.1 ∈ A) = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    intro v hv
    exact (Finsupp.filter_eq_zero_iff _ _).1 h.2 v (not_not.2 hv)
  have h3 : (monomial e (AddMonoidAlgebra.coeff Q e) : MvPolynomial (S × τ) K) = AddMonoidAlgebra.coeff Q e • monomial e 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [slice_monomial, h.1, h2, ← C_apply, C_1, h3, map_smul, smul_eq_mul]

theorem slice_mul (γ : MvPolynomial (S × τ) K →ₗ[K] K) (P Q : MvPolynomial (S × τ) K)
    (hP : P ∈ supported K {v : S × τ | v.1 ∈ A}) (hQ : Q ∈ supported K {v : S × τ | v.1 ∉ A}) :
    slice A γ (P * Q) = γ Q • P := by
  rw [slice_mul_left A γ P Q hP, slice_spec A γ Q hQ, mul_smul_comm, mul_one]

end Slice

section Tensor

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {S : Type} [Fintype S] [DecidableEq S] {k n : ℕ}

theorem blockEmb_supported (s : S) (F : MvPolynomial (Fin k × Fin n) K) (q : S → Prop) (hs : q s) :
    blockEmb K s F ∈ supported K {v : S × (Fin k × Fin n) | q v.1} := by
  rw [mem_supported]
  intro v hv
  have hv' := vars_rename (fun w : Fin k × Fin n => (s, w)) F (Finset.mem_coe.1 hv)
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hv'
  exact hs

theorem prod_split (A : Finset S) (F : S → MvPolynomial (Fin k × Fin n) K) :
    ∏ s, blockEmb K s (F s) =
      (∏ s, blockEmb K s (if s ∈ A then F s else 1)) * ∏ s, blockEmb K s (if s ∈ A then 1 else F s) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  split_ifs <;> simp

theorem slice_tensor (A : Finset S) (M MT Msp : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (h1 : ∀ s ∈ A, M s ≤ MT s ∧ (1 : MvPolynomial (Fin k × Fin n) K) ∈ Msp s)
    (h2 : ∀ s, s ∉ A → (1 : MvPolynomial (Fin k × Fin n) K) ∈ MT s ∧ M s ≤ Msp s)
    (γ : MvPolynomial (S × (Fin k × Fin n)) K →ₗ[K] K) (c : K)
    (hγ : ∀ Q ∈ tensorLat R K Msp, ∃ a : R, γ Q = c * algebraMap R K a) :
    ∀ u ∈ tensorLat R K M, ∃ y ∈ tensorLat R K MT, slice A γ u = c • y := by
  intro u hu
  unfold tensorLat at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    have hXs : (∏ s, blockEmb K s (if s ∈ A then F s else 1)) ∈
        supported K {v : S × (Fin k × Fin n) | v.1 ∈ A} := by
      refine Subalgebra.prod_mem _ fun s _ => ?_
      split_ifs with h
      · exact blockEmb_supported s _ (· ∈ A) h
      · rw [map_one]; exact one_mem _
    have hYs : (∏ s, blockEmb K s (if s ∈ A then 1 else F s)) ∈
        supported K {v : S × (Fin k × Fin n) | v.1 ∉ A} := by
      refine Subalgebra.prod_mem _ fun s _ => ?_
      split_ifs with h
      · rw [map_one]; exact one_mem _
      · exact blockEmb_supported s _ (· ∉ A) h
    have hYm : (∏ s, blockEmb K s (if s ∈ A then 1 else F s)) ∈ tensorLat R K Msp := by
      unfold tensorLat
      refine Submodule.subset_span ⟨_, fun s => ?_, rfl⟩
      split_ifs with h
      · exact (h1 s h).2
      · exact (h2 s h).2 (hF s)
    obtain ⟨a, ha⟩ := hγ _ hYm
    refine ⟨a • ∏ s, blockEmb K s (if s ∈ A then F s else 1), Submodule.smul_mem _ a ?_, ?_⟩
    · unfold tensorLat
      refine Submodule.subset_span ⟨_, fun s => ?_, rfl⟩
      split_ifs with h
      · exact (h1 s h).1 (hF s)
      · exact (h2 s h).1
    · rw [prod_split A F, slice_mul A γ _ _ hXs hYs, ha, mul_smul, algebraMap_smul]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ea⟩ := hx
    obtain ⟨b, hb, eb⟩ := hy
    exact ⟨a + b, add_mem ha hb, by rw [map_add (f := _), ea, eb, smul_add]⟩
  | smul r x _ hx =>
    obtain ⟨a, ha, ea⟩ := hx
    exact ⟨r • a, Submodule.smul_mem _ r ha, by rw [LinearMap.map_smul_of_tower, ea, smul_comm]⟩

end Tensor

end Formalism.MainNotions.TestSideCounting
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneMemH0WeightZero

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.MainNotions.G.LatticeSystems (kp_lamAt_antitone H0_le_twisted_nabla)

structure Peel {n' m : ℕ} (A : Finset (Fin n')) (X XT sp : Fin n' → Fin (m + 1) → ℤ) : Prop where
  top : ∀ s ∈ A, XT s = X s ∧ sp s = 0
  off : ∀ s, s ∉ A → XT s = 0 ∧ sp s = X s

theorem lamAt_congr {n' m : ℕ} {X Y : Fin n' → Fin (m + 1) → ℤ} {s : Fin n'} (h : X s = Y s) : lamAt X s = lamAt Y s := by
  unfold lamAt
  rw [h]

theorem lamAt_zero {n' m : ℕ} {X : Fin n' → Fin (m + 1) → ℤ} {s : Fin n'} (h : X s = 0) : lamAt X s = 0 := by
  unfold lamAt
  rw [h]
  split_ifs
  · rfl
  · funext i
    simp

theorem nuOf_zero (m : ℕ) : nuOf (0 : Fin (m + 1) → ℤ) = 0 := by
  funext t
  simp [nuOf]

theorem anti_zero (m : ℕ) : Antitone (0 : Fin (m + 1) → ℤ) := fun _ _ _ => le_rfl

theorem one_mem_H0_weight_zero (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (Λ : Submodule O (Fin (m + 1) → Kf)) :
    (1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) ∈ H0 O m 0 Λ := by
  unfold H0
  rw [if_pos (anti_zero m)]
  simp only [Submodule.mem_iInf]
  rintro g ⟨hg, -⟩
  rw [nablaLTwMem O Kf m 0 g hg]
  refine ⟨1, ?_, ?_⟩
  · have : (fun t : Fin (m + 1) => (((0 : Fin (m + 1) → ℤ) t) - (0 : Fin (m + 1) → ℤ) (Fin.last m)).toNat) = 0 := by
      funext t
      simp
    rw [this]
    exact one_mem_dualWeyl
  · simp

section

variable {Kf : Type} [Field Kf] {n' m : ℕ} {A : Finset (Fin n')} {X XT sp : Fin n' → Fin (m + 1) → ℤ}

theorem slice_V (hP : Peel A X XT sp)
    (γ : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₗ[Kf] Kf) :
    ∀ u ∈ Vsp Kf X, slice A γ u ∈ Vsp Kf XT := by
  intro u hu
  obtain ⟨y, hy, he⟩ := slice_tensor (R := Kf) A
    (fun s => if Antitone (lamAt X s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt X s)) else ⊥)
    (fun s => if Antitone (lamAt XT s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt XT s)) else ⊥)
    (fun s => if Antitone (lamAt sp s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt sp s)) else ⊥)
    (fun s hs => ⟨by rw [lamAt_congr (hP.top s hs).1], by
      rw [lamAt_zero (hP.top s hs).2, if_pos (anti_zero m), nuOf_zero]; exact one_mem_dualWeyl⟩)
    (fun s hs => ⟨by rw [lamAt_zero (hP.off s hs).1, if_pos (anti_zero m), nuOf_zero]; exact one_mem_dualWeyl, by
      rw [lamAt_congr (hP.off s hs).2]⟩)
    γ 1 (fun Q _ => ⟨γ Q, by simp⟩) u hu
  rw [he, one_smul]
  exact hy

variable {O : Type} [CommRing O] [Algebra O Kf]

theorem slice_Hten (hP : Peel A X XT sp) (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf))
    (γ : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₗ[Kf] Kf) (c : Kf)
    (hγ : ∀ Q ∈ Hten O sp Λ, ∃ a : O, γ Q = c * algebraMap O Kf a) :
    ∀ u ∈ Hten O X Λ, ∃ y ∈ Hten O XT Λ, slice A γ u = c • y :=
  slice_tensor (R := O) A _ _ _
    (fun s hs => ⟨by rw [lamAt_congr (hP.top s hs).1], by
      rw [lamAt_zero (hP.top s hs).2]; exact one_mem_H0_weight_zero O Kf m _⟩)
    (fun s hs => ⟨by rw [lamAt_zero (hP.off s hs).1]; exact one_mem_H0_weight_zero O Kf m _, by
      rw [lamAt_congr (hP.off s hs).2]⟩)
    γ c hγ

theorem Hten_le_V (hd : IsDominant X) (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf))
    (hΛ : ∀ s, ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧ Λ s = colSpan O g) :
    ∀ Q ∈ Hten O X Λ, Q ∈ Vsp Kf X := by
  intro Q hQ
  choose g hg hΛg using hΛ
  have h1 : Q ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (lamAt X s) (g s)) := by
    refine Submodule.span_mono ?_ hQ
    rintro _ ⟨F, hF, rfl⟩
    refine ⟨F, fun s => ?_, rfl⟩
    have h0 : F s ∈ H0 O m (lamAt X s) (Λ s) := hF s
    rw [hΛg s] at h0
    exact H0_le_twisted_nabla m _ (kp_lamAt_antitone X hd s) (g s) (hg s) h0
  have h2 := tr_tens_le O Kf m (fun s => lamAt X s) g hg Q h1
  unfold Vsp
  have : (fun s => if Antitone (lamAt X s) then dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt X s)) else ⊥) =
      fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt X s)) := by
    funext s
    rw [if_pos (kp_lamAt_antitone X hd s)]
  rw [this]
  exact h2

end

end Formalism.MainNotions.TestSideCounting
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.DualFockLinear.DualWeylZeroConst

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.MainNotions.G.LatticeSystems (lb_D lb_D_det)

section Ext

variable {Kf : Type} [Field Kf] {n' m : ℕ} {A : Finset (Fin n')} {X XT sp : Fin n' → Fin (m + 1) → ℤ}

theorem exists_ext (G : Module.Dual Kf (Vsp Kf X)) :
    ∃ γ : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₗ[Kf] Kf, ∀ Q : Vsp Kf X, γ (Q : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = G Q := by
  obtain ⟨γ, hγ⟩ := LinearMap.exists_extend G
  exact ⟨γ, fun Q => by rw [← hγ]; rfl⟩

def extD (G : Module.Dual Kf (Vsp Kf X)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₗ[Kf] Kf := (exists_ext G).choose

theorem extD_spec (G : Module.Dual Kf (Vsp Kf X)) (Q : Vsp Kf X) : extD G (Q : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = G Q :=
  (exists_ext G).choose_spec Q

def peelMap (hP : Peel A X XT sp) (c : Kf) (G : Module.Dual Kf (Vsp Kf sp)) : Vsp Kf X →ₗ[Kf] Vsp Kf XT :=
  (c • slice A (extD G)).restrict (fun u hu => Submodule.smul_mem _ _ (slice_V hP _ u hu))

theorem peelMap_coe (hP : Peel A X XT sp) (c : Kf) (G : Module.Dual Kf (Vsp Kf sp)) (u : Vsp Kf X) :
    ((peelMap hP c G u : Vsp Kf XT) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = c • slice A (extD G) (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := rfl

variable {O : Type} [CommRing O] [Algebra O Kf]

theorem peel_Hten (hP : Peel A X XT sp) (hdT : IsDominant XT) (hdsp : IsDominant sp)
    (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf))
    (hΛ : ∀ s, ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧ Λ s = colSpan O g)
    (c0 c : Kf) (G : Module.Dual Kf (Vsp Kf sp))
    (hG : ∀ Qv : Vsp Kf sp, (Qv : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O sp Λ → ∃ a : O, G Qv = c * algebraMap O Kf a)
    (u : Vsp Kf X) (hu : (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O X Λ) :
    ∃ yv : Vsp Kf XT, (yv : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O XT Λ ∧ peelMap hP c0 G u = (c0 * c) • yv := by
  obtain ⟨y, hy, he⟩ := slice_Hten hP Λ (extD G) c (fun Q hQ => by
      obtain ⟨a, ha⟩ := hG ⟨Q, Hten_le_V hdsp Λ hΛ Q hQ⟩ hQ
      exact ⟨a, by rw [← ha]; exact extD_spec G ⟨Q, _⟩⟩) u hu
  refine ⟨⟨y, Hten_le_V hdT Λ hΛ y hy⟩, hy, Subtype.ext ?_⟩
  rw [peelMap_coe, he, smul_smul]
  rfl

end Ext

section Lat

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem Re'_le_scale (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (X : Fin n' → Fin (m + 1) → ℤ)
    (hd : IsDominant X) (e : Edge W Qq (m + 1)) (he : IsEdge p n' r e) (M : ℕ) (hM : ordMax r X ≤ M) :
    Re' p ι σ w r X e ≤ scale (algebraMap O Kf w ^ (-(M : ℤ))) (dualLat O Kf (HL (O := O) ι σ X e.tgt)) := by
  obtain ⟨I, hI, x, π, _, c2, _, c4, c4', _, c7⟩ := edge_lattice_adapted_basis h m r X hd e he
  have hw := w_ne_zero h
  have hp0 : (p : Kf) ≠ 0 := by rw [Formalism.L2.G.Model.p_eq h]; exact pow_ne_zero _ hw
  rw [← c7, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine mem_scale.2 ⟨w ^ ((M : ℤ) - order r X (π i)).toNat • (((p : Kf) ^ π i)⁻¹ • x.coord i), ?_, ?_⟩
  · rw [← c2, Formalism.L2.G.Model.dualLat_span x (fun i => (p : Kf) ^ π i) (fun i => zpow_ne_zero _ hp0)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · have h1 := c4' i
    rw [← algebraMap_smul Kf (w ^ ((M : ℤ) - order r X (π i)).toNat), smul_smul, smul_smul, map_pow, ← zpow_natCast,
      Int.toNat_of_nonneg (by omega), ← zpow_add₀ hw]
    show _ = ((algebraMap O Kf) w ^ (-order r X (π i)) * (p : Kf) ^ (-π i)) • x.coord i
    rw [zpow_neg (p : Kf)]
    congr 3
    ring

variable {m : ℕ} {A : Finset (Fin n')} {X XT sp : Fin n' → Fin (m + 1) → ℤ}

theorem p_zpow (h : HidaSetting p n' W Qq O Kf ι σ j w) (z : ℤ) : (p : Kf) ^ z = algebraMap O Kf w ^ (2 * z) := by
  rw [Formalism.L2.G.Model.p_eq h, ← zpow_natCast, ← zpow_mul]
  norm_num

theorem peel_Re (h : HidaSetting p n' W Qq O Kf ι σ j w) (hP : Peel A X XT sp) (hX : X = XT + sp) (hdT : IsDominant XT)
    (hdsp : IsDominant sp) (r : ℕ) (e' : Edge W Qq (m + 1)) (he' : IsEdge p n' r e') (N : ℤ)
    (G : Module.Dual Kf (Vsp Kf sp))
    (hG : ∀ Q ∈ Re p ι σ w r sp e', ∃ a : O, be p r sp Q G = algebraMap O Kf w ^ N * algebraMap O Kf a) :
    ∀ u ∈ Re p ι σ w r X e',
      peelMap hP ((p : Kf) ^ Ar r sp) G u ∈ scale (algebraMap O Kf w ^ N) (Re p ι σ w r XT e') := by
  intro u hu
  have hw := w_ne_zero h
  have hAr : Ar r X = Ar r XT + Ar r sp := by rw [hX]; exact Ar_add r _ _
  obtain ⟨gs, hgs, _, h2, _⟩ := Formalism.L2.G.Model.edgeLat h m r e' he'
  have hΛ : ∀ s : Fin n', ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧
      LeAt p ι σ w s.val e' = colSpan O g := fun s =>
    ⟨_, by rw [Matrix.det_mul]; exact (hgs _).mul (lb_D_det _ _ _ hw), h2 s.val⟩
  obtain ⟨u0, hu0, rfl⟩ := mem_scale.1 hu
  have hu0' : ((u0 : Vsp Kf X) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O X (fun s => LeAt p ι σ w s.val e') := hu0
  obtain ⟨yv, hy, he⟩ := peel_Hten hP hdT hdsp (fun s => LeAt p ι σ w s.val e') hΛ ((p : Kf) ^ Ar r sp)
    (algebraMap O Kf w ^ (N - Ar r sp)) G (by
      intro Qv hQv
      obtain ⟨a, ha⟩ := hG (algebraMap O Kf w ^ (-Ar r sp) • Qv) (mem_scale.2 ⟨Qv, hQv, rfl⟩)
      refine ⟨a, ?_⟩
      rw [be_smulK_left] at ha
      unfold be at ha
      rw [map_smul, smul_eq_mul, p_zpow h, ← mul_assoc, ← zpow_add₀ hw] at ha
      have e1 : -Ar r sp + 2 * Ar r sp = Ar r sp := by ring
      rw [e1] at ha
      rw [zpow_sub₀ hw, div_mul_eq_mul_div, eq_div_iff (zpow_ne_zero _ hw), mul_comm]
      exact ha) u0 hu0'
  rw [map_smul, he]
  refine mem_scale.2 ⟨algebraMap O Kf w ^ (-Ar r XT) • yv, mem_scale.2 ⟨yv, hy, rfl⟩, ?_⟩
  rw [smul_smul, smul_smul, p_zpow h, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, hAr]
  congr 2
  ring

theorem peel_HL (hP : Peel A X XT sp) (hdT : IsDominant XT) (hdsp : IsDominant sp)
    (L : Submodule W (Fin (m + 1) → Qq))
    (hL : ∀ s : Fin n', ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧ extO O ι σ s.val L = colSpan O g)
    (c0 c : Kf) (G : Module.Dual Kf (Vsp Kf sp))
    (hG : ∀ Q ∈ HL (O := O) ι σ sp L, ∃ a : O, G Q = c * algebraMap O Kf a) :
    ∀ u ∈ HL (O := O) ι σ X L, peelMap hP c0 G u ∈ scale (c0 * c) (HL (O := O) ι σ XT L) := by
  intro u hu
  obtain ⟨yv, hy, he⟩ := peel_Hten hP hdT hdsp (fun s => extO O ι σ s.val L) hL c0 c G (fun Qv hQv => hG Qv hQv) u hu
  exact mem_scale.2 ⟨yv, hy, he.symm⟩

end Lat

theorem dualWeyl_zero_const {R : Type} [CommRing R] {r n : ℕ} (F : MvPolynomial (Fin r × Fin n) R)
    (hF : F ∈ dualWeyl R r n 0) : F = C (AddMonoidAlgebra.coeff F 0) := by
  classical
  have h1 : IsWeightedHomogeneous (colW r n) F 0 := (mem_dualWeyl_iff.1 hF).1
  ext e
  rw [coeff_C]
  split_ifs with he
  · rw [he]
  · apply h1.coeff_eq_zero
    intro hwt
    apply he
    symm
    ext v
    have h2 := congrFun hwt v.2
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at h2
    by_contra hv
    have h3 := (Finset.sum_eq_zero_iff.1 h2) v (Finsupp.mem_support_iff.2 (by simpa using hv))
    simp [colW] at h3
    exact hv (by simpa using h3)

end Formalism.MainNotions.TestSideCounting
end
end
end
