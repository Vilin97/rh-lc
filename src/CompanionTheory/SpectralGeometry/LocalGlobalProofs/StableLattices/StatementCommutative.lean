module

public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FinrankRangePowConvex
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.ReduceModChar
public import Mathlib.LinearAlgebra.Eigenspace.Basic

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommuteOfMemAdjoin

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.CommStep

open Module

theorem commute_of_mem_adjoin {V : Type} [AddCommGroup V] [Module ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (hc : ∀ i j, Commute (a i) (a j)) (i : Fin (l + 1))
    {y : Module.End ℂ V} (hy : y ∈ Algebra.adjoin ℂ (Set.range a)) : Commute y (a i) := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact hc j i
  | algebraMap r => exact Algebra.commutes r (a i)
  | add x y _ _ hx hy => exact hx.add_left hy
  | mul x y _ _ hx hy => exact hx.mul_left hy

theorem adjoin_le_sup {V : Type} [AddCommGroup V] [Module ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (hc : ∀ i j, Commute (a i) (a j)) :
    Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)) ⊔
        (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
          (LinearMap.mulRight ℂ (a 0)) := by
  have hBC : Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ) ≤
      Algebra.adjoin ℂ (Set.range a) :=
    Algebra.adjoin_mono (Set.range_subset_iff.2 fun k => ⟨k.succ, rfl⟩)
  have ha0 : a 0 ∈ Algebra.adjoin ℂ (Set.range a) := Algebra.subset_adjoin ⟨0, rfl⟩
  intro y hy
  rw [Subalgebra.mem_toSubmodule] at hy
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    induction j using Fin.cases with
    | zero =>
      refine Submodule.mem_sup_right (Submodule.mem_map.2 ⟨1, ?_, ?_⟩)
      · exact (Subalgebra.mem_toSubmodule _).2 (one_mem _)
      · rw [LinearMap.mulRight_apply, one_mul]
    | succ k => exact Submodule.mem_sup_left (Algebra.subset_adjoin ⟨k, rfl⟩)
  | algebraMap r => exact Submodule.mem_sup_left (Subalgebra.algebraMap_mem _ r)
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    obtain ⟨p₁, hp₁, z₁, hz₁, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨p₂, hp₂, z₂, hz₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨q₁, hq₁, rfl⟩ := Submodule.mem_map.1 hz₁
    obtain ⟨q₂, hq₂, rfl⟩ := Submodule.mem_map.1 hz₂
    rw [Subalgebra.mem_toSubmodule] at hp₁ hp₂ hq₁ hq₂
    rw [LinearMap.mulRight_apply, LinearMap.mulRight_apply]
    have hp₂c : Commute p₂ (a 0) := GlobalTheory.CompanionTheory.CommStep.commute_of_mem_adjoin a hc 0 (hBC hp₂)
    have hq₂c : Commute q₂ (a 0) := GlobalTheory.CompanionTheory.CommStep.commute_of_mem_adjoin a hc 0 hq₂
    have e₁ : q₁ * a 0 * p₂ = q₁ * p₂ * a 0 := by
      rw [mul_assoc, ← hp₂c.eq, ← mul_assoc]
    have e₂ : q₁ * a 0 * (q₂ * a 0) = q₁ * q₂ * a 0 * a 0 := by
      rw [← mul_assoc, mul_assoc q₁, ← hq₂c.eq, ← mul_assoc]
    have key : (p₁ + q₁ * a 0) * (p₂ + q₂ * a 0) =
        p₁ * p₂ + (p₁ * q₂ + q₁ * p₂ + q₁ * q₂ * a 0) * a 0 := by
      rw [add_mul, mul_add, mul_add, e₁, e₂]
      simp only [add_mul, mul_assoc, add_assoc]
    rw [key]
    refine Submodule.add_mem_sup ((Subalgebra.mem_toSubmodule _).2 (mul_mem hp₁ hp₂))
      (Submodule.mem_map.2 ⟨p₁ * q₂ + q₁ * p₂ + q₁ * q₂ * a 0, ?_, LinearMap.mulRight_apply _ _ _⟩)
    rw [Subalgebra.mem_toSubmodule]
    exact add_mem (add_mem (mul_mem (hBC hp₁) hq₂) (mul_mem hq₁ (hBC hp₂)))
      (mul_mem (mul_mem hq₁ hq₂) ha0)

theorem finrank_map_pow_le {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (hc : ∀ i j, Commute (a i) (a j)) (k : ℕ) :
    finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
        (LinearMap.mulRight ℂ (a 0 ^ k))) ≤
      finrank ℂ (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)) +
        finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
          (LinearMap.mulRight ℂ (a 0 ^ (k + 1)))) := by
  have h := Submodule.map_mono (f := LinearMap.mulRight ℂ (a 0 ^ k))
    (GlobalTheory.CompanionTheory.CommStep.adjoin_le_sup a hc)
  have hcomp : (LinearMap.mulRight ℂ (a 0 ^ k)).comp (LinearMap.mulRight ℂ (a 0)) =
      LinearMap.mulRight ℂ (a 0 ^ (k + 1)) :=
    LinearMap.ext fun b => by
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, pow_succ', mul_assoc]
  rw [Submodule.map_sup, ← Submodule.map_comp, hcomp] at h
  have h1 := Submodule.finrank_mono h
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ))).map
      (LinearMap.mulRight ℂ (a 0 ^ k)))
    ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
      (LinearMap.mulRight ℂ (a 0 ^ (k + 1))))
  have h3 := Submodule.finrank_map_le (LinearMap.mulRight ℂ (a 0 ^ k))
    (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)))
  rw [Subalgebra.finrank_toSubmodule] at h3
  omega

theorem comm_step : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (l : ℕ)
    (a : Fin (l + 1) → Module.End ℂ V), (∀ i j, Commute (a i) (a j)) → ∀ x : ℕ,
    Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
      x * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i : Fin l => a i.succ)) +
        Module.finrank ℂ ((Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range a))).map
          (LinearMap.mulRight ℂ (a 0 ^ x))) := by
  intro V _ _ _ l a hc x
  induction x with
  | zero =>
    have hid : LinearMap.mulRight ℂ (a 0 ^ 0) = LinearMap.id :=
      LinearMap.ext fun b => by simp
    rw [hid, Submodule.map_id, Nat.zero_mul, Nat.zero_add, Subalgebra.finrank_toSubmodule]
  | succ x ih =>
    have h := GlobalTheory.CompanionTheory.CommStep.finrank_map_pow_le a hc x
    rw [add_mul, one_mul]
    omega

end GlobalTheory.CompanionTheory.CommStep
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FinrankAdjoinLeAdd

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.CommSplit

open Module

variable {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def compr (W W' : Submodule ℂ V) (hc : IsCompl W W') :
    End ℂ V →ₗ[ℂ] End ℂ W where
  toFun b := (W.linearProjOfIsCompl W' hc) ∘ₗ b ∘ₗ W.subtype
  map_add' b c := by ext w; simp
  map_smul' t b := by ext w; simp

lemma compr_of_inv (W W' : Submodule ℂ V) (hc : IsCompl W W') (b : End ℂ V)
    (hb : ∀ w ∈ W, b w ∈ W) (w : W) : compr W W' hc b w = ⟨b w, hb w w.2⟩ := by
  show W.linearProjOfIsCompl W' hc (b w) = _
  exact Submodule.linearProjOfIsCompl_apply_left hc ⟨b w, hb w w.2⟩

lemma compr_eq_restrict (W W' : Submodule ℂ V) (hc : IsCompl W W') (b : End ℂ V)
    (hb : ∀ w ∈ W, b w ∈ W) : compr W W' hc b = b.restrict hb := by
  refine LinearMap.ext fun w => ?_
  rw [compr_of_inv W W' hc b hb w]
  rfl

lemma compr_mul (W W' : Submodule ℂ V) (hc : IsCompl W W') (b c : End ℂ V)
    (hcW : ∀ w ∈ W, c w ∈ W) :
    compr W W' hc (b * c) = compr W W' hc b * compr W W' hc c := by
  refine LinearMap.ext fun w => ?_
  rw [Module.End.mul_apply, compr_of_inv W W' hc c hcW w]
  rfl

lemma compr_algebraMap (W W' : Submodule ℂ V) (hc : IsCompl W W') (t : ℂ) :
    compr W W' hc (algebraMap ℂ (End ℂ V) t) = algebraMap ℂ (End ℂ W) t := by
  have hb : ∀ w ∈ W, algebraMap ℂ (End ℂ V) t w ∈ W := fun w hw => by
    rw [Module.algebraMap_end_apply]
    exact W.smul_mem t hw
  rw [compr_eq_restrict W W' hc _ hb]
  ext w
  simp [Module.algebraMap_end_apply]

lemma adjoin_compr {l : ℕ} (a : Fin l → End ℂ V) (W W' : Submodule ℂ V) (hc : IsCompl W W')
    (h : ∀ i, ∀ w ∈ W, a i w ∈ W) (b : End ℂ V) (hb : b ∈ Algebra.adjoin ℂ (Set.range a)) :
    (∀ w ∈ W, b w ∈ W) ∧ compr W W' hc b ∈
      Algebra.adjoin ℂ (Set.range fun i => ((a i).restrict (h i) : End ℂ W)) := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨h i, ?_⟩
    rw [compr_eq_restrict W W' hc _ (h i)]
    exact Algebra.subset_adjoin ⟨i, rfl⟩
  | algebraMap r =>
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [Module.algebraMap_end_apply]
      exact W.smul_mem r hw
    · rw [compr_algebraMap]
      exact Subalgebra.algebraMap_mem _ r
  | add x y _ _ hx hy =>
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [LinearMap.add_apply]
      exact W.add_mem (hx.1 w hw) (hy.1 w hw)
    · rw [map_add (f := _)]
      exact Subalgebra.add_mem _ hx.2 hy.2
  | mul x y _ _ hx hy =>
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [Module.End.mul_apply]
      exact hx.1 _ (hy.1 w hw)
    · rw [compr_mul W W' hc x y hy.1]
      exact Subalgebra.mul_mem _ hx.2 hy.2

theorem finrank_adjoin_le_add :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (l : ℕ)
      (a : Fin l → Module.End ℂ V) (W W' : Submodule ℂ V), IsCompl W W' →
      ∀ (h : ∀ i, ∀ w ∈ W, a i w ∈ W) (h' : ∀ i, ∀ w ∈ W', a i w ∈ W'),
      Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i =>
          ((a i).restrict (h i) : Module.End ℂ W))) +
        Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i =>
          ((a i).restrict (h' i) : Module.End ℂ W'))) := by
  intro V _ _ _ l a W W' hc h h'
  let AW := Algebra.adjoin ℂ (Set.range fun i => ((a i).restrict (h i) : Module.End ℂ W))
  let AW' := Algebra.adjoin ℂ (Set.range fun i => ((a i).restrict (h' i) : Module.End ℂ W'))
  let Φ : Algebra.adjoin ℂ (Set.range a) →ₗ[ℂ] AW × AW' :=
    { toFun := fun b => (⟨compr W W' hc b, (adjoin_compr a W W' hc h b b.2).2⟩,
        ⟨compr W' W hc.symm b, (adjoin_compr a W' W hc.symm h' b b.2).2⟩)
      map_add' := fun b c => by
        ext <;> simp [map_add (f := _)]
      map_smul' := fun t b => by
        ext <;> simp [map_smul] }
  have hinj : Function.Injective Φ := by
    intro b c hbc
    have h1 := congrArg (fun p => (p.1 : Module.End ℂ W)) hbc
    have h2 := congrArg (fun p => (p.2 : Module.End ℂ W')) hbc
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h1 h2
    apply Subtype.ext
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ W ⊔ W' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
    have e1 : (b : Module.End ℂ V) w = (c : Module.End ℂ V) w := by
      have e := LinearMap.congr_fun h1 ⟨w, hw⟩
      rw [compr_of_inv W W' hc _ (adjoin_compr a W W' hc h b b.2).1,
        compr_of_inv W W' hc _ (adjoin_compr a W W' hc h c c.2).1] at e
      exact congrArg Subtype.val e
    have e2 : (b : Module.End ℂ V) w' = (c : Module.End ℂ V) w' := by
      have e := LinearMap.congr_fun h2 ⟨w', hw'⟩
      rw [compr_of_inv W' W hc.symm _ (adjoin_compr a W' W hc.symm h' b b.2).1,
        compr_of_inv W' W hc.symm _ (adjoin_compr a W' W hc.symm h' c c.2).1] at e
      exact congrArg Subtype.val e
    rw [map_add (f := _), map_add (f := _), e1, e2]
  calc Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤ Module.finrank ℂ (AW × AW') :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = Module.finrank ℂ AW + Module.finrank ℂ AW' := Module.finrank_prod

end GlobalTheory.CompanionTheory.CommSplit
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StatementCommutative

section

@[expose] public section

open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.Bernstein

theorem arith_nil (N D D' E m K : ℕ) (hN : 0 < N)
    (h1 : D ≤ (2 * N - 1) * D' + E) (h2 : (2 * N - 1 + 1) * E ≤ m ^ 2)
    (h3 : 4 * N ^ 2 * D' ≤ m ^ 2 + K * m) : N * D ≤ m ^ 2 + K * m := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e2 : 2 * (k + 1) - 1 + 1 = 2 * (k + 1) := by omega
  rw [e1] at h1
  rw [e2] at h2
  have h4 : (2 * (k + 1)) * D ≤ (2 * (k + 1)) * ((2 * k + 1) * D') + m ^ 2 := by
    calc (2 * (k + 1)) * D ≤ (2 * (k + 1)) * ((2 * k + 1) * D' + E) :=
          Nat.mul_le_mul_left _ h1
      _ = (2 * (k + 1)) * ((2 * k + 1) * D') + (2 * (k + 1)) * E := by ring
      _ ≤ _ := Nat.add_le_add_left h2 _
  have h5 : (2 * (k + 1)) * ((2 * k + 1) * D') ≤ 4 * (k + 1) ^ 2 * D' := by
    have : (2 * (k + 1)) * ((2 * k + 1) * D') + 2 * (k + 1) * D' = 4 * (k + 1) ^ 2 * D' := by ring
    omega
  have h6 : (2 * (k + 1)) * D ≤ 2 * m ^ 2 + K * m := by omega
  have h7 : 2 * ((k + 1) * D) ≤ 2 * (m ^ 2 + K * m) := by
    have : (2 * (k + 1)) * D = 2 * ((k + 1) * D) := by ring
    omega
  omega

theorem adjoin_shift {V : Type} [AddCommGroup V] [Module ℂ V] {l : ℕ}
    (a : Fin (l + 1) → Module.End ℂ V) (μ : ℂ) :
    Algebra.adjoin ℂ (Set.range (Fin.cons (a 0 - algebraMap ℂ _ μ) (fun i : Fin l => a i.succ) :
      Fin (l + 1) → Module.End ℂ V)) = Algebra.adjoin ℂ (Set.range a) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      exact Subalgebra.sub_mem _ (Algebra.subset_adjoin ⟨0, rfl⟩) (Subalgebra.algebraMap_mem _ μ)
    · simp only [Fin.cons_succ]
      exact Algebra.subset_adjoin ⟨j.succ, rfl⟩
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · have h0 : a 0 - algebraMap ℂ _ μ ∈ Algebra.adjoin ℂ (Set.range (Fin.cons (a 0 - algebraMap ℂ _ μ)
          (fun i : Fin l => a i.succ) : Fin (l + 1) → Module.End ℂ V)) :=
        Algebra.subset_adjoin ⟨0, by simp⟩
      have := Subalgebra.add_mem _ h0 (Subalgebra.algebraMap_mem (Algebra.adjoin ℂ (Set.range (Fin.cons (a 0 - algebraMap ℂ _ μ)
          (fun i : Fin l => a i.succ) : Fin (l + 1) → Module.End ℂ V))) μ)
      simpa using this
    · exact Algebra.subset_adjoin ⟨j.succ, by simp⟩

theorem positionOne_invariantIntegral_exchange_step (l N K : ℕ) (hN : 0 < N)
    (hK : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (a : Fin l → Module.End ℂ V), (∀ i j, Commute (a i) (a j)) →
      4 * N ^ 2 * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ V ^ 2 + K * Module.finrank ℂ V) :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (a : Fin (l + 1) → Module.End ℂ V), Module.finrank ℂ V = n → (∀ i j, Commute (a i) (a j)) →
      N * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ V ^ 2 + K * Module.finrank ℂ V := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ a hn hc
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) = 0 :=
      Module.finrank_zero_of_subsingleton
    simp [this]
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (a 0)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  set s : Module.End ℂ V := a 0 - algebraMap ℂ _ μ with hs
  have hsc : ∀ i, Commute s (a i) := fun i =>
    (hc 0 i).sub_left (Algebra.commutes μ (a i))
  have hsv : s v = 0 := by
    simp [hs, hv.apply_eq_smul, Module.algebraMap_end_apply]
  obtain ⟨k, hcompl, hk⟩ :=
    ((LinearMap.eventually_isCompl_ker_pow_range_pow s).and (Filter.eventually_ge_atTop 1)).exists
  have hkc : ∀ i, Commute (s ^ k) (a i) := fun i => (hsc i).pow_left k
  have h : ∀ i, ∀ w ∈ LinearMap.ker (s ^ k), a i w ∈ LinearMap.ker (s ^ k) := by
    intro i w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have := congrArg (fun f : Module.End ℂ V => f w) (hkc i).eq
    simp only [Module.End.mul_apply] at this
    rw [this, hw, map_zero]
  have h' : ∀ i, ∀ w ∈ LinearMap.range (s ^ k), a i w ∈ LinearMap.range (s ^ k) := by
    rintro i _ ⟨u, rfl⟩
    refine ⟨a i u, ?_⟩
    have := congrArg (fun f : Module.End ℂ V => f u) (hkc i).eq
    simpa only [Module.End.mul_apply] using this
  by_cases hr : LinearMap.range (s ^ k) = ⊥
  ·
    have hnil : IsNilpotent s := ⟨k, LinearMap.range_eq_bot.mp hr⟩
    set b : Fin (l + 1) → Module.End ℂ V := Fin.cons s (fun i : Fin l => a i.succ) with hb
    have hadj : Algebra.adjoin ℂ (Set.range b) = Algebra.adjoin ℂ (Set.range a) :=
      adjoin_shift a μ
    have hb0 : b 0 = s := rfl
    have hbs : ∀ i : Fin l, b i.succ = a i.succ := fun i => rfl
    have hbc : ∀ i j, Commute (b i) (b j) := by
      intro i j
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
      · exact Commute.refl _
      · rw [hb0, hbs]; exact hsc _
      · rw [hb0, hbs]; exact (hsc _).symm
      · rw [hbs, hbs]; exact hc _ _
    have hmem : ∀ c ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range b)), Commute c s := by
      intro c hcm
      have hle : Algebra.adjoin ℂ (Set.range b) ≤ Subalgebra.centralizer ℂ {s} := by
        apply Algebra.adjoin_le
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
        rintro g rfl
        exact hbc 0 i
      have := hle hcm
      rw [Subalgebra.mem_centralizer_iff] at this
      exact (this s rfl).symm
    have h1 := GlobalTheory.CompanionTheory.CommStep.comm_step V l b hbc (2 * N - 1)
    have h2 := GlobalTheory.CompanionTheory.CommNil.succ_mul_finrank_map_le V s hnil (2 * N - 1) _ hmem
    rw [hb0] at h1
    have h3 := hK V (fun i : Fin l => b i.succ) (fun i j => hbc _ _)
    rw [hadj] at h1 h2
    exact arith_nil N _ _ _ _ K hN h1 h2 h3
  ·
    have hker : LinearMap.ker (s ^ k) ≠ ⊥ := by
      intro hbot
      have hmem : v ∈ LinearMap.ker (s ^ k) := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply, hsv, map_zero]
      rw [hbot, Submodule.mem_bot] at hmem
      exact hv.2 hmem
    have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
    have p1 : Module.finrank ℂ (LinearMap.ker (s ^ k)) ≠ 0 := fun h0 =>
      hker (Submodule.finrank_eq_zero.mp h0)
    have p2 : Module.finrank ℂ (LinearMap.range (s ^ k)) ≠ 0 := fun h0 =>
      hr (Submodule.finrank_eq_zero.mp h0)
    have hres : ∀ (W : Submodule ℂ V) (g : ∀ i, ∀ w ∈ W, a i w ∈ W) (i j : Fin (l + 1)),
        Commute (((a i).restrict (g i) : Module.End ℂ W)) ((a j).restrict (g j)) := by
      intro W g i j
      show ((a i).restrict (g i) : Module.End ℂ W) * (a j).restrict (g j) =
        ((a j).restrict (g j) : Module.End ℂ W) * (a i).restrict (g i)
      refine LinearMap.ext fun w => Subtype.ext ?_
      have := congrArg (fun f : Module.End ℂ V => f w.1) (hc i j).eq
      simpa [Module.End.mul_apply] using this
    have i1 := ih (Module.finrank ℂ (LinearMap.ker (s ^ k))) (by omega) (LinearMap.ker (s ^ k))
      (fun i => ((a i).restrict (h i) : Module.End ℂ (LinearMap.ker (s ^ k)))) rfl (hres _ h)
    have i2 := ih (Module.finrank ℂ (LinearMap.range (s ^ k))) (by omega) (LinearMap.range (s ^ k))
      (fun i => ((a i).restrict (h' i) : Module.End ℂ (LinearMap.range (s ^ k)))) rfl (hres _ h')
    have h3 := GlobalTheory.CompanionTheory.CommSplit.finrank_adjoin_le_add V (l + 1) a _ _ hcompl h h'
    rw [← hsum]
    calc N * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a))
        ≤ N * (_ + _) := Nat.mul_le_mul_left _ h3
      _ = _ + _ := Nat.mul_add _ _ _
      _ ≤ _ := Nat.add_le_add i1 i2
      _ ≤ _ := by nlinarith [Nat.zero_le (Module.finrank ℂ (LinearMap.ker (s ^ k)) *
            Module.finrank ℂ (LinearMap.range (s ^ k)))]

theorem stComm : StComm := by
  unfold StComm
  intro l
  induction l with
  | zero =>
    intro N
    refine ⟨N, ?_⟩
    intro V _ _ _ a _
    have hr : Set.range a = ∅ := Set.range_eq_empty a
    rw [hr, Algebra.adjoin_empty]
    rcases subsingleton_or_nontrivial V with hV | hV
    · have : Module.finrank ℂ (⊥ : Subalgebra ℂ (Module.End ℂ V)) = 0 :=
        Module.finrank_zero_of_subsingleton
      simp [this]
    · have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
      rw [Subalgebra.finrank_bot]
      nlinarith
  | succ l ih =>
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact ⟨0, fun V _ _ _ a _ => by simp⟩
    obtain ⟨K, hK⟩ := ih (4 * N ^ 2)
    exact ⟨K, fun V _ _ _ a hc => positionOne_invariantIntegral_exchange_step l N K hN hK _ V a rfl hc⟩

end GlobalTheory.CompanionTheory.Bernstein
end
end
