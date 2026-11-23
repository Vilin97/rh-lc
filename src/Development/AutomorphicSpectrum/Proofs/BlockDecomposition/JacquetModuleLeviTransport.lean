module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import GroundTheory.AutomorphicForms.InductionParabolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusCharacterLeviStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import GroundTheory.AutomorphicForms.Iwasawa
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
public import GroundTheory.AutomorphicForms.FiniteBruhat
public import GroundTheory.AutomorphicForms.GeometricLemmaJacquetCell
public import GroundTheory.AutomorphicForms.GeometricLemmaNormal
import GroundTheory.AutomorphicForms.GeometricLemmaOrbit
public import GroundTheory.AutomorphicForms.InductionParabolicGroups

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicEqBlockUpper

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.ParabBridge

theorem parab_eq_blockUpper : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → parab k e = blockUpper k N β := by
  intro k _ _ _ _ α _ _ N m _ _ e β h
  ext g
  rw [mem_parab, GroundTheory.Automorphic.Iwasawa.mem_blockUpper]
  exact forall₂_congr fun i j => by rw [h j i]

end GlobalTheory.CompanionTheory.ParabBridge
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicEqBlockUpperStatement

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.parabolic_eq_block_upper : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → parab k e = blockUpper k N β := by
  first | exact @GlobalTheory.CompanionTheory.ParabBridge.parab_eq_blockUpper | exact GlobalTheory.CompanionTheory.ParabBridge.parab_eq_blockUpper | (intros; apply GlobalTheory.CompanionTheory.ParabBridge.parab_eq_blockUpper <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLeviProjection

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.SmGLBridge

theorem leviProj_found_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ (p : GL (Fin N) k) (h1 : p ∈ parab k e) (h2 : p ∈ blockUpper k N β), φ (leviProj k e ⟨p, h1⟩) = GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩ := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ φ hφ p h1 h2
  have hblk : ∀ x y, β x = β y ↔ blk e x = blk e y := by
    intro x y
    constructor
    · intro h
      have h3 := (hβ x y).not.1 (by omega)
      have h4 := (hβ y x).not.1 (by omega)
      exact le_antisymm (not_lt.1 h4) (not_lt.1 h3)
    · intro h
      have h3 := (hβ x y).not.2 (by rw [h]; exact lt_irrefl _)
      have h4 := (hβ y x).not.2 (by rw [h]; exact lt_irrefl _)
      omega
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro x y
  rw [hφ]
  rw [show ((GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩ : levi k N β) : GL (Fin N) k).val x y = _ from GroundTheory.Automorphic.Parabolic.leviProj_apply _ x y]
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
  by_cases hab : a = b
  · subst hab
    rw [if_pos ((hblk _ _).2 (by simp))]
    have := leviEmb_apply_same k e (leviProj k e ⟨p, h1⟩) a i j
    rw [this, leviProj_apply]
  · rw [if_neg (fun h => hab (by simpa using (hblk _ _).1 h))]
    exact leviEmb_apply_ne k e _ hab i j

end GlobalTheory.CompanionTheory.SmGLBridge
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLeviProjectionStatement

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.parabolic_levi_projection : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ (p : GL (Fin N) k) (h1 : p ∈ parab k e) (h2 : p ∈ blockUpper k N β), φ (leviProj k e ⟨p, h1⟩) = GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩ := by
  first | exact @GlobalTheory.CompanionTheory.SmGLBridge.leviProj_found_eq | exact GlobalTheory.CompanionTheory.SmGLBridge.leviProj_found_eq | (intros; apply GlobalTheory.CompanionTheory.SmGLBridge.leviProj_found_eq <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleLeviTransport

section

@[expose] public section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.ParIndBridge

theorem parInd_equiv_parabolicInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((parInd e ρ).Equiv (parabolicInd k N β (ρ.comp φ.symm.toMonoidHom))) := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ φ hφ W _ _ ρ
  have hP : parab k e = blockUpper k N β := GlobalTheory.T.parabolic_eq_block_upper k e β hβ
  have h12 : ∀ {p : GL (Fin N) k}, p ∈ parab k e → p ∈ blockUpper k N β := fun h => hP ▸ h
  have h21 : ∀ {p : GL (Fin N) k}, p ∈ blockUpper k N β → p ∈ parab k e := fun h => hP ▸ h
  have hchar : ∀ (p : GL (Fin N) k) (h1 : p ∈ parab k e) (h2 : p ∈ blockUpper k N β) (w : W),
      (deltaHalf k m (leviProj k e ⟨p, h1⟩) : ℂ) • ρ (leviProj k e ⟨p, h1⟩) w =
        sqrtModular k N β ⟨p, h2⟩ •
          ρ (φ.symm (GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩)) w := by
    intro p h1 h2 w
    have hL := GlobalTheory.T.parabolic_levi_projection k e β hβ φ hφ p h1 h2
    rw [← hL, MulEquiv.symm_apply_apply, GlobalTheory.T.modulus_character_levi k e β hβ φ hφ, hL,
      GroundTheory.Automorphic.Parabolic.sqrtModular_leviProj]
  let σ := ρ.comp φ.symm.toMonoidHom
  let E : IndSp e ρ ≃ₗ[ℂ] GroundTheory.Automorphic.Parabolic.parabolicIndSpace k N β σ :=
    { toFun := fun f => ⟨f.1.1, fun p g => by
          have h := parInd_law e ρ f ⟨p.1, h21 p.2⟩ g
          refine h.trans ?_
          exact hchar p.1 (h21 p.2) p.2 _,
        GroundTheory.Automorphic.stabilizerOf (GlobalTheory.PRep.ind (parab k e)
          ((twist ρ (deltaHalf k m)).comp (leviProj k e))) f.1, f.2, fun x hx g => by
          have h := GroundTheory.Automorphic.mem_stabilizerOf.1 hx
          exact congrFun (congrArg Subtype.val h) g⟩
      invFun := fun f => ⟨⟨f.1, fun p g => by
          have h := f.2.1 ⟨p.1, h12 p.2⟩ g
          refine h.trans ?_
          exact (hchar p.1 p.2 (h12 p.2) _).symm⟩, by
          obtain ⟨-, K, hK, hf⟩ := f.2
          refine mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds (one_mem K)) fun x hx => ?_)
          exact Subtype.ext (funext fun g => hf x hx g)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨Representation.Equiv.mk E fun g => LinearMap.ext fun f => Subtype.ext (funext fun x => rfl)⟩

end GlobalTheory.CompanionTheory.ParIndBridge
end
end
