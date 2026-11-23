module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityTransportLocalFieldIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityTransportLocalFieldIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveFrameMatrixTransportIffStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaFunctionTransportLocalFieldIsoStatement
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrespondingLatticesBlockLattice

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport

theorem latCorr_blockLat : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type} [DecidableEq D] [DecidableEq D₂], IsLocIso j → ∀ (cD : D₂ ≃ D) {ϖ : kˣ} {ϖ₂ : k'ˣ}, IsUnif ϖ → IsUnif ϖ₂ → ∀ (e : ℕ) (P : Finset D) (P₂ : Finset D₂), (∀ c, c ∈ P₂ ↔ cD c ∈ P) → LatCorr j cD (blockLat ϖ e P) (blockLat ϖ₂ e P₂) := by
  intro k k' _ _ _ _ _ _ _ _ j D D₂ _ _ hj cD ϖ ϖ₂ hϖ hϖ₂ e P P₂ hP x
  have hu : valuation k' (j (ϖ : k)) = valuation k' (ϖ₂ : k') := by
    have h1 := isUnif_map hj hϖ
    exact h1.trans hϖ₂.symm
  have hb : ∀ c : D₂, valuation k' ((blockUnits ϖ₂ e P₂ c : k'ˣ) : k') =
      valuation k' (j (blockUnits ϖ e P (cD c) : kˣ)) := by
    intro c
    by_cases hc : c ∈ P₂
    · have hc' : cD c ∈ P := (hP c).1 hc
      simp only [blockUnits, if_pos hc, if_pos hc', Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀,
        map_pow, hu]
    · have hc' : cD c ∉ P := fun h => hc ((hP c).2 h)
      simp [blockUnits, hc, hc']
  show (∀ c, valuation k' (j (x (cD c))) ≤ valuation k' ((blockUnits ϖ₂ e P₂ c : k'ˣ) : k')) ↔
    ∀ d, valuation k (x d) ≤ valuation k ((blockUnits ϖ e P d : kˣ) : k)
  simp only [hb, val_le_iff hj]
  exact ⟨fun h d => by simpa using h (cD.symm d), fun h c => h (cD c)⟩

end GlobalTheory.PureMatch.Transport
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrespondingLatticesBlockLatticeStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport


theorem _root_.GlobalTheory.T.correspondingLattices_blockLattice : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type} [DecidableEq D] [DecidableEq D₂], IsLocIso j → ∀ (cD : D₂ ≃ D) {ϖ : kˣ} {ϖ₂ : k'ˣ}, IsUnif ϖ → IsUnif ϖ₂ → ∀ (e : ℕ) (P : Finset D) (P₂ : Finset D₂), (∀ c, c ∈ P₂ ↔ cD c ∈ P) → LatCorr j cD (blockLat ϖ e P) (blockLat ϖ₂ e P₂) := by
  first | exact @GlobalTheory.PureMatch.Transport.latCorr_blockLat | exact GlobalTheory.PureMatch.Transport.latCorr_blockLat | (intros; apply GlobalTheory.PureMatch.Transport.latCorr_blockLat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeCorrespondingLattices

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch.Transport

theorem dualLat_latCorr {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
    {D D₂ : Type} [Fintype D] [Fintype D₂] (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) : LatCorr j cD (dualLat Λ) (dualLat Λ₂) := by
  have key : ∀ y x : D → k, (fun c => j (y (cD c))) ⬝ᵥ (fun c => j (x (cD c))) = j (y ⬝ᵥ x) := by
    intro y x

    simp only [dotProduct, map_sum, map_mul]
    exact Fintype.sum_equiv cD _ _ fun c => rfl
  intro y
  rw [mem_dualLat, mem_dualLat]
  constructor
  · intro H x hx
    have := H _ ((h x).2 hx)
    rw [key] at this
    exact (hj.2.2 _).1 this
  · intro H x₂ hx₂
    set x : D → k := fun d => j.symm (x₂ (cD.symm d)) with hxdef
    have hx : (fun c => j (x (cD c))) = x₂ := by
      funext c; simp [x]
    rw [← hx] at hx₂ ⊢
    rw [key]
    exact (hj.2.2 _).2 (H x ((h x).1 hx₂))

end GlobalTheory.PureMatch.Transport
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeCorrespondingLatticesStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport


theorem _root_.GlobalTheory.T.dualLattice_correspondingLattices : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type} [Fintype D] [Fintype D₂], IsLocIso j → ∀ (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}, LatCorr j cD Λ Λ₂ → LatCorr j cD (dualLat Λ) (dualLat Λ₂) := by
  first | exact @GlobalTheory.PureMatch.Transport.dualLat_latCorr | exact GlobalTheory.PureMatch.Transport.dualLat_latCorr | (intros; apply GlobalTheory.PureMatch.Transport.dualLat_latCorr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatCorrSmul

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

noncomputable section
namespace GlobalTheory.PureMatch.Transport

theorem latCorr_smul {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {D D₂ : Type}
    (_hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (hΛ : LatCorr j cD Λ Λ₂) (c : kˣ) (c₂ : k'ˣ) (hc : valuation k' (j c) = valuation k' (c₂ : k')) :
    LatCorr j cD (c • Λ) (c₂ • Λ₂) := by

  have key : ∀ a : k', valuation k' a ≤ 1 → ∀ y ∈ Λ₂, a • y ∈ Λ₂ := fun a ha y hy =>
    Λ₂.smul_mem (⟨a, (Valuation.mem_integer_iff _ _).2 ha⟩ : 𝒪[k']) hy
  have hc₂ : valuation k' (c₂ : k') ≠ 0 := by simp
  set u : k' := (c₂⁻¹ : k'ˣ) * j c with hu
  have hu1 : valuation k' u = 1 := by
    rw [hu, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hc, inv_mul_cancel₀ hc₂]
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hu1; exact zero_ne_one hu1
  have hu1' : valuation k' u⁻¹ = 1 := by rw [map_inv₀, hu1, inv_one]
  intro x
  rw [mem_smul_lat, mem_smul_lat, ← hΛ]
  have heq : (c₂⁻¹ : k'ˣ) • (fun d => j (x (cD d))) = u • (fun d => j (((c⁻¹ : kˣ) • x) (cD d))) := by
    funext d
    simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, map_mul, hu, Units.val_inv_eq_inv_val, map_inv₀]
    field_simp
  rw [heq]
  constructor
  · intro h
    have := key u⁻¹ hu1'.le _ h
    rwa [smul_smul, inv_mul_cancel₀ hu0, one_smul] at this
  · exact key u hu1.le _

end GlobalTheory.PureMatch.Transport
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumPhiASplitPlaceTransportEq

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section

namespace GlobalTheory.PureMatch.Transport
open GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport
open scoped Pointwise

section General
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
  {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
  [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂]

theorem corr_smul_of (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) (c : kˣ) (c₂ : k'ˣ) (hc : valuation k' (j c) = valuation k' (c₂ : k')) :
    LatCorr j cD (c • Λ) (c₂ • Λ₂) := latCorr_smul hj cD h c c₂ hc

theorem corr_dual_of (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) : LatCorr j cD (dualLat Λ) (dualLat Λ₂) := GlobalTheory.T.dualLattice_correspondingLattices hj cD h

theorem primFrame_corr (hj : IsLocIso j) (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) (Z : Matrix A D k) :
    IsPrimFrame Λ₂ (trM j rA cD Z) ↔ IsPrimFrame Λ Z := GlobalTheory.T.isPrimitiveFrame_matrixTransport_iff hj rA cD h Z

theorem corr_blockLat_of (hj : IsLocIso j) (cD : D₂ ≃ D) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂)
    (e : ℕ) (P : Finset D) (P₂ : Finset D₂) (hP : ∀ c, c ∈ P₂ ↔ cD c ∈ P) :
    LatCorr j cD (blockLat ϖ e P) (blockLat ϖ₂ e P₂) := GlobalTheory.T.correspondingLattices_blockLattice hj cD hϖ hϖ₂ e P P₂ hP

variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k']

theorem fFun_corr (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D)
    (μ₂ : MeasureTheory.Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D)
    (hσ : ∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ)
    (hν : ∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k) :
    fFun μ₂ σ₂ ν₂ Ψ (trM j rA cD Z) = fFun (pullMeas hj rA' μ₂) σ ν (fun Y => Ψ (trM j rA' cD Y)) Z :=
  GlobalTheory.T.zetaFunction_transport_localFieldIso hj rA rA' cD μ₂ σ₂ σ hσ ν₂ ν hν Ψ Z

end General
end GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch.Transport
open GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport
open scoped Pointwise

section General
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
  {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
  [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂]

theorem latCorr_latA (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂) (e : ℕ) :
    LatCorr j cD (latA ϖ e Λ) (latA ϖ₂ e Λ₂) := by
  refine corr_smul_of hj cD (corr_dual_of hj cD h) _ _ ?_
  have h1 : valuation k' (j ϖ) = valuation k' (ϖ₂ : k') := (isUnif_map hj hϖ).trans hϖ₂.symm
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow, h1]

theorem trM_mem_matLat (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) (Z : Matrix A D k) : trM j rA cD Z ∈ matLat A₂ Λ₂ ↔ Z ∈ matLat A Λ := by
  rw [mem_matLat, mem_matLat]
  refine ⟨fun H a => ?_, fun H r => (h (Z.row (rA r))).2 (H _)⟩
  obtain ⟨r, rfl⟩ := rA.surjective a
  exact (h (Z.row (rA r))).1 (H r)

theorem hasDepth_trM (hj : IsLocIso j) (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ)
    (hϖ₂ : IsUnif ϖ₂) (e : ℕ) (Ξ : Matrix A D k → ℂ) (hΞ : HasDepth ϖ e Λ Ξ) :
    HasDepth ϖ₂ e Λ₂ (fun Y => Ξ (trM j.symm rA.symm cD.symm Y)) := by
  have h1 : valuation k' (j ϖ) = valuation k' (ϖ₂ : k') := (isUnif_map hj hϖ).trans hϖ₂.symm
  have hs : LatCorr j cD (ϖ ^ e • Λ) (ϖ₂ ^ e • Λ₂) := corr_smul_of hj cD h _ _ (by
    simp only [Units.val_pow_eq_pow_val, map_pow]; rw [h1])
  refine ⟨fun Y hY => hΞ.1 _ fun hZ => hY ?_, fun Y W hW => ?_⟩
  · rw [← trM_trM_symm j rA cD Y]; exact (trM_mem_matLat rA cD h _).2 hZ
  · have hW' : trM j.symm rA.symm cD.symm W ∈ matLat A (ϖ ^ e • Λ) := by
      rw [← trM_mem_matLat rA cD hs, trM_trM_symm]; exact hW
    show Ξ (trM j.symm rA.symm cD.symm (Y + W)) = Ξ (trM j.symm rA.symm cD.symm Y)
    rw [show trM j.symm rA.symm cD.symm (Y + W) = trM j.symm rA.symm cD.symm Y + trM j.symm rA.symm cD.symm W by
      ext r c; simp]
    exact hΞ.2 _ _ hW'

variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k']

theorem phiA_trM (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D)
    (μ₂ : MeasureTheory.Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D)
    (hσ : ∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ)
    (hν : ∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂) (e : ℕ)
    {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂)
    (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k) :
    phiA μ₂ σ₂ ν₂ ϖ₂ e Λ₂ Ψ (trM j rA cD Z) =
      phiA (pullMeas hj rA' μ₂) σ ν ϖ e Λ (fun Y => Ψ (trM j rA' cD Y)) Z := by
  classical
  unfold phiA
  rw [primFrame_corr hj rA cD (latCorr_latA hj cD h hϖ hϖ₂ e), fFun_corr hj rA rA' cD μ₂ σ₂ σ hσ ν₂ ν hν]

end General
end GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch
open GlobalTheory.PureMatch.Transport GlobalTheory.FlipMatch

theorem mem_one_block_iff {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T)
    (w : Pl D.host.E) {i j : Fin D.R.m} (e : Num G i j) (c : (locGrid G t w).Cols i j) :
    c ∈ Assignment.one.block _ _ ↔ GlobalTheory.SquareFlipReach.colE t w e c ∈ blockV e := by
  rcases c with c | c
  · simp [Assignment.block, blockV, GlobalTheory.SquareFlipReach.colE]
  · simp [Assignment.block, blockV, GlobalTheory.SquareFlipReach.colE]

theorem phiA_transport_split_place : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (e : Num G i j) (w : Pl D.host.E) (hw : w ∈ locPl G t) (v : Pl D.host.F) (hv : w.under (𝓞 D.host.F) = v)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), splitPrime τ = w → ∀ n : ℕ,
    ∃ (μ : @Measure (GL (Fin (spW₁ G i j).rank) (Fv D.host.F v)) Units.instMeasurableSpace)
      (_ : @Measure.IsHaarMeasure _ _ _ Units.instMeasurableSpace μ)
      (σ' : Fin (spW G i j).rank ⊕ Fin (spW₁ G i j).rank ≃ Fin ((spW G i j).rank + (spW₁ G i j).rank)),
      (∀ (Ψ : Matrix (Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) Z,
        phiA (haarVol ((givenLevel G t w ((i : ℕ), (j : ℕ))).map invT)) (stdSplit ((locGrid G t w).rank_square i j))
          ((locGrid G t w).nu i j) (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ψ (trA t hv e Z) =
        phiA μ σ' (((locGrid G t w).nu i j).comp (Units.map (GlobalTheory.LFun.complMap hv).toMonoidHom)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n
          (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) (fun Y => Ψ (trB t hv e Y)) Z) ∧
      ∀ Ξ, HasDepth (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) Ξ →
        ∃ Ξ', HasDepth (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ξ' ∧ ∀ Y, Ξ' (trB t hv e Y) = Ξ Y := by
  intro D T L sc G μ₀ hL t i j e w hw v hv τ hτ n
  subst hτ
  have hjj := isLocIso_complEquiv τ hv
  have hO := GivenAdm.givenLevel_open (G := G) hL hw ((i : ℕ), (j : ℕ))
  have hO' := isOpen_map_invT hO.1 hO.2
  haveI := isHaarMeasure_haarVol hO'.1 hO'.2
  have hϖv : IsUnif (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F v)).choose_spec
  have hc := corr_blockLat_of hjj (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) hϖv (isUnif_unifAt _) n (blockV e)
      (Assignment.one.block _ _) (mem_one_block_iff t _ e)
  refine ⟨pullMeas hjj (rowB t (splitPrime τ) i j)
      (haarVol ((givenLevel G t (splitPrime τ) ((i : ℕ), (j : ℕ))).map invT)), inferInstance,
    (Equiv.sumCongr (GlobalTheory.SquareFlipReach.rowE t (splitPrime τ) i j).symm (rowB t (splitPrime τ) i j).symm).trans
      ((stdSplit ((locGrid G t (splitPrime τ)).rank_square i j)).trans (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e)),
    fun Ψ Z => ?_, fun Ξ hΞ => ?_⟩
  · exact phiA_trM hjj (GlobalTheory.SquareFlipReach.rowE t (splitPrime τ) i j) (rowB t (splitPrime τ) i j)
      (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) _ _ _ (fun s => by simp) _ _ (fun x => rfl) hϖv
      (isUnif_unifAt _) n hc Ψ Z
  · exact ⟨_, hasDepth_trM hjj (rowB t (splitPrime τ) i j) (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) hc hϖv
      (isUnif_unifAt _) n Ξ hΞ, fun Y => by
        show Ξ (trM _ _ _ (trM (GlobalTheory.LFun.SplitTie.complEquiv τ hv) (rowB t (splitPrime τ) i j)
          (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) Y)) = Ξ Y
        rw [trM_symm_trM]⟩

end GlobalTheory.PureMatch
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumPhiASplitPlaceTransportEqStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel


theorem _root_.GlobalTheory.T.datumPhiA_splitPlace_transport_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (e : Num G i j) (w : Pl D.host.E) (hw : w ∈ locPl G t) (v : Pl D.host.F) (hv : w.under (𝓞 D.host.F) = v)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), splitPrime τ = w → ∀ n : ℕ,
    ∃ (μ : @Measure (GL (Fin (spW₁ G i j).rank) (Fv D.host.F v)) Units.instMeasurableSpace)
      (_ : @Measure.IsHaarMeasure _ _ _ Units.instMeasurableSpace μ)
      (σ' : Fin (spW G i j).rank ⊕ Fin (spW₁ G i j).rank ≃ Fin ((spW G i j).rank + (spW₁ G i j).rank)),
      (∀ (Ψ : Matrix (Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) Z,
        phiA (haarVol ((givenLevel G t w ((i : ℕ), (j : ℕ))).map invT)) (stdSplit ((locGrid G t w).rank_square i j))
          ((locGrid G t w).nu i j) (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ψ (trA t hv e Z) =
        phiA μ σ' (((locGrid G t w).nu i j).comp (Units.map (GlobalTheory.LFun.complMap hv).toMonoidHom)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n
          (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) (fun Y => Ψ (trB t hv e Y)) Z) ∧
      ∀ Ξ, HasDepth (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) Ξ →
        ∃ Ξ', HasDepth (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ξ' ∧ ∀ Y, Ξ' (trB t hv e Y) = Ξ Y := by
  first | exact @GlobalTheory.PureMatch.phiA_transport_split_place | exact GlobalTheory.PureMatch.phiA_transport_split_place | (intros; apply GlobalTheory.PureMatch.phiA_transport_split_place <;> assumption)
end
end
