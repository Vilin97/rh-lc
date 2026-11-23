module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsRead
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingAffPtUncurry
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFactorReductionKernelAllNonFreeUnreadEntries
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFactorReductionKernelIntegratesFreeEntries
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelReductionExtendEvaluatedIntegrated
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEqZeroOfFlatMapColumnZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFactorThroughFlatMapFourierJacobiColumn

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.LocFlat

section Lin
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}


open Classical in
theorem flCol_integrand_integrable (ψ : AddChar k Circle) (hψ : Continuous ψ) (ν : Measure k)
    (hν : ν.IsAddHaarMeasure) (p : ℕ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (x : Matrix n (n' ⊕ Unit) k) :
    Integrable (fun e => Φ (ptCol p x e) * (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ))
      (Measure.pi fun _ => ν) := by
  have := GlobalTheory.SplitWeil.t2Space k
  have := GlobalTheory.SplitWeil.secondCountable k
  have := hν
  have hemb : Topology.IsClosedEmbedding (fun e => ptCol (c := c) p x e) := by
    have hslice : Topology.IsClosedEmbedding (Prod.mk x.toCols₁ :
        ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → _) :=
      Function.LeftInverse.isClosedEmbedding (f := Prod.snd) (fun _ => rfl)
        continuous_snd (Continuous.prodMk_right x.toCols₁)
    exact (Homeomorph.addRight (colAt n' c p fun r => x r (Sum.inr ()))).isClosedEmbedding.comp
      ((isClosedEmbedding_affPt_uncurry p).comp hslice)
  have hch : Continuous fun e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k =>
      ((ψ (-ch (affPt p (0 : Matrix n n' k) e)) : Circle) : ℂ) := by
    refine continuous_subtype_val.comp (hψ.comp (Continuous.neg ?_))
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_affPt_uncurry p).comp (Continuous.prodMk_right (0 : Matrix n n' k))).matrix_elem _ _
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (hΦ.1.continuous.comp hemb.continuous).mul hch
  · exact (hΦ.2.comp_isClosedEmbedding hemb).mul_right

theorem flCol_add_of_SB (ψ : AddChar k Circle) (hψ : Continuous ψ) (ν : Measure k)
    (hν : ν.IsAddHaarMeasure) (p : ℕ) (Φ₁ Φ₂ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (h₁ : Φ₁ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (h₂ : Φ₂ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    flCol ψ ν p (Φ₁ + Φ₂) = flCol ψ ν p Φ₁ + flCol ψ ν p Φ₂ := by
  funext x
  simp only [flCol_eq_integral, Pi.add_apply, add_mul]
  exact integral_add (flCol_integrand_integrable ψ hψ ν hν p Φ₁ h₁ x)
    (flCol_integrand_integrable ψ hψ ν hν p Φ₂ h₂ x)

theorem flCol_smul (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (a : ℂ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) :
    flCol ψ ν p (a • Φ) = a • flCol ψ ν p Φ := by
  funext x
  simp only [flCol_eq_integral, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

end Lin

theorem flCol_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c + 1 → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), (∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), (∀ x, GlobalTheory.LocFlat.flCol ψ ν p Φ.1 x = 0) → L Φ = 0) → ∃ L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψ ν p Φ.1 → L Φ = L₀ Ψ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p hp1 hpc M _ _ L hL
  have hSB := (flat_SB_onto k ψ ν hψ hν n n' c p hp1).1 hpc
  let F : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) :=
    { toFun := fun Φ => ⟨flCol ψ ν p Φ.1, hSB.1 Φ.1 Φ.2⟩
      map_add' := fun Φ₁ Φ₂ => Subtype.ext (flCol_add_of_SB ψ hψ ν hν p Φ₁.1 Φ₂.1 Φ₁.2 Φ₂.2)
      map_smul' := fun a Φ => Subtype.ext (flCol_smul ψ ν p a Φ.1) }
  have hFs : Function.Surjective F := fun Ψ => by
    obtain ⟨Φ, hΦ, h⟩ := hSB.2 Ψ.1 Ψ.2
    exact ⟨⟨Φ, hΦ⟩, Subtype.ext h⟩
  have hker : LinearMap.ker F ≤ LinearMap.ker L := fun Φ hΦ => by
    rw [LinearMap.mem_ker] at hΦ ⊢
    apply hL
    intro x
    have := congrArg (fun Ψ : SB (Matrix n (n' ⊕ Unit) k) => Ψ.1 x) hΦ
    simpa [F] using this
  refine ⟨((LinearMap.ker F).liftQ L hker).comp (F.quotKerEquivOfSurjective hFs).symm.toLinearMap, ?_⟩
  intro Φ Ψ hΨ
  have hΨF : Ψ = F Φ := Subtype.ext hΨ
  subst hΨF
  have h2 : (F.quotKerEquivOfSurjective hFs).symm (F Φ) = Submodule.Quotient.mk Φ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h2]
  rfl

end GlobalTheory.LocFlat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFactorThroughFlatMapFourierJacobiColumnStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.exists_factor_through_flatMapFourierJacobiColumn : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c + 1 → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), (∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), (∀ x, GlobalTheory.LocFlat.flCol ψ ν p Φ.1 x = 0) → L Φ = 0) → ∃ L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψ ν p Φ.1 → L Φ = L₀ Ψ := by
  first | exact @GlobalTheory.LocFlat.flCol_factor | exact GlobalTheory.LocFlat.flCol_factor | (intros; apply GlobalTheory.LocFlat.flCol_factor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFactorReductionKernelAllNonFreeUnreadEntriesStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.flatFactorReduction_kernel_all_nonFreeUnread_entries : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → GlobalTheory.FlatFactor.TwLaw ρ ψ l → GlobalTheory.FlatFactor.KerRed ν (GlobalTheory.FlatFactor.evC n n' c ρ) (GlobalTheory.FlatFactor.itB n n' c ρ) (basePt c (0 : Matrix n n' k)) l → GlobalTheory.FlatFactor.KerRed ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itB n n' c ρ) (basePt c (0 : Matrix n n' k)) l := by
  first | exact @GlobalTheory.FlatFactor.LowStage.kerRed_evAll | exact GlobalTheory.FlatFactor.LowStage.kerRed_evAll | (intros; apply GlobalTheory.FlatFactor.LowStage.kerRed_evAll <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFactorReductionKernelIntegratesFreeEntriesStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.flatFactorReduction_kernel_integrates_free_entries : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → GlobalTheory.FlatFactor.TwLaw ρ ψ l → GlobalTheory.FlatFactor.KerRed ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itB n n' c ρ) (basePt c (0 : Matrix n n' k)) l → GlobalTheory.FlatFactor.KerRed ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itFree n n' c ρ) (basePt c (0 : Matrix n n' k)) l := by
  first | exact @GlobalTheory.FlatFactor.UpStage.kerRed_itFree | exact GlobalTheory.FlatFactor.UpStage.kerRed_itFree | (intros; apply GlobalTheory.FlatFactor.UpStage.kerRed_itFree <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelReductionExtendEvaluatedIntegratedStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.kernelReduction_extend_evaluated_integrated : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it ev' it' : Finset (m × m')), ev ⊆ ev' → it ⊆ it' → Disjoint ev' it' → GlobalTheory.FlatFactor.KerRed ν ev it β l → (∀ e ∈ ev', e ∉ ev → ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → (∀ e ∈ it', e ∉ it → ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) → GlobalTheory.FlatFactor.KerRed ν ev' it' β l := by
  first | exact @GlobalTheory.FlatFactor.KerRedStep.kerRed_extend | exact GlobalTheory.FlatFactor.KerRedStep.kerRed_extend | (intros; apply GlobalTheory.FlatFactor.KerRedStep.kerRed_extend <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiFactorsLocalFlat

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section

namespace GlobalTheory.FlatFactor

theorem ch_add_mat {k : Type} [Field k] {n n' : Type} {c : ℕ} (a b : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    ch (a + b) = ch a + ch b := by
  simp [ch, Finset.sum_add_distrib]

theorem continuous_ch {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n n' : Type} {c : ℕ} :
    Continuous (ch : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → k) :=
  continuous_finsetSum _ fun i _ => continuous_id.matrix_elem _ _

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

theorem kerRed_empty {M : Type} [AddCommGroup M] [Module ℂ M] (ν : Measure k) (β : Matrix m m' k)
    (l : SB (Matrix m m' k) →ₗ[ℂ] M) : KerRed ν ∅ ∅ β l := by
  intro Θ h
  have hΘ : Θ = 0 := by
    ext t
    have ht := h t
    simp only [red] at ht
    haveI : IsEmpty {e : m × m' // e ∈ (∅ : Finset (m × m'))} := ⟨fun e => Finset.notMem_empty _ e.2⟩
    rw [Measure.pi_of_empty (x := isEmptyElim), integral_dirac] at ht
    have hf : fill ∅ ∅ β t isEmptyElim = t := by ext r q; simp [fill]
    rw [hf] at ht
    simpa using ht
  rw [hΘ, map_zero]

theorem mem_SB_addChar_mul (ψ : AddChar k Circle) (hψ : Continuous ψ) {X : Type} [TopologicalSpace X]
    (f : X → k) (hf : Continuous f) (Θ : X → ℂ) (hΘ : Θ ∈ SB X) :
    (fun t => (ψ (f t) : ℂ) * Θ t) ∈ SB X :=
  ⟨((GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψ hψ).comp_continuous hf).mul hΘ.1,
    hΘ.2.mul_left⟩

end

end GlobalTheory.FlatFactor

open GlobalTheory.FlatFactor in
theorem GlobalTheory.FlatFactor.flCol_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val < ρ ∧ ¬ Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l, r = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, q = Sum.inr i → i.val = ρ) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ ≤ i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → L Φ' = (ψ (ch (Matrix.single r q a)) : ℂ) • L Φ) → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → (∀ l l' : Fin c, l.val < ρ → ρ ≤ l'.val → u.val l l' = 0) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∃ L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ.1 → L Φ = L₀ Ψ := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν n n' _ _ _ _ c ρ M _ _ L hc H1 H2 H3 H4
  set Mt := Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k
  set β : Mt := basePt c (0 : Matrix n n' k)
  have tw : ∀ (f : Mt → k), Continuous f → ∀ Θ : SB Mt, (fun t => (ψ (f t) : ℂ) * Θ.1 t) ∈ SB Mt :=
    fun f hf Θ => mem_SB_addChar_mul ψ hψc f hf Θ.1 Θ.2
  let T : SB Mt → SB Mt := fun Θ => ⟨fun t => (ψ (ch t) : ℂ) * Θ.1 t, tw _ continuous_ch Θ⟩
  let L' : SB Mt →ₗ[ℂ] M :=
    { toFun := fun Θ => L (T Θ)
      map_add' := fun Θ₁ Θ₂ => by
        show L (T (Θ₁ + Θ₂)) = L (T Θ₁) + L (T Θ₂)
        rw [← map_add (f := _)]; congr 1; apply Subtype.ext; funext t
        show (ψ (ch t) : ℂ) * (Θ₁.1 t + Θ₂.1 t) = (ψ (ch t) : ℂ) * Θ₁.1 t + (ψ (ch t) : ℂ) * Θ₂.1 t
        ring
      map_smul' := fun a Θ => by
        show L (T (a • Θ)) = a • L (T Θ)
        rw [← map_smul]; congr 1; apply Subtype.ext; funext t
        show (ψ (ch t) : ℂ) * (a * Θ.1 t) = a * ((ψ (ch t) : ℂ) * Θ.1 t)
        ring }
  have hL' : ∀ Θ, L' Θ = L (T Θ) := fun _ => rfl

  have hTw : TwLaw ρ ψ L' := by
    intro u hN hblk Θ Θ' Θ'' h' h''
    rw [hL', hL']
    have := H4 u hN hblk (T Θ'') (T Θ') (fun t => by
      simp only [T, h', h'']
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
      rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 3; ring)
    exact this

  have hS1 : KerRed ν (evC n n' c ρ) (itB n n' c ρ) β L' := by
    refine GlobalTheory.T.kernelReduction_extend_evaluated_integrated k ψ ν hψc hψ1 hν _ _ M L' β ∅ ∅ _ _ (Finset.empty_subset _) (Finset.empty_subset _) ?_
      (kerRed_empty ν β L') ?_ ?_
    · rw [Finset.disjoint_left]
      rintro ⟨r, q⟩ h1 h2
      simp only [evC, itB, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rcases h1 with ⟨i, hq, -, hfr⟩ | ⟨l, hr, hl, hq⟩
      · exact hfr h2.1
      · subst hr
        rcases q with q | q
        · simp [Free] at h2; omega
        · have := hq q rfl; simp [Free] at h2; omega
    · rintro ⟨r, q⟩ he - b Θ Θ' hΘ
      simp only [evC, Finset.mem_filter, Finset.mem_univ, true_and] at he
      rw [hL', hL']
      rcases he with he | he
      · exact H1 r q he b (T Θ) (T Θ') (fun t => by simp only [T, hΘ]; ring)
      · exact H2 r q he b (T Θ) (T Θ') (fun t => by simp only [T, hΘ]; ring)
    · rintro ⟨r, q⟩ he - a Θ Θ' hΘ
      simp only [itB, Finset.mem_filter, Finset.mem_univ, true_and] at he
      rw [hL', hL']
      set E : Mt := Matrix.single r q a
      let Φ' : SB Mt := ⟨fun t => (ψ (ch (t + E)) : ℂ) * Θ'.1 t, tw _ (continuous_ch.comp (continuous_add_const E)) Θ'⟩
      have h3 := H3 r q he.1 he.2 a (T Θ) Φ' (fun t => by
        show (ψ (ch (t + E)) : ℂ) * Θ'.1 t = (ψ (ch (t + E)) : ℂ) * Θ.1 (t + E)
        rw [hΘ])
      have hT : T Θ' = (ψ (-ch E) : ℂ) • Φ' := by
        ext t
        show (ψ (ch t) : ℂ) * Θ'.1 t = (ψ (-ch E) : ℂ) * ((ψ (ch (t + E)) : ℂ) * Θ'.1 t)
        have hm : ∀ x y : k, (ψ x : ℂ) * ψ y = ψ (x + y) := by
          intro x y; rw [AddChar.map_add_eq_mul, Circle.coe_mul]
        rw [← mul_assoc, hm, ch_add_mat, show -ch E + (ch t + ch E) = ch t by ring]
      rw [hT, map_smul, h3, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel,
        AddChar.map_zero_eq_one, Circle.coe_one, one_smul]
  have hS2 := GlobalTheory.T.flatFactorReduction_kernel_all_nonFreeUnread_entries k ψ ν hψc hψ1 hν n n' c ρ M L' hc hTw hS1
  have hS3 := GlobalTheory.T.flatFactorReduction_kernel_integrates_free_entries k ψ ν hψc hψ1 hν n n' c ρ M L' hc hTw hS2
  refine GlobalTheory.T.exists_factor_through_flatMapFourierJacobiColumn k ψ ν hψc hν n n' c (ρ + 1) (by omega) (by omega) M L ?_
  intro Φ hΦ
  let Θ : SB Mt := ⟨fun t => (ψ (-ch t) : ℂ) * Φ.1 t, tw _ continuous_ch.neg Φ⟩
  have hΘ : T Θ = Φ := by
    ext t
    simp only [T, Θ]
    rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one,
      Circle.coe_one, one_mul]
  have := hS3 Θ (GlobalTheory.T.partialReduction_eq_zero_of_flatMapColumn_zero k ψ ν n n' c ρ hc Φ.1 hΦ)
  rw [hL', hΘ] at this
  exact this
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiFactorsLocalFlatStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.flatMap_fourierJacobi_factors_local_flat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val < ρ ∧ ¬ Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l, r = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, q = Sum.inr i → i.val = ρ) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ ≤ i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → L Φ' = (ψ (ch (Matrix.single r q a)) : ℂ) • L Φ) → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → (∀ l l' : Fin c, l.val < ρ → ρ ≤ l'.val → u.val l l' = 0) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∃ L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ.1 → L Φ = L₀ Ψ := by
  first | exact @GlobalTheory.FlatFactor.flCol_factor | exact GlobalTheory.FlatFactor.flCol_factor | (intros; apply GlobalTheory.FlatFactor.flCol_factor <;> assumption)
end
end
