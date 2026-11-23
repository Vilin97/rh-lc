module

public import Mathlib.MeasureTheory.Group.ModularCharacter
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
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.Topology.Algebra.Group.ContinuousInv

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularCharacterFunEqOfMapLeftMul

section

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ModChar

theorem modularCharacterFun_eq_of_map_left_mul :
    ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] [MeasurableSpace Q] [BorelSpace Q] (ρ : Measure Q) [IsFiniteMeasureOnCompacts ρ] [ρ.IsOpenPosMeasure] [ρ.IsMulRightInvariant] (δ : Q →* ℝ≥0), (∀ q : Q, ρ.map (fun x => q * x) = (δ q)⁻¹ • ρ) → ∀ q : Q, Measure.modularCharacterFun q = δ q := by
  intro Q _ _ _ _ _ _ _ _ ρ _ _ _ δ h q
  have : ρ.inv.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  have hδ : (δ q⁻¹)⁻¹ = δ q := by
    rw [inv_eq_iff_eq_inv]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, inv_mul_cancel, map_one]
  have hcomp : (fun x : Q => x * q) ∘ Inv.inv = Inv.inv ∘ (fun y : Q => q⁻¹ * y) := by
    funext y
    simp [mul_inv_rev]
  have hmap : Measure.map (fun x : Q => x * q) ρ.inv = δ q • ρ.inv := by
    rw [Measure.inv_def, Measure.map_map (measurable_mul_const q) measurable_inv, hcomp,
      ← Measure.map_map measurable_inv (measurable_const_mul q⁻¹), h q⁻¹, Measure.map_smul, hδ]
    exact measurable_inv.aemeasurable
  rw [Measure.modularCharacterFun_eq_haarScalarFactor ρ.inv q]
  simp only [hmap, Measure.haarScalarFactor_smul, Measure.haarScalarFactor_self, smul_eq_mul, mul_one]

end GlobalTheory.CompanionTheory.ModChar
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemidirectProductHomeomorphOfClosedComplement

section

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.TopGroup

theorem homeomorph_prod_of_closed_complements :
    ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
      [T2Space Q] [SecondCountableTopology Q] (N M : Subgroup Q),
      IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) →
      (∀ x, x ∈ N → x ∈ M → x = 1) →
      ∃ Φ : (N × M) ≃ₜ Q, ∀ p, Φ p = (p.1 : Q) * (p.2 : Q) := by
  intro Q _ _ _ _ _ _ N M hN hM hprod hint
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace M := hM.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N :=
    TopologicalSpace.Subtype.secondCountableTopology (N : Set Q)
  haveI : SecondCountableTopology M :=
    TopologicalSpace.Subtype.secondCountableTopology (M : Set Q)
  haveI : SigmaCompactSpace (N × M) := sigmaCompactSpace_of_locallyCompact_secondCountable
  letI act : MulAction (N × M) Q :=
    { smul := fun p q => (p.1 : Q) * q * (p.2 : Q)⁻¹
      one_smul := fun q => by
        change ((1 : N) : Q) * q * ((1 : M) : Q)⁻¹ = q
        simp
      mul_smul := fun p r q => by
        change ((p.1 * r.1 : N) : Q) * q * ((p.2 * r.2 : M) : Q)⁻¹ =
          (p.1 : Q) * ((r.1 : Q) * q * (r.2 : Q)⁻¹) * (p.2 : Q)⁻¹
        simp [mul_assoc] }
  have hsmul : ∀ (p : N × M) (q : Q), p • q = (p.1 : Q) * q * (p.2 : Q)⁻¹ := fun _ _ => rfl
  haveI : ContinuousSMul (N × M) Q := ⟨by
    have : (fun x : (N × M) × Q => x.1 • x.2) =
        fun x : (N × M) × Q => ((x.1.1 : Q)) * x.2 * ((x.1.2 : Q))⁻¹ := rfl
    rw [this]
    fun_prop⟩
  haveI : MulAction.IsPretransitive (N × M) Q := ⟨fun x y => by
    obtain ⟨n₁, hn₁, m₁, hm₁, rfl⟩ := hprod x
    obtain ⟨n₂, hn₂, m₂, hm₂, rfl⟩ := hprod y
    refine ⟨(⟨n₂ * n₁⁻¹, N.mul_mem hn₂ (N.inv_mem hn₁)⟩,
      ⟨m₂⁻¹ * m₁, M.mul_mem (M.inv_mem hm₂) hm₁⟩), ?_⟩
    rw [hsmul]
    simp [mul_assoc]⟩
  have hopen₀ : IsOpenMap (fun g : N × M => g • (1 : Q)) := isOpenMap_smul_of_sigmaCompact (1 : Q)
  let e : (N × M) ≃ₜ (N × M) := (Homeomorph.refl N).prodCongr (Homeomorph.inv M)
  let f : N × M → Q := fun p => (p.1 : Q) * (p.2 : Q)
  have hf : f = (fun g : N × M => g • (1 : Q)) ∘ e := by
    funext p
    change (p.1 : Q) * (p.2 : Q) = ((e p).1 : Q) * 1 * (((e p).2 : M) : Q)⁻¹
    simp [e]
  have hopen : IsOpenMap f := by
    rw [hf]
    exact hopen₀.comp e.isOpenMap
  have hcont : Continuous f := by fun_prop
  have hinj : Function.Injective f := by
    rintro ⟨⟨n₁, hn₁⟩, ⟨m₁, hm₁⟩⟩ ⟨⟨n₂, hn₂⟩, ⟨m₂, hm₂⟩⟩ h
    have h' : n₁ * m₁ = n₂ * m₂ := h
    have h1 : n₂⁻¹ * n₁ = m₂ * m₁⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, h']
    have h2 : n₂⁻¹ * n₁ = 1 :=
      hint _ (N.mul_mem (N.inv_mem hn₂) hn₁) (h1 ▸ M.mul_mem hm₂ (M.inv_mem hm₁))
    have h3 : n₁ = n₂ := by
      rw [inv_mul_eq_one] at h2
      exact h2.symm
    have h4 : m₁ = m₂ := by
      subst h3
      exact mul_left_cancel h'
    subst h3
    subst h4
    rfl
  have hsurj : Function.Surjective f := fun q => by
    obtain ⟨n, hn, m, hm, rfl⟩ := hprod q
    exact ⟨(⟨n, hn⟩, ⟨m, hm⟩), rfl⟩
  exact ⟨(Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen,
    fun _ => rfl⟩

end GlobalTheory.CompanionTheory.TopGroup
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemidirectProductHomeomorphOfClosedComplementStatement

section

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

theorem _root_.GlobalTheory.T.semidirect_product_homeomorph_of_closed_complement : ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] (N M : Subgroup Q), IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) → (∀ x, x ∈ N → x ∈ M → x = 1) → ∃ Φ : (N × M) ≃ₜ Q, ∀ p, Φ p = (p.1 : Q) * (p.2 : Q) := by
  first | exact @GlobalTheory.CompanionTheory.TopGroup.homeomorph_prod_of_closed_complements | exact GlobalTheory.CompanionTheory.TopGroup.homeomorph_prod_of_closed_complements | (intros; apply GlobalTheory.CompanionTheory.TopGroup.homeomorph_prod_of_closed_complements <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSemidirectProductFormula

section

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ModChar

theorem modularCharacterFun_semidirect :
    ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] [MeasurableSpace Q] [BorelSpace Q] (N M : Subgroup Q) [N.Normal] [LocallyCompactSpace N] [LocallyCompactSpace M], IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) → (∀ x, x ∈ N → x ∈ M → x = 1) → ∀ (νN : Measure N) (νM : Measure M), νN.IsHaarMeasure → νN.IsMulRightInvariant → νM.IsHaarMeasure → νM.IsMulRightInvariant → ∀ δ : Q →* ℝ≥0, (∀ n ∈ N, δ n = 1) → (∀ m ∈ M, νN.map (fun n : N => MulAut.conjNormal m n) = (δ m)⁻¹ • νN) → ∀ q : Q, Measure.modularCharacterFun q = δ q := by
  intro Q _ _ _ _ _ _ _ _ N M _ _ _ hN hM hgen hdisj νN νM hNH hNR hMH hMR δ hδN hδM q
  haveI := hNH
  haveI := hNR
  haveI := hMH
  haveI := hMR
  haveI : BorelSpace N := Subtype.borelSpace (fun x => x ∈ (N : Set Q))
  haveI : BorelSpace M := Subtype.borelSpace (fun x => x ∈ (M : Set Q))
  haveI : SecondCountableTopology N :=
    TopologicalSpace.Subtype.secondCountableTopology (N : Set Q)
  haveI : SecondCountableTopology M :=
    TopologicalSpace.Subtype.secondCountableTopology (M : Set Q)
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.semidirect_product_homeomorph_of_closed_complement Q N M hN hM hgen hdisj
  let Ψ : (M × N) ≃ₜ Q := (Homeomorph.prodComm M N).trans Φ
  have hΨ : ∀ p : M × N, Ψ p = (p.2 : Q) * (p.1 : Q) := fun p => hΦ (p.2, p.1)
  have hΨm : Measurable Ψ := Ψ.continuous.measurable
  set ρ : Measure Q := (νM.prod νN).map Ψ with hρ
  have hconj : ∀ (m : Q) (n : N), ((MulAut.conjNormal m n : N) : Q) = m * n * m⁻¹ :=
    fun m n => MulAut.conjNormal_apply m n
  haveI : IsFiniteMeasureOnCompacts ρ := by
    refine ⟨fun K hK => ?_⟩
    rw [hρ, show ((νM.prod νN).map Ψ) K = (νM.prod νN) (Ψ ⁻¹' K) from
      Ψ.toMeasurableEquiv.map_apply K]
    have : IsCompact (Ψ ⁻¹' K) := by
      have := hK.image Ψ.symm.continuous
      rwa [Ψ.symm.image_eq_preimage_symm, Ψ.symm_symm] at this
    exact this.measure_lt_top
  haveI : ρ.IsOpenPosMeasure := by
    refine ⟨fun U hU hne => ?_⟩
    rw [hρ, show ((νM.prod νN).map Ψ) U = (νM.prod νN) (Ψ ⁻¹' U) from
      Ψ.toMeasurableEquiv.map_apply U]
    exact (hU.preimage Ψ.continuous).measure_ne_zero _ (hne.preimage Ψ.surjective)
  haveI : ρ.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨⟨m₀, n₀⟩, rfl⟩ := Ψ.surjective g
    have hmul : Measurable (fun y : Q => y * Ψ (m₀, n₀)) := measurable_mul_const _
    have hc : Continuous (fun p : M × N => (MulAut.conjNormal (p.1 : Q) n₀ : N)) := by
      have h : Continuous (fun p : M × N => (p.1 : Q) * n₀ * (p.1 : Q)⁻¹) := by fun_prop
      exact Topology.IsInducing.subtypeVal.continuous_iff.2
        (h.congr fun p => (hconj _ _).symm)
    let T : M × N → M × N := fun p => (p.1 * m₀, p.2 * MulAut.conjNormal (p.1 : Q) n₀)
    have hT : MeasurePreserving T (νM.prod νN) (νM.prod νN) := by
      refine MeasurePreserving.skew_product (f := fun m : M => m * m₀)
        (g := fun (m : M) (n : N) => n * MulAut.conjNormal (m : Q) n₀)
        (measurePreserving_mul_right νM m₀) ?_ (Filter.Eventually.of_forall fun m => ?_)
      · exact (continuous_snd.mul hc).measurable
      · exact (measurePreserving_mul_right νN _).map_eq
    have hcomp : (fun y : Q => y * Ψ (m₀, n₀)) ∘ Ψ = Ψ ∘ T := by
      funext ⟨m, n⟩
      simp only [Function.comp, T, hΨ, Subgroup.coe_mul, hconj]
      group
    rw [hρ, Measure.map_map hmul hΨm, hcomp, ← Measure.map_map hΨm hT.measurable, hT.map_eq]
  refine GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_eq_of_map_left_mul Q ρ δ ?_ q
  intro q₀
  obtain ⟨⟨m₀, n₀⟩, rfl⟩ := Ψ.surjective q₀
  have hmul : Measurable (fun y : Q => Ψ (m₀, n₀) * y) := measurable_const_mul _
  have hcm : Continuous (fun n : N => (MulAut.conjNormal (m₀ : Q) n : N)) := by
    have h : Continuous (fun n : N => (m₀ : Q) * n * (m₀ : Q)⁻¹) := by fun_prop
    exact Topology.IsInducing.subtypeVal.continuous_iff.2
      (h.congr fun p => (hconj _ _).symm)
  let f₁ : M → M := fun m => m₀ * m
  let f₂ : N → N := fun n => n₀ * MulAut.conjNormal (m₀ : Q) n
  have hf₁ : Measurable f₁ := measurable_const_mul _
  have hf₂ : Measurable f₂ := (continuous_const.mul hcm).measurable
  have hcomp : (fun y : Q => Ψ (m₀, n₀) * y) ∘ Ψ = Ψ ∘ Prod.map f₁ f₂ := by
    funext ⟨m, n⟩
    simp only [Function.comp, Prod.map, f₁, f₂, hΨ, Subgroup.coe_mul, hconj]
    group
  have hνM : νM.map f₁ = νM := (measurePreserving_mul_left νM m₀).map_eq
  have hνN : νN.map f₂ = (δ m₀)⁻¹ • νN := by
    have : f₂ = (fun n : N => n₀ * n) ∘ (fun n : N => (MulAut.conjNormal (m₀ : Q) n : N)) := rfl
    rw [this, ← Measure.map_map (measurable_const_mul _) hcm.measurable, hδM _ m₀.2,
      Measure.map_smul (c := (δ m₀)⁻¹) (f := fun x : N => n₀ * x)
        (measurable_const_mul _).aemeasurable,
      (measurePreserving_mul_left νN n₀).map_eq]
  have hδ : δ (Ψ (m₀, n₀)) = δ m₀ := by
    rw [hΨ]
    simp [map_mul, hδN _ n₀.2]
  rw [hρ, Measure.map_map hmul hΨm, hcomp,
    ← Measure.map_map hΨm (hf₁.prodMap hf₂), ← Measure.map_prod_map νM νN hf₁ hf₂, hνM, hνN,
    Measure.prod_smul_right,
    Measure.map_smul (c := (δ m₀)⁻¹) (f := Ψ) hΨm.aemeasurable, hδ]

end GlobalTheory.CompanionTheory.ModChar
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSemidirectProductFormulaStatement

section

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

theorem _root_.GlobalTheory.T.haar_measure_semidirect_product_formula : ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] [MeasurableSpace Q] [BorelSpace Q] (N M : Subgroup Q) [N.Normal] [LocallyCompactSpace N] [LocallyCompactSpace M], IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) → (∀ x, x ∈ N → x ∈ M → x = 1) → ∀ (νN : Measure N) (νM : Measure M), νN.IsHaarMeasure → νN.IsMulRightInvariant → νM.IsHaarMeasure → νM.IsMulRightInvariant → ∀ δ : Q →* ℝ≥0, (∀ n ∈ N, δ n = 1) → (∀ m ∈ M, νN.map (fun n : N => MulAut.conjNormal m n) = (δ m)⁻¹ • νN) → ∀ q : Q, Measure.modularCharacterFun q = δ q := by
  first | exact @GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_semidirect | exact GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_semidirect | (intros; apply GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_semidirect <;> assumption)
end
end
