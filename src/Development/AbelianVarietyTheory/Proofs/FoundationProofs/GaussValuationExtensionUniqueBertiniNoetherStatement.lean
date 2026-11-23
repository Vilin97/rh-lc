module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetPrimesMemValuationSubringOver
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMonicIrreducibleIntegralPrimitiveElement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubringNoMonicFactorisationSpecialisation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussExtensionCoeffMemNonunits
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringLeOfResidueIndependent

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetPrimesMemValuationSubringOverStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_finset_primes_mem_valuationSubring_over : ∀ {F : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] (s : Finset F), ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ x ∈ s, x ∈ V := by
  first | exact @GlobalTheory.exists_finset_primes_forall_mem_valuationSubring | exact GlobalTheory.exists_finset_primes_forall_mem_valuationSubring | (intros; apply GlobalTheory.exists_finset_primes_forall_mem_valuationSubring <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMonicIrreducibleIntegralPrimitiveElementStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_monic_irreducible_integral_primitive_element : ∀ {F : Type} [Field F] [CharZero F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ (Φ : Polynomial (Polynomial F)) (ω : L), Φ.Monic ∧ Irreducible Φ ∧ Φ.eval₂ (Polynomial.aeval t).toRingHom ω = 0 ∧ ∀ x : L, ∃ Q : Polynomial F, Q ≠ 0 ∧ ∃ R : Polynomial (Polynomial F), Polynomial.aeval t Q * x = R.eval₂ (Polynomial.aeval t).toRingHom ω := by
  first | exact @GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive | exact GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive | (intros; apply GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubringNoMonicFactorisationSpecialisationStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_subring_no_monic_factorisation_specialisation : ∀ {F : Type} [Field F] [IsAlgClosed F] (Φ : Polynomial (Polynomial F)), Φ.Monic → Irreducible Φ → ∃ s : Finset F, ∃ Ψ : Polynomial (Polynomial (Subring.closure (s : Set F))), Ψ.map (Polynomial.mapRingHom (Subring.closure (s : Set F)).subtype) = Φ ∧ ∀ (k : Type) [Field k] (φ : Subring.closure (s : Set F) →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic → A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0 := by
  first | exact @GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation | exact GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation | (intros; apply GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussExtensionCoeffMemNonunitsStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.gaussExtension_coeff_mem_nonunits_alt : ∀ {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L) (V : ValuationSubring F) (W : ValuationSubring L), (∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) → (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1) → ∀ (Ψ : Polynomial (Polynomial V)) (ω : L), Ψ.Monic → (Ψ.map (Polynomial.mapRingHom V.subtype)).eval₂ (Polynomial.aeval t).toRingHom ω = 0 → (∀ (k : Type) [Field k] (φ : V →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic → A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0) → ∀ R : Polynomial (Polynomial F), R.natDegree < Ψ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits := by
  first | exact @GlobalTheory.gaussExtension_coeff_mem_nonunits | exact GlobalTheory.gaussExtension_coeff_mem_nonunits | (intros; apply GlobalTheory.gaussExtension_coeff_mem_nonunits <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringLeOfResidueIndependentStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.valuationSubring_le_of_residue_independent : ∀ {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L) (V : ValuationSubring F) (Φ : Polynomial (Polynomial F)) (ω : L), Φ.Monic → (∀ i j, (Φ.coeff i).coeff j ∈ V) → Φ.eval₂ (Polynomial.aeval t).toRingHom ω = 0 → (∀ x : L, ∃ Q : Polynomial F, Q ≠ 0 ∧ ∃ R : Polynomial (Polynomial F), Polynomial.aeval t Q * x = R.eval₂ (Polynomial.aeval t).toRingHom ω) → ∀ W₁ W₂ : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W₁ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W₁.valuation (Polynomial.aeval t P) = 1)) → ((∀ a : F, algebraMap F L a ∈ W₂ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W₂.valuation (Polynomial.aeval t P) = 1)) → (∀ R : Polynomial (Polynomial F), R.natDegree < Φ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W₁.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits) → W₁ ≤ W₂ := by
  first | exact @GlobalTheory.BertiniNoether.le_of_residue_independent | exact GlobalTheory.BertiniNoether.le_of_residue_independent | (intros; apply GlobalTheory.BertiniNoether.le_of_residue_independent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussValuationExtensionUniqueBertiniNoether

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.BertiniNoether

theorem gauss_extension_unique : ∀ {F : Type} [Field F] [CharZero F] [IsAlgClosed F] [Algebra.IsAlgebraic ℚ F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W₁ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W₁.valuation (Polynomial.aeval t P) = 1)) → ((∀ a : F, algebraMap F L a ∈ W₂ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W₂.valuation (Polynomial.aeval t P) = 1)) → W₁ = W₂ := by
  intro F _ _ _ _ L _ _ t ht hfin
  obtain ⟨Φ, ω, hmon, hirr, hroot, hspan⟩ := GlobalTheory.T.exists_monic_irreducible_integral_primitive_element t ht hfin
  obtain ⟨s, Ψ₀, hΨ₀, hgr⟩ := GlobalTheory.T.exists_subring_no_monic_factorisation_specialisation Φ hmon hirr
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_finset_primes_mem_valuationSubring_over s
  refine ⟨S, fun q hq hqS V hV W₁ W₂ h₁ h₂ => ?_⟩
  have hcl : Subring.closure (s : Set F) ≤ V.toSubring :=
    (Subring.closure_le).2 (fun x hx => hS q hq hqS V hV x hx)
  let ι : Subring.closure (s : Set F) →+* V :=
    { toFun := fun x => ⟨x.1, hcl x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hcomp : V.subtype.comp ι = (Subring.closure (s : Set F)).subtype := RingHom.ext fun _ => rfl
  set Ψ := Ψ₀.map (Polynomial.mapRingHom ι) with hΨdef
  have hΨ : Ψ.map (Polynomial.mapRingHom V.subtype) = Φ := by
    rw [hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp, hcomp, hΨ₀]
  have hinj : Function.Injective (Polynomial.mapRingHom V.subtype) :=
    Polynomial.map_injective _ (fun a b h => Subtype.ext h)
  have hΨmon : Ψ.Monic := Polynomial.monic_of_injective hinj (by rw [hΨ]; exact hmon)
  have hdeg : Ψ.natDegree = Φ.natDegree := by
    rw [← hΨ, Polynomial.natDegree_map_eq_of_injective hinj]
  have hgrV : ∀ (k : Type) [Field k] (φ : V →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic →
      A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0 := by
    intro k _ φ A B hA hB hAB
    refine hgr k (φ.comp ι) A B hA hB ?_
    rw [hAB, hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp]
  have hcoef : ∀ i j, (Φ.coeff i).coeff j ∈ V := by
    intro i j; rw [← hΨ]; simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
    exact ((Ψ.coeff i).coeff j).2
  have hrootΨ : (Ψ.map (Polynomial.mapRingHom V.subtype)).eval₂ (Polynomial.aeval t).toRingHom ω = 0 := by
    rw [hΨ]; exact hroot
  have conv : ∀ W : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1)) →
      ((∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1)) :=
    fun W h => ⟨h.1, fun P hP ⟨i, h0, hv, hinv⟩ => h.2 P hP ⟨i, hv, h0, hinv⟩⟩
  have key : ∀ W : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1)) →
      ∀ R : Polynomial (Polynomial F), R.natDegree < Φ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits := by
    intro W hW R hR
    exact GlobalTheory.T.gaussExtension_coeff_mem_nonunits_alt t V W hW.1 hW.2 Ψ ω hΨmon hrootΨ hgrV R (hdeg ▸ hR)
  exact le_antisymm (GlobalTheory.T.valuationSubring_le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₁ W₂ (conv W₁ h₁) (conv W₂ h₂) (key W₁ (conv W₁ h₁)))
    (GlobalTheory.T.valuationSubring_le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₂ W₁ (conv W₂ h₂) (conv W₁ h₁) (key W₂ (conv W₂ h₂)))

end GlobalTheory.BertiniNoether
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussValuationExtensionUniqueBertiniNoetherStatement

section

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.gauss_valuation_extension_unique_bertiniNoether : ∀ {F : Type} [Field F] [CharZero F] [IsAlgClosed F] [Algebra.IsAlgebraic ℚ F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W₁ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W₁.valuation (Polynomial.aeval t P) = 1)) → ((∀ a : F, algebraMap F L a ∈ W₂ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W₂.valuation (Polynomial.aeval t P) = 1)) → W₁ = W₂ := by
  first | exact @GlobalTheory.BertiniNoether.gauss_extension_unique | exact GlobalTheory.BertiniNoether.gauss_extension_unique | (intros; apply GlobalTheory.BertiniNoether.gauss_extension_unique <;> assumption)
end
end
