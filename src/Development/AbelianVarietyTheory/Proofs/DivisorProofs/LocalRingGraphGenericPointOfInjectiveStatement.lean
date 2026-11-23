module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgEquivFractionFieldOfLocalRingOfVarietyPStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphLocalRingRegularParamsAndDimStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfVarietyPointTensorGraphLocalizationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormsGraphLocalRingFreelyGenerated

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTranscendenceBasisOverConstEqOfAlgEquiv

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem GlobalTheory.trBasis_card_eq_of_algEquiv : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ] (e : K ≃ₐ[ℂ] κ)
  (n k : ℕ) (x : Fin n → K) (z : Fin k → κ),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ) z → n = k := by
  intro K κ _ _ _ _ e n k x z hx hz
  have eK : (algebraMap ℂ K).toAlgebra = (inferInstance : Algebra ℂ K) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have eκ : (algebraMap ℂ κ).toAlgebra = (inferInstance : Algebra ℂ κ) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  unfold TrBasis at hx hz
  rw [eK] at hx
  rw [eκ] at hz
  have h1 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hz
  rw [Cardinal.mk_fin, e.trdeg_eq] at h1
  rw [Cardinal.mk_fin, ← h1] at h2
  exact_mod_cast h2.symm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTranscendenceBasisOverConstEqOfAlgEquivStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.card_transcendenceBasisOverConst_eq_of_algEquiv : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ] (e : K ≃ₐ[ℂ] κ)
  (n k : ℕ) (x : Fin n → K) (z : Fin k → κ),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ) z → n = k := by
  first | exact @GlobalTheory.trBasis_card_eq_of_algEquiv | exact GlobalTheory.trBasis_card_eq_of_algEquiv | (intros; apply GlobalTheory.trBasis_card_eq_of_algEquiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeOfLocalRingOfVarietyPoint

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory

theorem essFiniteType_of_isLocModel : ∀ {K : Type} [Field K] [Algebra ℂ K] (R : Subring K),
    IsLocModel (algebraMap ℂ K) R → Algebra.EssFiniteType ℂ K := by
  intro K _ _ R h
  letI : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R h.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := h.essFiniteType
  haveI : IsScalarTower ℂ R K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsFractionRing R K := IsFractionRing.of_field R K fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h.frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by
      show z = a / b
      rw [eq_div_iff hb0, e]⟩
  haveI : Algebra.EssFiniteType R K :=
    Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors R)
  exact Algebra.EssFiniteType.comp ℂ R K

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeOfLocalRingOfVarietyPointStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.essFiniteType_of_localRingOfVarietyPoint : ∀ {K : Type} [Field K] [Algebra ℂ K] (R : Subring K),
  IsLocModel (algebraMap ℂ K) R → Algebra.EssFiniteType ℂ K := by
  first | exact @GlobalTheory.essFiniteType_of_isLocModel | exact GlobalTheory.essFiniteType_of_isLocModel | (intros; apply GlobalTheory.essFiniteType_of_isLocModel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormsGraphLocalRingFreelyGeneratedStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.topForms_graphLocalRing_freelyGenerated : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K]
  [Algebra ℂ κ'] [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ') (n k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ')
  (hc : ∀ a, algebraMap ℂ L a ∈ GlobalTheory.DiagLoc.loc L σ),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' →
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' →
  IsFreeGen (GlobalTheory.DiagLoc.loc L σ) (dForm ((algebraMap ℂ L).codRestrict (GlobalTheory.DiagLoc.loc L σ) hc)
    (Fin.append (fun i => GlobalTheory.DiagLoc.toLoc L σ (1 ⊗ₜ[ℂ] τ' i)) (fun i => GlobalTheory.DiagLoc.toLoc L σ (x i ⊗ₜ[ℂ] 1)))) := by
  first | exact @GlobalTheory.DiagLoc.isFreeGen_dForm_graph | exact GlobalTheory.DiagLoc.isFreeGen_dForm_graph | (intros; apply GlobalTheory.DiagLoc.isFreeGen_dForm_graph <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingGraphGenericPointOfInjective

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair


open GlobalTheory.DiagLoc in
theorem localRing_graph_of_injective : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  Function.Injective π → (∀ g : K, ∃ a b : R, (b : K) ≠ 0 ∧ g * b = a) →
  IsLocModel (algebraMap ℂ K) R → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → 1 ≤ k →
  ∃ (Q : Subring L) (hQ : IsLocModel (algebraMap ℂ L) Q), letI := hQ.isLocalRing; ∃ z : Fin k → Q,
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) ∧ ringKrullDim Q = k ∧
    (∀ g : K, g ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1)) ∧
    (∀ b : κ', b ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      ∃ q : Q, IsUnit q ∧ (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) ∧
    (∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
      ∃ q : Q, (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ∧ q ∈ IsLocalRing.maximalIdeal Q ^ M) ∧
    ∃ (y : Fin (k' + n) → Q) (q : Q), IsFreeGen Q (dForm ((algebraMap ℂ L).codRestrict Q hQ.const_mem) y) ∧ IsUnit q ∧
      dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) = (q : L) • dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ' hz hπc hπf hπi hRf hR hκ' hk
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_algEquiv_fractionField_of_localRingOfVarietyPoint R π hR hπc hπf hπi
  obtain ⟨z, hz⟩ := hz
  obtain rfl : n = k := GlobalTheory.T.card_transcendenceBasisOverConst_eq_of_algEquiv e n k x z hx hz
  have hK : Algebra.EssFiniteType ℂ K := GlobalTheory.T.essFiniteType_of_localRingOfVarietyPoint R hR
  obtain ⟨O', hO'⟩ := hκ'
  have hκ'f : Algebra.EssFiniteType ℂ κ' := GlobalTheory.T.essFiniteType_of_localRingOfVarietyPoint O' hO'
  set σ : K →ₐ[ℂ] κ' := ρ.comp e.toAlgHom with hσ
  have hQ : IsLocModel (algebraMap ℂ L) (loc L σ) := GlobalTheory.T.isLocalRingOfVarietyPoint_tensorGraphLocalization σ hK hκ'f
  obtain ⟨hm, hdim⟩ := GlobalTheory.T.graphLocalRing_regular_params_and_dim (L := L) σ n x hK hκ'f hx
  have hsum : ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'),
      algebraMap (K ⊗[ℂ] κ') L (∑ i, (a i : K) ⊗ₜ[ℂ] b i) =
        ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i) := fun l a b => map_sum _ _ _
  have hprod : ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'),
      Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ') (∑ i, (a i : K) ⊗ₜ[ℂ] b i) =
        ∑ i, ρ (π (a i)) * b i := by
    intro l a b

    simp [map_sum, σ, he]
  refine ⟨loc L σ, hQ, fun i => toLoc L σ (x i ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] σ (x i)), hm, hdim, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    refine ⟨toLoc L σ (g ⊗ₜ 1), ?_, rfl⟩
    refine IsUnit.map _ ?_
    exact ((IsUnit.mk0 g hg).map (Algebra.TensorProduct.includeLeft (R := ℂ) (S := ℂ) (B := κ')))
  · intro b hb
    refine ⟨toLoc L σ (1 ⊗ₜ b), ?_, rfl⟩
    refine IsUnit.map _ ?_
    exact ((IsUnit.mk0 b hb).map (Algebra.TensorProduct.includeRight (R := ℂ) (A := K)))
  · intro l a b hne
    refine ⟨toLoc L σ (∑ i, (a i : K) ⊗ₜ[ℂ] b i), ?_, ?_⟩
    · have hs : (∑ i, (a i : K) ⊗ₜ[ℂ] b i) ∈ (ker σ).primeCompl := by
        intro hmem
        exact hne ((hprod l a b).symm.trans hmem)
      exact IsLocalization.map_units (loc L σ) (⟨_, hs⟩ : (ker σ).primeCompl)
    · simp only [coe_toLoc]
      exact hsum l a b
  · intro M l a b hJ
    refine ⟨toLoc L σ (∑ i, (a i : K) ⊗ₜ[ℂ] b i), by simp only [coe_toLoc]; exact hsum l a b, ?_⟩
    let E : K ⊗[ℂ] κ' ≃ₐ[ℂ] κ ⊗[ℂ] κ' := Algebra.TensorProduct.congr e AlgEquiv.refl
    have hE : (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')).comp E.toAlgHom =
        Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ') := by
      apply Algebra.TensorProduct.ext'
      intro g b
      simp [E, σ]
    have hker : ker σ = (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))).comap
        (E : K ⊗[ℂ] κ' →+* κ ⊗[ℂ] κ') := by
      ext s
      simp only [mem_ker, Ideal.mem_comap, RingHom.mem_ker]
      rw [← hE]
      rfl
    have hEs : E (∑ i, (a i : K) ⊗ₜ[ℂ] b i) = ∑ i, π (a i) ⊗ₜ[ℂ] b i := by
      simp [E, he]
    have hmem : (∑ i, (a i : K) ⊗ₜ[ℂ] b i) ∈ ker σ ^ M := by
      have h1 : (∑ i, (a i : K) ⊗ₜ[ℂ] b i) = E.symm (∑ i, π (a i) ⊗ₜ[ℂ] b i) := by
        rw [← hEs, AlgEquiv.symm_apply_apply]
      have h2 := Ideal.mem_map_of_mem (E.symm : κ ⊗[ℂ] κ' →+* K ⊗[ℂ] κ') hJ
      have h3 : (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))).comap
          (E : K ⊗[ℂ] κ' →+* κ ⊗[ℂ] κ') =
          (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))).map
          (E.symm : κ ⊗[ℂ] κ' →+* K ⊗[ℂ] κ') := by
        ext s
        rw [Ideal.mem_comap, Ideal.mem_map_iff_of_surjective (E.symm : κ ⊗[ℂ] κ' →+* K ⊗[ℂ] κ')
          E.symm.surjective]
        constructor
        · intro hs
          exact ⟨E s, hs, by simp⟩
        · rintro ⟨t, ht, rfl⟩
          simpa using ht
      rw [h1, hker, h3, ← Ideal.map_pow]
      exact h2
    have := Ideal.mem_map_of_mem (toLoc L σ) hmem
    rw [Ideal.map_pow, map_ker] at this
    exact this
  · refine ⟨_, 1, GlobalTheory.T.topForms_graphLocalRing_freelyGenerated σ n k' x τ' hQ.const_mem hK hκ'f hx hτ', isUnit_one, ?_⟩
    rw [Submonoid.coe_one, one_smul]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

end GlobalTheory.FieldPair
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingGraphGenericPointOfInjectiveStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.localRing_graph_generic_point_of_injective : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  Function.Injective π → (∀ g : K, ∃ a b : R, (b : K) ≠ 0 ∧ g * b = a) →
  IsLocModel (algebraMap ℂ K) R → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → 1 ≤ k →
  ∃ (Q : Subring L) (hQ : IsLocModel (algebraMap ℂ L) Q), letI := hQ.isLocalRing; ∃ z : Fin k → Q,
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) ∧ ringKrullDim Q = k ∧
    (∀ g : K, g ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1)) ∧
    (∀ b : κ', b ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      ∃ q : Q, IsUnit q ∧ (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) ∧
    (∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
      ∃ q : Q, (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ∧ q ∈ IsLocalRing.maximalIdeal Q ^ M) ∧
    ∃ (y : Fin (k' + n) → Q) (q : Q), IsFreeGen Q (dForm ((algebraMap ℂ L).codRestrict Q hQ.const_mem) y) ∧ IsUnit q ∧
      dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) = (q : L) • dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  first | exact @GlobalTheory.FieldPair.localRing_graph_of_injective | exact GlobalTheory.FieldPair.localRing_graph_of_injective | (intros; apply GlobalTheory.FieldPair.localRing_graph_of_injective <;> assumption)
end
end
