module

public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteEpsilonOperator
public import Formalism.LocalToGlobal.IndefiniteReal.TransferStatement
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalIdempotentCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepRealisingCharOfMultiplicityOne
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepRealisingCharOfMultiplicityOneStatement

section

@[expose] public section

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem _root_.GlobalTheory.T.exists_rep_realising_char_of_multiplicity_one : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (χ : G → K), IsAbsIrrChar χ → ∀ (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ), ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) = (Fintype.card P : K) → ∃ (n : ℕ) (τ : Representation K G (Fin n → K)), 0 < n ∧ Function.Surjective τ.asAlgebraHom ∧ ∀ g, LinearMap.trace K (Fin n → K) (τ g) = χ g := by
  first | exact @GlobalTheory.MultOneRealised.exists_rep_of_mult_one | exact GlobalTheory.MultOneRealised.exists_rep_of_mult_one | (intros; apply GlobalTheory.MultOneRealised.exists_rep_of_mult_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSet

section

@[expose] public section

noncomputable section

namespace GlobalTheory.GoodSetOfChars

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem eS_eq_chiIdem {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G) (s : T.S) :
    Formalism.MainNotions.PrimeDegreeVariant.eS T s = chiIdem fun g => LinearMap.trace K (T.W s) (T.tau s g) := by
  unfold Formalism.MainNotions.PrimeDegreeVariant.eS chiIdem
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [LinearMap.trace_one]

theorem exists_goodSet (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K))
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P0 : Formalism.MainNotions.PrimeDegreeVariant.Pair K G) [Fintype P0.H]
    (h1 : ∀ χ ∈ X, ∑ h : P0.H, χ (h : G) * (((P0.chi h)⁻¹ : Kˣ) : K) = (Fintype.card P0.H : K)) :
    ∃ T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G,
      (∀ χ, χ ∈ X ↔ ∃ s, χ = fun g => LinearMap.trace K (T.W s) (T.tau s g)) ∧
        Formalism.MainNotions.PrimeDegreeVariant.M1 T P0 ∧ Formalism.MainNotions.PrimeDegreeVariant.eG T = idemOf X := by
  classical
  have key : ∀ s : X, ∃ (n : ℕ) (τ : Representation K G (Fin n → K)), 0 < n ∧
      Function.Surjective τ.asAlgebraHom ∧ ∀ g, LinearMap.trace K (Fin n → K) (τ g) = (s : G → K) g :=
    fun s => GlobalTheory.T.exists_rep_realising_char_of_multiplicity_one K G s (hX s s.2) P0.H P0.chi (h1 s s.2)
  choose n τ hn hs ht using key
  have ht' : ∀ s : X, (fun g => LinearMap.trace K (Fin (n s) → K) (τ s g)) = (s : G → K) := fun s => funext (ht s)
  let T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G :=
    { S := X
      W := fun s => Fin (n s) → K
      ntW := fun s => by
        have : Nonempty (Fin (n s)) := ⟨⟨0, hn s⟩⟩
        infer_instance
      tau := τ
      irr := hs
      inj := fun a b hab => Subtype.ext (by rw [← ht' a, ← ht' b]; exact hab) }
  refine ⟨T, fun χ => ⟨fun h => ⟨⟨χ, h⟩, (ht' ⟨χ, h⟩).symm⟩, ?_⟩, fun s => ?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact (ht' s).symm ▸ s.2
  · have h2 := (GlobalTheory.CuspidalIdempotentCharacters.finrank_eq_one_iff (τ s) P0.H P0.chi).2 (by
      simp_rw [ht s]
      rw [h1 _ s.2, Nat.card_eq_fintype_card])
    rw [← GlobalTheory.CuspidalIdempotentCharacters.eps_eq_lvlIdem] at h2
    exact h2
  · unfold Formalism.MainNotions.PrimeDegreeVariant.eG idemOf
    rw [← Finset.sum_coe_sort X]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [eS_eq_chiIdem]
    exact congrArg chiIdem (ht' s)

end GlobalTheory.GoodSetOfChars
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFamilyGivenCharactersMultiplicityOne

section

@[expose] public section

noncomputable section

open Formalism.L2.DIV NumberField

namespace GlobalTheory.GoodFamilyOfChars

theorem nOf_eq_nS {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G) (P0 : Subgroup G)
    [Fintype P0] (ψ0 : P0 →* Kˣ) (s : T.S) :
    Formalism.IndefR.IndefiniteEpsilonOperator.nOf (T.tau s) ⟨P0, ψ0⟩ = Formalism.MainNotions.PrimeDegreeVariant.nS T ⟨P0, ψ0⟩ s := by
  classical
  have e : Formalism.IndefR.IndefiniteEpsilonOperator.epOp (T.tau s) ⟨P0, ψ0⟩ = (T.tau s).asAlgebraHom (Formalism.MainNotions.PrimeDegreeVariant.eps ⟨P0, ψ0⟩) := by

    rw [Formalism.MainNotions.PrimeDegreeVariant.eps, map_smul, map_sum, Formalism.IndefR.IndefiniteEpsilonOperator.epOp]
    congr 1
    have hsub : (Finset.univ.map (Function.Embedding.subtype (· ∈ P0))) ⊆ Finset.univ := Finset.subset_univ _
    rw [← Finset.sum_subset hsub (fun x _ hx => by
      have : x ∉ P0 := fun h => hx (Finset.mem_map.2 ⟨⟨x, h⟩, Finset.mem_univ _, rfl⟩)
      simp [this]), Finset.sum_map]
    simp only [Function.Embedding.subtype_apply]
    refine Finset.sum_congr (by convert rfl) fun h _ => ?_
    simp [h.2, Representation.asAlgebraHom_of, map_inv]
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.nOf Formalism.IndefR.IndefiniteEpsilonOperator.epSp Formalism.MainNotions.PrimeDegreeVariant.nS
  rw [e]

variable {K : Type} [Field K] {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module K W]

theorem asAlg_mem (τ : Representation K G W) (U : Submodule K W) (hU : ∀ g : G, ∀ w ∈ U, τ g w ∈ U)
    (a : MonoidAlgebra K G) : ∀ w ∈ U, τ.asAlgebraHom a w ∈ U := by
  induction a using MonoidAlgebra.induction_on with
  | of g => intro w hw; simpa [Representation.asAlgebraHom_of] using hU g w hw
  | add a b ha hb => intro w hw; simpa using U.add_mem (ha w hw) (hb w hw)
  | smul r a ha => intro w hw; simpa using U.smul_mem r (ha w hw)

theorem asAlg_comm (τ : Representation K G W) (f : W →ₗ[K] W) (hf : ∀ g : G, f ∘ₗ τ g = τ g ∘ₗ f)
    (a : MonoidAlgebra K G) : f * τ.asAlgebraHom a = τ.asAlgebraHom a * f := by
  induction a using MonoidAlgebra.induction_on with
  | of g => simpa [Representation.asAlgebraHom_of, Module.End.mul_eq_comp] using hf g
  | add a b ha hb => simp [map_add (f := _), mul_add, add_mul, ha, hb]
  | smul r a ha => simp [map_smul, ha]

theorem irr_of_surj (τ : Representation K G W) (hs : Function.Surjective τ.asAlgebraHom)
    (U : Submodule K W) (hU : ∀ g : G, ∀ w ∈ U, τ g w ∈ U) : U = ⊥ ∨ U = ⊤ := by
  classical
  by_cases h : U = ⊥
  · exact Or.inl h
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K W, φ w ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff K w).1 hc)
  rw [eq_top_iff]
  intro v _
  obtain ⟨a, ha⟩ := hs ((φ w)⁻¹ • φ.smulRight v)
  have := asAlg_mem τ U hU a w hw
  rw [ha] at this
  simpa [hφ] using this

theorem scalar_of_surj (τ : Representation K G W) (hs : Function.Surjective τ.asAlgebraHom)
    (f : W →ₗ[K] W) (hf : ∀ g : G, f ∘ₗ τ g = τ g ∘ₗ f) : ∃ c : K, f = c • LinearMap.id := by
  have hc : f ∈ Set.center (Module.End K W) := by
    rw [Semigroup.mem_center_iff]
    intro e
    obtain ⟨a, rfl⟩ := hs e
    exact (asAlg_comm τ f hf a).symm
  obtain ⟨α, hα, rfl⟩ := Module.End.mem_center_iff.1 hc
  exact ⟨α, by ext x; simp⟩

theorem exists_goodFamily : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ (P0 : Subgroup G) [Fintype P0] (ψ0 : P0 →* Kˣ), (∀ χ ∈ X, ∑ h : P0, χ (h : G) * (((ψ0 h)⁻¹ : Kˣ) : K) = (Fintype.card P0 : K)) → ∃ (S : Type) (_ : Fintype S) (Ws : S → Type) (_ : ∀ s, AddCommGroup (Ws s)) (_ : ∀ s, Module K (Ws s)) (_ : ∀ s, FiniteDimensional K (Ws s)) (τ : ∀ s, Representation K G (Ws s)), Formalism.IndefR.TransferLatticeStatement.IsGood τ ∧ (∀ χ : G → K, χ ∈ X ↔ ∃ s, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = χ) ∧ Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩ := by
  intro K _ _ G _ _ X hX P0 _ ψ0 h1
  obtain ⟨T, hT, hM, -⟩ := GlobalTheory.GoodSetOfChars.exists_goodSet K G X hX ⟨P0, ψ0⟩ h1
  have hch : ∀ s, Formalism.IndefR.TransferLatticeStatement.charOf (T.tau s) = fun g => LinearMap.trace K (T.W s) (T.tau s g) := fun s => rfl
  have hmem : ∀ s, Formalism.IndefR.TransferLatticeStatement.charOf (T.tau s) ∈ X := fun s => (hT _).2 ⟨s, (hch s)⟩
  refine ⟨T.S, inferInstance, T.W, inferInstance, inferInstance, inferInstance, T.tau,
    ⟨fun s => inferInstance, fun s U hU => irr_of_surj (T.tau s) (T.irr s) U hU,
     fun s f hf => scalar_of_surj (T.tau s) (T.irr s) f hf, fun s t h => T.inj h⟩,
    fun χ => ⟨fun h => ?_, ?_⟩, fun s => ?_⟩
  · obtain ⟨s, hs⟩ := (hT χ).1 h
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, rfl⟩
    exact hmem s
  · rw [nOf_eq_nS]
    exact hM s

end GlobalTheory.GoodFamilyOfChars
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFamilyGivenCharactersMultiplicityOneStatement

section

@[expose] public section

open Formalism.L2.DIV NumberField

theorem _root_.GlobalTheory.T.exists_goodFamily_given_characters_multiplicityOne : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ (P0 : Subgroup G) [Fintype P0] (ψ0 : P0 →* Kˣ), (∀ χ ∈ X, ∑ h : P0, χ (h : G) * (((ψ0 h)⁻¹ : Kˣ) : K) = (Fintype.card P0 : K)) → ∃ (S : Type) (_ : Fintype S) (Ws : S → Type) (_ : ∀ s, AddCommGroup (Ws s)) (_ : ∀ s, Module K (Ws s)) (_ : ∀ s, FiniteDimensional K (Ws s)) (τ : ∀ s, Representation K G (Ws s)), Formalism.IndefR.TransferLatticeStatement.IsGood τ ∧ (∀ χ : G → K, χ ∈ X ↔ ∃ s, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = χ) ∧ Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩ := by
  first | exact @GlobalTheory.GoodFamilyOfChars.exists_goodFamily | exact GlobalTheory.GoodFamilyOfChars.exists_goodFamily | (intros; apply GlobalTheory.GoodFamilyOfChars.exists_goodFamily <;> assumption)
end
end
