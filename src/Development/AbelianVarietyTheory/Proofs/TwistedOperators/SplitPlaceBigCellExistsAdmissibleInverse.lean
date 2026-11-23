module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledVacuumLatticeStabilizerBlocksKeepLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleLiftSplitPlaceConjugatePairStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfBlockSumExistsInverseIntegralSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralBlocksLeftInverseIsUnitDetSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLocalBasisConjugatesOfKeepsLatticeAtPlacStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAtSplitPlaceLocalBasesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLeftInverseLiftingSplitPlaceInverses

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.MatrixLeftInverseLift

theorem matrix_left_inverse_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (π₁ π₂ : AE F E →+* Fv F v), (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) → (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ K : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) (K - 1) →
  ∀ N₁ N₂ : Matrix (Fin d) (Fin d) (Fv F v), N₁ * K.map π₁ = 1 → N₂ * K.map π₂ = 1 →
  ∃ M : Matrix (Fin d) (Fin d) (AE F E), M * K = 1 ∧ M.map π₁ = N₁ ∧ M.map π₂ = N₂ := by
  intro F E _ _ _ _ _ d v π₁ π₂ hinj hsurj K hK N₁ N₂ h₁ h₂
  choose Z hZA hZ₁ hZ₂ using fun i j => hsurj ((N₁ - 1) i j) ((N₂ - 1) i j)
  let Zm : Matrix (Fin d) (Fin d) (AE F E) := Matrix.of Z
  have hZm : ∀ u, evFin F v u = 0 → u • Zm = 0 := by
    intro u hu; ext i j; simpa [Zm] using hZA i j u hu
  have hmap : ∀ (π : AE F E →+* Fv F v) (N : Matrix (Fin d) (Fin d) (Fv F v)),
      (∀ i j, π (Z i j) = (N - 1) i j) → (Zm + 1).map π = N := by
    intro π N hπ
    ext i j
    have h := hπ i j
    by_cases hij : i = j
    · subst hij; simp [Zm, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, h]
    · simp [Zm, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, hij, h]
  have hM₁ := hmap π₁ N₁ hZ₁
  have hM₂ := hmap π₂ N₂ hZ₂
  refine ⟨Zm + 1, ?_, hM₁, hM₂⟩
  have hdecomp : (Zm + 1) * K - 1 = Zm * (K - 1) + Zm + (K - 1) := by
    rw [Matrix.mul_sub, Matrix.mul_one, add_mul, one_mul]; abel
  have hAt : ∀ u, evFin F v u = 0 → u • ((Zm + 1) * K - 1) = 0 := by
    intro u hu
    rw [hdecomp, smul_add, smul_add, ← Matrix.mul_smul, hK u hu, hZm u hu]; simp
  have hπ : ∀ (π : AE F E →+* Fv F v) (N : Matrix (Fin d) (Fin d) (Fv F v)),
      (Zm + 1).map π = N → N * K.map π = 1 → ((Zm + 1) * K - 1).map π = 0 := by
    intro π N hM hN
    have : π.mapMatrix ((Zm + 1) * K - 1) = π.mapMatrix (Zm + 1) * π.mapMatrix K - 1 := by
      rw [map_sub, map_mul, map_one]
    change π.mapMatrix ((Zm + 1) * K - 1) = 0
    rw [this]; change (Zm + 1).map π * K.map π - 1 = 0
    rw [hM, hN, sub_self]
  have e₁ := hπ π₁ N₁ hM₁ h₁
  have e₂ := hπ π₂ N₂ hM₂ h₂
  rw [← sub_eq_zero]
  ext i j
  apply hinj
  · intro u hu
    have := congrArg (fun m => m i j) (hAt u hu)
    simpa using this
  · simpa using congrArg (fun m => m i j) e₁
  · simpa using congrArg (fun m => m i j) e₂

end GlobalTheory.MatrixLeftInverseLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLeftInverseLiftingSplitPlaceInversesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.exists_leftInverse_lifting_splitPlaceInverses : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v), (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) → (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ K : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) (K - 1) →
  ∀ N₁ N₂ : Matrix (Fin d) (Fin d) (Fv F v), N₁ * K.map π₁ = 1 → N₂ * K.map π₂ = 1 →
  ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * K = 1 ∧ M.map π₁ = N₁ ∧ M.map π₂ = N₂ := by
  first | exact @GlobalTheory.MatrixLeftInverseLift.matrix_left_inverse_lift | exact GlobalTheory.MatrixLeftInverseLift.matrix_left_inverse_lift | (intros; apply GlobalTheory.MatrixLeftInverseLift.matrix_left_inverse_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfBlockSumTwistSubOneSupportedAtPlace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.TwistBlockK

theorem atK_sub_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (g : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
  At (evFin F v) (g - 1) → At (evFin F v) Y → At (evFin F v) ((⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ + (g).toBlocks₂₁ + (g).toBlocks₂₂) +
      Y * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ - (g).toBlocks₂₁ - (g).toBlocks₂₂))) - 1) := by
  intro F E _ _ _ _ _ d v g Y hg hY u hu
  have hgu := hg u hu
  have hYu : u • Y = 0 := hY u hu
  rw [smul_sub, sub_eq_zero] at hgu
  have h11 : u • g.toBlocks₁₁ = u • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    ext i j
    have := congrFun (congrFun hgu (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.toBlocks₁₁, Matrix.one_apply] using this
  have h22 : u • g.toBlocks₂₂ = u • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    ext i j
    have := congrFun (congrFun hgu (Sum.inr i)) (Sum.inr j)
    simpa [Matrix.toBlocks₂₂, Matrix.one_apply] using this
  have h12 : u • g.toBlocks₁₂ = 0 := by
    ext i j
    have := congrFun (congrFun hgu (Sum.inl i)) (Sum.inr j)
    simpa [Matrix.toBlocks₁₂, Matrix.one_apply] using this
  have h21 : u • g.toBlocks₂₁ = 0 := by
    ext i j
    have := congrFun (congrFun hgu (Sum.inr i)) (Sum.inl j)
    simpa [Matrix.toBlocks₂₁, Matrix.one_apply] using this
  rw [smul_sub, smul_add, ← Matrix.smul_mul, hYu, Matrix.zero_mul, add_zero,
    smul_comm u (⅟(2 : AF F))]
  simp only [smul_add, h11, h12, h21, h22, add_zero]
  rw [← add_smul, invOf_two_add_invOf_two, one_smul, sub_self]

end GlobalTheory.TwistBlockK
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfBlockSumTwistSubOneSupportedAtPlaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.halfBlockSumTwist_sub_one_supportedAtPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (g : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
  At (evFin F v) (g - 1) → At (evFin F v) Y → At (evFin F v) ((⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ + (g).toBlocks₂₁ + (g).toBlocks₂₂) +
      Y * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ - (g).toBlocks₂₁ - (g).toBlocks₂₂))) - 1) := by
  first | exact @GlobalTheory.TwistBlockK.atK_sub_one | exact GlobalTheory.TwistBlockK.atK_sub_one | (intros; apply GlobalTheory.TwistBlockK.atK_sub_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.KeepsLatticeAtPlaceOfIntegralLocalBasisConjugate

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.KeepInt

theorem mulVec_conj_mem {d : ℕ} {K : Type} [Field K] (S : ValuationSubring K)
    (b : GL (Fin d) K) (M : Matrix (Fin d) (Fin d) K) (w : Fin d → K)
    (hM : ∀ i j, (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * M * (b : Matrix (Fin d) (Fin d) K)) i j ∈ S)
    (hw : ∀ i, (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w) i ∈ S) :
    ∀ i, (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (M *ᵥ w)) i ∈ S := by
  intro i
  have key : ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ (M *ᵥ w) =
      (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * M * (b : Matrix (Fin d) (Fin d) K)) *ᵥ
        (((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ w) := by
    have h1 : (b : Matrix (Fin d) (Fin d) K) * ((b⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc _ (b : Matrix (Fin d) (Fin d) K), h1, Matrix.mul_one]
  rw [key]
  simp only [Matrix.mulVec, dotProduct]
  exact S.sum_mem (fun j _ => mul_mem (hM i j) (hw j))

end GlobalTheory.KeepInt

theorem GlobalTheory.KeepInt.keepLat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z : Fin d → AE F E, z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
      (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
        v.adicCompletionIntegers F) ∧
      (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
        v.adicCompletionIntegers F)) →
  ∀ A : Matrix (Fin d) (Fin d) (AE F E), (∀ i j, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) → (∀ i j, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) := by
  intro F E _ _ _ _ _ d W v π₁ π₂ b₁ b₂ hiff A hA₁ hA₂ z hz
  obtain ⟨hAt, h₁, h₂⟩ := (hiff z).1 hz
  refine (hiff _).2 ⟨?_, ?_, ?_⟩
  · intro u hu
    rw [← Matrix.mulVec_smul, hAt u hu, Matrix.mulVec_zero]
  · have e : (fun j => π₁ ((A *ᵥ z) j)) = (A.map π₁) *ᵥ (fun j => π₁ (z j)) := by
      funext j; exact RingHom.map_mulVec π₁ A z j
    rw [e]
    exact GlobalTheory.KeepInt.mulVec_conj_mem (v.adicCompletionIntegers F) b₁ _ _ hA₁ h₁
  · have e : (fun j => π₂ ((A *ᵥ z) j)) = (A.map π₂) *ᵥ (fun j => π₂ (z j)) := by
      funext j; exact RingHom.map_mulVec π₂ A z j
    rw [e]
    exact GlobalTheory.KeepInt.mulVec_conj_mem (v.adicCompletionIntegers F) b₂ _ _ hA₂ h₂
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.KeepsLatticeAtPlaceOfIntegralLocalBasisConjugateStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.keepsLatticeAtPlace_of_integral_localBasisConjugates : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
      (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
        v.adicCompletionIntegers F) ∧
      (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
        v.adicCompletionIntegers F)) →
  ∀ A : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ i j, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₁ * (b₁ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) → (∀ i j, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) * (A).map π₂ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F) →
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, A *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) := by
  first | exact @GlobalTheory.KeepInt.keepLat | exact GlobalTheory.KeepInt.keepLat | (intros; apply GlobalTheory.KeepInt.keepLat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceBigCellExistsAdmissibleInverse

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitPlaceBigCell

theorem splitPlace_bigCell_exists_admissible_inverse : (∀ {R : Type} [CommRing R] [IsLocalRing R], IsUnit (2 : R) → ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) R), IsUnit S.det →
    ∀ (G₁ G₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R), IsUnit G₁.det →
      G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) →
      ∃ X₁ X₂ : Matrix (Fin n) (Fin n) R, X₁ᵀ * S + S * X₂ = 0 ∧
        IsUnit (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ + G₁.toBlocks₂₁ + G₁.toBlocks₂₂ +
          X₁ * (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ - G₁.toBlocks₂₁ - G₁.toBlocks₂₂)).det ∧
        IsUnit (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ + G₂.toBlocks₂₁ + G₂.toBlocks₂₂ +
          X₂ * (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ - G₂.toBlocks₂₁ - G₂.toBlocks₂₂)).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (∀ i j, σ (W.J j i) = -W.J i j) →
    IsUnit (2 : v.adicCompletionIntegers F) →
    ∀ (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) →
      (∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) →
      ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
        Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  intro hLoc F E _ _ _ _ _ σ d W v hskew h2 π₁ π₂ b₁ b₂ hd hSx g hg
  obtain ⟨hc₁, hc₂, ha₁, ha₂, hinj, hsurj, hlat⟩ := hd
  obtain ⟨S, hSdet, hS⟩ := hSx
  obtain ⟨k11, k12, k21, k22, k11', k12', k21', k22'⟩ := GlobalTheory.T.doubledVacuumLatticeStabilizer_blocks_keep_lattice σ W v g hg
  have I := fun A hA => GlobalTheory.T.integral_localBasisConjugates_of_keepsLatticeAtPlace W v π₁ π₂ b₁ b₂ hlat hsurj A hA
  have hinv : GlobalTheory.DblVac.matD g⁻¹ * GlobalTheory.DblVac.matD g = 1 := g.1.inv_mul
  obtain ⟨G₁, hG₁, hG₁u⟩ := GlobalTheory.T.integralBlocks_leftInverse_isUnit_det_splitPlace v π₁ b₁ (GlobalTheory.DblVac.matD g) (GlobalTheory.DblVac.matD g⁻¹) hinv
    (I _ k11).1 (I _ k12).1 (I _ k21).1 (I _ k22).1 (I _ k11').1 (I _ k12').1 (I _ k21').1 (I _ k22').1
  obtain ⟨G₂, hG₂, -⟩ := GlobalTheory.T.integralBlocks_leftInverse_isUnit_det_splitPlace v π₂ b₂ (GlobalTheory.DblVac.matD g) (GlobalTheory.DblVac.matD g⁻¹) hinv
    (I _ k11).2 (I _ k12).2 (I _ k21).2 (I _ k22).2 (I _ k11').2 (I _ k12').2 (I _ k21').2 (I _ k22').2
  have hU := GlobalTheory.T.unitary_at_splitPlace_localBases σ W v π₁ π₂ b₁ b₂ hc₁ g
  have e : ∀ {m n o : Type} [Fintype n] (A : Matrix m n (v.adicCompletionIntegers F))
      (B : Matrix n o (v.adicCompletionIntegers F)),
      (A * B).map (fun x => (x : Fv F v)) = A.map (fun x => (x : Fv F v)) * B.map (fun x => (x : Fv F v)) :=
    fun A B => Matrix.map_mul (f := (v.adicCompletionIntegers F).subtype)
  have hUO : G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) := by
    apply Matrix.map_injective (f := fun x : v.adicCompletionIntegers F => (x : Fv F v)) Subtype.coe_injective
    beta_reduce
    have en : (-S).map (fun x => (x : Fv F v)) = -(S.map (fun x => (x : Fv F v))) := by ext i j; rfl
    have ez : (0 : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F)).map (fun x => (x : Fv F v)) = 0 := by
      ext i j; rfl
    rw [e, e, Matrix.transpose_map, Matrix.fromBlocks_map, en, ez, hG₁, hG₂, hS]
    exact hU
  obtain ⟨X₁, X₂, hX, hP₁, hP₂⟩ := hLoc h2 S hSdet G₁ G₂ hG₁u hUO
  obtain ⟨Y, hYat, hY₁, hY₂, hYadm⟩ :=
    GlobalTheory.T.exists_admissible_lift_splitPlaceConjugatePair σ W v hskew π₁ π₂ b₁ b₂ hc₁ hc₂ hinj hsurj S hS X₁ X₂ hX
  obtain ⟨N₁, hN₁, hN₁i⟩ := GlobalTheory.T.halfBlockSum_exists_inverse_integral_splitPlace v π₁ b₁ ha₁ (GlobalTheory.DblVac.matD g) G₁ hG₁ X₁ hP₁ Y hY₁
  obtain ⟨N₂, hN₂, hN₂i⟩ := GlobalTheory.T.halfBlockSum_exists_inverse_integral_splitPlace v π₂ b₂ ha₂ (GlobalTheory.DblVac.matD g) G₂ hG₂ X₂ hP₂ Y hY₂
  have hK := GlobalTheory.T.halfBlockSumTwist_sub_one_supportedAtPlace v (GlobalTheory.DblVac.matD g) Y hg.1 hYat
  obtain ⟨M, hMK, hM₁, hM₂⟩ := GlobalTheory.T.exists_leftInverse_lifting_splitPlaceInverses v π₁ π₂ hinj hsurj _ hK N₁ N₂ hN₁ hN₂
  have hYi : ∀ (b : GL (Fin d) (Fv F v)) (X : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F)),
      ∀ i j, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *
        ((b : Matrix (Fin d) (Fin d) (Fv F v)) * X.map (fun x => (x : Fv F v)) *
          ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))) *
        (b : Matrix (Fin d) (Fin d) (Fv F v))) i j ∈ v.adicCompletionIntegers F := by
    intro b X i j
    have : ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *
        ((b : Matrix (Fin d) (Fin d) (Fv F v)) * X.map (fun x => (x : Fv F v)) *
          ((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))) *
        (b : Matrix (Fin d) (Fin d) (Fv F v)) = X.map (fun x => (x : Fv F v)) := by
      simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [this]; exact (X i j).2
  refine ⟨Y, hYat, GlobalTheory.T.keepsLatticeAtPlace_of_integral_localBasisConjugates W v π₁ π₂ b₁ b₂ hlat Y ?_ ?_, hYadm, M, hMK,
    GlobalTheory.T.keepsLatticeAtPlace_of_integral_localBasisConjugates W v π₁ π₂ b₁ b₂ hlat M ?_ ?_⟩
  · rw [hY₁]; exact hYi b₁ X₁
  · rw [hY₂]; exact hYi b₂ X₂
  · rw [hM₁]; exact hN₁i
  · rw [hM₂]; exact hN₂i

end GlobalTheory.SplitPlaceBigCell
end
end
