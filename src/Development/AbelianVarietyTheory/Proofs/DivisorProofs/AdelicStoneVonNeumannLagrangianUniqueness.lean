module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZeroStatement
import Mathlib.Algebra.Module.Torsion.Prod
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBlockGeneratorsLagrangianNormalF

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

namespace GlobalTheory.AdelicSvN.LagrangianNormalForm

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem exists_ginv_form (X : Matrix κ κ F) :
    ∃ G C : Matrix κ κ F, X * G * X = X ∧ Cᵀ = C ∧ ∀ v, (Xᵀ * C * X) *ᵥ v = 0 → X *ᵥ v = 0 := by
  obtain ⟨L, L', d, h⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal X
  set P := (L.map Matrix.TransvectionStruct.toMatrix).prod with hP
  set Q := (L'.map Matrix.TransvectionStruct.toMatrix).prod with hQ
  have dP : IsUnit P.det := by rw [hP, Matrix.TransvectionStruct.det_toMatrix_prod]; exact isUnit_one
  have dQ : IsUnit Q.det := by rw [hQ, Matrix.TransvectionStruct.det_toMatrix_prod]; exact isUnit_one
  have hX : X = P⁻¹ * Matrix.diagonal d * Q⁻¹ := by
    rw [← h]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ dQ, Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ dP]
  have hPX : P * X = Matrix.diagonal d * Q⁻¹ := by
    rw [← h]; simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ dQ, Matrix.mul_one]
  refine ⟨Q * Matrix.diagonal (fun i => (d i)⁻¹) * P, Pᵀ * P, ?_, ?_, ?_⟩
  · have e : Matrix.diagonal d * (Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d) = Matrix.diagonal d := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1; funext i
      by_cases hi : d i = 0
      · simp [hi]
      · simp [hi]
    conv_lhs => rw [hX]
    conv_rhs => rw [hX, ← e]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ dQ,
      Matrix.mul_nonsing_inv_cancel_left _ _ dP]
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  · intro v hv
    have e : Xᵀ * (Pᵀ * P) * X = (Q⁻¹)ᵀ * (Matrix.diagonal d * (Matrix.diagonal d * Q⁻¹)) := by
      have : Xᵀ * (Pᵀ * P) * X = (P * X)ᵀ * (P * X) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [this, hPX, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [e] at hv
    have h2 := congrArg (fun w => Qᵀ *ᵥ w) hv
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ dQ, Matrix.transpose_one,
      Matrix.one_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h2
    have h3 : Matrix.diagonal d *ᵥ (Q⁻¹ *ᵥ v) = 0 := by
      funext i
      have := congrFun h2 i
      simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at this ⊢
      rcases mul_eq_zero.mp this with h0 | h0
      · simp [h0]
      · exact h0
    rw [hX, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h3, Matrix.mulVec_zero]

theorem exists_symm_isUnit (X Y : Matrix κ κ F) (hs : Xᵀ * Y = Yᵀ * X)
    (hi : ∀ v, X *ᵥ v = 0 → Y *ᵥ v = 0 → v = 0) :
    ∃ C : Matrix κ κ F, Cᵀ = C ∧ IsUnit (Y + C * X).det := by
  obtain ⟨G, C, hG, hC, hv⟩ := exists_ginv_form X
  refine ⟨C - Gᵀ * (Xᵀ * Y) * G, ?_, ?_⟩
  · rw [Matrix.transpose_sub, hC]
    congr 1
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Yᵀ, ← hs, Matrix.mul_assoc]
  · have e : Xᵀ * (Y + (C - Gᵀ * (Xᵀ * Y) * G) * X) = Xᵀ * C * X := by
      have e1 : Xᵀ * (Gᵀ * (Xᵀ * Y) * G * X) = Xᵀ * Y := by
        have : Xᵀ * (Gᵀ * (Xᵀ * Y) * G * X) = (X * G * X)ᵀ * Y * G * X := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        rw [this, hG, hs, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc X, hG]
      rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, e1, Matrix.mul_assoc]
      abel
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv1⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hX : X *ᵥ v = 0 := by
      apply hv
      rw [← e, ← Matrix.mulVec_mulVec, hv1, Matrix.mulVec_zero]
    apply hv0
    apply hi v hX
    rwa [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hX, Matrix.mulVec_zero, add_zero] at hv1

theorem upper_mem (S : Matrix κ κ F) (hS : Sᵀ = S) :
    Matrix.fromBlocks 1 S 0 1 ∈ Submonoid.closure (gens F κ) := by
  have hJ : Matrix.fromBlocks (0 : Matrix κ κ F) (1 : Matrix κ κ F) (-1 : Matrix κ κ F) (0 : Matrix κ κ F)
      ∈ Submonoid.closure (gens F κ) := Submonoid.subset_closure (Or.inr rfl)
  have hn : Matrix.fromBlocks (1 : Matrix κ κ F) (0 : Matrix κ κ F) (-S) (1 : Matrix κ κ F)
      ∈ Submonoid.closure (gens F κ) := Submonoid.subset_closure (Or.inl (Or.inr ⟨S, hS, rfl⟩))
  have := mul_mem (mul_mem (mul_mem (mul_mem hJ hn) hJ) hJ) hJ
  simpa [Matrix.fromBlocks_multiply] using this

theorem exists_mem_closure (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ]
    (L : Submodule F ((κ → F) × (κ → F)))
    (hL : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) (hd : Module.finrank F L = Fintype.card κ) :
    ∃ g ∈ Submonoid.closure (gens F κ), ∀ y : κ → F,
      ((g *ᵥ Sum.elim 0 y) ∘ Sum.inl, (g *ᵥ Sum.elim 0 y) ∘ Sum.inr) ∈ L := by
  let b : Module.Basis κ F L := (Module.finBasisOfFinrankEq F L hd).reindex (Fintype.equivFin κ).symm
  let X : Matrix κ κ F := Matrix.of fun i j => (b j).1.1 i
  let Y : Matrix κ κ F := Matrix.of fun i j => (b j).1.2 i
  have key : ∀ v : κ → F, (X *ᵥ v, Y *ᵥ v) = ((∑ j, v j • b j : L) : (κ → F) × (κ → F)) := by
    intro v
    ext i
    · simp [X, Matrix.mulVec, dotProduct, Prod.fst_sum, mul_comm]
    · simp [Y, Matrix.mulVec, dotProduct, Prod.snd_sum, mul_comm]
  have hs : Xᵀ * Y = Yᵀ * X := by
    ext i j
    have := hL _ (b i).2 _ (b j).2
    simp only [dotProduct] at this
    simp only [Matrix.mul_apply, X, Y, Matrix.transpose_apply, Matrix.of_apply]
    rw [this]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hi : ∀ v, X *ᵥ v = 0 → Y *ᵥ v = 0 → v = 0 := by
    intro v h1 h2
    have h3 := key v
    rw [h1, h2] at h3
    have h4 : ∑ j, v j • b j = 0 := Subtype.ext h3.symm
    funext j
    exact Fintype.linearIndependent_iff.mp b.linearIndependent v h4 j
  obtain ⟨C, hC, hM⟩ := exists_symm_isUnit X Y hs hi
  set M := Y + C * X with hMdef
  have hXM : Xᵀ * M = Mᵀ * X := by
    rw [hMdef, Matrix.transpose_add, Matrix.transpose_mul, hC, Matrix.mul_add, Matrix.add_mul, hs,
      Matrix.mul_assoc]
  have hS : (X * M⁻¹)ᵀ = X * M⁻¹ := by
    have h1 : (M⁻¹)ᵀ * Mᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hM, Matrix.transpose_one]
    calc (X * M⁻¹)ᵀ = (M⁻¹)ᵀ * (Xᵀ * M) * M⁻¹ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hM, Matrix.mul_one]
      _ = X * M⁻¹ := by rw [hXM, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hn : Matrix.fromBlocks (1 : Matrix κ κ F) (0 : Matrix κ κ F) (-C) (1 : Matrix κ κ F)
      ∈ Submonoid.closure (gens F κ) := Submonoid.subset_closure (Or.inl (Or.inr ⟨C, hC, rfl⟩))
  refine ⟨_, mul_mem hn (upper_mem _ hS), fun y => ?_⟩
  have hy : Y *ᵥ (M⁻¹ *ᵥ y) = -(C *ᵥ (X *ᵥ (M⁻¹ *ᵥ y))) + y := by
    have : M *ᵥ (M⁻¹ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
    generalize M⁻¹ *ᵥ y = v at this ⊢
    rw [← this, hMdef, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
    abel
  have hmem : (X *ᵥ (M⁻¹ *ᵥ y), Y *ᵥ (M⁻¹ *ᵥ y)) ∈ L := by rw [key]; exact Subtype.property _
  rw [hy] at hmem
  simpa [← Matrix.mulVec_mulVec, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec] using hmem

end GlobalTheory.AdelicSvN.LagrangianNormalForm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBlockGeneratorsLagrangianNormalFStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_symplecticBlockGenerators_lagrangian_normal_form : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ] (L : Submodule F ((κ → F) × (κ → F))),
    (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank F L = Fintype.card κ →
    ∃ g ∈ Submonoid.closure (gens F κ), ∀ y : κ → F,
      ((g *ᵥ Sum.elim 0 y) ∘ Sum.inl, (g *ᵥ Sum.elim 0 y) ∘ Sum.inr) ∈ L := by
  first | exact @GlobalTheory.AdelicSvN.LagrangianNormalForm.exists_mem_closure | exact GlobalTheory.AdelicSvN.LagrangianNormalForm.exists_mem_closure | (intros; apply GlobalTheory.AdelicSvN.LagrangianNormalForm.exists_mem_closure <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTransposeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

theorem _root_.GlobalTheory.T.isRealisedOnAdelicSchwartz_levi_inverseTranspose : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ F), IsUnit A.det → Realised ψ (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ) := by
  first | exact @GlobalTheory.AdelicSvNLevi.realised_levi | exact GlobalTheory.AdelicSvNLevi.realised_levi | (intros; apply GlobalTheory.AdelicSvNLevi.realised_levi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourierStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

theorem _root_.GlobalTheory.T.isRealisedOnAdelicSchwartz_weyl_fourier : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ], Realised ψ (Matrix.fromBlocks (0 : Matrix κ κ F) 1 (-1) 0) := by
  first | exact @GlobalTheory.AdelicSvN.Weyl.realised_weyl | exact GlobalTheory.AdelicSvN.Weyl.realised_weyl | (intros; apply GlobalTheory.AdelicSvN.Weyl.realised_weyl <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartzStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

theorem _root_.GlobalTheory.T.lowerUnipotent_realisedOnAdelicSchwartz : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ] (C : Matrix κ κ F), Cᵀ = C → Realised ψ (Matrix.fromBlocks 1 0 (-C) 1) := by
  first | exact @GlobalTheory.AdelicSvNQuad.realised_unip | exact GlobalTheory.AdelicSvNQuad.realised_unip | (intros; apply GlobalTheory.AdelicSvNQuad.realised_unip <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniqueness

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.AdelicSvN

variable {F : Type} [Field F] [NumberField F]

theorem dot_smul_rat {κ : Type} [Fintype κ] (s t : AF F) (u v : (κ → F) × (κ → F)) :
    (s • ((fun i => algebraMap F (AF F) (u.1 i)), (fun i => algebraMap F (AF F) (u.2 i)))).1 ⬝ᵥ
      (t • ((fun i => algebraMap F (AF F) (v.1 i)), (fun i => algebraMap F (AF F) (v.2 i)))).2 =
      s * t * algebraMap F (AF F) (u.1 ⬝ᵥ v.2) := by
  simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [show (fun i => algebraMap F (AF F) (u.1 i)) ⬝ᵥ (fun i => algebraMap F (AF F) (v.2 i)) =
    algebraMap F (AF F) (u.1 ⬝ᵥ v.2) from (RingHom.map_dotProduct (algebraMap F (AF F)) u.1 v.2).symm]
  ring

theorem inv_sum (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F))) (hL : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ)
    {ι : Type} (s : Finset ι) (t : ι → AF F) (w : ι → (κ → F) × (κ → F)) (hw : ∀ j, w j ∈ L) :
    ∀ φ ∈ schA F κ, l (schr ψ (∑ j ∈ s, t j • ((fun i => algebraMap F (AF F) ((w j).1 i)),
      (fun i => algebraMap F (AF F) ((w j).2 i)))) φ) = l φ := by
  classical
  induction s using Finset.induction_on with
  | empty => intro φ _; simp only [Finset.sum_empty]; congr 1; funext x; simp [schr]
  | insert j s hj ih =>
    intro φ hφ
    set a := t j • ((fun i => algebraMap F (AF F) ((w j).1 i)), (fun i => algebraMap F (AF F) ((w j).2 i)))
    set b := ∑ k ∈ s, t k • ((fun i => algebraMap F (AF F) ((w k).1 i)), (fun i => algebraMap F (AF F) ((w k).2 i)))
    have hab : a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 = 0 := by
      simp only [a, b, Prod.fst_sum, Prod.snd_sum, dotProduct_sum, sum_dotProduct, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [dot_smul_rat, dot_smul_rat, hL _ (hw j) _ (hw k)]
      ring
    have e := GlobalTheory.ThetaQuasiRat.schr_schr ψ a b φ
    rw [hab, mul_zero, AddChar.map_zero_eq_one, one_smul] at e
    rw [Finset.sum_insert hj, ← e, hl _ _ (hw j) _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ b φ hφ), ih φ hφ]

end GlobalTheory.AdelicSvN

namespace GlobalTheory.AdelicSvN
variable {F : Type} [Field F] [NumberField F]

theorem realised_of_mem_closure (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ] [DecidableEq κ]
    {g : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : g ∈ Submonoid.closure (gens F κ)) : Realised ψ g := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
    rcases hg with (⟨A, hA, rfl⟩ | ⟨C, hC, rfl⟩) | rfl
    · exact GlobalTheory.T.isRealisedOnAdelicSchwartz_levi_inverseTranspose F ψ κ A hA
    · exact GlobalTheory.T.lowerUnipotent_realisedOnAdelicSchwartz F ψ hψ κ C hC
    · exact GlobalTheory.T.isRealisedOnAdelicSchwartz_weyl_fourier F ψ hψ κ
  | one => exact realised_one ψ
  | mul g h _ _ hg hh => exact hg.mul hh

theorem act_zero_eq_sum {κ : Type} [Fintype κ] [DecidableEq κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (y : κ → AF F) :
    act g (0, y) = ∑ j, y j • ((fun i => algebraMap F (AF F) (((g *ᵥ Sum.elim 0 (Pi.single j 1)) ∘ Sum.inl) i)),
      (fun i => algebraMap F (AF F) (((g *ᵥ Sum.elim 0 (Pi.single j 1)) ∘ Sum.inr) i))) := by
  have key : ∀ k, (g.map (algebraMap F (AF F)) *ᵥ Sum.elim 0 y) k =
      ∑ j, y j * algebraMap F (AF F) ((g *ᵥ Sum.elim 0 (Pi.single j 1)) k) := by
    intro k
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_add, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j (fun m _ hm => by simp [Pi.single_apply, hm]) (by simp)]
    simp [mul_comm]
  ext i
  · simp only [act, Function.comp_apply, key, Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
  · simp only [act, Function.comp_apply, key, Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F))), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) →
    Module.finrank F L = Fintype.card κ →
    ∀ l₁ ∈ (adeleClass F).adm κ, ∀ l₂ ∈ (adeleClass F).adm κ,
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₁ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₁ φ) →
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₂ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₂ φ) →
    (∃ φ ∈ schA F κ, l₂ φ ≠ 0) → ∃ c : ℂ, ∀ φ ∈ schA F κ, l₁ φ = c * l₂ φ := by
  intro F _ _ ψ hψ κ _ L hL hdim l₁ hl₁ l₂ hl₂ hi₁ hi₂ ⟨φ₀, hφ₀, hne⟩
  classical
  obtain ⟨g, hg, hgL⟩ := GlobalTheory.T.exists_symplecticBlockGenerators_lagrangian_normal_form F κ L hL hdim
  obtain ⟨S, hS, hSs, hSa, hSi⟩ := realised_of_mem_closure ψ hψ hg
  have key : ∀ l ∈ (adeleClass F).adm κ, (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ) →
      ∃ c : ℂ, ∀ φ ∈ schA F κ, l (S φ) = c * φ 0 := by
    intro l hl hi
    obtain ⟨l', hl', e⟩ := hSa l hl
    obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F ψ hψ κ l' hl' (fun y φ hφ => by
      have hm : (fun x => ψ (x ⬝ᵥ y) * φ x) = schr ψ (0, y) φ := by funext x; simp [schr]
      rw [hm, e _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ), e φ hφ, hSi _ φ hφ, act_zero_eq_sum]
      exact inv_sum ψ hψ L hL l hi Finset.univ y _ (fun j => hgL _) _ (hS φ hφ))
    exact ⟨c, fun φ hφ => (e φ hφ).symm.trans (hc φ hφ)⟩
  obtain ⟨c₁, h₁⟩ := key l₁ hl₁ hi₁
  obtain ⟨c₂, h₂⟩ := key l₂ hl₂ hi₂
  obtain ⟨ψ₀, hψ₀, rfl⟩ := hSs φ₀ hφ₀
  have hc₂ : c₂ ≠ 0 := fun h => hne (by rw [h₂ ψ₀ hψ₀, h, zero_mul])
  refine ⟨c₁ / c₂, fun φ hφ => ?_⟩
  obtain ⟨φ', hφ', rfl⟩ := hSs φ hφ
  rw [h₁ φ' hφ', h₂ φ' hφ']
  field_simp
end GlobalTheory.AdelicSvN
end
end
end
