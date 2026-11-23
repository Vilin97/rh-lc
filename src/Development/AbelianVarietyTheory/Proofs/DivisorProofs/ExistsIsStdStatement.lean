module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersOfCompOnGeneratorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersAugmentationIdeal
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersSplitAugmentationExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAndAugmentationMap

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersAugmentationIdealStatement

section

@[expose] public section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

theorem _root_.GlobalTheory.T.exists_isPreDividedPowers_augmentationIdeal : ∀ (B : Type) [CommRing B] (Q : PDPoly B), ∃ η : ℕ → Q.P → Q.P, IsPreDP Q.aug η ∧ ∀ n k : ℕ, η n (Q.e (k + 1)) = (n.uniformBell (k + 1) : Q.P) * Q.e (n * (k + 1)) := by
  first | exact @GlobalTheory.PDA.exists_isPreDividedPowers_augmentation | exact GlobalTheory.PDA.exists_isPreDividedPowers_augmentation | (intros; apply GlobalTheory.PDA.exists_isPreDividedPowers_augmentation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersDividedPowerPolyAlgebraAugIde

section

@[expose] public section

set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem uniformBell_comp_coeff (m : ℕ) {n N : ℕ} (hn : n ≠ 0) (hN : N ≠ 0) :
    n.uniformBell N ^ m * m.uniformBell (n * N) = m.uniformBell n * (m * n).uniformBell N := by
  have h1 := Nat.uniformBell_mul_eq n hN
  have h2 := Nat.uniformBell_mul_eq m (Nat.mul_ne_zero hn hN)
  have h3 := Nat.uniformBell_mul_eq m hn
  have h4 := Nat.uniformBell_mul_eq (m * n) hN
  have hpos : 0 < m.factorial * n.factorial ^ m * N.factorial ^ (m * n) := by positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc n.uniformBell N ^ m * m.uniformBell (n * N) * (m.factorial * n.factorial ^ m * N.factorial ^ (m * n))
      = m.uniformBell (n * N) * (n.uniformBell N * N.factorial ^ n * n.factorial) ^ m * m.factorial := by ring
    _ = (m * (n * N)).factorial := by rw [h1, h2]
    _ = ((m * n) * N).factorial := by rw [Nat.mul_assoc]
    _ = (m * n).uniformBell N * N.factorial ^ (m * n) * (m.uniformBell n * n.factorial ^ m * m.factorial) := by
      rw [h3, h4]
    _ = m.uniformBell n * (m * n).uniformBell N * (m.factorial * n.factorial ^ m * N.factorial ^ (m * n)) := by ring

theorem exists_dividedPowers_aug : ∀ (B : Type) [CommRing B] (Q : PDPoly B),
    ∃ η : DividedPowers Q.aug, ∀ n : ℕ, η.dpow n (Q.e 1) = Q.e n := by
  intro B _ Q
  obtain ⟨γ, hγ, he⟩ := GlobalTheory.T.exists_isPreDividedPowers_augmentationIdeal B Q
  have hcomp : ∀ x ∈ Set.range (fun k : ℕ ↦ Q.e (k + 1)), ∀ m n : ℕ, n ≠ 0 →
      γ m (γ n x) = (m.uniformBell n : Q.P) * γ (m * n) x := by
    rintro _ ⟨k, rfl⟩ m n hn
    obtain ⟨j, hj⟩ : ∃ j, n * (k + 1) = j + 1 := ⟨n * (k + 1) - 1, by
      have : 0 < n * (k + 1) := Nat.mul_pos (Nat.pos_of_ne_zero hn) k.succ_pos
      omega⟩
    have hmem : Q.e (n * (k + 1)) ∈ Q.aug := hj ▸ Q.e_succ_mem_aug j
    have key := congrArg (Nat.cast (R := Q.P)) (uniformBell_comp_coeff m hn k.succ_ne_zero)
    push_cast at key
    rw [he n k, hγ.mul m _ _ hmem, hj, he m j, ← hj, he (m * n) k, ← Nat.mul_assoc]
    linear_combination key * Q.e (m * n * (k + 1))
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_dividedPowers_of_comp_on_generators Q.P Q.aug γ (Set.range fun k : ℕ ↦ Q.e (k + 1)) hγ rfl hcomp
  refine ⟨δ, fun n ↦ ?_⟩
  rw [hδ]
  have := he n 0
  simpa [Nat.uniformBell_one_right] using this

end GlobalTheory.PDA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersDividedPowerPolyAlgebraAugIdeStatement

section

@[expose] public section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

theorem _root_.GlobalTheory.T.exists_dividedPowers_dividedPowerPolyAlgebra_augIdeal : ∀ (B : Type) [CommRing B] (Q : PDPoly B), ∃ η : DividedPowers Q.aug, ∀ n : ℕ, η.dpow n (Q.e 1) = Q.e n := by
  first | exact @GlobalTheory.PDA.exists_dividedPowers_aug | exact GlobalTheory.PDA.exists_dividedPowers_aug | (intros; apply GlobalTheory.PDA.exists_dividedPowers_aug <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersSplitAugmentationExtensionStatement

section

@[expose] public section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

theorem _root_.GlobalTheory.T.exists_dividedPowers_split_augmentation_extension : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (P : Type) [CommRing P] [Algebra B P] (ε : P →ₐ[B] B) (𝔞 : Ideal P) (η : DividedPowers 𝔞), (∀ p, p ∈ 𝔞 ↔ ε p = 0) → ∃ θ : DividedPowers (J.map (algebraMap B P) ⊔ 𝔞), IsDPMorphism δ θ (algebraMap B P) ∧ ∀ n, ∀ p ∈ 𝔞, θ.dpow n p = η.dpow n p := by
  first | exact @GlobalTheory.SplitDP.exists_dp_ext | exact GlobalTheory.SplitDP.exists_dp_ext | (intros; apply GlobalTheory.SplitDP.exists_dp_ext <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAndAugmentationMapStatement

section

@[expose] public section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

theorem _root_.GlobalTheory.T.exists_lift_and_augmentation_map : ∀ (B : Type) [CommRing B] (Q : PDPoly B), (∀ (C : Type) [CommRing C] (f : B →+* C) (c : ℕ → C), c 0 = 1 → (∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) → ∃ F : Q.P →+* C, (∀ b, F (algebraMap B Q.P b) = f b) ∧ ∀ n, F (Q.e n) = c n) ∧ ∃ ε : Q.P →ₐ[B] B, ∀ p, p ∈ Q.aug ↔ ε p = 0 := by
  first | exact @GlobalTheory.PDA.PDPoly.exists_lift_and_aug | exact GlobalTheory.PDA.PDPoly.exists_lift_and_aug | (intros; apply GlobalTheory.PDA.PDPoly.exists_lift_and_aug <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStd

section

@[expose] public section

set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem PDPoly.exists_isStd : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B),
    ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  intro B _ J δ Q
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_dividedPowers_dividedPowerPolyAlgebra_augIdeal B Q
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.exists_lift_and_augmentation_map B Q).2
  obtain ⟨θ, hθ, hθη⟩ := GlobalTheory.T.exists_dividedPowers_split_augmentation_extension B J δ Q.P ε Q.aug η hε
  refine ⟨θ, ⟨hθ, fun n ↦ ?_⟩⟩
  rw [hθη n _ (Q.e_succ_mem_aug 0), hη]

end GlobalTheory.PDA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStdStatement

section

@[expose] public section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

theorem _root_.GlobalTheory.T.exists_dividedPowers_ext_isStd : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B), ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  first | exact @GlobalTheory.PDA.PDPoly.exists_isStd | exact GlobalTheory.PDA.PDPoly.exists_isStd | (intros; apply GlobalTheory.PDA.PDPoly.exists_isStd <;> assumption)
end
end
