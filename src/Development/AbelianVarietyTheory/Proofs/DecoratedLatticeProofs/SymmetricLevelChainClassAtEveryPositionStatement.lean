module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeBlockDiagonalTargetEntryConditionsStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagPartMulDiagPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpEOmTargetUnipotent
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleBlockTriangularMemIntegralMulLevi

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.PClassAlg

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem shape_aX (hp : 1 ≤ p) (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (l : Fin c) (y : n) :
    B (Sum.inr l) (Sum.inl y) = 0 := by
  by_cases h : l.val + 1 < p
  · apply h2
    show OrderDual.toDual (lev p (Sum.inl y : n ⊕ Fin c)) < OrderDual.toDual (lev p (Sum.inr l : n ⊕ Fin c))
    simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega
  · apply h1; simp only [Sum.elim_inl, Sum.elim_inr]; omega

theorem shape_aa (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (i j : Fin c) (hij : i ≠ j) :
    B (Sum.inr i) (Sum.inr j) = 0 := by
  have : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne this with h | h
  · apply h2
    show OrderDual.toDual (lev p (Sum.inr j : n ⊕ Fin c)) < OrderDual.toDual (lev p (Sum.inr i : n ⊕ Fin c))
    simp only [lev, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega
  · apply h1; simp only [Sum.elim_inr]; omega

theorem shape_Xa (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (x : n) (i : Fin c) (hi : i.val + 1 ≠ p) :
    B (Sum.inl x) (Sum.inr i) = 0 := by
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · apply h1; simp only [Sum.elim_inl, Sum.elim_inr]; omega
  · apply h2
    show OrderDual.toDual (lev p (Sum.inr i : n ⊕ Fin c)) < OrderDual.toDual (lev p (Sum.inl x : n ⊕ Fin c))
    simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega

theorem eq_fromBlocks (hp : 1 ≤ p) (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) :
    B = fromBlocks (toBlocks₁₁ B) (toBlocks₁₂ B) 0 (toBlocks₂₂ B) := by
  conv_lhs => rw [← fromBlocks_toBlocks B]
  congr 1
  ext l y; exact shape_aX hp B h1 h2 l y

theorem diag_block (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) :
    toBlocks₂₂ B = diagonal fun i => B (Sum.inr i) (Sum.inr i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [toBlocks₂₂]
  · simp [toBlocks₂₂, diagonal_apply_ne _ h, shape_aa B h1 h2 i j h]

end GlobalTheory.PClassAlg

namespace GlobalTheory.PClassAlg

theorem blockDiag_mem_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (A : GL (n ⊕ Fin c) k), A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧ (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) → (∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k]) → ∃ γ : GL n k, A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)) ∈ KO k (n ⊕ Fin c) := by
  intro k _ _ _ _ ϖ n _ _ c p hp hpc A hA1 hA2 hB1 hB2 hD hE
  have eA := eq_fromBlocks hp _ hA1 hA2
  have eB := eq_fromBlocks hp _ hB1 hB2
  have dA := diag_block _ hA1 hA2
  have dB := diag_block _ hB1 hB2
  have sXa := shape_Xa _ hA1 hA2
  set P := toBlocks₁₁ A.val
  set Q := toBlocks₁₂ A.val
  set S := toBlocks₂₂ A.val
  set P' := toBlocks₁₁ (A⁻¹).val
  set Q' := toBlocks₁₂ (A⁻¹).val
  set S' := toBlocks₂₂ (A⁻¹).val
  have hAB : A.val * (A⁻¹).val = 1 := Units.mul_inv A
  have hBA : (A⁻¹).val * A.val = 1 := Units.inv_mul A
  rw [eA, eB, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hAB hBA
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add] at hAB hBA
  obtain ⟨hPP', hPQ, -, -⟩ := hAB
  obtain ⟨hP'P, -, -, -⟩ := hBA
  let γ : GL n k := ⟨P', P, hP'P, hPP'⟩
  have hpow : ∀ i : Fin c, (((ϖ ^ (i.val + 1) : kˣ)) : k) = (ϖ : k) ^ (i.val + 1) := fun i => by simp
  have hne : ∀ i : Fin c, (ϖ : k) ^ (i.val + 1) ≠ 0 := fun i => pow_ne_zero _ ϖ.ne_zero
  refine ⟨γ, (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨?_, ?_⟩⟩
  · have hM : (A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))).val =
        fromBlocks (P * P') (Q * diagonal fun i : Fin c => (ϖ : k) ^ (i.val + 1)) 0
          (S * diagonal fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
      rw [Units.val_mul, Units.val_mul, eA]
      show fromBlocks P Q 0 S * fromBlocks P' 0 0 1 * fromBlocks 1 0 0 (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)).val = _
      simp [fromBlocks_multiply, hpow]
    rw [hM, hPP']
    rintro (x | l) (y | i)
    · simp only [fromBlocks_apply₁₁, Matrix.one_apply]; split_ifs <;> simp
    · simp only [fromBlocks_apply₁₂, mul_diagonal]
      by_cases h : i.val + 1 = p
      · exact hE i h x
      · simp [Q, toBlocks₁₂, sXa x i h]
    · simp
    · simp only [fromBlocks_apply₂₂, mul_diagonal, dA]
      by_cases h : l = i
      · subst h; simpa using (hD l).1
      · simp [diagonal_apply_ne _ h]

  · have hM : ((A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)))⁻¹).val =
        fromBlocks (P * P') (P * Q') 0
          ((diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) * S') := by
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, ← map_inv, ← map_inv, Units.val_mul, Units.val_mul, eB]
      show fromBlocks 1 0 0 ((GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))⁻¹).val *
        (fromBlocks P 0 0 1 * fromBlocks P' Q' 0 S') = _
      have : ((GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))⁻¹).val =
          diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹ := by
        ext i j; simp [GlobalTheory.SplitFlip.diagGL, diagonal_apply]
      rw [this]
      simp [fromBlocks_multiply]
    have hPQ' : P * Q' = -(Q * S') := eq_neg_of_add_eq_zero_left hPQ
    rw [hM, hPP', hPQ', dB]
    rintro (x | l) (y | i)
    · simp only [fromBlocks_apply₁₁, Matrix.one_apply]; split_ifs <;> simp
    · simp only [fromBlocks_apply₁₂, Matrix.neg_apply, mul_diagonal]
      by_cases h : i.val + 1 = p
      · have e : Q x i * (A⁻¹).val (Sum.inr i) (Sum.inr i) =
            (A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1)) *
              ((A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹) := by
          have := hne i
          simp only [Q, toBlocks₁₂, of_apply]
          field_simp
        rw [e]
        exact neg_mem (mul_mem (hE i h x) (hD i).2)
      · simp [Q, toBlocks₁₂, sXa x i h]
    · simp
    · simp only [fromBlocks_apply₂₂, diagonal_mul_diagonal, diagonal_apply]
      split_ifs with h
      · subst h; rw [mul_comm]; exact (hD l).2
      · exact zero_mem _

end GlobalTheory.PClassAlg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleBlockTriangularMemIntegralMulLeviStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.doubleBlockTriangular_mem_integral_mul_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (A : GL (n ⊕ Fin c) k), A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧ (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) → (∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k]) → ∃ γ : GL n k, A * embX c γ * embA n (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)) ∈ KO k (n ⊕ Fin c) := by
  first | exact @GlobalTheory.PClassAlg.blockDiag_mem_KO | exact GlobalTheory.PClassAlg.blockDiag_mem_KO | (intros; apply GlobalTheory.PClassAlg.blockDiag_mem_KO <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPhiSupportPeriodicStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.symmetricLevelChain_phi_support_periodic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (j c : ℕ) (H : j + c = s) (x z : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k), ((S.T t).Phi j c H x ≠ 0 → IntM ((embA (XIx (Fin κ) t (j + 1)) (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)))⁻¹.val * x * (embA (XIx (Fin κ) t j) (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1))).val)) ∧ (MaxM ((embA (XIx (Fin κ) t (j + 1)) (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)))⁻¹.val * z * (embA (XIx (Fin κ) t j) (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1))).val) → (S.T t).Phi j c H (x + z) = (S.T t).Phi j c H x) := by
  intro k _ _ _ _ s κ S t _ _ j c H x z
  set o := stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)
  set o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)
  set F := typeFrame (k := k) S.ϖ o
  set F' := typeFrame (k := k) S.ϖ o'
  have hPhi : ∀ y, (S.T t).Phi j c H y = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      ((F.coords F' y).submatrix (ixSucc _ t j) id) := fun y => rfl
  constructor
  · intro hx i l
    rw [hPhi] at hx
    have := TypeDatum.intM_of_Phi_ne_zero _ _ hx ((ixSucc _ t j).symm (o.symm i)) (o'.symm l)
    simpa [LatFrame.coords, F, F', typeFrame] using this
  · intro hz
    rw [hPhi, hPhi]
    have e : F.coords F' (x + z) = F.coords F' x + F.coords F' z := by
      unfold LatFrame.coords; rw [Matrix.mul_add, Matrix.add_mul]; rfl
    rw [e]
    exact TypeDatum.Phi_add _ (S.tame _) _ (y := (F.coords F' z).submatrix (ixSucc _ t j) id) fun _ _ => hz _ _
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainClassAtEveryPosition

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain

theorem classAt_all : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.ClassAt t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ j c H p hp1 hpc h hE
  haveI := hν.1
  obtain ⟨D, hDdef⟩ : ∃ D : GL (XIx (Fin κ) t (j + 1) ⊕ Fin c) k,
      D = embA (XIx (Fin κ) t (j + 1)) (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)) := ⟨_, rfl⟩
  obtain ⟨D', hD'def⟩ : ∃ D' : GL (XIx (Fin κ) t j ⊕ Fin (c + 1)) k,
      D' = embA (XIx (Fin κ) t j) (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1)) := ⟨_, rfl⟩
  have hD : (S.T t).bas (j + 1) c (by omega) = D := by rw [hDdef]; rfl
  have hlt : valuation k (S.ϖ : k) < 1 := (S.unif (S.ϖ : k)).2 le_rfl
  let lv' : XIx (Fin κ) t (j + 1) ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))
  have hlv : ∀ r s, lev p s < lev p r → lv' s < lv' r := by
    rintro (r | r) (s | s) h0 <;> simp only [lev, lv', Sum.elim_inl, Sum.elim_inr] at h0 ⊢ <;> omega
  obtain ⟨b, hb, w, hw, hbw⟩ := iwasawa_blockTriangular k _ lv' (h * D)
  have hb' : b.val.BlockTriangular (lev p) := fun r s hrs => hb (hlv r s hrs)
  obtain ⟨u, hu, m, hm1, hm2, hum⟩ := BlockLevi.exists_unip_mul_levi k _ c p b hb'
  have hh : h = u * (m * w * D⁻¹) := by
    have : h = h * D * D⁻¹ := by group
    rw [this, hbw, hum]; group
  obtain ⟨v, hv⟩ : ∃ v, v = m * w * D⁻¹ := ⟨_, rfl⟩
  rw [← hv] at hh
  have key : om (S.μ (j + 1)) 1 (u * v) ((S.T t).Phi j c H) =
      om (S.μ (j + 1)) 1 u (om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H)) := by
    simpa using Model.om_mul (S.μ (j + 1)) 1 1 u v ((S.T t).Phi j c H)
  have hE' : opE S.ψ ν p (om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H)) ≠ 0 := by
    intro h0; apply hE
    rw [hh, key, opE_om_target_unipotent k _ _ c p hp1 hpc S.ψ ν (S.μ (j + 1)) _ u hu, h0, smul_zero]
  have eg : D⁻¹ * v⁻¹ = w⁻¹ * m⁻¹ := by rw [hv]; group
  have ev : ∀ x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k,
      (D⁻¹).val * ((v⁻¹).val * x) * D'.val = (w⁻¹).val * ((m⁻¹).val * x * D'.val) := by
    intro x
    rw [← Matrix.mul_assoc (D⁻¹).val, ← Units.val_mul, eg, Units.val_mul]; simp only [Matrix.mul_assoc]
  have hinst := GlobalTheory.T.symmetricLevelChain_phi_support_periodic k s κ S t j c H
  rw [← hDdef, ← hD'def] at hinst
  have hsup : ∀ x, om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H) x ≠ 0 → IntM ((m⁻¹).val * x * D'.val) := by
    intro x hx
    have hΦ : (S.T t).Phi j c H ((v⁻¹).val * x) ≠ 0 := by
      have := right_ne_zero_of_mul hx
      simpa using this
    have h1 := (hinst ((v⁻¹).val * x) 0).1 hΦ
    rw [ev] at h1
    have e2 : (m⁻¹).val * x * D'.val = w.val * ((w⁻¹).val * ((m⁻¹).val * x * D'.val)) := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [e2]; exact (intM_of_mem_KO hw).mul h1
  have hper : ∀ x z, MaxM ((m⁻¹).val * z * D'.val) →
      om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H) (x + z) = om (S.μ (j + 1)) 1 v ((S.T t).Phi j c H) x := by
    intro x z hz
    have h1 : MaxM ((D⁻¹).val * ((v⁻¹).val * z) * D'.val) := by
      rw [ev]; exact (mem_KO.1 hw).2.mul_maxM hz
    simp only [om, Units.val_one, Matrix.mul_one, Matrix.mul_add]
    rw [(hinst ((v⁻¹).val * x) ((v⁻¹).val * z)).2 h1]
  have sm1 : m.val.BlockTriangular lv' := by
    intro r s hrs
    by_cases e : lev p r = lev p s
    · rw [hm2 r s e]; exact hb hrs
    · exact hm1 r s e
  have sm2 : m.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) := by
    intro r s hrs
    exact hm1 r s (Nat.ne_of_lt (OrderDual.toDual_lt_toDual.mp hrs))
  have si1 : (m⁻¹).val.BlockTriangular lv' := BlockLevi.blockTriangular_inv lv' m sm1
  have si2 : (m⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) := by
    letI : Invertible m.val := m.invertible
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular sm2
  have sm1' : (m⁻¹⁻¹).val.BlockTriangular lv' := by rw [inv_inv]; exact sm1
  have sm2' : (m⁻¹⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) := by rw [inv_inv]; exact sm2
  rw [hD'def] at hsup hper
  obtain ⟨E1, E2⟩ := GlobalTheory.T.rootExchange_blockDiagonal_target_entry_conditions k S.ψ ν S.cond S.ϖ hlt _ _ c p hp1 hpc m⁻¹ si1 si2 sm1' sm2' _ hsup hper hE'
  obtain ⟨γ, hK⟩ := GlobalTheory.T.doubleBlockTriangular_mem_integral_mul_levi k S.ϖ _ c p hp1 hpc m⁻¹ si1 si2 sm1' sm2' E1 E2
  rw [← hDdef] at hK
  refine ⟨u * embX c γ, mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left ⟨γ, rfl⟩),
    (u * embX c γ)⁻¹ * h, ?_, by group⟩
  rw [hD, mem_stabLat]
  have : D⁻¹ * ((u * embX c γ)⁻¹ * h) * D = (m⁻¹ * embX c γ * D)⁻¹ * w := by
    rw [hh, hv]; group
  rw [this]
  exact mul_mem (inv_mem hK) hw

end GlobalTheory.SymChain
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainClassAtEveryPositionStatement

section

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.symmetricLevelChain_classAt_every_position : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.ClassAt t ν := by
  first | exact @GlobalTheory.SymChain.classAt_all | exact GlobalTheory.SymChain.classAt_all | (intros; apply GlobalTheory.SymChain.classAt_all <;> assumption)
end
end
