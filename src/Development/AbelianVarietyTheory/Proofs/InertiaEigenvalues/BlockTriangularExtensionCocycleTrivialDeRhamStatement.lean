module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KroneckerTransposeMulVec
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Field.Subfield.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantRightInverseField

section

@[expose] public section

namespace GlobalTheory.InvariantRightInverse

theorem exists_rightInverse_subfield {L : Type} [Field L] (K : Subfield L) {N b : Type}
    [Fintype N] [DecidableEq b] (κ : Matrix b N L) (Y : Matrix N b L)
    (h : κ * Y = 1) (hκ : ∀ i k, κ i k ∈ K) :
    ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ k j, Λ k j ∈ K := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (fun x y hxy => Subtype.ext hxy))
  have hπ' : ∀ x : K, π (x : L) = x := fun x => LinearMap.congr_fun hπ x
  refine ⟨Matrix.of fun k j => (π (Y k j) : L), ?_, fun k j => (π (Y k j)).2⟩
  ext i j
  have h1 : ∑ k, κ i k * Y k j = (1 : Matrix b b L) i j := by
    rw [← h, Matrix.mul_apply]
  have h2 : ∀ k, κ i k * (π (Y k j) : L) = (π (κ i k * Y k j) : L) := by
    intro k
    have := π.map_smul (⟨κ i k, hκ i k⟩ : K) (Y k j)
    have e : (⟨κ i k, hκ i k⟩ : K) • Y k j = κ i k * Y k j := rfl
    rw [e] at this
    rw [this]
    rfl
  have h3 : (1 : Matrix b b L) i j ∈ K := by
    rw [Matrix.one_apply]
    split_ifs
    · exact K.one_mem
    · exact K.zero_mem
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  calc ∑ k, κ i k * (π (Y k j) : L) = ∑ k, (π (κ i k * Y k j) : L) :=
        Finset.sum_congr rfl (fun k _ => h2 k)
    _ = ((∑ k, π (κ i k * Y k j) : K) : L) := by push_cast; rfl
    _ = (π (∑ k, κ i k * Y k j) : L) := by rw [map_sum]
    _ = (1 : Matrix b b L) i j := by
        rw [h1]
        exact congrArg Subtype.val (hπ' ⟨_, h3⟩)

theorem exists_invariant_rightInverse_field {L : Type} [Field L] (G : Type)
    (act : G → L →+* L) (N b : Type) [Fintype N] [DecidableEq b]
    (κ : Matrix b N L) (Y : Matrix N b L) (h : κ * Y = 1)
    (hκ : ∀ g : G, Matrix.map κ (⇑(act g) : L → L) = κ) :
    ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ g : G, Matrix.map Λ (⇑(act g) : L → L) = Λ := by
  have hK : ∀ x : L, x ∈ (⨅ g : G, RingHom.eqLocusField (act g) (RingHom.id L)) ↔
      ∀ g, act g x = x := by
    intro x
    rw [Subfield.mem_iInf]
    exact Iff.rfl
  obtain ⟨Λ, h1, h2⟩ := exists_rightInverse_subfield
    (⨅ g : G, RingHom.eqLocusField (act g) (RingHom.id L)) κ Y h
    (fun i k => (hK _).2 (fun g => congrFun (congrFun (hκ g) i) k))
  refine ⟨Λ, h1, fun g => ?_⟩
  ext k j
  exact (hK _).1 (h2 k j) g

theorem exists_invariant_rightInverse :
    ∀ (L : Type) [inst : CommRing L], IsField L → ∀ (G : Type) (act : G → L →+* L) (N b : Type) [inst_1 : Fintype N] [DecidableEq N] [Fintype b] [inst_4 : DecidableEq b] (κ : Matrix b N L) (Y : Matrix N b L), κ * Y = (1 : Matrix b b L) → (∀ (g : G), Matrix.map κ (⇑(act g) : L → L) = κ) → ∃ (Λ : Matrix N b L), κ * Λ = (1 : Matrix b b L) ∧ ∀ (g : G), Matrix.map Λ (⇑(act g) : L → L) = Λ := by
  intro L _ hL G act N b _ _ _ _ κ Y h hκ
  letI : Field L := hL.toField
  exact exists_invariant_rightInverse_field G act N b κ Y h hκ

end GlobalTheory.InvariantRightInverse
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantRightInverseOfRightInverse

section

@[expose] public section

open Matrix

namespace GlobalTheory

theorem invariant_right_inverse_of_right_inverse :
    ∀ (L : Type) [CommRing L], IsField L → ∀ (G : Type) (act : G → L →+* L) (N b : Type)
      [Fintype N] [DecidableEq N] [Fintype b] [DecidableEq b] (κ : Matrix b N L)
      (Y : Matrix N b L), κ * Y = 1 → (∀ g, κ.map (act g) = κ) →
      ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ g, Λ.map (act g) = Λ := by
  first
  | exact @_root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse
  | exact _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse
  | (apply _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse ..)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantRightInverseOfRightInverseStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_invariant_right_inverse : ∀ (L : Type) [CommRing L], IsField L → ∀ (G : Type) (act : G → L →+* L) (N b : Type) [Fintype N] [DecidableEq N] [Fintype b] [DecidableEq b] (κ : Matrix b N L) (Y : Matrix N b L), κ * Y = 1 → (∀ g, κ.map (act g) = κ) → ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ g, Λ.map (act g) = Λ := by
  first | exact @GlobalTheory.invariant_right_inverse_of_right_inverse | exact GlobalTheory.invariant_right_inverse_of_right_inverse | (intros; apply GlobalTheory.invariant_right_inverse_of_right_inverse <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockTriangularExtensionCocycleTrivialDeRham

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per



theorem GlobalTheory.PMon.extCoc_dies_in_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → AdmDR P ρ → AdmDR P ρ₂ → ∀ m : ℕ, ∃ v : a × b → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (extCoc ρ₂ c g i))) = (matD P (homRep ρ₁ ρ₂) m g).mulVec (fun i => P.actQdR (g : GQ l) (v i)) - v := by
  intro l _ P AI T a b _ _ _ _ K ρ ρ₁ ρ₂ c hρ hQ hR m
  obtain ⟨Q, hQm⟩ := hQ m
  obtain ⟨R, hRm⟩ := hR m
  let f : ↥(MaximalUnramifiedExtension l) →+* P.R.BdR := (kd P).comp (fr l m)
  let σ : ↥(GK K) → P.R.BdR →+* P.R.BdR := fun g => ((P.actQdR (g : GQ l) : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →+* P.R.BdR)

  let A : ↥(GK K) → Matrix a a P.R.BdR := fun g => (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map f
  let C : ↥(GK K) → Matrix a b P.R.BdR := fun g => (c g).map f
  let D : ↥(GK K) → Matrix b b P.R.BdR := fun g => (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map f
  let Di : ↥(GK K) → Matrix b b P.R.BdR := fun g => (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map f
  have hDDi : ∀ g, D g * Di g = 1 := fun g => by
    simp only [D, Di]
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero f) (map_one f)]
  have hDiD : ∀ g, Di g * D g = 1 := fun g => by
    simp only [D, Di]
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero f) (map_one f)]
  have hM : ∀ g, matD P ρ m g = Matrix.fromBlocks (A g) (C g) 0 (D g) := fun g => by
    show (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map f = _
    rw [hρ g, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f)]
  let Qa : Matrix a (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inl id
  let Qb : Matrix b (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inr id
  have hb : ∀ g, D g * Qb.map (σ g) = Qb := fun g => by
    ext i j
    have h := congrFun (congrFun (hQm g) (Sum.inr i)) j
    rw [hM g] at h
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Qb, σ] using h
  have ha : ∀ g, A g * Qa.map (σ g) + C g * Qb.map (σ g) = Qa := fun g => by
    ext i j
    have h := congrFun (congrFun (hQm g) (Sum.inl i)) j
    rw [hM g] at h
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Qa, Qb, σ] using h
  have hRg : ∀ g, D g * (R : Matrix b b P.R.BdR).map (σ g) = R := fun g => hRm g
  let S : Matrix b b P.R.BdR := ((R⁻¹ : GL b P.R.BdR) : Matrix b b P.R.BdR)
  have hSR : S * R = 1 := by simp only [S]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hRS : (R : Matrix b b P.R.BdR) * S = 1 := by simp only [S]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgSR : ∀ g, S.map (σ g) * (R : Matrix b b P.R.BdR).map (σ g) = 1 := fun g => by
    rw [← Matrix.map_mul, hSR, Matrix.map_one _ (map_zero _) (map_one _)]
  have hgRS : ∀ g, (R : Matrix b b P.R.BdR).map (σ g) * S.map (σ g) = 1 := fun g => by
    rw [← Matrix.map_mul, hRS, Matrix.map_one _ (map_zero _) (map_one _)]
  have hgS : ∀ g, S.map (σ g) = S * D g := fun g => by
    calc S.map (σ g) = (S * (D g * (R : Matrix b b P.R.BdR).map (σ g))) * S.map (σ g) := by
          rw [hRg g, hSR, Matrix.one_mul]
      _ = S * D g * ((R : Matrix b b P.R.BdR).map (σ g) * S.map (σ g)) := by
          simp only [Matrix.mul_assoc]
      _ = S * D g := by rw [hgRS g, Matrix.mul_one]
  have hgR : ∀ g, (R : Matrix b b P.R.BdR).map (σ g) = Di g * R := fun g => by
    symm
    conv_lhs => rw [← hRg g]
    rw [← Matrix.mul_assoc, hDiD g, Matrix.one_mul]
  obtain ⟨κ, hκdef⟩ : ∃ κ : Matrix b (a ⊕ b) P.R.BdR, κ = S * Qb := ⟨_, rfl⟩
  have hκ : ∀ g, κ.map (σ g) = κ := fun g => by
    rw [hκdef, Matrix.map_mul, hgS g, Matrix.mul_assoc, hb g]
  let Y : Matrix (a ⊕ b) b P.R.BdR :=
    (((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr) * (R : Matrix b b P.R.BdR)
  have hQQ : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQb : Qb * (((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr) = 1 := by
    ext i j
    have h := congrFun (congrFun hQQ (Sum.inr i)) (Sum.inr j)
    simpa [Matrix.mul_apply, Matrix.one_apply, Qb] using h
  have hY : κ * Y = 1 := by
    simp only [Y]
    rw [hκdef, Matrix.mul_assoc, ← Matrix.mul_assoc Qb, hQb, Matrix.one_mul, hSR]
  obtain ⟨Λ, hκΛ, hΛ⟩ := GlobalTheory.T.exists_invariant_right_inverse P.R.BdR (GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).1 (↥(GK K)) σ (a ⊕ b) b κ Y hY hκ
  have hQbR : Qb = (R : Matrix b b P.R.BdR) * κ := by
    rw [hκdef, ← Matrix.mul_assoc, hRS, Matrix.one_mul]
  have hgQb : ∀ g, Qb.map (σ g) = (R : Matrix b b P.R.BdR).map (σ g) * κ := fun g => by
    conv_lhs => rw [hQbR]
    rw [Matrix.map_mul, hκ g]
  let Z : Matrix a b P.R.BdR := Qa * Λ
  have hAZ : ∀ g, A g * Z.map (σ g) = Z - C g * (R : Matrix b b P.R.BdR).map (σ g) := fun g => by
    have e : A g * Qa.map (σ g) = Qa - C g * ((R : Matrix b b P.R.BdR).map (σ g) * κ) := by
      rw [← hgQb g]
      exact eq_sub_of_add_eq (ha g)
    simp only [Z]
    rw [Matrix.map_mul, hΛ g, ← Matrix.mul_assoc, e, Matrix.sub_mul, Matrix.mul_assoc (C g),
      Matrix.mul_assoc ((R : Matrix b b P.R.BdR).map (σ g)), hκΛ, Matrix.mul_one]
  refine ⟨vecM (-(Z * S)), fun g => ?_⟩
  have hL : (fun i => kd P (fr l m (extCoc ρ₂ c g i))) = vecM (C g * Di g) := by
    show vecM ((c g * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l))).map f) = _
    rw [Matrix.map_mul]
  have hR' : (matD P (homRep ρ₁ ρ₂) m g).mulVec (fun i => P.actQdR (g : GQ l) (vecM (-(Z * S)) i)) =
      vecM (A g * (-(Z * S)).map (σ g) * Di g) := by
    show (((homUnit (ρ₁ g) (ρ₂ g) : GL (a × b) ↥(MaximalUnramifiedExtension l)) : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map f).mulVec
      (vecM ((-(Z * S)).map (σ g))) = _
    rw [homUnit_mulVec]
  rw [hL, hR']
  have hsub : ∀ X Y : Matrix a b P.R.BdR, vecM X - vecM Y = vecM (X - Y) := fun _ _ => rfl
  rw [hsub]
  congr 1
  have hneg : (-(Z * S)).map (σ g) = -(Z.map (σ g) * S.map (σ g)) := by
    rw [Matrix.map_neg _ (map_neg (σ g)), Matrix.map_mul]
  rw [hneg, hgS g, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc (A g), hAZ g, hgR g]
  simp only [Matrix.sub_mul, Matrix.mul_assoc, hDDi g, hRS, Matrix.mul_one]
  abel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockTriangularExtensionCocycleTrivialDeRhamStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.blockTriangular_extensionCocycle_trivial_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → AdmDR P ρ → AdmDR P ρ₂ → ∀ m : ℕ, ∃ v : a × b → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (extCoc ρ₂ c g i))) = (matD P (homRep ρ₁ ρ₂) m g).mulVec (fun i => P.actQdR (g : GQ l) (v i)) - v := by
  first | exact @GlobalTheory.PMon.extCoc_dies_in_BdR | exact GlobalTheory.PMon.extCoc_dies_in_BdR | (intros; apply GlobalTheory.PMon.extCoc_dies_in_BdR <;> assumption)
end
end
