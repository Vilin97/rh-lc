module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
public import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.LocalRingCardinality.Params
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCofactorTwistHighestWeight
public import Formalism.GradedWeylDivisibility.StatementA
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowDivRowWeight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowDivSwap

section

@[expose] public section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

noncomputable section

namespace GlobalTheory.ValCmp

theorem adjugate_transvection_of_ne {A : Type} [CommRing A] {n : ℕ} (a b : Fin n) (hab : a ≠ b) (c : A) :
    (Matrix.transvection a b c).adjugate = Matrix.transvection a b (-c) := by
  have h1 : Matrix.transvection a b c * Matrix.transvection a b (-c) = 1 := by
    rw [Matrix.transvection_mul_transvection_same a b hab, add_neg_cancel, Matrix.transvection_zero]
  calc (Matrix.transvection a b c).adjugate
      = (Matrix.transvection a b c).adjugate * (Matrix.transvection a b c * Matrix.transvection a b (-c)) := by
        rw [h1, Matrix.mul_one]
    _ = Matrix.transvection a b (-c) := by
        rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.det_transvection_of_ne a b hab, one_smul,
          Matrix.one_mul]

theorem rowGen_map_genM (R : Type) [CommRing R] (n : ℕ) (a b : Fin n) :
    (rowGen R (n := n) b a).toRingHom.mapMatrix (genM R n) =
      Matrix.transvection a b Polynomial.X * (Polynomial.C (R := MP R n)).mapMatrix (genM R n) := by
  ext1 i s
  by_cases hi : i = a
  · subst hi
    rw [Matrix.transvection_mul_apply_same]
    simp [genM, rowGen]
  · rw [Matrix.transvection_mul_apply_of_ne _ _ _ _ hi]
    simp [genM, rowGen, hi]

theorem rowGen_det_genM (R : Type) [CommRing R] (n : ℕ) (a b : Fin n) (hab : a ≠ b) :
    rowGen R (n := n) b a (genM R n).det = Polynomial.C (genM R n).det := by
  have h := RingHom.map_det (rowGen R (n := n) b a).toRingHom (genM R n)
  rw [rowGen_map_genM, Matrix.det_mul, Matrix.det_transvection_of_ne a b hab, one_mul,
    ← RingHom.map_det] at h
  exact h

theorem rowGen_adjugate_genM (R : Type) [CommRing R] (n : ℕ) (a b : Fin n) (hab : a ≠ b) (t i : Fin n) :
    rowGen R (n := n) b a ((genM R n).adjugate t i) =
      Polynomial.C ((genM R n).adjugate t i) +
        (if i = b then -Polynomial.X * Polynomial.C ((genM R n).adjugate t a) else 0) := by
  have h := RingHom.map_adjugate (rowGen R (n := n) b a).toRingHom (genM R n)
  rw [rowGen_map_genM, Matrix.adjugate_mul_distrib, adjugate_transvection_of_ne a b hab,
    ← RingHom.map_adjugate] at h
  have h2 := congrFun (congrFun h t) i
  refine Eq.trans h2 ?_
  by_cases hi : i = b
  · subst hi
    rw [Matrix.mul_transvection_apply_same]
    simp
  · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hi]
    simp [hi]

theorem rowGen_cofAct (R : Type) [CommRing R] (n : ℕ) (a b : Fin n) (hab : a ≠ b) (f : MP R n) :
    rowGen R (n := n) b a (cofAct R n f) =
      ((rowGen R (n := n) a b f).map (cofAct R n).toRingHom).comp (Polynomial.C (-1) * Polynomial.X) := by
  induction f using MvPolynomial.induction_on with
  | C x =>
    have e1 : (C x : MP R n) = algebraMap R _ x := rfl
    rw [e1, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes, Polynomial.algebraMap_apply,
      Polynomial.map_C, Polynomial.C_comp]
    exact congrArg Polynomial.C ((cofAct R n).commutes x).symm
  | add p q hp hq => simp only [map_add (f := _), hp, hq, Polynomial.map_add (f := _), Polynomial.add_comp]
  | mul_X p v hp =>
    simp only [map_mul, hp, Polynomial.map_mul, Polynomial.mul_comp]
    refine congrArg₂ (· * ·) rfl ?_
    have e1 : ∀ w : Fin n × Fin n, cofAct R n (X w) = (genM R n).adjugate w.2.rev w.1 := fun w => by
      simp [cofAct]
    rw [e1, rowGen_adjugate_genM R n a b hab]
    by_cases hv : v.1 = b
    · simp [rowGen, hv, e1]
    · simp [rowGen, hv, e1]

theorem cofRel_rowDiv (R : Type) [CommRing R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (a b : Fin (m + 1)) (k : ℕ)
    (f g : MP R (m + 1)) (hab : a ≠ b) (h : CofRel R m ν f g) :
    CofRel R m ν (rowDiv R a b k f) (((-1 : ℤ) ^ k) • rowDiv R b a k g) := by
  unfold CofRel at h ⊢
  have h1 := congrArg (fun p => (rowGen R (n := m + 1) b a p).coeff k) h
  simp only [map_mul, map_pow, rowGen_det_genM R _ a b hab, rowGen_cofAct R _ a b hab,
    Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_map] at h1
  rw [← map_pow, Polynomial.coeff_C_mul] at h1
  have h2 : ((-1 : MP R (m + 1)) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  unfold rowDiv
  rw [zsmul_eq_mul, mul_left_comm, h1]
  push_cast
  rw [mul_left_comm, h2, mul_one]
  rfl

end GlobalTheory.ValCmp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowDivSwapStatement

section

@[expose] public section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

theorem _root_.GlobalTheory.T.cofactorTwistRelation_rowDiv_swap : ∀ (R : Type) [CommRing R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (a b : Fin (m + 1)) (k : ℕ) (f g : MP R (m + 1)), a ≠ b → CofRel R m ν f g → CofRel R m ν (rowDiv R a b k f) (((-1 : ℤ) ^ k) • rowDiv R b a k g) := by
  first | exact @GlobalTheory.ValCmp.cofRel_rowDiv | exact GlobalTheory.ValCmp.cofRel_rowDiv | (intros; apply GlobalTheory.ValCmp.cofRel_rowDiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCofactorTwistHighestWeightStatement

section

@[expose] public section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

theorem _root_.GlobalTheory.T.exists_cofactorTwist_highestWeight : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν (hw R le_rfl ν) g := by
  first | exact @GlobalTheory.ValCmp.exists_cofRel_hw | exact GlobalTheory.ValCmp.exists_cofRel_hw | (intros; apply GlobalTheory.ValCmp.exists_cofRel_hw <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowDivRowWeightStatement

section

@[expose] public section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

theorem _root_.GlobalTheory.T.isWeightedHomogeneous_div_and_diag_eq_choose_smul : ∀ (R : Type) [CommRing R] (r n : ℕ) (μ : Fin r → ℕ) (f : MvPolynomial (Fin r × Fin n) R), IsWeightedHomogeneous (rowW r n) f μ → (∀ (a b : Fin r) (k : ℕ), ∃ μ' : Fin r → ℕ, IsWeightedHomogeneous (rowW r n) (rowDiv R a b k f) μ') ∧ ∀ (a : Fin r) (k : ℕ), rowDiv R a a k f = ((μ a).choose k) • f := by
  first | exact @GlobalTheory.ValCmp.rowDiv_rowWeight | exact GlobalTheory.ValCmp.rowDiv_rowWeight | (intros; apply GlobalTheory.ValCmp.rowDiv_rowWeight <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeylLatticeExistsCofactorTwistDual

section

@[expose] public section

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem applyWord_hw_cofRel (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : Antitone ν)
    (h0 : ν (Fin.last m) = 0) (w : List (Fin (m + 1) × Fin (m + 1) × ℕ)) :
    (∃ μ : Fin (m + 1) → ℕ, IsWeightedHomogeneous (rowW (m + 1) (m + 1)) (applyWord R w (hw R le_rfl ν)) μ) ∧
      ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν (applyWord R w (hw R le_rfl ν)) g := by
  induction w with
  | nil => exact ⟨⟨_, hwRowWeight R _ _ le_rfl ν hν⟩, GlobalTheory.T.exists_cofactorTwist_highestWeight R m ν hν h0⟩
  | cons x w ih =>
    obtain ⟨a, b, k⟩ := x
    obtain ⟨⟨μ, hμ⟩, g, hg, hrel⟩ := ih
    have hstep : applyWord R ((a, b, k) :: w) (hw R le_rfl ν) =
        rowDiv R a b k (applyWord R w (hw R le_rfl ν)) := rfl
    rw [hstep]
    obtain ⟨h1, h2⟩ := GlobalTheory.T.isWeightedHomogeneous_div_and_diag_eq_choose_smul R _ _ μ _ hμ
    refine ⟨h1 a b k, ?_⟩
    by_cases hab : a = b
    · subst hab
      refine ⟨((μ a).choose k) • g, nsmul_mem hg _, ?_⟩
      rw [h2 a k]
      unfold CofRel at hrel ⊢
      rw [map_nsmul, ← hrel, mul_smul_comm]
    · exact ⟨_, zsmul_mem (weylRowDivStable R _ _ le_rfl _ b a k g hg) _, GlobalTheory.T.cofactorTwistRelation_rowDiv_swap R m ν a b k _ g hab hrel⟩

theorem weyl_exists_cofRel : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν →
    ν (Fin.last m) = 0 → ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl ν,
      ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν f g := by
  intro R _ _ m ν hν h0 f hf
  unfold weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact (applyWord_hw_cofRel R m ν hν h0 w).2
  | zero => exact ⟨0, zero_mem _, by simp [CofRel]⟩
  | add x y _ _ hx hy =>
    obtain ⟨g, hg, hr⟩ := hx
    obtain ⟨g', hg', hr'⟩ := hy
    refine ⟨g + g', add_mem hg hg', ?_⟩
    unfold CofRel at hr hr' ⊢
    rw [map_add (f := _), ← hr, ← hr', mul_add]
  | smul c x _ hx =>
    obtain ⟨g, hg, hr⟩ := hx
    refine ⟨c • g, Submodule.smul_mem _ c hg, ?_⟩
    unfold CofRel at hr ⊢
    rw [map_smul, ← hr, mul_smul_comm]

end GlobalTheory.ValCmp
end
end
