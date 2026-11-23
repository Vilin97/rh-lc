module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBilinCyclic
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLComm

section

@[expose] public section

noncomputable section

namespace GlobalTheory.HCCommF

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

variable {F : Type} [Field F]

def aflip {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  (M.submatrix Fin.revPerm Fin.revPerm).transpose

theorem aflip_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : Fin n) : aflip M i j = M j.rev i.rev := rfl

theorem aflip_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) F) : aflip (M * N) = aflip N * aflip M := by
  unfold aflip
  rw [← Matrix.transpose_mul, Matrix.submatrix_mul_equiv]

theorem aflip_one {n : ℕ} : aflip (1 : Matrix (Fin n) (Fin n) F) = 1 := by
  unfold aflip
  rw [Matrix.submatrix_one_equiv, Matrix.transpose_one]

theorem aflip_aflip {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : aflip (aflip M) = M := by
  ext i j; simp [aflip_apply]

theorem aflip_similar {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    ∃ P : Matrix (Fin n) (Fin n) F, IsUnit P ∧ P * M = aflip M * P := by
  obtain ⟨P, hP, h⟩ := GlobalTheory.SimilarTranspose.main F (Fin n) (M.submatrix Fin.revPerm Fin.revPerm)
  let Q : Matrix (Fin n) (Fin n) F := (1 : Matrix (Fin n) (Fin n) F).submatrix Fin.revPerm (Equiv.refl _)
  have hQ : IsUnit Q := by
    have : Q * (1 : Matrix (Fin n) (Fin n) F).submatrix (Equiv.refl _) Fin.revPerm = 1 := by
      simp only [Q]
      rw [Matrix.submatrix_mul_equiv, mul_one, Matrix.submatrix_one_equiv]
    exact IsUnit.of_mul_eq_one _ this
  have hQM : Q * M = M.submatrix Fin.revPerm Fin.revPerm * Q := by
    have h1 : Q * M = Q * M.submatrix (Equiv.refl _) (Equiv.refl _) := rfl
    rw [h1]
    simp only [Q]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, one_mul, mul_one]
  refine ⟨P * Q, hP.mul hQ, ?_⟩
  rw [mul_assoc, hQM, ← mul_assoc, h, mul_assoc]
  rfl

def aflipG {n : ℕ} (x : GL (Fin n) F) : GL (Fin n) F where
  val := aflip (x : Matrix (Fin n) (Fin n) F)
  inv := aflip ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  val_inv := by rw [← aflip_mul, Units.inv_mul, aflip_one]
  inv_val := by rw [← aflip_mul, Units.mul_inv, aflip_one]

theorem aflipG_coe {n : ℕ} (x : GL (Fin n) F) :
    ((aflipG x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = aflip (x : Matrix (Fin n) (Fin n) F) := rfl

theorem aflipG_mul {n : ℕ} (x y : GL (Fin n) F) : aflipG (x * y) = aflipG y * aflipG x :=
  Units.ext (by simp only [aflipG_coe, Units.val_mul, aflip_mul])

theorem aflipG_inv {n : ℕ} (x : GL (Fin n) F) : aflipG x⁻¹ = (aflipG x)⁻¹ := Units.ext rfl

theorem aflipG_aflipG {n : ℕ} (x : GL (Fin n) F) : aflipG (aflipG x) = x := Units.ext (aflip_aflip _)

def aflipE (n : ℕ) : GL (Fin n) F ≃ GL (Fin n) F := ⟨aflipG, aflipG, aflipG_aflipG, aflipG_aflipG⟩

theorem aflipG_conj {n : ℕ} (x : GL (Fin n) F) : ∃ p : GL (Fin n) F, aflipG x = p * x * p⁻¹ := by
  obtain ⟨P, hP, h⟩ := aflip_similar (x : Matrix (Fin n) (Fin n) F)
  refine ⟨hP.unit, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact Units.ext (by simp only [Units.val_mul, aflipG_coe, IsUnit.unit_spec, h])

theorem toG_coe' {n : ℕ} (x : GL (Fin n) F) : toG (x : Matrix (Fin n) (Fin n) F) = x := by
  unfold toG
  rw [dite_eq_left x.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

theorem cl_conj {n : ℕ} {α : GL (Fin n) F → ℂ} (hα : IsCl α) (p x : GL (Fin n) F) :
    α (p * x * p⁻¹) = α x := by
  have := hα x p⁻¹
  rwa [inv_inv] at this

theorem class_aflip {n : ℕ} {α : GL (Fin n) F → ℂ} (hα : IsCl α) (M : Matrix (Fin n) (Fin n) F) :
    α (toG (aflip M)) = α (toG M) := by
  by_cases h : IsUnit M
  · obtain ⟨x, rfl⟩ := h
    obtain ⟨p, hp⟩ := aflipG_conj x
    have h1 : toG (aflip (x : Matrix (Fin n) (Fin n) F)) = aflipG x := toG_coe' (aflipG x)
    rw [h1, toG_coe', hp, cl_conj hα]
  · have h' : ¬ IsUnit (aflip M) := by
      rintro ⟨x, hx⟩
      exact h ⟨aflipG x, by rw [aflipG_coe, hx, aflip_aflip]⟩
    unfold toG
    rw [dite_eq_right h, dite_eq_right h']

theorem inPar_aflip {a b : ℕ} (y : GL (Fin (a + b)) F) : InPar b (aflipG y) ↔ InPar a y := by
  constructor
  · intro h i j hj hi
    have := h j.rev i.rev (by rw [Fin.val_rev]; omega) (by rw [Fin.val_rev]; omega)
    simpa [aflipG_coe, aflip_apply] using this
  · intro h i j hj hi
    rw [aflipG_coe, aflip_apply]
    exact h j.rev i.rev (by rw [Fin.val_rev]; omega) (by rw [Fin.val_rev]; omega)

theorem tl_aflip {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : tl b (aflip M) = aflip (br a b M) := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [aflip_apply]
  unfold tl br ent
  rw [dite_eq_left (by omega), dite_eq_left (by simp only [Fin.val_rev]; omega), aflip_apply]
  congr 1 <;> apply Fin.ext <;> simp only [Fin.val_rev] <;> omega

theorem br_aflip {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) F) : br b a (aflip M) = aflip (tl a M) := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [aflip_apply]
  unfold tl br ent
  rw [dite_eq_left (by omega), dite_eq_left (by simp only [Fin.val_rev]; omega), aflip_apply]
  congr 1 <;> apply Fin.ext <;> simp only [Fin.val_rev] <;> omega

theorem gal_id (n : ℕ) (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j; simp [gal]

end GlobalTheory.HCCommF
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLCommStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
private lemma hc_conj_invariant {F : Type} [Field F] (a b n : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (x p : GL (Fin n) F) :
    hc a b α β n (p * x * p⁻¹) = hc a b α β n x := by
  unfold hc hcTw
  simp only [GlobalTheory.HCCommF.gal_id]
  congr 1
  rw [← finsum_comp_equiv (Equiv.mulLeft p)]
  congr 1
  funext y
  have h : ((Equiv.mulLeft p) y)⁻¹ * (p * x * p⁻¹) * (Equiv.mulLeft p) y = y⁻¹ * x * y := by
    change (p * y)⁻¹ * (p * x * p⁻¹) * (p * y) = y⁻¹ * x * y
    simp [mul_assoc]
  rw [h]

private lemma inPar_swap_eq_inPar_aflipG {F : Type} [Field F] (a b : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β) (z : GL (Fin (a + b)) F) :
    (if InPar b z then β (tlG b z) * α (brG b a z) else 0) =
      (if InPar a (GlobalTheory.HCCommF.aflipG z) then
        α (tlG a (GlobalTheory.HCCommF.aflipG z)) * β (brG a b (GlobalTheory.HCCommF.aflipG z)) else 0) := by
  obtain ⟨w, rfl⟩ : ∃ w, z = GlobalTheory.HCCommF.aflipG w :=
    ⟨GlobalTheory.HCCommF.aflipG z, (GlobalTheory.HCCommF.aflipG_aflipG z).symm⟩
  rw [GlobalTheory.HCCommF.aflipG_aflipG, GlobalTheory.HCCommF.inPar_aflip]
  unfold tlG brG
  rw [GlobalTheory.HCCommF.aflipG_coe, GlobalTheory.HCCommF.tl_aflip, GlobalTheory.HCCommF.br_aflip,
    GlobalTheory.HCCommF.class_aflip hβ, GlobalTheory.HCCommF.class_aflip hα, mul_comm (β _)]

private lemma hc_swap_eq_hc_aflipG {F : Type} [Field F] (a b : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β) (x : GL (Fin (a + b)) F) :
    hc b a β α (a + b) x = hc a b α β (a + b) (GlobalTheory.HCCommF.aflipG x) := by
  unfold hc hcTw
  simp only [GlobalTheory.HCCommF.gal_id]
  have hcard : Nat.card {p : GL (Fin (a + b)) F // InPar b p} =
      Nat.card {p : GL (Fin (a + b)) F // InPar a p} :=
    Nat.card_congr (Equiv.subtypeEquiv (GlobalTheory.HCCommF.aflipE (F := F) (a + b)) (fun p => by
      show InPar b p ↔ InPar a (GlobalTheory.HCCommF.aflipG p)
      conv_lhs => rw [← GlobalTheory.HCCommF.aflipG_aflipG p]
      exact GlobalTheory.HCCommF.inPar_aflip _))
  rw [hcard]
  congr 1
  conv_rhs => rw [← finsum_comp_equiv ((GlobalTheory.HCCommF.aflipE (F := F) (a + b)).trans (Equiv.inv _))]
  congr 1
  funext y
  rw [inPar_swap_eq_inPar_aflipG a b α β hα hβ]
  have h : GlobalTheory.HCCommF.aflipG (y⁻¹ * x * y) =
      ((GlobalTheory.HCCommF.aflipG y)⁻¹)⁻¹ * GlobalTheory.HCCommF.aflipG x * (GlobalTheory.HCCommF.aflipG y)⁻¹ := by
    rw [inv_inv, GlobalTheory.HCCommF.aflipG_mul, GlobalTheory.HCCommF.aflipG_mul, GlobalTheory.HCCommF.aflipG_inv, mul_assoc]
  rw [h]
  rfl


theorem _root_.GlobalTheory.T.harishChandraInductionGL_comm : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsCl α → IsCl β → n = a + b → hc a b α β n = hc b a β α n := by
  intro F _ _ a b n α β hα hβ hn
  subst hn
  funext x
  rw [hc_swap_eq_hc_aflipG a b α β hα hβ x]
  obtain ⟨p, hp⟩ := GlobalTheory.HCCommF.aflipG_conj x
  rw [hp, hc_conj_invariant]
end
end
