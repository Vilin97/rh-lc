module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IwahoriFactorisation
public import Mathlib.Data.Matrix.Mul
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UdlApply

section

@[expose] public section

namespace GlobalTheory.UnipotentDecomposition

open Matrix

theorem udl_apply {O : Type} [CommRing O] {m : ℕ} (A B : Matrix (Fin m) (Fin m) O) (d : Fin m → O) (i j : Fin m) :
    (A * Matrix.diagonal d * B) i j = ∑ k, A i k * d k * B k j := by
  rw [Matrix.mul_apply]; simp_rw [Matrix.mul_diagonal]

theorem key {O : Type} [CommRing O] [IsLocalRing O] {α β : O} (hab : ¬ IsUnit (α * β)) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O),
      (∀ i j, (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)) → (∀ i, IsUnit (g i i)) →
      ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O),
        (∀ i j, (j < i → u i j = 0) ∧ (i = j → u i j = 1) ∧ (i < j → α ∣ u i j)) ∧
        (∀ i j, (i < j → l i j = 0) ∧ (i = j → l i j = 1) ∧ (j < i → β ∣ l i j)) ∧
        g = (u * Matrix.diagonal fun i => (d i : O)) * l ∧ ∀ i, α * β ∣ (d i : O) - g i i := by
  intro n
  induction n with
  | zero =>
    intro g _ _
    refine ⟨1, fun i => i.elim0, 1, fun i => i.elim0, fun i => i.elim0, ?_, fun i => i.elim0⟩
    ext i; exact i.elim0
  | succ n ih =>
    intro g hg hu
    set a : Oˣ := (hu (Fin.last n)).unit with ha
    have haa : (a : O) = g (Fin.last n) (Fin.last n) := IsUnit.unit_spec _
    have hinv : (↑a⁻¹ : O) * ↑a = 1 := Units.inv_mul a
    set r : Fin n → O := fun i => g i.castSucc (Fin.last n) with hr_def
    set c : Fin n → O := fun j => g (Fin.last n) j.castSucc with hc_def
    set G : Matrix (Fin n) (Fin n) O := fun i j => g i.castSucc j.castSucc - r i * ↑a⁻¹ * c j with hG_def
    have hr : ∀ i, α ∣ r i := fun i => (hg i.castSucc (Fin.last n)).1 (Fin.castSucc_lt_last i)
    have hc : ∀ j, β ∣ c j := fun j => (hg (Fin.last n) j.castSucc).2 (Fin.castSucc_lt_last j)
    have hG : ∀ i j, (i < j → α ∣ G i j) ∧ (j < i → β ∣ G i j) := by
      intro i j
      constructor
      · intro h
        exact dvd_sub ((hg _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h))
          (Dvd.dvd.mul_right (Dvd.dvd.mul_right (hr i) _) _)
      · intro h
        exact dvd_sub ((hg _ _).2 (Fin.castSucc_lt_castSucc_iff.2 h)) (Dvd.dvd.mul_left (hc j) _)
    have hrc : ∀ i, α * β ∣ r i * ↑a⁻¹ * c i := by
      intro i
      rw [show r i * ↑a⁻¹ * c i = r i * c i * ↑a⁻¹ by ring]
      exact Dvd.dvd.mul_right (mul_dvd_mul (hr i) (hc i)) _
    have hGu : ∀ i, IsUnit (G i i) := by
      intro i
      by_contra h
      have h1 : r i * ↑a⁻¹ * c i ∈ nonunits O := fun hu' => hab (isUnit_of_dvd_unit (hrc i) hu')
      have h2 := IsLocalRing.nonunits_add (show G i i ∈ nonunits O from h) h1
      have h3 : G i i + r i * ↑a⁻¹ * c i = g i.castSucc i.castSucc := sub_add_cancel _ _
      rw [h3] at h2
      exact h2 (hu _)
    obtain ⟨U, D, L, hU, hL, hUDL, hD⟩ := ih G hG hGu
    refine ⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => O)
              (Fin.lastCases (motive := fun _ => O) 1 (fun _ => 0) j)
              (fun i' => Fin.lastCases (motive := fun _ => O) (r i' * ↑a⁻¹) (fun j' => U i' j') j) i,
            fun i => Fin.lastCases (motive := fun _ => Oˣ) a D i,
            Matrix.of fun i j => Fin.lastCases (motive := fun _ => O)
              (Fin.lastCases (motive := fun _ => O) 1 (fun j' => ↑a⁻¹ * c j') j)
              (fun i' => Fin.lastCases (motive := fun _ => O) 0 (fun j' => L i' j') j) i,
            ?_, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last j).ne', not_lt_of_gt (Fin.castSucc_lt_last j)]
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last i).ne, not_lt_of_gt (Fin.castSucc_lt_last i)]
        first | exact hr i | exact (hr i).mul_right _
      · simpa using hU i j
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last j).ne', not_lt_of_gt (Fin.castSucc_lt_last j)]
        first | exact hc j | exact (hc j).mul_left _
      · simp [Fin.castSucc_lt_last, (Fin.castSucc_lt_last i).ne, not_lt_of_gt (Fin.castSucc_lt_last i)]
      · simpa using hL i j
    · ext i j
      rw [udl_apply, Fin.sum_univ_castSucc]
      refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [haa]
      · simp [c]
        done
      · simp [r]
        done
      · have e := congrFun (congrFun hUDL i) j
        rw [udl_apply] at e
        simp only [Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero, add_zero, mul_one]
        rw [← e]
        simp only [G]
        linear_combination (-(r i * ↑a⁻¹ * c j)) * hinv
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [haa]
      · have e : ((D i : O)) - g i.castSucc i.castSucc = ((D i : O) - G i i) - r i * ↑a⁻¹ * c i := by
          simp [G]; ring
        simpa [e] using dvd_sub (hD i) (hrc i)

theorem main : (let d1 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (β : O) (l : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → l i j = (0 : O)) ∧ (i = j → l i j = (1 : O)) ∧ (j < i → β ∣ l i j)); let d2 : {O : Type} → [CommRing O] → {n : ℕ} → O → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α β : O) (g : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)); let d3 : {O : Type} → [CommRing O] → {n : ℕ} → O → Matrix (Fin n) (Fin n) O → Prop := @(fun {O : Type} [CommRing O] {n : ℕ} (α : O) (u : Matrix (Fin n) (Fin n) O) ↦ ∀ (i j : Fin n), (j < i → u i j = (0 : O)) ∧ (i = j → u i j = (1 : O)) ∧ (i < j → α ∣ u i j)); ∀ {O : Type} [inst : CommRing O] [IsLocalRing O] {α β : O}, ¬IsUnit (α * β) → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), d2 α β g → (∀ (i : Fin n), IsUnit (g i i)) → ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O), d3 α u ∧ d1 β l ∧ g = (u * Matrix.diagonal fun (i : Fin n) ↦ (↑(d i) : O)) * l ∧ ∀ (i : Fin n), α * β ∣ (↑(d i) : O) - g i i) := by
  intro d1 d2 d3 O _ _ α β hab n g hg hu
  exact key hab n g hg hu

end GlobalTheory.UnipotentDecomposition
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdInvOfBlockTriangular

section

@[expose] public section

open Polynomial

namespace GlobalTheory.IwahoriFactor

section General

variable {O : Type} [CommRing O] {n : ℕ}

def Shape (α β : O) (g : Matrix (Fin n) (Fin n) O) : Prop :=
  ∀ i j, (i < j → α ∣ g i j) ∧ (j < i → β ∣ g i j)

def UpperUnip (α : O) (u : Matrix (Fin n) (Fin n) O) : Prop :=
  ∀ i j, (j < i → u i j = 0) ∧ (i = j → u i j = 1) ∧ (i < j → α ∣ u i j)

def LowerUnip (β : O) (l : Matrix (Fin n) (Fin n) O) : Prop :=
  ∀ i j, (i < j → l i j = 0) ∧ (i = j → l i j = 1) ∧ (j < i → β ∣ l i j)

theorem Shape.mul {α β : O} {x y : Matrix (Fin n) (Fin n) O} (hx : Shape α β x)
    (hy : Shape α β y) : Shape α β (x * y) := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.dvd_sum fun k _ => ?_
    rcases lt_or_ge i k with hk | hk
    · exact ((hx i k).1 hk).mul_right _
    · exact ((hy k j).1 (hk.trans_lt h)).mul_left _
  · rw [Matrix.mul_apply]
    refine Finset.dvd_sum fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · exact ((hx i k).2 hk).mul_right _
    · exact ((hy k j).2 (h.trans_le hk)).mul_left _

theorem dvd_inv_of_blockTriangular {ι : Type} [LinearOrder ι] (b : Fin n → ι) (γ : O)
    (g : GL (Fin n) O) (hg : ∀ i j, b j < b i → γ ∣ (g : Matrix (Fin n) (Fin n) O) i j) :
    ∀ i j, b j < b i → γ ∣ ((g⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) i j := by
  let f := Ideal.Quotient.mk (Ideal.span {γ})
  have hf : ∀ x, f x = 0 ↔ γ ∣ x := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have h1 : ((g : Matrix (Fin n) (Fin n) O).map f) *
      (((g⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O).map f) = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero f) (map_one f)]
  letI := invertibleOfRightInverse _ _ h1
  have h2 : ((g : Matrix (Fin n) (Fin n) O).map f).BlockTriangular b :=
    fun i j h => (hf _).2 (hg i j h)
  have h3 := Matrix.blockTriangular_inv_of_blockTriangular h2
  rw [Matrix.inv_eq_right_inv h1] at h3
  intro i j h
  exact (hf _).1 (h3 h)

theorem Shape.inv {α β : O} {g : GL (Fin n) O} (hg : Shape α β (g : Matrix (Fin n) (Fin n) O)) :
    Shape α β ((g⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact dvd_inv_of_blockTriangular (ι := (Fin n)ᵒᵈ) OrderDual.toDual α g
      (fun i j h => (hg i j).1 h) i j h
  · exact dvd_inv_of_blockTriangular id β g (fun i j h => (hg i j).2 h) i j h

theorem UpperUnip.shape {α : O} (β : O) {u : Matrix (Fin n) (Fin n) O} (hu : UpperUnip α u) :
    Shape α β u := fun i j =>
  ⟨(hu i j).2.2, fun h => by rw [(hu i j).1 h]; exact dvd_zero _⟩

theorem LowerUnip.shape (α : O) {β : O} {l : Matrix (Fin n) (Fin n) O} (hl : LowerUnip β l) :
    Shape α β l := fun i j =>
  ⟨fun h => by rw [(hl i j).1 h]; exact dvd_zero _, (hl i j).2.2⟩

theorem Shape.diagonal (α β : O) (d : Fin n → O) : Shape α β (Matrix.diagonal d) := fun i j =>
  ⟨fun h => by rw [Matrix.diagonal_apply_ne _ h.ne]; exact dvd_zero _,
    fun h => by rw [Matrix.diagonal_apply_ne _ h.ne']; exact dvd_zero _⟩

theorem UpperUnip.det {α : O} {u : Matrix (Fin n) (Fin n) O} (hu : UpperUnip α u) :
    u.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j h => (hu i j).1 h)]
  exact Finset.prod_eq_one fun i _ => (hu i i).2.1 rfl

theorem LowerUnip.det {β : O} {l : Matrix (Fin n) (Fin n) O} (hl : LowerUnip β l) :
    l.det = 1 := by
  rw [Matrix.det_of_lowerTriangular l (fun i j h => (hl i j).1 h)]
  exact Finset.prod_eq_one fun i _ => (hl i i).2.1 rfl

theorem factor_unique {α β α' β' : O} {u u' l l' : Matrix (Fin n) (Fin n) O} {d d' : Fin n → Oˣ}
    (hu : UpperUnip α u) (hu' : UpperUnip α' u') (hl : LowerUnip β l) (hl' : LowerUnip β' l')
    (h : u * Matrix.diagonal (fun i => (d i : O)) * l =
      u' * Matrix.diagonal (fun i => (d' i : O)) * l') :
    u = u' ∧ d = d' ∧ l = l' := by
  have iu' : IsUnit u'.det := by rw [hu'.det]; exact isUnit_one
  have il : IsUnit l.det := by rw [hl.det]; exact isUnit_one
  letI := u'.invertibleOfIsUnitDet iu'
  letI := l.invertibleOfIsUnitDet il
  have tu : u.BlockTriangular id := fun i j h => (hu i j).1 h
  have tu' : u'.BlockTriangular id := fun i j h => (hu' i j).1 h
  have tl : l.BlockTriangular OrderDual.toDual := fun i j h => (hl i j).1 h
  have tl' : l'.BlockTriangular OrderDual.toDual := fun i j h => (hl' i j).1 h
  set X := u'⁻¹ * (u * Matrix.diagonal (fun i => (d i : O))) with hX
  have e1 : u' * X = u * Matrix.diagonal (fun i => (d i : O)) := by
    rw [hX, Matrix.mul_nonsing_inv_cancel_left _ _ iu']
  have e2 : X * l = Matrix.diagonal (fun i => (d' i : O)) * l' := by
    rw [hX, Matrix.mul_assoc, h, Matrix.mul_assoc u', Matrix.nonsing_inv_mul_cancel_left _ _ iu']
  have e3 : X = Matrix.diagonal (fun i => (d' i : O)) * l' * l⁻¹ := by
    rw [← e2, Matrix.mul_nonsing_inv_cancel_right _ _ il]
  have tX : X.BlockTriangular id :=
    (Matrix.blockTriangular_inv_of_blockTriangular tu').mul
      (tu.mul (Matrix.blockTriangular_diagonal _))
  have tX' : X.BlockTriangular OrderDual.toDual := by
    rw [e3]
    exact ((Matrix.blockTriangular_diagonal _).mul tl').mul
      (Matrix.blockTriangular_inv_of_blockTriangular tl)
  have hd : X = Matrix.diagonal (fun i => X i i) := by
    ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [Matrix.diagonal_apply_ne _ h.ne]; exact tX' h
    · rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h.ne']; exact tX h
  rw [hd] at e1 e2
  have f1 : ∀ i j, u' i j * X j j = u i j * d j := fun i j => by
    simpa [Matrix.mul_diagonal] using congrFun (congrFun e1 i) j
  have f2 : ∀ i j, X i i * l i j = d' i * l' i j := fun i j => by
    simpa [Matrix.diagonal_mul] using congrFun (congrFun e2 i) j
  have g1 : ∀ i, X i i = d i := fun i => by
    simpa [(hu i i).2.1 rfl, (hu' i i).2.1 rfl] using f1 i i
  have g2 : ∀ i, X i i = d' i := fun i => by
    simpa [(hl i i).2.1 rfl, (hl' i i).2.1 rfl] using f2 i i
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have := f1 i j
    rw [g1] at this
    exact ((Units.mul_left_inj _).1 this).symm
  · funext i
    exact Units.ext ((g1 i).symm.trans (g2 i))
  · ext i j
    have := f2 i j
    rw [g2] at this
    exact (Units.mul_right_inj _).1 this

theorem exists_factor [IsLocalRing O] {α β : O} (hαβ : ¬ IsUnit (α * β)) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), Shape α β g → (∀ i, IsUnit (g i i)) →
      ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O),
        UpperUnip α u ∧ LowerUnip β l ∧ g = u * Matrix.diagonal (fun i => (d i : O)) * l ∧
          ∀ i, α * β ∣ (d i : O) - g i i := by
  first
  | exact @_root_.GlobalTheory.UnipotentDecomposition.main
  | exact _root_.GlobalTheory.UnipotentDecomposition.main
  | (apply _root_.GlobalTheory.UnipotentDecomposition.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnipotentDecomposition.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnipotentDecomposition.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnipotentDecomposition.main ..)

theorem isUnit_diag [IsLocalRing O] {α β : O} (hβ : ¬ IsUnit β) {g : Matrix (Fin n) (Fin n) O}
    (hdet : IsUnit g.det) (hg : Shape α β g) (i : Fin n) : IsUnit (g i i) := by
  let f := IsLocalRing.residue O
  have h0 : ∀ x, f x = 0 ↔ ¬ IsUnit x := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have h1 : (g.map f).BlockTriangular id := fun i j h =>
    (h0 _).2 fun hu => hβ (isUnit_of_dvd_unit ((hg i j).2 h) hu)
  have h2 : f g.det = ∏ k, f (g k k) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.det_of_upperTriangular h1]
    rfl
  by_contra hi
  have h3 : f g.det = 0 := by
    rw [h2]; exact Finset.prod_eq_zero (Finset.mem_univ i) ((h0 _).2 hi)
  exact (h0 _).1 h3 hdet

def flip (g : Matrix (Fin n) (Fin n) O) : Matrix (Fin n) (Fin n) O :=
  g.submatrix Fin.revPerm Fin.revPerm

theorem flip_apply (g : Matrix (Fin n) (Fin n) O) (i j : Fin n) :
    flip g i j = g i.rev j.rev := rfl

theorem flip_flip (g : Matrix (Fin n) (Fin n) O) : flip (flip g) = g := by
  ext i j; simp [flip_apply]

theorem flip_triple (u l : Matrix (Fin n) (Fin n) O) (d : Fin n → O) :
    flip (u * Matrix.diagonal d * l) =
      flip u * Matrix.diagonal (fun i => d i.rev) * flip l := by
  unfold flip
  rw [← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm, ← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm,
    Matrix.submatrix_diagonal_equiv]
  rfl

theorem Shape.flip {α β : O} {g : Matrix (Fin n) (Fin n) O} (hg : Shape α β g) :
    Shape β α (flip g) := fun i j =>
  ⟨fun h => (hg _ _).2 (Fin.rev_lt_rev.2 h), fun h => (hg _ _).1 (Fin.rev_lt_rev.2 h)⟩

theorem UpperUnip.flip {α : O} {u : Matrix (Fin n) (Fin n) O} (hu : UpperUnip α u) :
    LowerUnip α (flip u) := fun i j =>
  ⟨fun h => (hu _ _).1 (Fin.rev_lt_rev.2 h), fun h => (hu _ _).2.1 (congrArg Fin.rev h),
    fun h => (hu _ _).2.2 (Fin.rev_lt_rev.2 h)⟩

theorem LowerUnip.flip {β : O} {l : Matrix (Fin n) (Fin n) O} (hl : LowerUnip β l) :
    UpperUnip β (flip l) := fun i j =>
  ⟨fun h => (hl _ _).1 (Fin.rev_lt_rev.2 h), fun h => (hl _ _).2.1 (congrArg Fin.rev h),
    fun h => (hl _ _).2.2 (Fin.rev_lt_rev.2 h)⟩

theorem not_isUnit_mul {α β : O} (hβ : ¬ IsUnit β) : ¬ IsUnit (α * β) :=
  fun h => hβ (isUnit_of_mul_isUnit_right h)

theorem existsUnique_factor [IsLocalRing O] {α β : O} (hβ : ¬ IsUnit β) (g : GL (Fin n) O)
    (hg : Shape α β (g : Matrix (Fin n) (Fin n) O)) :
    ∃! p : Matrix (Fin n) (Fin n) O × (Fin n → Oˣ) × Matrix (Fin n) (Fin n) O,
      UpperUnip α p.1 ∧ LowerUnip β p.2.2 ∧
        (g : Matrix (Fin n) (Fin n) O) = p.1 * Matrix.diagonal (fun i => (p.2.1 i : O)) * p.2.2 := by
  first
  | exact @_root_.GlobalTheory.UnipotentBorder.iwahori_factorisation
  | exact _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation
  | (apply _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnipotentBorder.iwahori_factorisation <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation ..)

theorem existsUnique_factor_opp [IsLocalRing O] {α β : O} (hβ : ¬ IsUnit β) (g : GL (Fin n) O)
    (hg : Shape α β (g : Matrix (Fin n) (Fin n) O)) :
    ∃! p : Matrix (Fin n) (Fin n) O × (Fin n → Oˣ) × Matrix (Fin n) (Fin n) O,
      LowerUnip β p.1 ∧ UpperUnip α p.2.2 ∧
        (g : Matrix (Fin n) (Fin n) O) = p.1 * Matrix.diagonal (fun i => (p.2.1 i : O)) * p.2.2 := by
  obtain ⟨u, d, l, hu, hl, hfac, -⟩ :=
    exists_factor (α := β) (β := α) (by rw [mul_comm]; exact not_isUnit_mul hβ) n _ hg.flip
      (fun i => isUnit_diag hβ (Matrix.isUnits_det_units g) hg i.rev)
  have hfac2 := congrArg flip hfac
  rw [flip_flip, flip_triple] at hfac2
  refine ⟨(flip u, fun i => d i.rev, flip l), ⟨hu.flip, hl.flip, hfac2⟩, ?_⟩
  rintro ⟨l', d', u'⟩ ⟨hl', hu', hfac'⟩
  have hfac3 := congrArg flip hfac'
  rw [flip_triple] at hfac3
  obtain ⟨h1, h2, h3⟩ := factor_unique (d' := fun i => d' i.rev) hu hl'.flip hl hu'.flip
    (hfac.symm.trans hfac3)
  subst h1 h2 h3
  simp [flip_flip]

end General

end GlobalTheory.IwahoriFactor
end
end
