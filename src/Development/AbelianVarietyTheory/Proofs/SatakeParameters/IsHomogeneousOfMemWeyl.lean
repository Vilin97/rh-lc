module

public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.GradedWeylDivisibility.StatementA
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeylRowActionMemWeylLatticeSquare
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Mathlib.NumberTheory.Padics.Complex
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.KernelAwayPrimes
public import Formalism.LocalRingCardinality.DataKerP
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.RenameUpperLeftCornerMemWeylLattice

section

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory

namespace WeylRankEmbed

variable (R : Type) [CommRing R] {a b : ℕ} (hab : a ≤ b)

abbrev corner : Fin a × Fin a → Fin b × Fin b :=
  fun v => (Fin.castLE hab v.1, Fin.castLE hab v.2)

theorem rename_lpMinor (s : ℕ) (h1 : s ≤ a) (h2 : s ≤ b) :
    rename (corner hab) (lpMinor R s h1 h1) = lpMinor R s h2 h2 := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q : 2
  simp [corner]

theorem rename_hw (ν : Fin a → ℕ) (ν' : Fin b → ℕ)
    (h : ∀ j : Fin b, ν' j = if h : (j : ℕ) < a then ν ⟨j, h⟩ else 0) :
    rename (corner hab) (hw R le_rfl ν) = hw R le_rfl ν' := by
  unfold hw
  rw [map_prod]
  symm
  refine (Finset.prod_of_injOn (Fin.castLE hab) ((Fin.castLE_injective hab).injOn)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_).symm
  · intro j _ hj
    have hja : ¬ (j : ℕ) < a := by
      intro hlt
      exact hj ⟨⟨j, hlt⟩, by simp, by ext; simp⟩
    rw [h j, dite_eq_right hja]
    simp
  · intro i _
    rw [map_pow, rename_lpMinor R hab _ _ (by have := i.2; omega)]
    have e1 : ν' (Fin.castLE hab i) = ν i := by
      rw [h, dite_eq_left (by simp)]
      rfl
    have e2 : nuNext ν' (Fin.castLE hab i) = nuNext ν i := by
      unfold nuNext
      by_cases h1 : (i : ℕ) + 1 < a
      · rw [dite_eq_left h1, dite_eq_left (by simp; omega), h, dite_eq_left (by simpa using h1)]
        rfl
      · rw [dite_eq_right h1]
        split_ifs with h2
        · rw [h, dite_eq_right (by simpa using h1)]
        · rfl
    rw [e1, e2]
    rfl

theorem rename_rowDiv (x y : Fin a) (k : ℕ) (f : MvPolynomial (Fin a × Fin a) R) :
    rename (corner hab) (rowDiv R x y k f) =
      rowDiv R (Fin.castLE hab x) (Fin.castLE hab y) k (rename (corner hab) f) := by
  have key : (Polynomial.mapAlgHom (rename (R := R) (corner hab))).comp (rowGen R x y) =
      (rowGen R (Fin.castLE hab x) (Fin.castLE hab y)).comp (rename (corner hab)) := by
    apply MvPolynomial.algHom_ext
    intro v
    by_cases hv : v.1 = y
    · simp [rowGen, hv, corner]
    · have hv' : Fin.castLE hab v.1 ≠ Fin.castLE hab y := fun e => hv (Fin.castLE_injective hab e)
      simp [rowGen, hv, corner]
  have h2 := congrArg (fun φ => (φ f).coeff k) key
  simpa [rowDiv, Polynomial.coeff_map] using h2

theorem rename_applyWord (w : List (Fin a × Fin a × ℕ)) (f : MvPolynomial (Fin a × Fin a) R) :
    rename (corner hab) (applyWord R w f) =
      applyWord R (w.map fun x => (Fin.castLE hab x.1, Fin.castLE hab x.2.1, x.2.2))
        (rename (corner hab) f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons, List.map_cons] at ih ⊢
    rw [rename_rowDiv, ih]

end WeylRankEmbed

theorem weyl_rename_castLE_mem :
    ∀ (R : Type) [CommRing R] (a b : ℕ) (hab : a ≤ b) (ν : Fin a → ℕ) (ν' : Fin b → ℕ), (∀ j : Fin b, ν' j = if h : (j : ℕ) < a then ν ⟨j, h⟩ else 0) → ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R a a le_rfl ν, MvPolynomial.rename (fun v : Fin a × Fin a => ((Fin.castLE hab v.1, Fin.castLE hab v.2) : Fin b × Fin b)) f ∈ Formalism.GradedWeylDivisibility.weyl R b b le_rfl ν' := by
  intro R _ a b hab ν ν' h f hf
  change rename (WeylRankEmbed.corner hab) f ∈ _
  unfold weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨w.map fun x => (Fin.castLE hab x.1, Fin.castLE hab x.2.1, x.2.2), ?_⟩
    simp only
    rw [WeylRankEmbed.rename_applyWord, WeylRankEmbed.rename_hw R hab ν ν' h]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.RenameUpperLeftCornerMemWeylLatticeStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.rename_upperLeftCorner_mem_weylLattice : ∀ (R : Type) [CommRing R] (a b : ℕ) (hab : a ≤ b) (ν : Fin a → ℕ) (ν' : Fin b → ℕ), (∀ j : Fin b, ν' j = if h : (j : ℕ) < a then ν ⟨j, h⟩ else 0) → ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R a a le_rfl ν, MvPolynomial.rename (fun v : Fin a × Fin a => ((Fin.castLE hab v.1, Fin.castLE hab v.2) : Fin b × Fin b)) f ∈ Formalism.GradedWeylDivisibility.weyl R b b le_rfl ν' := by
  first | exact @GlobalTheory.weyl_rename_castLE_mem | exact GlobalTheory.weyl_rename_castLE_mem | (intros; apply GlobalTheory.weyl_rename_castLE_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeylRowActionMemWeylLatticeSquareStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.weylRowAction_mem_weylLattice_square : ∀ (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ (M : Matrix (Fin n) (Fin n) R), ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν, Formalism.GradedWeylDivisibility.rowAct R M f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν := by
  first | exact @GlobalTheory.WeylRowAll.rowAct_mem_weyl_square | exact GlobalTheory.WeylRowAll.rowAct_mem_weyl_square | (intros; apply GlobalTheory.WeylRowAll.rowAct_mem_weyl_square <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHomogeneousOfMemWeyl

section

@[expose] public section

noncomputable section

namespace GlobalTheory.LiftTypePrime

open NumberField MvPolynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

section Generic

open Formalism.GradedWeylDivisibility

variable {a b : ℕ} (hab : a ≤ b)

def subGen : MvPolynomial (Fin a × Fin a) ℤ →ₐ[ℤ] MvPolynomial (Fin b × Fin a) (MvPolynomial (Fin b × Fin b) ℤ) :=
  aeval fun v => ∑ β : Fin b, C (X (β, Fin.castLE hab v.2)) * X (β, v.1)

theorem aeval_subGen {A : Type} [CommRing A] (d : Fin b × Fin a → A) (y : Fin b × Fin b → A)
    (f : MvPolynomial (Fin a × Fin a) ℤ) :
    aeval (fun v : Fin a × Fin a => ∑ β : Fin b, y (β, Fin.castLE hab v.2) * d (β, v.1)) f =
      ∑ α ∈ (subGen hab f).support, aeval y ((subGen hab f).coeff α) * ∏ v ∈ α.support, d v ^ α v := by
  have h := eval₂_eq (aeval (R := ℤ) y).toRingHom d (subGen hab f)
  refine Eq.trans ?_ h
  have : (aeval (R := ℤ) (fun v : Fin a × Fin a => ∑ β : Fin b, y (β, Fin.castLE hab v.2) * d (β, v.1))).toRingHom =
      (eval₂Hom (aeval (R := ℤ) y).toRingHom d).comp (subGen hab).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun v => ?_
    simp [subGen]
  exact RingHom.congr_fun this f

theorem isHomogeneous_of_mem_weyl {ν : Fin a → ℕ} (hν : Antitone ν) {f : MvPolynomial (Fin a × Fin a) ℤ}
    (hf : f ∈ weyl ℤ a a le_rfl ν) : f.IsHomogeneous (∑ r, ν r) := by
  have h : IsWeightedHomogeneous (colW a a) f ν := (weylLeDual ℤ a a le_rfl ν hν hf).1
  intro m hm
  rw [← h hm]
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, colW]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Pi.single_apply]

theorem subGen_isHomogeneous {n : ℕ} {f : MvPolynomial (Fin a × Fin a) ℤ} (hf : f.IsHomogeneous n) :
    (subGen hab f).IsHomogeneous n := by
  have := hf.aeval (fun v : Fin a × Fin a => ∑ β : Fin b,
    (C (X (β, Fin.castLE hab v.2)) * X (β, v.1) : MvPolynomial (Fin b × Fin a) (MvPolynomial (Fin b × Fin b) ℤ)))
    (n := 1) (fun v => IsHomogeneous.sum _ _ _ fun β _ => isHomogeneous_C_mul_X _ _)
  rw [one_mul] at this
  exact this

theorem coeff_subGen_mem {ν : Fin a → ℕ} {ν' : Fin b → ℕ} (hν : Antitone ν')
    (h : ∀ j : Fin b, ν' j = if h : (j : ℕ) < a then ν ⟨j, h⟩ else 0) {f : MvPolynomial (Fin a × Fin a) ℤ}
    (hf : f ∈ weyl ℤ a a le_rfl ν) (α : Fin b × Fin a →₀ ℕ) : (subGen hab f).coeff α ∈ weyl ℤ b b le_rfl ν' := by
  let S := MvPolynomial (Fin b × Fin a) ℤ
  let M : Matrix (Fin b) (Fin b) S := fun i β => if h : (i : ℕ) < a then X (β, ⟨i, h⟩) else 0
  have h1 := GlobalTheory.T.rename_upperLeftCorner_mem_weylLattice ℤ a b hab ν ν' h f hf
  have hmap : ∀ g ∈ weyl ℤ b b le_rfl ν', map (algebraMap ℤ S) g ∈ weyl S b b le_rfl ν' := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact Submodule.subset_span ⟨w, by
        beta_reduce
        rw [← lclosedeq_hw_map (algebraMap ℤ S), lclosedeq_applyWord_map]⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := map (algebraMap ℤ S))]; exact add_mem hx hy
    | smul c x _ hx => rw [map_zsmul]; exact zsmul_mem hx c
  have h2 := GlobalTheory.T.weylRowAction_mem_weylLattice_square S b ν' hν M _ (hmap _ h1)
  let ψ : MvPolynomial (Fin b × Fin b) S →+* MvPolynomial (Fin b × Fin a) (MvPolynomial (Fin b × Fin b) ℤ) :=
    eval₂Hom (map (algebraMap ℤ _)) fun v => C (X v)
  have hψ : ∀ g : MvPolynomial (Fin b × Fin b) ℤ, ψ (map (algebraMap ℤ S) g) = C g := fun g => by
    have : ψ.comp (map (algebraMap ℤ S)) = C :=
      MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun v => by simp [ψ]
    exact RingHom.congr_fun this g
  have e : subGen hab f = ψ (rowAct S M (map (algebraMap ℤ S) (rename (fun v : Fin a × Fin a =>
      ((Fin.castLE hab v.1, Fin.castLE hab v.2) : Fin b × Fin b)) f))) := by
    have : (subGen hab).toRingHom = ψ.comp ((rowAct S M).toRingHom.comp ((map (algebraMap ℤ S)).comp
        (rename (fun v : Fin a × Fin a => ((Fin.castLE hab v.1, Fin.castLE hab v.2) : Fin b × Fin b))).toRingHom)) := by
      refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun v => ?_
      simp [subGen, rowAct, ψ, M, mul_comm]
      exact Finset.sum_congr rfl fun x _ => congrArg (· * _) (map_X _ _).symm
    exact RingHom.congr_fun this f
  rw [e]
  generalize rowAct S M _ = F at h2
  induction h2 using Submodule.span_induction generalizing α with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    have : applyWord S w (hw S le_rfl ν') = map (algebraMap ℤ S) (applyWord ℤ w (hw ℤ le_rfl ν')) := by
      rw [← lclosedeq_hw_map (algebraMap ℤ S), lclosedeq_applyWord_map]
    simp only [this, hψ, coeff_C]
    split_ifs
    · exact Submodule.subset_span ⟨w, rfl⟩
    · exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), AddMonoidAlgebra.coeff_add]; exact add_mem (hx α) (hy α)
  | smul c x _ hx =>
    classical
    rw [smul_eq_C_mul, map_mul, coeff_mul]
    refine Submodule.sum_mem _ fun p _ => ?_
    have : ψ (C c) = map (algebraMap ℤ _) c := by simp [ψ]
    rw [this, coeff_map, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hx _)

end Generic

section Integral

variable {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]}

variable {D : D7} {N : ℕ} {wt : D.what₂.Tau → DomWeight N}

variable {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {O : LiftObj D (D.chTw u μ)} {i : ℕ}

end Integral

section Subst

variable {D : D7} {N N' : ℕ}

end Subst

section Lift

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup}

theorem natW_anti {n : ℕ} (l : DomWeight n) : Antitone l.natW := fun _ _ h =>
  Int.toNat_le_toNat (sub_le_sub_right (l.anti h) _)

end Lift

end GlobalTheory.LiftTypePrime

end
end
end
