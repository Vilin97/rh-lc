module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorFormula
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.CayDivOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.Bridge
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.CayDiv
public import Mathlib.RingTheory.Derivation.Lie
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
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.SPrimeOfAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.SecOneConst

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.DerivationConstantVanishes

section

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP

variable {n : ℕ}

namespace CommPf

def cc (s : ℂ) (b : Bool) : ℂ := if b then Complex.I * s else -(Complex.I * s)

def al (m : ℕ) (b : Bool) : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X

def k0 (s : ℂ) (b : Bool) : Fm n := MvPolynomial.C (Polynomial.C (-(cc s b)))

def mm (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : Fm n := k0 s b * (MvPolynomial.C (al m b) * yv b l k)

def dl (s : ℂ) (b : Bool) (k l : Fin n) : Derivation (Polynomial ℂ) (Fm n) (Fm n) :=
  MvPolynomial.mkDerivation (Polynomial ℂ)
    (fun v => if v.1 = b then k0 s b * (yv b v.2.1 k * yv b l v.2.2) else 0)

theorem dl_X (s : ℂ) (b : Bool) (k l : Fin n) (v : Bool × Fin n × Fin n) :
    dl s b k l (X v) = if v.1 = b then k0 s b * (yv b v.2.1 k * yv b l v.2.2) else 0 := by
  simp [dl, MvPolynomial.mkDerivation_X]

theorem smul_eq (c : ℂ) (p : Fm n) : c • p = MvPolynomial.C (Polynomial.C c) * p := by
  rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply]
  rfl

theorem sum_eq (s : ℂ) (b : Bool) (k l : Fin n) (p : Fm n) :
    (∑ a : Fin n, ∑ d : Fin n, (-(cc s b)) • (yv b a k * yv b l d * MvPolynomial.pderiv (b, a, d) p)) = dl s b k l p := by
  let D : Derivation (Polynomial ℂ) (Fm n) (Fm n) :=
    ∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) • MvPolynomial.pderiv (b, a, d)
  have hD : ∀ q : Fm n, D q = ∑ a : Fin n, ∑ d : Fin n, (-(cc s b)) • (yv b a k * yv b l d * MvPolynomial.pderiv (b, a, d) q) := by
    intro q
    have : (D : Fm n → Fm n) = fun q => ∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) * MvPolynomial.pderiv (b, a, d) q := by
      funext q
      simp only [D]
      rw [show ((∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) • MvPolynomial.pderiv (b, a, d) :
          Derivation (Polynomial ℂ) (Fm n) (Fm n)) q) =
          Derivation.coeFnAddMonoidHom (∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) • MvPolynomial.pderiv (b, a, d)) q from rfl]

      rw [map_sum]

      simp only [map_sum, Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, smul_eq_mul]
    rw [this]
    simp only [smul_eq, k0]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have hDl : D = dl s b k l := by
    apply MvPolynomial.derivation_ext
    intro v
    rw [dl_X]
    have : (D : Fm n → Fm n) (X v) = ∑ a : Fin n, ∑ d : Fin n, (k0 s b * (yv b a k * yv b l d)) * MvPolynomial.pderiv (b, a, d) (X v) := by
      rw [hD]
      simp only [smul_eq, k0]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
      ring
    rw [this]
    obtain ⟨b0, a0, d0⟩ := v
    simp only [MvPolynomial.pderiv_X, Pi.single_apply]
    by_cases hb : b0 = b
    · subst hb
      simp only [if_true]
      rw [Finset.sum_eq_single a0, Finset.sum_eq_single d0]
      · simp
      · intro d _ hd; simp [Prod.ext_iff, Ne.symm hd]
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro a _ ha; apply Finset.sum_eq_zero; intro d _; simp [Prod.ext_iff, Ne.symm ha]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hb]
      apply Finset.sum_eq_zero; intro a _; apply Finset.sum_eq_zero; intro d _
      have : ¬ ((b0, a0, d0) = (b, a, d)) := fun h => hb (congrArg Prod.fst h)
      simp only [Pi.single_apply, this, if_false, mul_zero]
  rw [← hD, hDl]

theorem opH_apply (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) (p : Fm n) :
    opH s m b k l p = mm s m b k l * p + dl s b k l p := by
  rw [← sum_eq]
  simp only [opH, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.coe_restrictScalars, LinearMap.mulLeft_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, Derivation.coeFn_coe]
  rw [smul_eq]
  simp only [mm, k0, cc, al]
  congr 1
  split_ifs <;> ring

theorem dl_other (s : ℂ) (b b' : Bool) (h : b ≠ b') (k l a d : Fin n) : dl s b k l (yv b' a d) = 0 := by
  rw [yv, dl_X]; simp [Ne.symm h]

theorem dl_C (s : ℂ) (b : Bool) (k l : Fin n) (r : Polynomial ℂ) : dl s b k l (MvPolynomial.C r) = 0 :=
  MvPolynomial.derivation_C _ r

theorem derivation_constant_vanishes (s : ℂ) (b b' : Bool) (k l : Fin n) : dl s b k l (k0 s b' : Fm n) = 0 := dl_C _ _ _ _ _

theorem dl_yv (s : ℂ) (b : Bool) (k l a d : Fin n) : dl s b k l (yv b a d) = k0 s b * (yv b a k * yv b l d) := by
  rw [yv, dl_X]; simp

theorem key1 (s : ℂ) (m : ℕ) (b b' : Bool) (k l k' l' : Fin n) :
    dl s b k l (mm s m b' k' l') = dl s b' k' l' (mm s m b k l) := by
  simp only [mm, Derivation.leibniz, derivation_constant_vanishes, dl_C, smul_zero, add_zero, smul_eq_mul]
  by_cases h : b = b'
  · subst h
    rw [dl_yv, dl_yv]; ring
  · rw [dl_other s b b' h, dl_other s b' b (Ne.symm h)]; ring

theorem key2 (s : ℂ) (b b' : Bool) (k l k' l' : Fin n) : ⁅dl s b k l, dl s b' k' l'⁆ = 0 := by
  apply MvPolynomial.derivation_ext
  intro v
  rw [Derivation.commutator_apply, dl_X, dl_X]
  obtain ⟨b0, a0, d0⟩ := v
  by_cases h1 : b0 = b' <;> by_cases h2 : b0 = b
  · subst h1; subst h2
    simp only [if_true, Derivation.leibniz, derivation_constant_vanishes, dl_yv, smul_zero, add_zero, smul_eq_mul]
    simp
    ring
  · subst h1
    simp only [if_true, if_neg h2, Derivation.map_zero, Derivation.leibniz, derivation_constant_vanishes, smul_zero, add_zero, smul_eq_mul,
      dl_other s b b0 (Ne.symm h2)]
    simp
  · subst h2
    simp only [if_true, if_neg h1, Derivation.map_zero, Derivation.leibniz, derivation_constant_vanishes, smul_zero, add_zero, smul_eq_mul,
      dl_other s b' b0 (Ne.symm h1)]
    simp
  · simp [if_neg h1, if_neg h2]

end CommPf


open CommPf in
theorem comm : Comm := by
  intro n s m b b' k l k' l'
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, CommPf.opH_apply, Derivation.leibniz, map_add (f := _), smul_eq_mul]
  have h2 : CommPf.dl s b k l (CommPf.dl s b' k' l' p) = CommPf.dl s b' k' l' (CommPf.dl s b k l p) := by
    have := congrArg (fun D : Derivation (Polynomial ℂ) (Fm n) (Fm n) => D p) (CommPf.key2 s b b' k l k' l')
    simpa [Derivation.commutator_apply, sub_eq_zero] using this
  rw [h2, CommPf.key1 s m b b' k l k' l']
  ring

end PositivityTheory.Rg.Sw.SP
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.DetEqZeroOfRankLt

section

@[expose] public section

noncomputable section

open MvPolynomial Matrix Module

namespace PositivityTheory.Rg.Sw.SP

namespace NullPf

variable {K : Type*} [Field K]

theorem exists_rows {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] (M : Matrix m n K) {k : ℕ} (hk : k ≤ M.rank) :
    ∃ I : Fin k ↪ m, LinearIndependent K (fun p => M (I p)) := by
  classical
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent K (Set.range M.row)
  have hfin : b.Finite := (Set.finite_range _).subset hbs
  have : Fintype b := hfin.fintype
  have hcard : M.rank = b.toFinset.card := by
    rw [M.rank_eq_finrank_span_row, ← hspan]
    exact finrank_span_set_eq_card hli
  have hkb : k ≤ Fintype.card b := by rw [← Set.toFinset_card]; omega
  let e : Fin k ↪ b := (Fin.castLEEmb hkb).trans (Fintype.equivFin b).symm.toEmbedding
  let sec : b → m := fun v => (hbs v.2).choose
  have hsec : ∀ v : b, M.row (sec v) = v := fun v => (hbs v.2).choose_spec
  have hinj : Function.Injective sec := by
    intro v w h
    apply Subtype.ext
    rw [← hsec v, ← hsec w, h]
  refine ⟨e.trans ⟨sec, hinj⟩, ?_⟩
  have h2 : (fun p => M ((e.trans ⟨sec, hinj⟩) p)) = (fun v : b => (v : n → K)) ∘ e := by
    funext p
    simp only [Function.comp_apply, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
    exact hsec (e p)
  rw [h2]
  exact hli.comp e e.injective

theorem exists_minor_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {k : ℕ} (hk : k ≤ M.rank) :
    ∃ I J : Fin k ↪ Fin n, (M.submatrix I J).det ≠ 0 := by
  classical
  obtain ⟨I, hI⟩ := exists_rows M hk
  set R : Matrix (Fin k) (Fin n) K := M.submatrix I id with hR
  have hRrank : R.rank = k := by
    have : LinearIndependent K R.row := hI
    simpa using this.rank_matrix
  have hRt : k ≤ Rᵀ.rank := by rw [rank_transpose, hRrank]
  obtain ⟨J, hJ⟩ := exists_rows Rᵀ hRt
  refine ⟨I, J, ?_⟩
  set T : Matrix (Fin k) (Fin k) K := Rᵀ.submatrix J id with hT
  have hTu : IsUnit T := by
    rw [← linearIndependent_rows_iff_isUnit]
    exact hJ
  have hTeq : T = (M.submatrix I J)ᵀ := by
    ext p q
    simp [T, R, transpose_apply, submatrix_apply]
  have := (Matrix.isUnit_iff_isUnit_det T).1 hTu
  rw [hTeq, det_transpose] at this
  exact this.ne_zero

theorem rank_lt_of_minors {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {k : ℕ}
    (h : ∀ I J : Fin k ↪ Fin n, (M.submatrix I J).det = 0) : M.rank < k := by
  by_contra hc
  obtain ⟨I, J, hIJ⟩ := exists_minor_ne_zero M (not_lt.1 hc)
  exact hIJ (h I J)

theorem rank_add_le' {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) : (A + B).rank ≤ A.rank + B.rank := by
  simp only [← Matrix.finrank_range_mulVecLin]
  rw [Matrix.mulVecLin_add]
  calc finrank K (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ finrank K ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin : Submodule K (Fin n → K)) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

theorem det_eq_zero_of_rank_lt {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : M.rank < n) : M.det = 0 := by
  by_contra hd
  have := Matrix.rank_of_isUnit M ((Matrix.isUnit_iff_isUnit_det M).2 (Ne.isUnit hd))
  simp at this
  omega

end NullPf

open NullPf in
theorem null : Null := by
  classical
  intro n m hmn N₀
  set S : Set (PAB n) := {x : PAB n | ∃ i j : ℕ, i + j = n - m ∧
        ((i = 0 ∧ j = 0 ∧ x = 1) ∨
         (i = 0 ∧ 0 < j ∧ ∃ (I J : Fin j ↪ Fin n), x = minorPolynomial true I J ^ N₀) ∨
         (0 < i ∧ j = 0 ∧ ∃ (I J : Fin (m + i) ↪ Fin n), x = minorPolynomial false I J ^ N₀) ∨
         (0 < i ∧ 0 < j ∧ ∃ (I J : Fin (m + i) ↪ Fin n) (I' J' : Fin j ↪ Fin n),
            x = minorPolynomial false I J ^ N₀ * minorPolynomial true I' J' ^ N₀))} with hS
  set D : PAB n := Matrix.det (fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n)) with hD
  suffices hrad : D ∈ (Ideal.span S).radical from (Ideal.mem_radical_iff).1 hrad
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
  intro x hx
  rw [mem_zeroLocus_iff] at hx
  have hgen : ∀ s ∈ S, aeval x s = 0 := fun s hs => hx s (Ideal.subset_span hs)
  set A : Matrix (Fin n) (Fin n) ℂ := fun p q => x (false, p, q) with hA
  set B : Matrix (Fin n) (Fin n) ℂ := fun p q => x (true, p, q) with hB
  have hminor : ∀ (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n),
      aeval x (minorPolynomial b I J) = Matrix.det (fun p q : Fin ρ => x (b, I p, J q)) := by
    intro b ρ I J
    calc aeval x (minorPolynomial b I J) = ((aeval x : PAB n →ₐ[ℂ] ℂ) : PAB n →+* ℂ) (minorPolynomial b I J) := rfl
      _ = _ := by
        have h := RingHom.map_det ((aeval x : PAB n →ₐ[ℂ] ℂ) : PAB n →+* ℂ)
          (Matrix.of fun p q : Fin ρ => (X (b, I p, J q) : PAB n))
        refine h.trans ?_
        congr 1
        ext p q
        simp
  have hpow : ∀ (a : ℂ), a ^ N₀ = 0 → a = 0 := fun a h => ((pow_eq_zero_iff' (M₀ := ℂ)).1 h).1
  have hr : 0 < n - m := by omega

  have hBr : B.rank < n - m := by
    apply rank_lt_of_minors
    intro I J
    have := hgen (minorPolynomial true I J ^ N₀) ⟨0, n - m, by omega, Or.inr (Or.inl ⟨rfl, hr, I, J, rfl⟩)⟩
    rw [map_pow, hminor] at this
    exact hpow _ this
  have hsum : (A + B).rank < n := by
    rcases Nat.eq_zero_or_pos B.rank with h0 | hpos
    · have hAr : A.rank < m + (n - m) := by
        apply rank_lt_of_minors
        intro I J
        have := hgen (minorPolynomial false I J ^ N₀) ⟨n - m, 0, by omega, Or.inr (Or.inr (Or.inl ⟨hr, rfl, I, J, rfl⟩))⟩
        rw [map_pow, hminor] at this
        exact hpow _ this
      have := rank_add_le' A B
      omega
    · obtain ⟨I', J', hIJ'⟩ := exists_minor_ne_zero B (le_refl B.rank)
      have hAr : A.rank < m + (n - m - B.rank) := by
        apply rank_lt_of_minors
        intro I J
        have := hgen (minorPolynomial false I J ^ N₀ * minorPolynomial true I' J' ^ N₀)
          ⟨n - m - B.rank, B.rank, by omega, Or.inr (Or.inr (Or.inr ⟨by omega, hpos, I, J, I', J', rfl⟩))⟩
        rw [map_mul, map_pow, map_pow, hminor, hminor] at this
        rcases mul_eq_zero.1 this with h | h
        · exact hpow _ h
        · exact absurd (hpow _ h) hIJ'
      have := rank_add_le' A B
      omega
  have hdet := det_eq_zero_of_rank_lt (A + B) hsum
  calc aeval x D = ((aeval x : PAB n →ₐ[ℂ] ℂ) : PAB n →+* ℂ) D := rfl
    _ = (A + B).det := by
        have h := RingHom.map_det ((aeval x : PAB n →ₐ[ℂ] ℂ) : PAB n →+* ℂ)
          (Matrix.of fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n))
        refine h.trans ?_
        congr 1
        ext p q
        simp [A, B, Matrix.add_apply]
        rfl
    _ = 0 := hdet

end PositivityTheory.Rg.Sw.SP
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorZ

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Rg.Sw.SP

open Polynomial

theorem divZ_C_mul {n : ℕ} (i : ℕ) (p : Polynomial ℂ) (R : Fm n) (h : (X : Polynomial ℂ) ^ i ∣ p) :
    DivZ i (MvPolynomial.C p * R) := by
  intro e
  rw [MvPolynomial.coeff_C_mul]
  exact Dvd.dvd.mul_right h _

theorem pow_dvd_prod (N ρ i : ℕ) (f : ℕ → ℕ → Polynomial ℂ) (hi : i ≤ N)
    (hf : ∀ l < i, ∃ i' < ρ, f l i' = -X) :
    (X : Polynomial ℂ) ^ i ∣ ∏ l ∈ Finset.range N, ∏ i' ∈ Finset.range ρ, f l i' := by
  have h1 : (X : Polynomial ℂ) ^ i = ∏ _l ∈ Finset.range i, (X : Polynomial ℂ) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [h1]
  refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ fun l hl => ?_)
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono hi))
  obtain ⟨i', hi', he⟩ := hf l (Finset.mem_range.1 hl)
  have h2 : f l i' ∣ ∏ i' ∈ Finset.range ρ, f l i' := Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hi')
  rw [he] at h2
  exact dvd_trans (dvd_neg.2 dvd_rfl) h2

theorem minorZ_of (hF : MinorFormula) : MinorZ := by
  intro n s hs m i N hiN I J
  rw [hF n s hs m false (m + i) N I J]
  apply divZ_C_mul
  apply Dvd.dvd.mul_left
  apply pow_dvd_prod N (m + i) i _ hiN
  intro l hl
  refine ⟨m + l, by omega, ?_⟩
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_add, map_sub, map_add (f := _)]
  ring

theorem minorZ'_of (hF : MinorFormula) : MinorZ' := by
  intro n s hs m j N hjN I J
  rw [hF n s hs m true j N I J]
  apply divZ_C_mul
  apply Dvd.dvd.mul_left
  apply pow_dvd_prod N j j _ hjN
  intro l hl
  refine ⟨l, hl, ?_⟩
  simp only [↓reduceIte, sub_self, map_zero, sub_zero]

end PositivityTheory.Rg.Sw.SP
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.SPrimeOfMinor

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.SP

theorem sPrime_of_minor (h : MinorFormula) : SPrime :=
  sPrime_of bridge (cayDiv_of comm (minorZ_of h) (minorZ'_of h) null)

theorem wrOrd_of_minor (h : MinorFormula) : PositivityTheory.SiegelWeilFormula.Gen.WROrd := wrOrd_of (sPrime_of_minor h)

end PositivityTheory.Rg.Sw.SP
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.SPrime

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.SP

theorem wrOrd : PositivityTheory.SiegelWeilFormula.Gen.WROrd := wrOrd_of_minor minorFormula

end PositivityTheory.Rg.Sw.SP
end
end
