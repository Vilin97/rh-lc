module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Mathlib.RingTheory.Ideal.Maps
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.WittVector.DiscreteValuationRing

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTer

section

@[expose] public section

namespace GlobalTheory.ClosedStatement

open Ideal Module

theorem main {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (m : Ideal R)
    [hm : Ideal.IsMaximal m] (hne : Ideal.map f m ≠ ⊤) :
    ∃ (ι : Type) (b : ι → A) (i₀ : ι), b i₀ = (1 : A) ∧
      (∀ x : A, ∃ a : ι →₀ R, (x - Finsupp.sum a fun (i : ι) (y : R) ↦ (f : R → A) y * b i)
        ∈ Ideal.map f m) ∧
      ∀ a : ι →₀ R, (Finsupp.sum a fun (i : ι) (y : R) ↦ (f : R → A) y * b i) ∈ Ideal.map f m →
        ∀ i : ι, (a : ι → R) i ∈ m := by
  classical
  letI : Algebra R A := f.toAlgebra
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have hf : algebraMap R A = f := rfl
  rw [← hf] at hne ⊢
  haveI : Nontrivial (A ⧸ Ideal.map (algebraMap R A) m) := Ideal.Quotient.nontrivial_iff.mpr hne
  have hli : LinearIndepOn (R ⧸ m) id ({1} : Set (A ⧸ Ideal.map (algebraMap R A) m)) :=
    (linearIndepOn_singleton_iff (R ⧸ m)).mpr one_ne_zero
  let v := Basis.extend hli
  have h1mem : (1 : A ⧸ Ideal.map (algebraMap R A) m) ∈ hli.extend (Set.subset_univ _) :=
    Basis.subset_extend hli rfl
  let b : ↥(hli.extend (Set.subset_univ _)) → A := fun i =>
    if (i : A ⧸ Ideal.map (algebraMap R A) m) = 1 then 1
    else (Ideal.Quotient.mk_surjective (i : A ⧸ Ideal.map (algebraMap R A) m)).choose
  have hb : ∀ i, Ideal.Quotient.mk (Ideal.map (algebraMap R A) m) (b i) = v i := by
    intro i
    rw [Basis.coe_extend]
    simp only [b]
    split_ifs with h
    · rw [map_one, h]
    · exact (Ideal.Quotient.mk_surjective _).choose_spec
  have key : ∀ a : ↥(hli.extend (Set.subset_univ _)) →₀ R,
      Ideal.Quotient.mk (Ideal.map (algebraMap R A) m)
        (Finsupp.sum a fun i y ↦ (algebraMap R A) y * b i) =
      Finsupp.linearCombination (R ⧸ m) v (a.mapRange (Ideal.Quotient.mk m) (map_zero _)) := by
    intro a
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp), map_finsuppSum]
    refine Finsupp.sum_congr (fun i _ => ?_)
    rw [map_mul, hb, Algebra.smul_def, Ideal.Quotient.algebraMap_quotient_map_quotient]
  refine ⟨_, b, ⟨1, h1mem⟩, by simp [b], ?_, ?_⟩
  · intro x
    let g : R ⧸ m → R := fun c => if c = 0 then 0 else (Ideal.Quotient.mk_surjective c).choose
    have hg : ∀ c, Ideal.Quotient.mk m (g c) = c := by
      intro c
      simp only [g]
      split_ifs with h
      · rw [h, map_zero]
      · exact (Ideal.Quotient.mk_surjective c).choose_spec
    refine ⟨(v.repr (Ideal.Quotient.mk _ x)).mapRange g (by simp [g]), ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, key]
    have hc : ∀ c : ↥(hli.extend (Set.subset_univ _)) →₀ R ⧸ m,
        (c.mapRange g (by simp [g])).mapRange (Ideal.Quotient.mk m) (map_zero _) = c := by
      intro c; ext i; simp [hg]
    rw [hc, Basis.linearCombination_repr, sub_self]
  · intro a ha i
    rw [← Ideal.Quotient.eq_zero_iff_mem, key] at ha
    have h0 := linearIndependent_iff.mp v.linearIndependent _ ha
    have := congrArg (fun l => l i) h0
    simpa [Ideal.Quotient.eq_zero_iff_mem] using this

end GlobalTheory.ClosedStatement
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealSpanPrimeVariableBasis

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_residue_basis_of_isMaximal {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (m : Ideal R)
    [hm : m.IsMaximal] (h : m.map f ≠ ⊤) :
    ∃ (ι : Type) (b : ι → A) (i₀ : ι), b i₀ = 1 ∧
      (∀ x : A, ∃ a : ι →₀ R, x - a.sum (fun i y => f y * b i) ∈ m.map f) ∧
      ∀ a : ι →₀ R, a.sum (fun i y => f y * b i) ∈ m.map f → ∀ i, a i ∈ m := by
  first
  | exact @_root_.GlobalTheory.ClosedStatement.main
  | exact _root_.GlobalTheory.ClosedStatement.main
  | (apply _root_.GlobalTheory.ClosedStatement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosedStatement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosedStatement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosedStatement.main ..)

theorem isMaximal_span_l_sup_span_X (l a : ℕ) [Fact l.Prime] [NeZero a] :
    (Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(X : (Wq l a)⟦X⟧)}).IsMaximal := by
  have hmax : (Ideal.span {(l : Wq l a)}).IsMaximal := by
    rw [← (WittVector.irreducible l (k := Fq l a)).maximalIdeal_eq]
    infer_instance
  have hsurj : Function.Surjective (constantCoeff (R := Wq l a)) := fun w => ⟨C w, by simp⟩
  have heq : Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(X : (Wq l a)⟦X⟧)} =
      (Ideal.span {(l : Wq l a)}).comap (constantCoeff (R := Wq l a)) := by
    apply le_antisymm
    · refine sup_le ?_ ?_ <;> rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      · rw [map_natCast]
        exact Ideal.mem_span_singleton_self _
      · simp
    · intro x hx
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hx)
      have hX : (X : (Wq l a)⟦X⟧) ∣ x - C w * l := by
        rw [X_dvd_iff, map_sub, map_mul, map_natCast, constantCoeff_C, hw, sub_self]
      have : x = C w * l + (x - C w * l) := by ring
      rw [this]
      exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
        (Ideal.mem_span_singleton.2 hX)
  rw [heq]
  exact Ideal.comap_isMaximal_of_surjective _ hsurj

theorem BK.map_span_l_sup_span_X_ne_top {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev ≠ ⊤ := by
  let M : Ideal (Ainf l) := (IsLocalRing.maximalIdeal (OC l)).comap (Per.θ l)
  haveI hM : M.IsPrime := Ideal.comap_isPrime _ _
  let N : Ideal bk.S := M.comap bk.ev
  haveI hN : N.IsPrime := Ideal.comap_isPrime _ _
  have hl : (l : bk.S) ∈ N := by
    change Per.θ l (bk.ev l) ∈ IsLocalRing.maximalIdeal (OC l)
    rw [map_natCast, map_natCast]
    exact (Fact.out : ¬ IsUnit (l : OC l))
  have hE : bk.E ∈ N := by
    change Per.θ l (bk.ev bk.E) ∈ IsLocalRing.maximalIdeal (OC l)
    have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker.1 this]
    exact Ideal.zero_mem _
  have hX : (X : bk.S) ∈ N := by
    apply hN.mem_of_pow_mem bk.Ep.natDegree
    have h1 := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) bk.monic.as_sum

    rw [map_add (f := _), map_pow, map_sum] at h1
    have hs : ∑ i ∈ Finset.range bk.Ep.natDegree, Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)
        (Polynomial.C (bk.Ep.coeff i) * Polynomial.X ^ i) ∈ N := by
      refine Ideal.sum_mem _ fun i hi => ?_
      obtain ⟨w, hw⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
      rw [hw, map_mul, map_mul, map_mul, map_natCast, map_natCast]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hl)
    have h2 := N.sub_mem hE hs
    simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X] at h1 h2
    have h3 := sub_eq_of_eq_add h1
    rwa [h3] at h2
  intro htop
  apply hM.ne_top
  rw [eq_top_iff, ← htop, Ideal.map_le_iff_le_comap]
  exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hl) ((Ideal.span_singleton_le_iff_mem _).2 hX)

theorem BK.exists_residue_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    ∃ (ι : Type) (b : ι → Ainf l) (i₀ : ι), b i₀ = 1 ∧
      (∀ x : Ainf l, ∃ a : ι →₀ bk.S, x - a.sum (fun i y => bk.ev y * b i) ∈
        (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev) ∧
      ∀ a : ι →₀ bk.S, a.sum (fun i y => bk.ev y * b i) ∈
        (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev →
        ∀ i, a i ∈ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} := by
  intro l _ K bk
  haveI := isMaximal_span_l_sup_span_X l bk.a
  exact exists_residue_basis_of_isMaximal bk.ev _ bk.map_span_l_sup_span_X_ne_top

end GlobalTheory.BSP
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealSpanPrimeVariableBasisStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.ideal_span_prime_variable_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (ι : Type) (b : ι → Ainf l) (i₀ : ι), b i₀ = 1 ∧ (∀ x : Ainf l, ∃ a : ι →₀ bk.S, x - a.sum (fun i y => bk.ev y * b i) ∈ (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev) ∧ ∀ a : ι →₀ bk.S, a.sum (fun i y => bk.ev y * b i) ∈ (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev → ∀ i, a i ∈ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} := by
  first | exact @GlobalTheory.BSP.BK.exists_residue_basis | exact GlobalTheory.BSP.BK.exists_residue_basis | (intros; apply GlobalTheory.BSP.BK.exists_residue_basis <;> assumption)
end
end
