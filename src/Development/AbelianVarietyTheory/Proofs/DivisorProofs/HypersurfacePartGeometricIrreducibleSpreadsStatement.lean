module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
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
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplittingAbsenceSpreadsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypersurfaceDiffIsPreirreducibleOfNoSplitting

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem exists_prime_factor_mem_prime_ideal_ufd {R : Type} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (I : Ideal R) [hI : I.IsPrime] (a : R) (ha : a ≠ 0)
    (haI : a ∈ I) : ∃ u : R, Prime u ∧ u ∣ a ∧ u ∈ I := by
  induction a using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl ha
  | h₂ x hx => exact absurd (I.eq_top_of_isUnit_mem haI hx) hI.ne_top
  | h₃ a p ha' hp ih =>
    rcases hI.mem_or_mem haI with h | h
    · exact ⟨p, hp, dvd_mul_right _ _, h⟩
    · obtain ⟨u, hu, hua, huI⟩ := ih (right_ne_zero_of_mul ha) h
      exact ⟨u, hu, dvd_mul_of_dvd_right hua _, huI⟩

theorem hypersurface_diff_isPreirreducible (Ω : Type) [Field Ω] [IsAlgClosed Ω] (σ : Type) [Finite σ]
    (f g : MvPolynomial σ Ω) (D : ℕ) (hf0 : f ≠ 0) (hfD : f.totalDegree ≤ D)
    (hno : ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧
      ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧
        MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0)) :
    IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) := by
  intro U V hU hV ⟨p, hpS, hpU⟩ ⟨q, hqS, hqV⟩
  have hfp : f ∈ p.asIdeal := by simpa using hpS.1
  have hgp : g ∉ p.asIdeal := by simpa using hpS.2
  obtain ⟨u, hu, huf, hup⟩ := exists_prime_factor_mem_prime_ideal_ufd p.asIdeal f hf0 hfp
  obtain ⟨v, rfl⟩ := huf
  have hu0 : u ≠ 0 := hu.ne_zero
  have hv0 : v ≠ 0 := right_ne_zero_of_mul hf0
  have hdeg := MvPolynomial.totalDegree_mul_of_isDomain hu0 hv0

  have hgrad : g ∉ (Ideal.span {u}).radical := by
    intro hg
    apply hgp
    have : (Ideal.span {u}).radical ≤ p.asIdeal :=
      (Ideal.radical_mono ((Ideal.span_singleton_le_iff_mem _).mpr hup)).trans
        p.isPrime.radical.le
    exact this hg
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω)] at hgrad
  simp only [MvPolynomial.mem_vanishingIdeal_iff, not_forall] at hgrad
  obtain ⟨P, hP, hPg⟩ := hgrad
  have hPu : MvPolynomial.eval P u = 0 := by
    have := hP u (Ideal.mem_span_singleton_self u)
    simpa [MvPolynomial.aeval_eq_eval] using this
  have hPg' : MvPolynomial.eval P g ≠ 0 := by simpa [MvPolynomial.aeval_eq_eval] using hPg

  have hvg : g ∈ (Ideal.span {v}).radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω)]
    intro Q hQ
    have hQv : MvPolynomial.eval Q v = 0 := by
      have := hQ v (Ideal.mem_span_singleton_self v)
      simpa [MvPolynomial.aeval_eq_eval] using this
    by_contra hQg
    apply hno
    refine ⟨u, v, by omega, by omega, rfl, P, Q, hPu, hPg', hQv, ?_⟩
    simpa [MvPolynomial.aeval_eq_eval] using hQg

  have hprime : (Ideal.span {u}).IsPrime := (Ideal.span_singleton_prime hu0).mpr hu
  let x : PrimeSpectrum (MvPolynomial σ Ω) := ⟨Ideal.span {u}, hprime⟩
  have key : ∀ y ∈ PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g},
      y ∈ closure ({x} : Set _) := by
    intro y hy
    have hfy : u * v ∈ y.asIdeal := by simpa using hy.1
    have hgy : g ∉ y.asIdeal := by simpa using hy.2
    rw [← PrimeSpectrum.le_iff_mem_closure]
    show Ideal.span {u} ≤ y.asIdeal
    rw [Ideal.span_singleton_le_iff_mem]
    rcases y.isPrime.mem_or_mem hfy with h | h
    · exact h
    · exfalso; apply hgy
      have : (Ideal.span {v}).radical ≤ y.asIdeal :=
        (Ideal.radical_mono ((Ideal.span_singleton_le_iff_mem _).mpr h)).trans
          y.isPrime.radical.le
      exact this hvg
  have hxS : x ∈ PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g} := by
    constructor
    · simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
      exact Ideal.mem_span_singleton.mpr (dvd_mul_right u v)
    · simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
      intro hg
      exact hgp (((Ideal.span_singleton_le_iff_mem _).mpr hup) hg)
  have hxU : x ∈ U := by
    have := key p hpS
    rw [mem_closure_iff] at this
    obtain ⟨z, hzU, hz⟩ := this U hU hpU
    rw [Set.mem_singleton_iff.mp hz] at hzU; exact hzU
  have hxV : x ∈ V := by
    have := key q hqS
    rw [mem_closure_iff] at this
    obtain ⟨z, hzV, hz⟩ := this V hV hqV
    rw [Set.mem_singleton_iff.mp hz] at hzV; exact hzV
  exact ⟨x, hxS, hxU, hxV⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypersurfaceDiffIsPreirreducibleOfNoSplittingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.hypersurface_diff_isPreirreducible_of_no_splitting : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (σ : Type) [Finite σ] (f g : MvPolynomial σ Ω) (D : ℕ), f ≠ 0 → f.totalDegree ≤ D → ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧ ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) := by
  first | exact @GlobalTheory.hypersurface_diff_isPreirreducible | exact GlobalTheory.hypersurface_diff_isPreirreducible | (intros; apply GlobalTheory.hypersurface_diff_isPreirreducible <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoSplittingFactorisationOfPderivNeZero

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem hypersurface_part_no_splitting_factorisation :
    ∀ (Ω : Type) [Field Ω] (σ : Type) (f g : MvPolynomial σ Ω) (i : σ) (D : ℕ),
      (∀ Q : σ → Ω, MvPolynomial.eval Q f = 0 → MvPolynomial.eval Q g ≠ 0 →
        MvPolynomial.eval Q (MvPolynomial.pderiv i f) ≠ 0) →
      IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) →
      ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧
        ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧
          MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0) := by
  intro Ω _ σ f g i D hsmooth hirr ⟨u, v, _, _, huv, P, Q, hPu, hPg, hQv, hQg⟩
  subst huv
  let pt : (σ → Ω) → PrimeSpectrum (MvPolynomial σ Ω) := fun R =>
    ⟨RingHom.ker (MvPolynomial.eval R), RingHom.ker_isPrime _⟩
  have mem_pt : ∀ R h, h ∈ (pt R).asIdeal ↔ MvPolynomial.eval R h = 0 :=
    fun R h => RingHom.mem_ker
  have inS : ∀ R, MvPolynomial.eval R (u * v) = 0 → MvPolynomial.eval R g ≠ 0 →
      pt R ∈ PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g} := by
    intro R h1 h2
    refine ⟨?_, ?_⟩
    · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]; exact (mem_pt R _).2 h1
    · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      exact fun h => h2 ((mem_pt R _).1 h)
  have hcov : PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g} ⊆
      PrimeSpectrum.zeroLocus {u} ∪ PrimeSpectrum.zeroLocus {v} := by
    intro x hx
    have hx1 := hx.1
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hx1
    rcases x.isPrime.mem_or_mem hx1 with h | h
    · left; rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]; exact h
    · right; rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]; exact h
  have key : ∀ R, MvPolynomial.eval R u = 0 → MvPolynomial.eval R v = 0 →
      MvPolynomial.eval R g ≠ 0 → False := by
    intro R hu hv hg
    apply hsmooth R (by simp [hu]) hg
    simp [Derivation.leibniz, hu, hv]
  rcases (isPreirreducible_iff_isClosed_union_isClosed.1 hirr) _ _
      (PrimeSpectrum.isClosed_zeroLocus _) (PrimeSpectrum.isClosed_zeroLocus _) hcov with h | h
  · have hm := h (inS Q (by simp [hQv]) hQg)
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hm
    exact key Q ((mem_pt Q _).1 hm) hQv hQg
  · have hm := h (inS P (by simp [hPu]) hPg)
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hm
    exact key P hPu ((mem_pt P _).1 hm) hPg

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoSplittingFactorisationOfPderivNeZeroStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.no_splitting_factorisation_of_pderiv_ne_zero : ∀ (Ω : Type) [Field Ω] (σ : Type) (f g : MvPolynomial σ Ω) (i : σ) (D : ℕ), (∀ Q : σ → Ω, MvPolynomial.eval Q f = 0 → MvPolynomial.eval Q g ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv i f) ≠ 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) → ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧ ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0) := by
  first | exact @GlobalTheory.hypersurface_part_no_splitting_factorisation | exact GlobalTheory.hypersurface_part_no_splitting_factorisation | (intros; apply GlobalTheory.hypersurface_part_no_splitting_factorisation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypersurfacePartGeometricIrreducibleSpreads

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem hypersurface_part_preirreducible_spreads : ∀ (A : Type) [CommRing A] (σ : Type) [Finite σ] (f g : MvPolynomial σ A) (i : σ), (∀ (k : Type) [Field k] (ψ : A →+* k), MvPolynomial.map ψ f ≠ 0) → (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : σ → k), MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv i (MvPolynomial.map ψ f)) ≠ 0) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map φ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map φ g}) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map ψ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map ψ g}) := by
  intro A _ σ _ f g i h0 hd Ω _ _ φ hirr
  have h3 := GlobalTheory.T.no_splitting_factorisation_of_pderiv_ne_zero Ω σ (MvPolynomial.map φ f) (MvPolynomial.map φ g) i f.totalDegree
    (hd Ω φ) hirr
  obtain ⟨a, I, ha, hI, h⟩ := GlobalTheory.T.splitting_absence_spreads_alt A σ f g f.totalDegree Ω φ h3
  refine ⟨a, I, ha, hI, fun k _ _ ψ hψa hψI => ?_⟩
  refine GlobalTheory.T.hypersurface_diff_isPreirreducible_of_no_splitting k σ (MvPolynomial.map ψ f) (MvPolynomial.map ψ g) f.totalDegree
    (h0 k ψ) ?_ (h k ψ hψa hψI)
  exact Finset.sup_mono (MvPolynomial.support_map_subset ψ f)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypersurfacePartGeometricIrreducibleSpreadsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.hypersurface_part_geometric_irreducible_spreads : ∀ (A : Type) [CommRing A] (σ : Type) [Finite σ] (f g : MvPolynomial σ A) (i : σ), (∀ (k : Type) [Field k] (ψ : A →+* k), MvPolynomial.map ψ f ≠ 0) → (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : σ → k), MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv i (MvPolynomial.map ψ f)) ≠ 0) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map φ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map φ g}) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map ψ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map ψ g}) := by
  first | exact @GlobalTheory.hypersurface_part_preirreducible_spreads | exact GlobalTheory.hypersurface_part_preirreducible_spreads | (intros; apply GlobalTheory.hypersurface_part_preirreducible_spreads <;> assumption)
end
end
