module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DigitMonomialsBasisEnvelopeModPowStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureAdicCompletionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsAdicCompletionMapOfFgStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRingHomExtendIsAdicCompletionMapStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeltaRingHomOfDenseDeltaCommuteLocusStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticEnvelopeRelationTriangularStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicTopologicalBasisOfLevelBases

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.LevelBasis

variable {A L Q : Type} [CommRing A] [CommRing L] [CommRing Q] (s : A →+* L) (i : L →+* Q) (J : Ideal A)
  {ι : Type} (m : ι → L)

def lsum (c : ι →₀ A) : L := c.sum fun k a => s a * m k

theorem lsum_add (c c' : ι →₀ A) : lsum s m (c + c') = lsum s m c + lsum s m c' :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [map_add (f := _), add_mul])

theorem lsum_sub (c c' : ι →₀ A) : lsum s m (c - c') = lsum s m c - lsum s m c' :=
  Finsupp.sum_sub_index (fun _ _ _ => by rw [map_sub, sub_mul])

theorem lsum_smul (a : A) (c : ι →₀ A) : lsum s m (a • c) = s a * lsum s m c := by
  unfold lsum
  rw [Finsupp.sum_smul_index (fun _ => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [map_mul, mul_assoc]

theorem lsum_single (k : ι) : lsum s m (Finsupp.single k 1) = m k := by
  unfold lsum; rw [Finsupp.sum_single_index (by simp), map_one, one_mul]

def IsApprox (n : ℕ) (x : Q) (c : ι →₀ A) : Prop := x - i (lsum s m c) ∈ (J ^ n).map (i.comp s)

theorem map_pow_eq (n : ℕ) : (J ^ n).map (i.comp s) = ((J.map s) ^ n).map i := by
  rw [← Ideal.map_map, Ideal.map_pow]

variable {s i J m}

theorem IsApprox.mono {n n' : ℕ} {x : Q} {c : ι →₀ A} (h : n' ≤ n) (hc : IsApprox s i J m n x c) :
    IsApprox s i J m n' x c :=
  Ideal.map_mono (Ideal.pow_le_pow_right h) hc

theorem exists_approx (hc : IsCompl i (J.map s))
    (H1 : ∀ (n : ℕ) (x : L), ∃ c : ι →₀ A, x - c.sum (fun k a => s a * m k) ∈ (J ^ n).map s)
    (n : ℕ) (x : Q) : ∃ c, IsApprox s i J m n x c := by
  obtain ⟨a, ha⟩ := hc.surj x n
  obtain ⟨c, hc'⟩ := H1 n a
  refine ⟨c, ?_⟩
  unfold IsApprox
  have e : x - i (lsum s m c) = (x - i a) + i (a - lsum s m c) := by rw [map_sub]; ring
  rw [e, map_pow_eq]
  refine add_mem ha (Ideal.mem_map_of_mem i ?_)
  rw [← Ideal.map_pow]; exact hc'

theorem approx_unique (hc : IsCompl i (J.map s))
    (H2 : ∀ (n : ℕ) (c : ι →₀ A), c.sum (fun k a => s a * m k) ∈ (J ^ n).map s → ∀ k, c k ∈ J ^ n)
    {n : ℕ} {x : Q} {c c' : ι →₀ A} (h : IsApprox s i J m n x c) (h' : IsApprox s i J m n x c') (k : ι) :
    c k - c' k ∈ J ^ n := by
  have h3 := sub_mem h' h
  have e : x - i (lsum s m c') - (x - i (lsum s m c)) = i (lsum s m (c - c')) := by
    rw [lsum_sub, map_sub]; ring
  rw [e, map_pow_eq] at h3
  have h4 := hc.ker _ n h3
  rw [← Ideal.map_pow] at h4
  simpa using H2 n (c - c') h4 k

end GlobalTheory.BSP.LevelBasis


open GlobalTheory.BSP.LevelBasis in
theorem GlobalTheory.BSP.exists_topBasis_of_levels (A : Type) [CommRing A] (L : Type) [CommRing L] (Q : Type) [CommRing Q]
    (s : A →+* L) (i : L →+* Q) (J : Ideal A) (ι : Type) (m : ι → L) (k₀ : ι) (h1 : m k₀ = 1)
    (hA : IsAdicComplete J A) (hc : IsCompl i (J.map s))
    (H1 : ∀ (n : ℕ) (x : L), ∃ c : ι →₀ A, x - c.sum (fun k a => s a * m k) ∈ (J ^ n).map s)
    (H2 : ∀ (n : ℕ) (c : ι →₀ A), c.sum (fun k a => s a * m k) ∈ (J ^ n).map s → ∀ k, c k ∈ J ^ n) :
    ∃ tb : TopBasis (i.comp s) J ι, ∀ k, tb.b k = i (m k) := by
  have mt : ∀ n : ℕ, (J ^ n • ⊤ : Submodule A A) = J ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  have exA := exists_approx (m := m) hc H1
  have lim : ∀ (x : Q) (k : ι), ∃ a : A, ∀ n c, IsApprox s i J m n x c → c k - a ∈ J ^ n := by
    intro x k
    choose f hf using exA
    obtain ⟨a, ha⟩ := hA.toIsPrecomplete.prec (f := fun n => f n x k) (fun {p q} hpq => by
      rw [SModEq.sub_mem, mt]
      exact approx_unique hc H2 (hf p x) ((hf q x).mono hpq) k)
    refine ⟨a, fun n c hcn => ?_⟩
    have h2 := ha n
    rw [SModEq.sub_mem, mt] at h2
    have := add_mem (approx_unique hc H2 hcn (hf n x) k) h2
    simpa using this
  choose C hC using lim
  have uniq : ∀ x k a, (∀ n, ∃ c, IsApprox s i J m n x c ∧ c k - a ∈ J ^ n) → C x k = a := by
    intro x k a h
    refine sub_eq_zero.1 (hA.toIsHausdorff.haus _ fun n => ?_)
    rw [SModEq.sub_mem, mt, sub_zero]
    obtain ⟨c, hc1, hc2⟩ := h n
    have := sub_mem hc2 (hC x k n c hc1)
    convert this using 1; ring
  have single_approx : ∀ n k, IsApprox s i J m n (i (m k)) (Finsupp.single k 1) := by
    intro n k; unfold IsApprox; rw [lsum_single, sub_self]; exact zero_mem _
  refine ⟨{
    b := fun k => i (m k)
    c := fun k => AddMonoidHom.mk' (fun x => C x k) (fun x y => uniq (x + y) k _ fun n => by
      obtain ⟨c, hc⟩ := exA n x
      obtain ⟨c', hc'⟩ := exA n y
      refine ⟨c + c', ?_, ?_⟩
      · unfold IsApprox at hc hc' ⊢
        have e : x + y - i (lsum s m (c + c')) = (x - i (lsum s m c)) + (y - i (lsum s m c')) := by
          rw [lsum_add, map_add (f := _)]; ring
        rw [e]; exact add_mem hc hc'
      · have := add_mem (hC x k n c hc) (hC y k n c' hc')
        convert this using 1; simp only [Finsupp.add_apply]; ring)
    c_mul := fun k a x => by
      simp only [AddMonoidHom.mk'_apply]
      refine uniq _ k _ fun n => ?_
      obtain ⟨c, hc⟩ := exA n x
      refine ⟨a • c, ?_, ?_⟩
      · unfold IsApprox at hc ⊢
        have e : (i.comp s) a * x - i (lsum s m (a • c)) = (i.comp s) a * (x - i (lsum s m c)) := by
          rw [lsum_smul, map_mul, RingHom.comp_apply]; ring
        rw [e]; exact Ideal.mul_mem_left _ _ hc
      · have e : (a • c) k - a * C x k = a * (c k - C x k) := by
          rw [Finsupp.smul_apply, smul_eq_mul]; ring
        rw [e]; exact Ideal.mul_mem_left _ _ (hC x k n c hc)
    c_self := fun k => by
      simp only [AddMonoidHom.mk'_apply]
      exact uniq _ k _ fun n => ⟨_, single_approx n k, by simp⟩
    c_ne := fun j k hjk => by
      simp only [AddMonoidHom.mk'_apply]
      exact uniq _ j _ fun n => ⟨_, single_approx n k, by simp [Finsupp.single_apply, Ne.symm hjk]⟩
    fin := fun x n => by
      obtain ⟨c, hc⟩ := exA n x
      refine c.support.finite_toSet.subset fun k hk => ?_
      simp only [Set.mem_setOf_eq, AddMonoidHom.mk'_apply] at hk
      by_contra h
      simp only [Finset.mem_coe, Finsupp.mem_support_iff, not_not] at h
      have := hC x k n c hc
      rw [h, zero_sub, neg_mem_iff] at this
      exact hk this
    approx := fun x n F hF => by
      classical
      simp only [AddMonoidHom.mk'_apply] at hF ⊢
      obtain ⟨c, hc⟩ := exA n x
      have e1 : i (lsum s m c) = ∑ k ∈ F ∪ c.support, (i.comp s) (c k) * i (m k) := by
        unfold lsum

        rw [Finsupp.sum_of_support_subset c (Finset.subset_union_right (s₁ := F)) _ (fun _ _ => by simp), map_sum]
        simp [RingHom.comp_apply, map_mul]
      have e2 : ∑ k ∈ F, (i.comp s) (C x k) * i (m k) =
          ∑ k ∈ F ∪ c.support, (i.comp s) (if k ∈ F then C x k else 0) * i (m k) := by
        rw [← Finset.sum_subset Finset.subset_union_left (fun k _ hk => by rw [if_neg hk, map_zero, zero_mul])]
        exact Finset.sum_congr rfl fun k hk => by rw [if_pos hk]
      have e3 : x - ∑ k ∈ F, (i.comp s) (C x k) * i (m k) = (x - i (lsum s m c)) +
          ∑ k ∈ F ∪ c.support, (i.comp s) (c k - if k ∈ F then C x k else 0) * i (m k) := by
        rw [e2, e1]; simp only [map_sub, sub_mul, Finset.sum_sub_distrib]; ring
      rw [e3]
      refine add_mem hc (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_))
      by_cases hk : k ∈ F
      · rw [if_pos hk]; exact hC x k n c hc
      · rw [if_neg hk, sub_zero]
        have := add_mem (hC x k n c hc) (hF k hk)
        simpa using this
    complete := by rw [← Ideal.map_map]; exact hc.complete
    i₀ := k₀
    b_i₀ := by simp only [h1, map_one] }, fun k => rfl⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicTopologicalBasisOfLevelBasesStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_adicTopologicalBasis_of_level_bases : ∀ (A : Type) [CommRing A] (L : Type) [CommRing L] (Q : Type) [CommRing Q] (s : A →+* L) (i : L →+* Q) (J : Ideal A) (ι : Type) (m : ι → L) (k₀ : ι), m k₀ = 1 → IsAdicComplete J A → IsCompl i (J.map s) → (∀ (n : ℕ) (x : L), ∃ c : ι →₀ A, x - c.sum (fun k a => s a * m k) ∈ (J ^ n).map s) → (∀ (n : ℕ) (c : ι →₀ A), c.sum (fun k a => s a * m k) ∈ (J ^ n).map s → ∀ k, c k ∈ J ^ n) → ∃ tb : TopBasis (i.comp s) J ι, ∀ k, tb.b k = i (m k) := by
  first | exact @GlobalTheory.BSP.exists_topBasis_of_levels | exact GlobalTheory.BSP.exists_topBasis_of_levels | (intros; apply GlobalTheory.BSP.exists_topBasis_of_levels <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureQuotientSpan

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem GlobalTheory.BSP.delta_quot_span : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (s : Set A), (∀ x ∈ s, D.δ x ∈ Ideal.span s) → ∃ D' : Delta l (A ⧸ Ideal.span s), IsδMap D D' (Ideal.Quotient.mk (Ideal.span s)) := by
  intro l _ A _ D s hs
  let N := Ideal.span s
  let g : A →+* W2 l (A ⧸ N) := (W2.map (Ideal.Quotient.mk N)).comp (deltaSectionToWittLengthTwo D)
  have hg : ∀ a ∈ N, g a = 0 := by
    intro a ha
    have hle : N ≤ RingHom.ker g := by
      refine Ideal.span_le.2 fun x hx => ?_
      rw [SetLike.mem_coe, RingHom.mem_ker]
      refine W2.ext ?_ ?_
      · exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hx)
      · exact Ideal.Quotient.eq_zero_iff_mem.2 (hs x hx)
    exact hle ha
  let sec : A ⧸ N →+* W2 l (A ⧸ N) := Ideal.Quotient.lift N g hg
  have hsec : ∀ a, (sec a).fst = a := by
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl
  exact ⟨deltaStructureOfWittLengthTwoSection sec hsec, fun a => rfl⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureQuotientSpanStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_deltaRingStructure_quotient_span : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (s : Set A), (∀ x ∈ s, D.δ x ∈ Ideal.span s) → ∃ D' : Delta l (A ⧸ Ideal.span s), IsδMap D D' (Ideal.Quotient.mk (Ideal.span s)) := by
  first | exact @GlobalTheory.BSP.delta_quot_span | exact GlobalTheory.BSP.delta_quot_span | (intros; apply GlobalTheory.BSP.delta_quot_span <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EnvRingExists

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.EnvExist

variable {l : ℕ}

theorem iter_map {A B : Type} [CommRing A] [CommRing B] {D : Delta l A} {D' : Delta l B} {g : A →+* B}
    (hg : IsδMap D D' g) (n : ℕ) (x : A) : g (D.δ^[n] x) = D'.δ^[n] (g x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hg, ih]

theorem polyEval_isδ [Fact l.Prime] {A C : Type} [CommRing A] [CommRing C] (D : Delta l A) (DC : Delta l C)
    (f : A →+* C) (hf : IsδMap D DC f) (v : C) :
    IsδMap (polyDelta D) DC (MvPolynomial.eval₂Hom f fun k => DC.δ^[k] v) := by
  intro x
  have : x ∈ δLocus (polyDelta D) DC (MvPolynomial.eval₂Hom f fun k => DC.δ^[k] v) := by
    refine MvPolynomial.induction_on x ?_ ?_ ?_
    · intro a
      rw [mem_δLocus, polyDelta_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      exact hf a
    · intro p q hp hq
      exact add_mem hp hq
    · intro p k hp
      refine mul_mem hp ?_
      rw [mem_δLocus, polyDelta_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
        Function.iterate_succ_apply']
  exact mem_δLocus.1 this

end GlobalTheory.BSP.EnvExist


open GlobalTheory.BSP.EnvExist in
theorem GlobalTheory.BSP.envRing_exists : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A)
    (d p : A), J.FG → (l : A) ∈ J → d ∈ J → IsUnit (D.δ d) → IsAdicComplete J A →
    Nonempty (EnvRing D J d p) := by
  intro l _ A _ D J d p hfg hl hd hδ hc
  have hstab : ∀ x ∈ Set.range (envRel D d p), (polyDelta D).δ x ∈ Ideal.span (Set.range (envRel D d p)) := by
    rintro _ ⟨k, rfl⟩
    refine Ideal.subset_span ⟨k + 1, ?_⟩
    unfold envRel
    exact Function.iterate_succ_apply' _ _ _
  obtain ⟨DL, hDL⟩ := GlobalTheory.T.exists_deltaRingStructure_quotient_span l (MvPolynomial ℕ A) (polyDelta D) _ hstab
  set mk := Ideal.Quotient.mk (Ideal.span (Set.range (envRel D d p))) with hmk
  set s : A →+* MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p)) := mk.comp MvPolynomial.C with hs
  obtain ⟨Q, _, iQ, hQ⟩ := GlobalTheory.T.exists_isAdicCompletionMap_of_fg _ (J.map s) (hfg.map s)
  have hlL : ((l : ℕ) : MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p))) ∈ J.map s := by
    rw [← map_natCast s]; exact Ideal.mem_map_of_mem s hl
  obtain ⟨DQ, hDQ⟩ := GlobalTheory.T.exists_deltaRingStructure_adicCompletion l _ Q iQ (J.map s) hQ hlL DL
  have hX : ∀ k, iQ (mk (MvPolynomial.X k)) = DQ.δ^[k] (iQ (mk (MvPolynomial.X 0))) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [← polyDelta_X D k, hDL, hDQ, ih, Function.iterate_succ_apply']

  have hshape := GlobalTheory.T.prismaticEnvelopeRelation_triangular l A D J d p hl hd hδ
  have hlev := GlobalTheory.T.digitMonomials_basis_envelope_mod_pow l A J (envRel D d p) hshape
  have hmono : ∀ (α : ℕ →₀ ℕ) (a : A), mk (MvPolynomial.monomial α a) = s a * mk (MvPolynomial.monomial α 1) := by
    intro α a
    rw [hs, RingHom.comp_apply, ← map_mul, MvPolynomial.C_mul_monomial, mul_one]
  have hsum : ∀ c : Digits l →₀ A, mk (c.sum fun α a => MvPolynomial.monomial α.1 a) =
      c.sum fun α a => s a * mk (MvPolynomial.monomial α.1 1) := fun c => by
    rw [map_finsuppSum]; exact Finsupp.sum_congr fun α _ => hmono α.1 (c α)
  have hmapmem : ∀ (n : ℕ) (y : MvPolynomial ℕ A), y ∈ Ideal.span (Set.range (envRel D d p)) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) →
      mk y ∈ (J ^ n).map s := by
    intro n y hy
    have h := Ideal.mem_map_of_mem mk hy
    rwa [Ideal.map_sup, hmk, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_map] at h
  have hcomap : ∀ (n : ℕ) (y : MvPolynomial ℕ A), mk y ∈ (J ^ n).map s →
      y ∈ Ideal.span (Set.range (envRel D d p)) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
    intro n y hy
    rw [hs, ← Ideal.map_map] at hy
    have h := Ideal.mem_comap.2 hy
    rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm] at h
  obtain ⟨tb, htb⟩ := GlobalTheory.T.exists_adicTopologicalBasis_of_level_bases A (MvPolynomial ℕ A ⧸ Ideal.span (Set.range (envRel D d p))) Q s iQ J (Digits l)
    (fun α => mk (MvPolynomial.monomial α.1 1)) ⟨0, fun _ => by simpa using (Fact.out : l.Prime).pos⟩
    (by simp) hc hQ
    (fun n x => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨c, hc'⟩ := (hlev n).1 y
      refine ⟨c, ?_⟩
      have h := hmapmem n _ hc'
      rwa [map_sub, hsum] at h)
    (fun n c hcs => (hlev n).2 c (hcomap n _ (by rw [hsum]; exact hcs)))
  have hiδ : IsδMap D DQ (iQ.comp s) := by
    intro a
    show iQ (mk (MvPolynomial.C (D.δ a))) = DQ.δ (iQ (mk (MvPolynomial.C a)))
    rw [← polyDelta_C, hDL, hDQ]
  set_option synthInstance.maxHeartbeats 200000 in
  have hrel : DQ.δ ((iQ.comp s) p + (iQ.comp s) d * iQ (mk (MvPolynomial.X 0))) = 0 := by
    show DQ.δ (iQ (mk (MvPolynomial.C p)) + iQ (mk (MvPolynomial.C d)) * iQ (mk (MvPolynomial.X 0))) = 0
    have h0 : mk (envRel D d p 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨0, rfl⟩)
    rw [← map_mul iQ, ← map_mul mk, ← map_add iQ, ← map_add mk, ← hDQ, ← hDL]
    change iQ (mk (envRel D d p 0)) = 0
    rw [h0, map_zero]
  have htbb : ∀ α, tb.b α = α.1.prod fun k n => (DQ.δ^[k] (iQ (mk (MvPolynomial.X 0)))) ^ n := by
    intro α
    rw [htb α]
    show (iQ.comp mk) (MvPolynomial.monomial α.1 1) = _
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, map_finsuppProd]
    refine Finsupp.prod_congr fun k _ => ?_
    rw [map_pow, RingHom.comp_apply, hX]
  have hlift : ∀ (C : Type) [CommRing C] (DC : Delta l C) (JC : Ideal C), IsAdicComplete JC C → ∀ f : A →+* C,
      IsδMap D DC f → J.map f ≤ JC → ∀ v : C, DC.δ (f p + f d * v) = 0 →
      ∃ h : Q →+* C, IsδMap DQ DC h ∧ h.comp (iQ.comp s) = f ∧ h (iQ (mk (MvPolynomial.X 0))) = v := by
    intro C _ DC JC hC f hf hJ v hv
    have hg₀ := polyEval_isδ D DC f hf v
    set g₀ := MvPolynomial.eval₂Hom f fun k => DC.δ^[k] v with hg₀def
    have hle : Ideal.span (Set.range (envRel D d p)) ≤ RingHom.ker g₀ := by
      rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      have hz : g₀ (MvPolynomial.C p + MvPolynomial.C d * MvPolynomial.X 0) = f p + f d * v := by
        simp [g₀]
      show g₀ (envRel D d p k) = 0
      rw [envRel, iter_map hg₀, Function.iterate_succ_apply, hz, hv]
      exact Function.iterate_fixed DC.δ_zero k
    set g₁ := Ideal.Quotient.lift (Ideal.span (Set.range (envRel D d p))) g₀ (fun a ha => hle ha) with hg₁def
    have hg₁C : g₁.comp s = f := RingHom.ext fun a => by
      show g₀ (MvPolynomial.C a) = f a
      exact MvPolynomial.eval₂Hom_C _ _ _
    obtain ⟨h, hh⟩ := GlobalTheory.T.exists_ringHom_extend_isAdicCompletionMap _ Q C iQ (J.map s) JC hQ hC g₁ (by rw [Ideal.map_map, hg₁C]; exact hJ)
    have e : ∀ z, h (iQ z) = g₁ z := fun z => RingHom.congr_fun hh z
    have hlQ : ((l : ℕ) : Q) ∈ (J.map s).map iQ := by
      rw [← map_natCast iQ]; exact Ideal.mem_map_of_mem iQ hlL
    have hJQ : ((J.map s).map iQ).map h ≤ JC := by
      rw [Ideal.map_map, hh, Ideal.map_map, hg₁C]; exact hJ
    have hhδ : IsδMap DQ DC h := GlobalTheory.T.isDeltaRingHom_of_dense_deltaCommuteLocus l Q C DQ DC ((J.map s).map iQ) JC h hlQ hJQ inferInstance
      (fun x n => by
        obtain ⟨b, hb⟩ := hQ.surj x n
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
        refine ⟨iQ (mk y), ?_, ?_⟩
        · rw [mem_δLocus, ← hDQ, ← hDL, e, e]
          exact hg₀ y
        · rw [← Ideal.map_pow]; exact hb)
    refine ⟨h, hhδ, ?_, ?_⟩
    · rw [← RingHom.comp_assoc, hh, hg₁C]
    · show h (iQ (mk (MvPolynomial.X 0))) = v
      rw [e]
      show g₀ (MvPolynomial.X 0) = v
      rw [hg₀def, MvPolynomial.eval₂Hom_X']
      rfl
  exact ⟨{ Q := Q, DQ := DQ, i := iQ.comp s, i_δ := hiδ, w := iQ (mk (MvPolynomial.X 0)), rel := hrel, tb := tb, tb_b := htbb, lift := hlift }⟩
end
end
end
