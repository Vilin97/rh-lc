module

public import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinateStatement
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
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AevalSurjectiveOfSpanCotangent
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankOmegaLeFinrankFrobeniusKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinateStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEqZeroOfEvAEqZeroOfLeFinrank

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.BoxMonomials

variable {d : ℕ}

noncomputable def boxPt {q : ℕ} (a : Fin d → Fin q) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))

theorem boxPt_apply {q : ℕ} (a : Fin d → Fin q) (i : Fin d) : boxPt a i = a i := by
  simp [boxPt]

theorem boxPt_injective {q : ℕ} : Function.Injective (boxPt (d := d) (q := q)) := by
  intro a b h
  funext i
  exact Fin.ext (by simpa [boxPt_apply] using DFunLike.congr_fun h i)

theorem exists_boxPt {q : ℕ} (β : Fin d →₀ ℕ) (h : ∀ i, β i < q) :
    ∃ a : Fin d → Fin q, boxPt a = β :=
  ⟨fun i => ⟨β i, h i⟩, by ext i; simp [boxPt_apply]⟩

end GlobalTheory.BoxMonomials


open GlobalTheory.BoxMonomials in
theorem GlobalTheory.coeff_eq_zero_of_evA_eq_zero_of_le_finrank :
    ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (d q : ℕ)
      (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)) (J : Ideal A),
      Function.Surjective (MvPolynomial.aeval (R := K) x) → (∀ i, x i ^ q ∈ J) →
      q ^ d ≤ Module.finrank K (A ⧸ J) → ∀ f : MvPowerSeries (Fin d) K, evA K x hx f = 0 →
      ∀ α : Fin d →₀ ℕ, α.degree < q → coeff α f = 0 := by
  intro K A _ _ _ _ d q x hx J hsurj hJ hdim f hf α hα
  classical
  set E : MvPowerSeries (Fin d) K →ₐ[K] A ⧸ J := (Ideal.Quotient.mkₐ K J).comp (evA K x hx)
    with hE
  have hEapp : ∀ y, E y = Ideal.Quotient.mk J (evA K x hx y) := fun y => rfl
  have hEX : ∀ i, evA K x hx (X i) = x i := fun i => GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate K (Fin d) A x hx i
  have hEXq : ∀ i g, E (X i ^ q * g) = 0 := by
    intro i g
    rw [hEapp, Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, hEX]
    exact J.mul_mem_right _ (hJ i)
  have hmono : ∀ β : Fin d →₀ ℕ, ∀ i, q ≤ β i → ∀ c : K, E (monomial β c) = 0 := by
    intro β i hi c
    have : monomial β c = X i ^ q * monomial (β - Finsupp.single i q) c := by
      rw [X_pow_eq, monomial_mul_monomial, one_mul,
        add_tsub_cancel_of_le (Finsupp.single_le_iff.2 hi)]
    rw [this]
    exact hEXq i _
  set v : (Fin d → Fin q) → A ⧸ J := fun a => E (monomial (boxPt a) 1) with hv
  have hcoe : ∀ P : MvPolynomial (Fin d) K,
      Ideal.Quotient.mk J (MvPolynomial.aeval x P) = E (P : MvPowerSeries (Fin d) K) := by
    intro P
    have : (Ideal.Quotient.mkₐ K J).comp (MvPolynomial.aeval x) =
        E.comp (MvPolynomial.coeToMvPowerSeries.algHom K) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [hEapp, hEX]
    exact DFunLike.congr_fun this P
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    rintro y -
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨P, rfl⟩ := hsurj a'
    rw [hcoe]
    induction P using MvPolynomial.induction_on' with
    | monomial β c =>
      rw [MvPolynomial.coe_monomial]
      by_cases hb : ∀ i, β i < q
      · obtain ⟨a, rfl⟩ := exists_boxPt β hb
        have : monomial (boxPt a) c = c • monomial (boxPt a) (1 : K) := by
          rw [← map_smul, smul_eq_mul, mul_one]
        rw [this, map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
      · push_neg at hb
        obtain ⟨i, hi⟩ := hb
        rw [hmono β i hi c]
        exact Submodule.zero_mem _
    | add P Q hP hQ =>
      rw [MvPolynomial.coe_add, map_add (f := _)]
      exact Submodule.add_mem _ hP hQ
  have hcard : Fintype.card (Fin d → Fin q) = Module.finrank K (A ⧸ J) := by
    apply le_antisymm
    · simpa [Fintype.card_fun] using hdim
    · have h1 := finrank_range_le_card (R := K) v
      have h2 : Set.finrank K (Set.range v) = Module.finrank K (A ⧸ J) := by
        unfold Set.finrank
        rw [eq_top_iff.2 hspan, finrank_top]
      omega
  have hli := linearIndependent_of_top_le_span_of_card_eq_finrank hspan hcard
  set P : MvPowerSeries (Fin d) K :=
    ∑ a : Fin d → Fin q, coeff (boxPt a) f • monomial (boxPt a) (1 : K) with hP
  have hPcoeff : ∀ a : Fin d → Fin q, coeff (boxPt a) P = coeff (boxPt a) f := by
    intro a

    rw [hP, map_sum, Finset.sum_eq_single a]
    · simp [coeff_monomial]
    · intro b _ hb
      simp [coeff_monomial, boxPt_injective.ne (Ne.symm hb)]
    · simp
  set h : MvPowerSeries (Fin d) K := f - P with hh
  let hi : Fin d → MvPowerSeries (Fin d) K := fun i β =>
    if q ≤ β i ∧ ∀ j < i, β j < q then coeff β h else 0
  have hic : ∀ i β, coeff β (hi i) = if q ≤ β i ∧ ∀ j < i, β j < q then coeff β h else 0 :=
    fun i β => by rw [coeff_apply]
  have hdiv : ∀ i, X i ^ q ∣ hi i := by
    intro i
    rw [X_pow_dvd_iff]
    intro m hm
    rw [hic, if_neg]
    omega
  have hsum : h = ∑ i, hi i := by
    ext β

    rw [map_sum]
    simp only [hic]
    by_cases hb : ∀ i, β i < q
    · obtain ⟨a, rfl⟩ := exists_boxPt β hb
      have : coeff (boxPt a) h = 0 := by rw [hh, map_sub, hPcoeff, sub_self]
      rw [this]
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      have := hb i
      omega
    · push_neg at hb
      obtain ⟨i0, hi0mem, hmin⟩ := (Finset.univ.filter (fun i => q ≤ β i)).exists_min_image id
        (by obtain ⟨i, hi⟩ := hb; exact ⟨i, by simp [hi]⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, id] at hi0mem hmin
      rw [Finset.sum_eq_single i0]
      · rw [if_pos]
        refine ⟨hi0mem, fun j hj => ?_⟩
        by_contra hc
        exact absurd (hmin j (by omega)) (not_le.2 hj)
      · intro j _ hj
        rw [if_neg]
        rintro ⟨hjq, hjlt⟩
        rcases lt_or_gt_of_ne hj with hlt | hlt
        · exact absurd (hmin j hjq) (not_le.2 hlt)
        · have := hjlt i0 hlt
          omega
      · simp
  have hEh : E h = 0 := by

    rw [hsum, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    obtain ⟨g, hg⟩ := hdiv i
    rw [hg]
    exact hEXq i g
  have hEf : E f = 0 := by rw [hEapp, hf, map_zero]
  have hfP : f = P + h := by rw [hh]; ring
  have hzero : ∑ a : Fin d → Fin q, coeff (boxPt a) f • v a = 0 := by
    have : E P = ∑ a : Fin d → Fin q, coeff (boxPt a) f • v a := by

      rw [hP, map_sum]
      simp only [map_smul, hv]
    rw [← this, ← hEf, hfP, map_add (f := _), hEh, add_zero]
  have hall := Fintype.linearIndependent_iff.1 hli _ hzero
  obtain ⟨a, rfl⟩ := exists_boxPt α (fun i => lt_of_le_of_lt (Finsupp.le_degree i α) hα)
  exact hall a
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEqZeroOfEvAEqZeroOfLeFinrankStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.coeff_eq_zero_of_evA_eq_zero_of_le_finrank' : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (d q : ℕ) (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)) (J : Ideal A), Function.Surjective (MvPolynomial.aeval (R := K) x) → (∀ i, x i ^ q ∈ J) → q ^ d ≤ Module.finrank K (A ⧸ J) → ∀ f : MvPowerSeries (Fin d) K, evA K x hx f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < q → coeff α f = 0 := by
  first | exact @GlobalTheory.coeff_eq_zero_of_evA_eq_zero_of_le_finrank | exact GlobalTheory.coeff_eq_zero_of_evA_eq_zero_of_le_finrank | (intros; apply GlobalTheory.coeff_eq_zero_of_evA_eq_zero_of_le_finrank <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesGenerateConnectedLevels

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem aeval_surjective_of_dUnit_span {K A : Type} [Field K] [CommRing A] [Bialgebra K A]
    [Module.Finite K A] (hconn : ∀ a ∈ augIdeal K A, IsNilpotent a) {d : ℕ} (x : Fin d → A)
    (hx : ∀ i, Coalgebra.counit (R := K) (x i) = 0)
    (hspan : ∀ c : Cot K A, ∃ l : Fin d → K, c = ∑ i, l i • dUnit (R := K) (x i)) :
    Function.Surjective (MvPolynomial.aeval (R := K) x) := by
  haveI : IsNoetherianRing A := isNoetherian_of_tower K inferInstance
  have hxm : ∀ i, x i ∈ RingHom.ker (counitAlgHom K A) := fun i => by
    rw [RingHom.mem_ker]; exact hx i
  have hnil : IsNilpotent (RingHom.ker (counitAlgHom K A)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro a ha
    exact mem_nilradical.2 (hconn a ha)
  refine GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent (counitAlgHom K A) hnil x hxm ?_
  intro y hy
  obtain ⟨l, hl⟩ := hspan (dUnit (R := K) y)
  refine ⟨l, ?_⟩
  have hmem : y - ∑ i, l i • x i ∈ RingHom.ker (counitAlgHom K A) :=
    sub_mem hy (Ideal.sum_mem _ fun i _ => by
      rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (hxm i))
  have h0 : dUnit (R := K) (y - ∑ i, l i • x i) = 0 := by
    have e : dUnit (R := K) (y - ∑ i, l i • x i) = dUnit (R := K) y - ∑ i, l i • dUnit (R := K) (x i) := by

      simp only [dUnit, map_sub, map_sum, map_smul]
    rw [e, ← hl, sub_self]
  rwa [dUnit, AugCot.d_of_mem _ hmem, Ideal.toCotangent_eq_zero] at h0

theorem exists_coords_generate (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) (hG : G.IsConn) :
    ∃ x : ∀ n, Fin (Module.finrank K G.omega) → G.A n,
      (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n i, Coalgebra.counit (R := K) (x n i) = 0) ∧
        ∀ n, Function.Surjective (MvPolynomial.aeval (R := K) (x n)) := by
  haveI : Module.Finite K (Cot K (G.A 1)) :=
    Module.Finite.of_surjective (AugCot.d (counitAlgHom K (G.A 1))) (AugCot.d_surjective _)
  haveI : Module.Finite K G.omega :=
    Module.Finite.equiv (LinearEquiv.ofBijective _ (G.omegaLevel_one_bijective h)).symm
  set d := Module.finrank K G.omega with hd
  let b := Module.finBasis K G.omega
  have h1 : ∀ i, ∃ a : G.A 1, Coalgebra.counit (R := K) a = 0 ∧ dUnit (R := K) a = (b i).1 1 := by
    intro i
    obtain ⟨a, ha⟩ := AugCot.d_surjective (counitAlgHom K (G.A 1)) ((b i).1 1)
    refine ⟨a - algebraMap K _ (Coalgebra.counit (R := K) a), ?_, ?_⟩
    · have e : Coalgebra.counit (R := K) (algebraMap K (G.A 1) (Coalgebra.counit (R := K) a)) =
          Coalgebra.counit (R := K) a := by
        have := (counitAlgHom K (G.A 1)).commutes (Coalgebra.counit (R := K) a)
        simpa using this
      rw [map_sub, e, sub_self]
    · rw [dUnit, map_sub, AugCot.d_algebraMap, sub_zero]; exact ha
  choose x1 hx1c hx1d using h1
  let z : (n : ℕ) → Fin d → G.A (n + 1) := fun n =>
    Nat.rec (motive := fun n => Fin d → G.A (n + 1)) x1
      (fun n zn i => Function.surjInv (G.res_surjective (n + 1)) (zn i)) n
  let x : ∀ n, Fin d → G.A n := fun n =>
    Nat.rec (motive := fun n => Fin d → G.A n) (fun i => G.res 0 (x1 i)) (fun n _ => z n) n
  have hres : ∀ n i, G.res n (x (n + 1) i) = x n i := by
    intro n i
    cases n with
    | zero => rfl
    | succ n => exact Function.surjInv_eq (G.res_surjective (n + 1)) (z n i)
  have hcou1 : ∀ n i, Coalgebra.counit (R := K) (x (n + 1) i) = 0 := by
    intro n
    induction n with
    | zero => exact hx1c
    | succ n ih =>
      intro i
      rw [← ih i, ← hres (n + 1) i, CoalgHomClass.counit_comp_apply]
  have hcou : ∀ n i, Coalgebra.counit (R := K) (x n i) = 0 := by
    intro n i
    cases n with
    | zero => rw [← hres 0 i, CoalgHomClass.counit_comp_apply]; exact hcou1 0 i
    | succ n => exact hcou1 n i
  have hdu : ∀ n i, dUnit (R := K) (x (n + 1) i) = (b i).1 (n + 1) := by
    intro n
    induction n with
    | zero => exact hx1d
    | succ n ih =>
      intro i
      obtain ⟨u, hu⟩ := G.omegaLevel_surjective (n + 2) (dUnit (R := K) (x (n + 2) i))
      rw [omegaLevel_apply] at hu
      have hn : (u - b i).1 (n + 1) = 0 := by
        change u.1 (n + 1) - (b i).1 (n + 1) = 0
        rw [← ih i, ← cotMap_res_omega, hu, cotMap_d, hres, sub_self]
      have h1' : G.omegaLevel 1 (u - b i) = 0 :=
        G.omega_val_eq_zero_of_le (by omega) hn
      have hub : u = b i := sub_eq_zero.1
        ((G.omegaLevel_one_bijective h).1 (h1'.trans (map_zero _).symm))
      rw [← hu, hub]
  have hspan : ∀ n (c : Cot K (G.A n)), ∃ l : Fin d → K, c = ∑ i, l i • dUnit (R := K) (x n i) := by
    intro n c
    cases n with
    | zero => exact ⟨0, by rw [G.cot_zero_eq_zero c]; simp⟩
    | succ n =>
      obtain ⟨w, rfl⟩ := G.omegaLevel_surjective (n + 1) c
      refine ⟨b.repr w, ?_⟩
      conv_lhs => rw [← b.sum_repr w]

      simp only [map_sum, map_smul, omegaLevel_apply, hdu]
      rfl
  exact ⟨x, hres, hcou, fun n =>
    aeval_surjective_of_dUnit_span (hG n) (x n) (hcou n) (hspan n)⟩

end GlobalTheory.PDivGroup
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesGenerateConnectedLevelsStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.exists_coordinates_generate_connected_levels : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), G.IsConn → ∃ x : ∀ n, Fin (Module.finrank K G.omega) → G.A n, (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n i, Coalgebra.counit (R := K) (x n i) = 0) ∧ ∀ n, Function.Surjective (MvPolynomial.aeval (R := K) (x n)) := by
  first | exact @GlobalTheory.PDivGroup.exists_coords_generate | exact GlobalTheory.PDivGroup.exists_coords_generate | (intros; apply GlobalTheory.PDivGroup.exists_coords_generate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectedPDivGroupChartOfIsConn

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem evA_comp_coe {K A : Type} [Field K] [CommRing A] [Algebra K A] {d : ℕ}
    (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)) :
    (evA K x hx).comp (MvPolynomial.coeToMvPowerSeries.algHom K) = MvPolynomial.aeval x := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply, MvPolynomial.aeval_X]
  simp only [MvPolynomial.coe_X, map_X]
  exact GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate K (Fin d) A x hx i

theorem exists_chart_of_isConn (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) (hG : G.IsConn) : ∃ d, Nonempty (Chart G d) := by
  obtain ⟨x, hres, haug, hsurj⟩ := GlobalTheory.T.exists_coordinates_generate_connected_levels p K h G hG
  have hmem : ∀ n i, x n i ∈ augIdeal K (G.A n) := fun n i => by
    simp [augIdeal, haug n i]
  have hnil : ∀ n i, IsNilpotent (x n i) := fun n i => hG n _ (hmem n i)
  refine ⟨_, ⟨{ x := x, nil := hnil, res := hres, aug := haug, presents := ⟨?_, ?_⟩ }⟩⟩
  · intro n a
    obtain ⟨P, hP⟩ := hsurj n a
    refine ⟨(P : MvPowerSeries _ K), ?_⟩
    have := congrArg (fun φ => φ P) (evA_comp_coe (x n) (hnil n))
    simp only [AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply] at this
    rw [← hP, ← this]
    rfl
  · intro N
    refine ⟨N, fun f hf α hα => ?_⟩
    have hq : ∀ i, x N i ^ (p ^ N) ∈ frobKerIdeal (p ^ N) K (G.A N) :=
      fun i => pow_mem_frobKerIdeal (hmem N i)
    exact GlobalTheory.T.coeff_eq_zero_of_evA_eq_zero_of_le_finrank' K (G.A N) _ (p ^ N) (x N) (hnil N) _ (hsurj N) hq
      (GlobalTheory.T.pow_finrank_omega_le_finrank_frobeniusKernel p K h G N) f hf α
      (lt_of_lt_of_le hα (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le)

end GlobalTheory.Katz
end
end
