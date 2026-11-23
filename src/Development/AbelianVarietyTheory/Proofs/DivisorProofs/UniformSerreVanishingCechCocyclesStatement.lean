module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.ReesAlgebra
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGradedModuleExactAtOfLargeDegree
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousIdealOverReesAlgebraStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfFractionCocycleHomogeneousIdea

section

@[expose] public section

open MvPolynomial DirectSum

namespace GlobalTheory

theorem cocycle_all_pairs_of_lt {Q : Type*} [CommRing Q] {ι : Type*} [LinearOrder ι]
    (x : ι → Q) (f : ι → ι → Q) (g : ι → Q) (N N' : ℕ)
    (hcoc : ∀ i j l, ∃ L : ℕ, (x i * x j * x l) ^ L * (x l ^ N * f i j + x i ^ N * f j l - x j ^ N * f i l) = 0)
    (hlt : ∀ i j, i < j → ∃ L : ℕ, (x i * x j) ^ L *
      ((x i * x j) ^ N' * f i j - (x i * x j) ^ N * (x j ^ N' * g i - x i ^ N' * g j)) = 0)
    (i j : ι) : ∃ L : ℕ, (x i * x j) ^ L *
      ((x i * x j) ^ N' * f i j - (x i * x j) ^ N * (x j ^ N' * g i - x i ^ N' * g j)) = 0 := by
  obtain ⟨L₃, h₃⟩ := hcoc i i i
  have h₃' : x i ^ (3 * L₃ + N) * f i i = 0 := by linear_combination h₃
  rcases lt_trichotomy i j with h | rfl | h
  · exact hlt i j h
  · exact ⟨3 * L₃ + N, by linear_combination (x i ^ (3 * L₃ + N + 2 * N')) * h₃'⟩
  · obtain ⟨L₁, h₁⟩ := hlt j i h
    obtain ⟨L₂, h₂⟩ := hcoc i j i
    have hs : x i ^ (2 * L₂ + 3 * L₃ + 2 * N) * x j ^ L₂ * (f i j + f j i) = 0 := by
      linear_combination (x i ^ (3 * L₃ + N)) * h₂ + ((x i ^ 2 * x j) ^ L₂ * x j ^ N) * h₃'
    refine ⟨3 * L₂ + 3 * L₃ + 2 * N + L₁, ?_⟩
    linear_combination (x i ^ L₂ * x j ^ (2 * L₂ + 3 * L₃ + 2 * N) * (x i * x j) ^ L₁ *
      (x i * x j) ^ N') * hs - (x i * x j) ^ (3 * L₂ + 3 * L₃ + 2 * N) * h₁

theorem exists_triple_of_card_eq_three {ι : Type*} [LinearOrder ι] {t : Finset ι}
    (ht : t.card = 3) : ∃ i j l, i < j ∧ j < l ∧ t = {i, j, l} := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 ht
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases lt_or_gt_of_ne hbc with h3 | h3
  all_goals first
    | exact ⟨a, b, c, by assumption, by assumption, rfl⟩
    | exact ⟨a, b, c, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨a, c, b, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨b, a, c, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨b, c, a, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨c, a, b, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨c, b, a, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | (exfalso; order)

theorem Cube.d_two_apply_triple {ι : Type} [LinearOrder ι] {R : Type*} [Ring R]
    (A : Cube ι R) (x : Cube.Term A 2) {i j l : ι} (hij : i < j) (hjl : j < l) :
    Cube.d A 2 x ⟨{i, j, l}, by rw [Finset.card_eq_three]; exact ⟨i, j, l, hij.ne, (hij.trans hjl).ne, hjl.ne, rfl⟩⟩ =
      Cube.res A (by intro k; simp; tauto) (x ⟨{j, l}, Finset.card_pair hjl.ne⟩) -
        Cube.res A (by intro k; simp; tauto) (x ⟨{i, l}, Finset.card_pair (hij.trans hjl).ne⟩) +
        Cube.res A (by intro k; simp; tauto) (x ⟨{i, j}, Finset.card_pair hij.ne⟩) := by
  have hil := hij.trans hjl
  rw [Cube.d_apply_extend, Finset.sum_insert (by simp [hij.ne, hil.ne]), Finset.sum_pair hjl.ne,
    ← Cube.extend_apply_of_eq A x (Finset.card_pair hjl.ne),
    ← Cube.extend_apply_of_eq A x (Finset.card_pair hil.ne),
    ← Cube.extend_apply_of_eq A x (Finset.card_pair hij.ne)]
  have e1 : ({i, j, l} : Finset ι).erase i = {j, l} := by
    ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, h | h | h⟩ <;> first | exact absurd h hk | simp [h]
    · rintro (rfl | rfl) <;> simp [hij.ne', hil.ne']
  have e2 : ({i, j, l} : Finset ι).erase j = {i, l} := by
    ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, h | h | h⟩ <;> first | exact absurd h hk | simp [h]
    · rintro (rfl | rfl) <;> simp [hij.ne, hjl.ne']
  have e3 : ({i, j, l} : Finset ι).erase l = {i, j} := by
    ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, h | h | h⟩ <;> first | exact absurd h hk | simp [h]
    · rintro (rfl | rfl) <;> simp [hil.ne, hjl.ne]
  have s1 : cubeSign ({i, j, l} : Finset ι) i = 1 :=
    cubeSign_eq_one_of_forall_le (by simp [hij.le, hil.le])
  have s2 : cubeSign ({i, j, l} : Finset ι) j = -1 := by
    have := cubeSign_erase_of_lt (t := {i, j, l}) (by simp) hij
    rw [e1, cubeSign_eq_one_of_forall_le (by simp [hjl.le])] at this
    omega
  have s3 : cubeSign ({i, j, l} : Finset ι) l = 1 := by
    have a1 := cubeSign_erase_of_lt (t := {i, j, l}) (by simp) hil
    rw [e1] at a1
    have a2 := cubeSign_erase_of_lt (t := {j, l}) (by simp) hjl
    rw [Finset.erase_insert (by simp [hjl.ne]), cubeSign_singleton] at a2
    omega
  rw [Cube.res_congr A _ e1 _ (by intro k; simp; tauto), Cube.res_congr A _ e2 _ (by intro k; simp; tauto),
    Cube.res_congr A _ e3 _ (by intro k; simp; tauto), s1, s2, s3]
  simp only [one_smul, neg_smul]
  abel

section GrCubeVal
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] {n : ℤ}

abbrev grCubeVal {s : Finset ι} (z : (grCube ι ℳ n).obj s) :
    LocalizedModule.Away (xProd R s) M :=
  Subtype.val (p := fun w => w ∈ homLoc ℳ s n) z

theorem grCubeVal_add {s : Finset ι} (a b : (grCube ι ℳ n).obj s) :
    grCubeVal (a + b) = grCubeVal a + grCubeVal b := rfl

theorem grCubeVal_sub {s : Finset ι} (a b : (grCube ι ℳ n).obj s) :
    grCubeVal (a - b) = grCubeVal a - grCubeVal b := rfl

theorem grCubeVal_zero {s : Finset ι} : grCubeVal (0 : (grCube ι ℳ n).obj s) = 0 := rfl

theorem grCubeVal_injective {s : Finset ι} :
    Function.Injective (grCubeVal : (grCube ι ℳ n).obj s → _) := fun _ _ h => Subtype.ext h

theorem grCubeVal_res {s t : Finset ι} (h : s ⊆ t) (z : (grCube ι ℳ n).obj s) :
    grCubeVal (Cube.res (grCube ι ℳ n) h z) = locRes X M h (grCubeVal z) := rfl

end GrCubeVal

theorem exists_coboundary_lt {ι : Type} [LinearOrder ι] [Fintype ι] {A : Type} [CommRing A]
    (J : Ideal (MvPolynomial ι A)) (d : ℕ)
    (hex : Function.Exact (Cube.d (grCube ι (grQuot (polyGrading ι A) J) (d : ℤ)) 1)
      (Cube.d (grCube ι (grQuot (polyGrading ι A) J) (d : ℤ)) 2))
    (N : ℕ) (F : ι → ι → MvPolynomial ι A) (hF : ∀ i j, (F i j).IsHomogeneous (d + 2 * N))
    (hcoc : ∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial ι A) * X j * X l) ^ L *
      (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J) :
    ∃ (N' : ℕ) (G : ι → MvPolynomial ι A), (∀ i, (G i).IsHomogeneous (d + N')) ∧
      ∀ i j, i < j → ∃ L : ℕ, ((X i : MvPolynomial ι A) * X j) ^ L *
        ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J := by
  classical
  have hne : ∀ s : {s : Finset ι // s.card = 2}, s.1.Nonempty := fun s =>
    Finset.card_pos.1 (by rw [s.2]; norm_num)
  let x : Cube.Term (grCube ι (grQuot (polyGrading ι A) J) (d : ℤ)) 2 := fun s =>
    ⟨awayFrac _ (xProd A s.1) N
        (Submodule.Quotient.mk (p := J) (F (s.1.min' (hne s)) (s.1.max' (hne s)))),
      awayFrac_mem_homLoc ⟨_, mem_polyGrading_natCast.2 (hF _ _), rfl⟩
        (by rw [s.2]; push_cast; ring)⟩
  have hmin : ∀ i j, i < j → ∀ hn : ({i, j} : Finset ι).Nonempty, ({i, j} : Finset ι).min' hn = i :=
    fun i j h hn => le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ (by simp [h.le]))
  have hmax : ∀ i j, i < j → ∀ hn : ({i, j} : Finset ι).Nonempty, ({i, j} : Finset ι).max' hn = j :=
    fun i j h hn => le_antisymm (Finset.max'_le _ _ _ (by simp [h.le])) (Finset.le_max' _ _ (by simp))
  have hx : ∀ i j (h : i < j), grCubeVal (x ⟨{i, j}, Finset.card_pair h.ne⟩) =
      awayFrac _ (xProd A {i, j}) N (Submodule.Quotient.mk (p := J) (F i j)) := by
    intro i j h
    show awayFrac _ _ N _ = _
    rw [hmin i j h, hmax i j h]
  have hdx : Cube.d _ 2 x = 0 := by
    funext ⟨t, ht⟩
    obtain ⟨i, j, l, hij, hjl, rfl⟩ := exists_triple_of_card_eq_three ht
    rw [Cube.d_two_apply_triple _ x hij hjl]
    have hil := hij.trans hjl
    apply grCubeVal_injective
    rw [grCubeVal_add, grCubeVal_sub, grCubeVal_res, grCubeVal_res, grCubeVal_res, hx j l hjl,
      hx i l hil, hx i j hij, Pi.zero_apply, grCubeVal_zero]
    have hP : (∏ k ∈ ({i, j, l} : Finset ι), (X k : MvPolynomial ι A)) = X i * X j * X l := by
      rw [Finset.prod_insert (by simp [hij.ne, hil.ne]), Finset.prod_pair hjl.ne, mul_assoc]
    rw [locRes_awayFrac X _ (c := X i) (by rw [hP, Finset.prod_pair hjl.ne]; ring),
      locRes_awayFrac X _ (c := X j) (by rw [hP, Finset.prod_pair hil.ne]; ring),
      locRes_awayFrac X _ (c := X l) (by rw [hP, Finset.prod_pair hij.ne]; ring),
      ← map_sub, ← map_add, awayFrac_eq_zero_iff]
    obtain ⟨L, hL⟩ := hcoc i j l
    refine ⟨L, ?_⟩
    have hL' := Ideal.Quotient.eq_zero_iff_mem.2 hL
    rw [hP]
    simp only [map_mul, map_pow, map_add (f := _), map_sub] at hL'
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mk_eq_mk, map_mul,
      map_pow]
    linear_combination hL'
  obtain ⟨y, hy⟩ := (hex x).1 hdx
  have hk := fun i : ι => exists_awayFrac_of_mem_homLoc (grQuot (polyGrading ι A) J)
    (Subtype.property (p := fun w => w ∈ homLoc (grQuot (polyGrading ι A) J) {i} (d : ℤ))
      (y ⟨{i}, Finset.card_singleton i⟩))
  choose k₀ hk₀ using hk
  set N' := Finset.univ.sup k₀ with hN'
  choose m hm hmeq using fun i => hk₀ i N' (Finset.le_sup (Finset.mem_univ i))
  have hmeq' : ∀ i, grCubeVal (y ⟨{i}, Finset.card_singleton i⟩) =
      awayFrac _ (xProd A {i}) N' (m i) := fun i => (hmeq i).symm
  choose g hg hgm using fun i => mem_grQuot.1 (hm i)
  refine ⟨N', fun i => -g i, fun i => ?_, fun i j h => ?_⟩
  · refine mem_polyGrading_natCast.1 ?_
    have := neg_mem (hg i)
    simp only [Finset.card_singleton] at this
    convert this using 2
    push_cast
    ring
  · have e := congrArg grCubeVal (congrFun hy ⟨{i, j}, Finset.card_pair h.ne⟩)
    rw [Cube.d_one_apply_pair _ _ h, grCubeVal_sub, grCubeVal_res, grCubeVal_res, hx i j h,
      hmeq' i, hmeq' j, ← hgm i, ← hgm j,
      locRes_awayFrac X _ (c := X i) (by rw [Finset.prod_pair h.ne, Finset.prod_singleton]),
      locRes_awayFrac X _ (c := X j) (by rw [Finset.prod_pair h.ne, Finset.prod_singleton]; ring),
      ← map_sub, awayFrac_eq_iff] at e
    obtain ⟨l, hl⟩ := e
    rw [Finset.prod_pair h.ne] at hl
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mk_eq_mk, map_mul,
      map_pow, mul_sub] at hl
    refine ⟨l, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
    simp only [map_mul, map_pow, map_sub, map_neg]
    linear_combination (exp := 1) -hl

theorem exists_coboundary_of_cocycle_homogeneous : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (n : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) A)), (∀ F ∈ J, ∀ d, homogeneousComponent d F ∈ J) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (N : ℕ) (F : Fin (n + 1) → Fin (n + 1) → MvPolynomial (Fin (n + 1)) A), (∀ i j, (F i j).IsHomogeneous (d + 2 * N)) → (∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) A) * X j * X l) ^ L * (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J) → ∃ (N' : ℕ) (G : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A), (∀ i, (G i).IsHomogeneous (d + N')) ∧ ∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) A) * X j) ^ L * ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J := by
  intro A _ _ n J hJ
  classical
  have hJh : (J : Submodule (MvPolynomial (Fin (n + 1)) A) (MvPolynomial (Fin (n + 1)) A)).IsHomogeneous
      (polyGrading (Fin (n + 1)) A) := by
    have e : J = Submodule.span (MvPolynomial (Fin (n + 1)) A)
        {g | ∃ F ∈ J, ∃ k : ℕ, g = homogeneousComponent k F} := by
      apply le_antisymm
      · intro F hF
        rw [← sum_homogeneousComponent F]
        exact Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨F, hF, k, rfl⟩
      · rw [Submodule.span_le]
        rintro _ ⟨F, hF, k, rfl⟩
        exact hJ F hF k
    rw [e]
    exact isHomogeneous_span_gr _ (by
      rintro _ ⟨F, _, k, rfl⟩
      exact ⟨k, mem_polyGrading_natCast.2 (homogeneousComponent_isHomogeneous k F)⟩)
  letI := grQuotDecomposition (polyGrading (Fin (n + 1)) A) hJh
  obtain ⟨n₀, h₀⟩ := cubeComplex_grCube_exactAt_of_finite (Fin (n + 1)) A
    (MvPolynomial (Fin (n + 1)) A ⧸ J) (grQuot (polyGrading (Fin (n + 1)) A) J) inferInstance
  refine ⟨n₀.toNat, fun d hd N F hF hcoc => ?_⟩
  have hex := (cubeComplex_exactAt_succ_iff _ 1).1 (h₀ d (by omega) 2)
  obtain ⟨N', G, hG, hlt⟩ := exists_coboundary_lt J d hex N F hF hcoc
  refine ⟨N', G, hG, fun i j => ?_⟩
  obtain ⟨L, hL⟩ := cocycle_all_pairs_of_lt (fun i => Ideal.Quotient.mk J (X i))
    (fun i j => Ideal.Quotient.mk J (F i j)) (fun i => Ideal.Quotient.mk J (G i)) N N'
    (fun i j l => (hcoc i j l).imp fun L hL => by
      simpa only [map_mul, map_pow, map_sub, map_add (f := _)] using Ideal.Quotient.eq_zero_iff_mem.2 hL)
    (fun i j h => (hlt i j h).imp fun L hL => by
      simpa only [map_mul, map_pow, map_sub, map_add (f := _)] using Ideal.Quotient.eq_zero_iff_mem.2 hL)
    i j
  exact ⟨L, Ideal.Quotient.eq_zero_iff_mem.1 (by simpa only [map_mul, map_pow, map_sub] using hL)⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfFractionCocycleHomogeneousIdeaStatement

section

@[expose] public section

open MvPolynomial

theorem _root_.GlobalTheory.T.exists_coboundary_of_fraction_cocycle_homogeneous_ideal : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (n : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) A)), (∀ F ∈ J, ∀ d, homogeneousComponent d F ∈ J) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (N : ℕ) (F : Fin (n + 1) → Fin (n + 1) → MvPolynomial (Fin (n + 1)) A), (∀ i j, (F i j).IsHomogeneous (d + 2 * N)) → (∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) A) * X j * X l) ^ L * (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J) → ∃ (N' : ℕ) (G : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A), (∀ i, (G i).IsHomogeneous (d + N')) ∧ ∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) A) * X j) ^ L * ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J := by
  first | exact @GlobalTheory.exists_coboundary_of_cocycle_homogeneous | exact GlobalTheory.exists_coboundary_of_cocycle_homogeneous | (intros; apply GlobalTheory.exists_coboundary_of_cocycle_homogeneous <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSerreVanishingCechCocycles

section

@[expose] public section

open MvPolynomial

namespace GlobalTheory.UniformCocycle

variable {R : Type} [CommRing R] {σ : Type}

noncomputable def proj (I : Ideal R) (e : ℕ) (P : MvPolynomial σ (reesAlgebra I)) :
    MvPolynomial σ R :=
  ∑ m ∈ P.support, monomial m (((AddMonoidAlgebra.coeff P m : reesAlgebra I) : Polynomial R).coeff e)

theorem coeff_proj (I : Ideal R) (e : ℕ) (P : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (proj I e P) m = ((AddMonoidAlgebra.coeff P m : reesAlgebra I) : Polynomial R).coeff e := by
  classical
  simp only [proj, coeff_sum, coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not] at h
    simp [h]

theorem proj_add (I : Ideal R) (e : ℕ) (P Q : MvPolynomial σ (reesAlgebra I)) :
    proj I e (P + Q) = proj I e P + proj I e Q := by
  ext m; simp [coeff_proj]

theorem proj_sub (I : Ideal R) (e : ℕ) (P Q : MvPolynomial σ (reesAlgebra I)) :
    proj I e (P - Q) = proj I e P - proj I e Q := by
  ext m; simp [coeff_proj]

theorem proj_X_mul (I : Ideal R) (e : ℕ) (i : σ) (P : MvPolynomial σ (reesAlgebra I)) :
    proj I e (X i * P) = X i * proj I e P := by
  classical
  ext m
  rw [coeff_proj, coeff_X_mul', coeff_X_mul']
  split_ifs <;> simp [coeff_proj]

theorem proj_Xpow_mul (I : Ideal R) (e : ℕ) (i : σ) (k : ℕ) (P : MvPolynomial σ (reesAlgebra I)) :
    proj I e (X i ^ k * P) = X i ^ k * proj I e P := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, proj_X_mul, ih, ← mul_assoc, ← pow_succ']


open Classical in
noncomputable def liftCoeff (I : Ideal R) (e : ℕ) (r : R) : reesAlgebra I :=
  if h : r ∈ I ^ e then ⟨Polynomial.monomial e r, reesAlgebra.monomial_mem.mpr h⟩ else 0

theorem liftCoeff_zero (I : Ideal R) (e : ℕ) : liftCoeff I e 0 = 0 := by
  unfold liftCoeff
  rw [dite_eq_left (zero_mem _)]
  apply Subtype.ext; simp

noncomputable def liftE (I : Ideal R) (e : ℕ) (F : MvPolynomial σ R) :
    MvPolynomial σ (reesAlgebra I) :=
  ∑ m ∈ F.support, monomial m (liftCoeff I e (AddMonoidAlgebra.coeff F m))

theorem coeff_liftE (I : Ideal R) (e : ℕ) (F : MvPolynomial σ R) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (liftE I e F) m = liftCoeff I e (AddMonoidAlgebra.coeff F m) := by
  classical
  simp only [liftE, coeff_sum, coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not] at h
    rw [h, liftCoeff_zero]

theorem proj_liftE {I : Ideal R} {e : ℕ} {F : MvPolynomial σ R} (h : ∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e)
    (e' : ℕ) : proj I e' (liftE I e F) = if e' = e then F else 0 := by
  ext m
  rw [coeff_proj, coeff_liftE, liftCoeff, dite_eq_left (h m)]
  simp only [Polynomial.coeff_monomial]
  by_cases h1 : e' = e
  · subst h1; simp
  · rw [Finsupp.single_eq_of_ne h1, ite_eq_right h1]
    simp

theorem isHomogeneous_liftE {I : Ideal R} {e t : ℕ} {F : MvPolynomial σ R}
    (hF : F.IsHomogeneous t) : (liftE I e F).IsHomogeneous t := by
  intro m hm
  apply hF
  intro h0
  apply hm
  rw [coeff_liftE, h0, liftCoeff_zero]

theorem isHomogeneous_proj {I : Ideal R} {e t : ℕ} {P : MvPolynomial σ (reesAlgebra I)}
    (hP : P.IsHomogeneous t) : (proj I e P).IsHomogeneous t := by
  intro m hm
  apply hP
  intro h0
  apply hm
  rw [coeff_proj, h0]
  simp

end GlobalTheory.UniformCocycle

namespace GlobalTheory


open UniformCocycle in
theorem uniformSerre_cocycle : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ e : ℕ, ∀ (N : ℕ) (F : Fin (n + 1) → Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i j, (F i j).IsHomogeneous (d + 2 * N)) → (∀ i j m, AddMonoidAlgebra.coeff (F i j) m ∈ I ^ e) → (∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j * X l) ^ L * (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J e) → ∃ (N' : ℕ) (G : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i, (G i).IsHomogeneous (d + N')) ∧ (∀ i m, AddMonoidAlgebra.coeff (G i) m ∈ I ^ e) ∧ ∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j) ^ L * ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J e := by
  open UniformCocycle in
  intro R _ _ I n J hJ
  obtain ⟨𝔞, h𝔞h, h𝔞⟩ := GlobalTheory.T.exists_homogeneous_ideal_over_reesAlgebra R I n J hJ
  obtain ⟨d₀, hd₀⟩ := GlobalTheory.T.exists_coboundary_of_fraction_cocycle_homogeneous_ideal (reesAlgebra I) n 𝔞 h𝔞h
  refine ⟨d₀, fun d hd e N F hFh hFc hcoc => ?_⟩
  have hF'h : ∀ i j, (liftE I e (F i j)).IsHomogeneous (d + 2 * N) :=
    fun i j => isHomogeneous_liftE (hFh i j)
  have hF'p : ∀ e' i j, proj I e' (liftE I e (F i j)) = if e' = e then F i j else 0 :=
    fun e' i j => proj_liftE (hFc i j) e'
  have hcoc' : ∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) (reesAlgebra I)) * X j * X l) ^ L *
      (X l ^ N * liftE I e (F i j) + X i ^ N * liftE I e (F j l) - X j ^ N * liftE I e (F i l)) ∈ 𝔞 := by
    intro i j l
    obtain ⟨L, hL⟩ := hcoc i j l
    refine ⟨L, ?_⟩
    have hh := ((((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).mul (isHomogeneous_X _ l)).pow L).mul
      ((((isHomogeneous_X_pow l N).mul (hF'h i j)).add ((isHomogeneous_X_pow i N).mul (hF'h j l))).sub
        ((isHomogeneous_X_pow j N).mul (hF'h i l)))
    rw [h𝔞 _ _ hh]
    intro e' G hG
    have hGe : G = proj I e' (((X i : MvPolynomial (Fin (n + 1)) (reesAlgebra I)) * X j * X l) ^ L *
      (X l ^ N * liftE I e (F i j) + X i ^ N * liftE I e (F j l) - X j ^ N * liftE I e (F i l))) := by
      ext m; rw [hG, coeff_proj]
    rw [hGe]
    simp only [mul_pow, mul_assoc, proj_add, proj_sub, proj_Xpow_mul, hF'p]
    by_cases he : e' = e
    · subst he
      simp only [↓reduceIte]
      simpa only [mul_pow, mul_assoc] using hL
    · simp [he]
  obtain ⟨N', G', hG'h, hG'⟩ := hd₀ d hd N (fun i j => liftE I e (F i j)) hF'h hcoc'
  refine ⟨N', fun i => proj I e (G' i), fun i => isHomogeneous_proj (hG'h i), fun i m => ?_, fun i j => ?_⟩
  · rw [coeff_proj]
    exact (mem_reesAlgebra_iff I _).mp (AddMonoidAlgebra.coeff (G' i) m).2 e
  · obtain ⟨L, hL⟩ := hG' i j
    refine ⟨L, ?_⟩
    have h2 : (1 + 1) * N + (N' + (d + N')) = (1 + 1) * N' + (d + 2 * N) := by ring
    have hh := (((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).pow L).mul
      ((((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).pow N').mul (hF'h i j) |>.sub
        (h2 ▸ (((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).pow N).mul
          (((isHomogeneous_X_pow j N').mul (hG'h i)).sub ((isHomogeneous_X_pow i N').mul (hG'h j)))))
    rw [h𝔞 _ _ hh] at hL
    have := hL e (proj I e _) (fun m => coeff_proj I e _ m)
    simp only [mul_pow, mul_assoc, proj_add, proj_sub, proj_Xpow_mul, hF'p, ↓reduceIte] at this
    simpa only [mul_pow, mul_assoc] using this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSerreVanishingCechCocyclesStatement

section

@[expose] public section

open MvPolynomial

theorem _root_.GlobalTheory.T.uniform_serre_vanishing_cech_cocycles : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ e : ℕ, ∀ (N : ℕ) (F : Fin (n + 1) → Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i j, (F i j).IsHomogeneous (d + 2 * N)) → (∀ i j m, AddMonoidAlgebra.coeff (F i j) m ∈ I ^ e) → (∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j * X l) ^ L * (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J e) → ∃ (N' : ℕ) (G : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i, (G i).IsHomogeneous (d + N')) ∧ (∀ i m, AddMonoidAlgebra.coeff (G i) m ∈ I ^ e) ∧ ∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j) ^ L * ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J e := by
  first | exact @GlobalTheory.uniformSerre_cocycle | exact GlobalTheory.uniformSerre_cocycle | (intros; apply GlobalTheory.uniformSerre_cocycle <;> assumption)
end
end
