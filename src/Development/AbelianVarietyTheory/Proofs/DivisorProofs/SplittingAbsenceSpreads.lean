module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.Continuity
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Algebra.MvPolynomial.Monad

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoCommonZeroSpreadsConstructibleNbhd

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory
namespace NoCommonZeroSpread

lemma exists_common_denominator {A Ω : Type} [CommRing A] [Field Ω] (φ : A →+* Ω)
    (S : Finset Ω) (hS : ∀ x ∈ S, x ∈ Subfield.closure (φ.range : Set Ω)) :
    ∃ b : A, φ b ≠ 0 ∧ ∀ x ∈ S, φ b * x ∈ Set.range φ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert x S hx ih =>
    obtain ⟨b, hb, hbS⟩ := ih (fun y hy => hS y (Finset.mem_insert_of_mem hy))
    have hxK := hS x (Finset.mem_insert_self x S)
    rw [Subfield.mem_closure_iff, Subring.closure_eq] at hxK
    obtain ⟨y, hy, z, hz, hyz⟩ := hxK
    obtain ⟨a, rfl⟩ := RingHom.mem_range.1 hy
    obtain ⟨c, rfl⟩ := RingHom.mem_range.1 hz
    by_cases hc : φ c = 0
    · have hx0 : x = 0 := by rw [← hyz, hc, div_zero]
      refine ⟨b, hb, fun w hw => ?_⟩
      rcases Finset.mem_insert.1 hw with h | h
      · exact ⟨0, by rw [h, hx0, mul_zero, map_zero]⟩
      · exact hbS w h
    · refine ⟨b * c, by simp [hb, hc], fun w hw => ?_⟩
      rcases Finset.mem_insert.1 hw with h | h
      · refine ⟨b * a, ?_⟩
        rw [h, ← hyz, map_mul, map_mul]
        field_simp
      · obtain ⟨d, hd⟩ := hbS w h
        refine ⟨d * c, ?_⟩
        rw [map_mul, hd, map_mul]
        ring

theorem no_common_zero_spreads : ∀ (A : Type) [CommRing A] (τ J : Type) [Finite τ] (F : J → MvPolynomial τ A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), (¬ ∃ z : τ → Ω, ∀ j, MvPolynomial.eval₂ φ z (F j) = 0) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → ¬ ∃ z : τ → k, ∀ j, MvPolynomial.eval₂ ψ z (F j) = 0 := by
  intro A _ τ J _ F Ω _ _ φ hno
  classical
  let G : J → MvPolynomial τ Ω := fun j => MvPolynomial.map φ (F j)

  have h1 : (1 : MvPolynomial τ Ω) ∈ Ideal.span (Set.range G) := by
    have hz : MvPolynomial.zeroLocus Ω (Ideal.span (Set.range G)) = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      apply hno
      refine ⟨x, fun j => ?_⟩
      have := hx (G j) (Ideal.subset_span ⟨j, rfl⟩)
      simpa [G, MvPolynomial.coe_aeval_eq_eval, MvPolynomial.eval_map] using this
    have := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω) (Ideal.span (Set.range G))
    rw [hz, MvPolynomial.vanishingIdeal_empty, eq_comm, Ideal.radical_eq_top] at this
    rw [this]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h1

  let K : Subfield Ω := Subfield.closure (φ.range : Set Ω)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K Ω)
    (LinearMap.ker_eq_bot.2 (algebraMap K Ω).injective)
  have hg1 : ∀ y : K, g (y : Ω) = y := fun y => by
    exact LinearMap.congr_fun hg y
  have hgK : ∀ (x : Ω) (y : K), ((g (x * y) : K) : Ω) = (g x : Ω) * y := by
    intro x y
    have : x * (y : Ω) = y • x := by rw [mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, Subfield.coe_mul, mul_comm]
  have hφK : ∀ a : A, φ a ∈ K := fun a => Subfield.subset_closure (RingHom.mem_range_self φ a)
  let P : MvPolynomial τ Ω → MvPolynomial τ Ω := fun h =>
    ∑ m ∈ h.support, MvPolynomial.monomial m ((g (h.coeff m) : K) : Ω)
  have hPc : ∀ h n, (P h).coeff n = ((g (h.coeff n) : K) : Ω) := by
    intro h n
    simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hn
    · rfl
    · rw [MvPolynomial.notMem_support_iff.1 hn]; simp
  have hPadd : ∀ h₁ h₂, P (h₁ + h₂) = P h₁ + P h₂ := by
    intro h₁ h₂; ext n; simp [hPc, MvPolynomial.coeff_add]
  have hP1 : P 1 = 1 := by
    ext n
    rw [hPc, MvPolynomial.coeff_one]
    split_ifs
    · have := hg1 1; simpa using this
    · simp
  have hPmul : ∀ h j, P (h * G j) = P h * G j := by
    intro h j; ext n

    rw [hPc, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul, map_sum]
    refine (map_sum K.subtype _ _).trans (Finset.sum_congr rfl fun x _ => ?_)
    show ((g _ : K) : Ω) = _
    have e : (G j).coeff x.2 = ((⟨φ ((F j).coeff x.2), hφK _⟩ : K) : Ω) := by
      simp [G, MvPolynomial.coeff_map]
    rw [e, hgK, hPc]
  let PA : MvPolynomial τ Ω →+ MvPolynomial τ Ω := AddMonoidHom.mk' P hPadd
  have hsum : ∑ j ∈ c.support, P (c j) * G j = 1 := by
    simp only [Finsupp.sum, smul_eq_mul] at hc
    have := congrArg PA hc

    rw [map_sum] at this
    simp only [PA, AddMonoidHom.mk'_apply] at this
    rw [← hP1]
    convert this using 1
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (hPmul _ _).symm

  let S : Finset Ω := c.support.biUnion (fun j => (P (c j)).coeffs)
  obtain ⟨b, hb, hbS⟩ := exists_common_denominator φ S (by
    intro x hx
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hj
    rw [hPc]; exact (g _).2)
  have hQ : ∀ j, ∃ q : MvPolynomial τ A,
      MvPolynomial.map φ q = MvPolynomial.C (φ b) * P (c j) := by
    intro j
    have : MvPolynomial.C (φ b) * P (c j) ∈ Set.range (MvPolynomial.map (σ := τ) φ) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro y hy
      obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 (Finset.mem_coe.1 hy)
      rw [MvPolynomial.coeff_C_mul]
      by_cases hn : (P (c j)).coeff n = 0
      · rw [hn, mul_zero]; exact ⟨0, map_zero φ⟩
      · have hj : j ∈ c.support := by
          rw [Finsupp.mem_support_iff]
          intro h0; apply hn; rw [hPc, h0]; simp
        exact hbS _ (Finset.mem_biUnion.2 ⟨j, hj,
          MvPolynomial.mem_coeffs_iff.2 ⟨n, MvPolynomial.mem_support_iff.2 hn, rfl⟩⟩)
    exact this
  choose q hq using hQ
  let E : MvPolynomial τ A := MvPolynomial.C b - ∑ j ∈ c.support, q j * F j
  have hE : MvPolynomial.map φ E = 0 := by
    have hG : ∀ j, MvPolynomial.map φ (F j) = G j := fun j => rfl

    simp only [E, map_sub, map_sum, map_mul, MvPolynomial.map_C, hq, hG, _root_.mul_assoc]
    rw [← Finset.mul_sum, hsum, _root_.mul_one, sub_self]
  refine ⟨b, E.coeffs, hb, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hy
    have := congrArg (AddMonoidAlgebra.coeff · n) hE
    rwa [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this
  · intro k _ ψ hψb hψI ⟨z, hz⟩
    have h0 : MvPolynomial.map ψ E = 0 := by
      ext n
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
      by_cases hn : n ∈ E.support
      · exact hψI _ (MvPolynomial.mem_coeffs_iff.2 ⟨n, hn, rfl⟩)
      · rw [MvPolynomial.notMem_support_iff.1 hn, map_zero]
        rfl
    have h2 : MvPolynomial.eval₂ ψ z E = 0 := by
      rw [MvPolynomial.eval₂_eq_eval_map, h0, map_zero]
    have h3 : MvPolynomial.eval₂ ψ z E = ψ b := by
      simp [E, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_C, MvPolynomial.eval₂_sum,
        MvPolynomial.eval₂_mul, hz]
    exact hψb (h3 ▸ h2)

end NoCommonZeroSpread
end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoCommonZeroSpreadsConstructibleNbhdStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.no_common_zero_spreads_constructible_nbhd : ∀ (A : Type) [CommRing A] (τ J : Type) [Finite τ] (F : J → MvPolynomial τ A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), (¬ ∃ z : τ → Ω, ∀ j, MvPolynomial.eval₂ φ z (F j) = 0) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → ¬ ∃ z : τ → k, ∀ j, MvPolynomial.eval₂ ψ z (F j) = 0 := by
  first | exact @GlobalTheory.NoCommonZeroSpread.no_common_zero_spreads | exact GlobalTheory.NoCommonZeroSpread.no_common_zero_spreads | (intros; apply GlobalTheory.NoCommonZeroSpread.no_common_zero_spreads <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplittingAbsenceSpreads

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory.SplitSpread

open MvPolynomial

abbrev Mon (σ : Type) (D : ℕ) := {m : σ →₀ ℕ // m.degree ≤ D}

instance instFiniteMon (σ : Type) [Finite σ] (D : ℕ) : Finite (Mon σ D) :=
  (Finsupp.finite_of_degree_le (σ := σ) D).to_subtype

noncomputable instance instFintypeMon (σ : Type) [Finite σ] (D : ℕ) : Fintype (Mon σ D) :=
  Fintype.ofFinite _

abbrev Var (σ : Type) (D : ℕ) := (Bool × Mon σ D) ⊕ (Bool × σ) ⊕ Bool

theorem sum_eq_degree {σ : Type} (s : σ →₀ ℕ) : (s.sum fun _ e => e) = s.degree := rfl

theorem hom_eval {R S τ : Type} [CommSemiring R] [CommSemiring S] (h : R →+* S) (x : τ → R)
    (W : MvPolynomial τ R) : h (eval x W) = MvPolynomial.eval (h ∘ x) (MvPolynomial.map h W) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, RingHom.comp_id]

variable {σ : Type} [Finite σ] (A : Type) [CommRing A] (D : ℕ)

noncomputable def gen (b : Bool) : MvPolynomial σ (MvPolynomial (Var σ D) A) :=
  ∑ m : Mon σ D, monomial m.1 (X (Sum.inl (b, m)))

noncomputable def eqs (f g : MvPolynomial σ A) :
    ((σ →₀ ℕ) ⊕ Bool ⊕ Bool) → MvPolynomial (Var σ D) A
  | Sum.inl n => AddMonoidAlgebra.coeff (gen A D true * gen A D false - MvPolynomial.map C f) n
  | Sum.inr (Sum.inl b) => MvPolynomial.eval (fun i => X (Sum.inr (Sum.inl (b, i)))) (gen A D b)
  | Sum.inr (Sum.inr b) =>
      X (Sum.inr (Sum.inr b)) * MvPolynomial.eval (fun i => X (Sum.inr (Sum.inl (b, i)))) (MvPolynomial.map C g) - 1

variable {A D}

theorem map_gen {k : Type} [CommRing k] (ψ : A →+* k) (z : Var σ D → k) (b : Bool) :
    MvPolynomial.map (eval₂Hom ψ z) (gen A D b) = ∑ m : Mon σ D, monomial m.1 (z (Sum.inl (b, m))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [gen, map_sum, map_monomial]

theorem totalDegree_sum_le {k : Type} [CommRing k] (c : Mon σ D → k) :
    (∑ m : Mon σ D, monomial m.1 (c m)).totalDegree ≤ D := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m _ => ?_)
  exact (totalDegree_monomial_le _ _).trans m.2

theorem sum_coeff {k : Type} [CommRing k] (p : MvPolynomial σ k) (hp : p.totalDegree ≤ D) :
    ∑ m : Mon σ D, monomial m.1 (AddMonoidAlgebra.coeff p m.1) = p := by
  classical
  ext n
  simp only [coeff_sum, coeff_monomial]
  by_cases hn : n.degree ≤ D
  · rw [Finset.sum_eq_single ⟨n, hn⟩]
    · simp
    · intro m _ hm
      rw [if_neg]
      intro h; exact hm (Subtype.ext h)
    · simp
  · rw [Finset.sum_eq_zero]
    · by_contra h
      exact hn ((sum_eq_degree n ▸ le_totalDegree (mem_support_iff.mpr (Ne.symm h))).trans hp)
    · intro m _
      rw [if_neg]
      rintro rfl; exact hn m.2

end GlobalTheory.SplitSpread

namespace GlobalTheory.SplitSpread
open MvPolynomial
variable {σ : Type} [Finite σ] {A : Type} [CommRing A] {D : ℕ}

noncomputable def spec {k : Type} [CommRing k] (z : Var σ D → k) (b : Bool) : MvPolynomial σ k :=
  ∑ m : Mon σ D, monomial m.1 (z (Sum.inl (b, m)))

theorem eval_eqs_coeff {k : Type} [CommRing k] (ψ : A →+* k) (z : Var σ D → k)
    (f g : MvPolynomial σ A) (n : σ →₀ ℕ) :
    eval₂ ψ z (eqs A D f g (Sum.inl n)) = AddMonoidAlgebra.coeff (spec z true * spec z false - MvPolynomial.map ψ f) n := by
  rw [← coe_eval₂Hom]
  simp only [eqs]
  rw [← MvPolynomial.coeff_map, map_sub, map_mul, map_gen, map_gen, MvPolynomial.map_map,
    eval₂Hom_comp_C]
  rfl

theorem eval_eqs_point {k : Type} [CommRing k] (ψ : A →+* k) (z : Var σ D → k)
    (f g : MvPolynomial σ A) (b : Bool) :
    eval₂ ψ z (eqs A D f g (Sum.inr (Sum.inl b))) =
      MvPolynomial.eval (fun i => z (Sum.inr (Sum.inl (b, i)))) (spec z b) := by
  rw [← coe_eval₂Hom]
  simp only [eqs]
  rw [hom_eval, map_gen]
  congr 2 <;> (ext i; simp)

theorem eval_eqs_inv {k : Type} [CommRing k] (ψ : A →+* k) (z : Var σ D → k)
    (f g : MvPolynomial σ A) (b : Bool) :
    eval₂ ψ z (eqs A D f g (Sum.inr (Sum.inr b))) =
      z (Sum.inr (Sum.inr b)) *
        MvPolynomial.eval (fun i => z (Sum.inr (Sum.inl (b, i)))) (MvPolynomial.map ψ g) - 1 := by
  simp only [eqs, eval₂_sub, eval₂_mul, eval₂_X, eval₂_one]
  rw [← coe_eval₂Hom, hom_eval, MvPolynomial.map_map, eval₂Hom_comp_C]
  congr 4 <;> (ext i; simp)
end GlobalTheory.SplitSpread

namespace GlobalTheory.SplitSpread
open MvPolynomial
variable {σ : Type} [Finite σ] {A : Type} [CommRing A]

def Bad (f g : MvPolynomial σ A) (D : ℕ) (k : Type) [Field k] (ψ : A →+* k) : Prop :=
  ∃ u v : MvPolynomial σ k, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧
    u * v = MvPolynomial.map ψ f ∧ ∃ P Q : σ → k, MvPolynomial.eval P u = 0 ∧
      MvPolynomial.eval P (MvPolynomial.map ψ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧
      MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0

theorem bad_iff (f g : MvPolynomial σ A) (D : ℕ) (k : Type) [Field k] (ψ : A →+* k) :
    (∃ z : Var σ D → k, ∀ j, eval₂ ψ z (eqs A D f g j) = 0) ↔ Bad f g D k ψ := by
  constructor
  · rintro ⟨z, hz⟩
    have hinv : ∀ b, MvPolynomial.eval (fun i => z (Sum.inr (Sum.inl (b, i))))
        (MvPolynomial.map ψ g) ≠ 0 := by
      intro b h0
      have := hz (Sum.inr (Sum.inr b))
      rw [eval_eqs_inv, h0] at this
      simp at this
    refine ⟨spec z true, spec z false, totalDegree_sum_le _, totalDegree_sum_le _, ?_,
      fun i => z (Sum.inr (Sum.inl (true, i))), fun i => z (Sum.inr (Sum.inl (false, i))),
      ?_, hinv true, ?_, hinv false⟩
    · ext n
      have := hz (Sum.inl n)
      rw [eval_eqs_coeff, MvPolynomial.coeff_sub, sub_eq_zero] at this
      exact this
    · have := hz (Sum.inr (Sum.inl true)); rwa [eval_eqs_point] at this
    · have := hz (Sum.inr (Sum.inl false)); rwa [eval_eqs_point] at this
  · rintro ⟨u, v, hu, hv, huv, P, Q, hPu, hPg, hQv, hQg⟩
    let z : Var σ D → k := Sum.elim (fun p => AddMonoidAlgebra.coeff (if p.1 then u else v) p.2.1)
      (Sum.elim (fun p => if p.1 then P p.2 else Q p.2)
        (fun b => (MvPolynomial.eval (if b then P else Q) (MvPolynomial.map ψ g))⁻¹))
    have hs : ∀ b, spec z b = if b then u else v := by
      intro b
      cases b
      · exact sum_coeff v hv
      · exact sum_coeff u hu
    refine ⟨z, ?_⟩
    rintro (n | b | b)
    · rw [eval_eqs_coeff, hs, hs]
      simp [huv]
    · rw [eval_eqs_point, hs]
      cases b <;> simpa [z]
    · rw [eval_eqs_inv]
      cases b
      · simp only [z, Sum.elim_inr, Bool.false_eq_true, if_false]
        exact sub_eq_zero.mpr (inv_mul_cancel₀ hQg)
      · simp only [z, Sum.elim_inr, if_true]
        exact sub_eq_zero.mpr (inv_mul_cancel₀ hPg)

end GlobalTheory.SplitSpread

theorem GlobalTheory.splitting_absence_spreads : ∀ (A : Type) [CommRing A] (σ : Type) [Finite σ] (f g : MvPolynomial σ A) (D : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = MvPolynomial.map φ f ∧ ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P (MvPolynomial.map φ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q (MvPolynomial.map φ g) ≠ 0) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → ¬ (∃ u v : MvPolynomial σ k, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = MvPolynomial.map ψ f ∧ ∃ P Q : σ → k, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P (MvPolynomial.map ψ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0) := by
  intro A _ σ _ f g D Ω _ _ φ hbad
  have h0 : ¬ ∃ z : GlobalTheory.SplitSpread.Var σ D → Ω, ∀ j,
      MvPolynomial.eval₂ φ z (GlobalTheory.SplitSpread.eqs A D f g j) = 0 := by
    rw [GlobalTheory.SplitSpread.bad_iff]; exact hbad
  obtain ⟨a, I, ha, hI, hk⟩ := GlobalTheory.T.no_common_zero_spreads_constructible_nbhd A _ _ (GlobalTheory.SplitSpread.eqs A D f g) Ω φ h0
  refine ⟨a, I, ha, hI, fun k _ ψ hψa hψI hb => hk k ψ hψa hψI ?_⟩
  exact (GlobalTheory.SplitSpread.bad_iff f g D k ψ).mpr hb
end
end
