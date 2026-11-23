module

public import Development.EtaleCohomology.DivisorCycles.CycleCount
public import Development.EtaleCohomology.DivisorCycles.ChainPf
public import Development.EtaleCohomology.DivisorCycles.ConjugateIdempotents
public import Development.EtaleCohomology.DivisorCycles.CycleCount2
public import Development.EtaleCohomology.DivisorCycles.DegPoly2
public import Development.EtaleCohomology.DivisorCycles.ExpVanPf
public import Development.EtaleCohomology.DivisorCycles.GenSpecProof
public import Development.EtaleCohomology.DivisorCycles.MatUnitsOf
public import Development.EtaleCohomology.DivisorCycles.SpecPtPf
public import Development.EtaleCohomology.DivisorCycles.SumMulSum
public import Development.EtaleCohomology.DivisorCycles.TangentDegree
public import Development.EtaleCohomology.DivisorCycles.TangentFieldExtension
public import Development.EtaleCohomology.DivisorCycles.TangentIndexDvd
public import Development.EtaleCohomology.DivisorCycles.OpenCoset
public import Mathlib.RingTheory.PowerSeries.Exp
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.EtaleCohomology.DivisorCycles.UnitFactorizationTheorem

-- Source module: Development.EtaleCohomology.DivisorCycles.TorusPtPf

section

@[expose] public section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.TorusPtPf
open LateralTheory.DivDb

variable {C : Type} [Field C] [CharZero C]

noncomputable def E (a : C) : PowerSeries C := PowerSeries.rescale a (PowerSeries.exp C)

lemma coeff_E (a : C) (k : ℕ) : PowerSeries.coeff k (E a) = a ^ k * (k.factorial : C)⁻¹ := by
  simp [E, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]

lemma E_add (a b : C) : E a * E b = E (a + b) := PowerSeries.exp_mul_exp_eq_exp_add a b

lemma E_zero : E (0 : C) = 1 := by
  ext k; rcases k with _ | k <;> simp [coeff_E, PowerSeries.coeff_one]

lemma E_prod {ι : Type} (s : Finset ι) (a : ι → C) : ∏ i ∈ s, E (a i) = E (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [E_zero]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, E_add]

lemma E_pow (a : C) (m : ℕ) : E a ^ m = E ((m : C) * a) := by
  induction m with
  | zero => simp [E_zero]
  | succ m ih => rw [pow_succ, ih, E_add]; congr 1; push_cast; ring

lemma E_ne (a b c : C) (h : E a - PowerSeries.C b * E c = 0) : b = 1 ∧ a = c := by
  have h0 := congrArg (PowerSeries.coeff 0) h
  have h1 := congrArg (PowerSeries.coeff 1) h
  simp only [map_sub, PowerSeries.coeff_C_mul, coeff_E, map_zero] at h0 h1
  simp at h0 h1
  have hb : b = 1 := by linear_combination -h0
  refine ⟨hb, ?_⟩
  rw [hb] at h1
  linear_combination h1

lemma pow_sys {N n : ℕ} {p : Fin n → Mat C N} (hp : Sys p) (e : Fin n → C) (k : ℕ) :
    (∑ i, e i • p i) ^ k = ∑ i, e i ^ k • p i := by
  induction k with
  | zero => simpa using hp.1.complete.symm
  | succ k ih =>
    rw [pow_succ, ih, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [smul_mul_smul_comm, (hp.1.idem i).eq, pow_succ]
    · intro j _ hji; rw [smul_mul_smul_comm, hp.1.ortho hji.symm, smul_zero]
    · simp

lemma entry_exp {N n : ℕ} {p : Fin n → Mat C N} (hp : Sys p) (e : Fin n → C) (a b : Fin N) :
    (PowerSeries.mk fun k => ((k.factorial : C)⁻¹ • (∑ i, e i • p i) ^ k) a b) =
      ∑ j, PowerSeries.C (p j a b) * E (e j) := by
  ext k

  simp only [PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_C_mul, coeff_E, pow_sys hp, Matrix.smul_apply,
  Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

noncomputable def bin {n : ℕ} (q : Finset (Fin n) × Finset (Fin n) × C) : MvPolynomial (Fin n) C :=
  (∏ i ∈ q.1, MvPolynomial.X i) ^ q.2.1.card - MvPolynomial.C q.2.2 * (∏ i ∈ q.2.1, MvPolynomial.X i) ^ q.1.card

theorem TorusPt_of (hE : ExpVan) (hS : SpecPt) : TorusPt := by
  intro C _ _ _ N n S p e hp hlac hX B hB
  classical
  let x : Fin n → PowerSeries C := fun j => E (e j)
  let Q : Set (Finset (Fin n) × Finset (Fin n) × C) :=
    {q | q.1.Nonempty ∧ q.2.1.Nonempty ∧ Disjoint q.1 q.2.1 ∧ q.2.2 ∈ B}
  let G : Set (MvPolynomial (Fin n) C) := Set.range (fun j => MvPolynomial.X j) ∪ bin '' Q
  have hQ : Q.Finite := (Set.finite_univ.prod (Set.finite_univ.prod hB)).subset fun q hq => by
    simp only [Set.mem_prod, Set.mem_univ, true_and]; exact hq.2.2.2
  have hG : G.Finite := (Set.finite_range _).union (hQ.image _)
  have hxg : ∀ g ∈ G, MvPolynomial.aeval x g ≠ 0 := by
    rintro g (⟨j, rfl⟩ | ⟨q, ⟨h1, h2, h3, h4⟩, rfl⟩)
    · intro h0
      have := congrArg (PowerSeries.coeff 0) h0
      simp [x, coeff_E] at this
    · intro h0
      simp only [bin, map_sub, map_mul, map_pow, map_prod, MvPolynomial.aeval_X, MvPolynomial.aeval_C, x, E_prod,
        E_pow] at h0
      have h0' : E ((q.2.1.card : C) * ∑ i ∈ q.1, e i) - PowerSeries.C q.2.2 * E ((q.1.card : C) * ∑ i ∈ q.2.1, e i) = 0 := by
        simpa using h0
      exact hlac _ _ h1 h2 h3 (E_ne _ _ _ h0').2
  obtain ⟨y, hy1, hy2⟩ := hS C (PowerSeries C) (Fin n) x G hG hxg
  refine ⟨y, fun j => ?_, fun f hf => ?_, fun O O' hO hO' hd b hb => ?_⟩
  · have := hy2 _ (Or.inl ⟨j, rfl⟩); simpa using this
  · have h := hE C N S _ hX f hf
    have hent : (fun ab : Fin N × Fin N => PowerSeries.mk fun k =>
          ((k.factorial : C)⁻¹ • (∑ i, e i • p i) ^ k) ab.1 ab.2)
        = fun ab => MvPolynomial.aeval x (∑ j, MvPolynomial.C (p j ab.1 ab.2) * MvPolynomial.X j) := by
      funext ab; rw [entry_exp hp]; simp [x]
    rw [hent, ← MvPolynomial.aeval_bind₁] at h
    have h2 := hy1 _ h
    have h3 : MvPolynomial.aeval y
        ((MvPolynomial.bind₁ fun ab : Fin N × Fin N => ∑ j, MvPolynomial.C (p j ab.1 ab.2) * MvPolynomial.X j) f) = 0 := by
      exact h2
    rw [MvPolynomial.aeval_bind₁] at h3
    unfold ev
    rw [show (fun q : Fin N × Fin N => (∑ j, y j • p j) q.1 q.2) = fun ab =>
        MvPolynomial.aeval y (∑ j, MvPolynomial.C (p j ab.1 ab.2) * MvPolynomial.X j) from
      funext fun ab => by simp [Matrix.sum_apply, mul_comm]]
    exact h3
  · intro h
    apply hy2 _ (Or.inr ⟨(O, O', b), ⟨hO, hO', hd, hb⟩, rfl⟩)
    simp only [bin, map_sub, map_mul, map_pow, map_prod, MvPolynomial.eval_X, MvPolynomial.eval_C]
    rw [h]; ring
end LateralTheory.DivDb.TorusPtPf
end
end

-- Source module: Development.EtaleCohomology.DivisorCycles.UnipotentPartTrivial

section

@[expose] public section

open Matrix
namespace LateralTheory.DivDb.UnipotentPartTrivial
open LateralTheory.DivDb

theorem pow_vanish {C : Type} [Field C] {N : ℕ} (E : Mat C N) (h : E * E = 0) (k : ℕ) (hk : 2 ≤ k) :
    E ^ k = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, sq, h, zero_mul]

theorem series_eq {C : Type} [Field C] {N : ℕ} (E : Mat C N) (h : E * E = 0) (p : Fin N × Fin N) :
    PowerSeries.mk (fun k => ((k.factorial : C)⁻¹ • E ^ k) p.1 p.2)
      = ((Polynomial.C ((1 : Mat C N) p.1 p.2) + Polynomial.X * Polynomial.C (E p.1 p.2) : Polynomial C) :
          PowerSeries C) := by
  ext k
  rw [PowerSeries.coeff_mk, Polynomial.coeff_coe]
  rcases k with _ | _ | k
  · simp
  · simp
  · rw [pow_vanish E h _ (by omega)]
    simp

theorem Unip_of (h : ExpVan) : Unip := by
  intro C _ _ N S E hE hEE f hf
  have h0 := h C N S E hE f hf
  let g : Fin N × Fin N → Polynomial C := fun p =>
    Polynomial.C ((1 : Mat C N) p.1 p.2) + Polynomial.X * Polynomial.C (E p.1 p.2)
  have h1 : MvPolynomial.aeval g f = 0 := by
    apply Polynomial.coe_injective
    rw [Polynomial.coe_zero]
    have hc := congrArg (fun φ => φ f)
      (MvPolynomial.comp_aeval (R := C) g (Polynomial.coeToPowerSeries.algHom C))
    simp only [AlgHom.comp_apply] at hc
    simp only [Polynomial.coeToPowerSeries.algHom_apply, PowerSeries.map_id, Algebra.algebraMap_self] at hc
    simp only [id] at hc
    have hs : (fun p : Fin N × Fin N => PowerSeries.mk (fun k => ((k.factorial : C)⁻¹ • E ^ k) p.1 p.2))
        = fun i => ((g i : Polynomial C) : PowerSeries C) := funext (series_eq E hEE)
    rw [hs] at h0
    exact hc.trans h0
  have h2 := congrArg (fun q => Polynomial.aeval (1 : C) q) h1
  simp only [map_zero] at h2
  have hc := congrArg (fun φ => φ f) (MvPolynomial.comp_aeval (R := C) g (Polynomial.aeval (1 : C)))
  simp only [AlgHom.comp_apply] at hc
  rw [hc] at h2
  have h3 : (fun p : Fin N × Fin N => Polynomial.aeval (1 : C) (g p)) = fun p => (1 + E) p.1 p.2 := by
    funext p; simp [g]
  rw [h3] at h2
  unfold ev
  exact h2

end LateralTheory.DivDb.UnipotentPartTrivial
end
end

-- Source module: Development.EtaleCohomology.DivisorCycles.ZclMulPf

section

@[expose] public section

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.ZclMulPf
open LateralTheory.DivDb

theorem left_mem (hC : Chain) {C : Type} [Field C] {N : ℕ} (S : Submonoid (Mat C N))
    (s : Mat C N) (hs : s ∈ S) (y : Mat C N) (hy : y ∈ Zcl (S : Set (Mat C N))) :
    s * y ∈ Zcl (S : Set (Mat C N)) := by
  intro f hf
  obtain ⟨f', hf', -⟩ := hC C N N (LinearMap.mulLeft C s) f
  have hv : f' ∈ Van (S : Set (Mat C N)) := by
    intro t ht
    rw [hf']
    exact hf _ (S.mul_mem hs ht)
  have := hy f' hv
  rw [hf'] at this
  simpa using this

theorem mul_mem (hC : Chain) {C : Type} [Field C] {N : ℕ} (S : Submonoid (Mat C N))
    (x : Mat C N) (hx : x ∈ Zcl (S : Set (Mat C N))) (y : Mat C N) (hy : y ∈ Zcl (S : Set (Mat C N))) :
    x * y ∈ Zcl (S : Set (Mat C N)) := by
  intro f hf
  obtain ⟨f', hf', -⟩ := hC C N N (LinearMap.mulRight C y) f
  have hv : f' ∈ Van (S : Set (Mat C N)) := by
    intro t ht
    rw [hf']
    exact left_mem hC S t ht y hy f hf
  have := hx f' hv
  rw [hf'] at this
  simpa using this

end LateralTheory.DivDb.ZclMulPf

namespace LateralTheory.DivDb

theorem ZclMul_of (hC : Chain) : ZclMul := fun _C _ _N S x hx y hy =>
  LateralTheory.DivDb.ZclMulPf.mul_mem hC S x hx y hy

end LateralTheory.DivDb
end
end

-- Source module: Development.EtaleCohomology.DivisorCycles.FinKey

section

@[expose] public section

namespace LateralTheory.Fin.Key
theorem etale_matrix_units_system_of_key : LateralTheory.DivDb.MatrixUnits₂ := by
  apply LateralTheory.DivDb.MatrixUnitConstruction.MatUnits_of
theorem etale_idempotent_conjugacy_of_key : LateralTheory.DivDb.IdemConj := by
  apply LateralTheory.DivDb.ConjugateIdempotents.IdemConj_of <;> first | exact etale_matrix_units_system_of_key
theorem etale_unit_factorization_of_key : LateralTheory.DivDb.UnitFactorization := by
  apply LateralTheory.DivDb.UnitFactorizationTheorem.UnitFactor_of
theorem etale_divisibility_chain_of_key : LateralTheory.DivDb.Chain := by
  apply LateralTheory.DivDb.Chain_of
theorem etale_zariski_closure_mul_closed_of_key : LateralTheory.DivDb.ZclMul := by
  apply LateralTheory.DivDb.ZclMul_of <;> first | exact etale_divisibility_chain_of_key
theorem etale_tangent_index_divides_of_key : LateralTheory.DivDb.TanIndex := by
  apply LateralTheory.DivDb.TangentIndexDvd.TanIndex_of <;> first | exact etale_divisibility_chain_of_key | exact etale_zariski_closure_mul_closed_of_key
theorem etale_tangent_field_extension_of_key : LateralTheory.DivDb.TanField := by
  apply LateralTheory.DivDb.TangentFieldExtension.TanField_of <;> first | exact etale_divisibility_chain_of_key
theorem etale_exponent_vanishing_of_key : LateralTheory.DivDb.ExpVan := by
  apply LateralTheory.DivDb.ExpVan_of <;> first | exact etale_tangent_field_extension_of_key
theorem etale_unipotent_part_trivial_of_key : LateralTheory.DivDb.Unip := by
  apply LateralTheory.DivDb.UnipotentPartTrivial.Unip_of <;> first | exact etale_exponent_vanishing_of_key
theorem etale_generic_spectrum_of_key : LateralTheory.DivDb.GenSpec := by
  apply LateralTheory.DivDb.GenSpecProof.GenSpec_of
theorem etale_special_point_exists_of_key : LateralTheory.DivDb.SpecPt := by
  apply LateralTheory.DivDb.SpecPtPf.SpecPt_of
theorem etale_torus_point_exists_of_key : LateralTheory.DivDb.TorusPt := by
  apply LateralTheory.DivDb.TorusPtPf.TorusPt_of <;> first | exact etale_exponent_vanishing_of_key | exact etale_special_point_exists_of_key
theorem etale_degree_polynomial_bound : LateralTheory.DivDb.DegPoly := by
  apply LateralTheory.DivDb.DegPoly₂.DegPoly_of
theorem etale_tangent_degree_bound_of_key : LateralTheory.DivDb.TanDeg := by
  apply LateralTheory.DivDb.TangentDegree.TanDeg_of <;> first | exact etale_exponent_vanishing_of_key | exact etale_degree_polynomial_bound
theorem etale_cycle_count_eigenvalues_of_key : LateralTheory.DivDb.CycleCount := by
  apply LateralTheory.DivDb.CycleCount₂.CycleCount_of
theorem etale_divisibility_key_criterion_of_components : LateralTheory.DivDb.Key := by
  apply LateralTheory.DivDb.KeyPf.Key_of <;> first | exact etale_idempotent_conjugacy_of_key | exact etale_matrix_units_system_of_key | exact etale_unit_factorization_of_key | exact etale_tangent_index_divides_of_key | exact etale_unipotent_part_trivial_of_key | exact etale_zariski_closure_mul_closed_of_key | exact etale_generic_spectrum_of_key | exact etale_torus_point_exists_of_key | exact etale_tangent_degree_bound_of_key | exact etale_cycle_count_eigenvalues_of_key
theorem intersectionNumber_baseChange : LateralTheory.DivDb.Key := etale_divisibility_key_criterion_of_components
end LateralTheory.Fin.Key
end
end
