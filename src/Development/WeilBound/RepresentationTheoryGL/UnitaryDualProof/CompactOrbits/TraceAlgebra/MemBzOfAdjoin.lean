module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.IsoOfTrace
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.RestrictionHomomorphisms.ResHomApply
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.CoefficientTraces.TraceAllHolds

section

@[expose] public section

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.T.Alg.Trall

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Alg

variable (k : Type) [Field k] [CharZero k]

theorem sum_coeff_trace {n : ℕ} (x z : Matrix (Fin n) (Fin n) k) (p : k[X]) (hp : aeval x p = 0) (m : ℕ) :
    ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * trace (z * x ^ (m + i)) = 0 := by
  have h : trace (z * x ^ m * aeval x p) = 0 := by rw [hp, mul_zero, trace_zero]
  rw [aeval_eq_sum_range, Finset.mul_sum, trace_sum] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, trace_smul, smul_eq_mul, mul_assoc, ← pow_add]

theorem trace_all_holds : TrAll k := by
  intro n Z x x' h z hz j
  have key : ∀ w : Z, ∀ j, j < 2 * n + 1 → trace ((w : Matrix (Fin n) (Fin n) k) * x ^ j) = trace ((w : Matrix (Fin n) (Fin n) k) * x' ^ j) := by
    intro w j hj
    have hw : (w : Matrix (Fin n) (Fin n) k) = ∑ i, (Module.finBasis k Z).repr w i • ((Module.finBasis k Z) i : Matrix (Fin n) (Fin n) k) := by
      nth_rewrite 1 [← (Module.finBasis k Z).sum_repr w]
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    rw [hw, Finset.sum_mul, Finset.sum_mul, trace_sum, trace_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, trace_smul, trace_smul]
    congr 1
    exact congrFun h (⟨j, hj⟩, i)
  set q := x.charpoly * x'.charpoly with hqdef
  have hqm : q.Monic := x.charpoly_monic.mul x'.charpoly_monic
  have hdeg : q.natDegree = 2 * n := by
    rw [hqdef, x.charpoly_monic.natDegree_mul x'.charpoly_monic, charpoly_natDegree_eq_dim, charpoly_natDegree_eq_dim, Fintype.card_fin]
    ring
  have hx0 : aeval x q = 0 := by rw [hqdef, map_mul, aeval_self_charpoly, zero_mul]
  have hx'0 : aeval x' q = 0 := by rw [hqdef, map_mul, aeval_self_charpoly, mul_zero]
  have hrec : ∀ m, ∑ i ∈ Finset.range (2 * n + 1), q.coeff i * (trace (z * x ^ (m + i)) - trace (z * x' ^ (m + i))) = 0 := by
    intro m
    have h1 := sum_coeff_trace k x z q hx0 m
    have h2 := sum_coeff_trace k x' z q hx'0 m
    rw [hdeg] at h1 h2
    simp only [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_zero]
  have hlead : q.coeff (2 * n) = 1 := by
    rw [← hdeg]
    exact hqm
  suffices hall : ∀ j, trace (z * x ^ j) - trace (z * x' ^ j) = 0 from sub_eq_zero.mp (hall j)
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < 2 * n + 1
    · exact sub_eq_zero.mpr (key ⟨z, hz⟩ j hj)
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 * n := ⟨j - 2 * n, by omega⟩
      have hm := hrec m
      rw [Finset.sum_range_succ, hlead, one_mul] at hm
      have hs : ∑ i ∈ Finset.range (2 * n), q.coeff i * (trace (z * x ^ (m + i)) - trace (z * x' ^ (m + i))) = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [Finset.mem_range] at hi
          rw [ih (m + i) (by omega), mul_zero]
      rw [hs, zero_add] at hm
      exact hm

end PositivityTheory.RgUd.T.Alg.Trall
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.LinearConjugation.ToLinAlgEquivEq

section

@[expose] public section

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.T.Alg.Conj2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Alg

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

def SS (a : Matrix (Fin n) (Fin n) k) : Prop := Module.End.IsSemisimple (Matrix.toLin' a)

theorem toLinAlgEquiv'_eq (a : Matrix (Fin n) (Fin n) k) : Matrix.toLinAlgEquiv' a = Matrix.toLin' a := rfl

theorem ss_add {a b : Matrix (Fin n) (Fin n) k} (h : Commute a b) (ha : SS a) (hb : SS b) : SS (a + b) := by
  unfold SS
  rw [← toLinAlgEquiv'_eq, map_add (f := _)]
  exact Module.End.IsSemisimple.add_of_commute (h.map Matrix.toLinAlgEquiv') ha hb

theorem ss_mul {a b : Matrix (Fin n) (Fin n) k} (h : Commute a b) (ha : SS a) (hb : SS b) : SS (a * b) := by
  unfold SS
  rw [← toLinAlgEquiv'_eq, map_mul]
  exact Module.End.IsSemisimple.mul_of_commute (h.map Matrix.toLinAlgEquiv') ha hb

theorem ss_algebraMap (c : k) : SS (algebraMap k (Matrix (Fin n) (Fin n) k) c) := by
  unfold SS
  rw [← toLinAlgEquiv'_eq, AlgEquiv.commutes]
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := X - C c)
    (Polynomial.irreducible_X_sub_C c).squarefree ?_
  simp

theorem ss_of_mem {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {z : Matrix (Fin n) (Fin n) k}
    (hz : z ∈ Z) : SS z := by
  obtain ⟨nn, hnn, ss, -, hnil, hsss, hsum⟩ := Module.End.exists_isNilpotent_isSemisimple (K := k) (f := Matrix.toLin' z)
  have hmap : Algebra.adjoin k {Matrix.toLin' z} =
      (Algebra.adjoin k {z}).map (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom := by
    rw [← Algebra.adjoin_image, Set.image_singleton]
    rfl
  rw [hmap] at hnn
  obtain ⟨m, hm, hmn⟩ := Subalgebra.mem_map.1 hnn
  have hmZ : m ∈ Z := Algebra.adjoin_le (Set.singleton_subset_iff.2 hz) hm
  have hmnil : IsNilpotent m := by
    have : IsNilpotent ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).symm nn) := hnil.map _
    rw [← hmn] at this
    simpa using this
  have hm0 : m = 0 := by
    have h1 : IsNilpotent (⟨m, hmZ⟩ : Z) := by
      obtain ⟨e, he⟩ := hmnil
      exact ⟨e, Subtype.ext (by simpa using he)⟩
    have := hZ.2.eq_zero _ h1
    simpa using congrArg Subtype.val this
  have hnn0 : nn = 0 := by rw [← hmn, hm0]; simp
  unfold SS
  rw [hsum, hnn0, zero_add]
  exact hsss

theorem conj_of (hiso : IsoOfTrace k) : Conj k := by
  intro n Z hZ s s' hs hs' hss hss' htr
  classical
  set S : Set (Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k) :=
    (fun z => (z, z)) '' (Z : Set (Matrix (Fin n) (Fin n) k)) ∪ {(s, s')} with hSdef
  have hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro a (⟨z, hz, rfl⟩ | ha) b (⟨w, hw, rfl⟩ | hb)
    · simp [hZ.1 z hz w hw]
    · rw [Set.mem_singleton_iff] at hb; subst hb
      simp [hs z hz, hs' z hz]
    · rw [Set.mem_singleton_iff] at ha; subst ha
      simp [hs w hw, hs' w hw]
    · rw [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
  set R := Algebra.adjoin k S with hRdef

  have hRc : ∀ x ∈ R, ∀ y ∈ R, Commute x y := fun x hx y hy =>
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb =>
      (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun a ha => hcomm b hb a ha).symm

  letI : CommRing R := { (inferInstance : Ring R) with
    mul_comm := fun x y => Subtype.ext (hRc x x.2 y y.2).eq }

  have hRss : ∀ x ∈ R, SS x.1 ∧ SS x.2 := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨z, hz, rfl⟩ | hx
      · exact ⟨ss_of_mem hZ hz, ss_of_mem hZ hz⟩
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact ⟨hss, hss'⟩
    | algebraMap c => exact ⟨ss_algebraMap c, ss_algebraMap c⟩
    | add x y hx hy ihx ihy =>
      have h := hRc x hx y hy
      exact ⟨ss_add (h.map (RingHom.fst _ _)) ihx.1 ihy.1, ss_add (h.map (RingHom.snd _ _)) ihx.2 ihy.2⟩
    | mul x y hx hy ihx ihy =>
      have h := hRc x hx y hy
      exact ⟨ss_mul (h.map (RingHom.fst _ _)) ihx.1 ihy.1, ss_mul (h.map (RingHom.snd _ _)) ihx.2 ihy.2⟩

  let f : Z →+* Matrix (Fin n) (Fin n) k := Z.val.toRingHom
  have hform : ∀ x ∈ R, ∃ P : Z[X], x = (P.eval₂ f s, P.eval₂ f s') := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨z, hz, rfl⟩ | hx
      · exact ⟨C ⟨z, hz⟩, by simp [f]⟩
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact ⟨X, by simp⟩
    | algebraMap c =>
      refine ⟨C (algebraMap k Z c), ?_⟩
      simp [f, Prod.algebraMap_apply]
    | add x y hx hy ihx ihy =>
      obtain ⟨P, rfl⟩ := ihx
      obtain ⟨Q, rfl⟩ := ihy
      exact ⟨P + Q, by simp [eval₂_add]⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨P, rfl⟩ := ihx
      obtain ⟨Q, rfl⟩ := ihy
      refine ⟨P * Q, ?_⟩
      rw [eval₂_mul_noncomm _ _ fun j => ?_, eval₂_mul_noncomm _ _ fun j => ?_]
      · rfl
      · exact hs' (f (Q.coeff j)) (Q.coeff j).2
      · exact hs (f (Q.coeff j)) (Q.coeff j).2
  have htrP : ∀ P : Z[X], trace (P.eval₂ f s) = trace (P.eval₂ f s') := by
    intro P
    rw [eval₂_eq_sum, eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def, trace_sum, trace_sum]
    exact Finset.sum_congr rfl fun e _ => htr _ (P.coeff e).2 e

  haveI : IsReduced R := ⟨fun x hx => by
    have h1 : IsNilpotent (x : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k) := hx.map R.val
    have hs1 := hRss x x.2
    have e1 : (x : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k).1 = 0 := by
      have hn1 := (h1.map (RingHom.fst (Matrix (Fin n) (Fin n) k) (Matrix (Fin n) (Fin n) k))).map
        (Matrix.toLinAlgEquiv' (R := k) (n := Fin n))
      have := Module.End.eq_zero_of_isNilpotent_isSemisimple hn1 (by exact hs1.1)
      exact (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective (this.trans (map_zero _).symm)
    have e2 : (x : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k).2 = 0 := by
      have hn2 := (h1.map (RingHom.snd (Matrix (Fin n) (Fin n) k) (Matrix (Fin n) (Fin n) k))).map
        (Matrix.toLinAlgEquiv' (R := k) (n := Fin n))
      have := Module.End.eq_zero_of_isNilpotent_isSemisimple hn2 (by exact hs1.2)
      exact (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective (this.trans (map_zero _).symm)
    exact Subtype.ext (Prod.ext e1 e2)⟩
  let ρ : R →ₐ[k] Module.End k (Fin n → k) :=
    (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp ((AlgHom.fst k _ _).comp R.val)
  let ρ' : R →ₐ[k] Module.End k (Fin n → k) :=
    (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp ((AlgHom.snd k _ _).comp R.val)
  have hρ : ∀ r : R, ρ r = Matrix.toLin' (r : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k).1 :=
    fun r => rfl
  have hρ' : ∀ r : R, ρ' r = Matrix.toLin' (r : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k).2 :=
    fun r => rfl
  have htrace : ∀ r, LinearMap.trace k _ (ρ r) = LinearMap.trace k _ (ρ' r) := by
    intro r
    rw [hρ, hρ', Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq]
    obtain ⟨P, hP⟩ := hform r r.2
    rw [hP]
    exact htrP P
  obtain ⟨φ, hφ⟩ := hiso n R ρ ρ' htrace

  let A : Matrix (Fin n) (Fin n) k := LinearMap.toMatrix' (φ : (Fin n → k) →ₗ[k] (Fin n → k))
  let B : Matrix (Fin n) (Fin n) k := LinearMap.toMatrix' (φ.symm : (Fin n → k) →ₗ[k] (Fin n → k))
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext v : 1
    simp
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext v : 1
    simp
  let g : GL (Fin n) k := ⟨A, B, hAB, hBA⟩

  have hint : ∀ x ∈ R, A * x.1 = x.2 * A := by
    intro x hx
    have hc : (φ : (Fin n → k) →ₗ[k] (Fin n → k)).comp (Matrix.toLin' x.1) =
        (Matrix.toLin' x.2).comp (φ : (Fin n → k) →ₗ[k] (Fin n → k)) := by
      refine LinearMap.ext fun v => ?_
      have := hφ ⟨x, hx⟩ v
      rw [hρ, hρ'] at this
      simpa using this
    have := congrArg LinearMap.toMatrix' hc
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_toLin'] at this
    exact this
  refine ⟨g, fun a ha => ?_, ?_⟩
  · have := hint (a, a) (Algebra.subset_adjoin (Or.inl ⟨a, ha, rfl⟩))
    exact this.symm
  · have h1 := hint (s, s') (Algebra.subset_adjoin (Or.inr rfl))
    show A * s * B = s'
    rw [h1, Matrix.mul_assoc, hAB, Matrix.mul_one]

end PositivityTheory.RgUd.T.Alg.Conj2
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.NilpotentTraces.TrNil

section

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Alg.Jcnil

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Alg

variable (k : Type) [Field k] [CharZero k]

theorem jc : JC k := by
  intro n x
  obtain ⟨N, -, S, hS, hN, hSs, hx⟩ := Module.End.exists_isNilpotent_isSemisimple (K := k) (f := Matrix.toLin' x)
  have hsx : Matrix.toLinAlgEquiv' (Matrix.toLinAlgEquiv'.symm S) = S := AlgEquiv.apply_symm_apply _ _
  refine ⟨Matrix.toLinAlgEquiv'.symm S, ?_, ?_, ?_⟩
  · have hmap := AlgHom.map_adjoin (Matrix.toLinAlgEquiv'.symm : _ ≃ₐ[k] Matrix (Fin n) (Fin n) k).toAlgHom {Matrix.toLin' x}
    rw [Set.image_singleton] at hmap
    have hx' : (Matrix.toLinAlgEquiv'.symm : _ ≃ₐ[k] Matrix (Fin n) (Fin n) k).toAlgHom (Matrix.toLin' x) = x :=
      Matrix.toLinAlgEquiv'.symm_apply_apply x
    rw [hx'] at hmap
    rw [← hmap]
    exact Subalgebra.mem_map.mpr ⟨S, hS, rfl⟩
  · have : Matrix.toLin' (Matrix.toLinAlgEquiv'.symm S) = S := hsx
    rw [this]
    exact hSs
  · have hdiff : x - Matrix.toLinAlgEquiv'.symm S = Matrix.toLinAlgEquiv'.symm N := by
      apply Matrix.toLinAlgEquiv'.injective
      rw [map_sub, hsx, AlgEquiv.apply_symm_apply]
      have : Matrix.toLinAlgEquiv' x = Matrix.toLin' x := rfl
      rw [this, hx]
      abel
    rw [hdiff]
    exact hN.map _

theorem trNil : TrNil k := by
  intro n x s z hs hn hz j
  have hxs : Commute x s := Algebra.commute_of_mem_adjoin_self hs
  have hzs : Commute z s := Algebra.commute_of_mem_adjoin_singleton_of_commute hs hz
  have hdx : Commute (x - s) x := (Commute.refl x).sub_left hxs.symm
  have hds : Commute (x - s) s := hxs.sub_left (Commute.refl s)
  have hg := hxs.mul_geom_sum₂ j
  have hc : Commute (x - s) (∑ i ∈ Finset.range j, x ^ i * s ^ (j - 1 - i)) :=
    Commute.sum_right _ _ _ fun i _ => (hdx.pow_right i).mul_right (hds.pow_right _)
  have hzd : Commute z (x - s) := hz.sub_right hzs
  have hnil : IsNilpotent (z * x ^ j - z * s ^ j) := by
    rw [← mul_sub, ← hg, ← mul_assoc, hzd.eq, mul_assoc]
    exact Commute.isNilpotent_mul_right (hzd.symm.mul_right hc) hn
  have ht := Matrix.isNilpotent_trace_of_isNilpotent hnil
  rw [Matrix.trace_sub] at ht
  exact sub_eq_zero.mp ht.eq_zero

end PositivityTheory.RgUd.T.Alg.Jcnil
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.MemBzOfAdjoin

section

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Alg

open PositivityTheory.RgUd.T

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]

theorem mem_Bz_of_adjoin' {n : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x s : Matrix (Fin n) (Fin n) k}
    (hx : x ∈ Bz Z) (hs : s ∈ Algebra.adjoin k {x}) : s ∈ Bz Z := by
  intro a ha
  exact (Algebra.commute_of_mem_adjoin_singleton_of_commute hs (hx a ha)).eq

theorem dich : Dich (k := k) := by
  classical
  intro n Z hZ y
  by_cases hne : ∃ x₀ ∈ Bz Z, pZ Z x₀ = y
  · obtain ⟨x₀, hx₀, hy₀⟩ := hne
    obtain ⟨s₀, hs₀, hss₀, hn₀⟩ := Jcnil.jc k n x₀
    have hs₀B : s₀ ∈ Bz Z := mem_Bz_of_adjoin' k hx₀ hs₀

    have key : ∀ x ∈ Bz Z, pZ Z x = y → ∃ g ∈ Gz Z, ∃ s, s ∈ Algebra.adjoin k {x} ∧ IsNilpotent (x - s) ∧
        g.val * s * g⁻¹.val = s₀ := by
      intro x hx hy
      obtain ⟨s, hs, hss, hn⟩ := Jcnil.jc k n x
      have hsB : s ∈ Bz Z := mem_Bz_of_adjoin' k hx hs
      have htr : ∀ z ∈ Z, ∀ j : ℕ, trace (z * s ^ j) = trace (z * s₀ ^ j) := by
        intro z hz j
        rw [← Jcnil.trNil k n x s z hs hn (hx z hz) j, ← Jcnil.trNil k n x₀ s₀ z hs₀ hn₀ (hx₀ z hz) j]
        exact Trall.trace_all_holds k n Z x x₀ (hy.trans hy₀.symm) z hz j
      obtain ⟨g, hg, hgs⟩ := Conj2.conj_of Iso2.isoOfTrace n Z hZ s s₀ hsB hs₀B hss hss₀ htr
      exact ⟨g, hg, s, hs, hn, hgs⟩
    by_cases hZs : s₀ ∈ Z
    · refine Or.inl ⟨s₀, hZs, fun x hx hy => ?_⟩
      obtain ⟨g, hg, s, hs, hn, hgs⟩ := key x hx hy
      have hgc : g.val * s₀ = s₀ * g.val := (hg s₀ hZs).symm
      have : s = s₀ := by
        have h1 : g.val * s = s₀ * g.val := by
          rw [← hgs, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.mul_one]
        have h2 : g.val * s = g.val * s₀ := h1.trans hgc.symm
        have := congrArg (fun m => g⁻¹.val * m) h2
        simpa [← Matrix.mul_assoc, ← Units.val_mul] using this
      rw [← this]
      exact hn
    · refine Or.inr ⟨s₀, hs₀B, hZs, hss₀, fun x hx hy => ?_⟩
      obtain ⟨g, hg, s, hs, hn, hgs⟩ := key x hx hy
      refine ⟨g, hg, ?_, ?_⟩
      · have e : g.val * x * g⁻¹.val - s₀ = g.val * (x - s) * g⁻¹.val := by
          rw [← hgs, Matrix.mul_sub, Matrix.sub_mul]
        rw [e]
        obtain ⟨m, hm⟩ := hn
        refine ⟨m, ?_⟩
        have hconj : ∀ j : ℕ, (g.val * (x - s) * g⁻¹.val) ^ j = g.val * (x - s) ^ j * g⁻¹.val := by
          intro j
          induction j with
          | zero => simp [← Units.val_mul]
          | succ j ih =>
            rw [pow_succ, ih, pow_succ]
            simp only [Matrix.mul_assoc]
            congr 2
            rw [← Matrix.mul_assoc g⁻¹.val, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        rw [hconj, hm]
        simp
      · have hcs : Commute x s := (Algebra.commute_of_mem_adjoin_singleton_of_commute hs (Commute.refl x)).symm.symm
        rw [← hgs]
        have e1 : g.val * x * g⁻¹.val * (g.val * s * g⁻¹.val) = g.val * (x * s) * g⁻¹.val := by
          simp only [Matrix.mul_assoc]
          congr 2
          rw [← Matrix.mul_assoc g⁻¹.val, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        have e2 : g.val * s * g⁻¹.val * (g.val * x * g⁻¹.val) = g.val * (s * x) * g⁻¹.val := by
          simp only [Matrix.mul_assoc]
          congr 2
          rw [← Matrix.mul_assoc g⁻¹.val, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        show _ * _ = _ * _
        rw [e1, e2, hcs.eq]
  · refine Or.inl ⟨0, Z.zero_mem, fun x hx hy => absurd ⟨x, hx, hy⟩ hne⟩

end PositivityTheory.RgUd.T.Alg
end
end
end
