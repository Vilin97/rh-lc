module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinLocalOrderTensorPadicMatrixAlmostAllStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralTensorPointsSharpStableRing
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntVZero
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulMemSpan

section

@[expose] public section

namespace GlobalTheory.MultiplierOrders

theorem exists_nsmul_mem_span {C : Type} [AddCommGroup C] [Module ℚ C] (S : Set C) (x : C)
    (hx : x ∈ Submodule.span ℚ S) : ∃ m : ℕ, 0 < m ∧ m • x ∈ Submodule.span ℤ S := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by rw [one_smul]; exact Submodule.subset_span hy⟩
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm, hy⟩ := hy
    obtain ⟨n, hn, hz⟩ := hz
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]
      exact nsmul_mem hy n
    · rw [mul_smul]
      exact nsmul_mem hz m
  | smul q y _ hy =>
    obtain ⟨m, hm, hy⟩ := hy
    refine ⟨m * q.den, Nat.mul_pos hm q.den_pos, ?_⟩
    have h : (m * q.den) • q • y = q.num • m • y := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ m, ← Int.cast_smul_eq_zsmul ℚ,
        smul_smul, smul_smul]
      congr 1
      push_cast
      rw [mul_assoc, Rat.den_mul_eq_num, mul_comm]
    rw [h]
    exact Submodule.smul_mem _ _ hy

def multipliers {C : Type} [Ring C] (L : Submodule ℤ C) : Subring C where
  carrier := {x | ∀ y ∈ L, x * y ∈ L}
  mul_mem' := fun {a b} ha hb y hy => by
    rw [mul_assoc]; exact ha _ (hb y hy)
  one_mem' := fun y hy => by rw [one_mul]; exact hy
  add_mem' := fun {a b} ha hb y hy => by
    rw [add_mul]; exact L.add_mem (ha y hy) (hb y hy)
  zero_mem' := fun y _ => by rw [zero_mul]; exact L.zero_mem
  neg_mem' := fun {a} ha y hy => by
    rw [neg_mul]; exact L.neg_mem (ha y hy)

theorem exists_order (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] :
    ∃ OB : Subring C, Module.Finite ℤ OB ∧ ∀ b : C, ∃ m : ℕ, 0 < m ∧ (m : C) * b ∈ OB := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℚ) (M := C)
  have key : ∀ x : C, ∃ m : ℕ, 0 < m ∧ m • x ∈ Submodule.span ℤ (S : Set C) := fun x =>
    exists_nsmul_mem_span _ x (by rw [hS]; exact Submodule.mem_top)
  set L : Submodule ℤ C := Submodule.span ℤ (S : Set C) with hL
  haveI : Module.Finite ℤ L := Module.Finite.iff_fg.mpr ⟨S, rfl⟩
  refine ⟨multipliers L, ?_, ?_⟩
  · obtain ⟨m, hm, h1⟩ := key 1
    let f : multipliers L →+ L :=
      { toFun := fun x => ⟨x.1 * (m • (1 : C)), x.2 _ h1⟩
        map_zero' := Subtype.ext (by simp)
        map_add' := fun a b => Subtype.ext (by simp [add_mul]) }
    refine Module.Finite.of_injective f.toIntLinearMap ?_
    intro a b hab
    have h : a.1 * (m • (1 : C)) = b.1 * (m • (1 : C)) := congrArg Subtype.val hab
    rw [mul_smul_comm, mul_smul_comm, mul_one, mul_one, ← Nat.cast_smul_eq_nsmul ℚ,
      ← Nat.cast_smul_eq_nsmul ℚ] at h
    have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    exact Subtype.ext (smul_right_injective C hm' h)
  · intro b
    choose n hn hmem using fun s : C => key (b * s)
    refine ⟨∏ s ∈ S, n s, Finset.prod_pos fun s _ => hn s, ?_⟩
    intro y hy
    induction hy using Submodule.span_induction with
    | mem s hs =>
      have hs' : s ∈ S := hs
      rw [mul_assoc, ← nsmul_eq_mul, ← Finset.prod_erase_mul S n hs', mul_smul]
      exact nsmul_mem (hmem s) _
    | zero => rw [mul_zero]; exact L.zero_mem
    | add y z _ _ hy hz => rw [mul_add]; exact L.add_mem hy hz
    | smul k y _ hy => rw [mul_smul_comm]; exact L.smul_mem k hy

end GlobalTheory.MultiplierOrders
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralMatrixUnitsAtPlaces

section

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.MatrixUnits₂

theorem exists_order (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] :
    ∃ OB : Subring C, Module.Finite ℤ OB ∧ ∀ b : C, ∃ m : ℕ, 0 < m ∧ (m : C) * b ∈ OB := by
  first
  | exact @_root_.GlobalTheory.MultiplierOrders.exists_order
  | exact _root_.GlobalTheory.MultiplierOrders.exists_order
  | (apply _root_.GlobalTheory.MultiplierOrders.exists_order <;> assumption)
  | (intros; apply _root_.GlobalTheory.MultiplierOrders.exists_order <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MultiplierOrders.exists_order <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MultiplierOrders.exists_order ..)

theorem isIntV_order_eventually (p : ℕ) [Fact p.Prime] (G : HTGroup p) (OB : Subring G.C)
    (hfin : Module.Finite ℤ OB) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ x ∈ OB, IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] x) := by
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := OB)
  have H := Filter.eventually_all.2 fun i : Fin k => Filter.eventually_all.2 fun m =>
    ratCast_mem_intV_eventually p ((Module.finBasis ℚ G.C).repr (g i : G.C) m)
  refine H.mono fun v hv x hx => ?_
  have hx' : (⟨x, hx⟩ : OB) ∈ Submodule.span ℤ (Set.range g) := by rw [hg]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx'
  have e : (1 : Qv v) ⊗ₜ[ℚ] x = ∑ i, ((c i : ℤ) : Qv v) ⊗ₜ[ℚ] (g i : G.C) := by
    have hx2 : x = ∑ i, (c i : ℤ) • (g i : G.C) := by
      have := congrArg Subtype.val hc
      simpa using this.symm
    rw [hx2, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℚ, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    simp
  rw [e]
  exact isIntV_of_eq_sum G v _ _ _ (fun i _ => intCast_mem _ _) (fun i _ m => hv i m)

end GlobalTheory.OrbFinAf.MatrixUnits₂

namespace GlobalTheory.OrbFinAf.MatrixUnits₂

open Rat.HeightOneSpectrum

def theta (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) [Fact (primesEquiv v.1 : ℕ).Prime] :
    ℚ_[(primesEquiv v.1 : ℕ)] ⊗[ℚ] G.C ≃ₐ[ℚ] Qv v ⊗[ℚ] G.C :=
  Algebra.TensorProduct.congr (adicCompletion.padicEquiv v.1).symm.toAlgEquiv AlgEquiv.refl

theorem theta_tmul (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) [Fact (primesEquiv v.1 : ℕ).Prime]
    (r : ℚ_[(primesEquiv v.1 : ℕ)]) (c : G.C) :
    theta p G v (r ⊗ₜ c) = (adicCompletion.padicEquiv v.1).symm r ⊗ₜ c := rfl

theorem padicEquiv_symm_coe_mem (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) [Fact (primesEquiv v.1 : ℕ).Prime]
    (r : ℤ_[(primesEquiv v.1 : ℕ)]) :
    (adicCompletion.padicEquiv v.1).symm (r : ℚ_[(primesEquiv v.1 : ℕ)]) ∈ v.1.adicCompletionIntegers ℚ := by
  obtain ⟨x, hx, hxr⟩ := (adicCompletion.padicEquiv_bijOn v.1).surjOn
    (show (r : ℚ_[(primesEquiv v.1 : ℕ)]) ∈ PadicInt.subring _ from r.2)
  rw [← hxr, ContinuousAlgEquiv.symm_apply_apply]
  exact hx

end GlobalTheory.OrbFinAf.MatrixUnits₂

namespace GlobalTheory.OrbFinAf.MatrixUnits₂

open Rat.HeightOneSpectrum GlobalTheory.LKInvGood

theorem isIntV_theta_locOrder (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p)
    [Fact (primesEquiv v.1 : ℕ).Prime] (OB : Subring G.C)
    (hO : ∀ x ∈ OB, IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] x)) (h1 : IsIntV G v 1)
    (hmul : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z))
    (y : ℚ_[(primesEquiv v.1 : ℕ)] ⊗[ℚ] G.C) (hy : y ∈ locOrder (primesEquiv v.1 : ℕ) OB) :
    IsIntV G v (theta p G v y) := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    rw [theta_tmul, map_one]
    exact hO c hc
  | algebraMap r =>
    rw [Algebra.TensorProduct.algebraMap_apply, theta_tmul]
    intro k
    rw [basV_repr_tmul]
    have h1k := h1 k
    rw [Algebra.TensorProduct.one_def, basV_repr_tmul, one_mul] at h1k
    exact mul_mem (padicEquiv_symm_coe_mem p G v r) h1k
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact isIntV_add' G v hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact hmul _ _ hx hy

theorem finite_dvd (p : ℕ) (N : ℕ) (hN : 0 < N) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ¬ (primesEquiv v.1 : ℕ) ∣ N := by
  have hfin : {v : AwayP p | (primesEquiv v.1 : ℕ) ∣ N}.Finite := by
    have hinj : Function.Injective fun v : AwayP p => (primesEquiv v.1 : ℕ) :=
      fun a b h => Subtype.ext (primesEquiv.injective (Subtype.ext h))
    refine Set.Finite.of_finite_image ?_ hinj.injOn
    refine (Set.finite_le_nat N).subset ?_
    rintro _ ⟨v, hv, rfl⟩
    exact Nat.le_of_dvd hN hv
  exact hfin.eventually_cofinite_notMem

theorem matrixUnits_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∃ E : Fin G.n → Fin G.n → Qv v ⊗[ℚ] G.C,
      (∀ i j k l, E i j * E k l = if j = k then E i l else 0) ∧ ∑ i, E i i = 1 ∧
      ∀ i j, IsIntV G v (E i j) := by
  intro p _ G
  obtain ⟨OB, hfin, hspan⟩ := exists_order G.C
  obtain ⟨N, hN, hmat⟩ := GlobalTheory.T.adjoinLocalOrderTensorPadic_matrix_almost_all G.F G.C G.n G.rankC OB hfin hspan
  filter_upwards [finite_dvd p N hN, isIntV_order_eventually p G OB hfin, intV_order_eventually p G]
    with v hv hO hord
  haveI : Fact (primesEquiv v.1 : ℕ).Prime := ⟨(primesEquiv v.1).2⟩
  obtain ⟨ψ, -⟩ := hmat (primesEquiv v.1 : ℕ) hv
  let E : Fin G.n → Fin G.n → Qv v ⊗[ℚ] G.C := fun i j =>
    theta p G v ((ψ.symm (Matrix.single i j 1) : locOrder (primesEquiv v.1 : ℕ) OB) :
      ℚ_[(primesEquiv v.1 : ℕ)] ⊗[ℚ] G.C)
  refine ⟨E, fun i j k l => ?_, ?_, fun i j =>
    isIntV_theta_locOrder p G v OB hO hord.1 hord.2.1 _ (ψ.symm _).2⟩
  · simp only [E]
    rw [← map_mul, ← Subalgebra.coe_mul, ← map_mul]
    split_ifs with hjk
    · subst hjk
      rw [Matrix.single_mul_single_same, mul_one]
    · rw [Matrix.single_mul_single_of_ne (h := hjk), map_zero, ZeroMemClass.coe_zero, map_zero]
  · have hs : ∑ i, (Matrix.single i i (1 : cenOrder (primesEquiv v.1 : ℕ) G.F) :
        Matrix (Fin G.n) (Fin G.n) (cenOrder (primesEquiv v.1 : ℕ) G.F)) = 1 := by
      ext a b
      rw [Matrix.sum_apply, Matrix.one_apply, Finset.sum_eq_single a]
      · by_cases h : a = b
        · subst h; simp [Matrix.single_apply]
        · simp [Matrix.single_apply, h]
      · intro c _ hc; simp [Matrix.single_apply, hc]
      · simp
    simp only [E]

    rw [← map_sum (theta p G v), ← AddSubmonoidClass.coe_finsetSum, ← map_sum ψ.symm, hs, map_one,
    OneMemClass.coe_one, map_one]

end GlobalTheory.OrbFinAf.MatrixUnits₂
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralMatrixUnitsAtPlacesStatement

section

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eventually_integral_matrix_units_at_places : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∃ E : Fin G.n → Fin G.n → Qv v ⊗[ℚ] G.C, (∀ i j k l, E i j * E k l = if j = k then E i l else 0) ∧ ∑ i, E i i = 1 ∧ ∀ i j, IsIntV G v (E i j) := by
  first | (exact @GlobalTheory.OrbFinAf.MatrixUnits₂.matrixUnits_eventually) | (exact GlobalTheory.OrbFinAf.MatrixUnits₂.matrixUnits_eventually) | (intros; apply GlobalTheory.OrbFinAf.MatrixUnits₂.matrixUnits_eventually  <;> assumption)
end
end
