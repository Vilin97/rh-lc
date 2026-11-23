module

public import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.GenSectA
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Formalism.LocalToGlobal.ProjectiveLattices.GenSect
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

-- Source module: Formalism.LocalToGlobal.ProjectiveLattices.GenSectT

section

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.GenSect

open MvPolynomial
open scoped TensorProduct

variable (K Ω Kl K' : Type) [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
  [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K']

abbrev TZ : Type := K' ⊗[Kl] (Kl ⊗[K] Ω)

variable {K Ω Kl K'} {D m : ℕ}


variable (K Kl) in
def tsec (t : Fin (D + 1) × Fin m → K') (v : Fin m → Ω) (i : Fin (D + 1)) : TZ K Ω Kl K' :=
  ∑ k, t (i, k) ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] v k)


variable (K Kl) in
def tJ (t : Fin (D + 1) × Fin m → K') (v : Fin m → Ω) : Ideal (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0)) :=
  Ideal.span (Set.range fun i : Fin D =>
    algebraMap (TZ K Ω Kl K') (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0)) (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v i.succ) *
      IsLocalization.Away.invSelf (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0))





theorem s1T [CharZero K] (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = D)
    (v : Fin m → Ω) (k₀ : Fin m) (hv₀ : v k₀ ≠ 0)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun k => v k / v k₀)) = D)
    (t : Fin (D + 1) × Fin m → K') (ht : AlgebraicIndependent K t) :
    FiniteDimensional K' (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ⧸ tJ (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v) ∧
      IsReduced (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ⧸ tJ (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v) := by
  classical

  have hφ : Function.Injective (MvPolynomial.aeval t : KT K D m →ₐ[K] K').toRingHom := ht
  letI : Algebra (KTf K D m) K' := (IsFractionRing.lift (A := KT K D m) (K := KTf K D m) hφ).toAlgebra
  obtain ⟨-, hB⟩ := s1 (K := K) hfg htr v k₀ hv₀ hbig
  obtain ⟨hBfin, hBred⟩ := hB K'
  let ι : TZ K Ω Kl K' →+* (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ⧸ tJ (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v) :=
    algebraMap (TZ K Ω Kl K') (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ⧸ tJ (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v)
  have hιK : ∀ z : K', ι (algebraMap K' (TZ K Ω Kl K') z) =
      algebraMap K' (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ⧸ tJ (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v) z := fun z =>
    (IsScalarTower.algebraMap_apply K' (TZ K Ω Kl K') _ z).symm

  let fΩ : Ω →+* TZ K Ω Kl K' :=
    (Algebra.TensorProduct.includeRight (R := Kl) (A := K')).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := K) (A := Kl)).toRingHom
  let e0 : ΩT Ω D m →+* TZ K Ω Kl K' :=
    MvPolynomial.eval₂Hom fΩ (fun p => t p ⊗ₜ[Kl] (1 : Kl ⊗[K] Ω))
  have hKΩ : ∀ a : K, fΩ (algebraMap K Ω a) = algebraMap K' (TZ K Ω Kl K') (algebraMap K K' a) := by
    intro a
    show (1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] algebraMap K Ω a) = _
    rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply]
    have h1 : (algebraMap K Kl a ⊗ₜ[K] (1 : Ω) : Kl ⊗[K] Ω) = algebraMap K Kl a • (1 : Kl ⊗[K] Ω) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
      ← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.one_def]
    rfl
  have he0kt : ∀ q : KT K D m, e0 (ktToΩ K Ω D m q) =
      algebraMap K' (TZ K Ω Kl K') (MvPolynomial.aeval t q) := by
    intro q
    have : e0.comp (ktToΩ K Ω D m) =
        (algebraMap K' (TZ K Ω Kl K')).comp (MvPolynomial.aeval t : KT K D m →ₐ[K] K').toRingHom := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_)
      · simp only [RingHom.comp_apply, ktToΩ, MvPolynomial.map_C, e0, MvPolynomial.eval₂Hom_C,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
        exact hKΩ a
      · simp only [RingHom.comp_apply, ktToΩ, MvPolynomial.map_X, e0, MvPolynomial.eval₂Hom_X',
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
        rfl
    exact congrArg (fun f => f q) this
  have he0sec : ∀ i : Fin D, e0 (sec v i) = tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v i.succ := by
    intro i

    simp only [sec, tsec, map_sum, map_mul, e0, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
    refine Finset.sum_congr rfl fun k _ => ?_
    show (t (i.succ, k) ⊗ₜ[Kl] (1 : Kl ⊗[K] Ω)) * ((1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] v k)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

  let g0 : RS K Ω D m →+* (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ⧸ tJ (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v) :=
    IsLocalization.lift (M := KTS K Ω D m) (g := ι.comp e0) (by
      rintro ⟨s, hs⟩
      obtain ⟨q, hq, rfl⟩ := hs
      show IsUnit (ι (e0 (ktToΩ K Ω D m q)))
      rw [he0kt]
      have hne : (MvPolynomial.aeval t : KT K D m →ₐ[K] K') q ≠ 0 := fun h =>
        nonZeroDivisors.ne_zero hq (hφ (h.trans (map_zero _).symm))
      exact (IsUnit.mk0 _ hne).map (ι.comp (algebraMap K' (TZ K Ω Kl K'))))
  have hg0 : ∀ a : ΩT Ω D m, g0 (algebraMap (ΩT Ω D m) (RS K Ω D m) a) = ι (e0 a) := fun a =>
    IsLocalization.lift_eq _ a
  have hmemJ : ∀ i : Fin D, ι (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v i.succ) = 0 := by
    intro i
    rw [IsScalarTower.algebraMap_apply (TZ K Ω Kl K') (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0))
      (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ⧸ tJ (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v)]
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    have h1 : algebraMap (TZ K Ω Kl K') (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0)) (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v i.succ) =
        algebraMap (TZ K Ω Kl K') (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0)) (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) *
          (algebraMap (TZ K Ω Kl K') (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0)) (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v i.succ) *
            IsLocalization.Away.invSelf (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0)) := by
      rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]
    rw [h1]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have hIs : ∀ a ∈ Is (K := K) (D := D) v, g0 a = 0 := by
    intro a ha
    have hle : Is (K := K) (D := D) v ≤ RingHom.ker g0 := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, hg0, he0sec, hmemJ]
    exact hle ha
  let g1 : (RS K Ω D m ⧸ Is (K := K) (D := D) v) →+* (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ⧸ tJ (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v) :=
    Ideal.Quotient.lift (Is (K := K) (D := D) v) g0 hIs
  have hcomm : g1.comp (algebraMap (KTf K D m) (RS K Ω D m ⧸ Is (K := K) (D := D) v)) =
      algebraMap (KTf K D m) (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ⧸ tJ (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (KT K D m)) (RingHom.ext fun q => ?_)
    simp only [RingHom.comp_apply]
    rw [← Ideal.Quotient.mk_algebraMap]
    have hmap : algebraMap (KTf K D m) (RS K Ω D m) (algebraMap (KT K D m) (KTf K D m) q) =
        algebraMap (ΩT Ω D m) (RS K Ω D m) (ktToΩ K Ω D m q) := IsLocalization.map_eq _ _
    rw [hmap]
    show g0 _ = _
    rw [hg0, he0kt, hιK]
    rw [IsScalarTower.algebraMap_apply (KTf K D m) K' (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ⧸ tJ (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v)]
    rw [RingHom.algebraMap_toAlgebra, IsFractionRing.lift_algebraMap]
    rfl
  let g : (RS K Ω D m ⧸ Is (K := K) (D := D) v) →ₐ[KTf K D m] (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ⧸ tJ (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v) :=
    { g1 with commutes' := fun r => congrArg (fun f => f r) hcomm }
  let Θ := Algebra.TensorProduct.lift (Algebra.ofId K' (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ⧸ tJ (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v))
    g (fun _ _ => Commute.all _ _)
  haveI : IsArtinianRing (K' ⊗[KTf K D m] (RS K Ω D m ⧸ Is (K := K) (D := D) v)) :=
    IsArtinianRing.of_finite K' _

  have hΘ1 : ∀ y : RS K Ω D m ⧸ Is (K := K) (D := D) v, Θ (1 ⊗ₜ y) = g y := fun y => by
    simp [Θ, Algebra.TensorProduct.lift_tmul]
  have hι : ∀ z : TZ K Ω Kl K', ι z ∈ Θ.range := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add ι]; exact add_mem ha hb
    | tmul k y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [TensorProduct.tmul_add, map_add (f := _)]; exact add_mem ha hb
      | tmul l ω =>
        have he : k ⊗ₜ[Kl] (l ⊗ₜ[K] ω) =
            algebraMap K' (TZ K Ω Kl K') (k * algebraMap Kl K' l) * fΩ ω := by
          show _ = ((k * algebraMap Kl K' l) ⊗ₜ[Kl] (1 : Kl ⊗[K] Ω)) * ((1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ω))
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          have : l ⊗ₜ[K] ω = l • ((1 : Kl) ⊗ₜ[K] ω) := by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]
        rw [he, map_mul]
        refine mul_mem ?_ ?_
        · rw [hιK]; exact Subalgebra.algebraMap_mem _ _
        · have : ι (fΩ ω) = Θ (1 ⊗ₜ (Ideal.Quotient.mk (Is (K := K) (D := D) v)
              (algebraMap (ΩT Ω D m) (RS K Ω D m) (MvPolynomial.C ω)))) := by
            rw [hΘ1]
            show _ = g0 _
            rw [hg0]
            simp [e0]
          rw [this]; exact Θ.mem_range_self _
  have hu : IsUnit (ι (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0)) := by
    rw [IsScalarTower.algebraMap_apply (TZ K Ω Kl K') (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0))
      (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ⧸ tJ (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v)]
    exact (IsLocalization.Away.algebraMap_isUnit (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0)).map _
  obtain ⟨b0, hb0'⟩ := hι (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0)
  have hb0 : Θ b0 = ι (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) := hb0'
  obtain ⟨n0, y0, hy0⟩ := IsArtinian.exists_pow_succ_smul_dvd b0 (1 : K' ⊗[KTf K D m] (RS K Ω D m ⧸ Is (K := K) (D := D) v))
  have hinv : ι (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) * Θ y0 = 1 := by
    rw [Nat.succ_eq_add_one, smul_eq_mul, smul_eq_mul, mul_one] at hy0
    have h := congrArg Θ hy0
    rw [map_mul, map_pow, map_pow, hb0] at h
    have h' : ι (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ^ n0 * (ι (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) * Θ y0) = ι (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ^ n0 * 1 := by
      rw [← mul_assoc, ← pow_succ, h, mul_one]
    exact (hu.pow n0).mul_left_cancel h'
  have hsurj : Function.Surjective Θ := by
    intro c
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0)) w
    obtain ⟨n, hn'⟩ := s.2
    have hn : tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0 ^ n = (s : TZ K Ω Kl K') := hn'
    have hcs : Ideal.Quotient.mk (tJ (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v)
        (IsLocalization.mk' (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0)) z s) * ι (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ^ n = ι z := by
      rw [IsScalarTower.algebraMap_apply (TZ K Ω Kl K') (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0))
        (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ⧸ tJ (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v),
        IsScalarTower.algebraMap_apply (TZ K Ω Kl K') (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0))
        (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0) ⧸ tJ (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v) z]
      rw [Ideal.Quotient.algebraMap_eq, ← map_pow, ← map_pow, ← map_mul, hn, IsLocalization.mk'_spec]
    have hc : Ideal.Quotient.mk (tJ (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v)
        (IsLocalization.mk' (Localization.Away (tsec (K := K) (Ω := Ω) (Kl := Kl) (K' := K') t v 0)) z s) = ι z * Θ y0 ^ n := by
      rw [← hcs, mul_assoc, ← mul_pow, hinv, one_pow, mul_one]
    have hm : ι z * Θ y0 ^ n ∈ Θ.range := mul_mem (hι z) (pow_mem (Θ.mem_range_self y0) n)
    obtain ⟨b, hb⟩ := hm
    exact ⟨b, by rw [hc]; exact hb⟩
  refine ⟨Module.Finite.of_surjective Θ.toLinearMap hsurj, ?_⟩

  have hvnrB : ∀ b : K' ⊗[KTf K D m] (RS K Ω D m ⧸ Is (K := K) (D := D) v), ∃ y, b = b ^ 2 * y := by
    intro b
    obtain ⟨n, y, h⟩ := IsArtinian.exists_pow_succ_smul_dvd b (1 : K' ⊗[KTf K D m] (RS K Ω D m ⧸ Is (K := K) (D := D) v))
    rw [Nat.succ_eq_add_one, smul_eq_mul, smul_eq_mul, mul_one] at h
    have hnil : IsNilpotent (b * (1 - b * y)) := by
      refine ⟨n + 1, ?_⟩
      rw [mul_pow]
      linear_combination (-(b * (1 - b * y) ^ n)) * h
    have h0 := hBred.eq_zero _ hnil
    exact ⟨y, by linear_combination h0⟩
  refine ⟨fun c hc => ?_⟩
  obtain ⟨k, hk⟩ := hc
  obtain ⟨b, rfl⟩ := hsurj c
  obtain ⟨y, hy⟩ := hvnrB b
  have hv : Θ b = Θ b ^ 2 * Θ y := by rw [← map_pow, ← map_mul, ← hy]
  have hpow : ∀ j : ℕ, Θ b = Θ b ^ (j + 1) * Θ y ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc Θ b = Θ b ^ (j + 1) * Θ y ^ j := ih
        _ = Θ b ^ j * Θ b * Θ y ^ j := by rw [pow_succ]
        _ = Θ b ^ j * (Θ b ^ 2 * Θ y) * Θ y ^ j := by rw [← hv]
        _ = Θ b ^ (j + 1 + 1) * Θ y ^ (j + 1) := by ring
  rw [hpow k, pow_succ, hk, zero_mul, zero_mul]

end Formalism.L2.Pj.GenSect
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.FiniteReducedSection

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CurveRecord

open Formalism.L2.Pj NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

theorem finite_reduced_of_eq {K Ω Kl K' : Type} [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
    [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K'] [CharZero K] {Dd m : ℕ}
    (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = Dd)
    (v : Fin m → Ω) (k₀ : Fin m) (hv₀ : v k₀ ≠ 0)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun k => v k / v k₀)) = Dd)
    (t : Fin (Dd + 1) × Fin m → K') (ht : AlgebraicIndependent K t)
    (a : Fin (Dd + 1) → K' ⊗[Kl] (Kl ⊗[K] Ω)) (ha : ∀ i, a i = ∑ k, t (i, k) ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] v k)) :
    FiniteDimensional K' (Localization.Away (a 0) ⧸ Ideal.span (Set.range fun i : Fin Dd =>
        algebraMap _ (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0))) ∧
      IsReduced (Localization.Away (a 0) ⧸ Ideal.span (Set.range fun i : Fin Dd =>
        algebraMap _ (Localization.Away (a 0)) (a i.succ) * IsLocalization.Away.invSelf (a 0))) := by
  have e : a = GenSect.tsec K Kl t v := funext fun i => ha i
  subst e
  have := GenSect.s1T (Kl := Kl) hfg htr v k₀ hv₀ hbig t ht
  unfold GenSect.tJ at this
  exact this



theorem tv_indep {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) [Algebra B.KO (Kp X la N)]
    [IsScalarTower B.KO (X.Kl la) (Kp X la N)] :
    AlgebraicIndependent B.KO (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) := by
  have hinj : Function.Injective (IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N)) :=
    IsLocalization.injective (Op X la N) (Ideal.primeCompl_le_nonZeroDivisors (gI X la N))
  have h0 := (MvPolynomial.algebraicIndependent_X (Idx D j N) (X.Ol la)).map' hinj
  have h1 := h0.map' (f := IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N))
    (IsFractionRing.injective (Op X la N) (Kp X la N))
  have : Algebra.IsAlgebraic (X.Ol la) (X.Kl la) := IsLocalization.isAlgebraic _ (nonZeroDivisors (X.Ol la))
  have h2 := (Algebra.IsAlgebraic.algebraicIndependent_iff (X.Ol la) (X.Kl la)).mp h1
  have h3 := h2.restrictScalars (R := B.KO) (algebraMap B.KO (X.Kl la)).injective
  have hfun : (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) =
      ⇑(IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N)) ∘
        (⇑(IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N)) ∘ MvPolynomial.X) := by
    funext p
    rw [Function.comp_apply, Function.comp_apply, IsScalarTower.toAlgHom_apply, IsScalarTower.toAlgHom_apply, Tv]
  rw [hfun]
  exact h3

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) (Ω : Type) [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω) {wL : WeightFamilies.Wt D j}
  (w : Fin N → B.Cusp j wL)

theorem rzMap_sec_eq (i : Fin (WeightFamilies.dimY D j + 1)) :
    rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i) =
      ∑ k, @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (i, k)) ⊗ₜ[X.Kl la]
        ((1 : X.Kl la) ⊗ₜ[B.KO] gF (X.inc wL (w k))) := by

  rw [Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, rzMap_emb, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem map_Jid_eq : Ideal.map (phiZ X la N Ω gF w) (Jid X la w) =
    Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i.succ)) *
        IsLocalization.Away.invSelf (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) := by
  have key : ∀ {R : Type} [CommRing R] {a b c : R}, a * b = 1 → a * c = 1 → b = c :=
    fun {_} _ {_} {b} {c} h1 h2 => by linear_combination c * h1 - b * h2
  rw [Jid, Ideal.map_span, ← Set.range_comp]
  refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
  show phiZ X la N Ω gF w (sfr X la w i.succ) = _
  rw [phiZ_apply, coe_sfr, frac_apply, pow_one, map_mul, lwZ_alg]
  congr 1
  have h1 := congrArg (lwZ X la N Ω gF w) (section_mul_inverse_eq_one X la w)
  rw [map_mul, lwZ_alg, map_one] at h1
  exact key h1 (IsLocalization.Away.mul_invSelf _)

theorem finite_reduced_record
    (hfg : (⊤ : IntermediateField B.KO Ω).FG) (htr : Algebra.trdeg B.KO Ω = WeightFamilies.dimY D j)
    (v : Fin N → Ω) (hv : ∀ k, gF (X.inc wL (w k)) = v k) (k₀ : Fin N) (hv₀ : v k₀ ≠ 0)
    (hbig : Algebra.trdeg B.KO (IntermediateField.adjoin B.KO (Set.range fun k => v k / v k₀)) =
      WeightFamilies.dimY D j) :
    FiniteDimensional (Kp X la N) (RZs X la N Ω gF w ⧸ Ideal.map (phiZ X la N Ω gF w) (Jid X la w)) ∧
      IsReduced (RZs X la N Ω gF w ⧸ Ideal.map (phiZ X la N Ω gF w) (Jid X la w)) := by
  let iK : Algebra B.KO (Kp X la N) :=
    ((algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la))).toAlgebra
  have : IsScalarTower B.KO (X.Kl la) (Kp X la N) := IsScalarTower.of_algebraMap_eq' rfl
  rw [map_Jid_eq]
  exact finite_reduced_of_eq hfg htr v k₀ hv₀ hbig _ (tv_indep X la N)
    (fun i => rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w i)) (fun i => by rw [rzMap_sec_eq]; simp only [hv])

end Rec

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)




theorem finite_reduced_section (hfg : FnFG (T.Q.Xo j) T.Q.c) (htr : FnTrdeg (T.Q.Xo j) T.Q.c (WeightFamilies.dimY D j)) :
    ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 → ∀ Z,
      FiniteDimensional (Kp (recPlus h j hj) la G.N)
          (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
            Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)) ∧
        IsReduced (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
          Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)) := by
  intro ka wL wF G S g0 la hH Z
  obtain ⟨-, ⟨-, hB2⟩, -, -⟩ := hH
  obtain ⟨k₀, hk₀, htrZ⟩ := hB2 Z
  exact finite_reduced_record (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w (hfg Z) (htr Z)
    (fun k => evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j))
    (fun k => formsEvR_single j hG hT Z _ _) k₀ hk₀ htrZ

end GlobalTheory.CurveRecord
end
end
end
