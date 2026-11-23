module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopNorm
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfArith
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
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
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.ReduceModChar
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PSelfDual
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfGen

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonicAevalEqZero

section

@[expose] public section

universe u_1

namespace GlobalTheory.IntegralTrace

open Polynomial

theorem exists_monic_aeval_eq_zero {R E : Type*} [CommRing R] [Field E] [Algebra R E] {n : ℕ}
    (L : Submodule R (Fin n → E)) (hL : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, M.mulVec x ∈ L) :
    ∃ p : R[X], p.Monic ∧ aeval M (p.map (algebraMap R E)) = 0 := by
  haveI : Module.Finite R L := Module.Finite.iff_fg.mpr hL
  let g : Module.End R (Fin n → E) := (Matrix.toLin' M).restrictScalars R
  have hg : ∀ x ∈ L, g x ∈ L := fun x hx => by simpa [g] using hM x hx
  obtain ⟨p, hp, hp0⟩ := LinearMap.exists_monic_and_aeval_eq_zero R (g.restrict hg)
  refine ⟨p, hp, ?_⟩
  have key : ∀ (q : R[X]) (x : L), ((aeval (g.restrict hg) q x : L) : Fin n → E)
      = (aeval M (q.map (algebraMap R E))).mulVec x := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x
      simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
    | add a b ha hb =>
      intro x
      simp only [map_add (f := _), Polynomial.map_add (f := _), LinearMap.add_apply, Submodule.coe_add, ha, hb,
        Matrix.add_mulVec]
    | monomial k a ih =>
      intro x
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.map_mul, map_mul (aeval M), Module.End.mul_apply,
        ih,
        Polynomial.map_X, aeval_X, aeval_X, ← Matrix.mulVec_mulVec]
      rfl
  apply Matrix.toLin'.injective
  rw [map_zero]
  apply LinearMap.ext_on hspan
  intro x hx
  have := key p ⟨x, hx⟩
  rw [hp0] at this
  simpa using this.symm

theorem isIntegral_trace {E : Type u_1} [inst : Field E] [NumberField E] (_φ : E →+* ℂ) {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.FG L)
    (hspan : Submodule.span E (↑L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, Matrix.mulVec M x ∈ L) :
    IsIntegral ℤ (Matrix.trace M) := by
  obtain ⟨p, hp, hp0⟩ := exists_monic_aeval_eq_zero L hL hspan M hM
  let K := AlgebraicClosure E
  let N : Matrix (Fin n) (Fin n) K := (algebraMap E K).mapMatrix M
  have hN : aeval N (p.map (algebraMap (NumberField.RingOfIntegers E) K)) = 0 := by
    have h1 := Polynomial.aeval_algHom_apply ((Algebra.ofId E K).mapMatrix (m := Fin n)) M
      (p.map (algebraMap (NumberField.RingOfIntegers E) E))
    rw [hp0, map_zero] at h1
    rw [IsScalarTower.algebraMap_eq (NumberField.RingOfIntegers E) E K, ← Polynomial.map_map,
      aeval_map_algebraMap]
    exact h1
  rw [← isIntegral_algebraMap_iff (B := K)]
  have htr : algebraMap E K M.trace = N.trace := by
    simp [N, Matrix.trace]
  rw [htr, Matrix.trace_eq_sum_roots_charpoly]
  apply IsIntegral.multiset_sum
  intro z hz
  have hz1 : z ∈ spectrum K N := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    exact (Polynomial.mem_roots N.charpoly_monic.ne_zero).mp hz
  have hz2 := spectrum.subset_polynomial_aeval N
    (p.map (algebraMap (NumberField.RingOfIntegers E) K)) ⟨z, hz1, rfl⟩
  rw [hN] at hz2
  have hz3 : eval z (p.map (algebraMap (NumberField.RingOfIntegers E) K)) = 0 := by
    by_contra h
    rw [spectrum.mem_iff] at hz2
    apply hz2
    rw [sub_zero]
    exact (IsUnit.mk0 _ h).map _
  have hz4 : IsIntegral (NumberField.RingOfIntegers E) z := ⟨p, hp, by rwa [eval_map] at hz3⟩
  exact isIntegral_trans z hz4

end GlobalTheory.IntegralTrace
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL3.PHfInt

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.TI

open Polynomial NumberField Matrix

theorem trace_isIntegral {E : Type*} [Field E] [NumberField E] (φ : E →+* ℂ) {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, M *ᵥ x ∈ L) : IsIntegral ℤ M.trace := by
  first | exact GlobalTheory.IntegralTrace.isIntegral_trace .. | (apply GlobalTheory.IntegralTrace.isIntegral_trace <;> assumption) | (intros; apply GlobalTheory.IntegralTrace.isIntegral_trace <;> assumption) | (apply @GlobalTheory.IntegralTrace.isIntegral_trace <;> assumption) | (intros; apply @GlobalTheory.IntegralTrace.isIntegral_trace <;> assumption) | (apply @GlobalTheory.IntegralTrace.isIntegral_trace <;> first | assumption | infer_instance) | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n L hfg hsp M hM | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n L hfg hsp M | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n L hfg hsp | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n L hfg | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n L | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ n | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› φ | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› ‹_› | exact @GlobalTheory.IntegralTrace.isIntegral_trace E ‹_› | exact @GlobalTheory.IntegralTrace.isIntegral_trace E

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.TI

end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.TI

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits Matrix

variable (D : D7)

def sE {N N' : ℕ} (A B : Matrix (Fin N') (Fin N) D.host.E) : D.host.E :=
  ∑ i, ∑ j, A i j * D.host.conj (B i j)

theorem hYY_eq {N N' : ℕ} (A B : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D A B = Algebra.trace D.host.K D.host.E (sE D A B) := rfl

theorem conj_int (o : 𝓞 D.host.E) : IsIntegral ℤ (D.host.conj (o : D.host.E)) :=
  o.isIntegral_coe.map (D.host.conj : D.host.E →ₐ[ℚ] D.host.E).toRingHom.toIntAlgHom

def cO (o : 𝓞 D.host.E) : 𝓞 D.host.E := ⟨D.host.conj (o : D.host.E), conj_int D o⟩

theorem smul_entry {N N' : ℕ} (o : 𝓞 D.host.E) (A : Matrix (Fin N') (Fin N) D.host.E) (i j) :
    (o • A) i j = (o : D.host.E) * A i j := by
  rw [Matrix.smul_apply, Algebra.smul_def]

theorem sE_add_left {N N' : ℕ} (A A' B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D (A + A') B = sE D A B + sE D A' B := by
  simp only [sE, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem sE_add_right {N N' : ℕ} (A B B' : Matrix (Fin N') (Fin N) D.host.E) :
    sE D A (B + B') = sE D A B + sE D A B' := by
  simp only [sE, Matrix.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem sE_zero_left {N N' : ℕ} (B : Matrix (Fin N') (Fin N) D.host.E) : sE D 0 B = 0 := by
  simp [sE]

theorem sE_zero_right {N N' : ℕ} (A : Matrix (Fin N') (Fin N) D.host.E) : sE D A 0 = 0 := by
  simp [sE]

theorem sE_smul_left {N N' : ℕ} (o : 𝓞 D.host.E) (A B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D (o • A) B = (o : D.host.E) * sE D A B := by
  simp only [sE, smul_entry, Finset.mul_sum, mul_assoc]

theorem sE_smul_right {N N' : ℕ} (o : 𝓞 D.host.E) (A B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D A (o • B) = D.host.conj (o : D.host.E) * sE D A B := by
  simp only [sE, smul_entry, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sE_esmul_left {N N' : ℕ} (a : D.host.E) (A B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D (a • A) B = a * sE D A B := by
  simp only [sE, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem sE_esmul_right {N N' : ℕ} (b : D.host.E) (A B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D A (b • B) = D.host.conj b * sE D A B := by
  simp only [sE, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sE_hom_gen {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    (A B : Matrix (Fin N') (Fin N) D.host.E)
    (hA : ∀ x ∈ L, A *ᵥ x ∈ L') (hB : ∀ x ∈ L, B *ᵥ x ∈ L') : IsIntegral ℤ (sE D A B) := by
  let _ := D.host.cmStar
  set Bs : Matrix (Fin N) (Fin N') D.host.E := Matrix.of fun j i => D.host.conj (B i j) with hBs
  have hBs_mem : ∀ y ∈ L', Bs *ᵥ y ∈ L := by
    intro y hy
    rw [hL.2.2]
    intro x hx
    have h1 : stdH D.host.E N x (Bs *ᵥ y) = stdH D.host.E N' (B *ᵥ x) y := by

      simp only [stdH, CU.star_conj D, Matrix.mulVec, dotProduct, hBs, Matrix.of_apply, map_sum,
      map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1]
    exact (hL'.2.2 y).1 hy _ (hB x hx)
  have hM : ∀ x ∈ L, (Bs * A) *ᵥ x ∈ L := by
    intro x hx
    rw [← Matrix.mulVec_mulVec]
    exact hBs_mem _ (hA x hx)
  have h := trace_isIntegral D.host.φ₀ L hL.1 hL.2.1 (Bs * A) hM
  have htr : (Bs * A).trace = sE D A B := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, sE, hBs, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rwa [htr] at h

theorem sE_hom {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    (A B : Matrix (Fin N') (Fin N) D.host.E) (hA : A ∈ homL D L L') (hB : B ∈ homL D L L') :
    IsIntegral ℤ (sE D A B) := by
  have h1 : ∀ A ∈ homL D L L', ∀ B, (∀ x ∈ L, B *ᵥ x ∈ L') → IsIntegral ℤ (sE D A B) := by
    intro A hA B hB
    induction hA using Submodule.span_induction with
    | mem A hA => exact sE_hom_gen D L L' hL hL' A B hA hB
    | zero => rw [sE_zero_left]; exact isIntegral_zero
    | add A A' _ _ h1 h2 => rw [sE_add_left]; exact h1.add h2
    | smul o A _ h1 => rw [sE_smul_left]; exact o.isIntegral_coe.mul h1
  induction hB using Submodule.span_induction with
  | mem B hB => exact h1 A hA B hB
  | zero => rw [sE_zero_right]; exact isIntegral_zero
  | add B B' _ _ h2 h3 => rw [sE_add_right]; exact h2.add h3
  | smul o B _ h2 => rw [sE_smul_right]; exact (conj_int D o).mul h2

def TrOK (z : D.host.E) : Prop :=
  ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace D.host.K D.host.E ((o : D.host.E) * z))

theorem trOK_zero : TrOK D 0 := fun o => by rw [mul_zero, map_zero]; exact isIntegral_zero

theorem trOK_add {z w : D.host.E} (hz : TrOK D z) (hw : TrOK D w) : TrOK D (z + w) :=
  fun o => by rw [mul_add, map_add (f := _)]; exact (hz o).add (hw o)

theorem trOK_mul {z : D.host.E} (hz : TrOK D z) (o' : 𝓞 D.host.E) : TrOK D ((o' : D.host.E) * z) :=
  fun o => by
    have := hz (o * o')
    rwa [show ((o * o' : 𝓞 D.host.E) : D.host.E) = (o : D.host.E) * o' from rfl, mul_assoc] at this

theorem trace_conj_integral (a b : D.host.E) (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    (hb : b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    IsIntegral ℤ (Algebra.trace D.host.K D.host.E (a * D.host.conj b)) := by
  have h := ((D.host.der.unimodular D.host.𝔟 D.host.𝔟_spec.1 a).1 ha) b hb
  obtain ⟨r, hr⟩ := h
  rw [← hr]
  exact r.isIntegral_coe

theorem trOK_gen (a b : D.host.E) (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    (hb : b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) (t : 𝓞 D.host.E) :
    TrOK D (a * D.host.conj b * t) := by
  intro o
  have hot : ((o * t : 𝓞 D.host.E) : D.host.E) * a ∈
      (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    have := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem (o * t) ha
    rwa [Algebra.smul_def] at this
  have := trace_conj_integral D _ b hot hb
  rw [show ((o * t : 𝓞 D.host.E) : D.host.E) = (o : D.host.E) * t from rfl] at this
  convert this using 2
  ring

theorem trOK_YY {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    (A B : Matrix (Fin N') (Fin N) D.host.E) (hA : A ∈ YYl D L L') (hB : B ∈ YYl D L L') :
    TrOK D (sE D A B) := by

  have hgen : ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∀ A₀ ∈ homL D L L',
      ∀ b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∀ B₀ ∈ homL D L L',
      TrOK D (sE D (a • A₀) (b • B₀)) := by
    intro a ha A₀ hA₀ b hb B₀ hB₀
    rw [sE_esmul_left, sE_esmul_right, ← mul_assoc]
    exact trOK_gen D a b ha hb ⟨sE D A₀ B₀, sE_hom D L L' hL hL' A₀ B₀ hA₀ hB₀⟩
  have h1 : ∀ A ∈ YYl D L L', ∀ b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      ∀ B₀ ∈ homL D L L', TrOK D (sE D A (b • B₀)) := by
    intro A hA b hb B₀ hB₀
    induction hA using Submodule.span_induction with
    | mem A hA =>
      obtain ⟨a, ha, A₀, hA₀, rfl⟩ := hA
      exact hgen a ha A₀ hA₀ b hb B₀ hB₀
    | zero => rw [sE_zero_left]; exact trOK_zero D
    | add A A' _ _ h2 h3 => rw [sE_add_left]; exact trOK_add D h2 h3
    | smul o A _ h2 => rw [sE_smul_left]; exact trOK_mul D h2 o
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨b, hb, B₀, hB₀, rfl⟩ := hB
    exact h1 A hA b hb B₀ hB₀
  | zero => rw [sE_zero_right]; exact trOK_zero D
  | add B B' _ _ h2 h3 => rw [sE_add_right]; exact trOK_add D h2 h3
  | smul o B _ h2 => rw [sE_smul_right]; exact trOK_mul D h2 (cO D o)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.TI

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.TI

theorem hermitian_pairing_integral : AR.HYYIntRec := by
  intro D N N' L L' hA A hA' B hB'
  have h := trOK_YY D L L' hA.2.2.1 hA.2.2.2 A B hA' hB' 1
  rw [hYY_eq]
  simpa using h

theorem arithmetic_hermitian_form : HfArithRec := HfArithRec_of_int hermitian_pairing_integral

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
end
end

-- Source module: Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep

section

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

theorem hermitian_form_integral_values : HfIntRec := HfIntRec_of_gen (HfGenRec_of_arith arithmetic_hermitian_form)

theorem theta_operator_isometry : ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ,
    IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IopIso D (tor0 D cc δ) :=
  IopIso_of_parts hermitian_form_integral_values self_dual_lattice

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
end
end
