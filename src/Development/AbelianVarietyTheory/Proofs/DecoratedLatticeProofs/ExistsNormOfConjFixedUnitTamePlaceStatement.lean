module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SigV
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionTensorRelativeBasisCoordsUniqueStatement
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.TypeStar
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SigV
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdeleAtPlaceWithComponentStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalIntegersTensorCoordsPrimeToDiscriminantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqIdOfIsUnramifiedAt
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdeleComponentAtFinitePlaceIntegralMemLocalTenso

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

namespace GlobalTheory.FixedUnitNorm

theorem compAt_mem_intV_of_intAt : ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ intAt D (· = v) → compAt D v a ∈ intV D v := by
  intro D v a ha
  have h : finPart D a ∈ intAE D := ha.2
  show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (finPart D a) ∈ intV D v
  generalize finPart D a = b at h ⊢
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    exact ⟨_, hα v, x, rfl⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [RingHom.map_add (f := _)]; exact add_mem hy hz
  | neg y _ hy => rw [RingHom.map_neg]; exact neg_mem hy

end GlobalTheory.FixedUnitNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdeleComponentAtFinitePlaceIntegralMemLocalTensoStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.adeleComponentAtFinitePlace_integral_mem_localTensor : ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ intAt D (· = v) → compAt D v a ∈ intV D v := by
  first | exact @GlobalTheory.FixedUnitNorm.compAt_mem_intV_of_intAt | exact GlobalTheory.FixedUnitNorm.compAt_mem_intV_of_intAt | (intros; apply GlobalTheory.FixedUnitNorm.compAt_mem_intV_of_intAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsEqAdicCompletionIntegers

section

@[expose] public section

open IsDedekindDomain NumberField IsLocalRing

namespace GlobalTheory.BinaryUnitForm

theorem exists_eq_of_henselian {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] [Finite (ResidueField R)] (t n u : R)
    (hD : IsUnit (t ^ 2 - 4 * n)) (hu : IsUnit u) :
    ∃ r s : R, r ^ 2 + t * r * s + n * s ^ 2 = u := by
  obtain ⟨r, s, hrs⟩ := GlobalTheory.UnramifiedHermitian.exists_binary_eq_of_finite
    (a := residue R t) (n := residue R n)
    (by simpa only [map_sub, map_mul, map_pow, map_ofNat] using (hD.map (residue R)).ne_zero)
    (residue R u)
  obtain ⟨r, rfl⟩ := residue_surjective r
  obtain ⟨s, rfl⟩ := residue_surjective s
  have hN : residue R (r ^ 2 + t * r * s + n * s ^ 2) = residue R u := by
    simpa only [map_add (f := _), map_mul, map_pow] using hrs
  have hNu : IsUnit (r ^ 2 + t * r * s + n * s ^ 2) := by
    rw [← residue_ne_zero_iff_isUnit, hN]
    exact (hu.map _).ne_zero
  obtain ⟨w, hw⟩ := hNu.exists_right_inv
  have he : u * w - 1 ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, map_mul, ← hN, ← map_mul, hw, map_one, sub_self]

  have hspan : Ideal.span {(2 : R), t} = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem _ _ hD
    rw [Ideal.mem_span_pair]
    exact ⟨-2 * n, t, by ring⟩
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1
    (show (1 : R) ∈ Ideal.span {(2 : R), t} by rw [hspan]; exact Submodule.mem_top)
  obtain ⟨T, hT⟩ := GlobalTheory.UnramifiedHermitian.exists_add_mul_sq_eq (maximalIdeal R)
    (α ^ 2 + t * α * β + n * β ^ 2) he
  refine ⟨r * (1 + T * α) - n * s * (T * β), r * (T * β) + (1 + T * α) * s + t * s * (T * β), ?_⟩
  linear_combination (r ^ 2 + t * r * s + n * s ^ 2) * T * hαβ
    + (r ^ 2 + t * r * s + n * s ^ 2) * hT + u * hw

theorem exists_eq_adicCompletionIntegers : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (t n u : v.adicCompletionIntegers F),
    IsUnit (t ^ 2 - 4 * n) → IsUnit u → ∃ r s : v.adicCompletionIntegers F,
      r ^ 2 + t * r * s + n * s ^ 2 = u := by
  intro F _ _ v t n u hD hu
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  exact exists_eq_of_henselian t n u hD hu

end GlobalTheory.BinaryUnitForm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsEqAdicCompletionIntegersStatement

section

@[expose] public section

open IsDedekindDomain NumberField

theorem _root_.GlobalTheory.T.exists_binary_quadratic_eq_unit_of_disc_isUnit : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t n u : v.adicCompletionIntegers F), IsUnit (t ^ 2 - 4 * n) → IsUnit u → ∃ r s : v.adicCompletionIntegers F, r ^ 2 + t * r * s + n * s ^ 2 = u := by
  first | exact @GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers | exact GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers | (intros; apply GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegerOfRelativeTraceNormIntegral

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

namespace GlobalTheory.FixedUnitNorm

theorem integral_of_trace_norm_integral : ∀ (D : D7) (w : D.host.E) (t n : 𝓞 D.host.F),
    w + D.sp.cm.sig w = algebraMap D.host.F D.host.E t →
    w * D.sp.cm.sig w = algebraMap D.host.F D.host.E n → ∃ x : 𝓞 D.host.E, (x : D.host.E) = w := by
  intro D w t n ht hn
  have hint : ∀ s : 𝓞 D.host.F, IsIntegral ℤ (algebraMap D.host.F D.host.E s) := fun s =>
    (NumberField.RingOfIntegers.isIntegral_coe s).map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
  let t' : 𝓞 D.host.E := ⟨algebraMap D.host.F D.host.E t, hint t⟩
  let n' : 𝓞 D.host.E := ⟨algebraMap D.host.F D.host.E n, hint n⟩
  have hw : IsIntegral (𝓞 D.host.E) w := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C n', ?_, ?_⟩
    · monicity!
    · have h1 : algebraMap (𝓞 D.host.E) D.host.E t' = w + D.sp.cm.sig w := ht.symm
      have h2 : algebraMap (𝓞 D.host.E) D.host.E n' = w * D.sp.cm.sig w := hn.symm
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C, h1, h2]
      ring
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 D.host.E) (K := D.host.E)).mp hw
  exact ⟨y, hy⟩

end GlobalTheory.FixedUnitNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegerOfRelativeTraceNormIntegralStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_integer_of_relative_trace_norm_integral : ∀ (D : D7) (w : D.host.E) (t n : 𝓞 D.host.F), w + D.sp.cm.sig w = algebraMap D.host.F D.host.E t → w * D.sp.cm.sig w = algebraMap D.host.F D.host.E n → ∃ x : 𝓞 D.host.E, (x : D.host.E) = w := by
  first | exact @GlobalTheory.FixedUnitNorm.integral_of_trace_norm_integral | exact GlobalTheory.FixedUnitNorm.integral_of_trace_norm_integral | (intros; apply GlobalTheory.FixedUnitNorm.integral_of_trace_norm_integral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOfConjFixedUnitTamePlace

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace
open IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

namespace GlobalTheory.FixedUnitNorm


theorem compAt_cA (D : D7) (v : Pl D) (a : AE D) : compAt D v (cA D a) = sigV D v (compAt D v a) := by
  induction a using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), map_add (f := _), hx, hy]
  | tmul a m => rfl


theorem tmul_algebraMap (D : D7) (v : Pl D) (c : Fv D.host.F v) (f : D.host.F) :
    c ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E f) = (algebraMap D.host.F (Fv D.host.F v) f * c) ⊗ₜ[D.host.F] (1 : D.host.E) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]




theorem fixed_unit_norm : ∀ (D : D7) (v : Pl D) (ε : AE D), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) →
    (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → ∀ u ∈ intAt D (· = v), cA D u = u →
    (∃ y ∈ intAt D (· = v), u * y = ε) → ∃ x ∈ intAt D (· = v), x * cA D x = u := by
  intro D v ε hT _ _ _ hid u hu hcu ⟨y, hy, huy⟩
  obtain ⟨w, t, n, h1, h2, h3⟩ := GlobalTheory.UnramifiedDiscriminant.exists_discr_notMem D.host.F D.host.E D.sp.cm.sig
    (GlobalTheory.AdelicU.isCMExt_host D) v (fun P hP => @hT.1 P.asIdeal P.isPrime hP)
  have hw : ∀ f : D.host.F, algebraMap D.host.F D.host.E f ≠ w := by
    intro f hf
    apply h3
    have hs : D.sp.cm.sig w = w := by rw [← hf, AlgHom.commutes]
    have e : algebraMap D.host.F D.host.E ((t : D.host.F) ^ 2 - 4 * n) = 0 := by
      rw [map_sub, map_pow, map_mul, ← h1, ← h2, hs, map_ofNat]; ring
    have e2 : ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) = 0 := by
      have := (FaithfulSMul.algebraMap_injective D.host.F D.host.E) (e.trans (map_zero _).symm)
      push_cast; exact this
    have e3 : t ^ 2 - 4 * n = 0 := RingOfIntegers.coe_eq_zero_iff.1 e2
    rw [e3]; exact v.asIdeal.zero_mem
  obtain ⟨W, hW⟩ := GlobalTheory.T.exists_integer_of_relative_trace_norm_integral D w t n h1 h2

  have hone : (1 : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intV D v :=
    AddSubgroup.subset_closure ⟨1, (v.adicCompletionIntegers D.host.F).one_mem, 1, by simp [Algebra.TensorProduct.one_def]⟩
  have hε1 : compAt D v ε = 1 := by
    obtain ⟨z, hz, hz1⟩ := GlobalTheory.T.exists_integralAdele_atPlace_with_component D v 1 hone
    have h := congrArg (compAt D v) ((hid z).1 hz.1)
    rwa [RingHom.map_mul, hz1, mul_one] at h

  obtain ⟨a, ha, b, hb, hU⟩ := GlobalTheory.T.localIntegers_tensor_coords_prime_to_discriminant D v w t n h1 h2 h3 _ (GlobalTheory.T.adeleComponentAtFinitePlace_integral_mem_localTensor D v u hu)
  have hsig : sigV D v (compAt D v u) = compAt D v u := by rw [← compAt_cA, hcu]
  have hsw : D.sp.cm.sig w = algebraMap D.host.F D.host.E t - w := by rw [← h1]; ring
  have hb0 : b = 0 := by
    have e : sigV D v (a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w) -
        (a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w) = 0 := by rw [← hU, hsig, sub_self]
    have e' : (algebraMap D.host.F (Fv D.host.F v) t * b) ⊗ₜ[D.host.F] (1 : D.host.E) + (-(2 * b)) ⊗ₜ[D.host.F] w = 0 := by
      rw [← e, sigV, map_add (f := _), Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply,
        map_one, hsw, TensorProduct.tmul_sub, tmul_algebraMap, TensorProduct.neg_tmul]
      rw [show (2 : Fv D.host.F v) * b = b + b by ring, TensorProduct.add_tmul]
      abel
    have := (GlobalTheory.T.completion_tensor_relativeBasis_coords_unique D v w hw _ _ e').2
    have h2b : (2 : Fv D.host.F v) * b = 0 := neg_eq_zero.1 this
    have h2ne : (2 : Fv D.host.F v) ≠ 0 := by
      intro h
      apply two_ne_zero (α := D.host.F)
      apply (algebraMap D.host.F (Fv D.host.F v)).injective
      rw [map_ofNat, map_zero]; exact h
    exact (mul_eq_zero.1 h2b).resolve_left h2ne
  rw [hb0, TensorProduct.zero_tmul, add_zero] at hU
  obtain ⟨a', ha', b', hb', hY⟩ := GlobalTheory.T.localIntegers_tensor_coords_prime_to_discriminant D v w t n h1 h2 h3 _ (GlobalTheory.T.adeleComponentAtFinitePlace_integral_mem_localTensor D v y hy)
  have haa : a * a' = 1 := by
    have e : compAt D v u * compAt D v y = 1 := by rw [← RingHom.map_mul, huy, hε1]
    rw [hU, hY, mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul] at e
    have e' : (a * a' - 1) ⊗ₜ[D.host.F] (1 : D.host.E) + (a * b') ⊗ₜ[D.host.F] w = 0 := by
      rw [TensorProduct.sub_tmul, ← Algebra.TensorProduct.one_def, ← e]; abel
    exact sub_eq_zero.1 (GlobalTheory.T.completion_tensor_relativeBasis_coords_unique D v w hw _ _ e').1
  let A : v.adicCompletionIntegers D.host.F := ⟨a, ha⟩
  have hAu : IsUnit A := ⟨⟨A, ⟨a', ha'⟩, Subtype.ext haa, Subtype.ext (by rw [mul_comm]; exact haa)⟩, rfl⟩
  have hD : IsUnit (algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) t ^ 2 -
      4 * algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) n) := by
    have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v _).2 h3
    rwa [map_sub, map_pow, map_mul, map_ofNat] at this
  obtain ⟨r, s, hrs⟩ := GlobalTheory.T.exists_binary_quadratic_eq_unit_of_disc_isUnit D.host.F v _ _ A hD hAu

  set x' : Fv D.host.F v ⊗[D.host.F] D.host.E := (r : Fv D.host.F v) ⊗ₜ[D.host.F] (1 : D.host.E) + (s : Fv D.host.F v) ⊗ₜ[D.host.F] w
  have hx'i : x' ∈ intV D v := by
    refine AddSubgroup.add_mem _ (AddSubgroup.subset_closure ⟨r, r.2, 1, by simp⟩)
      (AddSubgroup.subset_closure ⟨s, s.2, W, by rw [hW]⟩)
  have hcoe : ∀ c : 𝓞 D.host.F, ((algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) c : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) =
      algebraMap D.host.F (Fv D.host.F v) c := fun c => rfl
  have hnorm : x' * sigV D v x' = compAt D v u := by
    have hrs' : (r : Fv D.host.F v) ^ 2 + algebraMap D.host.F (Fv D.host.F v) t * r * s +
        algebraMap D.host.F (Fv D.host.F v) n * (s : Fv D.host.F v) ^ 2 = a := by
      have := congrArg (fun q : v.adicCompletionIntegers D.host.F => (q : Fv D.host.F v)) hrs
      exact this
    have e1 : sigV D v x' = (r : Fv D.host.F v) ⊗ₜ[D.host.F] (1 : D.host.E) + (s : Fv D.host.F v) ⊗ₜ[D.host.F] D.sp.cm.sig w := by
      simp only [x', sigV, map_add (f := _), Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    rw [e1, hU]
    simp only [x', add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have e2 : ((s : Fv D.host.F v) * r) ⊗ₜ[D.host.F] w = ((r : Fv D.host.F v) * s) ⊗ₜ[D.host.F] w := by rw [mul_comm]
    rw [e2, h2, tmul_algebraMap, hsw, TensorProduct.tmul_sub, tmul_algebraMap]
    have key : ∀ P Q R S : Fv D.host.F v ⊗[D.host.F] D.host.E, P + S + (Q - S + R) = P + Q + R := fun P Q R S => by abel
    rw [key, ← TensorProduct.add_tmul, ← TensorProduct.add_tmul]
    congr 1
    rw [← hrs']; ring
  obtain ⟨x, hxi, hxc⟩ := GlobalTheory.T.exists_integralAdele_atPlace_with_component D v x' hx'i
  refine ⟨x, hxi, ?_⟩
  have hx0 := (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ x).1 hxi.1
  have hu0 := (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ u).1 hu.1
  rw [← sub_eq_zero]
  apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
  · rw [RingHom.map_sub, RingHom.map_mul, hx0.1, zero_mul, hu0.1, sub_zero]
  · intro w'
    by_cases hw' : w' = v
    · subst hw'; rw [RingHom.map_sub, RingHom.map_mul, compAt_cA, hxc, hnorm, sub_self]
    · rw [RingHom.map_sub, RingHom.map_mul, hx0.2 w' hw', zero_mul, hu0.2 w' hw', sub_zero]

end GlobalTheory.FixedUnitNorm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOfConjFixedUnitTamePlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.exists_norm_of_conjFixed_unit_tamePlace : ∀ (D : D7) (v : Pl D) (ε : AE D), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → ∀ u ∈ intAt D (· = v), cA D u = u → (∃ y ∈ intAt D (· = v), u * y = ε) → ∃ x ∈ intAt D (· = v), x * cA D x = u := by
  first | exact @GlobalTheory.FixedUnitNorm.fixed_unit_norm | exact GlobalTheory.FixedUnitNorm.fixed_unit_norm | (intros; apply GlobalTheory.FixedUnitNorm.fixed_unit_norm <;> assumption)
end
end
