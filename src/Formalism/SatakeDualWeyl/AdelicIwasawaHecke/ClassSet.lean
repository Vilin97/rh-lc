module

public import Formalism.SatakeDualWeyl.StatementC
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.ClassInjectiveOfSpanRecovery
public import Formalism.SatakeDualWeyl.DefsCS
public import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
public import Formalism.HermitianLattices.HermitianLatticesProofs.FinIntermediate
public import Formalism.HermitianLattices.HermitianLatticesProofs.IsomOfTrace
public import Formalism.HermitianLattices.HermitianLatticesProofs.ShortVectors
public import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsAsmHformSmulRight
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsCovol
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEasy
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEquiv
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.ClassSetFiniteBoundedHolds

section

@[expose] public section

noncomputable section

open NumberField

namespace Formalism.UG.P

theorem csBdd_nat_mul {K : Type} [Field K] [NumberField K] (d : 𝓞 K) (hd : d ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ t : 𝓞 K, (m : 𝓞 K) = d * t := by
  classical
  refine ⟨Ideal.absNorm (Ideal.span {d}), ?_, ?_⟩
  · refine Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd
  · obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
    exact ⟨t, by rw [← ht, mul_comm]⟩

theorem class_set_finite_bounded_holds (hCovolOfDual : Formalism.UG.CS.CovolOfDual) :
    Formalism.UG.CS.ClassSetFiniteBdd := by
  intro K V _ _ _ _ _ _ _ _ h hsymm hpos d e hd he
  obtain ⟨N, ι, hι, hmul, hlat⟩ := Formalism.HermitianLatticesTheory.traceReal_main h hsymm hpos
  obtain ⟨C, hC⟩ := hCovolOfDual K V h hsymm hpos N ι hι e he
  obtain ⟨m, hm, t, ht⟩ := csBdd_nat_mul d hd
  let S : Set (Submodule (𝓞 K) V) := {M | Submodule.IsLattice K M ∧
    (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ (1 : Submodule (𝓞 K) K)) ∧
    (∀ x ∈ Formalism.HermitianLatticesTheory.dual h M, (e : K) • x ∈ M)}
  have hfull : ∀ M ∈ S, Submodule.IsFullLattice K M := by
    intro M hM
    let W := Submodule.span K (M : Set V)
    let b := Module.finBasis K W
    let f : V →ₗ[K] (Fin (Module.finrank K W) → K) := LinearMap.pi (fun i => h (b i : V))
    have hf : Function.Injective f := by
      apply LinearMap.ker_eq_bot.mp
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hzero : (h.flip x).comp W.subtype = 0 := by
        apply b.ext
        intro i
        exact congrFun (LinearMap.mem_ker.mp hx) i
      have hz (y : V) (hy : y ∈ M) : h y x = 0 :=
        LinearMap.congr_fun hzero ⟨y, Submodule.subset_span hy⟩
      have hxd : x ∈ Formalism.HermitianLatticesTheory.dual h M := by
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf,
          Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        rw [hz y hy]
        exact Submodule.zero_mem _
      -- The dual bound puts a nonzero scalar multiple of x in M, so positivity forces x = 0.
      have hxx := hsymm.eq_iff.mp (hz _ (hM.2.2 x hxd))
      rw [map_smul, smul_eq_mul] at hxx
      have heK : (e : K) ≠ 0 := fun he0 => he (RingOfIntegers.ext he0)
      have hxx0 := (mul_eq_zero.mp hxx).resolve_left heK
      by_contra hx0
      simpa [hxx0] using hpos x hx0
    have hdim := LinearMap.finrank_le_finrank_of_injective hf
    exact { hM.1 with
      span_eq_top := Submodule.eq_of_le_of_finrank_le le_top
        (by simpa only [finrank_top, Module.finrank_fin_fun] using hdim) }
  have hSd : ∀ M ∈ S, ∀ x ∈ M, ∀ y ∈ M, (m : K) * h x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro M hM x hx y hy
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hM.2.1 x hx y hy)
    refine Submodule.mem_one.mpr ⟨t * a, ?_⟩
    have hmK : (m : K) = (d : K) * (t : K) := by
      have := congrArg (algebraMap (𝓞 K) K) ht
      simpa using this
    rw [map_mul, ha, hmK]
    have htc : algebraMap (𝓞 K) K t = (t : K) := rfl
    rw [htc]
    ring
  obtain ⟨s, -, hs⟩ := Formalism.HermitianLatticesTheory.classSetFinite_core Formalism.HermitianLatticesTheory.shortVectors
    Formalism.HermitianLatticesTheory.finIntermediate Formalism.HermitianLatticesTheory.isomOfTrace h hpos N ι hι hmul m hm C S hSd
    (fun M hM => hlat M (hfull M hM)) (fun M hM _ _ => hC M hM.1 hM.2.2)
  exact ⟨s, fun M hM hdM heM => hs M ⟨hM, hdM, heM⟩⟩

end Formalism.UG.P
end
end
end

-- Source module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsTrace

section

@[expose] public section

noncomputable section

open NumberField

namespace Formalism.UG.P

theorem csTrace_trace_pos {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (b : F)
    (hb : ∀ ι : F →+* ℝ, 0 < ι b) : 0 < Algebra.trace ℚ F b := by
  have key : algebraMap ℚ ℂ (Algebra.trace ℚ F b) = ∑ σ : F →ₐ[ℚ] ℂ, σ b :=
    trace_eq_sum_embeddings ℂ
  have hre : ∀ σ : F →ₐ[ℚ] ℂ, 0 < (σ b).re := by
    intro σ
    have hr : NumberField.ComplexEmbedding.IsReal (σ : F →+* ℂ) :=
      NumberField.InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _)
    have e := hr.coe_embedding_apply b
    have e' : (σ : F →+* ℂ) b = σ b := rfl
    rw [← e', ← e, Complex.ofReal_re]
    exact hb _
  have hne : Nonempty (F →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have h2 := congrArg Complex.re key
  rw [Complex.re_sum] at h2
  have h3 : 0 < ∑ σ : F →ₐ[ℚ] ℂ, (σ b).re :=
    Finset.sum_pos (fun σ _ => hre σ) Finset.univ_nonempty
  rw [← h2] at h3
  simpa using h3

theorem csTrace_trace_algebraMap_pos {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [IsTotallyReal F] (b : F) (hb : ∀ ι : F →+* ℝ, 0 < ι b) :
    0 < Algebra.trace ℚ E (algebraMap F E b) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [← Algebra.trace_trace (S := F), Algebra.trace_algebraMap, map_nsmul]
  exact nsmul_pos (csTrace_trace_pos b hb) Module.finrank_pos.ne'

theorem trace_form_positive : Formalism.UG.CS.TracePos := by
  intro F E _ _ _ _ _ n _ _ σ J hJ
  obtain ⟨hF, hdef⟩ := hJ
  haveI : IsTotallyReal F := hF

  let φ0 : F →+* ℂ := (IsAlgClosed.lift : F →ₐ[ℚ] ℂ).toRingHom
  let ι0 : F →+* ℝ :=
    (NumberField.InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal (NumberField.InfinitePlace.mk φ0))).embedding
  have hval : ∀ x : n → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x := by
    intro x hx
    rcases hdef ι0 with h | h
    · obtain ⟨a, ha, -⟩ := h x hx; exact ⟨a, ha⟩
    · obtain ⟨a, ha, -⟩ := h x hx; exact ⟨a, ha⟩

  have same : ∀ x y : n → E, x ≠ 0 → y ≠ 0 → ∀ a b : F,
      algebraMap F E a = hform (σ : E →+* E) J x x →
      algebraMap F E b = hform (σ : E →+* E) J y y → ∀ ι : F →+* ℝ, 0 < ι a * ι b := by
    intro x y hx hy a b ha hb ι
    rcases hdef ι with h | h
    · obtain ⟨a', ha', hap⟩ := h x hx
      obtain ⟨b', hb', hbp⟩ := h y hy
      have e1 : a' = a := (algebraMap F E).injective (ha'.trans ha.symm)
      have e2 : b' = b := (algebraMap F E).injective (hb'.trans hb.symm)
      subst e1 e2
      exact mul_pos hap hbp
    · obtain ⟨a', ha', hap⟩ := h x hx
      obtain ⟨b', hb', hbp⟩ := h y hy
      have e1 : a' = a := (algebraMap F E).injective (ha'.trans ha.symm)
      have e2 : b' = b := (algebraMap F E).injective (hb'.trans hb.symm)
      subst e1 e2
      exact mul_pos_of_neg_of_neg hap hbp
  by_cases hx : ∃ x0 : n → E, x0 ≠ 0
  · obtain ⟨x0, hx0⟩ := hx
    obtain ⟨a0, ha0⟩ := hval x0 hx0
    have ha0ne : a0 ≠ 0 := by
      intro h0
      have := same x0 x0 hx0 hx0 a0 a0 ha0 ha0 ι0
      rw [h0, map_zero, zero_mul] at this
      exact lt_irrefl _ this
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a0
    have hqF : algebraMap (𝓞 F) F q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (nonZeroDivisors.ne_zero hq)
    have hp : algebraMap (𝓞 F) F p = a0 * algebraMap (𝓞 F) F q := by
      rw [← hpq, div_mul_cancel₀ _ hqF]
    have hc : ((p * q : 𝓞 F) : F) = a0 * algebraMap (𝓞 F) F q * algebraMap (𝓞 F) F q := by
      have : ((p * q : 𝓞 F) : F) = algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F q := by
        rw [← map_mul]
      rw [this, hp]
    refine ⟨p * q, ?_, ?_⟩
    · intro h0
      have : ((p * q : 𝓞 F) : F) = 0 := by simp [h0]
      rw [hc] at this
      exact mul_ne_zero (mul_ne_zero ha0ne hqF) hqF this
    · intro x hx
      obtain ⟨a, ha⟩ := hval x hx
      rw [← ha, ← map_mul]
      apply csTrace_trace_algebraMap_pos
      intro ι
      have hs := same x0 x hx0 hx a0 a ha0 ha ι
      have hq2 : 0 < ι (algebraMap (𝓞 F) F q) * ι (algebraMap (𝓞 F) F q) :=
        mul_self_pos.mpr ((map_ne_zero_iff _ ι.injective).mpr hqF)
      rw [hc, map_mul, map_mul, map_mul]
      nlinarith [mul_pos hs hq2]
  · push_neg at hx
    refine ⟨1, one_ne_zero, fun x hx' => absurd (hx x) hx'⟩

end Formalism.UG.P
end
end
end

-- Source module: Formalism.SatakeDualWeyl.AdelicIwasawaHecke.ClassSet

section

@[expose] public section

namespace Formalism.UG.P

theorem lattice_class_set_finite_local_holds : Formalism.UG.ClassSetFiniteL :=
  have hs := span_recovery_of_integral_adelic_approx integral_adele_approximation_holds
  classSetFiniteL_of sigma_involution_holds trace_form_positive hermitian_form_symmetry_holds unitary_isometry_lattice_holds
    global_lattice_isLattice_holds (class_injective_of_span_recovery hs global_lattice_equiv_holds) scale_bound_holds
    (dual_lattice_bound_holds hs) (class_set_finite_bounded_holds covolume_of_dual_holds) standard_lattice_full_holds

theorem lattice_class_set_finite_holds : Formalism.UG.ClassSetFinite :=
  have hs := span_recovery_of_integral_adelic_approx integral_adele_approximation_holds
  classSetFinite_of sigma_involution_holds trace_form_positive hermitian_form_symmetry_holds unitary_isometry_lattice_holds
    global_lattice_isLattice_holds (class_injective_of_span_recovery hs global_lattice_equiv_holds) scale_bound_holds
    (dual_lattice_bound_holds hs) (class_set_finite_bounded_holds covolume_of_dual_holds) standard_lattice_full_holds

end Formalism.UG.P
end
end
