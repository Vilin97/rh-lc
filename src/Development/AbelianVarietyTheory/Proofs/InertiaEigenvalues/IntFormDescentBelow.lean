module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGoodOfBddAll
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalSectionBoundedNonzeroMultipleStatement
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestrictionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsAllEmbeddingsOfInclusionReadingStatement
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeDifferentOrderBoundedAbsoluteRamificatioStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupSetFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceCombinationCoverFormIntegralOverPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationMulLeOneOfTraceApproxIdempotentIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralValuesAlgebraicPointsIffValueNonneg
public import Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanSteps
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CompIntField

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisBoundedModuleValuationRingPi

section

@[expose] public section

open IsDedekindDomain NumberField

namespace GlobalTheory

theorem locBasis_of_bounded {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (d : ℕ) (M : Set (Fin d → F)) (h0 : (0 : Fin d → F) ∈ M)
    (hadd : ∀ x ∈ M, ∀ y ∈ M, x + y ∈ M)
    (hsmul : ∀ a : F, p.valuation F a ≤ 1 → ∀ x ∈ M, a • x ∈ M)
    (hstd : ∀ i, Pi.single i 1 ∈ M)
    (hbd : ∃ D : F, D ≠ 0 ∧ ∀ x ∈ M, ∀ i, p.valuation F (D * x i) ≤ 1) :
    ∃ (m : ℕ) (b : Fin m → Fin d → F), (∀ k, b k ∈ M) ∧
      (∀ x ∈ M, ∃ a : Fin m → F, (∀ k, p.valuation F (a k) ≤ 1) ∧ x = ∑ k, a k • b k) ∧
      LinearIndependent F b := by
  obtain ⟨D, hD, hDM⟩ := hbd
  set A : ValuationSubring F := p.valuationSubringAtPrime F with hA
  haveI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F) p.ne_bot _
  have memA : ∀ a : F, a ∈ A ↔ p.valuation F a ≤ 1 := by
    intro a
    rw [hA, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff]
  let M' : Submodule A (Fin d → F) :=
    { carrier := M
      add_mem' := fun {x y} hx hy => hadd x hx y hy
      zero_mem' := h0
      smul_mem' := fun c x hx => by
        have : c • x = (c : F) • x := rfl
        rw [this]
        exact hsmul _ ((memA _).1 c.2) x hx }
  let e : Fin d → Fin d → F := fun i => D⁻¹ • Pi.single i 1
  have heF : LinearIndependent F e := by
    have h1 := (Pi.basisFun F (Fin d)).linearIndependent.units_smul
      (fun _ => Units.mk0 D⁻¹ (inv_ne_zero hD))
    convert h1 using 1
    ext i j
    simp [e, Pi.basisFun_apply]
  have heA : LinearIndependent A e := (LinearIndependent.iff_fractionRing A F).2 heF
  have hle : M' ≤ Submodule.span A (Set.range e) := by
    intro x hx
    have hx' : x = ∑ i, (D * x i) • e i := by
      ext j
      simp [e, Finset.sum_apply, Pi.single_apply]
      rw [mul_comm D, mul_assoc, mul_inv_cancel₀ hD, mul_one]
    rw [hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    have hc : D * x i ∈ A := (memA _).2 (hDM x hx i)
    have : (D * x i) • e i = (⟨D * x i, hc⟩ : A) • e i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨n, bas⟩ := Submodule.basisOfPidOfLE hle (Module.Basis.span heA)
  refine ⟨n, fun k => (bas k : Fin d → F), fun k => (bas k).2, ?_, ?_⟩
  · intro x hx
    refine ⟨fun k => (bas.repr ⟨x, hx⟩ k : F), fun k => (memA _).1 (bas.repr ⟨x, hx⟩ k).2, ?_⟩
    have h := congrArg (fun y : M' => (y : Fin d → F)) (bas.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  · have h1 : LinearIndependent A (M'.subtype ∘ bas) :=
      bas.linearIndependent.map' M'.subtype (Submodule.ker_subtype M')
    exact (LinearIndependent.iff_fractionRing A F).1 h1

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisBoundedModuleValuationRingPiStatement

section

@[expose] public section

open IsDedekindDomain NumberField

theorem _root_.GlobalTheory.T.exists_basis_bounded_module_valuationRing_pi : ∀ {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) (d : ℕ) (M : Set (Fin d → F)), (0 : Fin d → F) ∈ M → (∀ x ∈ M, ∀ y ∈ M, x + y ∈ M) → (∀ a : F, p.valuation F a ≤ 1 → ∀ x ∈ M, a • x ∈ M) → (∀ i, Pi.single i 1 ∈ M) → (∃ D : F, D ≠ 0 ∧ ∀ x ∈ M, ∀ i, p.valuation F (D * x i) ≤ 1) → ∃ (m : ℕ) (b : Fin m → Fin d → F), (∀ k, b k ∈ M) ∧ (∀ x ∈ M, ∃ a : Fin m → F, (∀ k, p.valuation F (a k) ≤ 1) ∧ x = ∑ k, a k • b k) ∧ LinearIndependent F b := by
  first | exact @GlobalTheory.locBasis_of_bounded | exact GlobalTheory.locBasis_of_bounded | (intros; apply GlobalTheory.locBasis_of_bounded <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastPowMulValuationLeOneOfNotPowSuccDvdDiffer

section

@[expose] public section

open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory

theorem natCast_pow_mul_valuation_le_one_of_not_pow_succ_dvd_differentIdeal :
    ∀ (l c : ℕ) (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      (la : HeightOneSpectrum (𝓞 L)), ((l : ℕ) : 𝓞 L) ∈ la.asIdeal →
      ¬ la.asIdeal ^ (c + 1) ∣ differentIdeal (𝓞 K) (𝓞 L) →
      ∀ y : L, (∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), la.valuation L (y * (d : L)) ≤ 1) →
        la.valuation L ((l : L) ^ c * y) ≤ 1 := by
  intro l c K L _ _ _ _ _ la hl hD y hy
  obtain ⟨d₀, hd₀D, hd₀⟩ : ∃ d₀ ∈ differentIdeal (𝓞 K) (𝓞 L), d₀ ∉ la.asIdeal ^ (c + 1) := by
    by_contra h
    push_neg at h
    exact hD (Ideal.dvd_iff_le.mpr h)
  have h1 : la.intValuation ((l : 𝓞 L) ^ c) ≤ WithZero.exp (-(c : ℤ)) :=
    (la.intValuation_le_pow_iff_mem _ c).mpr (Ideal.pow_mem_pow hl c)
  have h2 : WithZero.exp (-(c : ℤ)) ≤ la.intValuation d₀ := by
    rw [HeightOneSpectrum.exp_le_intValuation_iff_emultiplicity_le]
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem la,
      HeightOneSpectrum.intValuation_le_exp_iff_le_emultiplicity, not_le] at hd₀
    rw [← ENat.lt_natCast_add_one_iff]
    exact_mod_cast hd₀
  have hyd := hy d₀ hd₀D
  have e1 : la.valuation L (d₀ : L) = la.intValuation d₀ := la.valuation_of_algebraMap (K := L) d₀
  have e2 : la.valuation L ((l : L) ^ c) = la.intValuation ((l : 𝓞 L) ^ c) := by
    rw [← la.valuation_of_algebraMap (K := L)]
    simp
  rw [Valuation.map_mul] at hyd ⊢
  calc la.valuation L ((l : L) ^ c) * la.valuation L y
      ≤ la.valuation L (d₀ : L) * la.valuation L y := by
        gcongr
        rw [e1, e2]
        exact h1.trans h2
    _ = la.valuation L y * la.valuation L (d₀ : L) := mul_comm _ _
    _ ≤ 1 := hyd

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastPowMulValuationLeOneOfNotPowSuccDvdDifferStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open Classical

theorem _root_.GlobalTheory.T.valuation_prime_pow_mul_le_one_of_not_dvd_different : ∀ (l c : ℕ) (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (la : HeightOneSpectrum (𝓞 L)), ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → ¬ la.asIdeal ^ (c + 1) ∣ differentIdeal (𝓞 K) (𝓞 L) → ∀ y : L, (∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), la.valuation L (y * (d : L)) ≤ 1) → la.valuation L ((l : L) ^ c * y) ≤ 1 := by
  first | exact @GlobalTheory.natCast_pow_mul_valuation_le_one_of_not_pow_succ_dvd_differentIdeal | exact GlobalTheory.natCast_pow_mul_valuation_le_one_of_not_pow_succ_dvd_differentIdeal | (intros; apply GlobalTheory.natCast_pow_mul_valuation_le_one_of_not_pow_succ_dvd_differentIdeal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationMulLeOneOfTraceApproxIdempotentIntegralStatement

section

@[expose] public section

open NumberField IsDedekindDomain
open Classical

theorem _root_.GlobalTheory.T.valuation_mul_le_one_of_trace_approxIdempotent_integral : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (la : HeightOneSpectrum (𝓞 L)) (p : HeightOneSpectrum (𝓞 K)), la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ y : L, (∃ N : ℕ, ∀ b : 𝓞 L, (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal → b ∈ la'.asIdeal ^ N) → p.valuation K (Algebra.trace K L ((b : L) * y)) ≤ 1) → ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), la.valuation L (y * (d : L)) ≤ 1 := by
  first | exact @GlobalTheory.InvDiffLocal.valuation_mul_different_le_one | exact GlobalTheory.InvDiffLocal.valuation_mul_different_le_one | (intros; apply GlobalTheory.InvDiffLocal.valuation_mul_different_le_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntFormDescentBelow

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.XiIntSteps

theorem exists_local_basis {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) {V : Type} [AddCommGroup V]
    [Module F V] (C : Submodule F V) [FiniteDimensional F C] (Int : V → Prop) (h0 : Int 0)
    (hadd : ∀ f g, Int f → Int g → Int (f + g)) (hsmul : ∀ (a : F) f, p.valuation F a ≤ 1 → Int f → Int (a • f))
    (hbd : ∀ f ∈ C, ∃ κ : F, κ ≠ 0 ∧ Int (κ • f)) {M : ℕ} (g : Fin M → V) (hg : ∀ i, g i ∈ C)
    (hgen : ∀ f ∈ C, Int f → ∃ o : Fin M → F, (∀ i, p.valuation F (o i) ≤ 1) ∧ f = ∑ i, o i • g i) :
    ∃ (m : ℕ) (β : Fin m → V), (∀ k, β k ∈ C ∧ Int (β k)) ∧ (∀ f ∈ C, ∃ c : Fin m → F, f = ∑ k, c k • β k) ∧
      ∀ c : Fin m → F, Int (∑ k, c k • β k) → ∀ k, p.valuation F (c k) ≤ 1 := by
  classical
  let B₀ := Module.finBasis F C
  choose κ hκ0 hκ using fun i => hbd (B₀ i : V) (B₀ i).2
  let B := B₀.unitsSMul fun i => Units.mk0 (κ i) (hκ0 i)
  have hB : ∀ i, ((B i : C) : V) = κ i • (B₀ i : V) := fun i => by
    simp [B, Module.Basis.unitsSMul_apply, Units.smul_def]
  let e : (Fin (Module.finrank F C) → F) →ₗ[F] V := C.subtype ∘ₗ (B.equivFun.symm : _ →ₗ[F] C)
  have heC : ∀ x, e x ∈ C := fun x => (B.equivFun.symm x).2
  have he1 : ∀ f : C, e (B.equivFun f) = f := fun f => by simp [e]
  have heinj : Function.Injective e := Subtype.val_injective.comp B.equivFun.symm.injective
  have hsingle : ∀ i, e (Pi.single i 1) = κ i • (B₀ i : V) := fun i => by
    rw [← hB, ← he1 (B i)]
    congr 1
    funext k
    simp [Module.Basis.equivFun_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
  let S : Set (Fin (Module.finrank F C) → F) := {x | Int (e x)}
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F))
    (fun ki : Fin M × Fin (Module.finrank F C) => B.equivFun ⟨g ki.1, hg ki.1⟩ ki.2)
  have hvle : ∀ s : 𝓞 F, p.valuation F (algebraMap (𝓞 F) F s) ≤ 1 := fun s => by
    rw [HeightOneSpectrum.valuation_of_algebraMap]; exact p.intValuation_le_one s
  obtain ⟨m, b, hbM, hbsp, hbli⟩ := GlobalTheory.T.exists_basis_bounded_module_valuationRing_pi p _ S (by show Int (e 0); rw [map_zero]; exact h0)
    (fun x hx y hy => by show Int (e (x + y)); rw [map_add (f := _)]; exact hadd _ _ hx hy)
    (fun a ha x hx => by show Int (e (a • x)); rw [map_smul]; exact hsmul _ _ ha hx)
    (fun i => by show Int (e _); rw [hsingle]; exact hκ i)
    ⟨algebraMap (𝓞 F) F d, (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (nonZeroDivisors.coe_ne_zero d),
      fun x hx i => by
        obtain ⟨o, ho, hxo⟩ := hgen (e x) (heC x) hx
        have hx' : x = ∑ k, o k • B.equivFun ⟨g k, hg k⟩ := heinj (by

          rw [hxo, map_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [map_smul, he1])
        rw [hx', Finset.sum_apply, Finset.mul_sum]
        refine Valuation.map_sum_le _ fun k _ => ?_
        obtain ⟨r, hr⟩ := hd (k, i)
        rw [Pi.smul_apply, smul_eq_mul, mul_left_comm, map_mul, ← Algebra.smul_def]
        refine mul_le_one' (ho k) ?_
        rw [← hr]
        exact hvle r⟩
  refine ⟨m, fun k => e (b k), fun k => ⟨heC _, hbM k⟩, fun f hf => ?_, fun c hc k => ?_⟩
  · have hxsp : B.equivFun ⟨f, hf⟩ ∈ Submodule.span F (Set.range b) := by
      rw [← Finset.univ_sum_single (B.equivFun ⟨f, hf⟩)]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : Pi.single i (B.equivFun ⟨f, hf⟩ i) = B.equivFun ⟨f, hf⟩ i • (Pi.single i (1 : F) : Fin _ → F) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this]
      refine Submodule.smul_mem _ _ ?_
      obtain ⟨a, -, ha⟩ := hbsp (Pi.single i 1) (by show Int (e _); rw [hsingle]; exact hκ i)
      rw [ha]; exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hxsp
    refine ⟨c, ?_⟩
    have := he1 ⟨f, hf⟩

    rw [← hc, map_sum] at this
    exact this.symm.trans (Finset.sum_congr rfl fun k _ => map_smul _ _ _)
  · have hy : (∑ k, c k • b k) ∈ S := by
      show Int (e _)
      convert hc using 1

      rw [map_sum]; exact Finset.sum_congr rfl fun k _ => map_smul _ _ _
    obtain ⟨a, ha, hya⟩ := hbsp _ hy
    have hz : ∑ k, (c k - a k) • b k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]; rw [← hya, sub_self]
    rw [sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hbli _ hz k)]
    exact ha k

theorem intForm_descent_below (l e : ℕ) (hl : l.Prime) : ∃ c₀ : ℕ, ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j →
    ∀ w : WeightFamilies.Wt D j, w.LastPos → Dom (wtA w) w.n →
    holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) ≤ Submodule.span ℂ (rdU (T.U j T.σ₀) ''
      {f | f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧ rdU (T.U j T.σ₀) f ∈ holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n)}) →
    (∀ k ∈ T.Kf j T.σ₀, ∀ h, T.mu j T.σ₀ (h * k) = T.mu j T.σ₀ h) →
    ∀ C : Cover T j T.σ₀, C.IsUnif → C.IsPinned (wtA w) w.n →
    ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (p : HeightOneSpectrum (𝓞 T.Q.c.F)),
      la.asIdeal.comap (RingOfIntegers.mapRingHom C.inc) = p.asIdeal →
      ((l : ℕ) : 𝓞 C.d.c₂.F) ∈ la.asIdeal → ((l : ℕ) : 𝓞 C.d.c₂.F) ∉ la.asIdeal ^ (e + 1) →
      ∀ φ ∈ C.intForms (wtA w) w.n {la}, (∀ k ∈ T.Kf j T.σ₀, ∀ h, φ (h * k) = φ h) →
        ∃ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V j T.σ₀) → ℂ)), (∀ i, la.valuation C.d.c₂.F (x i) ≤ 1) ∧
          (∀ i, ψ i ∈ baseInt T j T.σ₀ (wtA w) w.n {p}) ∧ ((l : ℂ) ^ c₀) • φ = ∑ i, C.σ₂ (x i) • ψ i := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.relative_different_order_bounded_absolute_ramification l e hl
  refine ⟨c, ?_⟩
  intro D T hL j hj w hlast hD hspan hK C hU hP la p hp0 hl1 hl2 φ hφ hφK
  letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra
  have hp : la.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal := by
    rw [← hp0]; ext x; rfl
  have hσ := T.toCore.good_σ₀
  have hlp : ((l : ℕ) : 𝓞 T.Q.c.F) ∈ p.asIdeal := by
    rw [← hp0, Ideal.mem_comap, map_natCast]; exact hl1
  have hgood : T.Q.l.GoodAt l :=
    Formalism.L2.Pj.goodAt_of_two_primes hL.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne l hl
  have hfd := hL.cuspFD _ hj _ _ hD
  obtain ⟨M, g, hg, hgen⟩ := GlobalTheory.SupFinite.supSet_finitelyGenerated _ _ _ _ (T.Q.Xo j) T.Q.c _ (T.U j) (hL.unf _ hj) p l hl hlp
    hgood (wtA w) w.n hD hfd
  have hval := GlobalTheory.TowVal.bddAll_one_iff_valSet_nonneg _ _ _ _ (T.Q.Xo j) T.Q.c p
  obtain ⟨m, β, hβ, hspanβ, hprim⟩ := exists_local_basis p (cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n)
    (GlobalTheory.GoodPts.BddAll (T.Q.Xo j) T.Q.c p 1)
    ((hval 0).2 (by rintro _ ⟨y, rfl⟩; rw [vAtV_zero]; exact le_top))
    (fun f g => GlobalTheory.GoodPtsModel.bddAll_add)
    (fun a f ha hf => by
      by_cases h0 : a = 0
      · subst h0
        set_option synthInstance.maxHeartbeats 100000 in
          rw [zero_smul]
        exact (hval 0).2 (by rintro _ ⟨y, rfl⟩; rw [vAtV_zero]; exact le_top)
      have hv : (0 : ℤ) ≤ vLa p a := by
        have hne : p.valuation T.Q.c.F a ≠ 0 := (Valuation.ne_zero_iff _).2 h0
        have := (WithZero.log_le_log hne one_ne_zero).2 ha
        simp only [WithZero.log_one] at this
        simp only [vLa]; omega
      exact (GlobalTheory.GoodPtsModel.smul_mem_supSet (W := ⊤) hv ⟨trivial, hf⟩).2)
    (fun f hf => by
      obtain ⟨κ, h1, h2⟩ := GlobalTheory.T.cuspidal_section_bounded_nonzero_multiple _ _ _ _ (T.Q.Xo j) T.Q.c _ (T.U j) (hL.unf _ hj) p l hl hlp hgood (wtA w) w.n f hD hf
      exact ⟨κ, h1, (GlobalTheory.GoodPtsModel.bddAll_iff_smul _ _).1 h2⟩)
    g (fun i => (hg i).1) (fun f hf hb => hgen f ⟨hf, hb⟩)
  have hβs : ∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧
      rdU (T.U j T.σ₀) (β k) ∈ holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) := fun k =>
    ⟨cusp_le_sec _ _ _ _ _ (hβ k).1, ReciprocityTheory.ChartRestriction.G.PullbackSections.rdC_mem_holSub0 T.good_σ₀ (wtA w) w.n ⟨β k, (hβ k).1⟩⟩
  obtain ⟨m', x, ψ, hψ, hφe⟩ := GlobalTheory.T.holomorphic_sections_span_restriction D T hL j hj T.σ₀ hσ C hU _ _ hD hP hspan hK φ
    (C.intForms_subset _ _ _ hφ) hφK
  have hcc' : ∀ i, ∃ cc : Fin m → T.Q.c.F, ψ i = ∑ k, T.σ₀ (cc k) • T.phiJ j T.σ₀ (wtA w) (β k) := fun i => by
    obtain ⟨f, hf, hfe⟩ := hψ i
    obtain ⟨cc, hcc⟩ := hspanβ f (GlobalTheory.T.mem_cuspForms_allEmbeddings_of_inclusion_reading D T hL j hj w hlast f hf.1 hf.2)
    refine ⟨cc, ?_⟩
    rw [← hfe, hcc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [CoreJ.phiJ, map_sum, map_smulₛₗ, map_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  choose cc hcc using hcc'
  have hσ₂ : ∀ z, C.σ₂ (C.inc z) = T.σ₀ z := fun z => congrArg (fun f => f z) hU.2.2.1
  let y : Fin m → C.d.c₂.F := fun k => ∑ i, x i * C.inc (cc i k)
  have hsum : φ = ∑ k, C.σ₂ (y k) • T.phiJ j T.σ₀ (wtA w) (β k) := by
    rw [hφe]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, hcc, Finset.smul_sum, smul_smul, map_sum, Finset.sum_smul, map_mul, hσ₂]
    exact Finset.sum_comm
  have hφ' : (∑ k, C.σ₂ (y k) • T.phiJ j T.σ₀ (wtA w) (β k)) ∈ C.intForms (wtA w) w.n {la} := hsum ▸ hφ
  obtain ⟨N, hN⟩ := GlobalTheory.T.traceCombination_coverForm_integral_over_prime D T hL j hj T.σ₀ hσ _ _ hD hspan hK C hU hP la p hp m β hβs
    (fun k => (hval _).1 (hβ k).2) y hφ'
  have hdiff : ∀ k, ∀ d ∈ differentIdeal (𝓞 T.Q.c.F) (𝓞 C.d.c₂.F),
      la.valuation C.d.c₂.F (y k * (d : C.d.c₂.F)) ≤ 1 := fun k =>
    GlobalTheory.T.valuation_mul_le_one_of_trace_approxIdempotent_integral T.Q.c.F C.d.c₂.F la p hp (y k)
      ⟨N, fun b hb => hprim (fun k => Algebra.trace T.Q.c.F C.d.c₂.F ((b : C.d.c₂.F) * y k)) ((hval _).2 (hN b hb)) k⟩
  have hcd := hc T.Q.c.F C.d.c₂.F p la hp hl1 hl2
  refine ⟨m, fun k => (l : C.d.c₂.F) ^ c * y k, fun k => T.phiJ j T.σ₀ (wtA w) (β k), ?_, ?_, ?_⟩
  · exact fun k => GlobalTheory.T.valuation_prime_pow_mul_le_one_of_not_dvd_different l c T.Q.c.F C.d.c₂.F la hl1 hcd (y k) (hdiff k)
  · refine fun k => ⟨β k, ⟨(hβs k).1, (hβs k).2, fun q hq => ?_⟩, rfl⟩
    rw [Set.mem_singleton_iff.1 hq]
    exact (hval _).1 (hβ k).2
  · rw [hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, map_mul, map_pow, map_natCast]

end GlobalTheory.XiIntSteps
end
end
end
