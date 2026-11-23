module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModChebOm
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.TypeStar
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Mathlib.Topology.Algebra.OpenSubgroup
import ReciprocityTheory.NeutralLocalFields.HilbertClassField
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFrobCong
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGBasic
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModInertKur
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJInt
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedStatus

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFixJ

section

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem fixJ_nonunits_add {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {a b : Ω} (ha : a ∈ A.nonunits)
    (hb : b ∈ A.nonunits) : a + b ∈ A.nonunits := by
  exact add_mem ha hb

def fixJRoots {Ω : Type*} [Field Ω] (P : Polynomial ℤ) : Finset Ω := (P.map (Int.castRingHom Ω)).roots.toFinset

theorem mem_fixJRoots {Ω : Type*} [Field Ω] {P : Polynomial ℤ} (hP : P.Monic) (r : Ω) :
    r ∈ fixJRoots (Ω := Ω) P ↔ P.eval₂ (Int.castRingHom Ω) r = 0 := by
  rw [fixJRoots, Multiset.mem_toFinset, Polynomial.mem_roots (hP.map _).ne_zero, Polynomial.IsRoot.def,
    Polynomial.eval_map]

theorem map_mem_fixJRoots {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {P : Polynomial ℤ} (hP : P.Monic)
    (g : Ω ≃ₐ[E] Ω) {r : Ω} (hr : r ∈ fixJRoots (Ω := Ω) P) : g r ∈ fixJRoots (Ω := Ω) P := by
  rw [mem_fixJRoots hP] at hr ⊢
  have h := Polynomial.hom_eval₂ P (Int.castRingHom Ω) (g : Ω →+* Ω) r
  rw [hr, map_zero, RingHom.ext_int ((g : Ω →+* Ω).comp (Int.castRingHom Ω)) (Int.castRingHom Ω)] at h
  exact h.symm

theorem isIntegral_of_mem_fixJRoots {Ω : Type*} [Field Ω] {P : Polynomial ℤ} (hP : P.Monic) {r : Ω}
    (hr : r ∈ fixJRoots (Ω := Ω) P) : IsIntegral ℤ r := by
  refine ⟨P, hP, ?_⟩
  rw [algebraMap_int_eq]
  exact (mem_fixJRoots hP r).1 hr

def fixJStab (E Ω : Type*) [Field E] [Field Ω] [Algebra E Ω] (P : Polynomial ℤ) : Subgroup (Ω ≃ₐ[E] Ω) where
  carrier := {g | ∀ r ∈ fixJRoots (Ω := Ω) P, g r = r}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb r hr
    rw [AlgEquiv.mul_apply, hb r hr, ha r hr]
  inv_mem' := by
    intro a ha r hr
    have := ha r hr
    calc a⁻¹ r = a⁻¹ (a r) := by rw [this]
      _ = r := by rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl

theorem mem_fixJStab {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {P : Polynomial ℤ} {g : Ω ≃ₐ[E] Ω} :
    g ∈ fixJStab E Ω P ↔ ∀ r ∈ fixJRoots (Ω := Ω) P, g r = r := Iff.rfl

theorem fixJStab_normal {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {P : Polynomial ℤ} (hP : P.Monic) :
    (fixJStab E Ω P).Normal := by
  constructor
  intro n hn g
  rw [mem_fixJStab] at hn ⊢
  intro r hr
  have h1 : g⁻¹ r ∈ fixJRoots (Ω := Ω) P := map_mem_fixJRoots hP g⁻¹ hr
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hn _ h1, ← AlgEquiv.mul_apply, mul_inv_cancel]
  rfl

theorem fixJStab_isOpen {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] [Algebra.IsAlgebraic E Ω]
    {P : Polynomial ℤ} : IsOpen (fixJStab E Ω P : Set (Ω ≃ₐ[E] Ω)) := by
  let K : IntermediateField E Ω := IntermediateField.adjoin E ((fixJRoots (Ω := Ω) P : Finset Ω) : Set Ω)
  haveI : FiniteDimensional E K := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral)
  refine Subgroup.isOpen_mono (H₁ := K.fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen K)
  intro g hg
  rw [mem_fixJStab]
  intro r hr
  exact hg ⟨r, IntermediateField.subset_adjoin E _ hr⟩

end ReciprocityTheory.ChartRestriction.L1
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModSepInt

section

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem exists_int_multiple {Ω : Type*} [Field Ω] [CharZero Ω] {β : Ω} (hβ : IsIntegral ℤ β) (h0 : β ≠ 0) :
    ∃ (n : ℤ) (γ : Ω), n ≠ 0 ∧ IsIntegral ℤ γ ∧ (n : Ω) = β * γ := by
  obtain ⟨p, hpm, hp0⟩ := id hβ
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpm.ne_zero 0
  simp only [map_zero, sub_zero] at hpq hq
  have hq0 : q.coeff 0 ≠ 0 := fun h => hq (Polynomial.X_dvd_iff.2 h)
  have haq : Polynomial.aeval β q = 0 := by
    have h1 : Polynomial.aeval β p = 0 := by rw [Polynomial.aeval_def]; exact hp0
    rw [hpq, map_mul, map_pow, Polynomial.aeval_X] at h1
    exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ h0)
  refine ⟨q.coeff 0, -(Polynomial.aeval β q.divX), hq0, ?_, ?_⟩
  · have hmem := adjoin_le_integralClosure hβ (Polynomial.aeval_mem_adjoin_singleton ℤ β (p := q.divX))
    exact (neg_mem hmem : _ ∈ integralClosure ℤ Ω)
  · have h2 := congrArg (Polynomial.aeval β) (Polynomial.divX_mul_X_add q)
    rw [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, haq, eq_intCast] at h2
    linear_combination h2

theorem mem_valuationSubring_of_isIntegral {Ω : Type*} [Field Ω] {x : Ω} (hx : IsIntegral ℤ x)
    (A : ValuationSubring Ω) : x ∈ A := by
  have hA : IsIntegral A x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hA
  rw [← hy]
  exact y.2

theorem sepInt {Ω : Type*} [Field Ω] [CharZero Ω] (s : Finset Ω) (hs : ∀ r ∈ s, IsIntegral ℤ r) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → ∀ A : ValuationSubring Ω, r - r' ∈ A.nonunits →
      (n : Ω) ∈ A.nonunits := by
  classical
  have key : ∀ q ∈ s.offDiag, ∃ (m : ℤ) (γ : Ω), m ≠ 0 ∧ IsIntegral ℤ γ ∧ (m : Ω) = (q.1 - q.2) * γ := by
    intro q hq
    rw [Finset.mem_offDiag] at hq
    exact exists_int_multiple ((hs _ hq.1).sub (hs _ hq.2.1)) (sub_ne_zero.2 hq.2.2)
  choose! m γ hm hγ hmγ using key
  refine ⟨∏ q ∈ s.offDiag, m q, Finset.prod_ne_zero_iff.2 hm, ?_⟩
  intro r hr r' hr' hne A hA
  have hq : (r, r') ∈ s.offDiag := Finset.mem_offDiag.2 ⟨hr, hr', hne⟩
  rw [Int.cast_prod, ← Finset.mul_prod_erase _ _ hq]
  rw [ValuationSubring.mem_nonunits_iff] at hA ⊢
  rw [Valuation.map_mul, hmγ _ hq, Valuation.map_mul]
  have h1 : A.valuation (γ (r, r')) ≤ 1 :=
    (A.valuation_le_one_iff _).2 (mem_valuationSubring_of_isIntegral (hγ _ hq) A)
  have h2 : A.valuation (∏ q ∈ s.offDiag.erase (r, r'), (m q : Ω)) ≤ 1 :=
    (A.valuation_le_one_iff _).2 (prod_mem fun q _ => intCast_mem _ _)
  calc _ ≤ A.valuation (r - r') * 1 * 1 := mul_le_mul' (mul_le_mul' le_rfl h1) h2
    _ < 1 := by rw [mul_one, mul_one]; exact hA

theorem finite_places (E : Type*) [Field E] [NumberField E] {n : ℤ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 E) | (n : 𝓞 E) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {(n : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors hI).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

end ReciprocityTheory.ChartRestriction.L1
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmLatticeGoodModelUnramified

section

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField ReciprocityTheory.ChartRestriction.L1

namespace GlobalTheory.ArtinClassCM

theorem inertia_fixes (hW : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧ (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) (hC : ChebOmSt)
    {d : ℕ} {L : PeriodPair} (hsf : Squarefree d) (hd : d % 4 = 3) (hL : HasCMBy d L)
    (x : Om d) (hx : (x : ℂ) = jInv L) (B : ValuationSubring (Om d)) (σ : Om d ≃ₐ[KQ d] Om d) (hσ : InertiaEl B σ) :
    σ x = x := by
  obtain ⟨art, hop, hin, hfrob⟩ := hW (KQ d) (Om d)
  have hxi : IsIntegral ℤ x := by
    obtain ⟨y, hy, hyi⟩ := exists_Om d (cm1 d L hsf hd hL)
    have : y = x := Subtype.ext (hy.trans hx.symm)
    rwa [this] at hyi
  obtain ⟨P, hP, hPx⟩ := hxi
  have hxs : x ∈ fixJRoots (Ω := Om d) P := by
    rw [mem_fixJRoots hP]
    rwa [show algebraMap ℤ (Om d) = Int.castRingHom (Om d) from RingHom.ext_int _ _] at hPx
  obtain ⟨n, hn0, hn⟩ := sepInt (fixJRoots (Ω := Om d) P) (fun r hr => isIntegral_of_mem_fixJRoots hP hr)
  set S : Set (HeightOneSpectrum (𝓞 (KQ d))) := {v | (n : 𝓞 (KQ d)) ∈ v.asIdeal} with hS
  have hSfin : S.Finite := finite_places (KQ d) hn0

  have key : ∀ (A : ValuationSubring (Om d)) (v : HeightOneSpectrum (𝓞 (KQ d))), LiesAbove A v → v ∉ S →
      ∀ r ∈ fixJRoots (Ω := Om d) P, ∀ r' ∈ fixJRoots (Ω := Om d) P, r - r' ∈ A.nonunits → r = r' := by
    intro A v hA hv r hr r' hr' h
    by_contra hne
    have h1 := hn r hr r' hr' hne A h
    apply hv
    rw [hS, Set.mem_ofPred_eq, ← hA]
    simpa using h1
  set H : Subgroup (Om d ≃ₐ[KQ d] Om d) := art.ker ⊓ fixJStab (KQ d) (Om d) P with hH
  have := fixJStab_normal (E := KQ d) (Ω := Om d) hP
  have hHn : H.Normal := inferInstance
  have hHo : IsOpen (H : Set (Om d ≃ₐ[KQ d] Om d)) := by
    rw [hH, Subgroup.coe_inf]
    exact hop.inter fixJStab_isOpen
  obtain ⟨A, v, φ, hA, hv, hp, hφ, hσφ⟩ := hC (KQ d) (Om d) S hSfin H hHn hHo (by
    intro A v hA hv g hg
    refine ⟨hin A g hg, fun r hr => ?_⟩
    exact key A v hA hv _ (map_mem_fixJRoots hP g hr) _ hr
      (hg.2 r (mem_of_isIntegral A (isIntegral_of_mem_fixJRoots hP hr)))) σ
  have hσ1 : art σ = 1 := hin B σ hσ
  have hφ1 : art φ = 1 := by
    have : σ⁻¹ * φ ∈ art.ker := hσφ.1
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ1, inv_one, one_mul] at this
    exact this
  have hcl := hfrob v A φ hA hφ
  rw [hφ1] at hcl
  have h1 := frobCong hsf hd hL x hx A v hA hp hcl.symm
  have h2 := hφ.2 x (mem_of_isIntegral A (isIntegral_of_mem_fixJRoots hP hxs))
  have h3 : φ x - x ∈ A.nonunits := by
    have := fixJ_nonunits_add A h2 h1
    simpa using this
  have h4 : φ x = x := key A v hA hv _ (map_mem_fixJRoots hP φ hxs) _ hxs h3
  have h5 := hσφ.2 x hxs
  rw [AlgEquiv.mul_apply, h4] at h5
  calc σ x = σ (σ⁻¹ x) := by rw [h5]
    _ = x := by rw [← AlgEquiv.mul_apply, mul_inv_cancel]; rfl

theorem good_model (hW : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧ (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) (hC : ChebOmSt) : CM2 := by
  refine goodReduction_of_integral_unramified jInt ?_
  intro d L hsf hd hL l _ hl hld ι
  obtain ⟨x, hx, -⟩ := exists_Om d (cm1 d L hsf hd hL)
  rw [← hx]
  exact inertKur (by omega) hld ι x fun σ hσ => inertia_fixes hW hC hsf hd hL x hx _ σ hσ

end GlobalTheory.ArtinClassCM
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmLatticeGoodModelUnramifiedStatement

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.HilbertClassField

theorem _root_.GlobalTheory.T.cmLattice_good_model_unramified : (∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧ (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) → ReciprocityTheory.ChartRestriction.L1.ChebOmSt → Formalism.L2.Th1.CM.CM2 := by
  first | exact @GlobalTheory.ArtinClassCM.good_model | exact GlobalTheory.ArtinClassCM.good_model | (intros; apply GlobalTheory.ArtinClassCM.good_model <;> assumption)
end
end
