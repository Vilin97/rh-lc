module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Algebra.Algebra.Equiv
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHahnSeriesScaleTwistRingHomStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInjectiveCuspExpansionRingHomStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivCoeffConjStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpPropsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSomeLevelOverCompGLTwoPosRatStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpTwoPiIRatInFieldRootsOfUnityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOverStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicMulEqZeroIffStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnitsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrictStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFractionFieldExtensionOfMaps

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fraction_field_extension : ∀ (Ω R L M : Type) [Field Ω] [CommRing R] [IsDomain R] [Field L] [Algebra Ω L] [CommRing M] (G S : Type) (c : Ω →+* R) (e : R →+* L) (sl : G → R ≃+* R) (ga : S → R ≃+* R) (A : R →+* M), Function.Injective e → (∀ x, e (c x) = algebraMap Ω L x) → (∀ g x, sl g (c x) = c x) → (∀ a, a ≠ 0 → IsUnit (A a)) → ∃ (K : Type) (_ : Field K) (_ : Algebra Ω K) (io : R →+* K) (e' : K →ₐ[Ω] L) (sl' : G → K ≃ₐ[Ω] K) (ga' : S → K ≃+* K) (A' : K →+* M), Function.Injective io ∧ (∀ f : K, ∃ a b : R, b ≠ 0 ∧ f * io b = io a) ∧ (∀ x, io (c x) = algebraMap Ω K x) ∧ (∀ a, e' (io a) = e a) ∧ (∀ g a, sl' g (io a) = io (sl g a)) ∧ (∀ s a, ga' s (io a) = io (ga s a)) ∧ ∀ a, A' (io a) = A a := by
  intro Ω R L M _ _ _ _ _ _ G S c e sl ga A he hce hsl hA
  letI alg : Algebra Ω (FractionRing R) := ((algebraMap R (FractionRing R)).comp c).toAlgebra
  have hΩ : ∀ x, algebraMap Ω (FractionRing R) x = algebraMap R (FractionRing R) (c x) := fun _ => rfl
  let e0 : FractionRing R →+* L := IsFractionRing.lift he
  have he0 : ∀ a, e0 (algebraMap R (FractionRing R) a) = e a := fun a => IsFractionRing.lift_algebraMap he a
  have hcom : ∀ x, e0 (algebraMap Ω (FractionRing R) x) = algebraMap Ω L x := fun x => by
    rw [hΩ, he0, hce]
  let e' : FractionRing R →ₐ[Ω] L :=
    { e0 with commutes' := hcom }
  let s0 : G → FractionRing R ≃+* FractionRing R := fun g => IsFractionRing.ringEquivOfRingEquiv (sl g)
  have hs0 : ∀ g a, s0 g (algebraMap R (FractionRing R) a) = algebraMap R (FractionRing R) (sl g a) :=
    fun g a => IsFractionRing.ringEquivOfRingEquiv_algebraMap (sl g) a
  let sl' : G → FractionRing R ≃ₐ[Ω] FractionRing R := fun g =>
    AlgEquiv.ofRingEquiv (f := s0 g) (fun x => by rw [hΩ, hs0, hsl])
  let ga' : S → FractionRing R ≃+* FractionRing R := fun s => IsFractionRing.ringEquivOfRingEquiv (ga s)
  have hunit : ∀ y : nonZeroDivisors R, IsUnit (A y) := fun y =>
    hA y (nonZeroDivisors.ne_zero y.2)
  let A' : FractionRing R →+* M := IsLocalization.lift (M := nonZeroDivisors R) hunit
  refine ⟨FractionRing R, inferInstance, alg, algebraMap R (FractionRing R), e', sl', ga', A',
    IsFractionRing.injective R (FractionRing R), ?_, fun x => (hΩ x).symm, he0, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective R f
    refine ⟨x, y, nonZeroDivisors.ne_zero hy, ?_⟩
    have hy' : algebraMap R (FractionRing R) y ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    rw [← hxy, div_mul_cancel₀ _ hy']
  · intro g a
    exact hs0 g a
  · intro s a
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (ga s) a
  · intro a
    exact IsLocalization.lift_eq hunit a

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFractionFieldExtensionOfMapsStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_fractionField_extension_of_maps : ∀ (Ω R L M : Type) [Field Ω] [CommRing R] [IsDomain R] [Field L] [Algebra Ω L] [CommRing M] (G S : Type) (c : Ω →+* R) (e : R →+* L) (sl : G → R ≃+* R) (ga : S → R ≃+* R) (A : R →+* M), Function.Injective e → (∀ x, e (c x) = algebraMap Ω L x) → (∀ g x, sl g (c x) = c x) → (∀ a, a ≠ 0 → IsUnit (A a)) → ∃ (K : Type) (_ : Field K) (_ : Algebra Ω K) (io : R →+* K) (e' : K →ₐ[Ω] L) (sl' : G → K ≃ₐ[Ω] K) (ga' : S → K ≃+* K) (A' : K →+* M), Function.Injective io ∧ (∀ f : K, ∃ a b : R, b ≠ 0 ∧ f * io b = io a) ∧ (∀ x, io (c x) = algebraMap Ω K x) ∧ (∀ a, e' (io a) = e a) ∧ (∀ g a, sl' g (io a) = io (sl g a)) ∧ (∀ s a, ga' s (io a) = io (ga s a)) ∧ ∀ a, A' (io a) = A a := by
  first | exact @GlobalTheory.fraction_field_extension | exact GlobalTheory.fraction_field_extension | (intros; apply GlobalTheory.fraction_field_extension <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivCompGLTwoPosRatFun

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem cmp_mem_ring (E : Subring ℂ) (g : GQ)
    (hE : ∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) {f : ℍ → ℂ} (hf : f ∈ ring E) :
    cmp g f ∈ ring E :=
  ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver E).1 _).2 (GlobalTheory.T.hasSomeLevelOver_compGLTwoPosRat E g f hE (((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver E).1 f).1 hf))

noncomputable def cmpHom (E : Subring ℂ) (g : GQ)
    (hE : ∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) : ring E →+* ring E where
  toFun a := ⟨cmp g a, cmp_mem_ring E g hE a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem cmp_cmp_inv (g : GQ) (f : ℍ → ℂ) : cmp g (cmp g⁻¹ f) = f := by
  rw [← GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.2.1, inv_mul_cancel, GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.1]

theorem cmp_inv_cmp (g : GQ) (f : ℍ → ℂ) : cmp g⁻¹ (cmp g f) = f := by
  rw [← GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.2.1, mul_inv_cancel, GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.1]

theorem cmp_ringEquiv : ∀ (E : Subring ℂ) (g : GQ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) →
    ∃ σ : GlobalTheory.FN.ring E ≃+* GlobalTheory.FN.ring E, ∀ a, ((σ a : GlobalTheory.FN.ring E) : ℍ → ℂ) = GlobalTheory.FN.cmp g a := by
  intro E g hE
  refine ⟨{ cmpHom E g hE with
    invFun := cmpHom E g⁻¹ hE
    left_inv := fun a => Subtype.ext (cmp_inv_cmp g a)
    right_inv := fun a => Subtype.ext (cmp_cmp_inv g a) }, fun a => rfl⟩

end GlobalTheory.FN
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivCompGLTwoPosRatFunStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_ringEquiv_compGLTwoPosRatFun : ∀ (E : Subring ℂ) (g : GQ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → ∃ σ : GlobalTheory.FN.ring E ≃+* GlobalTheory.FN.ring E, ∀ a, ((σ a : GlobalTheory.FN.ring E) : ℍ → ℂ) = GlobalTheory.FN.cmp g a := by
  first | exact @GlobalTheory.FN.cmp_ringEquiv | exact GlobalTheory.FN.cmp_ringEquiv | (intros; apply GlobalTheory.FN.cmp_ringEquiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionRingOverIsDomain

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem ring_isDomain : ∀ E : Subring ℂ, IsDomain (GlobalTheory.FN.ring E) := by
  intro E
  haveI : Nontrivial (GlobalTheory.FN.ring E) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 := congrArg (fun x : GlobalTheory.FN.ring E => (x : ℍ → ℂ) UpperHalfPlane.I) h
    simp at h1
  haveI : NoZeroDivisors (GlobalTheory.FN.ring E) := by
    refine ⟨fun {a b} hab => ?_⟩
    have hmem := (GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver E).1
    have ha := GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver E a ((hmem a).1 a.2)
    have hb := GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver E b ((hmem b).1 b.2)
    have h0 : ∀ τ, (a : ℍ → ℂ) τ * (b : ℍ → ℂ) τ = 0 := by
      intro τ
      have := congrArg (fun x : GlobalTheory.FN.ring E => (x : ℍ → ℂ) τ) hab
      simpa using this
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff a b ha hb h0 with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  exact NoZeroDivisors.to_isDomain _

end GlobalTheory.FN
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionRingOverIsDomainStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.modularFunctionRingOver_isDomain : ∀ E : Subring ℂ, IsDomain (GlobalTheory.FN.ring E) := by
  first | exact @GlobalTheory.FN.ring_isDomain | exact GlobalTheory.FN.ring_isDomain | (intros; apply GlobalTheory.FN.ring_isDomain <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldNonempty

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_nonempty : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ),
    Nonempty (Frac Ω ε) := by
  intro Ω _ _ _ ε
  classical
  haveI : IsDomain (ring ε.range) := GlobalTheory.T.modularFunctionRingOver_isDomain ε.range
  obtain ⟨hmem, hconst⟩ := GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range
  obtain ⟨-, huniq, hC, -, -⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  obtain ⟨e, he_inj, he_exp⟩ := GlobalTheory.T.exists_injective_cuspExpansion_ringHom Ω ε
  obtain ⟨hexp_mem, -, -, -, -, -⟩ := GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε
  obtain ⟨⟨G, hG⟩, hmd, -, -, hHs⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  obtain ⟨-, hid, hunit⟩ := GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units

  let cst : Ω →+* ring ε.range :=
    { toFun := fun x => ⟨fun _ => ε x, (hmem _).2 (hconst _ ⟨x, rfl⟩)⟩
      map_one' := Subtype.ext (funext fun _ => by simp)
      map_mul' := fun x y => Subtype.ext (funext fun _ => by simp)
      map_zero' := Subtype.ext (funext fun _ => by simp)
      map_add' := fun x y => Subtype.ext (funext fun _ => by simp) }
  have hcst : ∀ x, ((cst x : ring ε.range) : ℍ → ℂ) = fun _ => ε x := fun _ => rfl
  have hec : ∀ x, e (cst x) = algebraMap Ω (HahnSeries ℚ Ω) x := by
    intro x
    refine huniq _ _ _ (he_exp (cst x)) ?_
    simpa [hcst, HahnSeries.algebraMap_apply'] using hC x

  have hsl := fun g : GQ => GlobalTheory.T.exists_ringEquiv_compGLTwoPosRatFun ε.range g hexp_mem
  choose σ hσ using hsl
  have hslc : ∀ g x, σ g (cst x) = cst x := by
    intro g x
    apply Subtype.ext
    rw [hσ]
    rfl

  have hga := fun s : Ω ≃ₐ[ℚ] Ω => GlobalTheory.T.exists_ringEquiv_fn_ring_coeff_eq_apply Ω ε s.toRingEquiv
  choose τ hτ using hga

  let A : ring ε.range →+* Mero := G.comp (ring ε.range).subtype
  have hA : ∀ a : ring ε.range, A a = ((up (a : ℍ → ℂ) : ℂ → ℂ) : Mero) := fun a => hG a
  have hdiff : ∀ a : ring ε.range, DifferentiableOn ℂ (up (a : ℍ → ℂ)) Hs :=
    fun a => (hmd _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ ((hmem _).1 a.2))
  have hAunit : ∀ a, a ≠ 0 → IsUnit (A a) := by
    intro a ha
    rw [hA]
    refine (hunit _ (hdiff a) ?_).2
    intro h0
    apply ha
    have h0' : ((up (a : ℍ → ℂ) : ℂ → ℂ) : Mero) = ((up ((0 : ring ε.range) : ℍ → ℂ) : ℂ → ℂ) : Mero) := by
      rw [h0, ← hA, map_zero]
    have heq := hid _ _ (hdiff a) (hdiff 0) h0'
    apply Subtype.ext
    funext t
    have := heq t (hHs t)
    simpa [up, UpperHalfPlane.ofComplex_apply] using this
  obtain ⟨K, fK, aK, io, e', sl', ga', A', hinj, hsurj, hioc, he', hsl', hga', hA'⟩ :=
    GlobalTheory.T.exists_fractionField_extension_of_maps Ω (ring ε.range) (HahnSeries ℚ Ω) Mero GQ (Ω ≃ₐ[ℚ] Ω) cst e σ τ A he_inj hec hslc hAunit
  refine ⟨{
    K := K
    fld := fK
    alg := aK
    io := io
    io_inj := hinj
    io_surj := hsurj
    io_c := fun x a ha => ?_
    exp := e'
    exp_io := fun a => ?_
    sl := sl'
    sl_io := fun g a a' ha => ?_
    gal := ga'
    gal_exp := fun s f r => ?_
    an := A'
    an_io := fun a => ?_ }⟩
  · have : a = cst x := Subtype.ext ha
    rw [this, hioc]
  · rw [he']
    exact he_exp a
  · rw [hsl']
    congr 1
    exact Subtype.ext ((hσ g a).trans ha.symm)
  · obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω (s : Ω →+* Ω) 1 (fun _ => 1) one_pos rfl (fun _ _ => (mul_one 1).symm)
    have hΦ' : ∀ h r, (Φ h).coeff r = s (h.coeff r) := by
      intro h r
      have := hΦ h r
      simpa using this
    have key : ∀ a, e' (ga' s (io a)) = Φ (e' (io a)) := by
      intro a
      rw [hga', he', he']
      ext r
      rw [hτ s a (e a) (e (τ s a)) (he_exp a) (he_exp _) r, hΦ']
      rfl
    obtain ⟨a, b, hb, hf⟩ := hsurj f
    have hib : io b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    have hf' : f = io a * (io b)⁻¹ := by rw [← hf, mul_assoc, mul_inv_cancel₀ hib, mul_one]
    have hfe : e' (ga' s f) = Φ (e' f) := by
      rw [hf']
      simp only [map_mul, map_inv₀, key]
    rw [hfe, hΦ']
  · rw [hA', hA]
    rfl

end GlobalTheory.FN
end
end
