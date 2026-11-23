module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleTransportConjugation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompare
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldExtensionOfIntegralRetraction

section

@[expose] public section

open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc

noncomputable section

namespace GlobalTheory.UseLoc.ExtRet

variable {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l}

theorem algebraMap_ne_zero (LL : FinExt l) {d : ℤ_[l]} (hd : d ≠ 0) : algebraMap ℤ_[l] LL.1 d ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] LL.1]
  intro h0
  apply hd
  have h1 : algebraMap ℤ_[l] ℚ_[l] d = 0 := (map_eq_zero_iff _ (algebraMap ℚ_[l] LL.1).injective).1 h0
  exact (map_eq_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).1 h1

theorem exists_mul (LL : FinExt l) (x : LL.1) : ∃ d : ℤ_[l], d ≠ 0 ∧ IsIntegral ℤ_[l] (d • x) := by
  haveI := LL.2
  haveI : Algebra.IsAlgebraic ℤ_[l] LL.1 :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ_[l]) (K := ℚ_[l]) (C := LL.1)).2 inferInstance
  exact (Algebra.IsAlgebraic.isAlgebraic x).exists_integral_multiple

theorem r_smul (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (c : ℤ_[l]) (z : ↥(OL LL')) :
    ((r (c • z) : ↥(OL LL)) : LL.1) = algebraMap ℤ_[l] LL.1 c * ((r z : ↥(OL LL)) : LL.1) := by
  have e : c • z = incO h (algebraMap ℤ_[l] (OL LL) c) * z := by
    apply Subtype.ext
    simp [incO, Algebra.smul_def]
  rw [e, hr]
  simp

def ext (r : ↥(OL LL') →+ ↥(OL LL)) (x : LL'.1) : LL.1 :=
  ((r ⟨(exists_mul LL' x).choose • x, (exists_mul LL' x).choose_spec.2⟩ : ↥(OL LL)) : LL.1) /
    algebraMap ℤ_[l] LL.1 (exists_mul LL' x).choose

theorem ext_eq (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x)
    (x : LL'.1) (d : ℤ_[l]) (hd : d ≠ 0) (y : ↥(OL LL')) (hy : (y : LL'.1) = d • x) :
    ext r x = ((r y : ↥(OL LL)) : LL.1) / algebraMap ℤ_[l] LL.1 d := by
  unfold ext
  set d0 := (exists_mul LL' x).choose with hd0def
  have hd0 : d0 ≠ 0 := (exists_mul LL' x).choose_spec.1
  set y0 : ↥(OL LL') := ⟨d0 • x, (exists_mul LL' x).choose_spec.2⟩ with hy0
  have key : d • y0 = d0 • y := by
    apply Subtype.ext
    simp only [SetLike.val_smul, hy0, hy, smul_smul, mul_comm]
  have k2 := congrArg (fun z => ((r z : ↥(OL LL)) : LL.1)) key
  simp only [r_smul h r hr] at k2
  rw [div_eq_div_iff (algebraMap_ne_zero LL hd0) (algebraMap_ne_zero LL hd)]
  linear_combination k2

theorem ext_add (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (x₁ x₂ : LL'.1) :
    ext r (x₁ + x₂) = ext r x₁ + ext r x₂ := by
  obtain ⟨d₁, hd₁, hi₁⟩ := exists_mul LL' x₁
  obtain ⟨d₂, hd₂, hi₂⟩ := exists_mul LL' x₂
  let y₁ : ↥(OL LL') := ⟨d₁ • x₁, hi₁⟩
  let y₂ : ↥(OL LL') := ⟨d₂ • x₂, hi₂⟩
  have hy : ((d₂ • y₁ + d₁ • y₂ : ↥(OL LL')) : LL'.1) = (d₁ * d₂) • (x₁ + x₂) := by
    simp only [y₁, y₂, Subalgebra.coe_add, SetLike.val_smul, smul_smul, smul_add]
    rw [mul_comm d₂ d₁]
  rw [ext_eq h r hr _ (d₁ * d₂) (mul_ne_zero hd₁ hd₂) _ hy, ext_eq h r hr x₁ d₁ hd₁ y₁ rfl,
    ext_eq h r hr x₂ d₂ hd₂ y₂ rfl, map_add, Subalgebra.coe_add, r_smul h r hr, r_smul h r hr, map_mul]
  have n₁ := algebraMap_ne_zero LL hd₁
  have n₂ := algebraMap_ne_zero LL hd₂
  field_simp

theorem ext_mul (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (a : LL.1) (x : LL'.1) :
    ext r (IntermediateField.inclusion h a * x) = a * ext r x := by
  obtain ⟨d, hd, hi⟩ := exists_mul LL' x
  obtain ⟨e, he, hie⟩ := exists_mul LL a
  let y : ↥(OL LL') := ⟨d • x, hi⟩
  let a'' : ↥(OL LL) := ⟨e • a, hie⟩
  have hy : ((incO h a'' * y : ↥(OL LL')) : LL'.1) = (e * d) • (IntermediateField.inclusion h a * x) := by
    simp only [incO, y, a'', RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Subalgebra.coe_mul,
      SetLike.val_smul, map_smul]
    simp only [Algebra.smul_def, map_mul]
    have hc : IntermediateField.inclusion h (algebraMap ℤ_[l] LL.1 e) = algebraMap ℤ_[l] LL'.1 e := by simp
    rw [hc]
    ring
  rw [ext_eq h r hr _ (e * d) (mul_ne_zero he hd) _ hy, ext_eq h r hr x d hd y rfl, hr,
    Subalgebra.coe_mul, map_mul]
  have n₁ := algebraMap_ne_zero LL hd
  have n₂ := algebraMap_ne_zero LL he
  have ha : ((a'' : ↥(OL LL)) : LL.1) = algebraMap ℤ_[l] LL.1 e * a := by
    simp [a'', Algebra.smul_def]
  rw [ha]
  field_simp

theorem ext_int (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (x : ↥(OL LL')) :
    ext r (x : LL'.1) = ((r x : ↥(OL LL)) : LL.1) := by
  rw [ext_eq h r hr _ 1 one_ne_zero x (by simp)]
  simp

end GlobalTheory.UseLoc.ExtRet

namespace GlobalTheory.UseLoc

theorem extRet_exists : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL)), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) → r 1 = 1 → ∃ p : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ (a : ↥LL.1) (x : ↥LL'.1), p (IntermediateField.inclusion h a * x) = a * p x) ∧ ∀ x : ↥(OL LL'), p (x : ↥LL'.1) = ((r x : ↥(OL LL)) : ↥LL.1) := by
  intro l _ LL LL' h r hr _
  refine ⟨{ toFun := ExtRet.ext r
            map_add' := ExtRet.ext_add h r hr
            map_smul' := fun q x => ?_ }, ExtRet.ext_mul h r hr, ExtRet.ext_int h r hr⟩
  have e : q • x = IntermediateField.inclusion h (algebraMap ℚ_[l] LL.1 q) * x := by
    rw [Algebra.smul_def]
    rfl
  simp only [RingHom.id_apply]
  rw [e, ExtRet.ext_mul h r hr, Algebra.smul_def]

end GlobalTheory.UseLoc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldExtensionOfIntegralRetractionStatement

section

@[expose] public section

open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc

theorem _root_.GlobalTheory.T.exists_fieldExtension_of_integral_retraction : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL)), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) → r 1 = 1 → ∃ p : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ (a : ↥LL.1) (x : ↥LL'.1), p (IntermediateField.inclusion h a * x) = a * p x) ∧ ∀ x : ↥(OL LL'), p (x : ↥LL'.1) = ((r x : ↥(OL LL)) : ↥LL.1) := by
  first | exact @GlobalTheory.UseLoc.extRet_exists | exact GlobalTheory.UseLoc.extRet_exists | (intros; apply GlobalTheory.UseLoc.extRet_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionLocalIntegers

section

@[expose] public section

open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

theorem exists_linRetraction_of_isTorsionFree {R S : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] (hinj : Function.Injective (algebraMap R S))
    [Module.IsTorsionFree R (S ⧸ LinearMap.range (Algebra.linearMap R S))] :
    ∃ r : S →ₗ[R] R, r 1 = 1 := by
  set N := LinearMap.range (Algebra.linearMap R S) with hN
  haveI : Module.Free R (S ⧸ N) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  let φ : S →ₗ[R] S := LinearMap.id - s ∘ₗ N.mkQ
  have hφ : ∀ x, φ x ∈ N := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero]
    have := LinearMap.congr_fun hs (N.mkQ x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    have this' : (Submodule.Quotient.mk (s (Submodule.Quotient.mk x)) : S ⧸ N) = Submodule.Quotient.mk x := this
    simp [φ, Submodule.Quotient.mk_sub, this']
  have hinj' : Function.Injective (Algebra.linearMap R S) := hinj
  let e := LinearEquiv.ofInjective (Algebra.linearMap R S) hinj'
  refine ⟨e.symm.toLinearMap ∘ₗ φ.codRestrict N hφ, ?_⟩
  have h1 : (1 : S) ∈ N := ⟨1, map_one (algebraMap R S)⟩
  have hφ1 : φ 1 = 1 := by
    have : N.mkQ 1 = 0 := (Submodule.Quotient.mk_eq_zero N).2 h1
    simp [φ, this]
  apply hinj'
  have := congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict N hφ 1))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.ofInjective_apply] at this
  rw [this, LinearMap.codRestrict_apply, hφ1, Algebra.linearMap_apply, map_one]

theorem isTorsionFree_quot_range {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    (H : ∀ a : R, a ≠ 0 → ∀ (b : R) (z : S), algebraMap R S b = algebraMap R S a * z → ∃ c, algebraMap R S c = z) :
    Module.IsTorsionFree R (S ⧸ LinearMap.range (Algebra.linearMap R S)) := by
  refine ⟨fun a ha => ?_⟩
  intro x y hxy
  induction x using Submodule.Quotient.induction_on with | _ x => ?_
  induction y using Submodule.Quotient.induction_on with | _ y => ?_
  have hxy' : (Submodule.Quotient.mk (a • x) : S ⧸ LinearMap.range (Algebra.linearMap R S)) =
      Submodule.Quotient.mk (a • y) := hxy
  rw [Submodule.Quotient.eq] at hxy' ⊢
  obtain ⟨b, hb⟩ := hxy'
  rw [← smul_sub, Algebra.smul_def] at hb
  obtain ⟨c, hc⟩ := H a ha.ne_zero b (x - y) hb
  exact ⟨c, hc⟩

end GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

theorem incO_injective {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) :
    Function.Injective (incO h) := by
  intro a b hab
  have := congrArg (fun x : ↥(OL LL') => ((x : ↥LL'.1) : Om l)) hab
  exact Subtype.ext (Subtype.ext this)

theorem incO_div {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {a b : ↥(OL LL)} (ha0 : a ≠ 0)
    {z : ↥(OL LL')} (hb : incO h b = incO h a * z) : ∃ c, incO h c = z := by
  have haL : ((a : ↥LL.1) : Om l) ≠ 0 := fun e => ha0 (Subtype.ext (Subtype.ext e))
  have hb' : ((b : ↥LL.1) : Om l) = ((a : ↥LL.1) : Om l) * ((z : ↥LL'.1) : Om l) :=
    congrArg (fun x : ↥(OL LL') => ((x : ↥LL'.1) : Om l)) hb
  have hz : ((z : ↥LL'.1) : Om l) = ((b : ↥LL.1) : Om l) / ((a : ↥LL.1) : Om l) := by
    rw [eq_div_iff haL, mul_comm]
    exact hb'.symm
  have hc : (b : ↥LL.1) / (a : ↥LL.1) ∈ OL LL := by
    rw [Formalism.BasicNotions.Examples₂.LB.mem_OL]
    have hz1 := (Formalism.BasicNotions.Examples₂.LB.mem_OL LL' (z : ↥LL'.1)).1 z.2
    rw [hz] at hz1
    simpa using hz1
  refine ⟨⟨_, hc⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext
  change ((b : ↥LL.1) : Om l) / ((a : ↥LL.1) : Om l) = ((z : ↥LL'.1) : Om l)
  rw [hz]


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_intRetraction : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1),
    ∃ r : ↥(OL LL') →+ ↥(OL LL), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) ∧ r 1 = 1 := by
  intro l _ LL LL' h
  letI A : Algebra ↥(OL LL) ↥(OL LL') := (incO h).toAlgebra
  haveI : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  haveI T : IsScalarTower ℤ_[l] ↥(OL LL) ↥(OL LL') := IsScalarTower.of_algebraMap_eq (fun x => by
    apply Subtype.ext; apply Subtype.ext; rfl)
  haveI : Module.Finite ℤ_[l] ↥(OL LL') := Formalism.BasicNotions.Examples₂.LB.OL_finite LL'
  haveI : Module.Finite ↥(OL LL) ↥(OL LL') := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  haveI := isTorsionFree_quot_range (R := ↥(OL LL)) (S := ↥(OL LL')) (fun a ha b z hb => incO_div h ha hb)
  obtain ⟨r, hr⟩ := exists_linRetraction_of_isTorsionFree (R := ↥(OL LL)) (S := ↥(OL LL')) (incO_injective h)
  refine ⟨r.toAddMonoidHom, fun a x => ?_, hr⟩
  show r (incO h a * x) = a * r x
  have e1 : incO h a * x = a • x := (Algebra.smul_def a x).symm
  rw [e1, map_smul, smul_eq_mul]

end GlobalTheory.UseLoc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionLocalIntegersStatement

section

@[expose] public section

open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc

theorem _root_.GlobalTheory.T.exists_integral_retraction_localIntegers : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1), ∃ r : ↥(OL LL') →+ ↥(OL LL), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) ∧ r 1 = 1 := by
  first | exact @GlobalTheory.UseLoc.exists_intRetraction | exact GlobalTheory.UseLoc.exists_intRetraction | (intros; apply GlobalTheory.UseLoc.exists_intRetraction <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFinitePartOfLift

section

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

namespace GlobalTheory.UseLoc.DescHf

theorem exists_retraction {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) :
    ∃ p : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ (a : ↥LL.1) (x : ↥LL'.1), p (IntermediateField.inclusion h a * x) = a * p x) ∧
      (∀ a : ↥LL.1, p (IntermediateField.inclusion h a) = a) ∧ (∀ x : ↥LL'.1, x ∈ OL LL' → p x ∈ OL LL) := by
  obtain ⟨r, hr, hr1⟩ := GlobalTheory.T.exists_integral_retraction_localIntegers h
  obtain ⟨p, hp, hpr⟩ := GlobalTheory.T.exists_fieldExtension_of_integral_retraction h r hr hr1
  have h1 : p 1 = 1 := by
    have := hpr 1
    rw [hr1] at this
    exact this
  refine ⟨p, hp, fun a => ?_, fun x hx => ?_⟩
  · have := hp a 1
    rw [mul_one, h1, mul_one] at this
    exact this
  · have := hpr ⟨x, hx⟩
    rw [show p x = _ from this]
    exact (r ⟨x, hx⟩).2




theorem descHf : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C M)) →
    z ∈ HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) := by
  intro D i w hw C k M z hz
  obtain ⟨p, hpm, hp1, hpO⟩ := exists_retraction C.le
  obtain ⟨c, hc, m, hcm⟩ := (GlobalTheory.BlochKatoBaseChangeLe.mem_HfD_gen _ _ _).1 hz
  have hent : ∀ g a b, (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g) a b =
      IntermediateField.inclusion C.le (Br.loc D.nbr i w hw M g a b) := fun g a b => rfl
  have hp : ∀ g (v : Fin k → ↥C.LL.1),
      (fun j => p ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec v j)) =
        (Br.loc D.nbr i w hw M g).mulVec fun j => p (v j) := by
    intro g v
    funext a

    simp only [Matrix.mulVec, dotProduct, map_sum, hent, hpm]
  have hc' := GlobalTheory.TwistedSelmerCompare.crystallineCocycle_transport_conjugation (D.loc (D.nd.l i)) (D.nbr i w hw).Kw (D.nbr i w hw).Kw C.LL
    (D.nbr i w hw).LL (MonoidHom.id _) continuous_id 1 (fun g => by simp) _ (Br.loc D.nbr i w hw M) p hp c hc
  refine (GlobalTheory.BlochKatoBaseChangeLe.mem_HfD_gen _ _ _).2 ⟨_, hc', fun j => p (m j), fun g => ?_⟩
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (z g)
  have h1 : (Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) (incV C.le k u)) =
      Submodule.Quotient.mk (c g + ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec m - m)) := by
    refine (liftQ_mk C.le k u).symm.trans ?_
    refine Eq.trans ?_ (hcm g)
    exact congrArg (liftQ C.le k) hu
  obtain ⟨n, hn⟩ := (Submodule.Quotient.eq (stdG ↥(OL C.LL) ↥C.LL.1 k)).1 h1
  refine hu.symm.trans ((Submodule.Quotient.eq (stdG (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) k)).2 ?_)
  refine ⟨fun j => ⟨p (n j), hpO _ (n j).2⟩, ?_⟩
  funext j
  have h2 := congrArg p (congrFun hn j)
  have h3 := congrFun (hp g m) j
  change p ((n j : ↥C.LL.1)) = p (IntermediateField.inclusion C.le (u j) - (c g j + ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec m j - m j))) at h2
  change (p (n j) : Br.LL D.nbr i w hw) = u j - (p (c g j) + ((Br.loc D.nbr i w hw M g).mulVec (fun j => p (m j)) j - p (m j)))
  rw [h2, map_sub, map_add (f := _), map_sub, hp1, ← h3]

end GlobalTheory.UseLoc.DescHf
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFinitePartOfLiftStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

theorem _root_.GlobalTheory.T.mem_finite_part_of_lift : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C M)) →
    z ∈ HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) := by
  first | exact @GlobalTheory.UseLoc.DescHf.descHf | exact GlobalTheory.UseLoc.DescHf.descHf | (intros; apply GlobalTheory.UseLoc.DescHf.descHf <;> assumption)
end
end
