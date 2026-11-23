module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedPowerSeriesEvaluationDivisibilityStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPuncturedDiscInjectiveEvalAtPointStatement
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianLocalOfOrderFunction

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.OrdRing

section General

variable (R : Type) [CommRing R] [IsDomain R] [ValuationRing R]

noncomputable def intRing : ValuationSubring (FractionRing R) :=
  { (algebraMap R (FractionRing R)).range with
    mem_or_inv_mem' := fun x => by
      rcases ValuationRing.isInteger_or_isInteger R x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact Or.inl ⟨y, hy⟩
      · exact Or.inr ⟨y, hy⟩ }

noncomputable def intEquiv : R ≃+* intRing R :=
  RingEquiv.ofBijective ((algebraMap R (FractionRing R)).codRestrict (intRing R) fun y => ⟨y, rfl⟩)
    ⟨fun a b h => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h),
     fun ⟨x, ⟨y, hy⟩⟩ => ⟨y, Subtype.ext hy⟩⟩

variable {K : Type} [Field K] (φ : K →+* FractionRing R)

noncomputable def res : (intRing R).comap φ →+* R :=
  (intEquiv R).symm.toRingHom.comp (φ.restrict ((intRing R).comap φ) (intRing R) fun _ h => h)

theorem algebraMap_res (w : (intRing R).comap φ) :
    algebraMap R (FractionRing R) (res R φ w) = φ w :=
  congrArg Subtype.val ((intEquiv R).apply_symm_apply _)

theorem res_injective : Function.Injective (res R φ) := by
  intro a b h
  have := congrArg (algebraMap R (FractionRing R)) h
  rw [algebraMap_res, algebraMap_res] at this
  exact Subtype.ext (φ.injective this)

theorem dvd_of_res_dvd {x y : (intRing R).comap φ} (hy : y ≠ 0) (h : res R φ y ∣ res R φ x) :
    y ∣ x := by
  obtain ⟨c, hc⟩ := h
  have hyK : (y : K) ≠ 0 := fun h0 => hy (Subtype.ext h0)
  have hy' : algebraMap R (FractionRing R) (res R φ y) ≠ 0 := by
    rw [algebraMap_res]; exact (map_ne_zero φ).2 hyK
  have hmem : (x : K) / y ∈ (intRing R).comap φ := by
    rw [ValuationSubring.mem_comap, map_div₀, ← algebraMap_res, ← algebraMap_res, hc, map_mul,
      mul_div_cancel_left₀ _ hy']
    exact ⟨c, rfl⟩
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  show (x : K) = (y : K) * ((x : K) / y)
  field_simp

theorem isUnit_of_isUnit_res {a : (intRing R).comap φ} (h : IsUnit (res R φ a)) : IsUnit a := by
  have ha : a ≠ 0 := by rintro rfl; rw [map_zero] at h; exact not_isUnit_zero h
  refine isUnit_of_dvd_one (dvd_of_res_dvd R φ ha ?_)
  rw [map_one]; exact h.dvd

variable [IsDiscreteValuationRing R]

theorem isPrincipalIdealRing_comap : IsPrincipalIdealRing ((intRing R).comap φ) := by
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · subst hI; exact bot_isPrincipal
  obtain ⟨y0, hy0, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  let s : Set ((intRing R).comap φ) := {x | x ∈ I ∧ x ≠ 0}
  have hs : s.Nonempty := ⟨y0, hy0, hne⟩
  let y := Function.argminOn (fun x => IsDiscreteValuationRing.addVal R (res R φ x)) s hs
  have hy : y ∈ s := Function.argminOn_mem _ _ hs
  refine ⟨⟨y, le_antisymm ?_ ?_⟩⟩
  · intro x hx
    by_cases hx0 : x = 0
    · subst hx0; exact Submodule.zero_mem _
    rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
    exact dvd_of_res_dvd R φ hy.2
      (IsDiscreteValuationRing.addVal_le_iff_dvd.1 (Function.argminOn_le (fun x => IsDiscreteValuationRing.addVal R (res R φ x)) s ⟨hx, hx0⟩))
  · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hy.1

theorem mem_of_prime {q : Ideal ((intRing R).comap φ)} (hq : q.IsPrime) (hq0 : q ≠ ⊥)
    (a : (intRing R).comap φ) : a ∈ q ↔ ¬ IsUnit (res R φ a) := by
  constructor
  · intro ha hu
    exact hq.ne_top (Ideal.eq_top_of_isUnit_mem q ha (isUnit_of_isUnit_res R φ hu))
  · intro hna
    obtain ⟨y, hyq, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq0
    have hry : res R φ y ≠ 0 := fun h => hy0 (res_injective R φ (by rw [h, map_zero]))
    have hfin : IsDiscreteValuationRing.addVal R (res R φ y) ≠ ⊤ :=
      fun h => hry (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
    set N := (IsDiscreteValuationRing.addVal R (res R φ y)).toNat with hN
    have h1 : 1 ≤ IsDiscreteValuationRing.addVal R (res R φ a) :=
      ENat.one_le_iff_ne_zero.2 fun h => hna (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
    have hle : IsDiscreteValuationRing.addVal R (res R φ y) ≤
        IsDiscreteValuationRing.addVal R (res R φ (a ^ N)) := by
      rw [map_pow, IsDiscreteValuationRing.addVal_pow, ← ENat.coe_toNat hfin, ← hN]
      calc (N : ℕ∞) = N • (1 : ℕ∞) := by simp
        _ ≤ N • IsDiscreteValuationRing.addVal R (res R φ a) := nsmul_le_nsmul_right h1 N
    have hd := dvd_of_res_dvd R φ hy0 (IsDiscreteValuationRing.addVal_le_iff_dvd.1 hle)
    exact hq.mem_of_pow_mem N (Ideal.mem_of_dvd _ hd hyq)

end General

end GlobalTheory.MBLow.OrdRing

namespace GlobalTheory.MBLow.OrdRing

section Order

variable {B C : Type} [CommRing B] [IsDomain B] [Field C] (ev : B →+* C) (t : B)

theorem exists_pow_mul_not_dvd (hfin : ∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) {b : B}
    (hb : b ≠ 0) : ∃ (n : ℕ) (c : B), b = t ^ n * c ∧ ¬ t ∣ c := by
  obtain ⟨n, hn⟩ := hfin b hb
  have hf : FiniteMultiplicity t b := ⟨n, fun h => hn ((pow_dvd_pow t (Nat.le_succ n)).trans h)⟩
  obtain ⟨c, hc, hnd⟩ := hf.exists_eq_pow_mul_and_not_dvd
  exact ⟨_, c, hc, hnd⟩

theorem ker_eq_span (hker : ∀ b, ev b = 0 ↔ t ∣ b) : RingHom.ker ev = Ideal.span {t} := by
  ext b; rw [RingHom.mem_ker, Ideal.mem_span_singleton, hker]

theorem map_ker_eq_span (hker : ∀ b, ev b = 0 ↔ t ∣ b) :
    IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker ev)) =
      Ideal.span {algebraMap B (Localization.AtPrime (RingHom.ker ev)) t} := by
  have h := congrArg (Ideal.map (algebraMap B (Localization.AtPrime (RingHom.ker ev))))
    (ker_eq_span ev t hker)
  rw [Ideal.map_span, Set.image_singleton] at h
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker ev)]
  exact h

theorem isDVR (ht : t ≠ 0) (hker : ∀ b, ev b = 0 ↔ t ∣ b)
    (hfin : ∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) :
    IsDiscreteValuationRing (Localization.AtPrime (RingHom.ker ev)) := by
  set P := RingHom.ker ev
  have hinj : Function.Injective (algebraMap B (Localization.AtPrime P)) :=
    IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
  have ht' : algebraMap B (Localization.AtPrime P) t ≠ 0 :=
    fun h => ht (hinj (by rw [h, map_zero]))
  have htprime : Prime (algebraMap B (Localization.AtPrime P) t) := by
    rw [← Ideal.span_singleton_prime ht', ← map_ker_eq_span ev t hker]
    infer_instance
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, htprime.irreducible, fun {x} hx => ?_⟩
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
  have hb : b ≠ 0 := by rintro rfl; exact hx (IsLocalization.mk'_zero _)
  obtain ⟨n, c, rfl, hc⟩ := exists_pow_mul_not_dvd t hfin hb
  have hcP : c ∈ P.primeCompl := fun h => hc ((hker c).1 (RingHom.mem_ker.1 h))
  have hu := IsLocalization.map_units (Localization.AtPrime P) (⟨c, hcP⟩ : P.primeCompl)
  have hs := IsLocalization.map_units (Localization.AtPrime P) s
  refine ⟨n, hu.unit * hs.unit⁻¹, ?_⟩
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, Units.val_mul, IsUnit.unit_spec, map_mul, map_pow,
    _root_.mul_assoc, _root_.mul_assoc, hs.val_inv_mul, _root_.mul_one]

noncomputable def evLoc : Localization.AtPrime (RingHom.ker ev) →+* C :=
  IsLocalization.lift (M := (RingHom.ker ev).primeCompl) (g := ev)
    fun y => isUnit_iff_ne_zero.2 fun h => y.2 (RingHom.mem_ker.2 h)

theorem evLoc_algebraMap (b : B) :
    evLoc ev (algebraMap B (Localization.AtPrime (RingHom.ker ev)) b) = ev b :=
  IsLocalization.lift_eq _ _

theorem evLoc_eq_zero_iff (hker : ∀ b, ev b = 0 ↔ t ∣ b)
    (z : Localization.AtPrime (RingHom.ker ev)) : evLoc ev z = 0 ↔ ¬ IsUnit z := by
  constructor
  · intro h hu; exact (hu.map (evLoc ev)).ne_zero h
  · intro hz
    have hm : z ∈ IsLocalRing.maximalIdeal _ := hz
    rw [map_ker_eq_span ev t hker, Ideal.mem_span_singleton] at hm
    obtain ⟨c, rfl⟩ := hm
    rw [map_mul, evLoc_algebraMap, (hker t).2 dvd_rfl, zero_mul]

end Order

end GlobalTheory.MBLow.OrdRing

namespace GlobalTheory.MBLow.OrdRing

theorem exists_of_dvr (A B C Ω : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field C] [Field Ω] (f : A →+* B) (ev : B →+* C) (i : A →+* Ω)
    (hf : Function.Injective f) (hi : Function.Injective i)
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (j : B →+* R)
    (hj : Function.Injective j) (ev' : R →+* C) (hev : ∀ b, ev' (j b) = ev b)
    (hzero : ∀ z, ev' z = 0 ↔ ¬ IsUnit z) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W)
      (_ : IsIntegrallyClosed W) (g : A →+* W) (i₀ : W →+* Ω) (i₁ : W →+* C),
      Function.Injective i₀ ∧ i₀.comp g = i ∧ i₁.comp g = ev.comp f ∧
      (∀ a, i₁ a ≠ 0 → IsUnit a) ∧
      ∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁ := by
  have hg : Function.Injective ((algebraMap R (FractionRing R)).comp (j.comp f)) :=
    (IsFractionRing.injective R (FractionRing R)).comp (hj.comp hf)
  let φ : FractionRing A →+* FractionRing R := IsFractionRing.lift hg
  let V := (intRing R).comap φ
  haveI : IsPrincipalIdealRing V := isPrincipalIdealRing_comap R φ
  have hmemA : ∀ a : A, algebraMap A (FractionRing A) a ∈ V := fun a => by
    rw [ValuationSubring.mem_comap, IsFractionRing.lift_algebraMap]
    exact ⟨j (f a), rfl⟩
  let g : A →+* V := (algebraMap A (FractionRing A)).codRestrict V hmemA
  let i₀ : V →+* Ω := (IsFractionRing.lift hi).comp V.subtype
  have hi₀ : Function.Injective i₀ := fun x y h => Subtype.ext ((IsFractionRing.lift hi).injective h)
  have hres : ∀ a : A, res R φ (g a) = j (f a) := fun a => by
    apply IsFractionRing.injective R (FractionRing R)
    rw [algebraMap_res]
    exact IsFractionRing.lift_algebraMap hg a
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, g, i₀,
    ev'.comp (res R φ), hi₀, ?_, ?_, ?_, ?_⟩
  · ext a
    exact IsFractionRing.lift_algebraMap hi a
  · ext a
    simp only [RingHom.comp_apply]
    rw [hres, hev]
  · intro a ha
    exact isUnit_of_isUnit_res R φ (not_not.1 fun h => ha ((hzero _).2 h))
  · intro q hq
    by_cases hq0 : q = ⊥
    · left; rw [hq0, (RingHom.injective_iff_ker_eq_bot _).1 hi₀]
    · right
      ext a
      rw [mem_of_prime R φ hq hq0, RingHom.mem_ker, RingHom.comp_apply, hzero]

end GlobalTheory.MBLow.OrdRing

namespace GlobalTheory.MBLow


open GlobalTheory.MBLow.OrdRing in
theorem exists_localRing_of_order : ∀ (A B C Ω : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field C] [Field Ω] (f : A →+* B) (ev : B →+* C) (t : B) (i : A →+* Ω), Function.Injective f → Function.Injective i → t ≠ 0 → (∀ b, ev b = 0 ↔ t ∣ b) → (∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W) (_ : IsIntegrallyClosed W) (g : A →+* W) (i₀ : W →+* Ω) (i₁ : W →+* C), Function.Injective i₀ ∧ i₀.comp g = i ∧ i₁.comp g = ev.comp f ∧ (∀ a, i₁ a ≠ 0 → IsUnit a) ∧ ∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁ := by
  intro A B C Ω _ _ _ _ _ _ f ev t i hf hi ht hker hfin
  haveI := isDVR ev t ht hker hfin
  exact exists_of_dvr A B C Ω f ev i hf hi (Localization.AtPrime (RingHom.ker ev))
    (algebraMap B _) (IsLocalization.injective _ (RingHom.ker ev).primeCompl_le_nonZeroDivisors)
    (evLoc ev) (evLoc_algebraMap ev) (evLoc_eq_zero_iff ev t hker)

end GlobalTheory.MBLow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianLocalOfOrderFunctionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_noetherianLocal_of_orderFunction : ∀ (A B C Ω : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field C] [Field Ω] (f : A →+* B) (ev : B →+* C) (t : B) (i : A →+* Ω), Function.Injective f → Function.Injective i → t ≠ 0 → (∀ b, ev b = 0 ↔ t ∣ b) → (∀ b : B, b ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ b) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W) (_ : IsIntegrallyClosed W) (g : A →+* W) (i₀ : W →+* Ω) (i₁ : W →+* C), Function.Injective i₀ ∧ i₀.comp g = i ∧ i₁.comp g = ev.comp f ∧ (∀ a, i₁ a ≠ 0 → IsUnit a) ∧ ∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁ := by
  first | exact @GlobalTheory.MBLow.exists_localRing_of_order | exact GlobalTheory.MBLow.exists_localRing_of_order | (intros; apply GlobalTheory.MBLow.exists_localRing_of_order <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeformationBaseRingLocalDomain

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem tsum_coeff_C_mul_pow_eq {K : Type} [NormedField K] (a u : K) :
    ∑' n, PowerSeries.coeff n (PowerSeries.C a) * u ^ n = a := by
  rw [tsum_eq_single 0 (fun n hn => by simp [PowerSeries.coeff_C, hn])]
  simp

theorem summable_coeff_C_mul_pow {K : Type} [NormedField K] (a u : K) :
    Summable fun n => ‖PowerSeries.coeff n (PowerSeries.C a) * u ^ n‖ :=
  (hasSum_single 0 (fun n hn => by simp [PowerSeries.coeff_C, hn])).summable

theorem ring_of_deformation : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [CharZero C] (e : C →+* ℂ) (I I' : Type) [Finite I] [Finite I'] (Φ : I → PowerSeries C) (c : I' → C) (π : C) (b ε : ℝ), ‖π‖ < 1 → 0 < ε → (∀ a n, ‖PowerSeries.coeff n (Φ a)‖ ≤ b) → (∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → ∀ a, Summable fun n => ‖e (PowerSeries.coeff n (Φ a)) * u ^ n‖) → ∃ (u : ℂ) (o : Type) (_ : Field o) (_ : CharZero o) (j : o →+* C) (c₀ : I' → o), u ≠ 0 ∧ ‖u‖ < ε ∧ (∀ a, j (c₀ a) = c a) ∧ ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W) (_ : IsIntegrallyClosed W) (_ : CharZero W) (β : o →+* W) (i₀ : W →+* ℂ) (i₁ : W →+* C) (φ : I → W), Function.Injective i₀ ∧ i₀.comp β = e.comp j ∧ i₁.comp β = j ∧ (∀ a, i₁ a ≠ 0 → IsUnit a) ∧ (∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁) ∧ ∀ a, i₀ (φ a) = ∑' n, e (PowerSeries.coeff n (Φ a)) * u ^ n ∧ i₁ (φ a) = ∑' n, PowerSeries.coeff n (Φ a) * π ^ n := by
  intro C _ _ _ _ e I I' _ _ Φ c π b ε hπ hε hb hsum
  classical

  set o : Subfield C := Subfield.closure (Set.range c) with ho_def
  have hoc : Countable o := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Subfield.cardinalMk_closure_le_max _).trans
      (max_le (Cardinal.mk_le_aleph0_iff.2 (Set.finite_range c).countable.to_subtype) le_rfl)

  set G : Set (PowerSeries C) :=
    Set.range (fun x : o => PowerSeries.C (x : C)) ∪ Set.range Φ with hG
  set A : Subring (PowerSeries C) := Subring.closure G with hA
  obtain ⟨B, ev, t, hB, hev, ht, hevt, hfin⟩ := GlobalTheory.T.bounded_power_series_evaluation_divisibility C π hπ
  have hAB : A ≤ B := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨x, rfl⟩ | ⟨a, rfl⟩)
    · refine (hB _).2 ⟨‖(x : C)‖, fun n => ?_⟩
      rw [PowerSeries.coeff_C]; split_ifs <;> simp
    · exact (hB _).2 ⟨b, hb a⟩

  set S : Set (PowerSeries ℂ) := PowerSeries.map e '' G with hS
  have hSc : S.Countable :=
    ((Set.countable_range _).union (Set.finite_range Φ).countable).image _
  have hSs : ∀ Ψ ∈ S, ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → Summable fun n => ‖PowerSeries.coeff n Ψ * u ^ n‖ := by
    rintro _ ⟨g, (⟨x, rfl⟩ | ⟨a, rfl⟩), rfl⟩ u hu0 hu
    · rw [PowerSeries.map_C]; exact summable_coeff_C_mul_pow _ _
    · simpa [PowerSeries.coeff_map] using hsum u hu0 hu a
  obtain ⟨u, ig, hu0, hu, hig, hige⟩ := GlobalTheory.T.exists_puncturedDisc_injective_evalAtPoint ε S hε hSc hSs
  have hmapA : ∀ x ∈ A, PowerSeries.map e x ∈ Subring.closure S := by
    intro x hx
    rw [hS, ← RingHom.map_closure]
    exact Subring.mem_map.2 ⟨x, hx, rfl⟩
  let m : A →+* Subring.closure S := (PowerSeries.map e).restrict A (Subring.closure S) hmapA
  have hm : ∀ x : A, (m x : PowerSeries ℂ) = PowerSeries.map e (x : PowerSeries C) := fun _ => rfl
  have hmapinj : Function.Injective (PowerSeries.map e) := by
    intro x y h
    ext n
    have := congrArg (PowerSeries.coeff n) h
    simp only [PowerSeries.coeff_map] at this
    exact e.injective this
  have hminj : Function.Injective m := by
    intro x y h
    apply Subtype.ext
    apply hmapinj
    rw [← hm, ← hm, h]
  let i : A →+* ℂ := ig.comp m
  have hi : Function.Injective i := hig.comp hminj
  let f : A →+* B := Subring.inclusion hAB
  have hf : Function.Injective f := fun x y h => Subtype.ext (congrArg Subtype.val h :)
  obtain ⟨W, _, _, _, _, _, g, i₀, i₁, hi₀, hgi₀, hgi₁, hunit, hprime⟩ :=
    GlobalTheory.T.exists_noetherianLocal_of_orderFunction A B C ℂ f ev t i hf hi ht hevt hfin
  let cA : o →+* A := (PowerSeries.C.comp o.subtype).codRestrict A
    (fun x => Subring.subset_closure (Or.inl ⟨x, rfl⟩))
  have hΦA : ∀ a, Φ a ∈ A := fun a => Subring.subset_closure (Or.inr ⟨a, rfl⟩)
  haveI : CharZero W := RingHom.charZero i₁
  refine ⟨u, o, inferInstance, inferInstance, o.subtype,
    fun a => ⟨c a, Subfield.subset_closure ⟨a, rfl⟩⟩, hu0, hu, fun a => rfl,
    W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    g.comp cA, i₀, i₁, fun a => g ⟨Φ a, hΦA a⟩, hi₀, ?_, ?_, hunit, hprime, fun a => ⟨?_, ?_⟩⟩
  · ext x
    have h1 := RingHom.congr_fun hgi₀ (cA x)
    simp only [RingHom.comp_apply] at h1 ⊢
    rw [h1]
    show ig (m (cA x)) = e x
    rw [hige, hm]
    show ∑' n, PowerSeries.coeff n (PowerSeries.map e (PowerSeries.C (x : C))) * u ^ n = e x
    rw [PowerSeries.map_C, tsum_coeff_C_mul_pow_eq]
  · ext x
    have h1 := RingHom.congr_fun hgi₁ (cA x)
    simp only [RingHom.comp_apply] at h1 ⊢
    rw [h1, hev]
    show ∑' n, PowerSeries.coeff n (PowerSeries.C (x : C)) * π ^ n = x
    rw [tsum_coeff_C_mul_pow_eq]
  · have h1 := RingHom.congr_fun hgi₀ ⟨Φ a, hΦA a⟩
    simp only [RingHom.comp_apply] at h1
    rw [h1]
    show ig (m ⟨Φ a, hΦA a⟩) = _
    rw [hige, hm]
    simp only [PowerSeries.coeff_map]
  · have h1 := RingHom.congr_fun hgi₁ ⟨Φ a, hΦA a⟩
    simp only [RingHom.comp_apply] at h1
    rw [h1, hev]
    rfl

end GlobalTheory.MBLow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeformationBaseRingLocalDomainStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_deformation_base_ring_local_domain : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [CharZero C] (e : C →+* ℂ) (I I' : Type) [Finite I] [Finite I'] (Φ : I → PowerSeries C) (c : I' → C) (π : C) (b ε : ℝ), ‖π‖ < 1 → 0 < ε → (∀ a n, ‖PowerSeries.coeff n (Φ a)‖ ≤ b) → (∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → ∀ a, Summable fun n => ‖e (PowerSeries.coeff n (Φ a)) * u ^ n‖) → ∃ (u : ℂ) (o : Type) (_ : Field o) (_ : CharZero o) (j : o →+* C) (c₀ : I' → o), u ≠ 0 ∧ ‖u‖ < ε ∧ (∀ a, j (c₀ a) = c a) ∧ ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W) (_ : IsIntegrallyClosed W) (_ : CharZero W) (β : o →+* W) (i₀ : W →+* ℂ) (i₁ : W →+* C) (φ : I → W), Function.Injective i₀ ∧ i₀.comp β = e.comp j ∧ i₁.comp β = j ∧ (∀ a, i₁ a ≠ 0 → IsUnit a) ∧ (∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁) ∧ ∀ a, i₀ (φ a) = ∑' n, e (PowerSeries.coeff n (Φ a)) * u ^ n ∧ i₁ (φ a) = ∑' n, PowerSeries.coeff n (Φ a) * π ^ n := by
  first | exact @GlobalTheory.MBLow.ring_of_deformation | exact GlobalTheory.MBLow.ring_of_deformation | (intros; apply GlobalTheory.MBLow.ring_of_deformation <;> assumption)
end
end
