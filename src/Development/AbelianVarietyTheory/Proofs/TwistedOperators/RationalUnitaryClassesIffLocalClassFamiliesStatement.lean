module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyUnitaryTorusOrbitalClassTrivialLocalStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTorusClassOfIrreducibleCharpolyUnitaryStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianIsometryBaseChange
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormClassesIffConjUnitaryTorusEllipticElementsStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusElementCharpolyRegularCentralizerStatement
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianIsometryBaseChangeStatement

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.hermitian_isometry_base_change : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k k' : Type) [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k'] (ψ : k →ₐ[F] k') (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ), ∃ (x' : plusUnits P k') (φ' : (k' ⊗[F] Fld P) ≃ₗ[k' ⊗[F] E] (Fin n → k' ⊗[F] E)) (h' : IsIsom P k' J x'.1.1 φ'), x'.1.1 = Algebra.TensorProduct.map ψ (AlgHom.id F (Fld P)) x.1.1 ∧ gam h' = mapH σ J ψ (gam h) ∧ ∀ t, torEmb h' (mapH (star' P) (one₁ P) ψ t) = mapH σ J ψ (torEmb h t) := by
  first | exact @GlobalTheory.TrEll.BaseChg.exists_isom_baseChange | exact GlobalTheory.TrEll.BaseChg.exists_isom_baseChange | (intros; apply GlobalTheory.TrEll.BaseChg.exists_isom_baseChange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalNormClassesEqLocalUnramifiedCM

section

@[expose] public section

open Set Filter Polynomial NumberField IsDedekindDomain
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.TrEll.Hasse

abbrev Ten {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r) (k : Type) [CommRing k]
    [Algebra F k] : Type := k ⊗[F] Fld P

section Bridge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  (P : PPol (IsCMField.complexConj E).toAlgHom r)

def toSR : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r :=
  ⟨P.1, P.2.1, P.2.2.1, P.2.2.2.1, by rw [coeff_zero_eq_eval_zero]; exact P.2.2.2.2.1, by
    have h := P.2.2.2.2.2
    rw [sharp, ← coeff_zero_eq_eval_zero] at h
    exact h⟩

variable (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]

def incl : k ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.plus (toSR P) →+* Ten P k :=
  (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.inclPlus (toSR P) k).toRingHom

theorem incl_injective : Function.Injective (incl P k) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := k) (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.plus (toSR P)).val.toLinearMap
    Subtype.val_injective

theorem sigR_incl (a) : sigR k (star' P) (incl P k a) = incl P k a :=
  GlobalTheory.TraceClasses.involBase_inclPlus (toSR P) k a

theorem exists_incl_eq_add (z : Ten P k) : ∃ a, incl P k a = z + sigR k (star' P) z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s y =>
    refine ⟨s ⊗ₜ ⟨y + star' P y, ?_⟩, TensorProduct.tmul_add _ _ _⟩
    change star' P (y + star' P y) = y + star' P y
    have : star' P (star' P y) = y := GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol_invol (toSR P) y
    rw [map_add (f := _), this, add_comm]
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]; ring⟩

theorem exists_incl_eq {z : Ten P k} (hz : sigR k (star' P) z = z) : ∃ a, incl P k a = z := by
  obtain ⟨a, ha⟩ := exists_incl_eq_add P k ((2⁻¹ : maximalRealSubfield E) • z)
  refine ⟨a, ?_⟩
  have : sigR k (star' P) ((2⁻¹ : maximalRealSubfield E) • z) = (2⁻¹ : maximalRealSubfield E) • sigR k (star' P) z :=
    map_smul (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) k) (star' P)) _ _
  rw [ha, this, hz, ← add_smul]
  norm_num

def unitMap : (k ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.plus (toSR P))ˣ →* plusUnits P k :=
  (Units.map (incl P k).toMonoidHom).codRestrict _ fun a => Units.ext (sigR_incl P k a)

theorem unitMap_surjective : Function.Surjective (unitMap P k) := by
  intro x
  obtain ⟨a, ha⟩ := exists_incl_eq P k (z := x.1.1) (congrArg Units.val x.2)
  obtain ⟨b, hb⟩ := exists_incl_eq P k (z := (x⁻¹).1.1) (congrArg Units.val (x⁻¹).2)
  have h : a * b = 1 := incl_injective P k (by rw [map_mul, ha, hb, map_one]; exact x.1.mul_inv)
  exact ⟨Units.mkOfMulEqOne a b h, Subtype.ext (Units.ext ha)⟩

theorem mk_unitMap_eq_iff (a b) : (QuotientGroup.mk (unitMap P k a) : Cls P k) = QuotientGroup.mk (unitMap P k b) ↔
    (QuotientGroup.mk a : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.NormClass (toSR P) k) = QuotientGroup.mk b := by
  rw [QuotientGroup.eq, QuotientGroup.eq, ← map_inv, ← map_mul]
  rfl

def clsMap : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.NormClass (toSR P) k →* Cls P k :=
  QuotientGroup.map _ _ (unitMap P k) fun _ h => h

theorem clsMap_injective : Function.Injective (clsMap P k) := by
  intro q q' h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q'
  exact (mk_unitMap_eq_iff P k a b).1 h

theorem clsMap_surjective : Function.Surjective (clsMap P k) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, rfl⟩ := unitMap_surjective P k x
  exact ⟨QuotientGroup.mk a, rfl⟩

theorem hform_eq (J : Matrix (Fin r) (Fin r) E) (u u' : Fin r → k ⊗[maximalRealSubfield E] E) :
    Formalism.UG.hform (sigR k (IsCMField.complexConj E).toAlgHom) (JR k J) u' u = GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.gramForm k Jᵀ u u' := by
  rw [Formalism.UG.hform, GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.gramForm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change GlobalTheory.HermLocal.ccBase E k (u' j) * ((1 : k) ⊗ₜ[maximalRealSubfield E] J j i) * u i =
    u i * ((1 : k) ⊗ₜ[maximalRealSubfield E] J j i) * GlobalTheory.HermLocal.ccBase E k (u' j)
  ring

theorem isometric_iff (J : Matrix (Fin r) (Fin r) E) (a) :
    (∃ φ, IsIsom P k J (incl P k a) φ) ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Isometric (toSR P) k Jᵀ a := by
  constructor
  · rintro ⟨φ, h⟩
    exact ⟨φ.toAddEquiv, fun e y => φ.map_smul e y, fun y y' => (hform_eq k J _ _).symm.trans (h y y')⟩
  · rintro ⟨φ, h1, h2⟩
    exact ⟨{ φ with map_smul' := h1 }, fun y y' => (hform_eq k J _ _).trans (h2 y y')⟩

theorem clsMap_mem_iff (J : Matrix (Fin r) (Fin r) E) (q) :
    clsMap P k q ∈ XSet P k J ↔ q ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.classes (toSR P) k Jᵀ := by
  constructor
  · rintro ⟨x, φ, e, h⟩
    obtain ⟨a, rfl⟩ := unitMap_surjective P k x
    exact ⟨a, clsMap_injective P k e, (isometric_iff P k J a.1).1 ⟨φ, h⟩⟩
  · rintro ⟨a, rfl, h⟩
    obtain ⟨φ, h⟩ := (isometric_iff P k J a.1).2 h
    exact ⟨unitMap P k a, φ, rfl, h⟩

theorem incl_toLocalPlus (a) : incl P k (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.toLocalPlus (toSR P) k a) =
    Algebra.TensorProduct.map (Algebra.ofId (maximalRealSubfield E) k) (AlgHom.id _ (Fld P))
      (incl P (maximalRealSubfield E) a) := by
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; exact (map_zero _).symm
  | tmul a b => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]; exact (map_add _ _ _).symm

theorem mapsCls_iff (q) (c : Cls P k) :
    MapsCls P (k := maximalRealSubfield E) (Algebra.ofId (maximalRealSubfield E) k) (clsMap P _ q) c ↔
      c = clsMap P k (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.toLocal (toSR P) k q) := by
  constructor
  · rintro ⟨x, x', e, rfl, h⟩
    obtain ⟨a, rfl⟩ := unitMap_surjective P _ x
    obtain rfl : QuotientGroup.mk a = q := clsMap_injective P _ e
    refine congrArg QuotientGroup.mk (Subtype.ext (Units.ext ?_))
    exact h.trans (incl_toLocalPlus P k a.1).symm
  · rintro rfl
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨unitMap P _ a, unitMap P k (Units.map (GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.toLocalPlus (toSR P) k).toMonoidHom a), rfl, rfl,
      incl_toLocalPlus P k a.1⟩

end Bridge

theorem rational_eq_local : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → (∀ q q' : Cls P F, q ∈ XSet P F J → q' ∈ XSet P F J → (∀ v : HeightOneSpectrum (𝓞 F), ∃ a : Cls P (Fv F v), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q a ∧ MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q' a) → (∀ w : InfinitePlace F, ∃ a : Cls P w.Completion, MapsCls P (k := F) (Algebra.ofId F w.Completion) q a ∧ MapsCls P (k := F) (Algebra.ofId F w.Completion) q' a) → q = q') ∧ ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion), (∀ v, qf v ∈ XSet P (Fv F v) J) → (∀ w, qa w ∈ XSet P w.Completion J) → (∀ᶠ v in cofinite, qf v = 1) → ∃ q : Cls P F, q ∈ XSet P F J ∧ (∀ v : HeightOneSpectrum (𝓞 F), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q (qf v)) ∧ ∀ w : InfinitePlace F, MapsCls P (k := F) (Algebra.ofId F w.Completion) q (qa w) := by
  intro E _ _ F _ σ hcm hur r P J hJ
  obtain ⟨h1, h2, h3, h4⟩ := hcm
  haveI : Algebra.IsQuadraticExtension F E := ⟨h3⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  obtain rfl : F = maximalRealSubfield E := CMExtension.eq_maximalRealSubfield E F
  obtain rfl : σ = (IsCMField.complexConj E).toAlgHom := by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact AlgHom.ext fun x => φ.injective ((h4 φ x).trans (IsCMField.complexEmbedding_complexConj E φ x).symm)
  have H := GlobalTheory.TraceClasses.rationalEqAdelic E hur r Jᵀ (fun a b => hJ.1 a b)
    (by rw [Matrix.det_transpose]; exact hJ.2) (toSR P)
  constructor
  · intro q q' hq hq' hf ha
    obtain ⟨q, rfl⟩ := clsMap_surjective P _ q
    obtain ⟨q', rfl⟩ := clsMap_surjective P _ q'
    refine congrArg _ (H.injOn ((clsMap_mem_iff P _ J q).1 hq) ((clsMap_mem_iff P _ J q').1 hq')
      (Prod.ext (funext fun v => ?_) (funext fun w => ?_)))
    · obtain ⟨a, e, e'⟩ := hf v
      exact clsMap_injective P _ (((mapsCls_iff P _ q a).1 e).symm.trans ((mapsCls_iff P _ q' a).1 e'))
    · obtain ⟨a, e, e'⟩ := ha w
      exact clsMap_injective P _ (((mapsCls_iff P _ q a).1 e).symm.trans ((mapsCls_iff P _ q' a).1 e'))
  · intro qf qa hf ha h1
    choose xf hxf using fun v => clsMap_surjective P _ (qf v)
    choose xa hxa using fun w => clsMap_surjective P _ (qa w)
    obtain ⟨q, hq, e⟩ := H.surjOn (show (xf, xa) ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.adelicClasses (toSR P) Jᵀ from
      ⟨fun v => (clsMap_mem_iff P _ J _).1 (by rw [hxf]; exact hf v),
        fun w => (clsMap_mem_iff P _ J _).1 (by rw [hxa]; exact ha w), by
        refine (Filter.eventually_cofinite.1 h1).subset fun v hv hv1 => hv ?_
        have : xf v = 1 := clsMap_injective P _ (by rw [hxf, hv1, map_one])
        exact ⟨1, RingHom.isIntegralElem_one _, RingHom.isIntegralElem_one _, this.symm⟩⟩)
    refine ⟨clsMap P _ q, (clsMap_mem_iff P _ J q).2 hq, fun v => (mapsCls_iff P _ q _).2 ?_,
      fun w => (mapsCls_iff P _ q _).2 ?_⟩
    · exact (hxf v).symm.trans (congrArg _ (congrFun (congrArg Prod.fst e) v).symm)
    · exact (hxa w).symm.trans (congrArg _ (congrFun (congrArg Prod.snd e) w).symm)

end GlobalTheory.TrEll.Hasse
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalNormClassesEqLocalUnramifiedCMStatement

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.rationalNormClasses_eq_local_unramifiedCM : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → (∀ q q' : Cls P F, q ∈ XSet P F J → q' ∈ XSet P F J → (∀ v : HeightOneSpectrum (𝓞 F), ∃ a : Cls P (Fv F v), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q a ∧ MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q' a) → (∀ w : InfinitePlace F, ∃ a : Cls P w.Completion, MapsCls P (k := F) (Algebra.ofId F w.Completion) q a ∧ MapsCls P (k := F) (Algebra.ofId F w.Completion) q' a) → q = q') ∧ ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion), (∀ v, qf v ∈ XSet P (Fv F v) J) → (∀ w, qa w ∈ XSet P w.Completion J) → (∀ᶠ v in cofinite, qf v = 1) → ∃ q : Cls P F, q ∈ XSet P F J ∧ (∀ v : HeightOneSpectrum (𝓞 F), MapsCls P (k := F) (Algebra.ofId F (Fv F v)) q (qf v)) ∧ ∀ w : InfinitePlace F, MapsCls P (k := F) (Algebra.ofId F w.Completion) q (qa w) := by
  first | exact @GlobalTheory.TrEll.Hasse.rational_eq_local | exact GlobalTheory.TrEll.Hasse.rational_eq_local | (intros; apply GlobalTheory.TrEll.Hasse.rational_eq_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalUnitaryClassesIffLocalClassFamilies

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll.RatClasses

section General

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r n : ℕ} {P : PPol σ r}
  {J : Matrix (Fin n) (Fin n) E} {k k' : Type} [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k']

theorem mapsCls_unique {ψ : k →ₐ[F] k'} {q : Cls P k} {a b : Cls P k'} (ha : MapsCls P ψ q a)
    (hb : MapsCls P ψ q b) : a = b := by
  obtain ⟨x, x', hx, rfl, ex⟩ := ha
  obtain ⟨y, y', hy, rfl, ey⟩ := hb
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 (hx.trans hy.symm))
  let m := Algebra.TensorProduct.map ψ (AlgHom.id F (Fld P))
  have hm : ∀ z, sigR k' (star' P) (m z) = m (sigR k (star' P) z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [m, sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ⟨Units.map m.toMonoidHom c, ?_⟩)
  have hc' : x.1.1 * (c.1 * sigR k (star' P) c.1) = y.1.1 := by
    have : c.1 * sigR k (star' P) c.1 = (x.1⁻¹ * y.1).1 := congrArg Units.val hc
    rw [this, Units.val_mul, Units.mul_inv_cancel_left]
  change _ = x'.1⁻¹ * y'.1
  rw [eq_inv_mul_iff_mul_eq]
  apply Units.ext
  change x'.1.1 * (m c.1 * sigR k' (star' P) (m c.1)) = y'.1.1
  rw [ex, ey, hm, ← hc', map_mul, map_mul]

theorem mapH_diagH (ψ : k →ₐ[F] k') (γ : Formalism.UG.UJ (σ : E →+* E) J) :
    mapH σ J ψ (diagH σ J k γ) = diagH σ J k' γ :=
  Subtype.ext (Units.ext (Matrix.ext fun r s => by
    change Algebra.TensorProduct.map ψ (AlgHom.id F E) ((1 : k) ⊗ₜ[F] (γ.1.1 r s)) = (1 : k') ⊗ₜ[F] (γ.1.1 r s)
    simp))

variable [NumberField F] [NumberField E] (hc : IsCMExt F E σ) (hJ : IsHermND σ J)
include hc hJ

theorem hasCls_unique {γ : HA k σ J} {q q' : Cls P k} (h : HasCls P k J γ q) (h' : HasCls P k J γ q') : q = q' := by
  obtain ⟨x, φ, h, rfl, e⟩ := h
  obtain ⟨x', φ', h', rfl, e'⟩ := h'
  exact (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hc r n P J hJ k x φ h x' φ' h').2.1 (by rw [e, e'])

theorem hasCls_of_isConj {γ γ' : HA k σ J} {q : Cls P k} (h : HasCls P k J γ q) (e : IsConj γ γ') :
    HasCls P k J γ' q := by
  obtain ⟨x, φ, h, rfl, rfl⟩ := h
  obtain ⟨g, rfl⟩ := isConj_iff.1 e
  exact (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hc r n P J hJ k x φ h x φ h).2.2.2 g

theorem isConj_of_hasCls {γ γ' : HA k σ J} {q : Cls P k} (h : HasCls P k J γ q) (h' : HasCls P k J γ' q) :
    IsConj γ γ' := by
  obtain ⟨x, φ, h, e, rfl⟩ := h
  obtain ⟨x', φ', h', e', rfl⟩ := h'
  obtain ⟨g, hg⟩ := (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hc r n P J hJ k x φ h x' φ' h').1 (e.trans e'.symm)
  exact isConj_iff.2 ⟨g, (hg _).symm⟩

theorem exists_mapsCls (ψ : k →ₐ[F] k') {γ : HA k σ J} {q : Cls P k} (h : HasCls P k J γ q) :
    ∃ q', MapsCls P ψ q q' ∧ HasCls P k' J (mapH σ J ψ γ) q' := by
  obtain ⟨x, φ, h, rfl, rfl⟩ := h
  obtain ⟨x', φ', h', e1, e2, -⟩ := GlobalTheory.T.hermitian_isometry_base_change F E σ hc r n P J hJ k k' ψ x φ h
  exact ⟨_, ⟨x, x', rfl, rfl, e1⟩, x', φ', h', rfl, e2⟩

theorem exists_mapsCls_rat (k : Type) [CommRing k] [Algebra F k] {γ : GRat σ J} {q : Cls P F}
    (h : HasCls P F J (diagH σ J F γ) q) :
    ∃ q', MapsCls P (k := F) (Algebra.ofId F k) q q' ∧ HasCls P k J (diagH σ J k γ) q' := by
  simpa only [mapH_diagH] using exists_mapsCls hc hJ (Algebra.ofId F k) h

theorem exists_hasCls_rat {P : PPol σ n} (γ : GRat σ J) (h : γ.1.1.charpoly = P.1) :
    ∃ q, HasCls P F J (diagH σ J F γ) q := by
  obtain ⟨P', e, hq⟩ := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hc n J hJ).2 γ (h ▸ P.2.2.1)
  obtain rfl : P' = P := Subtype.ext (e.symm.trans h)
  exact hq

theorem charpoly_of_hasCls {γ : GRat σ J} {q : Cls P F} (h : HasCls P F J (diagH σ J F γ) q) :
    γ.1.1.charpoly = P.1 := by
  obtain ⟨x, φ, h, -, e⟩ := h
  have h1 := (GlobalTheory.T.torusElement_charpoly_regular_centralizer F E σ hc r n P J hJ F x φ h).1
  rw [e] at h1
  apply Polynomial.map_injective (inclR (F := F) (E := E) F) (inclR (F := F) (E := E) F).injective
  rw [← h1, ← Matrix.charpoly_map]
  rfl

theorem isConj_of_diagH {γ γ' : GRat σ J} (h : IsConj (diagH σ J F γ) (diagH σ J F γ')) : IsConj γ γ' := by
  have hb := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hc n J hJ).1
  obtain ⟨g, e⟩ := isConj_iff.1 h
  obtain ⟨g, rfl⟩ := hb.2 g
  exact isConj_iff.2 ⟨g, hb.1 (by simpa only [map_mul, map_inv] using e)⟩

theorem existsUnique_hasCls_rat {P : PPol σ n} (k : Type) [CommRing k] [Algebra F k] (γ : GRat σ J)
    (h : γ.1.1.charpoly = P.1) : ∃! q, HasCls P k J (diagH σ J k γ) q := by
  obtain ⟨q, hq⟩ := exists_hasCls_rat hc hJ γ h
  obtain ⟨q', -, hq'⟩ := exists_mapsCls_rat hc hJ k hq
  exact ⟨q', hq', fun _ h => hasCls_unique hc hJ h hq'⟩

theorem exists_common {γ γ' : GRat σ J} {q q' : Cls P F} (h : HasCls P F J (diagH σ J F γ) q)
    (h' : HasCls P F J (diagH σ J F γ') q')
    (H : ∀ a, HasCls P k J (diagH σ J k γ) a → HasCls P k J (diagH σ J k γ') a) :
    ∃ a, MapsCls P (k := F) (Algebra.ofId F k) q a ∧ MapsCls P (k := F) (Algebra.ofId F k) q' a := by
  obtain ⟨a, h1, h2⟩ := exists_mapsCls_rat hc hJ k h
  obtain ⟨b, h3, h4⟩ := exists_mapsCls_rat hc hJ k h'
  exact ⟨a, h1, hasCls_unique hc hJ h4 (H a h2) ▸ h3⟩

theorem hasCls_of_mapsCls {γ : GRat σ J} {q : Cls P F} (h : HasCls P F J (diagH σ J F γ) q) {a : Cls P k}
    (H : MapsCls P (k := F) (Algebra.ofId F k) q a) : HasCls P k J (diagH σ J k γ) a := by
  obtain ⟨b, h1, h2⟩ := exists_mapsCls_rat hc hJ k h
  exact mapsCls_unique h1 H ▸ h2

end General

theorem rat_classes_iff_local (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E)
    (hc : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E)
    (hJ : IsHermND σ J) :
    (∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → (∀ v, ∃! q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q) ∧
      (∀ w, ∃! q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q) ∧
      ∀ᶠ v in cofinite, HasCls P _ J (proj σ J v (ratEmb σ J γ)) 1) ∧
    (∀ γ γ' : GRat σ J, γ.1.1.charpoly = P.1 → γ'.1.1.charpoly = P.1 → (IsConj γ γ' ↔
      (∀ v q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q → HasCls P _ J (proj σ J v (ratEmb σ J γ')) q) ∧
        ∀ w q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q → HasCls P _ J (projArch σ J w (ratEmb σ J γ')) q)) ∧
    ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion),
      (∀ v, qf v ∈ XSet P _ J) → (∀ w, qa w ∈ XSet P _ J) → (∀ᶠ v in cofinite, qf v = 1) →
      ∃ γ : GRat σ J, γ.1.1.charpoly = P.1 ∧ (∀ v, HasCls P _ J (proj σ J v (ratEmb σ J γ)) (qf v)) ∧
        ∀ w, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) (qa w) := by
  have e1 : ∀ v γ, proj σ J v (ratEmb σ J γ) = diagH σ J (Fv F v) γ := proj_ratEmb σ J
  have e2 : ∀ w γ, projArch σ J w (ratEmb σ J γ) = diagH σ J w.Completion γ := projArch_ratEmb σ J
  obtain ⟨H1, H2⟩ := GlobalTheory.T.rationalNormClasses_eq_local_unramifiedCM E F σ hc hu r P J hJ
  refine ⟨fun γ h => ⟨fun v => ?_, fun w => ?_, ?_⟩, fun γ γ' h h' => ⟨fun e => ⟨fun v q hq => ?_, fun w q hq => ?_⟩,
    fun H => ?_⟩, fun qf qa hf ha h1 => ?_⟩
  · rw [e1]; exact existsUnique_hasCls_rat hc hJ _ γ h
  · rw [e2]; exact existsUnique_hasCls_rat hc hJ _ γ h
  · have := isLattice_stdLattice (E := E) (n := r)
    filter_upwards [GlobalTheory.T.eventually_unitaryTorus_orbitalClass_trivial_local F E σ hc r P J hJ (stdLattice E r),
      eventually_proj_mem_stabLoc σ J (stdLattice E r) (ratEmb σ J γ)] with v hv hm
    obtain ⟨q, hq, -⟩ := existsUnique_hasCls_rat hc hJ (Fv F v) γ h
    rw [← e1] at hq
    exact hv.2.1 _ q hq ⟨1, by simpa only [inv_one, one_mul, mul_one] using hm⟩ ▸ hq
  · exact hasCls_of_isConj hc hJ hq ((proj σ J v).map_isConj ((ratEmb σ J).map_isConj e))
  · exact hasCls_of_isConj hc hJ hq ((projArch σ J w).map_isConj ((ratEmb σ J).map_isConj e))
  · simp only [e1, e2] at H
    obtain ⟨q, hq⟩ := exists_hasCls_rat hc hJ γ h
    obtain ⟨q', hq'⟩ := exists_hasCls_rat hc hJ γ' h'
    obtain rfl : q = q' := H1 q q' (hq.mem P) (hq'.mem P) (fun v => exists_common hc hJ hq hq' (H.1 v))
      fun w => exists_common hc hJ hq hq' (H.2 w)
    exact isConj_of_diagH hc hJ (isConj_of_hasCls hc hJ hq hq')
  · obtain ⟨q, hq, h2, h3⟩ := H2 qf qa hf ha h1
    obtain ⟨g, hg⟩ := exists_hasCls P hq
    obtain ⟨γ, rfl⟩ := (GlobalTheory.T.exists_torusClass_of_irreducible_charpoly_unitary F E σ hc r J hJ).1.2 g
    refine ⟨γ, charpoly_of_hasCls hc hJ hg, fun v => ?_, fun w => ?_⟩
    · rw [e1]; exact hasCls_of_mapsCls hc hJ hg (h2 v)
    · rw [e2]; exact hasCls_of_mapsCls hc hJ hg (h3 w)

end GlobalTheory.TrEll.RatClasses
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalUnitaryClassesIffLocalClassFamiliesStatement

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.rational_unitary_classes_iff_local_class_families : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → (∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → (∀ v, ∃! q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q) ∧ (∀ w, ∃! q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q) ∧ ∀ᶠ v in cofinite, HasCls P _ J (proj σ J v (ratEmb σ J γ)) 1) ∧ (∀ γ γ' : GRat σ J, γ.1.1.charpoly = P.1 → γ'.1.1.charpoly = P.1 → (IsConj γ γ' ↔ (∀ v q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q → HasCls P _ J (proj σ J v (ratEmb σ J γ')) q) ∧ ∀ w q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q → HasCls P _ J (projArch σ J w (ratEmb σ J γ')) q)) ∧ ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion), (∀ v, qf v ∈ XSet P _ J) → (∀ w, qa w ∈ XSet P _ J) → (∀ᶠ v in cofinite, qf v = 1) → ∃ γ : GRat σ J, γ.1.1.charpoly = P.1 ∧ (∀ v, HasCls P _ J (proj σ J v (ratEmb σ J γ)) (qf v)) ∧ ∀ w, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) (qa w) := by
  first | exact @GlobalTheory.TrEll.RatClasses.rat_classes_iff_local | exact GlobalTheory.TrEll.RatClasses.rat_classes_iff_local | (intros; apply GlobalTheory.TrEll.RatClasses.rat_classes_iff_local <;> assumption)
end
end
