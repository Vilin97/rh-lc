module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFixedEqPadicInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisExistsTPowMulThetaNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfFullGaloisLineUnitsStatement
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedPeriodAinfUnit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedOfInertiaFrobeniusStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateCharacterFiniteOnInertiaOfEigenvectorStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisGaloisActionFontaineTEqCyclotomic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisInvariantsBcrisEqMaxUnramified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLawsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfFrobeniusUnitEigenvectorGaloisLine

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.UnitLine

theorem exists_fixed {R : Type} [CommRing R] (φ σ : R →+* R) (h : ∀ a, φ (σ a) = σ (φ a)) (w c : R)
    (hw : IsUnit w) (hc : IsUnit c) (hσ : σ c = c) (hφ : φ w = c * w) :
    ∃ a, φ a = a ∧ σ w = a * w := by
  obtain ⟨v, hv⟩ := hw.exists_right_inv
  have e : σ w = σ w * v * w := by linear_combination (-σ w) * hv
  refine ⟨σ w * v, ?_, e⟩
  have h1 := congrArg φ e
  rw [map_mul φ _ w, h, hφ, map_mul σ, hσ] at h1
  apply (hc.mul hw).mul_right_cancel
  rw [← h1]
  linear_combination (-c * σ w) * hv

theorem sigma_unit_eigen : ∀ (l : ℕ) [Fact l.Prime] (w : Per.Ainf l) (u : ℤ_[l]ˣ), IsUnit w → Per.φA l w = Per.zA l u * w → ∀ g : GQ l, ∃ z : ℤ_[l], Per.σB g (Per.aB l w) = Per.zB l z * Per.aB l w := by
  intro l _ w u hw hφ g
  obtain ⟨-, -, -, -, -, h6, -, h8, -⟩ := ActLaws.act_laws l
  obtain ⟨a, ha, e⟩ := exists_fixed (Per.φA l) (Per.σA g) (ActLaws.φA_σA g) w (Per.zA l u) hw
    (u.isUnit.map _) (h8 g u) hφ
  obtain ⟨z, hz⟩ := phi_fixed_eq_padicInt l (algebraMap (Per.Ainf l) (Per.Acris l) a)
    ((PhiFix.phiA_alg l a).trans (congrArg _ ha))
  have hb : Per.aB l a = Per.zB l z := by
    rw [GlobalTheory.RingIface.zB_eq_aB_zA, GlobalTheory.RingIface.aB_eq_alg, GlobalTheory.RingIface.aB_eq_alg, hz]
  exact ⟨z, by rw [h6, e, map_mul, hb]⟩

end GlobalTheory.UnitLine
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfFrobeniusUnitEigenvectorGaloisLineStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.ainf_frobenius_unit_eigenvector_galois_line : ∀ (l : ℕ) [Fact l.Prime] (w : Per.Ainf l) (u : ℤ_[l]ˣ), IsUnit w → Per.φA l w = Per.zA l u * w → ∀ g : GQ l, ∃ z : ℤ_[l], Per.σB g (Per.aB l w) = Per.zB l z * Per.aB l w := by
  first | exact @GlobalTheory.UnitLine.sigma_unit_eigen | exact GlobalTheory.UnitLine.sigma_unit_eigen | (intros; apply GlobalTheory.UnitLine.sigma_unit_eigen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCharacterOfGaloisStableLineCLTate

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem exists_unit_character_of_stable_line (l : ℕ) [Fact l.Prime] (y : ℂ_[l]) (hy : y ≠ 0)
    (h : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σC g y = algebraMap ℚ_[l] ℂ_[l] x * y) :
    ∃ η : GQ l →* ℤ_[l]ˣ, ∀ g : GQ l,
      Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y := by
  choose x hx using h
  have hn : ∀ g, ‖x g‖ = 1 := fun g => by
    have h1 := GlobalTheory.RingBasics.norm_σC g y
    rw [hx, norm_mul, norm_algebraMap'] at h1
    exact mul_right_cancel₀ (norm_ne_zero_iff.2 hy) (h1.trans (one_mul _).symm)
  have hm : ∀ g k, x (g * k) = x g * x k := fun g k => by
    apply (algebraMap ℚ_[l] ℂ_[l]).injective
    apply mul_right_cancel₀ hy
    rw [← hx, GlobalTheory.RingBasics.σC_mul, hx k, map_mul, TateTwist.σC_algebraMap, hx g, map_mul]
    ring
  refine ⟨MonoidHom.mk' (fun g => PadicInt.mkUnits (hn g)) fun g k => ?_, fun g => hx g⟩
  apply Units.ext
  apply Subtype.ext
  exact hm g k

end GlobalTheory.Per
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCharacterOfGaloisStableLineCLTateStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_unitCharacter_of_galoisStable_line_cLTate : ∀ (l : ℕ) [Fact l.Prime] (y : ℂ_[l]), y ≠ 0 → (∀ g : GQ l, ∃ x : ℚ_[l], Per.σC g y = algebraMap ℚ_[l] ℂ_[l] x * y) → ∃ η : GQ l →* ℤ_[l]ˣ, ∀ g : GQ l, Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y := by
  first | exact @GlobalTheory.Per.exists_unit_character_of_stable_line | exact GlobalTheory.Per.exists_unit_character_of_stable_line | (intros; apply GlobalTheory.Per.exists_unit_character_of_stable_line <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedPeriodAinfUnitStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_unramified_period_ainf_unit : ∀ (l : ℕ) [Fact l.Prime] (F : GQ l), (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l) → ∀ u : ℤ_[l]ˣ, ∃ w : Per.Ainf l, IsUnit w ∧ (∀ g ∈ (MaximalUnramifiedExtension l).fixingSubgroup, Per.σA g w = w) ∧ Per.σA F w = Per.zA l u * w ∧ Per.φA l w = Per.zA l u * w := by
  first | exact @GlobalTheory.MemLoc.exists_unramified_period | exact GlobalTheory.MemLoc.exists_unramified_period | (intros; apply GlobalTheory.MemLoc.exists_unramified_period <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisInvariantsBcrisEqMaxUnramifiedStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galoisInvariants_Bcris_eq_maxUnramified : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l) (b : Per.Bcris l), (∀ g ∈ GK K, Per.σB g b = b) → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ C.u c = b := by
  first | exact @GlobalTheory.MemLoc.InvCris.invariants_Bcris | exact GlobalTheory.MemLoc.InvCris.invariants_Bcris | (intros; apply GlobalTheory.MemLoc.InvCris.invariants_Bcris <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfTensorInj

section

@[expose] public section

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.CrisRegular
variable {l : ℕ} [Fact l.Prime] (C : Core l)

theorem exists_frob (C : Core l) :
    ∃ F : GQ l, ∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l := by
  obtain ⟨g, hg⟩ := FrobLaws.exists_ext C.σ
  refine ⟨g, fun ζ m hm hlm hζ => ?_⟩
  let c : ↥(MaximalUnramifiedExtension l) := ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩⟩
  have := C.σ_root c m hm hlm (Subtype.ext hζ)
  rw [show ζ = (c : Om l) from rfl, hg, this]; rfl

theorem qB_coe (z : ℤ_[l]) : C.qB (z : ℚ_[l]) = Per.zB l z := (GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.2.1 z

theorem ι_aB (a : Per.Ainf l) :
    C.ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
  rw [GlobalTheory.RingIface.aB_eq_alg, C.ι_j, GlobalTheory.RingIface.tower, C.j_cris.on0, Subalgebra.coe_algebraMap]
  simp only [aDp, RingHom.comp_apply]

theorem theta_eig {b : Per.Bcris l} {y : Per.BdRp l}
    (h : C.ι b = algebraMap (Per.BdRp l) (Per.BdR l) y) {g : GQ l} {x : ℚ_[l]}
    (hx : Per.σB g b = C.qB x * b) :
    Per.σC g (Per.θD l y) = algebraMap ℚ_[l] ℂ_[l] x * Per.θD l y := by
  have h1 := congrArg C.ι hx
  rw [(GlobalTheory.T.localPeriodRingsData_unramified_laws l C).2.2.2.2.1, map_mul, h, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1,
    show C.ι (C.qB x) = _ from C.ι_u _, ← map_mul] at h1
  have h2 := congrArg (Per.θD l) ((BdRField.bdR_isField l).2.1 h1)
  rw [(thetaD_props l).2.2.2.2, map_mul, C.o_sec.th] at h2
  exact h2

theorem σB_tB (g : GQ l) : Per.σB g C.tB = C.qB ((C.χ g : ℤ_[l]) : ℚ_[l]) * C.tB := by
  rw [qB_coe, Core.tB, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1, TAct.t_act l C g, map_mul,
    GlobalTheory.RingIface.zB_eq_aB_zA, GlobalTheory.RingIface.aB_eq_alg]

theorem isUnit_of_theta {b : Per.Bcris l} {y : Per.BdRp l}
    (h : C.ι b = algebraMap (Per.BdRp l) (Per.BdR l) y) (hy : Per.θD l y ≠ 0)
    (hb : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) : IsUnit b := by
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_unitCharacter_of_galoisStable_line_cLTate l _ hy fun g => (hb g).imp fun x hx => theta_eig C h hx
  obtain ⟨N, hN, hI⟩ := GlobalTheory.T.tate_character_finite_on_inertia_of_eigenvector l η _ hy hη
  obtain ⟨F, hF⟩ := exists_frob C
  obtain ⟨w, hw, hwI, hwF, hwφ⟩ := GlobalTheory.T.exists_unramified_period_ainf_unit l F hF (η F ^ N)⁻¹
  have h2 : C.ι (b ^ N * Per.aB l w) = algebraMap (Per.BdRp l) (Per.BdR l) (y ^ N * aDp l w) := by
    rw [map_mul, map_pow, h, ι_aB, map_mul, map_pow]
  have hθ : Per.θD l (y ^ N * aDp l w) ≠ 0 := by
    rw [map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero _ hy) ((hw.map _).map _).ne_zero
  have hact : ∀ g : GQ l, Per.σC g (Per.θD l (y ^ N * aDp l w)) =
      algebraMap ℚ_[l] ℂ_[l] (((η g ^ N : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) * Per.θD l y ^ N *
        Per.θD l (aDp l (Per.σA g w)) := by
    intro g
    rw [map_mul, map_mul, map_pow, map_pow, hη, ← (thetaD_props l).2.2.2.2,
      (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.1, mul_pow, ← map_pow, Units.val_pow_eq_pow_val,
      PadicInt.coe_pow]
  have hfix := GlobalTheory.T.fixed_of_fixed_inertia_of_fixed_frobenius l F hF (Per.θD l (y ^ N * aDp l w))
    (fun g hg => by rw [hact, hI g hg, hwI g hg]; simp)
    (by
      rw [hact, hwF, map_mul, map_mul, ← C.o_sec.z, C.o_sec.th, map_mul, map_pow]
      have e : algebraMap ℚ_[l] ℂ_[l] (((η F ^ N : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) *
          algebraMap ℚ_[l] ℂ_[l] ((((η F ^ N)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = 1 := by
        rw [← map_mul, ← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one, map_one]
      have e' : ((algebraMap ℚ_[l] (Om l) ((((η F ^ N)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) : Om l) : ℂ_[l]) =
        algebraMap ℚ_[l] ℂ_[l] ((((η F ^ N)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := rfl
      rw [e']
      linear_combination (Per.θD l y ^ N * Per.θD l (aDp l w)) * e)
  have hinv : ∀ g : GQ l, Per.σB g (b ^ N * Per.aB l w) = b ^ N * Per.aB l w := by
    intro g
    obtain ⟨x, hx⟩ := hb g
    obtain ⟨z, hz⟩ := GlobalTheory.T.ainf_frobenius_unit_eigenvector_galois_line l w _ hw hwφ g
    have e : Per.σB g (b ^ N * Per.aB l w) = C.qB (x ^ N * z) * (b ^ N * Per.aB l w) := by
      rw [map_mul, map_pow, hx, hz, map_mul, map_pow, qB_coe]
      ring
    have e2 := theta_eig C h2 e
    rw [hfix] at e2
    have e3 : algebraMap ℚ_[l] ℂ_[l] (x ^ N * z) = 1 := mul_right_cancel₀ hθ (by rw [one_mul, ← e2])
    have e4 : x ^ N * (z : ℚ_[l]) = 1 := (algebraMap ℚ_[l] ℂ_[l]).injective (by rw [e3, map_one])
    rw [e, e4, map_one, one_mul]
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.galoisInvariants_Bcris_eq_maxUnramified l C ⟨⊥, inferInstance⟩ _ fun g _ => hinv g
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [← hc, map_zero, map_zero] at h2
    apply hθ
    rw [(BdRField.bdR_isField l).2.1 (h2.symm.trans (map_zero _).symm), map_zero]
  have hu : IsUnit (b ^ N * Per.aB l w) := hc ▸ (Ne.isUnit hc0).map C.u
  exact (isUnit_pow_iff hN.ne').1 (isUnit_of_mul_isUnit_left hu)

theorem isUnit_of_line (b : Per.Bcris l) (h0 : b ≠ 0)
    (hb : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) : IsUnit b := by
  obtain ⟨m, n, b', y, e, hy, hθ⟩ := GlobalTheory.T.bcris_exists_tPow_mul_theta_ne_zero l C b h0
  have ht : IsUnit C.tB := (core_t_unit_fil l C).1
  have hu : IsUnit b' := isUnit_of_theta C hy hθ fun g => by
    obtain ⟨x, hx⟩ := hb g
    set a : ℚ_[l] := ((C.χ g : ℤ_[l]) : ℚ_[l]) with ha
    have ha0 : a ≠ 0 := by
      rw [ha]
      exact PadicInt.coe_ne_zero.2 (C.χ g).ne_zero
    refine ⟨x * a ^ m * (a ^ n)⁻¹, ?_⟩
    have e1 := congrArg (Per.σB g) e
    rw [map_mul, map_mul, map_pow, map_pow, hx, σB_tB, ← ha] at e1
    have e2 : C.qB a ^ n * C.qB (a ^ n)⁻¹ = 1 := by
      rw [← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ ha0), map_one]
    apply (ht.pow n).mul_left_cancel
    rw [map_mul, map_mul, map_pow]
    linear_combination (-C.qB (a ^ n)⁻¹) * e1 + (C.qB x * C.qB a ^ m * C.qB (a ^ n)⁻¹) * e -
      (C.tB ^ n * Per.σB g b') * e2
  exact isUnit_of_mul_isUnit_left (e ▸ (ht.pow n).mul hu)

end GlobalTheory.MemLoc.CrisRegular

namespace GlobalTheory.MemLoc

theorem core_regular (l : ℕ) [Fact l.Prime] (C : Core l) : C.Regular :=
  GlobalTheory.T.bcris_regular_of_full_galois_line_units l C (CrisRegular.isUnit_of_line C)

theorem regular_of_tensorInj : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.TensorInj → C.Regular :=
  fun l _ C _ => core_regular l C

end GlobalTheory.MemLoc
end
end
end
