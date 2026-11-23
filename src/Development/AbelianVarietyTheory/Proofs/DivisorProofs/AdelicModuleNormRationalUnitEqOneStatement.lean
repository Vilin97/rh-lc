module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelesHaarMeasureCovolumeOne
import Mathlib.LinearAlgebra.Charpoly.BaseChange

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CountableOfNumberField

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal Pointwise

noncomputable section

namespace GlobalTheory.SWQ

theorem countable_of_numberField (F : Type) [Field F] [NumberField F] : Countable F :=
  Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

theorem map_unit_mul_eq (F : Type) [Field F] [NumberField F] (ν : Measure (AF F)) [ν.IsAddHaarMeasure]
    (w : (AF F)ˣ) : ν.map (fun x => w • x) = (distribHaarChar (AF F) w⁻¹ : ℝ≥0∞) • ν := by
  ext S hS
  rw [Measure.map_apply (measurable_const_smul w) hS, Set.preimage_smul, Measure.smul_apply, smul_eq_mul,
    distribHaarChar_mul]

theorem modrat_main : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ν : Measure (AF F)), IsCov1 ν →
    ∀ t : F, t ≠ 0 → ν.map (fun x => (algebraMap F (AF F) t) * x) = ν := by
  intro F _ _ _ ν hν t ht
  obtain ⟨hH, D, _, hD, hD1⟩ := hν
  haveI := hH
  haveI := countable_of_numberField F
  set K := (algebraMap F (AF F)).range.toAddSubgroup with hK
  haveI : Countable K := by
    refine Function.Surjective.countable (f := fun r : F => (⟨algebraMap F (AF F) r, ⟨r, rfl⟩⟩ : K)) ?_
    rintro ⟨x, ⟨r, rfl⟩⟩
    exact ⟨r, rfl⟩
  have htu : IsUnit (algebraMap F (AF F) t) := (isUnit_iff_ne_zero.mpr ht).map _
  set u : (AF F)ˣ := htu.unit with hu
  have hmul : (fun x : AF F => (algebraMap F (AF F) t) * x) = fun x => u • x := by
    funext x; rfl
  rw [hmul]

  let e : K ≃ K :=
    { toFun := fun g => ⟨algebraMap F (AF F) t⁻¹ * g, by
        obtain ⟨r, hr⟩ := g.2; exact ⟨t⁻¹ * r, by rw [map_mul, hr]⟩⟩
      invFun := fun g => ⟨algebraMap F (AF F) t * g, by
        obtain ⟨r, hr⟩ := g.2; exact ⟨t * r, by rw [map_mul, hr]⟩⟩
      left_inv := fun g => by
        ext; simp only; rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
      right_inv := fun g => by
        ext; simp only; rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul] }
  have hqmp : Measure.QuasiMeasurePreserving (MulAction.toPerm u).symm ν ν := by
    refine ⟨(measurable_const_smul u⁻¹).aemeasurable, ?_⟩
    have : ⇑(MulAction.toPerm u).symm = fun x : AF F => u⁻¹ • x := rfl
    rw [this, map_unit_mul_eq F ν u⁻¹]
    exact Measure.AbsolutelyContinuous.smul_left (Measure.AbsolutelyContinuous.refl _) _
  have hD' : IsAddFundamentalDomain K (MulAction.toPerm u '' D) ν := by
    refine hD.image_of_equiv (MulAction.toPerm u) hqmp e ?_
    intro g x
    change u • ((e g : AF F) + x) = (g : AF F) + u • x
    change algebraMap F (AF F) t * (algebraMap F (AF F) t⁻¹ * (g : AF F) + x) = (g : AF F) + algebraMap F (AF F) t * x
    rw [mul_add, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
  have himg : (MulAction.toPerm u '' D) = u • D := rfl
  have h1 : ν (u • D) = 1 := by rw [← himg, hD'.measure_eq hD, hD1]
  have hchar : distribHaarChar (AF F) u = 1 := by
    have := distribHaarChar_mul ν u D
    rw [h1, hD1, mul_one] at this
    exact_mod_cast this
  rw [map_unit_mul_eq F ν u, map_inv, hchar, inv_one, ENNReal.coe_one, one_smul]

end GlobalTheory.SWQ
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicModuleNormRationalUnitEqOne

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

open MeasureTheory

namespace GlobalTheory.NormModule

theorem norm_inclR (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (z : E) :
    Algebra.norm (AF F) (inclR (F := F) (AF F) z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = algebraMap F (AF F) (Algebra.norm F z) := by
  have e : (inclR (F := F) (AF F) z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = (1 : AF F) ⊗ₜ[F] z := rfl
  rw [e, Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange]

theorem modu_rat (F : Type) [Field F] [NumberField F] (w : (AF F)ˣ) (t : F) (hw : (w : AF F) = algebraMap F (AF F) t) :
    distribHaarChar (AdeleRing (𝓞 F) F) w = 1 := by
  haveI : Nontrivial (AF F) :=
    nontrivial_of_ne 0 1 (fun h => zero_ne_one (congrArg (fun a : AF F => a.1) h))
  have ht : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at hw
    exact not_isUnit_zero (hw ▸ w.isUnit)
  obtain ⟨ν, hν⟩ := GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one F
  haveI := hν.1
  have h1 := GlobalTheory.SWQ.modrat_main F 0 ν hν t ht
  have h2 := GlobalTheory.SWQ.map_unit_mul_eq F ν w
  have e : (fun x : AF F => w • x) = fun x => algebraMap F (AF F) t * x := by
    funext x; rw [Units.smul_def, smul_eq_mul, hw]
  rw [e, h1] at h2
  obtain ⟨K, hKc, hK0⟩ : ∃ K : Set (AF F), IsCompact K ∧ K ∈ nhds (0 : AF F) := exists_compact_mem_nhds 0
  have h3 := congrArg (fun m : Measure (AF F) => m K) h2
  simp only [Measure.smul_apply, smul_eq_mul] at h3
  have h4 : ((distribHaarChar (AF F) w⁻¹ : NNReal) : ENNReal) = 1 :=
    ((ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds ν hK0).ne' hKc.measure_lt_top.ne).1
      (h3.symm.trans (one_mul _).symm))
  have h5 : distribHaarChar (AF F) w⁻¹ = 1 := by exact_mod_cast h4
  rw [map_inv, inv_eq_one] at h5
  exact h5

end GlobalTheory.NormModule

theorem GlobalTheory.NormModule.modu_norm_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (u : (AE F E)ˣ) (z : E), (u : AE F E) = inclR (AF F) z → (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) u) = 1 := by
  intro F E _ _ _ _ _ u z hu
  apply GlobalTheory.NormModule.modu_rat F _ (Algebra.norm F z)
  rw [Units.coe_map, hu, GlobalTheory.NormModule.norm_inclR]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicModuleNormRationalUnitEqOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.adelicModule_norm_rationalUnit_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (u : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) (z : E), (u : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = inclR (AF F) z → (adeleClass F).modu (Units.map (Algebra.norm (AF F) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →* AF F) u) = 1 := by
  first | exact @GlobalTheory.NormModule.modu_norm_rat | exact GlobalTheory.NormModule.modu_norm_rat | (intros; apply GlobalTheory.NormModule.modu_norm_rat <;> assumption)
end
end
