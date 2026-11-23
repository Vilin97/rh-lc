module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyLatR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
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
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeKernelOfSplitCentralOneParamStatement
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousSplitCentre
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Matrix
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeGLAdelicTensorRationalTimesExpInt

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.GLOneVol

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange GlobalTheory.CuspRep.CuspidalL2GL

theorem symm_mem_latR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {g : GlobalTheory.CuspRep.GA E k} (hg : g ∈ GlobalTheory.UnitaryBC.latticeGL E k) :
    (glTens F E k).symm g ∈ latR F E k := by
  obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hg
  rw [map_mul, map_zpow]
  refine mul_mem (Subgroup.mem_sup_left ⟨γ, ?_⟩) (zpow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) n)
  apply (glTens F E k).injective
  rw [glTens_bc, ContinuousMulEquiv.apply_symm_apply]

def latEquiv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [_root_.NumberField.IsTotallyComplex E] (k : ℕ) : GlobalTheory.UnitaryBC.latticeGL E k ≃ latR F E k where
  toFun g := ⟨(glTens F E k).symm g, symm_mem_latR g.2⟩
  invFun x := ⟨glTens F E k x, latR_le k x.2⟩
  left_inv g := Subtype.ext ((glTens F E k).apply_symm_apply _)
  right_inv x := Subtype.ext ((glTens F E k).symm_apply_apply _)

theorem finvol_tens : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [_root_.NumberField.IsTotallyComplex E] (k : ℕ) [MeasurableSpace (GL (Fin k) (AF F ⊗[F] E))]
    [BorelSpace (GL (Fin k) (AF F ⊗[F] E))] (ν : Measure (GL (Fin k) (AF F ⊗[F] E)))
    (D : Set (GL (Fin k) (AF F ⊗[F] E))), ν.IsHaarMeasure → IsFundamentalDomain (latR F E k) D ν → ν D ≠ ⊤ := by
  intro F E _ _ _ _ _ _ k _ _ ν D hν hD
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  let f := (glTens F E k).toHomeomorph.toMeasurableEquiv
  let μ : Measure (GlobalTheory.CuspRep.GA E k) := ν.map f
  haveI : μ.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map ν (glTens F E k)
  have hq : Measure.QuasiMeasurePreserving f.symm μ ν :=
    (MeasurePreserving.mk f.symm.measurable (f.map_symm_map)).quasiMeasurePreserving
  have hD' : IsFundamentalDomain (GlobalTheory.UnitaryBC.latticeGL E k) (f '' D) μ :=
    hD.image_of_equiv f.toEquiv hq (latEquiv F E k) fun g x => by
      change glTens F E k ((glTens F E k).symm g * x) = g * glTens F E k x
      rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  have h1 : ν D = μ (f '' D) := by
    rw [f.map_apply, f.preimage_image]
  rw [h1, ← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hD']
  haveI := (GlobalTheory.CovolGL.finvol E k μ).1
  exact measure_ne_top _ _

end GlobalTheory.GLOneVol
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeGLAdelicTensorRationalTimesExpIntStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

theorem _root_.GlobalTheory.T.finite_covolume_GL_adelicTensor_rationalTimesExpInt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ) [MeasurableSpace (GL (Fin k) (AF F ⊗[F] E))] [BorelSpace (GL (Fin k) (AF F ⊗[F] E))] (ν : Measure (GL (Fin k) (AF F ⊗[F] E))) (D : Set (GL (Fin k) (AF F ⊗[F] E))), ν.IsHaarMeasure → IsFundamentalDomain (GlobalTheory.GLOneVol.latR F E k) D ν → ν D ≠ ⊤ := by
  first | exact @GlobalTheory.GLOneVol.finvol_tens | exact GlobalTheory.GLOneVol.finvol_tens | (intros; apply GlobalTheory.GLOneVol.finvol_tens <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogTensorIdeleAbsDetExpScalarCentreEqMul

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.GLOneVol

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume GlobalTheory.OneRep.SplitTwist

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem idl_det_eq (k : ℕ) (g : GL (Fin k) (AF F ⊗[F] E)) :
    GlobalTheory.TateConv.idl F E (Matrix.GeneralLinearGroup.det g) = Matrix.GeneralLinearGroup.det (glTens F E k g) := by
  ext
  change GlobalTheory.TateConv.tens F E (g : Matrix (Fin k) (Fin k) (AF F ⊗[F] E)).det =
    ((GlobalTheory.TateConv.tens F E).toRingEquiv.toRingHom.mapMatrix (g : Matrix (Fin k) (Fin k) (AF F ⊗[F] E))).det
  exact RingHom.map_det (GlobalTheory.TateConv.tens F E).toRingEquiv.toRingHom _

variable [_root_.NumberField.IsTotallyComplex E]

theorem absE_det_cR (k : ℕ) (t : ℝ) :
    ((absE F E (Matrix.GeneralLinearGroup.det (cR F E k t)) : ℝ≥0) : ℝ) =
      ideleNorm (E := E) (Matrix.GeneralLinearGroup.det (GlobalTheory.UnitaryBC.splitCentre E k t)) := by
  rw [GlobalTheory.TateConv.absE_eq, idl_det_eq, glTens_cR]
  rfl

end GlobalTheory.GLOneVol

theorem GlobalTheory.GLOneVol.log_absE_det_cR : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [_root_.NumberField.IsTotallyComplex E] (k : ℕ), 1 ≤ k → ∃ a : ℝ, a ≠ 0 ∧ ∀ t : ℝ,
      Real.log ((absE F E (Matrix.GeneralLinearGroup.det (GlobalTheory.GLOneVol.cR F E k t)) : ℝ≥0) : ℝ) = a * t := by
  intro F E _ _ _ _ _ _ k hk
  let D : ℝ →+ ℝ := AddMonoidHom.mk'
    (fun t => Real.log (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (E := E)
      (Matrix.GeneralLinearGroup.det (GlobalTheory.UnitaryBC.splitCentre E k t)))) fun x y => by
      rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_add, map_mul, map_mul,
        Real.log_mul (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _)]
  have hD : Continuous D :=
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleNorm.comp (Matrix.GeneralLinearGroup.continuous_det.comp
      GlobalTheory.OneRep.SplitTwist.continuous_splitCentre)).log fun _ => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _
  have hDt : ∀ t, D t = t * D 1 := fun t => by simpa using map_real_smul D hD t 1
  have hD1 : 0 < D 1 := by
    change 0 < Real.log (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (E := E)
      (Matrix.GeneralLinearGroup.det (GlobalTheory.UnitaryBC.splitCentre E k 1)))
    rw [GlobalTheory.CuspRep.CuspidalL2GL.det_splitCentre_one, map_pow, Real.log_pow]
    exact mul_pos (by exact_mod_cast hk) (Real.log_pos (GlobalTheory.IdeleCovolume.one_lt_ideleNorm_eIdele E))
  refine ⟨D 1, hD1.ne', fun t => ?_⟩
  rw [GlobalTheory.GLOneVol.absE_det_cR, mul_comm]
  exact hDt t
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogTensorIdeleAbsDetExpScalarCentreEqMulStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

theorem _root_.GlobalTheory.T.log_tensorIdeleAbs_det_expScalarCentre_eq_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ), 1 ≤ k → ∃ a : ℝ, a ≠ 0 ∧ ∀ t : ℝ, Real.log ((absE F E (Matrix.GeneralLinearGroup.det (GlobalTheory.GLOneVol.cR F E k t)) : ℝ≥0) : ℝ) = a * t := by
  first | exact @GlobalTheory.GLOneVol.log_absE_det_cR | exact GlobalTheory.GLOneVol.log_absE_det_cR | (intros; apply GlobalTheory.GLOneVol.log_absE_det_cR <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneAdelicGLLocallyCompactDiscreteFiniteCovol

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

open GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.GLOneVol

namespace GlobalTheory.GLOneVol

section Help

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_bc {k : ℕ} (γ : GL (Fin k) E) :
    Matrix.GeneralLinearGroup.det (bc (inclR (F := F) (AF F)) γ : GL (Fin k) (AF F ⊗[F] E)) =
      Units.map (inclR (F := F) (AF F)).toMonoidHom (Matrix.GeneralLinearGroup.det γ) :=
  Units.ext (RingHom.map_det _ _).symm

theorem absE_pos (x : (AF F ⊗[F] E)ˣ) : 0 < (absE F E x : ℝ) := by
  have h : absE F E x * absE F E x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have : absE F E x ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h
  exact_mod_cast pos_iff_ne_zero.2 this

end Help

theorem glOne_finvol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (k : ℕ), LocallyCompactSpace ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ∧ SecondCountableTopology ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ∧ DiscreteTopology ((bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range.subgroupOf ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) ∧ ∀ [MeasurableSpace (GL (Fin k) (AF F ⊗[F] E))] [BorelSpace (GL (Fin k) (AF F ⊗[F] E))] (π : Measure ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) (DM : Set ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker), π.IsHaarMeasure → IsFundamentalDomain ((bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range.subgroupOf ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) DM π → π DM ≠ ⊤ := by
  intro F E _ _ _ _ _ σ hCM k
  haveI : IsTotallyComplex E := hCM.2.1
  obtain ⟨hTR, hT2⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  set H := ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker with hHdef
  set Γ := (bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range with hΓdef
  have hemb := (glTens F E k).toHomeomorph.isClosedEmbedding
  haveI : LocallyCompactSpace (GL (Fin k) (AF F ⊗[F] E)) := hemb.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin k) (AF F ⊗[F] E)) := hemb.isEmbedding.secondCountableTopology
  haveI : T2Space (GL (Fin k) (AF F ⊗[F] E)) := hemb.isEmbedding.t2Space
  have hcont : Continuous fun g : GL (Fin k) (AF F ⊗[F] E) => absE F E (Matrix.GeneralLinearGroup.det g) :=
    GlobalTheory.Doubling.continuous_absE.comp Matrix.GeneralLinearGroup.continuous_det
  have hcl : IsClosed (H : Set (GL (Fin k) (AF F ⊗[F] E))) := isClosed_eq hcont continuous_const
  haveI : LocallyCompactSpace H := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hΓH : Γ ≤ H := by
    rintro _ ⟨γ, rfl⟩
    change absE F E (Matrix.GeneralLinearGroup.det _) = 1
    rw [det_bc]
    exact GlobalTheory.Doubling.absE_inclR _
  have hΓΛ : Γ ≤ latR F E k := le_sup_left
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · exact DiscreteTopology.of_continuous_injective
      (f := fun x : Γ.subgroupOf H => (⟨x.1.1, hΓΛ x.2⟩ : latR F E k))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun x y h => by
        apply Subtype.ext; apply Subtype.ext
        exact congrArg (fun z : latR F E k => (z : GL (Fin k) (AF F ⊗[F] E))) h)
  · intro _ _ π DM hπ hDM
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · haveI : Subsingleton H := inferInstance
      haveI : CompactSpace H := inferInstance
      exact ((measure_mono (Set.subset_univ DM)).trans_lt (isCompact_univ.measure_lt_top)).ne
    obtain ⟨a, ha, hs⟩ := GlobalTheory.T.log_tensorIdeleAbs_det_expScalarCentre_eq_mul F E k hk
    let s : GL (Fin k) (AF F ⊗[F] E) → ℝ := fun g => Real.log (absE F E (Matrix.GeneralLinearGroup.det g) : ℝ) / a
    refine GlobalTheory.T.finiteCovolume_kernel_of_split_central_oneParam _ H Γ (latR F E k) s (cR F E k) ?_ ?_ (continuous_cR k) (cR_add k) (cR_comm k) ?_ ?_ hΓH rfl
      inferInstance (fun ν D hν hD => GlobalTheory.T.finite_covolume_GL_adelicTensor_rationalTimesExpInt F E k ν D hν hD) π DM hπ hDM
    · exact ((NNReal.continuous_coe.comp hcont).log fun g => (absE_pos _).ne').div_const _
    · intro g h
      simp only [s, map_mul, NNReal.coe_mul]
      rw [Real.log_mul (absE_pos _).ne' (absE_pos _).ne', add_div]
    · intro t
      simp only [s, hs t]
      field_simp
    · intro g
      simp only [s, div_eq_zero_iff, ha, or_false, hHdef, MonoidHom.mem_ker, MonoidHom.comp_apply]
      rw [Real.log_eq_zero]
      have := absE_pos (Matrix.GeneralLinearGroup.det g)
      constructor
      · intro h; right; left; rw [h]; rfl
      · rintro (h | h | h)
        · linarith
        · exact_mod_cast h
        · linarith

end GlobalTheory.GLOneVol
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneAdelicGLLocallyCompactDiscreteFiniteCovolStatement

section

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

theorem _root_.GlobalTheory.T.normOneAdelicGL_locallyCompact_discrete_finiteCovolume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (k : ℕ), LocallyCompactSpace ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ∧ SecondCountableTopology ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ∧ DiscreteTopology ((bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range.subgroupOf ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) ∧ ∀ [MeasurableSpace (GL (Fin k) (AF F ⊗[F] E))] [BorelSpace (GL (Fin k) (AF F ⊗[F] E))] (π : Measure ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) (DM : Set ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker), π.IsHaarMeasure → IsFundamentalDomain ((bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range.subgroupOf ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) DM π → π DM ≠ ⊤ := by
  first | exact @GlobalTheory.GLOneVol.glOne_finvol | exact GlobalTheory.GLOneVol.glOne_finvol | (intros; apply GlobalTheory.GLOneVol.glOne_finvol <;> assumption)
end
end
