module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselFlagStabilizerAnisotropicBlockExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicGroupNormalizesFlagUnipotent
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSplitRealFiniteStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapConjSmallerUnitaryFlagUnipotentHaar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemiMeasFiniteOnCompactsAndOpenPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SemiMeasIsMulLeftInvariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicGroupNormalizesFlagUnipotent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicProjectionUnitaryInvEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiGroupSplitRealFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceCmHostAdeles
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupHaarIsMulRightInvariant

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesUnimod

theorem besGrp_isMulRightInvariant : ∀ (D : D7) (V V₀ A L : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L)
    (μ : Measure (besGrp d o)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  intro D V V₀ A L ρ d o μ hμ
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4, j5, j6, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨ν, 𝓝, hν⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D V ρ d.e (isIsoSub_e d)
  obtain ⟨hνH, h𝓝, h𝓝1⟩ := hν
  have hNc : IsClosed (flagN d : Set (GA D V)) := GlobalTheory.Mem.TrueRecord.isClosed_NFlag V (isIsoSub_e d)
  let μA : Measure (GA D A) := Measure.haar
  have hHaar := ((GlobalTheory.MixPer.jacGrp_besGrp_haar D V V₀ A L ρ d o ν 𝓝 ⟨hνH, h𝓝, h𝓝1⟩).2.2 μA inferInstance)
  haveI : LocallyCompactSpace (flagN d) := hNc.locallyCompactSpace
  haveI : SecondCountableTopology (flagN d) := TopologicalSpace.Subtype.secondCountableTopology _
  have hinj : Function.Injective fun γ : NFlagQ V d.e => (⟨γ.1.1, γ.2⟩ : GQ V) :=
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ V => (x : GA D V)) h))
  haveI : Countable (NFlagQ V d.e) := hinj.countable
  haveI : ν.IsMulRightInvariant :=
    GlobalTheory.SemiHaar.rightInv_of_fd (NFlagQ V d.e) ν h𝓝 (by rw [h𝓝1]; exact ENNReal.one_ne_top)
  haveI : μA.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D A μA inferInstance
  have hcA : Continuous (embA d o) := by
    have h1 : Continuous (fun h : GA D A => o.emb (h, 1)) := by
      have := o.continuous_emb
      fun_prop
    exact d.continuous_embed.comp h1
  have hnA : ∀ n ∈ flagN d, ∀ h, embA d o h * n * (embA d o h)⁻¹ ∈ flagN d := fun n hn h =>
    GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D V V₀ ρ d n hn (o.emb (h, 1))
  have hR := GlobalTheory.SemiHaar.semiMeas_rightInv (flagN d) (embA d o) hNc hcA hnA μA ν
  haveI : LocallyCompactSpace (besGrp d o) := by
    obtain ⟨e, -⟩ := GlobalTheory.SemiHaar.exists_homeo (flagN d) (embA d o) hnA hcA (GlobalTheory.BesProj.exists_continuous_proj D V V₀ A L ρ d o)
    exact e.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (besGrp d o) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨κ, k1, k2⟩ : ∃ κ : Measure (besGrp d o), κ.IsHaarMeasure ∧ κ.IsMulRightInvariant := ⟨_, hHaar, hR⟩
  rw [Measure.isMulLeftInvariant_eq_smul μ κ]
  infer_instance

end GlobalTheory.BesUnimod
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupHaarIsMulRightInvariantStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselGroup_haar_isMulRightInvariant : ∀ (D : D7) (V V₀ A L : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L) (μ : Measure (besGrp d o)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.BesUnimod.besGrp_isMulRightInvariant | exact GlobalTheory.BesUnimod.besGrp_isMulRightInvariant | (intros; apply GlobalTheory.BesUnimod.besGrp_isMulRightInvariant <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiGroupHaarIsMulRightInvariant

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.JacUnimod

theorem jacGrp_rightInv : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (μ : Measure (jacGrp d)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  intro D V V₀ ρ d μ hμ
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4, j5, -, j7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V₀
  have hNc : IsClosed (flagN d : Set (GA D V)) := GlobalTheory.Mem.TrueRecord.isClosed_NFlag V (isIsoSub_e d)
  obtain ⟨hlc, hsc, hbor, hcount⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  obtain ⟨ν, 𝓝, hνH, h𝓝, h𝓝1⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D V ρ d.e (isIsoSub_e d)
  have hnorm := GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D V V₀ ρ d
  have hp := GlobalTheory.JacProj.exists_continuous_proj D V V₀ ρ d
  have hc := GlobalTheory.FlagModulus.map_conj_smallerUnitary_flagUnipotent_haar D V V₀ ρ d ν hνH
  let μ₀ : Measure (GA D V₀) := Measure.haar
  have hμ₀ : μ₀.IsHaarMeasure := inferInstance
  haveI := hνH
  haveI : μ₀.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V₀ μ₀ hμ₀
  haveI : ν.IsMulRightInvariant := GlobalTheory.SemiHaar.rightInv_of_fd _ ν h𝓝 (by rw [h𝓝1]; exact ENNReal.one_ne_top)
  have a := GlobalTheory.MixPer.semiMeas_isMulLeftInvariant (flagN d) d.emb0 hNc d.continuous_embed hnorm hp μ₀ ν hμ₀ hνH hc
  obtain ⟨b, c⟩ := GlobalTheory.MixPer.semiMeas_finite_on_compacts_and_open_pos (flagN d) d.emb0 hNc d.continuous_embed hnorm hp
    μ₀ ν hμ₀ hνH hc
  have hH : (semiMeas (flagN d) d.emb0 μ₀ ν).IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := b, toIsMulLeftInvariant := a, toIsOpenPosMeasure := c }
  have hR := GlobalTheory.SemiHaar.semiMeas_rightInv (flagN d) d.emb0 hNc d.continuous_embed hnorm μ₀ ν
  obtain ⟨e, -⟩ := GlobalTheory.SemiHaar.exists_homeo (flagN d) d.emb0 hnorm d.continuous_embed hp
  haveI : LocallyCompactSpace (jacGrp d) := e.symm.isClosedEmbedding.locallyCompactSpace
  let κ : Measure (jacGrp d) := semiMeas (flagN d) d.emb0 μ₀ ν
  haveI hκH : κ.IsHaarMeasure := hH
  haveI hκR : κ.IsMulRightInvariant := hR
  have hk := Measure.isMulLeftInvariant_eq_smul μ κ
  rw [hk]
  infer_instance

end GlobalTheory.JacUnimod

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiGroupHaarIsMulRightInvariantStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fourierJacobiGroup_haar_isMulRightInvariant : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (μ : Measure (jacGrp d)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.JacUnimod.jacGrp_rightInv | exact GlobalTheory.JacUnimod.jacGrp_rightInv | (intros; apply GlobalTheory.JacUnimod.jacGrp_rightInv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicSplit

open scoped NNReal ENNReal

section General

variable {A B : Type} [Group A] [Group B] [TopologicalSpace A] [TopologicalSpace B]
  [IsTopologicalGroup A] [IsTopologicalGroup B] [LocallyCompactSpace A] [LocallyCompactSpace B]
  [SecondCountableTopology A] [SecondCountableTopology B] [T2Space A] [T2Space B]
  [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B]

theorem rightInv_of_prod (h : ∀ μ : Measure (A × B), μ.IsHaarMeasure → μ.IsMulRightInvariant)
    (ν : Measure B) (hν : ν.IsHaarMeasure) : ν.IsMulRightInvariant := by
  refine ⟨fun b => ?_⟩
  let μA : Measure A := Measure.haar
  haveI := h (μA.prod ν) inferInstance
  set c := Measure.haarScalarFactor (ν.map (· * b)) ν
  have hc : ν.map (· * b) = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  have h1 : (μA.prod ν).map (· * ((1 : A), b)) = μA.prod (ν.map (· * b)) := by
    have e : (fun x : A × B => x * ((1 : A), b)) = Prod.map id (· * b) := by
      funext x
      simp [Prod.ext_iff]
    rw [e, ← Measure.map_prod_map _ _ measurable_id (measurable_mul_const b), Measure.map_id]
  have h3 : μA.prod ν = (c : ℝ≥0∞) • μA.prod ν := by
    rw [← Measure.prod_smul_right, ← ENNReal.smul_def, ← hc, ← h1, map_mul_right_eq_self]
  obtain K : TopologicalSpace.PositiveCompacts (A × B) := Classical.arbitrary _
  have hpos : 0 < μA.prod ν K := Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty
  have hfin : μA.prod ν K < ⊤ := K.isCompact.measure_lt_top
  have h4 := congrArg (fun m : Measure (A × B) => m K) h3
  simp only [Measure.smul_apply, smul_eq_mul] at h4
  have h5 : (c : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hpos.ne' hfin.ne).1 (h4.symm.trans (one_mul _).symm)
  rw [hc, ENNReal.smul_def, h5, one_smul]

end General

section Restr

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def restrEquiv (P Q R : Subgroup G) (e : P × Q ≃ₜ* G) (he : ∀ p, e p = p.1.1 * p.2.1)
    (hs : ∀ a ∈ P, ∀ b ∈ Q, a * b ∈ R → a ∈ R ∧ b ∈ R) :
    R.subgroupOf P × R.subgroupOf Q ≃ₜ* R where
  toFun x := ⟨e (x.1.1, x.2.1), by
    rw [he]; exact R.mul_mem (Subgroup.mem_subgroupOf.1 x.1.2) (Subgroup.mem_subgroupOf.1 x.2.2)⟩
  invFun r :=
    have hr : ((e.symm r.1).1 : G) * (e.symm r.1).2 ∈ R := by rw [← he, e.apply_symm_apply]; exact r.2
    (⟨(e.symm r.1).1, Subgroup.mem_subgroupOf.2 (hs _ (e.symm r.1).1.2 _ (e.symm r.1).2.2 hr).1⟩,
     ⟨(e.symm r.1).2, Subgroup.mem_subgroupOf.2 (hs _ (e.symm r.1).1.2 _ (e.symm r.1).2.2 hr).2⟩)
  left_inv x := by
    have h : e.symm (e (x.1.1, x.2.1)) = (x.1.1, x.2.1) := e.symm_apply_apply _
    ext
    · exact congrArg (fun p => (p.1 : G)) h
    · exact congrArg (fun p => (p.2 : G)) h
  right_inv r := Subtype.ext (e.apply_symm_apply r.1)
  map_mul' x y := Subtype.ext (by
    change e ((x * y).1.1, (x * y).2.1) = e (x.1.1, x.2.1) * e (y.1.1, y.2.1)
    rw [← map_mul]; rfl)
  continuous_toFun := by
    refine Continuous.subtype_mk (e.continuous.comp ?_) _
    exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have h0 : Continuous fun r : R => e.symm r.1 := e.symm.continuous.comp continuous_subtype_val
    exact (Continuous.subtype_mk (continuous_fst.comp h0) _).prodMk (Continuous.subtype_mk (continuous_snd.comp h0) _)

variable [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem rightInv_restr (P Q R : Subgroup G) (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
    (hR : IsClosed (R : Set G)) (e : P × Q ≃ₜ* G) (he : ∀ p, e p = p.1.1 * p.2.1)
    (hs : ∀ a ∈ P, ∀ b ∈ Q, a * b ∈ R → a ∈ R ∧ b ∈ R)
    (hu : ∀ μ : Measure R, μ.IsHaarMeasure → μ.IsMulRightInvariant) :
    ∀ ν : Measure (R.subgroupOf Q), ν.IsHaarMeasure → ν.IsMulRightInvariant := by
  haveI : LocallyCompactSpace P := hP.locallyCompactSpace
  haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  haveI : LocallyCompactSpace R := hR.locallyCompactSpace
  have hRP : IsClosed ((R.subgroupOf P : Subgroup P) : Set P) := hR.preimage continuous_subtype_val
  have hRQ : IsClosed ((R.subgroupOf Q : Subgroup Q) : Set Q) := hR.preimage continuous_subtype_val
  haveI : LocallyCompactSpace (R.subgroupOf P) := hRP.locallyCompactSpace
  haveI : LocallyCompactSpace (R.subgroupOf Q) := hRQ.locallyCompactSpace
  intro ν hν
  refine rightInv_of_prod (A := R.subgroupOf P) (fun μ hμ => ?_) ν hν
  haveI := hμ
  exact GlobalTheory.UpqUnimodular.isMulRightInvariant_of_continuousMulEquiv (restrEquiv P Q R e he hs) μ
    (hu _ (ContinuousMulEquiv.isHaarMeasure_map μ (restrEquiv P Q R e he hs)))

end Restr

section Adelic

open GlobalTheory.AdelicU

variable {D : D7}

theorem ofInf_projInf_of_mem (V : HSp D) {a : GA D V} (ha : a ∈ GinfC V) :
    ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram a) = a := by
  have h := ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram a
  rwa [mem_infPts.1 ha, map_one, mul_one] at h

theorem ofFin_projFin_of_mem (V : HSp D) {b : GA D V} (hb : b ∈ GfC V) :
    ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram b) = b := by
  have h := ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram b
  rwa [mem_finPts.1 hb, map_one, one_mul] at h

theorem commute_GinfC_GfC (V : HSp D) {a b : GA D V} (ha : a ∈ GinfC V) (hb : b ∈ GfC V) : a * b = b * a := by
  rw [← ofInf_projInf_of_mem V ha, ← ofFin_projFin_of_mem V hb]
  exact commute_ofInf_ofFin _ _ _ _

def splitEquiv (V : HSp D) : GinfC V × GfC V ≃ₜ* GA D V where
  toFun p := p.1.1 * p.2.1
  invFun g := (⟨ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g), mem_infPts.2 (by simp)⟩,
    ⟨ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g), mem_finPts.2 (by simp)⟩)
  left_inv p := by
    have h1 : projInf D.sp.cm.sig V.gram p.2.1 = 1 := mem_finPts.1 p.2.2
    have h2 : projFin D.sp.cm.sig V.gram p.1.1 = 1 := mem_infPts.1 p.1.2
    ext
    · change ofInf _ _ (projInf _ _ (p.1.1 * p.2.1)) = p.1.1
      rw [map_mul, h1, mul_one, ofInf_projInf_of_mem V p.1.2]
    · change ofFin _ _ (projFin _ _ (p.1.1 * p.2.1)) = p.2.1
      rw [map_mul, h2, one_mul, ofFin_projFin_of_mem V p.2.2]
  right_inv g := ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram g
  map_mul' p q := by
    change p.1.1 * q.1.1 * (p.2.1 * q.2.1) = p.1.1 * p.2.1 * (q.1.1 * q.2.1)
    rw [mul_assoc, ← mul_assoc q.1.1, commute_GinfC_GfC V q.1.2 p.2.2, mul_assoc, mul_assoc]
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun :=
    (((continuous_ofInf _ _).comp (continuous_projInf _ _)).subtype_mk _).prodMk
      (((continuous_ofFin _ _).comp (continuous_projFin _ _)).subtype_mk _)

theorem splitEquiv_apply (V : HSp D) (p : GinfC V × GfC V) : splitEquiv V p = p.1.1 * p.2.1 := rfl

theorem isClosed_GinfC' (V : HSp D) : IsClosed (GinfC V : Set (GA D V)) := isClosed_infPts _ _
theorem isClosed_GfC' (V : HSp D) : IsClosed (GfC V : Set (GA D V)) := isClosed_finPts _ _

end Adelic

theorem adelic_split : ∀ (D : D7) (V : HSp D), IsClosed (GinfC V : Set (GA D V)) ∧ IsClosed (GfC V : Set (GA D V)) ∧ (∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b = b * a) ∧ (∃ e : (GinfC V × GfC V) ≃ₜ GA D V, ∀ p, e p = p.1 * p.2) ∧ (∀ μ : Measure (GfC V), μ.IsHaarMeasure → μ.IsMulRightInvariant) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), ((∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ jacGrp d → a ∈ jacGrp d ∧ b ∈ jacGrp d) ∧ (∀ μ : Measure (jacGrp d), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ μ : Measure ((jacGrp d).subgroupOf (GfC V)), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), (∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ besGrp d o → a ∈ besGrp d o ∧ b ∈ besGrp d o) ∧ (∀ μ : Measure (besGrp d o), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ μ : Measure ((besGrp d o).subgroupOf (GfC V)), μ.IsHaarMeasure → μ.IsInvInvariant := by
  intro D V
  have hi := isClosed_GinfC' V
  have hf := isClosed_GfC' V
  haveI : LocallyCompactSpace (GinfC V) := hi.locallyCompactSpace
  haveI : LocallyCompactSpace (GfC V) := hf.locallyCompactSpace
  refine ⟨hi, hf, fun a ha b hb => commute_GinfC_GfC V ha hb, ⟨(splitEquiv V).toHomeomorph, fun p => rfl⟩,
    fun μ hμ => rightInv_of_prod (A := GinfC V) (fun m hm => ?_) μ hμ, fun V₀ ρ d => ?_⟩
  · haveI := hm
    exact GlobalTheory.UpqUnimodular.isMulRightInvariant_of_continuousMulEquiv (splitEquiv V) m
      (GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V _ inferInstance)
  have hJ := GlobalTheory.jacGrp_isClosed D V V₀ ρ d
  haveI : LocallyCompactSpace (jacGrp d) := hJ.locallyCompactSpace
  refine ⟨⟨GlobalTheory.T.fourierJacobiGroup_split_real_finite D V V₀ ρ d, fun μ hμ => ?_, fun μ hμ => ?_⟩, fun A L o => ?_⟩
  · haveI := hμ
    haveI := GlobalTheory.T.fourierJacobiGroup_haar_isMulRightInvariant D V V₀ ρ d μ hμ
    exact GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  · have hc : IsClosed (((jacGrp d).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) :=
      hJ.preimage continuous_subtype_val
    haveI : LocallyCompactSpace ((jacGrp d).subgroupOf (GfC V)) := hc.locallyCompactSpace
    haveI := hμ
    haveI := rightInv_restr (GinfC V) (GfC V) (jacGrp d) hi hf hJ (splitEquiv V) (splitEquiv_apply V)
      (GlobalTheory.T.fourierJacobiGroup_split_real_finite D V V₀ ρ d) (GlobalTheory.T.fourierJacobiGroup_haar_isMulRightInvariant D V V₀ ρ d) μ hμ
    exact GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  have hB := GlobalTheory.BesClosed.besGrp_isClosed D V V₀ A L ρ d o
  haveI : LocallyCompactSpace (besGrp d o) := hB.locallyCompactSpace
  refine ⟨GlobalTheory.T.besselGroup_split_real_finite D V V₀ A L ρ d o, fun μ hμ => ?_, fun μ hμ => ?_⟩
  · haveI := hμ
    haveI := GlobalTheory.T.besselGroup_haar_isMulRightInvariant D V V₀ A L ρ d o μ hμ
    exact GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  · have hc : IsClosed (((besGrp d o).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) :=
      hB.preimage continuous_subtype_val
    haveI : LocallyCompactSpace ((besGrp d o).subgroupOf (GfC V)) := hc.locallyCompactSpace
    haveI := hμ
    haveI := rightInv_restr (GinfC V) (GfC V) (besGrp d o) hi hf hB (splitEquiv V) (splitEquiv_apply V)
      (GlobalTheory.T.besselGroup_split_real_finite D V V₀ A L ρ d o) (GlobalTheory.T.besselGroup_haar_isMulRightInvariant D V V₀ A L ρ d o) μ hμ
    exact GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ

end GlobalTheory.AdelicSplit
end
end
end
