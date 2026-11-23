module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseNormalFormRealFramesAtRealPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeReferenceLatticeStabiliserBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameSelfNormalFormExistsProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOnStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentEqLebesgueStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitiveStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOn
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianStabiliserCovolumeLe
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GoodLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KappaOffDiagonal
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.SharpRestriction.CuspSpanNormBounds.JExistsNatSmulMemL
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealIntegralUnipotentBesselModelsCountableSubgroStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointsBaseLatticeStabilizerFixedFrameUnipote
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalSetUnipotentOnBesselModelsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProofStatement
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMapStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.lebesgueCommonStabilizer_eq_radical_levi_map : ∀ (k r j : ℕ) (β : Fin r → ℕ), Monotone β → (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) → lebR0 k r j β = (volume : Measure ((UTin β → ℂ) × PTop k r j)).map (fun q => Matrix.of.symm (pTop k r j q.2 * uEmb k r (upperIn β q.1))) ∧ Set.range (rEl k r j β) = Set.range (fun q : (UTin β → ℂ) × PTop k r j => pTop k r j q.2 * uEmb k r (upperIn β q.1)) ∧ Function.Injective (fun q : (UTin β → ℂ) × PTop k r j => pTop k r j q.2 * uEmb k r (upperIn β q.1)) ∧ (j = 0 → lebR0 k r j β = lebN k r) := by
  first | exact @GlobalTheory.DegVol.Swap.range_eq_and_injective_parabolic_unipotent_product | exact GlobalTheory.DegVol.Swap.range_eq_and_injective_parabolic_unipotent_product | (intros; apply GlobalTheory.DegVol.Swap.range_eq_and_injective_parabolic_unipotent_product <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureEqOfStrictFundamentalSetsPlacewise

section

@[expose] public section

open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FundEq

open GlobalTheory.DegVol

theorem measurable_mulP {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) :
    Measurable (fun x : ι → Formalism.QuantumDeterminants.Mt k r => mulP m x) :=
  Measurable.of_eval fun v => (GlobalTheory.DegVol.Cov.continuous_lmulM _).measurable.comp (measurable_pi_apply v)

theorem measure_eq_tsum {ι : Type} {k r : ℕ} (μ : Measure (ι → Formalism.QuantumDeterminants.Mt k r))
    (R Γ Ω S : Set (ι → Formalism.QuantumDeterminants.Mt k r)) [Countable Γ] (hR : μ Rᶜ = 0)
    (hΩ : MeasurableSet Ω) (hS : MeasurableSet S) (h : ∀ x ∈ R, ∃! m, m ∈ Γ ∧ mulP m x ∈ Ω) :
    μ S = ∑' a : Γ, μ ((fun x => mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x) ⁻¹' Ω ∩ S) := by
  rw [← measure_iUnion₀]
  · apply measure_congr
    have : ∀ᵐ x ∂μ, x ∈ R := hR
    filter_upwards [this] with x hx
    obtain ⟨s, hs, -⟩ := h x hx
    constructor
    · intro hxS
      exact Set.mem_iUnion.2 ⟨⟨s, hs.1⟩, hs.2, hxS⟩
    · intro hxS
      obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hxS
      exact ha.2
  · intro a b hab
    refine measure_mono_null ?_ hR
    rintro x ⟨ha, hb⟩ hx
    exact hab (Subtype.ext ((h x hx).unique ⟨a.2, ha.1⟩ ⟨b.2, hb.1⟩))
  · intro a
    exact ((measurable_mulP _ hΩ).inter hS).nullMeasurableSet

def invP {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) : ι → Formalism.QuantumDeterminants.Mt k r :=
  fun v => Matrix.of.symm (Matrix.of (m v))⁻¹

theorem mulP_invP_mulP {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) (hm : ∀ v, IsUnit (Matrix.of (m v)).det)
    (x : ι → Formalism.QuantumDeterminants.Mt k r) : mulP (invP m) (mulP m x) = x := by
  funext v
  show (Matrix.of (m v))⁻¹ * (Matrix.of (m v) * Matrix.of (x v)) = x v
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hm v), Matrix.one_mul]
  rfl

theorem pointwiseInv_pointwiseInv {ι : Type} {k r : ℕ} (m : ι → Formalism.QuantumDeterminants.Mt k r) (hm : ∀ v, IsUnit (Matrix.of (m v)).det) :
    invP (invP m) = m := by
  funext v
  show ((Matrix.of (m v))⁻¹)⁻¹ = m v
  rw [Matrix.nonsing_inv_nonsing_inv _ (hm v)]
  rfl

theorem measure_le {ι : Type} [Fintype ι] {k r : ℕ} (μ : Measure (ι → Formalism.QuantumDeterminants.Mt k r))
    (R Γ Ω₁ Ω₂ : Set (ι → Formalism.QuantumDeterminants.Mt k r)) (hΓ : Γ.Countable) (hR : μ Rᶜ = 0)
    (hinv : ∀ m ∈ Γ, invP m ∈ Γ) (hu : ∀ m ∈ Γ, ∀ v, IsUnit (Matrix.of (m v)).det)
    (hpres : ∀ m ∈ Γ, μ.map (fun x => mulP m x) = μ)
    (h₁ : IsFund Γ R Ω₁) (h₂ : IsFund Γ R Ω₂) : μ Ω₁ ≤ μ Ω₂ := by
  haveI : Countable Γ := hΓ.to_subtype
  have e1 := measure_eq_tsum μ R Γ Ω₂ Ω₁ hR h₂.1 h₁.1 h₂.2
  have e2 := measure_eq_tsum μ R Γ Ω₁ Ω₂ hR h₁.1 h₂.1 h₁.2
  have hterm : ∀ a : Γ, μ ((fun x => mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x) ⁻¹' Ω₂ ∩ Ω₁) =
      μ ((fun x => mulP (invP (a : ι → Formalism.QuantumDeterminants.Mt k r)) x) ⁻¹' Ω₁ ∩ Ω₂) := by
    intro a
    have hs : MeasurableSet ((fun x => mulP (invP (a : ι → Formalism.QuantumDeterminants.Mt k r)) x) ⁻¹' Ω₁ ∩ Ω₂) :=
      (measurable_mulP _ h₁.1).inter h₂.1
    conv_rhs => rw [← hpres a a.2, Measure.map_apply (measurable_mulP _) hs]
    congr 1
    ext x
    show (mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x ∈ Ω₂ ∧ x ∈ Ω₁) ↔
      (mulP (invP (a : ι → Formalism.QuantumDeterminants.Mt k r)) (mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x) ∈ Ω₁ ∧ mulP (a : ι → Formalism.QuantumDeterminants.Mt k r) x ∈ Ω₂)
    rw [mulP_invP_mulP _ (hu a a.2)]
    exact And.comm
  let f : Γ → Γ := fun a => ⟨invP a, hinv a a.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h' : invP (a : ι → Formalism.QuantumDeterminants.Mt k r) = invP b := congrArg Subtype.val hab
    apply Subtype.ext
    rw [← pointwiseInv_pointwiseInv _ (hu a a.2), ← pointwiseInv_pointwiseInv _ (hu b b.2), h']
  rw [e1, e2, tsum_congr hterm]
  exact ENNReal.tsum_comp_le_tsum_of_injective hf
    (fun b : Γ => μ ((fun x => mulP (b : ι → Formalism.QuantumDeterminants.Mt k r) x) ⁻¹' Ω₁ ∩ Ω₂))

theorem measure_eq : ∀ (ι : Type) [Fintype ι] (k r : ℕ) (Γ Ω₁ Ω₂ : Set (ι → Formalism.QuantumDeterminants.Mt k r)),
    Γ.Countable → (fun _ => Matrix.of.symm 1) ∈ Γ → (∀ m ∈ Γ, ∀ m' ∈ Γ, GlobalTheory.DegVol.mulP m m' ∈ Γ) →
    (∀ m ∈ Γ, (fun v => Matrix.of.symm (Matrix.of (m v))⁻¹) ∈ Γ) →
    (∀ m ∈ Γ, ∀ v, Matrix.of (m v) ∈ Formalism.QuantumDeterminants.Nset k r) →
    GlobalTheory.DegVol.IsFund Γ (GlobalTheory.DegVol.RP k r (fun _ => 1)) Ω₁ → GlobalTheory.DegVol.IsFund Γ (GlobalTheory.DegVol.RP k r (fun _ => 1)) Ω₂ →
    Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) Ω₁ = Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) Ω₂ := by
  intro ι _ k r Γ Ω₁ Ω₂ hΓ _ _ hinv hN h₁ h₂
  have hH := GlobalTheory.Amp.NHaar.isHaarOn_lebN k r
  haveI : SigmaFinite (GlobalTheory.Amp.lebN k r) := hH.1
  have hu : ∀ m ∈ Γ, ∀ v, IsUnit (Matrix.of (m v)).det := fun m hm v =>
    GlobalTheory.DegVol.RealMat.isUnit_det (hN m hm v).1
  have hnull : Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) (GlobalTheory.DegVol.RP k r (fun _ => 1))ᶜ = 0 := by
    refine measure_mono_null (t := ⋃ v : ι, Function.eval v ⁻¹' {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) ?_
      (measure_iUnion_null fun v => Measure.pi_eval_preimage_null _ hH.2.2.1)
    intro x hx
    simp only [RP, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨v, hv'⟩ := hx
    refine Set.mem_iUnion.2 ⟨v, ?_⟩
    intro hxN
    apply hv'
    refine ⟨hxN, ?_⟩
    simpa using hxN
  have hpres : ∀ m ∈ Γ, (Measure.pi fun _ : ι => GlobalTheory.Amp.lebN k r).map (fun x => mulP m x) =
      Measure.pi fun _ : ι => GlobalTheory.Amp.lebN k r := fun m hm => by
    have e : ∀ v, (GlobalTheory.Amp.lebN k r).map (Formalism.QuantumDeterminants.lmulM (Matrix.of (m v))) = GlobalTheory.Amp.lebN k r :=
      fun v => hH.2.2.2 _ (hN m hm v)
    haveI : ∀ v, SigmaFinite ((GlobalTheory.Amp.lebN k r).map (Formalism.QuantumDeterminants.lmulM (Matrix.of (m v)))) := fun v => by
      rw [e]; infer_instance
    have := Measure.pi_map_pi (μ := fun _ : ι => GlobalTheory.Amp.lebN k r)
      (f := fun v => Formalism.QuantumDeterminants.lmulM (Matrix.of (m v))) fun v => (GlobalTheory.DegVol.Cov.continuous_lmulM _).measurable.aemeasurable
    simp only [e] at this
    exact this
  exact le_antisymm
    (measure_le _ _ Γ Ω₁ Ω₂ hΓ hnull hinv hu hpres h₁ h₂)
    (measure_le _ _ Γ Ω₂ Ω₁ hΓ hnull hinv hu hpres h₂ h₁)

end GlobalTheory.FundEq
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureEqOfStrictFundamentalSetsPlacewiseStatement

section

@[expose] public section

open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.measure_eq_of_strictFundamentalSetsPlacewise : ∀ (ι : Type) [Fintype ι] (k r : ℕ) (Γ Ω₁ Ω₂ : Set (ι → Formalism.QuantumDeterminants.Mt k r)),
    Γ.Countable → (fun _ => Matrix.of.symm 1) ∈ Γ → (∀ m ∈ Γ, ∀ m' ∈ Γ, GlobalTheory.DegVol.mulP m m' ∈ Γ) →
    (∀ m ∈ Γ, (fun v => Matrix.of.symm (Matrix.of (m v))⁻¹) ∈ Γ) →
    (∀ m ∈ Γ, ∀ v, Matrix.of (m v) ∈ Formalism.QuantumDeterminants.Nset k r) →
    GlobalTheory.DegVol.IsFund Γ (GlobalTheory.DegVol.RP k r (fun _ => 1)) Ω₁ → GlobalTheory.DegVol.IsFund Γ (GlobalTheory.DegVol.RP k r (fun _ => 1)) Ω₂ →
    Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) Ω₁ = Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) Ω₂ := by
  first | exact @GlobalTheory.FundEq.measure_eq | exact GlobalTheory.FundEq.measure_eq | (intros; apply GlobalTheory.FundEq.measure_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointsBaseLatticeStabilizerFixedFrameUnipoteStatement

section

@[expose] public section

open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.real_points_base_lattice_stabilizer_fixed_frame_unipotent : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1), Std D large₂ →
    ∀ N : GlobalTheory.DegCnt.NF (HV D) D.R.rS, N.F = F0 X u → N.F' = F0 X u →
      GlobalTheory.DegVol.realPts (fun τ => phiV C τ) (N.Gam (VS D).L0 : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) =
        trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u := by
  first | exact @GlobalTheory.TypeAsm.realPts_Gam_eq_trI_image_NOinf | exact GlobalTheory.TypeAsm.realPts_Gam_eq_trI_image_NOinf | (intros; apply GlobalTheory.TypeAsm.realPts_Gam_eq_trI_image_NOinf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCovolumeFiniteBounded

section

@[expose] public section

noncomputable section
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals

namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem covN_haarLie_smul {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (κ : ℝ≥0∞) :
    haarLie S κ = κ • haarLie S 1 := by
  unfold haarLie; rw [one_smul]

theorem covN_muNB_one (D : D7) : muNB D 1 =
    (kapN D 1 * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • GlobalTheory.Amp.lebN D.R.k D.R.rS := by
  rw [muNB, covN_haarLie_smul, GlobalTheory.T.haar_lie_nilpotent_eq_lebesgue, smul_smul]

theorem covN_pi_smul {ι : Type} [Fintype ι] {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (c : ℝ≥0) : Measure.pi (fun _ : ι => (c : ℝ≥0∞) • μ) = ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi (fun _ : ι => μ) := by
  haveI : SigmaFinite ((c : ℝ≥0∞) • μ) := by
    first
    | (have h : ((c : ℝ≥0∞) • μ) = c • μ := (ENNReal.smul_def c μ).symm
       rw [h]; infer_instance)
    | (rw [← ENNReal.smul_def]; infer_instance)
  refine (Measure.pi_eq fun s hs => ?_)
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem covN_arith (v : ℝ) (hv : 1 ≤ v) (r k f : ℕ) :
    1 ≤ ((2 * v) ^ (-((r : ℝ) * k)) * 1 * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f * v ^ (k * r * f) := by
  have hv0 : 0 < v := by linarith
  have h2v : 0 < 2 * v := by linarith
  have hA : (2 * v) ^ (-((r : ℝ) * k)) * v ^ (k * r) = ((2 : ℝ) ^ (r * k))⁻¹ := by
    rw [Real.rpow_neg h2v.le, show ((r : ℝ) * k) = ((r * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, mul_pow,
      show k * r = r * k from Nat.mul_comm k r]
    have : (0 : ℝ) < v ^ (r * k) := pow_pos hv0 _
    field_simp
  have hB : ((2 * v) ^ (-((r : ℝ) * k)) * 1 * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f * v ^ (k * r * f) =
      (((2 : ℝ) ^ (r * k))⁻¹ * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f := by
    rw [← hA, pow_mul, ← mul_pow]
    ring
  rw [hB]
  apply one_le_pow₀
  rw [← div_eq_inv_mul, one_le_div (by positivity)]
  apply pow_le_pow_right₀ (by norm_num)
  nlinarith [Nat.zero_le (r * (r - 1))]

theorem covNC_holds : CovNC := by
  intro D large₂ X Y u C hS
  obtain ⟨hCM, hPl, hv, hv1, -, hcard, -, -, -, hnorm, hfin, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  obtain ⟨N, hF, hF', hj, hT, h𝔡, hTerm, hRef, hist⟩ := GlobalTheory.T.fixedFrameSelfNormalFormExists_proof D large₂ X Y u hS (VS D).L0 (Or.inr rfl)
  obtain ⟨hU, -, hz, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive D.host.E (VS D).V (HV D) hCM D.R.rS N (gS D) (VS D).L0 (by omega) hTerm
  have hzL : N.F.z ∈ GlobalTheory.HermLat.latL N.F N.F' (VS D).L0 := by
    have h := (hz 1).2 (by simp)
    simpa using h
  have hFr := GlobalTheory.T.baseNormalForm_realFrames_at_realPlaces D large₂ X u C hS N hF hF' hj hT (hist rfl)
  have hN𝔡 : (Ideal.absNorm N.𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv D.host.E) ^ (2 * Fintype.card D.what₂.Tau) := by
    rw [h𝔡, hnorm, hv, hcard]
  have hv1' : 1 ≤ Formalism.HermitianLatticesTheory.vInv D.host.E := by rw [hv]; exact hv1
  obtain ⟨Ω, hΩ, hlo, hhi⟩ := GlobalTheory.T.covolume_referenceLattice_stabiliser_bounds D.host.E (VS D).V (HV D) hCM D.R.rS N D.R.k D.what₂.Tau (embS D)
    (fun _ => 0) (fun τ => phiV C τ) (fun τ => zB X (C.Qi τ) u τ) (fun τ => zB X (C.Qi τ) u τ) (fun _ => 1)
    hPl hfin hFr hN𝔡 hv1' _ hU hzL
  rw [hRef, GlobalTheory.T.real_points_base_lattice_stabilizer_fixed_frame_unipotent D large₂ X Y u C hS N hF hF'] at hΩ
  have hsw := (GlobalTheory.T.lebesgueCommonStabilizer_eq_radical_levi_map D.R.k D.R.rS N.j (fun _ => 0) monotone_const (by intro a b _; simp [hj])).2.2.2 hj
  rw [hsw, hj, hv, hcard, Nat.sub_zero] at hlo hhi
  obtain ⟨hc, h1, hmul, hinv, hNs⟩ := GlobalTheory.T.realIntegralUnipotent_besselModels_countable_subgroup D X Y u C
  have heq := GlobalTheory.T.measure_eq_of_strictFundamentalSetsPlacewise D.what₂.Tau D.R.k D.R.rS _ _ _ hc h1 hmul hinv hNs hΩ (GlobalTheory.T.strictFundamentalSet_unipotent_on_besselModels D X Y u C)
  haveI : SigmaFinite (GlobalTheory.Amp.lebN D.R.k D.R.rS) := (GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn D.R.k D.R.rS).1
  set c : ℝ≥0 := ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1).toNNReal *
    2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1)) with hc_def
  have hk : kapN D 1 * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1)) = (c : ℝ≥0∞) := by
    rw [hc_def, kapN, ENNReal.ofReal]
    push_cast
    rfl
  have hcov : covN C Y u = (c : ℝ≥0∞) ^ D.R.f * Measure.pi (fun _ : D.what₂.Tau => GlobalTheory.Amp.lebN D.R.k D.R.rS) Ω := by
    rw [covN, covN_muNB_one, hk, covN_pi_smul, Measure.smul_apply, smul_eq_mul, hcard, ← heq]
  have hfinΩ : Measure.pi (fun _ : D.what₂.Tau => GlobalTheory.Amp.lebN D.R.k D.R.rS) Ω ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hhi
  have hne : covN C Y u ≠ ⊤ := by
    rw [hcov]; exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hfinΩ
  refine ⟨hne, ?_⟩
  have hlo' := (ENNReal.ofReal_le_iff_le_toReal hfinΩ).1 hlo
  have hlpos : 0 < lossV D := by
    unfold lossV; exact pow_pos (by linarith) _
  have hcr : ((c : ℝ≥0∞) ^ D.R.f).toReal = ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
      2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) ^ D.R.f := by
    rw [ENNReal.toReal_pow, ENNReal.coe_toReal, hc_def, NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
    push_cast; ring
  rw [hcov, ENNReal.toReal_mul, hcr]
  have key := covN_arith D.host.v hv1 D.R.rS D.R.k D.R.f
  have hpos : 0 ≤ ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
      2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) ^ D.R.f := by positivity
  have hq : D.host.v ^ (D.R.k * D.R.rS * D.R.f) / (8 * D.host.v) ^ (2 * (D.R.rS + 1) ^ 2 * D.R.f) * lossV D =
      D.host.v ^ (D.R.k * D.R.rS * D.R.f) := by
    unfold lossV; field_simp
  calc (1 : ℝ) ≤ ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
        2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) ^ D.R.f * D.host.v ^ (D.R.k * D.R.rS * D.R.f) := key
    _ = ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
        2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) ^ D.R.f *
        (D.host.v ^ (D.R.k * D.R.rS * D.R.f) / (8 * D.host.v) ^ (2 * (D.R.rS + 1) ^ 2 * D.R.f) * lossV D) := by rw [hq]
    _ ≤ _ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hlpos.le
      exact mul_le_mul_of_nonneg_left hlo' hpos

end GlobalTheory.TypeAsm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCovolumeFiniteBoundedStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.integralUnipotent_covolume_finite_bounded : GlobalTheory.TypeAsm.CovNC := by
  first | exact @GlobalTheory.TypeAsm.covNC_holds | exact GlobalTheory.TypeAsm.covNC_holds | (intros; apply GlobalTheory.TypeAsm.covNC_holds <;> assumption)
end
end
