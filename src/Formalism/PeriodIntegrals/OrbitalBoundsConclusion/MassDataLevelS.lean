module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LevelKSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.CMInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.EvalVOpen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobLevelSOf
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.TypedNeOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelLeMaximalCompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobLevelS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatStab
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatAdapted
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Mathlib.Tactic.Linter.Style
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.PsiVMulVec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.UnipotentIntegralInLevel

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobFromParts

section

@[expose] public section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Volumes

theorem globFromParts_holds : GlobFromParts := by
  intro hLS h1 h2 h3 h4 D X hb _ _ w
  obtain ⟨hCM, hJ⟩ := h1 X
  obtain ⟨T, hT⟩ := h2 X w
  obtain ⟨ΛX, ΛW, ΛY, hA, hK⟩ := h3 X w
  obtain ⟨-, -, hHf, -, -, hNf, hSf, -⟩ := X.measW_norm w
  have key := (hLS X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hJ hJ D.R.rS (frameOf X w) T hT
    ΛX ΛW ΛY hA (X.measW w).μNf hNf (X.measW w).μHf hHf).2 (X.measW w).μSf ⟨hSf, h4 X w⟩
  simp only [KS, NO, KH, Subgroup.mem_inf, hK, SetLike.coe_mem, true_and] at key
  unfold muSf muNf muHf
  rw [← ENNReal.toReal_mul]
  exact congrArg ENNReal.toReal key

end MassDataLevelSSteps
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.InLevelSAtOf

section

@[expose] public section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem clauses_word (hA : TypedNe) (hB : GlobLevelS) (hC : RatioH) {D : D7} (X : HidaSetting D)
    (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hT : X.MeasTie hb) (hL : X.LevelSubgroupNormalized) (w : D.what₂.Word) :
    (muSf X w / ∏ p : TypX X, muSv X w p) * ∏ p : TypX X, muSv X w p = muNf X w * muHf X w ∧
    (muSf X w / ∏ p : TypX X, muSv X w p) * ∏ p : TypX X, muSvpp X hb w p = muNf X w * muHfpp X hb w := by
  have hne : ∏ p : TypX X, muSv X w p ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p _ => hA X hb hT hL w p)
  have hS := hB X hb hT hL w
  have hR := hC X hb hK hT hL w
  refine ⟨?_, ?_⟩
  · rw [div_mul_cancel₀ _ hne, hS]
  · rw [hS, div_mul_eq_mul_div, div_eq_iff hne]
    linear_combination (-muNf X w) * hR

theorem inLevelSAt_of (hA : TypedNe) (hB : GlobLevelS) (hC : RatioH) :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InLevelSAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X hb hK FdN FdN' u u' X0 L A hH
  obtain ⟨hT, hL, -, -⟩ := hH
  obtain ⟨h1, h2⟩ := clauses_word hA hB hC X hb hK hT hL u
  obtain ⟨h3, h4⟩ := clauses_word hA hB hC X hb hK hT hL u'
  exact ⟨h1, h2, h3, h4⟩

end MassDataLevelSSteps
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.InLevelSAtOfParts

section

@[expose] public section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.L2.SG.TypedSets Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Volumes

theorem inLevelSAt_of_parts (hLS : LevelSAll) (a1 : KSpCompact) (a2 : KSpOpen) (b1 : CMInst) (b2 : FrameStd)
    (b3 : LatAdapted) (b4 : ProdNH) (b5 : GlobFromParts) (c1 : HaarIdxLoc) (c2 : HaarIdxGlob) (c3 : LocLevi)
    (c4 : GlobProd) :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InLevelSAt X hb hK FdN FdN' u u' X0 L A :=
  inLevelSAt_of (typedNe_of a1 a2) (b5 hLS b1 b2 b3 b4) (ratioH_of c1 c2 c3 c4)

end MassDataLevelSSteps
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.KSpTop

section

@[expose] public section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem finiteDimensional_of_numberField (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : FiniteDimensional F E :=
  Module.Finite.of_restrictScalars_finite ℚ F E

theorem kSpCompact_holds : KSpCompact := by
  intro D X w p
  have := finiteDimensional_of_numberField X.B.I.F X.B.I.E
  exact (LatTop.isClosed_Ssub p.1 X.B.I.cm.sig X.B.I.J (frameOf X w)).isClosedEmbedding_subtypeVal.isCompact_preimage
    (LatTop.isCompact_Kv p.1 X.B.I.L X.B.I.L_span X.B.I.L_fg X.B.I.cm.sig X.B.I.J)

theorem kSpOpen_holds : KSpOpen := by
  intro D X w p
  have := finiteDimensional_of_numberField X.B.I.F X.B.I.E
  exact (LatTop.isOpen_Kv p.1 X.B.I.L X.B.I.L_span X.B.I.L_fg X.B.I.cm.sig X.B.I.J).preimage
    continuous_subtype_val

end MassDataLevelSSteps
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ProdNH

section

@[expose] public section

noncomputable section

namespace MassDataLevelSSteps.ProdW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes MeasureTheory NumberField
  IsDedekindDomain Topology PI.AdicCompletionValuation
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem isClosed_stabT (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [T2Space R]
    {a : ℕ} (X0 : Fin a → Fin n → E) :
    IsClosed ((stabT R σ J X0 : Subgroup (HA R σ J)) : Set (HA R σ J)) := by
  have hcont : Continuous fun g : HA R σ J => g • ratTup (F := F) R X0 := by
    show Continuous fun g : HA R σ J => actTup R (HA.mat R σ J g) (ratTup (F := F) R X0)
    unfold actTup HA.mat
    refine continuous_pi fun b => Continuous.matrix_mulVec ?_ continuous_const
    exact Units.continuous_val.comp
      (continuous_subtype_val : Continuous fun g : HR R σ J => (g : GL (Fin n) (R ⊗[F] E)))
  have : ((stabT R σ J X0 : Subgroup (HA R σ J)) : Set (HA R σ J)) =
      {g | g • ratTup (F := F) R X0 = ratTup (F := F) R X0} := by
    ext g
    exact MulAction.mem_stabilizer_iff
  rw [this]
  exact isClosed_eq hcont continuous_const

instance secondCountable_HAf : SecondCountableTopology (HA (Af F) σ J) :=
  PI.VolStabSW.TopoAF.secondCountable_HA_of (Af F) σ J

theorem prodNH_of {r : ℕ} (P : Frame E n r) (M : MeasW σ J P) (hM : M.IsTextNorm) :
    IsProdNH F E σ n J (Ssub (Af F) σ J P) (Nsub (Af F) σ J P) (Hsub (Af F) σ J P) M.μSf M.μNf M.μHf := by
  obtain ⟨-, -, hH, -, -, -, -, -, -, -, hS⟩ := hM
  have hcl : IsClosed ((Hsub (Af F) σ J P : Subgroup (HA (Af F) σ J)) : Set (HA (Af F) σ J)) :=
    isClosed_stabT σ J (Af F) (tupH P)
  have : LocallyCompactSpace (Hsub (Af F) σ J P) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have := hH
  have : SecondCountableTopology (HA (Af F) σ J) := secondCountable_HAf σ J
  have : SecondCountableTopology (Hsub (Af F) σ J P) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have : WeaklyLocallyCompactSpace (Hsub (Af F) σ J P) := inferInstance
  have : IsFiniteMeasureOnCompacts M.μHf := inferInstance
  have : IsLocallyFiniteMeasure M.μHf := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  have : SigmaFinite M.μHf := sigmaFinite_of_locallyFinite
  have : SFinite (amb M.μHf) := inferInstance
  have hmul : Measurable fun p : HA (Af F) σ J × HA (Af F) σ J => p.1 * p.2 := measurable_mul
  intro f hf
  have e1 : ∫⁻ k, f (k : HA (Af F) σ J) ∂M.μSf = ∫⁻ x, f x ∂(amb M.μSf) :=
    (lintegral_map hf measurable_subtype_coe).symm
  rw [e1, hS, lintegral_map hf hmul, lintegral_prod (fun p : HA (Af F) σ J × HA (Af F) σ J => f (p.1 * p.2)) (hf.comp hmul).aemeasurable]
  have hin : Measurable fun x : HA (Af F) σ J => ∫⁻ y, f (x * y) ∂(amb M.μHf) :=
    Measurable.lintegral_prod_right' (f := fun p : HA (Af F) σ J × HA (Af F) σ J => f (p.1 * p.2))
      (hf.comp hmul)
  rw [lintegral_map hin measurable_subtype_coe]
  refine lintegral_congr fun m => ?_
  exact lintegral_map (hf.comp (measurable_const_mul _)) measurable_subtype_coe

end MassDataLevelSSteps.ProdW

namespace MassDataLevelSSteps

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

theorem prodNH_holds : ProdNH := by
  intro D X w
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  exact ProdW.prodNH_of X.B.I.cm.sig X.B.I.J _ (X.measW w) (X.measW_norm w)

end MassDataLevelSSteps
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Assembly

section

@[expose] public section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.L2.SG.TypedSets Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem levelSAll_holds : Formalism.L2.SG.Volumes.LevelSAll := level_s_all_split

theorem inLevelSAt_holds :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InLevelSAt X hb hK FdN FdN' u u' X0 L A :=
  inLevelSAt_of_parts levelSAll_holds kSpCompact_holds kSpOpen_holds cmInst_holds frameStd_holds
    latAdapted_holds prodNH_holds globFromParts_holds haarIdxLoc_holds haarIdxGlob_holds locLevi_holds
    globProd_holds

end MassDataLevelSSteps
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataLevelS

section

@[expose] public section

theorem level_s_at_instance : ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X)) (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InLevelSAt X hb hK FdN FdN' u u' X0 L A :=
  MassDataLevelSSteps.inLevelSAt_holds
end
end
