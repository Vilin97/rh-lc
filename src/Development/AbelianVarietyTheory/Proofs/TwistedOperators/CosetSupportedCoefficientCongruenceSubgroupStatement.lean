module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetCharConditionIntegralUnitCongruentDepthStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizerStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResiduallyFiniteUnitOff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentComponentOfGroupElementStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingIdempotentPatchInFrameStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameIdempotentCutMatrixMemStabiliserReductionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjIdempotentConjFixedStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumInfPartIntegralOneSubMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalProjectionEqOfIdempotentPatchStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffFrameStabiliserAction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegralStatement
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatSmulSingle
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitian
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCongruenceSubgroupOfStabilisesAndCongruent

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.CongAssemble

open Matrix

variable {D : D7}

theorem isIntM_of_smul_maps {n : ℕ} {β : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (s : Lev.EAf D) (M : Matrix (Fin n) (Fin n) (Lev.EAf D))
    (h : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, s • (M *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    IsIntM (s • ((β⁻¹ : GL (Fin n) (Lev.EAf D)).1 * M * β.1)) := by
  intro i j
  have h1 := (hfr _).1 (h _ (GlobalTheory.FrameIdeal.col_mem_hatL hfr j)) i
  have e1 : (β⁻¹ : GL (Fin n) (Lev.EAf D)).1 *ᵥ (s • (M *ᵥ (β.1 *ᵥ Pi.single j 1))) =
      s • (((β⁻¹ : GL (Fin n) (Lev.EAf D)).1 * M * β.1) *ᵥ Pi.single j 1) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e1, Matrix.mulVec_single_one] at h1
  simpa [Matrix.smul_apply] using h1




theorem cong_assemble : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ 𝔪 : Ideal (𝓞 D.host.E),
    (∀ PP : Pl D.host.E, 𝔪 ≤ PP.asIdeal → PP ∈ Z) → ∀ g : GA D V,
    (∀ v, (∀ PP ∈ Z, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) →
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) →
    (∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      toEAf D e • ((Lev.finE V g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • (((Lev.finE V g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ)) →
    Lev.finE V g ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  classical
  intro D V Λ hsd Z e hZe 𝔪 h𝔪 g hg hx
  obtain ⟨β, hfr⟩ := frame_exists_alt D.host.F D.host.E V.rank Λ
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V Λ hsd)
  have hUA := GlobalTheory.LevSplit.finE_mem_UA V g
  have hγ : (β⁻¹ * Lev.finE V g * β : GL (Fin V.rank) (Lev.EAf D)).1 =
      (β⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 * (Lev.finE V g).1 * β.1 := by
    simp only [Units.val_mul]
  have hγi : ((β⁻¹ * Lev.finE V g * β)⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 =
      (β⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 * ((Lev.finE V g)⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 * β.1 := by
    simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  have h1 : IsIntM (toEAf D e • (β⁻¹ * Lev.finE V g * β : GL (Fin V.rank) (Lev.EAf D)).1) := by
    rw [hγ]; exact isIntM_of_smul_maps hfr _ _ fun x hx' => (hx x hx').1
  have h2 : IsIntM (toEAf D e • ((β⁻¹ * Lev.finE V g * β)⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1) := by
    rw [hγi]; exact isIntM_of_smul_maps hfr _ _ fun x hx' => (hx x hx').2.1
  obtain ⟨h3, h4⟩ := GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral V Λ β hsd hfr _ hUA _ rfl e h1 h2
  obtain ⟨hεε, hεc⟩ := GlobalTheory.T.idempotentSum_add_conj_idempotent_conj_fixed Z e hZe
  obtain ⟨k, -, hmt⟩ := GlobalTheory.T.exists_idempotent_component_of_group_element V (GlobalTheory.LevelNbhd.finPartG V g) (e + cA D e)
    (GlobalTheory.LevelNbhd.finPartG_mem_GfC V g) hεε hεc
  have hfk := GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame V β _ k (e + cA D e) hmt
  rw [GlobalTheory.SuppLevO.finE_finPartG] at hfk
  obtain ⟨hSt, -⟩ := GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction V.rank β _ _ Z e hZe h1 h2 h3 h4 hfk
  have hcomp : ∀ PP ∈ Z, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) k =
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g := fun PP hP => by
    rw [← GlobalTheory.SuppLevO.proj_finPartG V g]
    exact GlobalTheory.T.localProjection_eq_of_idempotent_patch V _ _ k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one Z e hZe PP hP) hmt
  have hkloc := (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V β Λ hfr k).1 hSt
  have hgSt : Lev.finE V g ∈ Formalism.L2.DIV.St β := by
    refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V β Λ hfr g).2 fun v => ?_
    by_cases hv : ∃ PP ∈ Z, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v
    · obtain ⟨PP, hP, rfl⟩ := hv
      rw [← hcomp PP hP]
      exact hkloc _
    · push_neg at hv
      exact hg v hv
  have hfw := GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β _ hfr hgSt
  have hbw := GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β _ hfr (inv_mem hgSt)

  have h𝔪0 : 𝔪 ≠ ⊥ := by
    intro h0
    haveI := GlobalTheory.LvT.Inh.ResFin.infinite_places D.host.E
    exact Set.infinite_univ (Z.finite_toSet.subset fun PP _ => h𝔪 PP (by rw [h0]; exact bot_le))
  have hrad : (∏ PP ∈ Z, PP.asIdeal) ≤ 𝔪.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun J ⟨hJ, hJp⟩ => ?_
    have hJ0 : J ≠ ⊥ := fun h => h𝔪0 (le_bot_iff.1 (h ▸ hJ))
    have hQ := h𝔪 ⟨J, hJp, hJ0⟩ hJ
    calc (∏ PP ∈ Z, PP.asIdeal) = (∏ PP ∈ Z.erase ⟨J, hJp, hJ0⟩, PP.asIdeal) * J := (Finset.prod_erase_mul _ _ hQ).symm
      _ ≤ J := by first | exact Ideal.mul_le_left | exact Ideal.mul_le_right | exact Ideal.mul_le_left'
  obtain ⟨N, hN⟩ := Ideal.exists_radical_pow_le_of_fg 𝔪 (IsNoetherian.noetherian _)
  have hle : (∏ PP ∈ Z, PP.asIdeal ^ N) ≤ 𝔪 := by
    rw [Finset.prod_pow]
    exact (Ideal.pow_right_mono hrad N).trans hN
  obtain ⟨t, ht, htv⟩ := (GlobalTheory.IdemSumIdeal.isIdemSum_props e Z (fun _ => N) hZe).2.2
  refine GlobalTheory.ChiGrid.mem_congLev.2 ⟨hUA, fun x => ⟨fun hx' => hfw x hx', fun hx' => ?_⟩, fun x hx' => ?_⟩
  · have := hbw _ hx'
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  · have hw : (Lev.finE V g).1 *ᵥ x - x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := Submodule.sub_mem _ (hfw x hx') hx'
    have e1 : (Lev.finE V g).1 *ᵥ x - x = toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) +
        (1 - toEAf D e) • ((Lev.finE V g).1 *ᵥ x - x) := by
      rw [← add_smul, add_sub_cancel, one_smul]
    rw [e1]
    refine Submodule.add_mem _ (hx x hx').2.2 ?_
    rw [← htv]
    exact Submodule.span_mono (Set.image_mono (Submodule.smul_mono_left hle)) (GlobalTheory.FrameIdeal.idS_smul_mem_hatL Λ ht hw)

end GlobalTheory.CongAssemble
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCongruenceSubgroupOfStabilisesAndCongruentStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix


theorem _root_.GlobalTheory.T.mem_congruenceSubgroup_of_stabilises_and_congruent : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ 𝔪 : Ideal (𝓞 D.host.E),
    (∀ PP : Pl D.host.E, 𝔪 ≤ PP.asIdeal → PP ∈ Z) → ∀ g : GA D V,
    (∀ v, (∀ PP ∈ Z, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) →
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) →
    (∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      toEAf D e • ((Lev.finE V g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • (((Lev.finE V g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ)) →
    Lev.finE V g ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  first | exact @GlobalTheory.CongAssemble.cong_assemble | exact GlobalTheory.CongAssemble.cong_assemble | (intros; apply GlobalTheory.CongAssemble.cong_assemble <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoeffEqZeroOfDistinctEigencharacters

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.TargetCoef

theorem coef_zero_of_target_eigen : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (m : Measure (WO S T)) (X : Set (WO S T)), IsCovolOne (ratL T S) m X → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F →
    ∀ (g : GA D T) (y : WO S T) (a b : AF D.host.F), heisO ψ S T y F = ψ a • F →
    heisO ψ S T (actO S T 1 g⁻¹ y) F = ψ b • F → ψ a ≠ ψ b → ∫ w in X, om (1, g) F w * conj (F w) ∂m = 0 := by
  intro D ψ S T χS χT om hw m X hm F hF g y a b ha hb hab
  have hψ := hw.std
  have hG : IsThetaFunO ψ S T (om (1, g) F) := hw.om_pres _ F hF
  have hact : actO S T 1 g (actO S T 1 g⁻¹ y) = y := by
    have := GlobalTheory.AdelicLatMove.actO_actO_inv S T 1 g y
    rwa [inv_one] at this
  have hy : heisO ψ S T y (om (1, g) F) = ψ b • om (1, g) F := by
    have e := hw.om_heis 1 g (actO S T 1 g⁻¹ y) F hF
    rw [hb, map_smul, hact] at e
    exact e.symm
  have hU := ((GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T m X hψ hm _ _ hG hF).2.2.2.2.2.2.1 y).1
  rw [hy, ha] at hU
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO at hU
  have hI : (∫ w in X, (ψ b • om (1, g) F) w * conj ((ψ a • F) w) ∂m) =
      (ψ b * conj (ψ a)) * ∫ w in X, om (1, g) F w * conj (F w) ∂m := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  rw [hI] at hU
  have hn : conj (ψ a) * ψ a = 1 := by
    rw [Complex.conj_mul', hψ.1.2.1 a]
    simp
  by_contra hne
  have hc : ψ b * conj (ψ a) = 1 := by
    have := congrArg (· / ∫ w in X, om (1, g) F w * conj (F w) ∂m) hU
    simpa [mul_div_assoc, div_self hne] using this
  apply hab
  calc ψ a = (ψ b * conj (ψ a)) * ψ a := by rw [hc, one_mul]
    _ = ψ b * (conj (ψ a) * ψ a) := by ring
    _ = ψ b := by rw [hn, mul_one]

end GlobalTheory.TargetCoef

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoeffEqZeroOfDistinctEigencharactersStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix


theorem _root_.GlobalTheory.T.weilMatrixCoeff_eq_zero_of_distinct_eigencharacters : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (m : Measure (WO S T)) (X : Set (WO S T)), IsCovolOne (ratL T S) m X → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F →
    ∀ (g : GA D T) (y : WO S T) (a b : AF D.host.F), heisO ψ S T y F = ψ a • F →
    heisO ψ S T (actO S T 1 g⁻¹ y) F = ψ b • F → ψ a ≠ ψ b → ∫ w in X, om (1, g) F w * conj (F w) ∂m = 0 := by
  first | exact @GlobalTheory.TargetCoef.coef_zero_of_target_eigen | exact GlobalTheory.TargetCoef.coef_zero_of_target_eigen | (intros; apply GlobalTheory.TargetCoef.coef_zero_of_target_eigen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSupportedCoefficientCongruenceSubgroup

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.CosSupport

theorem isHalf_actO_one {D : D7} (S T : HSp D) (c : AE D) (h : GA D T) (y : WO S T) (hy : IsHalf c y) :
    IsHalf c (actO S T 1 h y) := by
  intro i j
  simp only [actO, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hy k l]
  ring

theorem cosSupp : CosSupp := by
  classical
  intro D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ Φ hΦ m X hm g hg hne
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hw := W.om_is (.core i) (by show Node.InRange D.R.m (.core (i + 1)); simp [Node.InRange]; omega)
  have hth : IsThetaFunO W.ψ _ _ Φ := hΦ.1.1
  have hchar : ∀ y : WO (G.pS (.core i)) (G.pT (.core i)), IsHalf (cA D e) y →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u y) = 1) →
      (∀ u ∈ depLat G (.core i), W.ψ (symplO _ _ u (actO _ _ 1 g⁻¹ y)) = 1) →
      W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) y) =
        W.ψ (symplO (G.pS (.core i)) (G.pT (.core i)) (e • x₀.map (incA D)) (actO _ _ 1 g⁻¹ y)) := by
    intro y h1 h2 h3
    by_contra hne'
    exact hne (GlobalTheory.T.weilMatrixCoeff_eq_zero_of_distinct_eigencharacters D W.ψ _ _ _ _ (W.om (.core i)) hw m X hm Φ hth g y _ _ (hΦ.2 e he y h1 h2)
      (hΦ.2 e he _ (isHalf_actO_one _ _ _ _ y h1) h3) hne')
  have hloc := GlobalTheory.T.cosetCharCondition_integral_unit_congruent_depth D hq T L μ0 hL sc G W M hM i hi x₀ hx₀ e he g hchar
  refine GlobalTheory.T.mem_congruenceSubgroup_of_stabilises_and_congruent D (G.V (.core i)) (G.Λ (.core i)) (G.sp.P_is i (by omega)).sd G.pl.W0 e he G.modul ?_ g ?_ hloc
  · intro PP hPP
    have hprime : PP.asIdeal.IsPrime := PP.isPrime
    obtain ⟨v, hv, hle⟩ := hprime.prod_le.1 hPP
    have hle' : (G.pl.w v).asIdeal ≤ PP.asIdeal := hprime.le_of_pow_le hle
    have heq : G.pl.w v = PP := HeightOneSpectrum.ext ((G.pl.w v).isMaximal.eq_of_le hprime.ne_top hle')
    unfold Places.W0
    exact Finset.mem_image.2 ⟨v, hv, heq⟩
  · intro v hv
    apply hg v
    intro hvS
    exact hv _ (by unfold Places.W0; exact Finset.mem_image.2 ⟨v, hvS, rfl⟩) (G.pl.under_w hvS)

end GlobalTheory.CosSupport

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetSupportedCoefficientCongruenceSubgroupStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cosetSupported_coefficient_congruenceSubgroup : CosSupp := by
  first | exact @GlobalTheory.CosSupport.cosSupp | exact GlobalTheory.CosSupport.cosSupp | (intros; apply GlobalTheory.CosSupport.cosSupp <;> assumption)
end
end
