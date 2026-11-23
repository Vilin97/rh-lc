module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
public import Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFactorNonzero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsMaxCompactEqFrameGramSplitBasis
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsScaledStandardPairSectionsOfMaxCompactTran
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizer
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceIsoReadingComponentsCharacters
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.LocalEmbeddings.BotCoord
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawCharacterConductorAtRamifiedPlace

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.StdPairConeChars

theorem condLE_mono {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {e m : ℕ} (hem : e ≤ m)
    {χ : (Fv F v)ˣ →* ℂˣ} (h : GlobalTheory.SplitFlip.CondLE (unifAt v) e χ) : GlobalTheory.SplitFlip.CondLE (unifAt v) m χ := by
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have h1 : ValuativeRel.valuation (Fv F v) ((unifAt v : (Fv F v)ˣ) : Fv F v) ≤ 1 := hϖ.mem
  intro x hx
  refine h x ⟨hx.1, hx.2.trans ?_⟩
  simp only [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_pow_right_of_le_one' h1 hem

theorem nu_cond_at_ram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ v : B.P, v.1 ∈ X.T →
      GlobalTheory.SplitFlip.CondLE (unifAt v.1) (condExp (chrW X.ν (B.τ v))) (chrW X.ν (B.τ v)) ∧ 1 ≤ (condExp (chrW X.ν (B.τ v))) ∧
      chrW X.ν (B.τ v) = chrW X.α (B.τ v) / chrW X.β (B.τ v) ∧
      (∃ m, GlobalTheory.SplitFlip.CondLE (unifAt v.1) m (chrW X.α (B.τ v)) ∧ GlobalTheory.SplitFlip.CondLE (unifAt v.1) m (chrW X.β (B.τ v))) ∧
      (∀ x, ‖(chrW X.α (B.τ v) x : ℂ)‖ = 1) ∧ ∀ x, ‖(chrW X.β (B.τ v) x : ℂ)‖ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hvT
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v.1) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v.1)).choose_spec
  have hα := hT.chars.heckeα.1
  have hβ := hT.chars.heckeβ.1
  have hν : Continuous X.ν := (show Continuous fun x => X.α x / X.β x from hα.div' hβ)
  have hne : {c | GlobalTheory.SplitFlip.CondLE (unifAt v.1) c (chrW X.ν (B.τ v))}.Nonempty :=
    GlobalTheory.GaussNonvanish.exists_condLE hϖ _ (GlobalTheory.StepFacNe.chrW_continuous X.ν hν (B.τ v))
  have hmem : GlobalTheory.SplitFlip.CondLE (unifAt v.1) (condExp (chrW X.ν (B.τ v))) (chrW X.ν (B.τ v)) := Nat.sInf_mem hne
  obtain ⟨eα, heα⟩ := GlobalTheory.GaussNonvanish.exists_condLE hϖ _ (GlobalTheory.StepFacNe.chrW_continuous X.α hα (B.τ v))
  obtain ⟨eβ, heβ⟩ := GlobalTheory.GaussNonvanish.exists_condLE hϖ _ (GlobalTheory.StepFacNe.chrW_continuous X.β hβ (B.τ v))
  have hram : ¬ UnrAt X.ν (splitPrime (B.τ v)) :=
    hT.chars.ram _ (by rw [splitPrime_under]; exact hvT)
  obtain ⟨x₀, hx₀, hx₀', hνx₀⟩ := GlobalTheory.StepFacNe.chrW_ram X.ν (B.τ v) hram
  have hx₀v : ValuativeRel.valuation (Fv F v.1) (x₀ : Fv F v.1) = 1 := by
    have h1 := (GlobalTheory.GaussNonvanish.val_le_one_iff v.1 _).2 hx₀
    have h2 := (GlobalTheory.GaussNonvanish.val_le_one_iff v.1 _).2 hx₀'
    have h3 : ValuativeRel.valuation (Fv F v.1) (x₀ : Fv F v.1) *
        ValuativeRel.valuation (Fv F v.1) ((x₀⁻¹ : (Fv F v.1)ˣ) : Fv F v.1) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    refine le_antisymm h1 ?_
    calc (1 : ValuativeRel.ValueGroupWithZero (Fv F v.1)) = _ := h3.symm
      _ ≤ _ := mul_le_of_le_one_right' h2
  have hc1 : 1 ≤ condExp (chrW X.ν (B.τ v)) := by
    by_contra h
    have h0 : condExp (chrW X.ν (B.τ v)) = 0 := by omega
    have hm := hmem
    rw [h0] at hm
    refine hνx₀ (hm x₀ ⟨hx₀v, ?_⟩)
    rw [pow_zero, Units.val_one, map_one]
    exact ((ValuativeRel.valuation (Fv F v.1)).map_sub _ _).trans (by simp [hx₀v])
  have hdiv : chrW X.ν (B.τ v) = chrW X.α (B.τ v) / chrW X.β (B.τ v) := by
    ext x
    simp [chrW, locChar, Chars.ν]
  refine ⟨hmem, hc1, hdiv, ⟨max eα eβ, condLE_mono (le_max_left _ _) heα, condLE_mono (le_max_right _ _) heβ⟩,
    fun x => ?_, fun x => ?_⟩
  · exact GlobalTheory.ChrWSmooth.isUnitaryChar_chrW X.α (B.τ v) x
  · exact GlobalTheory.ChrWSmooth.isUnitaryChar_chrW X.β (B.τ v) x

end GlobalTheory.StdPairConeChars
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawCharacterConductorAtRamifiedPlaceStatement

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.seesawCharacter_conductor_at_ramified_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ v : B.P, v.1 ∈ X.T →
      GlobalTheory.SplitFlip.CondLE (unifAt v.1) (condExp (chrW X.ν (B.τ v))) (chrW X.ν (B.τ v)) ∧ 1 ≤ (condExp (chrW X.ν (B.τ v))) ∧
      chrW X.ν (B.τ v) = chrW X.α (B.τ v) / chrW X.β (B.τ v) ∧
      (∃ m, GlobalTheory.SplitFlip.CondLE (unifAt v.1) m (chrW X.α (B.τ v)) ∧ GlobalTheory.SplitFlip.CondLE (unifAt v.1) m (chrW X.β (B.τ v))) ∧
      (∀ x, ‖(chrW X.α (B.τ v) x : ℂ)‖ = 1) ∧ ∀ x, ‖(chrW X.β (B.τ v) x : ℂ)‖ = 1 := by
  first | exact @GlobalTheory.StdPairConeChars.nu_cond_at_ram | exact GlobalTheory.StdPairConeChars.nu_cond_at_ram | (intros; apply GlobalTheory.StdPairConeChars.nu_cond_at_ram <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.DivisorFrames.LocalCharConductorLeOfHeckeExponent

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.localChar_conductor_le_of_heckeExponent :
    ∀ (D : D7) (ν : (AE D)ˣ →* Circle) (νH : Formalism.L2.Host.HChar D.host.E), ChrEq ν νH →
        ∀ (v : Pl D.host.F) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (c : ℕ), GlobalTheory.CMVal.ExpAt νH (splitPrime τ) c →
        GlobalTheory.SplitFlip.CondLE (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) c (chrW ν τ) ∧ (¬ GlobalTheory.LFun.UnrAt ν (splitPrime τ) → 1 ≤ c) := by
  intro D ν νH h v τ c hc
  refine ⟨fun x hx => ?_, fun hn => ?_⟩
  · have h1 : Valued.v (x : Fv D.host.F v) = 1 := (GlobalTheory.FlipMatch.isEquiv_Fv v).eq_one_iff_eq_one.1 hx.1
    have h2 : Valued.v ((x : Fv D.host.F v) - 1) ≤ WithZero.exp (-(c : ℤ)) := by
      refine ((GlobalTheory.FlipMatch.isEquiv_Fv v _ _).1 hx.2).trans_eq ?_
      rw [Units.val_pow_eq_pow_val, map_pow, GlobalTheory.ChrWUnif.valued_unifAt, ← WithZero.exp_nsmul]
      simp
    have h3 := (hc c).2 le_rfl (Units.map (complMap (splitPrime_under τ)).toMonoidHom x)
      ((SplitTie.valued_complMap τ (splitPrime_under τ) _).trans h1) (by
        refine le_of_eq_of_le ?_ h2
        rw [← SplitTie.valued_complMap τ (splitPrime_under τ), RingHom.map_sub, RingHom.map_one]
        rfl)
    rw [← locChar_eq_of_chrEq h] at h3
    exact h3
  · by_contra h0
    apply hn
    rw [unrAt_iff_of_chrEq h]
    intro x hx
    refine (hc 0).2 (by omega) x hx ?_
    rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
    exact Valuation.map_sub_le _ (le_of_eq hx) (le_of_eq (map_one _))
end
end

-- Source module: Development.AutomorphicArithmetic.LocalEmbeddings.BotLocal

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

namespace GlobalTheory.BotMatch

variable {D : D7}


theorem local_pair {ψ : AddChar (AF D.host.F) ℂ} {W W₁ X : HSp D} {A : GlobalTheory.ChainFr.Fr W} {A₁ : GlobalTheory.ChainFr.Fr W₁}
    {B : GlobalTheory.ChainFr.Fr X} {α β : (AE D)ˣ →* Circle} {e : Fin (W.rank + W₁.rank) ≃ Fin X.rank} {Bs : Base D.host.F D.host.E}
    {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank} {Xc : Chars D.host.F D.host.E} {om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W}
    {om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W} (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc) {R Rf}
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf) {ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)}
    (sW : IsSelfDualC (GlobalTheory.Grid.sgn true W) ΛW) {βW : GL (Fin W.rank) (Lev.EAf D)} (fW : Formalism.L2.DIV.IsFrame βW ΛW)
    (hL : Γ.V.L = GlobalTheory.TripleSpaceW.conjSub ΛW) (βW₁ : GL (Fin W₁.rank) (Lev.EAf D)) (βX : GL (Fin X.rank) (Lev.EAf D))
    {νH : Formalism.L2.Host.HChar D.host.E} (hν : ChrEq (α / β) νH) (i : Bs.P) (hi : i.1 ∈ Xc.T) {c : ℕ}
    (hc : GlobalTheory.CMVal.ExpAt νH (splitPrime (Bs.τ i)) c) :
    ∃ (I : ((Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F i.1) → ℂ) →ₗ[ℂ]
        (Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (Fv D.host.F i.1) → ℂ))
      (I' : ((Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F i.1) → ℂ) →ₗ[ℂ]
        (Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (Fv D.host.F i.1) → ℂ))
      (φ : (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F i.1) → ℂ)
      (φ' : (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F i.1) → ℂ) (lam : ℂ),
      Γ.M.IsLinW Bs.ψ (Bs.τ i) (Γ.V.bas i) (Γ.W.bas i) I ∧ Γ.M'.IsLinBar Bs.ψ (Bs.τ i) (Γ.V'.bas i) (Γ.W.bas i) I' ∧
      φ ∈ GlobalTheory.WeilM.SB _ ∧ φ' ∈ GlobalTheory.WeilM.SB _ ∧ φ ≠ 0 ∧ φ' ≠ 0 ∧ lam ≠ 0 ∧ Rf.p i φ = Rf.p' i φ' ∧
      (∀ x : WO W X, I φ (((Γ.V.bas i)⁻¹).1 * (GlobalTheory.TripleRead.ptO (GlobalTheory.Grid.sgn true W).gram e x).map (piW (Bs.τ i)) *
          ((Γ.W.bas i)⁻¹).1ᵀ) =
        GlobalTheory.StdPairCone.stdA (chrW (α / β) (Bs.τ i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt i.1) c W.rank W₁.rank
          ((((frMapO W X βW βX x).map (evW (Bs.τ i)))ᵀ).submatrix id e)) ∧
      ∀ y : WO W₁ X, I' φ' (-((Γ.V'.bas i).1ᵀ * Γ.V'.J.map (Bs.τ i) *
          (GlobalTheory.TripleRead.ptO W₁.gram e y).map (piW ((Bs.τ i).comp D.sp.cm.sig)) * (Γ.W.J.map (Bs.τ i))ᵀ * (Γ.W.bas i).1)) =
        lam * GlobalTheory.StdPairCone.stdB (chrW (α / β) (Bs.τ i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt i.1) c W.rank W₁.rank
          (((GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord W₁ X βW₁ βX y).map (evW (Bs.τ i))).submatrix id e) := by
  have hXν : Xc.ν = α / β := by
    show Xc.α / Xc.β = _
    rw [h.α, h.β]
  obtain ⟨I, I', hI, hI', -, -, hiff⟩ := hM.fin.zeta i hi
  obtain ⟨-, -, hquot, ⟨m, hmα, hmβ⟩, hua, hub⟩ := GlobalTheory.T.seesawCharacter_conductor_at_ramified_place _ _ _ Bs _ _ Γ Xc om om' hM.triple i hi
  obtain ⟨hcond, hc1⟩ := UpperTheory.localChar_conductor_le_of_heckeExponent D (α / β) νH hν i.1 (Bs.τ i) c hc
  have hram := hM.triple.chars.ram (splitPrime (Bs.τ i)) ((splitPrime_under (Bs.τ i)).symm ▸ hi)
  rw [hXν] at hram
  obtain ⟨gA, hgA, egA⟩ := UpperTheory.exists_maxCompact_eq_frame_gram_splitBasis D (GlobalTheory.Grid.sgn true W) ΛW βW sW fW i.1 (Bs.τ i) (Γ.V.bas i)
    (hL ▸ hM.triple.geo.hV.bas i)
  have hx1 : (βX.val.map (evW (Bs.τ i))).submatrix e e * ((βX⁻¹).val.map (evW (Bs.τ i))).submatrix e e = 1 := by
    rw [Matrix.submatrix_mul_equiv, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.submatrix_one_equiv]
  let bX : GL (Fin (W.rank + W₁.rank)) (Fv D.host.F i.1) := ⟨_, _, hx1, mul_eq_one_comm.1 hx1⟩
  have hy1 : (βW₁⁻¹).val.map (evW (Bs.τ i)) * βW₁.val.map (evW (Bs.τ i)) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hy2 := gram_inv_map (Bs.τ i) W₁
  have hy3 : ((Γ.V'.bas i)⁻¹).valᵀ * (Γ.V'.bas i).valᵀ = 1 := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  let gB : GL (Fin W₁.rank) (Fv D.host.F i.1) :=
    ⟨_, _, hy1, mul_eq_one_comm.1 hy1⟩ * ⟨_, _, hy2, mul_eq_one_comm.1 hy2⟩ * ⟨_, _, hy3, mul_eq_one_comm.1 hy3⟩
  rw [← hXν] at hcond ⊢
  obtain ⟨lam, Ξ, Ψ, hlam, eΞ, eΨ, sΞ, sΨ, nΞ, nΨ, hz⟩ := UpperTheory.exists_scaled_standardPairSections_of_maxCompact_translate (Fv D.host.F i.1) _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt i.1) c m
    W.rank W₁.rank (GlobalTheory.SplitFlip.exists_isUnif).choose_spec hquot (hc1 hram) hcond hmα hmβ hua hub gA gB
    ((Γ.W.bas i)⁻¹ * bX) hgA
  obtain ⟨φ, sφ, rfl⟩ := hI.bij.surjOn sΞ
  obtain ⟨φ', sφ', rfl⟩ := hI'.bij.surjOn sΨ
  refine ⟨I, I', φ, φ', lam, hI, hI', sφ, sφ', fun h0 => nΞ (by rw [h0, map_zero]), fun h0 => nΨ (by rw [h0, map_zero]), hlam,
    (hiff φ sφ φ' sφ').2 hz, fun x => ?_, fun y => ?_⟩
  · rw [eΞ, egA]
    exact congrArg _ (frMapO_coX (Bs.τ i) (GlobalTheory.Grid.sgn true W) X e βW βX (Γ.V.bas i) (Γ.W.bas i) x)
  · rw [eΨ, h.JW₁, h.JX]
    exact congrArg (fun z => lam * GlobalTheory.StdPairCone.stdB _ _ c _ _ z)
      (dualCoord_coY (Bs.τ i) W₁ X e βW₁ βX (Γ.V'.bas i) (Γ.W.bas i) y)

end GlobalTheory.BotMatch

end
end
end
