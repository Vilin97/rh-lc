module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjTranslatedEvaluationMemAllRowsSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ModelIdentificationRespectsRealAndFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphiStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefWeightedLocUncond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CastGAMemGFset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHaarFund
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTReg
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTRph
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientModelConjDiscreteSeriesOfGapStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowLevelTranslatedEvaluationOfConjRowStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedRowEvaluationSquareIntegrableNorm
import Formalism.LocalToGlobal.IndefiniteReal.MeasurableMulGA
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransferOfFundamentalDomains
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjTranslatedLevelRowEvaluationMemAllRows

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace


open GlobalTheory.Core.Mi GlobalTheory.Core.Mi.SeeHH in
theorem GlobalTheory.Mem.SRe.conj_ev_mem_HHX : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ S ∈ MultR R F, ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) → star φ ∈ HHX X := by
  intro hDS hP hUq hRF D G' _ _ Pl0 T A Ks _ _ _ R F X h t hIdE hG hLev hinf hν hSee c v₀ hc1 hc2 S hS φ hφ
  have hθ : IsInfFam R.θ := hinf
  have hMat : Matches X h (JR R F) (chiR R F) t := ⟨hSee.fin, hSee.conj⟩
  have hCV : ConjVec X h R.θ (MP R) v₀ := ⟨c, hc1, hc2⟩
  have hL : ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v))
      (Formalism.REAL.muG (X.B.I.ε v)) := fun v => by
    have h1 := Formalism.L2.SG.WuDecayPf.coef_integrable_of_weighted X
      (Formalism.L2.SG.Pf.WuDec.coefWeighted_of_gap X GlobalTheory.Sloc.CoefWeighted.coefWeightedLoc_uncond hG) v
    have hs : Integrable (fun g => star (Formalism.L2.SG.WuDecayPf.coefV X v g)) (Formalism.REAL.muG (X.B.I.ε v)) :=
      h1.mono (continuous_star.comp_aestronglyMeasurable h1.1) (ae_of_all _ fun g => le_of_eq (norm_star _))
    exact hs.const_mul ((X.dv v : ℝ) : ℂ)
  have hR := GlobalTheory.T.modelIdentification_respects_real_and_finite D X h R.θ hθ hIdE
  have hT : PiTensorProduct.lift S ∈ MultT R.θ (MP R) (JR R F) (chiR R F) := by
    refine (mem_multT R.θ (MP R) (JR R F) (chiR R F) _).2 ?_
    rw [LinearEquiv.symm_apply_apply]; exact hS
  obtain ⟨hRow, hMem⟩ := GlobalTheory.T.translateToSecondModel_cuspFormMap_value_automorphic hP D X h R.θ _ (MP R) (JR R F) (chiR R F) t hθ hMat _ hT
    (PiTensorProduct.tprod ℂ v₀)
  have hfx : ∀ x, evS X h t (PiTensorProduct.lift S (PiTensorProduct.tprod ℂ v₀)) x =
      S v₀ ((iotaX X h).symm x * t) := fun x => by
    delta evS
    rw [PiTensorProduct.lift.tprod]
  generalize evS X h t (PiTensorProduct.lift S (PiTensorProduct.tprod ℂ v₀)) = f at hRow hMem hfx
  have hφ2 : (φ : X.B.I.GA → ℂ) =ᵐ[muX X] f := hφ.trans (Filter.Eventually.of_forall fun x => (hfx x).symm)
  have hφ' : φ = hMem.toLp f := Lp.ext (hφ2.trans hMem.coeFn_toLp.symm)
  have hRe := re_fix_of_row X hRow hMem
  have hι : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ iotaX X h g ∈ X.B.I.GFset := by
    intro g
    rw [Formalism.IndefR.RationalEmbedding.iota_rat]
    exact GlobalTheory.Mem.SJ.SchurMove.castGA_mem_GFset _ _
  obtain ⟨κ, hκ⟩ := GlobalTheory.Mem.SJ.HaarMove.schur_of_bridge (MP R) R.θ (JR R F) (chiR R F)
    (fun μ 𝓕 => GlobalTheory.MultFinite.schurMult hP μ 𝓕) hθ
    X.B.I X.B.μf X.B.fund X.B.fund_spec (iotaX X h) hι t S hS S hS
  have hv₀ : ∏ τ, ⟪(v₀ τ : (MP R).H τ), (v₀ τ : (MP R).H τ)⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    have hn : ‖(v₀ τ : (MP R).H τ)‖ = 1 := by
      rw [← (c τ).norm_map, hc2 τ]
      exact (X.low _).1
    rw [inner_self_eq_norm_sq_to_K, hn]
    simp
  have hs : MemLp (fun x => star (f x)) 2 (muX X) := hMem.star
  have hinv : ∀ γ ∈ X.B.I.GFset, ∀ y, star (f (γ * y)) = star (f y) := fun γ hγ y => by
    rw [hRow.left γ hγ y]
  have hnorm : (((‖hs.toLp (fun x => star (f x))‖ ^ 2 : ℝ)) : ℂ) = κ := by
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp hs, ← integral_complex_ofReal]
    have e := hκ v₀ v₀
    rw [hv₀, mul_one] at e
    rw [← e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [norm_star, hfx x, ← starRingEnd_apply, Complex.conj_mul']
    push_cast
    ring
  have hRph : X.Rph (star (hMem.toLp f)) = star (hMem.toLp f) := by
    rw [star_toLp_eq X hMem hs]
    refine Formalism.L2.SG.EvalTRph.rph_fix_of_coef X hL _ (fun g => ?_)
    obtain ⟨a, ha, hb, w, hw, hsh⟩ := real_shift X h R.θ (MP R) (JR R F) (chiR R F) t hMat.1 hR v₀ g
    have hco := coef_eq X h R.θ (MP R) v₀ hCV g a ha hb w hw
    have hRg := Formalism.L2.SG.EvalTReg.reg_toLp_X X (fun x => star (f x)) hinv hs (g, 1)
    have hpair : ⟪hs.toLp (fun x => star (f x)), X.B.R (g, 1) (hs.toLp (fun x => star (f x)))⟫_ℂ =
        ∫ x, star (S w ((iotaX X h).symm x * t)) * S v₀ ((iotaX X h).symm x * t) ∂(muX X) := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hs.coeFn_toLp, hRg] with x a1 a2
      rw [a1, a2]
      simp only [RCLike.inner_apply, hfx]
      rw [hsh S hS x, starRingEnd_apply, star_star, mul_comm]
    rw [hpair, hκ w v₀, hco, hnorm]
  rw [hφ']
  refine ⟨star (hMem.toLp f), ?_⟩
  show X.B.Re (X.Rph _) = _
  rw [hRph, hRe]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjTranslatedLevelRowEvaluationMemAllRowsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.conj_translated_level_row_evaluation_mem_all_rows : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ S ∈ MultR R F, ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) → star φ ∈ HHX X := by
  exact @GlobalTheory.Mem.SRe.conj_ev_mem_HHX
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedEvaluationSquareIntegrableNormAllRows

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.EvalAllRows

theorem eq_zero_of_units {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (T : MMap M)
    (h : ∀ v : M.Vec, (∀ τ, ‖(v τ : M.H τ)‖ = 1) → T v = 0) : T = 0 := by
  classical
  refine MultilinearMap.ext fun v => ?_
  by_cases hz : ∃ τ, v τ = 0
  · obtain ⟨τ, hτ⟩ := hz
    exact T.map_coord_zero τ hτ
  · push_neg at hz
    have hn : ∀ τ, ‖(v τ : M.H τ)‖ ≠ 0 := fun τ e => hz τ (Subtype.ext (norm_eq_zero.1 e))
    let u : M.Vec := fun τ => ((‖(v τ : M.H τ)‖⁻¹ : ℝ) : ℂ) • v τ
    have hu : ∀ τ, ‖(u τ : M.H τ)‖ = 1 := fun τ => by
      simp only [u, Submodule.coe_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (hn τ)
    have hv : v = fun τ => ((‖(v τ : M.H τ)‖ : ℝ) : ℂ) • u τ := by
      funext τ
      simp only [u, smul_smul]
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hn τ), Complex.ofReal_one, one_smul]
    rw [hv, T.map_smul_univ, h u hu, smul_zero]
    rfl

end GlobalTheory.EvalAllRows

theorem GlobalTheory.EvalAllRows.evalTranslate_norm_all : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ c : ℝ, 0 < c ∧ ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → ∀ S ∈ MultR R F, MemLp (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) 2 (muX X) ∧ ∫ x, ‖ev (MP R) v₀ S ((iotaX X h).symm x * t)‖ ^ 2 ∂(muX X) = c * (ipM (MP R) R.ν0 R.fd0 S S).re ∧ ((ipM (MP R) R.ν0 R.fd0 S S).re = 0 → S = 0) := by
  intro _ hCusp _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hHE hGap hL hinf hν0 hsee
  haveI hνH : R.ν0.IsHaarMeasure := hν0.1.1
  obtain ⟨c, hc, hmap⟩ := @GlobalTheory.EvalNormTransfer.exists_map_eq_smul D X h R.ν0 hνH
  obtain ⟨hι, hιs⟩ := measurable_of_borel X (iotaX X h) (GlobalTheory.EvalNormTransfer.borel_inst X)
  have hTr : SquareIntegrableTransfer R.ν0 R.fd0 X (iotaX X h).toMulEquiv t c :=
    squareIntegrableTransfer_of_rational_points R.ν0 R.fd0 X _ t c hι hιs hc hmap hνH hν0.2 (GlobalTheory.EvalNormTransfer.iotaX_rat X h)
  refine ⟨c, hc, fun v₀ hv S hS => ?_⟩
  have hSch : ∀ S' ∈ MultR R F, ∃ c', IsMultIP (MP R) R.ν0 R.fd0 S' S' c' := fun S' hS' =>
    GlobalTheory.MultFinite.schurMult hCusp R.ν0 R.fd0 hinf hνH hν0.2 S' hS' S' hS'
  have hcont : ∀ S' ∈ MultR R F, ∀ v, Continuous (S' v) ∧ ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S' v (γ * g) = S' v g :=
    fun S' hS' v => Formalism.IndefR.PeterssonHilbertSpace.mult_cont_left (M := R.MY 0) (θ := R.θ) (J := JR R F) (χ := chiR R F) hS' v
  haveI : BorelSpace (GA D (D.sp.Y 0)) := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (Yc D 0)
  have hL2 : ∀ S' ∈ MultR R F, ∀ v, MemLp (S' v) 2 (R.ν0.restrict R.fd0) := by
    intro S' hS' v
    obtain ⟨c', hip⟩ := hSch S' hS'
    refine (memLp_two_iff_integrable_sq_norm (hcont S' hS' v).1.measurable.aestronglyMeasurable).2
      (((hip v v).1).norm.congr (.of_forall fun x => ?_))
    simp only [norm_mul, norm_star, sq]
  obtain ⟨hm, hn⟩ := hTr (S v₀) (hcont S hS v₀).1 (hcont S hS v₀).2 (hL2 S hS v₀)
  refine ⟨hm, hn.trans (congrArg (c * ·) (re_ipM_eq (hSch S hS) hv).symm), ?_⟩
  intro h0
  refine GlobalTheory.EvalAllRows.eq_zero_of_units (MP R) S fun v hv' => ?_
  by_contra hne
  have hre := re_ipM_eq (hSch S hS) hv'
  have hint : IntegrableOn (fun x => ‖S v x‖ ^ 2) R.fd0 R.ν0 :=
    (memLp_two_iff_integrable_sq_norm (hL2 S hS v).aestronglyMeasurable).1 (hL2 S hS v)
  have hp := Formalism.IndefR.PeterssonHilbertSpace.petPos (D.sp.Y 0) R.ν0 R.fd0 hνH hν0.2 (S v) (hcont S hS v).1 (hcont S hS v).2 hne hint
  rw [← hre, h0] at hp
  exact lt_irrefl _ hp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedEvaluationSquareIntegrableNormAllRowsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.translatedEvaluation_squareIntegrable_norm_all_rows : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ c : ℝ, 0 < c ∧ ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → ∀ S ∈ MultR R F, MemLp (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) 2 (muX X) ∧ ∫ x, ‖ev (MP R) v₀ S ((iotaX X h).symm x * t)‖ ^ 2 ∂(muX X) = c * (ipM (MP R) R.ν0 R.fd0 S S).re ∧ ((ipM (MP R) R.ν0 R.fd0 S S).re = 0 → S = 0) := by
  first | exact @GlobalTheory.EvalAllRows.evalTranslate_norm_all | exact GlobalTheory.EvalAllRows.evalTranslate_norm_all | (intros; apply GlobalTheory.EvalAllRows.evalTranslate_norm_all <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestVectorEvaluationIdentifiesLevelRowsConj

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe



theorem evalOn_all : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) ∧ ∃ c : ℝ, 0 < c ∧ EvalOn R X h t v₀ c (MultR R F) (conjRows X) := by
  intro hDS hCusp hU hFin D G' _ _ Pl0 T A Ks _ _ _ R F X h t hE hGap hl hi hν hsee
  obtain ⟨cc, hcc, hsm⟩ := GlobalTheory.T.contragredientModel_conjDiscreteSeries_of_gap hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee
  let v₀ : (MP R).Vec := fun τ => ⟨(cc τ).symm (X.B.w (X.pl.symm τ)), hsm τ⟩
  have hv₀ : ∀ τ, cc τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ) := fun τ => by simp [v₀]
  have hnorm : ∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1 := fun τ => by
    show ‖(cc τ).symm (X.B.w (X.pl.symm τ))‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact (X.low _).1
  obtain ⟨c0, hc0, hN⟩ := GlobalTheory.T.translatedEvaluation_squareIntegrable_norm_all_rows hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee
  have hI := GlobalTheory.T.conj_translated_level_row_evaluation_mem_all_rows hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee cc v₀ hcc hv₀
  have hO := GlobalTheory.T.exists_rowLevel_translatedEvaluation_of_conj_row hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee cc v₀ hcc hv₀
  refine ⟨v₀, hnorm, c0, hc0, ?_⟩
  classical
  have hmem : ∀ S : MultR R F, MemLp (fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) 2 (muX X) :=
    fun S => (hN v₀ hnorm S S.2).1
  let Φ : MultR R F → conjRows X := fun S =>
    ⟨(hmem S).toLp _, hI S S.2 _ (hmem S).coeFn_toLp⟩
  have hΦ : ∀ S, ((Φ S : conjRows X) : L2X X) =ᵐ[muX X]
      (fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) := fun S => (hmem S).coeFn_toLp
  have key : ∀ (S : MultR R F) (Fx : conjRows X), ((Fx : L2X X) =ᵐ[muX X]
      fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) → Φ S = Fx := by
    intro S Fx hF
    apply Subtype.ext
    apply Lp.ext
    exact (hΦ S).trans hF.symm
  let L : MultR R F →ₗ[ℂ] conjRows X :=
    { toFun := Φ
      map_add' := fun S S' => by
        apply key
        have h1 := hΦ S
        have h2 := hΦ S'
        have h3 := Lp.coeFn_add ((Φ S : conjRows X) : L2X X) ((Φ S' : conjRows X) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.add h2))).trans ?_
        · simp only [Submodule.coe_add]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply]
      map_smul' := fun a S => by
        rw [RingHom.id_apply]
        apply key
        have h1 := hΦ S
        have h3 := Lp.coeFn_smul a ((Φ S : conjRows X) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.const_smul a))).trans ?_
        · simp only [Submodule.coe_smul]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply] }
  have hLn : ∀ S : MultR R F, ‖((L S : conjRows X) : L2X X)‖ ^ 2 =
      c0 * (ipM (MP R) R.ν0 R.fd0 (S : MMap (MP R)) (S : MMap (MP R))).re := by
    intro S
    show ‖((hmem S).toLp _ : L2X X)‖ ^ 2 = _
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp (hmem S)]
    exact (hN v₀ hnorm S S.2).2.1
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro S hS
    have h1 := hLn S
    rw [hS] at h1
    simp only [ZeroMemClass.coe_zero, norm_zero, zero_pow two_ne_zero] at h1
    have h2 := (mul_eq_zero_iff_left hc0.ne').mp h1.symm
    exact Subtype.ext ((hN v₀ hnorm S S.2).2.2 h2)
  have hsurj : Function.Surjective L := by
    intro Fx
    obtain ⟨S, hS, hF⟩ := hO (Fx : L2X X) Fx.2
    exact ⟨⟨S, hS⟩, key ⟨S, hS⟩ Fx hF⟩
  refine ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun S => ⟨hΦ S, hLn S⟩⟩

end GlobalTheory.Mem.SRe
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestVectorEvaluationIdentifiesLevelRowsConjStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lowestVector_evaluation_identifies_levelRows_conj : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) ∧ ∃ c : ℝ, 0 < c ∧ EvalOn R X h t v₀ c (MultR R F) (conjRows X) := by
  exact GlobalTheory.Mem.SRe.evalOn_all
end
end
