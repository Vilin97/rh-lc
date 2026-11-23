module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodSplitPlaceTranslationActsThroughWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExistStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecondStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalarStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceHeisenbergDerivThetaTransformAlgebraicD
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LieSecondOrderOfRealLift
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumDifferentiableAlongLine
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilLieAlgebraScalarAction
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivariance

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolStabInf

open Formalism.BasicNotions.TH GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem hasExp_div (τ : ∀ w : InfinitePlace F, EmbOver E w) {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (fun w => m w - m' w) := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : piInf (τ w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) / (‖piInf (τ w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))‖ : ℂ) ≠ 0 := by
    have h0 : piInf (τ w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ≠ 0 := by
      intro e
      have := congrArg (piInf (τ w)) z.mul_inv
      rw [map_mul, e, zero_mul, map_one] at this
      exact zero_ne_one this
    exact div_ne_zero h0 (by exact_mod_cast norm_ne_zero_iff.2 h0)
  rw [zpow_sub₀ this]

theorem locFin_fock1 (P Q R S : ℕ) (X : Mat P Q) (hX : IsKC X) (c : ℂ) :
    LocFin (fockAct1 P Q R S X + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).1 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs X hX y hy) (W.smul_mem c hy)⟩

theorem locFin_fock2 (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩


open scoped Classical in
theorem polStab : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    (∀ γ ∈ Lines σ G.V, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ G.M.Pol B.ψ B.emb) ∧
    (∀ k ∈ KInf σ G.V B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ G.M.Pol B.ψ B.emb) ∧
    (∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ f₂ : SInf F (Fin a × Fin (a + a')),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₂ → f₂ = f₁) ∧
    (∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb,
      Acts (evI F) (om (1, k)) f f₁ ∧ ∀ f₂ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, k)) f f₂ → f₂ = f₁) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' h
  obtain ⟨hb, hg, hc, hw, -⟩ := h
  choose A hA hAθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hD := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hD
  have hfe := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hD
  have hsec := GlobalTheory.T.lieSecond_of_prints_derEx_fockEx_vacLine_lieScalar hK.base hD hfe hvl (GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hK.base hD hvl)
  have hfst := GlobalTheory.T.lieFirst_of_lieSecond' hsec
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hD hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr
    hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1
    hc.expβ
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (hasExp_div B.emb hc.expβ hc.expα)
  have hadm := fun g => (hwp.isUSplitting).adm g
  have hL := GlobalTheory.RealLift.actsLaws
  have mem : ∀ T, Φ T ∈ G.M.Pol B.ψ B.emb := fun T => hr ▸ LinearMap.mem_range_self Φ T
  have pol : ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ T, f = Φ T := fun f hf => by
    rw [← hr] at hf
    obtain ⟨T, rfl⟩ := hf
    exact ⟨T, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ hγ f hf f₁ h1
    obtain ⟨T, rfl⟩ := pol f hf
    obtain ⟨Yg, -, hY⟩ := GlobalTheory.T.oneParamSubgroup_generators_exist F E σ (Fin a) _ _ B.emb (incM F G.V.J) 1 A hb.cm hA1 γ hγ
    have h2 := (hL F _ (Φ T) _ f₁).1 _ (fun t => map_zero _) (hW1 γ hγ Yg hY T)
    have e := (hL F _ (Φ T) _ f₁).2.2.1 _ h2 h1
    rw [← e]
    exact mem _
  · intro k hk f hf f₁ h1
    obtain ⟨T, rfl⟩ := pol f hf
    obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.RealLift.exists_line_of_upq F E σ (Fin a) _ _
      B.emb (incM F G.V.J) 1 A G.V.θ hb.cm hA1 hAθ k hk.1 hk.2
    obtain ⟨U, -, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F _ _ Φ _ ((om.comp (MonoidHom.inl _ _)).comp γ)
      (GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w => locFin_fock1 _ _ _ _ (Yg w) (hKC w) _) (fun t l hl => hadm _ l hl)
      (fun T => hW1 γ hγ Yg hgen T)
    have h2 := (hL F _ (Φ T) (Φ (U T)) f₁).2.1 _ (map_zero _) (hSA T)
    change Acts _ (om (MonoidHom.inl _ _ (γ (Multiplicative.ofAdd 1)))) _ _ at h2
    rw [hγ1] at h2
    have e := (hL F _ (Φ T) _ f₁).2.2.2.1 _ h2 h1
    rw [← e]
    exact mem _
  · intro γ hγ f hf
    obtain ⟨T, rfl⟩ := pol f hf
    obtain ⟨Yg, -, hY⟩ := GlobalTheory.T.oneParamSubgroup_generators_exist F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C hb.cm hC1 γ hγ
    have h2 := (hL F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) (hW2 γ hγ Yg hY T)
    exact ⟨_, mem _, h2, fun f₂ h3 => (hL F _ (Φ T) _ _).2.2.1 _ h3 h2⟩
  · intro k hk f hf
    obtain ⟨T, rfl⟩ := pol f hf
    obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.RealLift.exists_line_of_upq F E σ
      (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C G.W.θ hb.cm hC1 hCθ k hk.1 hk.2
    obtain ⟨U, -, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F _ _ Φ _ ((om.comp (MonoidHom.inr _ _)).comp γ)
      (GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w => locFin_fock2 _ _ _ _ (Yg w) (hKC w) _) (fun t l hl => hadm _ l hl)
      (fun T => hW2 γ hγ Yg hgen T)
    have h2 := (hL F _ (Φ T) (Φ (U T)) (Φ (U T))).2.1 _ (map_zero _) (hSA T)
    change Acts _ (om (MonoidHom.inr _ _ (γ (Multiplicative.ofAdd 1)))) _ _ at h2
    rw [hγ1] at h2
    exact ⟨_, mem _, h2, fun f₂ h3 => (hL F _ (Φ T) _ _).2.2.2.1 _ h3 h2⟩

end GlobalTheory.PolStabInf

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumPureLineDifferentiable

section

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.ThetaLinePureW
theorem hasDerivAt_thetaSum_pure_weight : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
    ∀ φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → ∀ u : Matrix (Fin a) (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ))) 0 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' h γ hγ f _ f₁ hD φ hφ hv u
  have H := _root_.GlobalTheory.T.theta_sum_differentiable_along_line hP G.M B.ψ X.β (X.β / X.α) om h.base.cm h.base.std h.geo.hM h.weil γ hγ 1 (fun _ => f) (fun _ => f₁)
    (fun _ => φ) (fun _ => ⟨hφ, hv⟩) (fun _ => hD) u
  simpa using H
end GlobalTheory.ThetaLinePureW
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.thetaSum_pure_line_differentiable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
    ∀ φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → ∀ u : Matrix (Fin a) (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ))) 0 := by
  first | exact @_root_.GlobalTheory.ThetaLinePureW.hasDerivAt_thetaSum_pure_weight | exact _root_.GlobalTheory.ThetaLinePureW.hasDerivAt_thetaSum_pure_weight | (intros; apply _root_.GlobalTheory.ThetaLinePureW.hasDerivAt_thetaSum_pure_weight <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilLieAlgebraActionByLineDerivatives

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.MaxLie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.RealLift Formalism.BasicNotions.TH
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem exists_derivation_action_weil (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om') :
    ∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ := by
  obtain ⟨hb, hg, hc, hw, -⟩ := h
  choose A hA hAθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [GlobalTheory.PolStabInf.incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [GlobalTheory.PolStabInf.incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hD := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hD
  have hfe := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hD
  have hsec := _root_.GlobalTheory.T.real_lift_lie_second_order hPr hD hfe hvl (_root_.GlobalTheory.T.weil_lie_algebra_scalar_action hPr hD hvl)
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hD hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr
    hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1
    hc.expβ
  have hL := GlobalTheory.RealLift.actsLaws
  have mem : ∀ T, Φ T ∈ G.M.Pol B.ψ B.emb := fun T => hr ▸ LinearMap.mem_range_self Φ T
  intro γ hγ f hf
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  obtain ⟨Yg, -, hY⟩ := GlobalTheory.T.oneParamSubgroup_generators_exist F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C hb.cm hC1 γ hγ
  have h2 := (hL F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) (hW2 γ hγ Yg hY T)
  exact ⟨_, mem _, h2⟩
theorem thetaSum_weil_hasDerivAt (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om')
    (γ : Multiplicative ℝ →* UA σ G.W.J) (hγ : γ ∈ Lines σ G.W) (f : SInf F (Fin a × Fin (a + a')))
    (hf : f ∈ G.M.Pol B.ψ B.emb) (f₁ : SInf F (Fin a × Fin (a + a')))
    (hA : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hev : ∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) (u : Matrix (Fin a) (Fin (a + a')) (AE F E)) :
    HasDerivAt (fun t : ℝ => thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (pure f φ))))
      (thetaSum F (G.M.co.rho B.ψ u (pure f₁ φ))) 0 :=
  _root_.GlobalTheory.T.thetaSum_pure_line_differentiable hPr F E σ B a a' G X om om' h γ hγ f hf f₁ hA φ hSB hev u
theorem exists_line_derivative_maxLie (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om')
    (γ : Multiplicative ℝ →* UA σ G.W.J) (hγ : γ ∈ Lines σ G.W) :
    ∀ Φ ∈ algD G.M B.ψ B.emb, ∃ Ψ ∈ algD G.M B.ψ B.emb,
      (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Ψ x) 0) ∧
      ∀ u, HasDerivAt (fun t : ℝ => thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) Φ)))
        (thetaSum F (G.M.co.rho B.ψ u Ψ)) 0 := by
  have hψ : IsStd B.ψ := h.base.std
  have hM := h.geo.hM
  have hsch : ∀ p, ∀ Φ ∈ schA F (Fin a × Fin (a + a')), om p Φ ∈ schA F (Fin a × Fin (a + a')) :=
    fun p Φ hΦ => (IsUWeilPair.isUSplitting h.weil).pres p Φ hΦ
  have hAD := GlobalTheory.SquareAgree.HeisDeriv.algD_le_schA G.M B.ψ B.emb hM
  have hrs : ∀ u, ∀ Φ ∈ schA F (Fin a × Fin (a + a')), G.M.co.rho B.ψ u Φ ∈ schA F (Fin a × Fin (a + a')) :=
    fun u Φ hΦ => GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hψ u Φ hΦ
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, zero_mem _, fun x => ?_, fun u => ?_⟩
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    · simp only [map_zero, GlobalTheory.SquareAgree.CoinvPass.rho_zero']
      simpa [thetaSum] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add a₁ b₁ ha₁ hb₁ ha hb =>
    obtain ⟨a₂, ha₂, hpa, hta⟩ := ha
    obtain ⟨b₂, hb₂, hpb, htb⟩ := hb
    refine ⟨a₂ + b₂, add_mem ha₂ hb₂, fun x => ?_, fun u => ?_⟩
    · simp only [map_add (f := _), Pi.add_apply]
      exact (hpa x).add (hpb x)
    · have e : (fun t : ℝ => thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (a₁ + b₁)))) =
          fun t => thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) a₁)) +
            thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) b₁)) := by
        funext t
        rw [map_add (f := _), GlobalTheory.SquareAgree.CoinvPass.rho_add', thetaSum_add F (hrs u _ (hsch _ _ (hAD ha₁)))
          (hrs u _ (hsch _ _ (hAD hb₁)))]
      rw [e, GlobalTheory.SquareAgree.CoinvPass.rho_add', thetaSum_add F (hrs u _ (hAD ha₂)) (hrs u _ (hAD hb₂))]
      exact (hta u).add (htb u)
  | smul c a₁ ha₁ ha =>
    obtain ⟨a₂, ha₂, hpa, hta⟩ := ha
    refine ⟨c • a₂, Submodule.smul_mem _ c ha₂, fun x => ?_, fun u => ?_⟩
    · simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      exact (hpa x).const_mul c
    · simp only [map_smul, GlobalTheory.SquareAgree.CoinvPass.rho_smul', GlobalTheory.SquareAgree.HeisDeriv.thetaSum_smul]
      exact (hta u).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hf, hSB, hev, rfl⟩ := hΦ
    obtain ⟨f₁, hf₁, hA⟩ := _root_.GlobalTheory.SquareAgree.MaxLie.exists_derivation_action_weil hPr h γ hγ f hf
    have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hev.and hM.std).mono fun v hv => hv.1.trans hv.2
    refine ⟨pure f₁ φ, Submodule.subset_span ⟨f₁, φ, hf₁, hSB, hev, rfl⟩, fun x => ?_, fun u => ?_⟩
    · exact hA _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd) x
    · exact _root_.GlobalTheory.SquareAgree.MaxLie.thetaSum_weil_hasDerivAt hPr h γ hγ f hf f₁ hA φ hSB hev u
end Gen
theorem maximal_lie_subalgebra_acts : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N, GlobalTheory.CoinvKer.IsStabW om Bs.emb (algD Γ.M Bs.ψ Bs.emb) N → ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ N, ∀ Φ,
    IsDatum Γ.M ψ cA ΦD Φ → ∃ Φ₁D ∈ N, ∃ Φ₁ ∈ algF ψ θ true A B, IsDatum Γ.M ψ cA Φ₁D Φ₁ ∧
      IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ₁ := by
  intro hPr D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ _hTr hO hT Pi rf rl p p' _hm N hN τ Y hY
    ΦD hΦD Φ hD
  have hψB := hO.psi
  subst hψB
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hO.JX
  obtain ⟨Ψ, hΨ, hpt, hth⟩ := _root_.GlobalTheory.SquareAgree.MaxLie.exists_line_derivative_maxLie hPr hT γ hγ ΦD (hN.1 hΦD)
  have hΨN : Ψ ∈ N := hN.2.2.2 γ hγ ΦD hΦD Ψ hΨ hpt
  obtain ⟨Φ₁, hΦ₁, hD₁⟩ := hO.algA' Ψ hΨ
  refine ⟨Ψ, hΨN, Φ₁, hΦ₁, hD₁, fun z => ?_⟩
  obtain ⟨u, rfl⟩ := cA.surjective z
  have key : (fun t : ℝ => ωA (1, oneP θ X τ Y t) Φ (cA u)) =
      fun t => thetaSum D.host.F (Γ.M.co.rho Bs.ψ u (om (1, γ (Multiplicative.ofAdd t)) ΦD)) := by
    funext t
    have k := (hO.weilA ΦD Φ hD 1 (oneP θ X τ Y t)).2 u
    rw [GlobalTheory.LocWeilAct.conjU_one', ← hγt t] at k
    exact k.symm
  show HasDerivAt (fun t : ℝ => ωA (1, oneP θ X τ Y t) Φ (cA u)) (Φ₁ (cA u)) 0
  rw [key, ← hD₁.2 u]
  exact hth u
end GlobalTheory.SquareAgree.MaxLie
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.weil_lie_algebra_action_by_line_derivatives : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N, GlobalTheory.CoinvKer.IsStabW om Bs.emb (algD Γ.M Bs.ψ Bs.emb) N → ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ N, ∀ Φ,
    IsDatum Γ.M ψ cA ΦD Φ → ∃ Φ₁D ∈ N, ∃ Φ₁ ∈ algF ψ θ true A B, IsDatum Γ.M ψ cA Φ₁D Φ₁ ∧
      IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ₁ := by
  first | exact @_root_.GlobalTheory.SquareAgree.MaxLie.maximal_lie_subalgebra_acts | exact _root_.GlobalTheory.SquareAgree.MaxLie.maximal_lie_subalgebra_acts | (intros; apply _root_.GlobalTheory.SquareAgree.MaxLie.maximal_lie_subalgebra_acts <;> assumption)
end
end
end
