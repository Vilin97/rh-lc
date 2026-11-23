module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKerPD
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposesStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LineSumDerivationFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationPairDerivation
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumDifferentiableAlongLine

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingAdelicVolume

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SquareAgree.LineDerFunB

theorem exists_sum_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) {Φ : (Fin n × Fin d → AF F) → ℂ}
    (hΦ : Φ ∈ algD M ψ emb) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) ∧
      Φ = ∑ i, pure (f i) (φ i) := by
  rw [algD, Submodule.mem_span_set'] at hΦ
  obtain ⟨m, c, g, rfl⟩ := hΦ
  choose f φ hf hφ hv hg using fun i => (g i).2
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hv i⟩, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hg i]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]

theorem conjU_one {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (h : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c h 1 = 1 := by
  apply Subtype.ext
  simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]

end GlobalTheory.SquareAgree.LineDerFunB


end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SquareAgreeLineDerivationIsDerivation

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
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.SquareAgree.LineDerFunB
end GlobalTheory.SquareAgree.LineDerFunB
open GlobalTheory.SquareAgree.LineDerFunB in
theorem GlobalTheory.SquareAgree.LineDerFunB.lineDerivation_isDerivation_of_datum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ Ψ ∈ algD Γ.M' Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hO.JX (oneP θ X τ Y t)) ΦD x) (Ψ x) 0) → ∀ Φ Φ',
    IsDatum Γ.M' ψ cB ΦD Φ → IsDatum Γ.M' ψ cB Ψ Φ' → IsDer θ X (fun h => ωB (1, h)) τ Y Φ Φ' := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ _ hO hT τ Y hY ΦD hΦD Ψ hΨ hD Φ Φ'
    hDat hDat'
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hO.JX
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.T.twist_lie_derivative_model hP Bs Γ Xc om om' hT γ hγ
  obtain ⟨m, f, φ, hf, rfl⟩ := exists_sum_pure Γ.M' Bs.ψ Bs.emb hΦD
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers D.host.F} 1 :=
    fun i => ((hf i).2.2.and hT.geo.hM'.std).mono fun v h => h.1.trans h.2
  have hder : ∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x)
      ((∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ (f i)) (φ i)) x) 0 := by
    intro x
    have e1 : (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x) =
        fun t => ∑ i, om' (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x := by
      funext t

      rw [map_sum, Finset.sum_apply]
    rw [e1, Finset.sum_apply]
    exact HasDerivAt.fun_sum fun i _ =>
      (hδ _ (hf i).1).2 _ (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hf i).2.1 (hstd i)) x
  have hΨe : Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ (f i)) (φ i) := by
    funext x
    have h1 := hD x
    simp only [← hγt] at h1
    exact h1.unique (hder x)
  intro z
  obtain ⟨u, rfl⟩ := cB.surjective z
  have hs : IsStd ψ := hO.psi ▸ hT.base.std
  have hg : Γ.M'.IsGood ψ := hO.psi ▸ hT.geo.hM'
  have hw : Γ.M'.IsWeil ψ Xc.α (Xc.α / Xc.β) om' := hO.psi ▸ hT.weil'
  have key := _root_.GlobalTheory.T.theta_sum_differentiable_along_line hP Γ.M' ψ Xc.α (Xc.α / Xc.β) om' hT.base.cm hs hg hw γ hγ m f (fun i => δ (f i)) φ
    (fun i => (hf i).2) (fun i => (hδ _ (hf i).1).2) u
  have e2 : (fun t : ℝ => ωB (1, oneP θ X τ Y t) Φ (cB u)) = fun t : ℝ =>
      GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho ψ u (om' (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))) := by
    funext t
    have h1 := (hO.weilB _ Φ hDat 1 (oneP θ X τ Y t)).2 u
    rw [conjU_one, ← hγt t] at h1
    exact h1.symm
  rw [e2, ← hDat'.2 u, hΨe]
  exact key
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

theorem _root_.GlobalTheory.T.squareAgree_lineDerivation_isDerivation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∀ Ψ ∈ algD Γ.M' Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hO.JX (oneP θ X τ Y t)) ΦD x) (Ψ x) 0) → ∀ Φ Φ',
    IsDatum Γ.M' ψ cB ΦD Φ → IsDatum Γ.M' ψ cB Ψ Φ' → IsDer θ X (fun h => ωB (1, h)) τ Y Φ Φ' := by
  first | exact @_root_.GlobalTheory.SquareAgree.LineDerFunB.lineDerivation_isDerivation_of_datum | exact _root_.GlobalTheory.SquareAgree.LineDerFunB.lineDerivation_isDerivation_of_datum | (intros; apply _root_.GlobalTheory.SquareAgree.LineDerFunB.lineDerivation_isDerivation_of_datum <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KerPolarizationProjectionStableUnderStabilizerLi

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
theorem GlobalTheory.SquareAgree.ker_polarizationProjection_stabilizer_lie : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W, ∀ Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p', ∀ Φ₁ ∈ algD Γ.M' Bs.ψ Bs.emb, (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hm γ hγ
    ΦD hΦD Φ₁D hΦ₁D hder
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  obtain ⟨-, Φ, hΦF, hD, hp⟩ := (mem_kerPD hψ θ A₁ B Bs Γ cB p' ΦD).1 hΦD
  have hΦD' : ΦD ∈ algD Γ.M' Bs.ψ Bs.emb := ((mem_kerPD hψ θ A₁ B Bs Γ cB p' ΦD).1 hΦD).1
  obtain ⟨l, hl, hγl⟩ := GlobalTheory.T.oneParamSubgroup_transposeGramUnitary_decomposes D θ X e Γ.W hO.JX hθ γ hγ
  have hder' : ∀ x, HasDerivAt (fun t : ℝ => om' (1, kapX X e hO.JX ((l.map fun q => oneP θ X q.1 q.2 t).prod)) ΦD x)
      (Φ₁D x) 0 := by
    intro x; have := hder x; simp only [hγl] at this; exact this
  obtain ⟨Ψ, hΨ, hsum⟩ := _root_.GlobalTheory.T.lineSum_derivation_formula hP D θ X e Bs Γ Xc om om' hO.JX hθ hT l hl ΦD hΦD' Φ₁D hder'
  choose Φ' hΦ'F hΦ'D using fun i => hO.algB' (Ψ i) (hΨ i).1
  obtain ⟨Φ₁, hΦ₁F, hD₁⟩ := hO.algB' Φ₁D hΦ₁D
  refine (mem_kerPD hψ θ A₁ B Bs Γ cB p' Φ₁D).2 ⟨hΦ₁D, Φ₁, hΦ₁F, hD₁, ?_⟩
  have hsumD : ∀ s : Finset (Fin l.length), IsDatum Γ.M' ψ cB (∑ i ∈ s, Ψ i) (∑ i ∈ s, Φ' i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (CoinvPass.isDatum_zero (M := Γ.M') (ψ := ψ) (crd := cB))
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact CoinvPass.isDatum_add hψ (hΦ'D a) ih
  have hΦ₁ : Φ₁ = ∑ i, Φ' i := IsDatum.fun_eq Γ.M' ψ cB cB.surjective hD₁ (hsum ▸ hsumD Finset.univ)

  rw [hΦ₁, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi := hl _ (List.get_mem l i)
  rw [hm.mapB.eql _ _ hi Φ hΦF (Φ' i) (hΦ'F i)
    (_root_.GlobalTheory.T.squareAgree_lineDerivation_isDerivation hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT _ _ hi ΦD hΦD' (Ψ i) (hΨ i).1
      (hΨ i).2 Φ (Φ' i) hD (hΦ'D i)), hp, map_zero]
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

theorem _root_.GlobalTheory.T.ker_polarizationProjection_stable_under_stabilizer_lie : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.W, ∀ Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p', ∀ Φ₁ ∈ algD Γ.M' Bs.ψ Bs.emb, (∀ x, HasDerivAt (fun t : ℝ => om' (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  first | exact @_root_.GlobalTheory.SquareAgree.ker_polarizationProjection_stabilizer_lie | exact _root_.GlobalTheory.SquareAgree.ker_polarizationProjection_stabilizer_lie | (intros; apply _root_.GlobalTheory.SquareAgree.ker_polarizationProjection_stabilizer_lie <;> assumption)
end
end
end
