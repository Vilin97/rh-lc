module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFockStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKRatInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {n m : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) :
    ResEtaPow K (χ / χ') (n + m) := by
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x]
  split_ifs
  · simp
  · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg_one]

theorem isHecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') := by
  refine ⟨?_, fun x => ?_⟩
  · show Continuous fun x => χ x / χ' x
    exact h.1.div' h'.1
  · rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

end GlobalTheory.ThKRatInv
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SquareAgreeStabilizerCompactWeyl

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
namespace GlobalTheory.SquareAgree.StabKW
theorem stabilizer_compact_weyl_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.W Bs.emb, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, om (1, k) ΦD ∈ algD Γ.M Bs.ψ Bs.emb := by
  intro _hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _hθ _hTr _hO hT Pi rf rl p p' _hm k hk ΦD hΦD
  have hdet : Γ.V.J.det ≠ 0 ∧ Γ.W.J.det ≠ 0 :=
    ⟨GlobalTheory.FinUniq.det_ne_zero_herm hT.geo.hV, GlobalTheory.FinUniq.det_ne_zero_skew hT.geo.hW⟩
  have key := GlobalTheory.T.compactUnitary_preserves_polynomialFock D.host.F D.host.E D.sp.cm.sig hT.base.cm W.rank (W.rank + W₁.rank) Γ.V Γ.W Γ.M Bs.ψ Xc.β
    (Xc.β / Xc.α) om hT.base.std hT.geo.hV.herm hdet.1 hT.geo.hW.skew hdet.2 hT.chars.resβ
    (GlobalTheory.ThKRatInv.resEtaPow_div hT.chars.resβ hT.chars.resα) hT.chars.heckeβ
    (GlobalTheory.ThKRatInv.isHecke_div hT.chars.heckeβ hT.chars.heckeα) hT.weil Bs.emb hT.geo.hV.cartan hT.geo.hW.cartan k hk
  have hgen : {Φ | ∃ f φ, f ∈ Γ.M.Pol Bs.ψ Bs.emb ∧ (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) ∧
      (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) ∧ Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ} ⊆
      ((algD Γ.M Bs.ψ Bs.emb).comap (om (1, k)) : Set _) := by
    rintro _ ⟨f, φ, hf, hSB, hcof, rfl⟩
    obtain ⟨⟨f₁, hf₁⟩, hpol⟩ := key f hf
    have hstd : ∀ᶠ v in Filter.cofinite,
        φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1 :=
      (hcof.and hT.geo.hM.std).mono fun v hv => hv.1.trans hv.2
    have hrest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑f) (GlobalTheory.EvZeroInf.finPart φ) :=
      ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add φ x z hz, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    have h := hf₁ _ hrest
    rw [← GlobalTheory.EvZeroInf.pure_eq_tens, ← GlobalTheory.EvZeroInf.pure_eq_tens] at h
    show om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ algD Γ.M Bs.ψ Bs.emb
    rw [h]
    exact Submodule.subset_span ⟨f₁, φ, hpol f₁ hf₁, hSB, hcof, rfl⟩
  exact (Submodule.span_le.2 hgen) hΦD
end GlobalTheory.SquareAgree.StabKW
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

theorem _root_.GlobalTheory.T.square_agree_stabilizer_compact_weyl : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.W Bs.emb, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, om (1, k) ΦD ∈ algD Γ.M Bs.ψ Bs.emb := by
  first | exact @_root_.GlobalTheory.SquareAgree.StabKW.stabilizer_compact_weyl_eq | exact _root_.GlobalTheory.SquareAgree.StabKW.stabilizer_compact_weyl_eq | (intros; apply _root_.GlobalTheory.SquareAgree.StabKW.stabilizer_compact_weyl_eq <;> assumption)
end
end
end
