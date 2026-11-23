module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightDominantIsoExistsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleWeightDescendsToPolynomialModuleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
public import Formalism.LocalToGlobal.Columns.MtAdWt
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightMatricesMatchOfCoeffSpaceIsoStatement
import Formalism.LocalToGlobal.Columns.MtAdWtIrr
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwFixEx
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwFixLine

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellWeightOfAdmissibleTwist

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section
namespace GlobalTheory.LevCmp
open Formalism.L2.DIV GlobalTheory.CoefModel

section Gen2
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem match_mtwRat (γ : GQ L n) : (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
    ((Formalism.L2.Col.mtwRat (L := L) (n := n) γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom :=
  (congrArg Units.val (Formalism.L2.Col.mtwInc_mtwRatFun γ)).symm

theorem domWeight_ext {N : ℕ} {a b : DomWeight N} (h : a.w = b.w) : a = b := by
  cases a; cases b; subst h; rfl

end Gen2


end GlobalTheory.LevCmp

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatchingMatricesOfBaseChangeRepresentation

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel

namespace GlobalTheory.BcMatch

theorem bcmatch_main : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K K' : Type} [Field K] [Field K'] (f : K →+* K') (e : K' →+* ℂ) {W₀ W W' : Type} [AddCommGroup W₀] [Module K W₀] [AddCommGroup W] [Module K' W] [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀) (ρ : Representation K' (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W'), (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b₀ : Module.Basis ι K W₀) (b₁ : Module.Basis ι K' W), ∀ γ, LinearMap.toMatrix b₁ b₁ (ρ γ) = (LinearMap.toMatrix b₀ b₀ (ρ₀ γ)).map f) → GlobalTheory.LevCmp.WtMatch (e.comp f) ρ₀ ρ' → GlobalTheory.LevCmp.WtMatch e ρ ρ' := by
  intro L _ _ _ n K K' _ _ f e W₀ W W' _ _ _ _ _ _ ρ₀ ρ ρ' hb hm
  obtain ⟨ι, _, _, b₀, b₁, hb⟩ := hb
  obtain ⟨κ, _, _, c₀, c', hc⟩ := hm
  set P : Matrix ι κ K := b₀.toMatrix c₀ with hP
  set Q : Matrix κ ι K := c₀.toMatrix b₀ with hQ
  have hPQ : P * Q = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b₀ c₀
  have hQP : Q * P = 1 := Module.Basis.toMatrix_mul_toMatrix_flip c₀ b₀
  have hPQf : P.map f * Q.map f = 1 := by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ f.map_zero f.map_one]
  have hQPf : Q.map f * P.map f = 1 := by rw [← Matrix.map_mul, hQP, Matrix.map_one _ f.map_zero f.map_one]
  let std := Pi.basisFun K' κ
  let E : (κ → K') ≃ₗ[K'] W := LinearEquiv.ofLinear (Matrix.toLin std b₁ (P.map f)) (Matrix.toLin b₁ std (Q.map f))
    (by rw [← Matrix.toLin_mul, hPQf, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, hQPf, Matrix.toLin_one])
  let d : Module.Basis κ K' W := std.map E
  have hd1 : b₁.toMatrix d = P.map f := by
    ext i j
    rw [Module.Basis.toMatrix_apply]
    have : d j = ∑ k, (P.map f) k j • b₁ k := by
      show E (std j) = _
      exact Matrix.toLin_self _ _ _ _
    rw [this, Module.Basis.repr_sum_self]
  have hd2 : d.toMatrix b₁ = Q.map f := by
    ext j i
    rw [Module.Basis.toMatrix_apply]
    simp [d, E, std, Matrix.toLin_self, Pi.single_apply]
  refine ⟨κ, inferInstance, inferInstance, d, c', fun γ => ?_⟩
  rw [hc γ, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix d b₁ d b₁ (ρ γ), hd1, hd2, hb γ,
    ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix c₀ b₀ c₀ b₀ (ρ₀ γ), ← hP, ← hQ]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.map_map]
  rfl

end GlobalTheory.BcMatch
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatchingMatricesOfBaseChangeRepresentationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel


theorem _root_.GlobalTheory.T.matchingMatrices_of_baseChange_representation : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K K' : Type} [Field K] [Field K'] (f : K →+* K') (e : K' →+* ℂ) {W₀ W W' : Type} [AddCommGroup W₀] [Module K W₀] [AddCommGroup W] [Module K' W] [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀) (ρ : Representation K' (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W'), (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b₀ : Module.Basis ι K W₀) (b₁ : Module.Basis ι K' W), ∀ γ, LinearMap.toMatrix b₁ b₁ (ρ γ) = (LinearMap.toMatrix b₀ b₀ (ρ₀ γ)).map f) → GlobalTheory.LevCmp.WtMatch (e.comp f) ρ₀ ρ' → GlobalTheory.LevCmp.WtMatch e ρ ρ' := by
  first | exact @GlobalTheory.BcMatch.bcmatch_main | exact GlobalTheory.BcMatch.bcmatch_main | (intros; apply GlobalTheory.BcMatch.bcmatch_main <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CellWeightsAdmissibleOfCmDatum

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
noncomputable section
namespace GlobalTheory.LevCmp
open Formalism.L2.DIV GlobalTheory.CoefModel
section Gen2
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Gen2

theorem cellWt_of_sideRead_of_admTw : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → CellWt (D := Dof x) (mtAt (D := Dof x) l.mt.M v j) l.b.Bs.exp b hA j e := by
  intro hN hL
  refine StepW.of_all fun K B f T w _ _ _ P x l v i b ψ hA j hTw hl hok e hSR => ?_
  have hemb : ∀ t, Formalism.L2.embT (Dof x) t = Formalism.BasicNotions.TH.tauE (Dof x) t := fun t => rfl
  have hinj : Function.Injective (Formalism.L2.embT (Dof x)) := GlobalTheory.StdRat.tauE_injective (Dof x)
  have hcm : ∀ t t', Formalism.L2.embT (Dof x) t ≠ ComplexEmbedding.conjugate (Formalism.L2.embT (Dof x) t') := by
    intro t t' h
    have h1 := (GlobalTheory.StdRat.tauE_cm (Dof x) (Formalism.L2.embT (Dof x) t')).1 ⟨t', rfl⟩
    exact h1 ⟨t, h⟩
  have hcov : ∀ σ : (Dof x).host.E →+* ℂ, ∃ t, σ = Formalism.L2.embT (Dof x) t ∨
      σ = ComplexEmbedding.conjugate (Formalism.L2.embT (Dof x) t) := by
    intro σ
    by_cases h : ∃ t, Formalism.BasicNotions.TH.tauE (Dof x) t = σ
    · obtain ⟨t, ht⟩ := h
      exact ⟨t, Or.inl ht.symm⟩
    · have h2 : ¬ ¬ ∃ t, Formalism.BasicNotions.TH.tauE (Dof x) t = ComplexEmbedding.conjugate σ :=
        fun h' => h ((GlobalTheory.StdRat.tauE_cm (Dof x) σ).2 h')
      obtain ⟨t, ht⟩ := not_not.1 h2
      refine ⟨t, Or.inr ?_⟩
      rw [hemb, ht]
      simp
  have hcj : ∀ y, NX.cE (Dof x) y = IsCMField.complexConj (Dof x).host.E y := by
    intro y
    show (Dof x).host.conj y = _
    symm
    apply (Dof x).host.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  have hke : ∀ t, (e.comp (NX.toKk (Dof x) i (T.k v))).comp (NX.kEmb (Dof x) i b t) = Formalism.L2.embT (Dof x) t := by
    intro t
    ext y
    have h1 := hSR (NX.embEL0 (Dof x) (((Dof x).host.sigmaOf ((Dof x).eTau t : (Dof x).R.GG)) y))
    refine Eq.trans ?_ (h1.trans (NX.embLL_embEL0 (Dof x) t y))
    rfl
  obtain ⟨lamC, T', hT'⟩ := GlobalTheory.T.algebraic_weight_dominant_iso_exists (Dof x).host.E (Dof x).R.nV (Dof x).what₂.Tau (Formalism.L2.embT (Dof x)) hinj hcm hcov
    (mtAt l.mt.M v j).wt
  have hT'r : ∀ γ y, T' ((mtAt l.mt.M v j).wt.ρ γ y) =
      rhoVr (Formalism.L2.embT (Dof x)) lamC (Formalism.L2.Col.mtwRat.toFun γ) (T' y) :=
    fun γ y => hT' γ _ (match_mtwRat γ) y
  have hinj' : Function.Injective (Formalism.L2.Col.mtwConj (Formalism.L2.embT (Dof x))) := by
    intro t t' h
    apply hinj
    have := congrArg ComplexEmbedding.conjugate h
    simpa [Formalism.L2.Col.mtwConj] using this
  have hcm' : ∀ t t', Formalism.L2.Col.mtwConj (Formalism.L2.embT (Dof x)) t ≠
      ComplexEmbedding.conjugate (Formalism.L2.Col.mtwConj (Formalism.L2.embT (Dof x)) t') := by
    intro t t' h
    have h2 : ComplexEmbedding.conjugate (Formalism.L2.embT (Dof x) t) = Formalism.L2.embT (Dof x) t' := by
      simpa [Formalism.L2.Col.mtwConj] using h
    exact hcm t' t (by rw [← h2])
  have hten := Formalism.L2.Col.tenIrr_of' highest_weight_fixed_exists highest_weight_fixed_line
    (Formalism.L2.embT (Dof x)) hinj hcm lamC
  have hten' := Formalism.L2.Col.tenIrr_of' highest_weight_fixed_exists highest_weight_fixed_line _ hinj' hcm' lamC
  have hiso : (Formalism.L2.Col.mtWt (Formalism.L2.embT (Dof x)) lamC hten).Iso (mtAt l.mt.M v j).wt :=
    ⟨T'.symm, fun γ y => by
      apply T'.injective
      have hs : ∀ z, T' (T'.symm z) = z := fun z => T'.apply_symm_apply z
      erw [hT'r, hs, hs]
      rfl⟩
  have hdual := GlobalTheory.WtDual.isDual_of_iso hiso (Formalism.L2.Col.mtWt_isDual _ lamC hten hten')
  have hC : ∀ t, NG.infOf (lamC t).w = NG.paramV (Dof x).R ((Dof x).hc t) j (1 / 2) := fun t =>
    l.mt.mt.wt _ j t _ _ hdual (Formalism.L2.Col.tenWt_hwAt _ hinj hcm lamC hten' t)
  have hj1 : 1 ≤ j.1 + 1 := by omega
  have hj2 : j.1 + 1 ≤ (Dof x).R.m := by omega
  choose lam0 hlam0 using fun t => l.b.Bs.exp.rhoW_hw i (j.1 + 1) b t hj1 hj2
  obtain ⟨lamK, hlamK, TK, hTK⟩ := GlobalTheory.T.irreducible_weight_descends_to_polynomial_module (Dof x).host.E (Dof x).R.nV (Dof x).what₂.Tau
    (FractionRing ((Dof x).ntw.O i)) (e.comp (NX.toKk (Dof x) i (T.k v))) (NX.kEmb (Dof x) i b)
    (by intro t t' h; beta_reduce at h; rw [hke, hke] at h; exact hinj h)
    (by intro t t'; beta_reduce; rw [hke, hke]; exact hcm t t')
    (by intro σ; beta_reduce; simp only [hke]; exact hcov σ)
    (NX.cE (Dof x)) hcj _ (l.b.Bs.exp.rhoW i (j.1 + 1) b) (l.b.Bs.exp.rhoW_irr i (j.1 + 1) b hj1 hj2) lam0 hlam0
  have hK : ∀ t, NG.infOf (lam0 t) = NG.paramV (Dof x).R ((Dof x).hc t) j (1 / 2) := by
    intro t
    rw [l.b.Bs.exp.rhoW_wt i (j.1 + 1) b t hj1 hj2 _ (lam0 t) (GlobalTheory.FitHecke.infG_etaT l.a.A.chr t) (hlam0 t)]
    congr 1
    push_cast
    ring
  have hlam : lamK = lamC := by
    funext t
    apply domWeight_ext
    apply GlobalTheory.MtRead.eq_of_infOf_eq (lamK t).anti (lamC t).anti
    rw [hlamK t, hK t, hC t]
  subst hlam
  have hTK' : ∀ γ y, TK (l.b.Bs.exp.rhoW i (j.1 + 1) b γ y) =
      rhoVr (NX.kEmb (Dof x) i b) lamK (Formalism.L2.Col.mtwRat.toFun γ) (TK y) := fun γ y => hTK γ _ (match_mtwRat γ) y
  have hfun : (fun t => (e.comp (NX.toKk (Dof x) i (T.k v))).comp (NX.kEmb (Dof x) i b t)) = Formalism.L2.embT (Dof x) :=
    funext hke
  have h1 := GlobalTheory.T.weightMatrices_match_of_coeffSpace_iso (e.comp (NX.toKk (Dof x) i (T.k v))) (NX.kEmb (Dof x) i b) lamK _ (mtAt l.mt.M v j).wt.ρ TK hTK'
    T' (by rw [hfun]; exact hT'r)
  unfold CellWt
  letI := (GlobalTheory.LevCmp.cell l.b.Bs.exp b hA j).acg
  letI := (GlobalTheory.LevCmp.cell l.b.Bs.exp b hA j).mod
  exact GlobalTheory.T.matchingMatrices_of_baseChange_representation (NX.toKk (Dof x) i (T.k v)) e (l.b.Bs.exp.rhoW i (j.1 + 1) b) (GlobalTheory.LevCmp.cell l.b.Bs.exp b hA j).ρ
    (mtAt l.mt.M v j).wt.ρ (GlobalTheory.LevCmp.cell l.b.Bs.exp b hA j).bc h1
end GlobalTheory.LevCmp
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

theorem _root_.GlobalTheory.T.cellWt_of_sideRead_of_twOK : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → CellWt (D := Dof x) (mtAt (D := Dof x) l.mt.M v j) l.b.Bs.exp b hA j e := by
  first | exact @_root_.GlobalTheory.LevCmp.cellWt_of_sideRead_of_admTw | exact _root_.GlobalTheory.LevCmp.cellWt_of_sideRead_of_admTw | (intros; apply _root_.GlobalTheory.LevCmp.cellWt_of_sideRead_of_admTw <;> assumption)
end
end
end
end
