module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAutLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalHeckeOperatorEqSmulOfLocalParameter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitarySatakeInvariantAntidiagTransport
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryAutFormEqZeroOfFinitePoints
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCanonicalInertTensorCompletionEquivStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Formalism.AlgebraicWeights.InertDatumExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorThroughFrameEvalFinitePoints
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeTransformInvariantUnderFieldAutomorphismStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntidiagTransportCompMemSphericalHecke

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.SatInd

theorem guMap_comp_mem_hecke : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ Formalism.UG.intL K ↔ g x ∈ Formalism.UG.intL K) → ∀ (n : ℕ) (h : Formalism.UG.GU σ' n → ℂ), h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ' n) → (fun y => h (GlobalTheory.SatInd.guMap g hg n y)) ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) := by
  intro K _ _ g σ σ' hg hint n h hh
  have hg' : ∀ x, g.symm (σ' x) = σ (g.symm x) := by
    intro x
    apply g.injective
    rw [hg]
    simp
  let e : Formalism.UG.GU σ n ≃* Formalism.UG.GU σ' n :=
    { toFun := guMap g hg n
      invFun := guMap g.symm hg' n
      left_inv := fun y => guMap_symm_comp g hg hg' y
      right_inv := fun y => by
        have := guMap_symm_comp g.symm hg' (by simpa using hg) y
        simpa using this
      map_mul' := map_mul _ }
  have hK : ∀ y, y ∈ Formalism.UG.KU σ' n ↔ e.symm y ∈ Formalism.UG.KU σ n := by
    intro y
    rw [mem_KU_iff_guMap g hg hint (e.symm y)]
    change y ∈ Formalism.UG.KU σ' n ↔ e (e.symm y) ∈ Formalism.UG.KU σ' n
    rw [MulEquiv.apply_symm_apply]
  have := GlobalTheory.LFun.EigLoc.comp_symm_mem_hecke e.symm hK hh
  exact this

end GlobalTheory.SatInd
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntidiagTransportCompMemSphericalHeckeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.antidiagTransport_comp_mem_sphericalHecke : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ Formalism.UG.intL K ↔ g x ∈ Formalism.UG.intL K) → ∀ (n : ℕ) (h : Formalism.UG.GU σ' n → ℂ), h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ' n) → (fun y => h (GlobalTheory.SatInd.guMap g hg n y)) ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) := by
  first | exact @GlobalTheory.SatInd.guMap_comp_mem_hecke | exact GlobalTheory.SatInd.guMap_comp_mem_hecke | (intros; apply GlobalTheory.SatInd.guMap_comp_mem_hecke <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByUnitaryIntegralPointsOfLevelFixed

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.UnramDict

theorem fixed_of_mem_KU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ U0 : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U0 ↔ κ ∈ Umax L n)) → ∀ (σ : w.adicCompletion L →+* w.adicCompletion L) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU σ n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∀ φ ∈ U, (∀ g, ∀ κ ∈ U0, φ (F.j (g * κ)) = φ (F.j g)) → ∀ x : locU n w, p x ∈ Formalism.UG.KU σ n → RU L n x.val φ = φ := by
  intro L _ _ _ n F U hU v w hw U0 hU0 σ b hb p hp φ hφU hfix x hK
  obtain rfl : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hw
  have hK1 : (p x).val ∈ GlobalTheory.LFun.KGL w (n := n) := (Subgroup.mem_subgroupOf.1 hK).2
  have hK2 : cLoc w x.val ∈ GlobalTheory.LFun.KGL w (n := n) := by
    have h : cLoc w x.val = b * (p x).val * b⁻¹ := by rw [hp]; group
    rw [h]
    exact mul_mem (mul_mem hb hK1) (inv_mem hb)
  have hx := x.2
  obtain ⟨y, hy⟩ := F.onto x.val (Subgroup.mem_inf.1 hx).1
  have hyU : y ∈ Umax L n := fun i j => mem_ALint F _ fun u => by
    rw [← F.loc, hy]
    exact cLoc_entry_mem hx hK2 u i j
  have hk (a : L) (z : AFplus L) :
      F.κ.toRingHom (a ⊗ₜ[maximalRealSubfield L] z) =
        algebraMap L _ a * GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L z := by
    have h1 (z : AFplus L) : F.κ (1 ⊗ₜ z) =
        GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L z := by
      refine FiniteAdeleRing.ext _ fun q => ?_
      obtain ⟨i, hi, hia⟩ := F.right q (q.under (𝓞 (maximalRealSubfield L))) rfl
      rw [hia]
      change i (z (q.under (𝓞 (maximalRealSubfield L)))) = GlobalTheory.LFun.complMap rfl (z (q.under (𝓞 (maximalRealSubfield L))))
      refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L)
        (q.under (𝓞 (maximalRealSubfield L)))).equalizer hi
        (GlobalTheory.LFun.InertChart.continuous_complMap rfl) (funext fun k => ?_)) _
      change i (algebraMap _ _ k) = GlobalTheory.LFun.complMap rfl (algebraMap _ _ k)
      rw [GlobalTheory.LFun.complMap_algebraMap]
      have he : (algebraMap (maximalRealSubfield L) (AFplus L) k) (q.under (𝓞 (maximalRealSubfield L))) =
          algebraMap _ (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) (q.under (𝓞 (maximalRealSubfield L)))) k := rfl
      rw [← he, ← hia, Algebra.algebraMap_eq_smul_one (A := AFplus L) k, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, F.left]
      rfl
    rw [← h1, ← F.left, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  have hc (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (z : AL L)
      (hz : ∀ u : HeightOneSpectrum (𝓞 L), u.under (𝓞 (maximalRealSubfield L)) = v → F.κ z u = 0) :
      compAt L v z = 0 :=
    (GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (ι := F.κ.toRingHom) hk v z).2 hz
  have hyt : TrivOutside {w.under (𝓞 (maximalRealSubfield L))} y := by
    intro v hv
    refine Matrix.ext fun i j => ?_
    have h0 := hc v (y.1.val i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) fun u hu => by
      have h := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u)
        (fun e => hv (hu.symm.trans e)))
      have h1 := F.loc y u i j
      rw [hy, h] at h1
      rw [map_sub]
      change F.κ _ u - F.κ _ u = 0
      rw [← h1]
      simp only [Units.val_one, Matrix.one_apply]
      split_ifs <;> simp <;> rfl
    rw [map_sub, sub_eq_zero] at h0
    rw [Matrix.map_apply, h0]
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have hy0 : y ∈ U0 := (hU0 y hyt).2 hyU
  rw [← sub_eq_zero]
  refine GlobalTheory.DefiniteDense.eq_zero_of_finU L n _ (hU.aut _ (U.sub_mem (hU.stable _ _ hφU) hφU)) fun z hz => ?_
  obtain ⟨g, rfl⟩ := F.onto z hz
  change φ (F.j g * x.val) - φ (F.j g) = 0
  rw [← hy, ← map_mul, sub_eq_zero]
  exact hfix g y hy0

end GlobalTheory.UnramDict

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByUnitaryIntegralPointsOfLevelFixedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.fixed_by_unitaryIntegralPoints_of_level_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ U0 : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U0 ↔ κ ∈ Umax L n)) → ∀ (σ : w.adicCompletion L →+* w.adicCompletion L) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU σ n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∀ φ ∈ U, (∀ g, ∀ κ ∈ U0, φ (F.j (g * κ)) = φ (F.j g)) → ∀ x : locU n w, p x ∈ Formalism.UG.KU σ n → RU L n x.val φ = φ := by
  first | exact @GlobalTheory.UnramDict.fixed_of_mem_KU | exact GlobalTheory.UnramDict.fixed_of_mem_KU | (intros; apply GlobalTheory.UnramDict.fixed_of_mem_KU <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorThroughFrameEvalFinitePointsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.inertHeckeOperator_through_frame_eval_finitePoints : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (D : InertDatum L n v w) (U0 : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U0 ↔ κ ∈ Umax L n)) → ∀ (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU D.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → (∀ y, D.loc y = b⁻¹ * cLoc w (F.j y) * b) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU D.σw n), ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U0, NG.rt L n κ f = f) → ∀ (lam : W →ₗ[ℂ] ℂ) (φ : UA L n → ℂ), (∀ g, φ (F.j g) = lam (f g)) → ∀ g, GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU D.σw n).comap p) (fun x => h (p x)) φ (F.j g) = lam (heckeFunI L n U0 D h f g) := by
  first | exact @GlobalTheory.InertTransfer.heckeVec_frame_eval | exact GlobalTheory.InertTransfer.heckeVec_frame_eval | (intros; apply GlobalTheory.InertTransfer.heckeVec_frame_eval <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftSatakeVectorLocalHeckeEigen

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

theorem GlobalTheory.InertHeckeTransfer.exists_lift_eigen : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → ∀ (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → Formalism.UG.cT Dv.σw b.val * b.val = Formalism.UG.antiJ (w.adicCompletion L) n → ∀ p : locU n w →* Formalism.UG.GU Dv.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∃ φ ∈ U, φ ≠ 0 ∧ (∀ x : locU n w, p x ∈ Formalism.UG.KU Dv.σw n → RU L n x.val φ = φ) ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU Dv.σw n).comap p) (fun x => h (p x)) φ = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • φ := by
  intro L _ _ _ n F π U hD v w hw Dv α hα hs b hbK hbJ p hp
  obtain ⟨f, hfS, hf0, U0, hfixU0, hU0, heig⟩ := hα
  obtain ⟨g0, hg0⟩ : ∃ g0, f g0 ≠ 0 := Function.ne_iff.1 hf0
  obtain ⟨lam, hlam⟩ : ∃ lam : Module.Dual ℂ π.W, lam (f g0) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hg0 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  have hmem : (fun x => lam (f x)) ∈ U.map (LinearMap.funLeft ℂ ℂ F.j) := by
    rw [hD.2]
    exact Submodule.subset_span ⟨f, hfS, lam, rfl⟩
  obtain ⟨φ, hφU, hφ⟩ := hmem
  have hφ' : ∀ g, φ (F.j g) = lam (f g) := fun g => congrFun hφ g
  have hfU : ∀ g, ∀ κ ∈ U0, f (g * κ) = f g := fun g κ hκ => congrFun (hfixU0 κ hκ) g
  refine ⟨φ, hφU, fun h => hlam ?_, GlobalTheory.T.fixed_by_unitaryIntegralPoints_of_level_fixed L n F U hD.1 v w hw U0 hU0 Dv.σw b hbK p hp φ hφU
    (fun g κ hκ => by rw [hφ', hφ', hfU g κ hκ]), fun h hh => ?_⟩
  · rw [← hφ', h]; rfl
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.exists_canonical_inert_tensor_completion_equiv L n F v w hw Dv hs
  have hbP : b ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL (w.adicCompletion L)).subtype).range := hbK
  let D0 : InertDatum L n v w := ⟨e, Dv.σw, Dv.ϖ, b, he1, Dv.unram, he2, hbP, hbJ⟩
  have hloc : ∀ y, D0.loc y = b⁻¹ * cLoc w (F.j y) * b := by
    intro y
    show b⁻¹ * _ * b = _
    congr 2
    refine Units.ext (Matrix.ext fun s t => ?_)
    rw [F.loc]
    exact he3 _
  have hbi := hh.1
  have hh' := GlobalTheory.T.antidiagTransport_comp_mem_sphericalHecke (GlobalTheory.SatInd.gEquiv Dv D0) (GlobalTheory.SatInd.gEquiv_comm Dv D0) (GlobalTheory.SatInd.gEquiv_intL Dv D0) n h hh
  have heig0 : heckeFunI L n U0 D0 h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f := by
    rw [GlobalTheory.SatInd.heckeFunI_indepDatum L n v w Dv D0 U0 π.W h hbi f, heig _ hh',
      GlobalTheory.T.satakeTransform_invariant_under_field_automorphism (GlobalTheory.SatInd.gEquiv Dv D0) (GlobalTheory.SatInd.gEquiv_comm Dv D0) (GlobalTheory.SatInd.gEquiv_intL Dv D0) Dv.ϖ _ n (n / 2)
        Dv.unram (by omega) (by omega) h hbi α]
  have htr := GlobalTheory.T.inertHeckeOperator_through_frame_eval_finitePoints L n F v w hw D0 U0 hU0 b hbK p hp hloc h hh π.W f hfixU0 lam φ hφ'
  have hvecU : GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU Dv.σw n).comap p) (fun x => h (p x)) φ ∈ U := by
    unfold GlobalTheory.LFun.heckeVec
    by_cases hfin : (Function.support fun c : (locU n w) ⧸ ((Formalism.UG.KU Dv.σw n).comap p) =>
        h (p c.out) • ((RU L n).comp (locU n w).subtype) c.out φ).Finite
    · rw [finsum_eq_sum _ hfin]
      exact U.sum_mem fun c _ => U.smul_mem _ (hD.1.stable _ _ hφU)
    · rw [finsum_of_infinite_support hfin]
      exact U.zero_mem
  rw [← sub_eq_zero]
  refine GlobalTheory.DefiniteDense.eq_zero_of_finU L n _ (hD.1.aut _ (U.sub_mem hvecU (U.smul_mem _ hφU))) fun z hz => ?_
  obtain ⟨g, rfl⟩ := F.onto z hz
  rw [Pi.sub_apply, Pi.smul_apply, htr g, heig0, hφ', Pi.smul_apply, map_smul, smul_eq_mul, sub_self]

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftSatakeVectorLocalHeckeEigenStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_lift_satake_vector_local_hecke_eigen : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → ∀ (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → Formalism.UG.cT Dv.σw b.val * b.val = Formalism.UG.antiJ (w.adicCompletion L) n → ∀ p : locU n w →* Formalism.UG.GU Dv.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∃ φ ∈ U, φ ≠ 0 ∧ (∀ x : locU n w, p x ∈ Formalism.UG.KU Dv.σw n → RU L n x.val φ = φ) ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU Dv.σw n).comap p) (fun x => h (p x)) φ = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • φ := by
  first | exact @GlobalTheory.InertHeckeTransfer.exists_lift_eigen | exact GlobalTheory.InertHeckeTransfer.exists_lift_eigen | (intros; apply GlobalTheory.InertHeckeTransfer.exists_lift_eigen <;> assumption)
end
end
