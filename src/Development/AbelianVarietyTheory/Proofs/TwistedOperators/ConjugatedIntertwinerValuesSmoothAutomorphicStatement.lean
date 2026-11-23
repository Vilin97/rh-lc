module

public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFiniteOfHcFinite
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzProperties
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIdentificationRespectsRealFinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateIntertwinerValuesSobolevContinuousStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerEquivariantRealPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerHasColumnLevelStatement
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIntertwinerValuesSmoothAutomorphic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalFrame
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativeClosedClassBoundedByInverseLeastSizeStatement
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HeightBoundByInfinityNorm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzProperties
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerContinuousRepresentativePowerBound

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjRepBound



theorem contRep_bound : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → 1 ≤ (D.sp.Y 0).rank → ∃ m : ℕ, ∀ u : (MP R).Vec, ∃ C : ℝ, ∀ y : X.B.I.GA, ‖GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) y‖ ≤ C * (GlobalTheory.Count.tau1 X.B.I y)⁻¹ ^ m := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h h1 h2 h3 hH hι t c ht hcl hc Φ hΦ hrep hrank
  classical
  have hn : 1 ≤ X.B.I.n := by
    rw [← GlobalTheory.Core.Mi.rank_eq X h]
    exact hrank
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hexp : ∀ τ, ∀ Y ∈ lieAt (D.sp.Y 0) τ, ∀ s : ℝ,
      NormedSpace.exp (s • Y) ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ) := fun τ Y hY s =>
    GlobalTheory.SmoothAutCheck.exp_mem_UH (Formalism.IndefR.Eqv.gramAt_isUnit D (D.sp.Y 0) τ) hY s
  obtain ⟨-, hfin, -, hpl, -⟩ := GlobalTheory.ConjRowAut.iota_data R.θ h3.inf hexp X.B.I h
  have hιt : (iotaX X h t).1 = 1 := hfin t ht
  have hcomm : ∀ z : X.B.I.GA, z.2 = 1 → iotaX X h t * z = z * iotaX X h t := by
    intro z hz
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_mul, hιt]
    · simp [Prod.snd_mul, hz]
  have hsymm : ∀ z, iotaX X h ((iotaX X h).toMulEquiv.symm z) = z := fun z =>
    (iotaX X h).toMulEquiv.apply_symm_apply z
  obtain ⟨f, hfdef⟩ : ∃ f : (MP R).Vec → X.B.I.GA → ℂ, ∀ u,
      f u = GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) :=
    ⟨_, fun _ => rfl⟩
  have hf : ∀ u, Formalism.L2.SG.EvalTOntoRep.IsContRep X
      (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) (f u) := by
    intro u
    obtain ⟨ψ, hψ⟩ := hrep u
    rw [hfdef, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
    exact hψ
  have hK : ∀ u, ∀ k ∈ X.B.I.Kg X.B.g, ∀ y, f u (y * (1, k)) = f u y := by
    intro u k hk y
    obtain ⟨S, -, hS⟩ := Submodule.mem_map.mp hΦ
    have hΦz : ∀ z, Φ z = X.B.Re (S z) := fun z => by rw [← hS]; rfl
    have hR : X.B.R (1, k) (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) =
        Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u)) := by
      rw [hΦz]
      exact ContinuousLinearMap.ext_iff.mp (GlobalTheory.Dec.CuspFrame.re_fixed X.B k hk) _
    have hr := Formalism.L2.SG.EvalTOntoRep.contRep_reg X (hf u) ((1, k) : X.B.I.GA)
    rw [hR] at hr
    exact congrFun (Formalism.L2.SG.EvalTOntoRep.contRep_unique X hr (hf u)) y
  have he := GlobalTheory.T.conjugatedIntertwiner_equivariant_realPlace hDS R F X h h1 h2 h3 hH hι t c ht hcl hc Φ hΦ hrep
  have hs := GlobalTheory.T.conjugateIntertwinerValues_sobolevContinuous hDS R F X h h1 h2 h3 hH hι t c ht hcl hc Φ hΦ hrep
  obtain ⟨m, hm⟩ := GlobalTheory.T.derivativeClosedClass_bounded_by_inverseLeastSize X.B hn hg
  have hW : ∀ g ∈ Set.range f, (∃ G, GlobalTheory.Dec.IsContRep X.B G g) ∧
      (∀ k ∈ X.B.I.Kg X.B.g, ∀ y, g (y * (1, k)) = g y) ∧
      ∀ (v : NumberField.InfinitePlace X.B.I.F) (E : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (X.B.I.ε v)), ∃ g' ∈ Set.range f,
        ∀ y, HasDerivAt (fun s : ℝ => g (y * GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B v E) s))
          (g' y) 0 := by
    rintro _ ⟨u, rfl⟩
    refine ⟨⟨_, hf u⟩, hK u, fun v E => ?_⟩
    obtain ⟨τ, Y, hY, hYt⟩ := hpl v E.1 E.2
    have h2s : ∀ s : ℝ, (iotaX X h (oneP R.θ (D.sp.Y 0) τ Y s)).2 = 1 := fun s => (hYt s).1
    have hone : ∀ s : ℝ, iotaX X h (oneP R.θ (D.sp.Y 0) τ Y s) =
        GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B v E) s := fun s =>
      GlobalTheory.RepSmooth.eq_onePar X.B v E s (hYt s).1 (hYt s).2.1 (hYt s).2.2
    refine ⟨f (Function.update u τ (GlobalTheory.RepSmooth.der u τ hY)), ⟨_, rfl⟩, fun y => ?_⟩
    have key := (GlobalTheory.RepSmooth.hasDerivAt_switch he hs τ u hY (iotaX X h).toMulEquiv
      (fun s => iotaX X h (oneP R.θ (D.sp.Y 0) τ Y s)) (fun _ => rfl) (y * iotaX X h t)).star
    have hfun : (fun s : ℝ => f u (y * GlobalTheory.SobolevBound.onePar X.B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace X.B v E) s)) =
        fun s => star (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u ((iotaX X h).toMulEquiv.symm
          (y * iotaX X h t * iotaX X h (oneP R.θ (D.sp.Y 0) τ Y s)))) := by
      funext s
      erw [GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t]
      rw [star_star, ← hone s, hfdef]
      congr 1
      erw [map_mul, map_inv, hsymm]
      rw [mul_assoc y, hcomm _ (h2s s), ← mul_assoc, mul_inv_cancel_right]
    have hval : f (Function.update u τ (GlobalTheory.RepSmooth.der u τ hY)) y =
        star (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update u τ (GlobalTheory.RepSmooth.der u τ hY))
          ((iotaX X h).toMulEquiv.symm (y * iotaX X h t))) := by
      erw [GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t]
      rw [star_star]
      erw [map_mul, map_inv, hsymm]
      rw [mul_inv_cancel_right, hfdef]
    rw [hfun, hval]
    exact key
  refine ⟨m, fun u => ?_⟩
  have hb := hm (Set.range f) hW (f u) ⟨u, rfl⟩
  rw [hfdef] at hb
  exact hb

end GlobalTheory.ConjRepBound

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerContinuousRepresentativePowerBoundStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.intertwiner_continuous_representative_power_bound : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → 1 ≤ (D.sp.Y 0).rank → ∃ m : ℕ, ∀ u : (MP R).Vec, ∃ C : ℝ, ∀ y : X.B.I.GA, ‖GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) y‖ ≤ C * (GlobalTheory.Count.tau1 X.B.I y)⁻¹ ^ m := by
  first | exact @GlobalTheory.ConjRepBound.contRep_bound | exact GlobalTheory.ConjRepBound.contRep_bound | (intros; apply GlobalTheory.ConjRepBound.contRep_bound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointIdentificationLeastSizeLinearGrowth

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.IotaNorm

theorem iota_norm_of_eq {D : D7} (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (I : Formalism.MainNotions.S.AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D) :
    (∀ g ∈ GinfC (D.sp.Y 0), ((Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm) g).2 = 1) ∧
    (1 ≤ (D.sp.Y 0).rank → ∀ x : I.GA, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ GinfC (D.sp.Y 0),
      (GlobalTheory.Count.tau1 I (x * (Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm) g))⁻¹ ≤
        C * normInf θ (D.sp.Y 0) g) := by
  subst h
  set ι := (Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm) with hιdef
  have key : ∀ k, (∀ v, Formalism.MainNotions.S.uMat ((ι k).1 v) = Formalism.L2.SG.AdBridge.ofHAInf (Formalism.L2.SG.InstExistsPf.instOf D) k v) ∧ (Formalism.L2.SG.InstExistsPf.instOf D).fmat (ι k).2 = Formalism.L2.SG.AdBridge.ofHAFin _ k := by
    intro k
    have := Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (Formalism.IndefR.RationalEmbedding.iota D k)
    have e := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply k
    exact ⟨fun v => (this.1 v).trans (congrArg (fun z => Formalism.L2.SG.AdBridge.ofHAInf (Formalism.IndefR.RationalEmbedding.inst D) z v) e),
      this.2.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin (Formalism.IndefR.RationalEmbedding.inst D)) e)⟩
  have hinf : ∀ k v, Formalism.MainNotions.S.uMat ((ι k).1 v) = ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ *
      Formalism.MainNotions.StandardLattice.infMat (Formalism.L2.SG.InstExistsPf.instOf D).cm.sig (Formalism.L2.SG.InstExistsPf.instOf D).J (θ ((Formalism.L2.Host.tauPl D).symm v)) k *
      (Formalism.L2.SG.InstExistsPf.instOf D).P v := fun k v =>
    ((key k).1 v).trans (congrArg (fun M => ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ * M * (Formalism.L2.SG.InstExistsPf.instOf D).P v)
      (GlobalTheory.IotaReal.map_thetaV_gen (Formalism.L2.SG.InstExistsPf.instOf D) v (θ ((Formalism.L2.Host.tauPl D).symm v)) (hθ _) k))
  have hfin : ∀ g ∈ GinfC (D.sp.Y 0), (ι g).2 = 1 := by
    intro g hg
    apply Subtype.ext
    apply Units.ext
    refine (key g).2.trans (GlobalTheory.IotaReal.ofHAFin_eq_one _ _ ?_)
    have e3 : (finHom (D.sp.Y 0) g).val = 1 := by
      rw [show finHom (D.sp.Y 0) g = 1 from hg]; rfl
    ext i j
    exact congrFun (congrFun e3 i) j
  refine ⟨hfin, fun hn x => ?_⟩
  choose c hc0 hc using fun v => GlobalTheory.TauNorm.exp_dOp_le ((Formalism.L2.SG.InstExistsPf.instOf D).P v)⁻¹ ((Formalism.L2.SG.InstExistsPf.instOf D).P v)
  have hC : 0 ≤ ∑ v, c v := Finset.sum_nonneg fun v _ => hc0 v
  have hn' : 1 ≤ (Formalism.L2.SG.InstExistsPf.instOf D).n := hn
  have hp : 0 ≤ (GlobalTheory.Count.tau1 (Formalism.L2.SG.InstExistsPf.instOf D) x)⁻¹ :=
    inv_nonneg.2 ((GlobalTheory.TauLipschitz.tauLip (Formalism.L2.SG.InstExistsPf.instOf D) hn').1 _).le
  refine ⟨(GlobalTheory.Count.tau1 (Formalism.L2.SG.InstExistsPf.instOf D) x)⁻¹ * ∑ v, c v, mul_nonneg hp hC, fun g hg => ?_⟩
  have hv : ∀ v, Real.exp (GlobalTheory.Count.dOp (Formalism.MainNotions.S.uMat ((ι g).1 v))) ≤ (∑ v, c v) * normInf θ (D.sp.Y 0) g := by
    intro v
    have h0 := GlobalTheory.TauNorm.uMat_ne_zero (Formalism.L2.SG.InstExistsPf.instOf D) hn' (ι g) v
    rw [hinf g v] at h0 ⊢
    have h2 := hc v _ h0
    have h3 : c v ≤ ∑ v, c v := Finset.single_le_sum (fun v _ => hc0 v) (Finset.mem_univ _)
    exact h2.trans (mul_le_mul h3 (GlobalTheory.TauNorm.sum_le_normInf θ g ((Formalism.L2.Host.tauPl D).symm v))
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hC)
  have hh := GlobalTheory.TauNorm.inv_tau_mul_le (Formalism.L2.SG.InstExistsPf.instOf D) hn' x (ι g) (hfin g hg) _ hv
  rw [← mul_assoc] at hh
  exact hh

theorem iotaX_norm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ g ∈ GinfC (D.sp.Y 0), (iotaX X h g).2 = 1) ∧ (1 ≤ (D.sp.Y 0).rank → ∀ x : X.B.I.GA, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ GinfC (D.sp.Y 0), (GlobalTheory.Count.tau1 X.B.I (x * iotaX X h g))⁻¹ ≤ C * normInf R.θ (D.sp.Y 0) g) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ hMod _
  exact iota_norm_of_eq R.θ hMod.inf X.B.I h

end GlobalTheory.IotaNorm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointIdentificationLeastSizeLinearGrowthStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realPointIdentification_leastSize_linear_growth : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ g ∈ GinfC (D.sp.Y 0), (iotaX X h g).2 = 1) ∧ (1 ≤ (D.sp.Y 0).rank → ∀ x : X.B.I.GA, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ GinfC (D.sp.Y 0), (GlobalTheory.Count.tau1 X.B.I (x * iotaX X h g))⁻¹ ≤ C * normInf R.θ (D.sp.Y 0) g) := by
  first | exact @GlobalTheory.IotaNorm.iotaX_norm | exact GlobalTheory.IotaNorm.iotaX_norm | (intros; apply GlobalTheory.IotaNorm.iotaX_norm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerValuesSmoothAutomorphic

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjAutSmooth

theorem castGA_mem {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) : castGA e x ∈ I'.GFset ↔ x ∈ I.GFset := by
  subst e; rfl

theorem iotaX_rat {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {γ : GA D (D.sp.Y 0)} (hγ : γ ∈ GQ (D.sp.Y 0)) : iotaX X h γ ∈ X.B.I.GFset := by
  show castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D γ) ∈ X.B.I.GFset
  rw [castGA_mem]
  exact (Formalism.IndefR.RationalEmbedding.iota_rat D γ).1 hγ



theorem conjMap_isAutFunSm : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsAutFunSm R.θ (Yc D 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep u
  set Ψ := GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t with hΨ
  have hθ : IsInfFam R.θ := hMod.inf
  have he : GlobalTheory.RepSmooth.IsEquiv R.θ Ψ := fun τ g hg v w hw =>
    GlobalTheory.T.conjugatedIntertwiner_equivariant_realPlace hDS R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep τ g hg v w hw
  have hs : GlobalTheory.RepSmooth.IsSob Ψ := fun τ v x =>
    GlobalTheory.T.conjugateIntertwinerValues_sobolevContinuous hDS R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep τ v x
  have hval : ∀ v (y : GA D (Yc D 0)), Ψ v y = star (GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c v)))
      (iotaX X h (y * t⁻¹))) := fun v y => GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t v y
  have hcont : ∀ v, Continuous (Ψ v) := by
    intro v
    obtain ⟨ψ, hψ⟩ := hrep v
    have e : Ψ v = fun y : GA D (Yc D 0) => star (ψ (iotaX X h (y * t⁻¹))) := by
      funext y; exact (hval v y).trans (by rw [GlobalTheory.ConjRowMult.contRepL_spec X hψ])
    rw [e]
    exact continuous_star.comp (hψ.1.comp ((iotaX X h).continuous.comp (continuous_mul_const t⁻¹)))
  refine ⟨⟨?_, ?_, hcont u⟩, fun k τs Xs hX g => GlobalTheory.RepSmooth.smooth hθ he hs hcont u k τs Xs hX g,
    GlobalTheory.RepSmooth.zfin he hs u, ?_⟩
  · intro γ hγ g
    obtain ⟨ψ, hψ⟩ := hrep u
    rw [hval, hval, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
    congr 1
    have e2 : iotaX X h (γ * g * t⁻¹) = iotaX X h γ * iotaX X h (g * t⁻¹) := by
      exact (congrArg (iotaX X h) (mul_assoc γ g t⁻¹)).trans (map_mul (iotaX X h) γ (g * t⁻¹))
    rw [e2]; exact hψ.2.1 _ (iotaX_rat X h hγ) _
  · obtain ⟨U, hU, hUk⟩ := GlobalTheory.GoodFiniteDim.exists_open_subgroup (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))
    refine ⟨U, hU, fun k hk hkf g => ?_⟩
    obtain ⟨h1, h2⟩ := hUk k hk hkf
    rw [GlobalTheory.T.conjugatedIntertwiner_hasColumnLevel hDS R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep u k h1 g, h2, one_mul]
  · have key : ∃ N : ℕ, ∀ v (x : GA D (Yc D 0)), ∃ C : ℝ, ∀ g ∈ GinfC (Yc D 0),
        ‖Ψ v (x * g)‖ ≤ C * normInf R.θ (Yc D 0) g ^ N := by
      rcases Nat.eq_zero_or_pos (D.sp.Y 0).rank with hn | hn
      · refine ⟨0, fun v x => ⟨‖Ψ v x‖, fun a _ => ?_⟩⟩
        have : a = 1 := Subtype.ext (Units.ext (Matrix.ext fun i => (Fin.cast hn i).elim0))
        simp [this]
      obtain ⟨hfin, hnorm⟩ := GlobalTheory.T.realPointIdentification_leastSize_linear_growth R F X h hRI hGrp hMod hιE
      obtain ⟨m, hm⟩ := GlobalTheory.T.intertwiner_continuous_representative_power_bound hDS R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep hn
      refine ⟨m, fun v x => ?_⟩
      obtain ⟨C, hC⟩ := hm v
      obtain ⟨C', hC0, hC'⟩ := hnorm hn (iotaX X h (x * t⁻¹))
      refine ⟨|C| * C' ^ m, fun a ha => ?_⟩
      have hi2 : (iotaX X h t⁻¹).1 = 1 :=
        ((GlobalTheory.IotaReal.iotaX_real_finite R F X h hRI hGrp hMod hιE).1 t⁻¹).1 (inv_mem ht)
      have hi1 : (iotaX X h a).2 = 1 := hfin a ha
      have hc : iotaX X h a * iotaX X h t⁻¹ = iotaX X h t⁻¹ * iotaX X h a :=
        Prod.ext (by simp [Prod.fst_mul, hi2]) (by simp [Prod.snd_mul, hi1])
      have hcomm : iotaX X h (x * a * t⁻¹) = iotaX X h (x * t⁻¹) * iotaX X h a := by
        have e1 : iotaX X h (x * a * t⁻¹) = iotaX X h x * iotaX X h a * iotaX X h t⁻¹ := by
          exact (map_mul (iotaX X h) (x * a) t⁻¹).trans (congrArg (· * iotaX X h t⁻¹) (map_mul (iotaX X h) x a))
        have e2 : iotaX X h (x * t⁻¹) = iotaX X h x * iotaX X h t⁻¹ := by
          exact map_mul (iotaX X h) x t⁻¹
        rw [e1, e2, mul_assoc, hc, ← mul_assoc]
      have hp : 0 ≤ (GlobalTheory.Count.tau1 X.B.I (iotaX X h (x * t⁻¹) * iotaX X h a))⁻¹ :=
        inv_nonneg.2 ((GlobalTheory.TauLipschitz.tauLip X.B.I (by rw [h]; exact hn)).1 _).le
      have h1 := hC (iotaX X h (x * a * t⁻¹))
      rw [hcomm] at h1
      rw [hval, norm_star, hcomm]
      refine h1.trans ?_
      calc C * (GlobalTheory.Count.tau1 X.B.I (iotaX X h (x * t⁻¹) * iotaX X h a))⁻¹ ^ m
          ≤ |C| * (C' * normInf R.θ (Yc D 0) a) ^ m :=
            mul_le_mul (le_abs_self _) (pow_le_pow_left₀ hp (hC' a ha) m) (pow_nonneg hp m) (abs_nonneg _)
        _ = |C| * C' ^ m * normInf R.θ (Yc D 0) a ^ m := by rw [mul_pow, mul_assoc]
    obtain ⟨N, hN⟩ := key
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨v, hv⟩ := GlobalTheory.RepSmooth.foldr_rder he hs u l hl
    obtain ⟨C, hC⟩ := hN v x
    exact ⟨C, fun g hg => (congrArg norm (congrFun hv (x * g))).le.trans (hC g hg)⟩

end GlobalTheory.ConjAutSmooth
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerValuesSmoothAutomorphicStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjugatedIntertwiner_values_smoothAutomorphic : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsAutFunSm R.θ (Yc D 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  first | exact @GlobalTheory.ConjAutSmooth.conjMap_isAutFunSm | exact GlobalTheory.ConjAutSmooth.conjMap_isAutFunSm | (intros; apply GlobalTheory.ConjAutSmooth.conjMap_isAutFunSm <;> assumption)
end
end
