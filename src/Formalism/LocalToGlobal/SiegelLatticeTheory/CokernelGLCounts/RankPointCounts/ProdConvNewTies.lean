module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvOfVolLocPos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AbsNormGeTwo
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OmegaUnramifiedHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocVolPrim
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataTies
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXHaarPos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXSDLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXTyped
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocFramePrim
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocMassTyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValDiffProd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrd
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdSd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondAllPf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.Basify
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Mathlib.Tactic.TypeStar

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalFactorsPosTypicalGeneral

section

@[expose] public section

noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.ProdConvCut2

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.MassDataX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem local_factors_pos_typical_general {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (ψ : AddChar (AF X.B.I.F) ℂ)
    (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w)
    (u u' : D.what₂.Word) (v : PlX X) (hv : TypAt X v) : 0 < MX X u u' ψ v ∧ 0 < localVolumeUnit X ψ v := by
  let p : TypX X := ⟨v, hv⟩
  have : Submodule.IsFullLattice X.B.I.E X.B.I.L :=
    { toIsLattice := Submodule.IsLattice.of_fg X.B.I.E X.B.I.L_fg
      span_eq_top := X.B.I.L_span }
  have hL := locTieX_of X ψ u (hloc u) (Formalism.L2.SG.Pf.LocVolPrim.primX X u locFramePrim)
  have hL' := locTieX_of X ψ u' (hloc u') (Formalism.L2.SG.Pf.LocVolPrim.primX X u' locFramePrim)
  have hTF := Formalism.L2.SG.Pf.typFacts_holds X hb u u'
  have h := locMassTyp X.B.I.cm.sig X.B.I.J ψ v (gAt X v) (frameOf X u) (frameOf X u')
    (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, hψ, hs⟩ _ _
    (MassDataLevelSSteps.FrameW.frameOf_isStd X u) (MassDataLevelSSteps.FrameW.frameOf_isStd X u')
    (Formalism.L2.SG.Pf.MassDataX.SDL.sdLocX_holds X v) (Formalism.L2.SG.Pf.NcX.OmVSt.unramAt_of_cm X.B.I.cm v)
    ⟨X.B.I.L, inferInstance, rfl⟩ (hTF p).1
    (gAt_mem X p) (hTF p).2.1 (hTF p).2.2.1 (hTF p).2.2.2.2
    _ (hL v).1 _ (hL v).2.1 (hL v).2.2.1 _ (hL' v).2.1 (hL' v).2.2.1 (hL v).2.2.2 (hL' v).2.2.2
  have hpos := div_pos (mul_pos (gv_pos X p (kg_sub_kv X p) subset_rfl)
      (gv_pos X p (kg_sub_knat X p u) (knat_sub_kv X p u)))
      (mul_pos (sv_pos X u p (kg_sub_kv X p) subset_rfl) (sv_pos X u' p (kg_sub_kv X p) subset_rfl))
  have hR : 0 < MX X u u' ψ v / localVolumeUnit X ψ v := by
    unfold MX localVolumeUnit OmX
    rw [if_pos hv, if_pos hv]
    exact lt_of_lt_of_eq hpos h.symm
  have hU0 : 0 ≤ localVolumeUnit X ψ v := ENNReal.toReal_nonneg
  rcases div_pos_iff.1 hR with ⟨h1, h2⟩ | ⟨-, h2⟩
  · exact ⟨h1, h2⟩
  · exact absurd h2 (not_lt.2 hU0)

end Formalism.L2.SG.Pf.ProdConvCut2
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnramifiedFactorEqOne

section

@[expose] public section

noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcVal
  Formalism.L2.SG.Pf.NcVal.VolOrdW Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.SG.TypedSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem absV_prod {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (s : Finset ι)
    (f : ι → Fv F v) : absV v (∏ i ∈ s, f i) = ∏ i ∈ s, absV v (f i) := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty]
    exact absV_one v
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, absV_mul, ih]

theorem absV_alp_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (h1 : absV v (dV v) = 1)
    (r : ℕ) (i : Fin (r + 1)) : absV v (alp v r i) = 1 := by
  rw [absV_alp, h1, Real.one_rpow]

section Vols

variable {X} {ψ}

theorem zz_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) : ZZX X u u' ψ v = 1 := by
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH1, -, hO1⟩ := hN v hv (Fin (D.R.rS + 1) × Fin (D.R.rS + 1))
  have := hH1
  have hsetZ : ZZOrd (E := X.B.I.E) v D.R.rS =
      Set.univ.pi fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) =>
        {c | sc (E := X.B.I.E) v (alp v D.R.rS p.1 * alp v D.R.rS p.2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [ZZOrd, locZ, Set.mem_pi, Prod.forall]
  unfold ZZX volS
  rw [if_neg hv, hsetZ, SdW.boxScaleL_holds v (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) hfin
    (sdE (E := X.B.I.E) ψ v (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
    (fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => alp v D.R.rS p.1 * alp v D.R.rS p.2)
    (fun p => mul_ne_zero (alp_ne_zero v D.R.rS p.1) (alp_ne_zero v D.R.rS p.2)), hO1, h1, one_pow, one_mul]
  refine Finset.prod_eq_one fun p _ => ?_
  rw [absV_mul, absV_alp_one v h1, absV_alp_one v h1]
  norm_num

theorem uo_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) :
    (sdE (E := X.B.I.E) ψ v (UIdx D.R.rS) (UO (E := X.B.I.E) v D.R.rS)).toReal = 1 := by
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH2, -, hO2⟩ := hN v hv (UIdx D.R.rS)
  have := hH2
  have hsetU : UO (E := X.B.I.E) v D.R.rS =
      Set.univ.pi fun q : UIdx D.R.rS =>
        {c | sc (E := X.B.I.E) v ((alp v D.R.rS q.1.1)⁻¹ * alp v D.R.rS q.1.2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [UO, Set.mem_pi]
  rw [hsetU, SdW.boxScaleL_holds v (UIdx D.R.rS) hfin (sdE (E := X.B.I.E) ψ v (UIdx D.R.rS))
    (fun q : UIdx D.R.rS => (alp v D.R.rS q.1.1)⁻¹ * alp v D.R.rS q.1.2)
    (fun q => mul_ne_zero (inv_ne_zero (alp_ne_zero v D.R.rS q.1.1)) (alp_ne_zero v D.R.rS q.1.2)), hO2, h1,
    one_pow, one_mul]
  refine Finset.prod_eq_one fun q _ => ?_
  rw [absV_mul, absV_inv v (alp_ne_zero v D.R.rS q.1.1), absV_alp_one v h1, absV_alp_one v h1]
  norm_num

theorem unramified_factor_eq_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) : localVolumeUnit X ψ v = 1 := by
  obtain ⟨hH2, hS2, -⟩ := hN v hv (UIdx D.R.rS)
  have := hH2
  have := hS2
  unfold localVolumeUnit volU
  rw [if_neg hv, localVolumeOrdinary, Measure.prod_prod, ENNReal.toReal_mul, uo_one hN hv h1, one_mul]

theorem pp_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) (l : Fin (D.R.rS + 1)) :
    PPX X u u' ψ l v = 1 := by
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH, -, hO⟩ := hN v hv Unit
  have := hH
  have hset : (fun c : Unit → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E => c ()) ⁻¹' PPOrd (E := X.B.I.E) v D.R.rS l =
      Set.univ.pi fun _ : Unit => {c | sc (E := X.B.I.E) v (alp v D.R.rS l ^ 2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [PPOrd, Set.mem_pi]
    exact ⟨fun h i => h, fun h => h ()⟩
  unfold PPX volC
  rw [if_neg hv, hset, SdW.boxScaleL_holds v Unit hfin (sdE (E := X.B.I.E) ψ v Unit)
    (fun _ : Unit => alp v D.R.rS l ^ 2) (fun _ => pow_ne_zero _ (alp_ne_zero v D.R.rS l)), hO, h1, one_pow, one_mul]
  refine Finset.prod_eq_one fun q _ => ?_
  rw [absV_pow, absV_alp_one v h1]
  norm_num

theorem jac_one {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) : jacX X v = 1 := by
  unfold jacX jacS
  refine Finset.prod_eq_one fun l _ => ?_
  rw [if_neg hv, mul_one, absV_prod]
  rw [Finset.prod_eq_one fun i _ => by rw [absV_pow, absV_alp_one v h1, one_pow]]
  norm_num

end Vols

theorem VolOneAEC_holds (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) : VolOneAEC X u u' ψ := by
  have hN : SdNormDV X ψ := sdNormDV_of X ψ (annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different) hψ hs
  have hT : Set.Finite {v : PlX X | TypAt X v} := (typSet X.B.I.F (D.host.g 0) (D.host.g 1)).finite_toSet
  have hI := differentIdeal_ne_zero' X.B.I.F
  have hD := Ideal.hasFiniteMulSupport hI
  refine (hT.union hD).subset fun v hv => ?_
  by_contra hnot
  simp only [Set.mem_union, Set.mem_setOf_eq, Function.mem_mulSupport, not_or, not_not] at hnot
  obtain ⟨htyp, hmax⟩ := hnot
  have h1 : absV v (dV v) = 1 := by rw [absV_dV, hmax, map_one, Nat.cast_one, inv_one]
  exact hv ⟨unramified_factor_eq_one hN htyp h1, zz_one u u' hN htyp h1, fun l => pp_one u u' hN htyp h1 l, jac_one htyp h1⟩

end Formalism.L2.SG.Pf.ProdConvCut2
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvNewTies

section

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.ProdConvCut

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)

def ProdConvNew : Prop :=
  (∀ v, (TypAt X v → 0 < MX X u u' ψ v) ∧ 0 < localVolumeUnit X ψ v ∧ 0 < ZZX X u u' ψ v ∧ (∀ l, 0 < PPX X u u' ψ l v) ∧
    0 < alX X u u' v) ∧
  True ∧ True ∧
  Multipliable (fun v : OrdX X => localVolumeUnit X ψ v.1) ∧ 0 < ∏' v : OrdX X, localVolumeUnit X ψ v.1 ∧
  Multipliable (ZZX X u u' ψ) ∧ 0 < ∏' v : PlX X, ZZX X u u' ψ v ∧
  (∀ l, Multipliable (PPX X u u' ψ l) ∧ 0 < ∏' v : PlX X, PPX X u u' ψ l v) ∧
  Multipliable (fun v : OrdX X => alX X u u' v.1) ∧ 0 < ∏' v : OrdX X, alX X u u' v.1 ∧
  Multipliable (jacX X) ∧ 0 < ∏' v : PlX X, jacX X v

private theorem multipliable_and_tprod_pos_of_finite_mulSupport {ι : Type*} (f : ι → ℝ) (hpos : ∀ i, 0 < f i) (hfin : (Function.mulSupport f).Finite) :
    Multipliable f ∧ 0 < ∏' i, f i := by
  refine ⟨multipliable_of_hasFiniteMulSupport hfin, ?_⟩
  rw [tprod_eq_prod' (s := hfin.toFinset) (by simp)]
  exact Finset.prod_pos fun i _ => hpos i

theorem prodConvNew_of (h1 : VolOneAEC X u u' ψ)
    (hpos : ∀ v, 0 < localVolumeUnit X ψ v ∧ 0 < ZZX X u u' ψ v ∧ (∀ l, 0 < PPX X u u' ψ l v) ∧ 0 < jacX X v)
    (hM : ∀ v, TypAt X v → 0 < MX X u u' ψ v) (hal : ∀ v, 0 < alX X u u' v) (h3 : AlConvC X u u') :
    ProdConvNew X u u' ψ := by
  have hS : ∀ g : PlX X → ℝ, (∀ v, g v ≠ 1 → ¬ (localVolumeUnit X ψ v = 1 ∧ ZZX X u u' ψ v = 1 ∧
      (∀ l, PPX X u u' ψ l v = 1) ∧ jacX X v = 1)) → (Function.mulSupport g).Finite :=
    fun g hg => h1.subset fun v hv => hg v hv
  have hU : (Function.mulSupport fun v : OrdX X => localVolumeUnit X ψ v.1).Finite := by
    refine (h1.preimage Subtype.val_injective.injOn).subset fun v hv => ?_
    intro h
    exact hv h.1
  have hZ := hS (ZZX X u u' ψ) fun v hv h => hv h.2.1
  have hP : ∀ l, (Function.mulSupport (PPX X u u' ψ l)).Finite := fun l => hS _ fun v hv h => hv (h.2.2.1 l)
  have hJ := hS (jacX X) fun v hv h => hv h.2.2.2
  have rU := multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v : OrdX X => (hpos v.1).1) hU
  have rZ := multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v => (hpos v).2.1) hZ
  have rJ := multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v => (hpos v).2.2.2) hJ
  exact ⟨fun v => ⟨hM v, (hpos v).1, (hpos v).2.1, (hpos v).2.2.1, hal v⟩, trivial, trivial, rU.1, rU.2, rZ.1, rZ.2,
    fun l => multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v => (hpos v).2.2.1 l) (hP l), h3.1, h3.2, rJ.1, rJ.2⟩

theorem prodConvNew_gen (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ)
    (hs : IsStdChar ψ) (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w)
    (hpos : ∀ v, (¬ TypAt X v → 0 < localVolumeUnit X ψ v) ∧ 0 < ZZX X u u' ψ v ∧ (∀ l, 0 < PPX X u u' ψ l v) ∧
      0 < jacX X v) :
    ProdConvNew X u u' ψ := by
  have hk : 1 ≤ D.R.k := Formalism.MainNotions.S.k_pos (D := D)
  refine prodConvNew_of X u u' ψ (VolOneAEC_holds (X := X) (u := u) (u' := u') (ψ := ψ) hψ hs) (fun v => ⟨?_, (hpos v).2.1,
    (hpos v).2.2.1, (hpos v).2.2.2⟩) (fun v h => (local_factors_pos_typical_general X hb ψ hψ hs hloc u u' v h).1)
    (fun v => lt_of_lt_of_le (Real.exp_pos _) (alX_bounds (X := X) (u := u) (u' := u') hk v).1)
    (AlConvC_holds (X := X) (u := u) (u' := u'))
  by_cases h : TypAt X v
  · exact (local_factors_pos_typical_general X hb ψ hψ hs hloc u u' v h).2
  · exact (hpos v).1 h

end Formalism.L2.SG.Pf.ProdConvCut2
end
end
end
