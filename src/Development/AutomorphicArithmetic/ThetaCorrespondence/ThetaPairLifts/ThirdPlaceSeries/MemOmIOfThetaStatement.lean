module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MapMemISupIsLinAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousDefiniteThetaIntegralVectorFormStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModerateGrowthDefiniteThetaIntegralVectorFormStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiplicitySpaceAllLevelsValuesSmoothCuspidalStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionContinuousInvariant
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FVContinuousInvariant

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
noncomputable section
namespace GlobalTheory.ThetaFormV
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.ThetaTri
open scoped Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Frame
variable {D : D7} {V : HSp D} {n : ℕ}
end Frame
section Forms
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}
theorem eW_cast_cV_rho_eq_wt_rho (A : GlobalTheory.NJoin.Agree X P.M P.rep) {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ)
    (j : Fin D.R.m) (k : ℕ) (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m)
    (h : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) {γ : GA D (Vc D j)} (hγ : γ ∈ GQ (Vc D j))
    (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h * A.a j))) (v : (X.R.cV j).W) :
    (Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M μ k p1 p2).wt.W) (fun _ _ => A.eW μ hμ j) hk p1 p2) ((X.R.cV j).ρ γ v) =
      (P.M μ k p1 p2).wt.ρ h ((Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M μ k p1 p2).wt.W) (fun _ _ => A.eW μ hμ j) hk p1 p2) v) := by
  subst hk
  exact A.wt μ hμ j h γ hγ he v
theorem eWloc_cV_rho_eq_wt_rho (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) {γ : GA D (Vc D j)}
    (hγ : γ ∈ GQ (Vc D j))
    (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h * A.a j))) (v : (X.R.cV j).W) :
    _root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ ((X.R.cV j).ρ γ v) = (P.M.loc i).wt.ρ h (_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ v) :=
  _root_.GlobalTheory.ThetaFormV.eW_cast_cV_rho_eq_wt_rho A hμ j _ hj _ _ h hγ he v
end Forms
section Main
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}
def agreementLocalMap (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    Bridge.Gf (Vc D j) → (X.R.cV j).W :=
  fun k => (_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k))
theorem fFin_apply' (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    (k : Bridge.Gf (Vc D j)) : _root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F k =
      (_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k)) := rfl
theorem formToVectorMap_eq_ext_fFin (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F = (X.R.cV j).ext (_root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F) := rfl
theorem fFin_rangeRestrict_mul (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    {γ : GA D (Vc D j)} (hγ : γ ∈ GQ (Vc D j)) (k : Bridge.Gf (Vc D j)) :
    _root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F ((finHom (Vc D j)).rangeRestrict γ * k) = (X.R.cV j).ρ γ (_root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F k) := by
  set x := preF (A.PV j) ((finHom (Vc D j)).rangeRestrict γ) with hxdef
  have hx : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ x) :=
    (congrArg Subtype.val (GlobalTheory.ThetaFormV.fin_preF (A.PV j) ((finHom (Vc D j)).rangeRestrict γ))).symm
  have e0 : (A.a j)⁻¹ * (A.a j * x * (A.a j)⁻¹) * A.a j = x := by group
  have hrat : A.a j * x * (A.a j)⁻¹ ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV :=
    (A.rat j _).2 ⟨γ, hγ, by rw [e0]; exact hx⟩
  have he : finHom (Vc D j) γ =
      finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * ((⟨_, hrat⟩ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) : GAf D.host.E D.R.nV) * A.a j)) := by
    rw [e0]; exact hx
  have e1 : A.a j * preF (A.PV j) ((finHom (Vc D j)).rangeRestrict γ * k) =
      (A.a j * x * (A.a j)⁻¹) * (A.a j * preF (A.PV j) k) := by
    rw [GlobalTheory.ThetaFormV.preF_mul, ← hxdef]; group
  have hF := F.2.1 ⟨_, hrat⟩ (A.a j * preF (A.PV j) k)
  unfold _root_.GlobalTheory.ThetaFormV.agreementLocalMap
  rw [e1]
  refine (LinearEquiv.symm_apply_eq _).2 ?_
  rw [_root_.GlobalTheory.ThetaFormV.eWloc_cV_rho_eq_wt_rho A i j hj hμ ⟨_, hrat⟩ hγ he, LinearEquiv.apply_symm_apply]
  exact hF
theorem formToVectorMap_left_invariant (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    ∀ γ ∈ GQ (Vc D j), ∀ h, _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F (γ * h) = _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h := by
  intro γ hγ h
  rw [_root_.GlobalTheory.ThetaFormV.formToVectorMap_eq_ext_fFin, GlobalTheory.ThetaFormV.ext_apply, GlobalTheory.ThetaFormV.ext_apply, map_mul, _root_.GlobalTheory.ThetaFormV.fFin_rangeRestrict_mul A i j hj hμ F hγ]
  have e : (X.R.cV j).ρ (γ * h)⁻¹ * (X.R.cV j).ρ γ = (X.R.cV j).ρ h⁻¹ := by
    rw [← map_mul]; congr 1; group
  exact congrArg (fun T : Module.End ℂ (X.R.cV j).W => T _) e
end Main
section Cont
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}
theorem continuous_formToVectorMap (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) :
    Continuous (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D (Vc D j)) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Vc D j).gram))
  obtain ⟨N, hN, hlev⟩ := F.2.2
  let J : Subgroup (Bridge.Gf (Vc D j)) :=
    { carrier := {q | ∀ k, _root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F (k * q) = _root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F k}
      mul_mem' := fun {a b} ha hb k => by simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [← mul_assoc, hb, ha]
      one_mem' := fun k => by rw [mul_one]
      inv_mem' := fun {a} ha k => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [← ha (k * a⁻¹), inv_mul_cancel_right] }
  have hfJ : _root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F ∈ Bridge.AdForms ((finHom (Vc D j)).rangeRestrict.comp (GQ (Vc D j)).subtype)
      ((X.R.cV j).ρ.comp (GQ (Vc D j)).subtype) J 1 := by
    exact GlobalTheory.ThetaFormV.mem_adForms_one _ _ (fun γ hγ k => _root_.GlobalTheory.ThetaFormV.fFin_rangeRestrict_mul A i j hj hμ F hγ k) J (fun q hq => hq)
  have hJ : ∀ᶠ κ in 𝓝 (1 : GA D (Vc D j)), ∃ h : (finHom (Vc D j)).rangeRestrict κ ∈ J,
      (1 : J →* ℂˣ) ⟨_, h⟩ = 1 := by
    filter_upwards [eventually_cong_preF (A.PV j) A.hF (A.stdV j) hN] with κ hκ
    refine ⟨fun k => ?_, rfl⟩
    show _root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F (k * (finHom (Vc D j)).rangeRestrict κ) = _root_.GlobalTheory.ThetaFormV.agreementLocalMap A i j hj hμ F k
    rw [_root_.GlobalTheory.ThetaFormV.fFin_apply', _root_.GlobalTheory.ThetaFormV.fFin_apply', GlobalTheory.ThetaFormV.preF_mul, ← mul_assoc, hlev _ hκ]
  exact (GlobalTheory.ThetaIntegrand.form_continuous (finHom (Vc D j)).rangeRestrict (GQ (Vc D j)) (X.R.cV j).ρ
    ((X.given.core.models.cV j).2.2.1) hJ hfJ).congr fun g => (GlobalTheory.ThetaFormV.ext_apply _ _ _).symm
end Cont
theorem formToVectorMap_continuous_and_left_invariant : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)
    (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)),
    Continuous (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F) ∧
      ∀ γ ∈ GQ (Vc D j), ∀ h, _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F (γ * h) = _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h :=
  fun _ _ _ _ A i j hj hμ F => ⟨_root_.GlobalTheory.ThetaFormV.continuous_formToVectorMap A i j hj hμ F, _root_.GlobalTheory.ThetaFormV.formToVectorMap_left_invariant A i j hj hμ F⟩
end GlobalTheory.ThetaFormV
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FVContinuousInvariantStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem _root_.GlobalTheory.T.form_to_vector_map_continuous_invariant : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)
    (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)),
    Continuous (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F) ∧
      ∀ γ ∈ GQ (Vc D j), ∀ h, _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F (γ * h) = _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h := by
  first | exact @_root_.GlobalTheory.ThetaFormV.formToVectorMap_continuous_and_left_invariant | exact _root_.GlobalTheory.ThetaFormV.formToVectorMap_continuous_and_left_invariant | (intros; apply _root_.GlobalTheory.ThetaFormV.formToVectorMap_continuous_and_left_invariant <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemOmIOfTheta

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.ThetaTri in
theorem mem_omI_of_theta_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (φ : (X.R.cV j).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) → ℂ)), (∀ v, Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) (φ v)) → φ ∈ _root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ := by
  intro _ hP hL D P X A i j hj Y hc hμ φ hφ
  have hm := X.given.core.models
  have hθ : IsInfFam X.R.θ := hm.inf
  have hω := X.given.core.thP.ωP j (X.tupT (D.nd.mu i))
  have hp : (Vc D j).IsPosDef := hm.vpos j
  have hpd : ∀ τ, (gramAt D (Vc D j) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((j : ℕ) + 1)) τ
  have hHV := (hm.νV j (X.tupT (D.nd.mu i))).1.1
  have hfdV := (hm.νV j (X.tupT (D.nd.mu i))).2
  have hHW : (X.R.νW j).IsHaarMeasure := (hm.νW j).1.1
  have hfdW : IsFundamentalDomain (GQ (Wc D j)) (X.R.fdW j) (X.R.νW j) := (hm.νW j).2
  intro p
  have hφ' : ∀ v, IsThetaFunO X.R.ψ (Vc D j) (Wc D j) (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ v) :=
    fun v => hω.om_pres _ _ (hφ v)
  refine ⟨hφ', fun F g => ?_, fun F y => ?_⟩
  · obtain ⟨hc1, hc2⟩ := _root_.GlobalTheory.T.form_to_vector_map_continuous_invariant hL D P X A i j hj hμ F
    exact GlobalTheory.DefiniteQuotient.integrableOn_theta D X.R.ψ hω.std (Vc D j) (Wc D j) _ _ _ hω hpd _
      (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ) hφ' _ hc1 hc2 _ _ hHV hfdV g
  · obtain ⟨hc1, hc2⟩ := _root_.GlobalTheory.T.form_to_vector_map_continuous_invariant hL D P X A i j hj hμ F
    have hmap := (Classical.choose_spec (Classical.choose_spec hc)).2.2.1
    have hey : _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y : Y.A) ∈ Formalism.IndefR.principalLevelFrame.Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)) := by
      rw [← hmap]; exact ⟨y, y.2, rfl⟩
    have hyv : _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y = _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y : Y.A) (fun τ => ((Classical.epsilon fun u : ↥(lowT (X.R.MW j (sg0 D X.A)) τ) =>
        ‖((u : (X.R.MW j (sg0 D X.A)).sm τ) : (X.R.MW j (sg0 D X.A)).H τ)‖ = 1 : ↥(lowT (X.R.MW j (sg0 D X.A)) τ)) :
          (X.R.MW j (sg0 D X.A)).sm τ)) := by
      simp [_root_.GlobalTheory.ThetaTri.thetaEvaluationMap, kUnit, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod]
    obtain ⟨haut, hcu⟩ := GlobalTheory.T.multiplicitySpaceAllLevels_values_smooth_cuspidal X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)) _ hey
      (fun τ => ((Classical.epsilon fun u : ↥(lowT (X.R.MW j (sg0 D X.A)) τ) =>
        ‖((u : (X.R.MW j (sg0 D X.A)).sm τ) : (X.R.MW j (sg0 D X.A)).H τ)‖ = 1 : ↥(lowT (X.R.MW j (sg0 D X.A)) τ)) :
          (X.R.MW j (sg0 D X.A)).sm τ))
    rw [← hyv] at haut hcu
    have hR := (GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ haut hcu).conj
    have hgr := GlobalTheory.T.moderateGrowth_definiteThetaIntegral_vectorForm X.R.ψ (Vc D j) (Wc D j) _ _ _ hω hpd _ _ hHV hfdV _
      (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ) hφ' _ hc1 hc2
    have hct := GlobalTheory.T.continuous_definiteThetaIntegral_vectorForm X.R.ψ (Vc D j) (Wc D j) _ _ _ hω hpd _ _ hHV hfdV _
      (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ) hφ' _ hc1 hc2
    have hinv : ∀ γ ∈ GQ (Wc D j), ∀ g, (∫ h in X.R.fdV j (X.tupT (D.nd.mu i)),
        thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) h (γ * g)
          (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h)) ∂(X.R.νV j (X.tupT (D.nd.mu i)))) =
        ∫ h in X.R.fdV j (X.tupT (D.nd.mu i)), thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) h g
          (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h)) ∂(X.R.νV j (X.tupT (D.nd.mu i))) := by
      intro γ hγ g
      congr 1
      funext h
      have e : ((h, γ * g) : GA D (Vc D j) × GA D (Wc D j)) = (1, γ) * (h, g) := by simp
      unfold thetaKO
      rw [e, map_mul]
      exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ (hφ' _))
    have := hR.integrableOn_modGrowth_mul hHW hfdW hgr hinv hct.aestronglyMeasurable
    convert this using 1
    rw [mul_comm]
    rfl
end GlobalTheory.ThetaTri
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemOmIOfThetaStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.theta_lift_linear_form_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (φ : (X.R.cV j).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) → ℂ)), (∀ v, Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) (φ v)) → φ ∈ _root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ := by
  first | exact @_root_.GlobalTheory.ThetaTri.mem_omI_of_theta_alt | exact _root_.GlobalTheory.ThetaTri.mem_omI_of_theta_alt | (intros; apply _root_.GlobalTheory.ThetaTri.mem_omI_of_theta_alt <;> assumption)
end
end
end
