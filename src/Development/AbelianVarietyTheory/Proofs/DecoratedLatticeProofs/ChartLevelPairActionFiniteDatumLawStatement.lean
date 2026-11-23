module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsKeepStandardLattice
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawUnderTwoChartLevelsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianTwistedRealReadingEntireAndInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionMovesByTranslatePair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalCongruenceFixesDefiniteStepVector
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairsStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntSubIsLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepAverageKillsThetaOfDenseFamily
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsKeepStandardLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

theorem _root_.GlobalTheory.T.chartLevels_keep_standardLattice : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, ∀ k ∈ A.U i β, Moves _ (rankN (I.rec7 l Z) i hi) k (Formalism.L2.Col.stdLat B.fields.E _) := by
  first | exact @GlobalTheory.AdForm.levels_keep_stdLat | exact GlobalTheory.AdForm.levels_keep_stdLat | (intros; apply GlobalTheory.AdForm.levels_keep_stdLat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilActionEqSmulOfKeepsLattice

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

noncomputable section
namespace GlobalTheory.LevLaw

theorem heisO_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (x : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
  funext t
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem omega_eq_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ vac Φ w, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) vac → IsSBHalf e (stdHom S T) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac Φ w → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, (∀ x, x ∈ stdHom S T ↔ actO S T k k' x ∈ stdHom S T) → ∀ p q : ℂ, om (k, k') vac = p • vac → (∀ z, IsHalf e z → p * Φ (actO S T k⁻¹ k'⁻¹ z) = q * Φ z) → om (k, k') w = q • w := by
  intro D ψ θ S T a b hS hT δ sc hstd μ om hW e SS hSS vac Φ w hvac hΦ hw k hk k' hk' hkeep p q hp hq
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hSS
  have hinf : infPart D e = 0 := GlobalTheory.PlaceDatum.infPart_idemSum hSS
  have sdS0 := GlobalTheory.SplitMove.selfDual_int S hstd.gS
  have sdT0 := GlobalTheory.SplitMove.selfDual_int T hstd.gT
  have hth : IsThetaFunO ψ S T vac := hvac.2.theta
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hw
  have th0 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hstd.std S T _ _ sdS0 sdT0 e hee hinf vac hth T₀ hT₀
  have pm := GlobalTheory.SplitMove.isPlaceModel_move₂ hW hkeep hT₀ th0
  rw [hp] at pm
  have omm : ∀ r s (X : WO S T → ℂ), om r (om s X) = om (r * s) X := fun r s X => by
    rw [map_mul]; rfl

  have hv0 : vac ≠ 0 := by
    intro h0
    obtain ⟨⟨m, hm⟩, hn⟩ := hvac.2.norm
    have h1 := hn m hm
    rw [h0] at h1
    simp [nrm2] at h1
  have hp0 : p ≠ 0 := by
    intro h0
    apply hv0
    have e1 : om (k⁻¹, k'⁻¹) (om (k, k') vac) = vac := by
      rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]; rfl
    rw [hp, h0, zero_smul, map_zero] at e1
    exact e1.symm
  set L := om (k, k') ∘ₗ T₀ ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T k k') with hL
  have pm2 : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac (p⁻¹ • L) := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, pm.trans Ψ hΨ x hx, heisO_smul]
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, pm.modul Ψ hΨ y hy, heisO_smul]
    · rw [LinearMap.smul_apply, pm.vac, smul_smul, inv_mul_cancel₀ hp0, one_smul]
  have w1 : w = T₀ Φ := hall T₀ hT₀
  have w2 : w = (p⁻¹ • L) Φ := hall _ pm2

  have hfun : q • (fun t => Φ (actO S T k k' t)) = p • Φ := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hz : IsHalf e (actO S T k k' z)
    · have h1 := hq _ hz
      rw [GlobalTheory.SplitHecke.actO_inv_actO] at h1
      exact h1.symm
    · have h2 : Φ (actO S T k k' z) = 0 := by
        by_contra hne; exact hz (hΦ.1 _ hne)
      have h3 : Φ z = 0 := by
        by_contra hne; exact hz (GlobalTheory.SplitHecke.isHalf_actO k k' (hΦ.1 _ hne))
      rw [h2, h3, mul_zero, mul_zero]
  have eL : L Φ = om (k, k') (T₀ fun t => Φ (actO S T k k' t)) := rfl
  calc om (k, k') w = om (k, k') (T₀ Φ) := by rw [← w1]
    _ = p⁻¹ • om (k, k') (T₀ (p • Φ)) := by
        rw [map_smul, map_smul, smul_smul, inv_mul_cancel₀ hp0, one_smul]
    _ = p⁻¹ • om (k, k') (T₀ (q • fun t => Φ (actO S T k k' t))) := by rw [hfun]
    _ = q • (p⁻¹ • L) Φ := by
        rw [map_smul, map_smul, LinearMap.smul_apply, eL, smul_comm]
    _ = q • w := by rw [← w2]

end GlobalTheory.LevLaw
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilActionEqSmulOfKeepsLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

theorem _root_.GlobalTheory.T.weilAction_eq_smul_of_keeps_lattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ vac Φ w, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) vac → IsSBHalf e (stdHom S T) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac Φ w → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, (∀ x, x ∈ stdHom S T ↔ actO S T k k' x ∈ stdHom S T) → ∀ p q : ℂ, om (k, k') vac = p • vac → (∀ z, IsHalf e z → p * Φ (actO S T k⁻¹ k'⁻¹ z) = q * Φ z) → om (k, k') w = q • w := by
  first | exact @GlobalTheory.LevLaw.omega_eq_smul | exact GlobalTheory.LevLaw.omega_eq_smul | (intros; apply GlobalTheory.LevLaw.omega_eq_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelPairActionFiniteDatumLaw

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.LevLaw

theorem latFr_stdLat (D : D7) (S : HSp D) (a : ℕ) (hS : S.rank = a) :
    latFr S hS (Formalism.L2.Col.stdLat D.host.E a) = intVec D S.rank := by
  subst hS
  rw [GlobalTheory.LatPairMove.latFr_rfl, coe_colStdLat]

theorem mem_stdHom_iff_actO (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (k : GA D S) (k' : GA D T)
    (h1 : Moves S hS 1 (Formalism.L2.Col.stdLat D.host.E a)) (h1' : Moves T hT 1 (Formalism.L2.Col.stdLat D.host.E b))
    (hk : Moves S hS k (Formalism.L2.Col.stdLat D.host.E a)) (hk' : Moves T hT k' (Formalism.L2.Col.stdLat D.host.E b)) :
    ∀ x, x ∈ stdHom S T ↔ actO S T k k' x ∈ stdHom S T := by
  have key := GlobalTheory.LatPairMove.latO_move D S T a b hS hT 1 k 1 k' _ _ _ _ h1 h1' (by rwa [mul_one]) (by rwa [mul_one])
  rw [latFr_stdLat, latFr_stdLat] at key
  intro x
  constructor
  · intro hx
    exact (key _).2 ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨u₀, hu₀, he⟩ := (key _).1 hx
    have hinv : ∀ v, actO S T k⁻¹ k'⁻¹ (actO S T k k' v) = v := fun v => by
      have := GlobalTheory.AdelicLatMove.actO_actO_inv S T k⁻¹ k'⁻¹ v
      rwa [inv_inv, inv_inv] at this
    have := congrArg (actO S T k⁻¹ k'⁻¹) he
    rw [hinv, hinv] at this
    rw [this]
    exact hu₀

theorem lev_law : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) ψ θ x vac c₀ kom dd w Ram rd cK, PinX I l Z ψ θ x vac c₀ → PinColL A ι ψ θ x vac c₀ kom dd w Ram rd cK → ∀ j, j < B.R.m → ∀ α γ (κ : A.U j (ι j α)) (κ' : A.U (j + 1) (ι (j + 1) γ)), kom j (κ.1, κ'.1) (comb ψ _ _ (dd j α γ) (vac j)) = (((A.chi j _ κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) _ κ' : ℂˣ) : ℂ)) • comb ψ _ _ (dd j α γ) (vac j) := by
  intro B X I hI hP l Z u a Ch₀ Ch A ι ψ θ x vac c₀ kom dd w Ram rd cK hX hC j hj α γ κ κ'
  have hj1 : j + 1 ≤ B.R.m := hj
  have hstd := GlobalTheory.T.trueColumnSteps_are_standardHermitianPairs I hI hP l Z ψ θ hX.std hX.inf
  have hSP := hstd.1 j hj1
  obtain ⟨xr, hxr⟩ := hstd.2.2.2.2 _ κ.1
  obtain ⟨yr, hyr⟩ := hstd.2.2.2.2 _ κ'.1
  have hU := hC.is.U j (Nat.le_of_succ_le hj1) (ι j α)
  have hU' := hC.is.U (j + 1) hj1 (ι (j + 1) γ)
  have hkG : κ.1 ∈ GfC _ := ((hU κ.1).1 κ.2).1
  have hkG' : κ'.1 ∈ GfC _ := ((hU' κ'.1).1 κ'.2).1
  have h1G : (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) ∈ GfC _ := ((hU 1).1 (one_mem _)).1
  have h1G' : (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (j + 1))) ∈ GfC _ := ((hU' 1).1 (one_mem _)).1
  have hMk := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is j (Nat.le_of_succ_le hj1) (ι j α) κ.1 κ.2
  have hMk' := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is (j + 1) hj1 (ι (j + 1) γ) κ'.1 κ'.2
  have hM1 := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is j (Nat.le_of_succ_le hj1) (ι j α) 1 (one_mem _)
  have hM1' := GlobalTheory.T.chartLevels_keep_standardLattice I hI hP l Z u a Ch₀ A hC.is (j + 1) hj1 (ι (j + 1) γ) 1 (one_mem _)
  have hom := hC.om j hj
  have hVT := (hX.mv j hj1).2 a (A.chr (j + 1)) (kom j) (hC.is.chr ⟨j, hj⟩) hom
  have e1 := hVT κ.1 hkG κ'.1 hkG' _ _ hMk hMk' xr yr hxr hyr
  have e0 := hVT 1 h1G 1 h1G' _ _ hM1 hM1' 1 1 (GlobalTheory.SmallFix.isDetRoot_one _) (GlobalTheory.SmallFix.isDetRoot_one _)
  have h11 : kom j ((1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), (1 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (j + 1)))) = 1 :=
    map_one (kom j)
  set p : ℂ := ((A.chr (j + 1) xr : ℂ))⁻¹ * (A.chr (j + 1) yr : ℂ) with hpdef
  have hvth : IsThetaFunO ψ _ _ (vac j) := (hX.vc j hj).2.theta
  have hp : kom j (κ.1, κ'.1) (vac j) = p • vac j := by
    have hf : IsThetaFunO ψ _ _ (kom j (κ.1, κ'.1) (vac j) - p • vac j) :=
      GlobalTheory.AvgKill.theta_sub' (hom.om_pres _ _ hvth) (GlobalTheory.LocMod.LinSpace.isThetaFunO_smul p hvth)
    have hz : xiN θ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1)) (rankN (I.rec7 l Z) (j + 1) hj1) I.A.δ I.A.sc
        (kom j (κ.1, κ'.1) (vac j) - p • vac j) = 0 := by
      funext z
      have a1 := congrFun e1 z
      have a0 := congrFun e0 z
      rw [h11] at a0
      simp only [ColDat.xiS, xiN, Module.End.one_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply, map_one, Circle.coe_one, inv_one, mul_one] at a1 a0 ⊢
      rw [hpdef, mul_sub, show ∀ q r s : ℂ, q * (r * s) = r * (q * s) from fun q r s => by ring]
      erw [a1, a0]
      ring
    exact sub_eq_zero.1 ((GlobalTheory.T.gaussianTwistedRealReading_entire_and_injective _ ψ θ _ _ _ _ _ _ _ _ hSP).2 _ hf hz)
  obtain ⟨-, Φ, hΦ, hΞ, hth⟩ := hC.dat j hj1 α γ
  have hq : ∀ z, IsHalf A.e z → p * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z) =
      (((A.chi j _ κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) _ κ' : ℂˣ) : ℂ)) * Φ z := fun z hz =>
    GlobalTheory.T.finite_datum_law_under_two_chart_levels I hI hP l Z u a Ch₀ A hC.is j hj1 (ι j α) (ι (j + 1) γ) Φ hΦ (w j α γ) (fun z => hΞ z) κ κ' xr yr hxr hyr z hz
  have hlat := mem_stdHom_iff_actO (I.rec7 l Z) _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1))
    (rankN (I.rec7 l Z) (j + 1) hj1) κ.1 κ'.1 hM1 hM1' hMk hMk'
  exact GlobalTheory.T.weilAction_eq_smul_of_keeps_lattice (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj1)) (rankN (I.rec7 l Z) (j + 1) hj1)
    I.A.δ I.A.sc hSP (A.chr (j + 1)) (kom j) hom A.e _ hC.is.idem (vac j) Φ _ (hX.vc j hj) hΦ hth κ.1 hkG κ'.1 hkG' hlat p _ hp hq

end GlobalTheory.AdForm.LevLaw
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelPairActionFiniteDatumLawStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chartLevelPair_action_finiteDatum_law : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) ψ θ x vac c₀ kom dd w Ram rd cK, PinX I l Z ψ θ x vac c₀ → PinColL A ι ψ θ x vac c₀ kom dd w Ram rd cK → ∀ j, j < B.R.m → ∀ α γ (κ : A.U j (ι j α)) (κ' : A.U (j + 1) (ι (j + 1) γ)), kom j (κ.1, κ'.1) (comb ψ _ _ (dd j α γ) (vac j)) = (((A.chi j _ κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (j + 1) _ κ' : ℂˣ) : ℂ)) • comb ψ _ _ (dd j α γ) (vac j) := by
  first | exact @GlobalTheory.AdForm.LevLaw.lev_law | exact GlobalTheory.AdForm.LevLaw.lev_law | (intros; apply GlobalTheory.AdForm.LevLaw.lev_law <;> assumption)
end
end
