module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFullFaithfulnessLatticeMorphism
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEqMulKisinInfTameSemidirectStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinExactTripleJumpsCharactersLiftStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensorStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelLatticeMapKilledByPrimePowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleTameDescentGoodLatticeStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TameDescentExtendedActionExtraVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPreimageInvertedPrimeBreuilOfExactTriple
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionClassEqLPowSmulGaloisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionLatticeIsCrysTameTypeWithJumpsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveOfPhiModuleExactTripleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsExactTripleBreuilKisinOfShortExactLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomLiftsBreuilKisinDescentHomStatement
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationBounds

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentUnitLatticeDatum

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.UnitDatum


set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (Pk : Pack a ϖ η H (unitLat (Gl l) : QLat LL)), ∃ (u : ME Pk.D.toPhiMod) (x : ↥(unitLat (Gl l) : QLat LL).L.T), x.1 = (1 : ↥LL.1) ∧ u.1 ∈ Pk.D.Minv ∧ Pk.D.phi u.1 = u.1 ∧ toW (thetaW a LL) ϖ Pk.D.toPhiMod u = Pk.R.I.ofT x := by
  intro BS l _ a e _ _ ϖ LL _ _ η H Pk
  have hx : ((1 : ↥LL.1) : (unitLat (Gl l) : QLat LL).V) ∈ (unitLat (Gl l) : QLat LL).L.T := ⟨1, by simp⟩
  let x : ↥(unitLat (Gl l) : QLat LL).L.T := ⟨(1 : ↥LL.1), hx⟩
  let x' : ↥(resF (unitLat (Gl l) : QLat LL) (ϖ.field a)).L.T := ⟨(1 : ↥LL.1), hx⟩
  have hTriv : IsTriv (resF (unitLat (Gl l) : QLat LL) (ϖ.field a)) := fun _ _ => rfl
  let b : Module.Basis Unit ↥(OL LL) ↥(resF (unitLat (Gl l) : QLat LL) (ϖ.field a)).L.T :=
    ⟨(LinearEquiv.ofInjective (Algebra.linearMap ↥(OL LL) ↥LL.1) IsUnitBall.inj).symm.trans
      (Finsupp.LinearEquiv.finsuppUnique _ _ _).symm⟩
  have hb : b () = x' := by
    apply Subtype.ext
    change Algebra.linearMap ↥(OL LL) ↥LL.1 ((Finsupp.LinearEquiv.finsuppUnique ↥(OL LL) ↥(OL LL) Unit) (Finsupp.single () 1)) = 1
    rw [show (Finsupp.LinearEquiv.finsuppUnique ↥(OL LL) ↥(OL LL) Unit) (Finsupp.single () 1) = 1 from Finsupp.single_eq_same]
    simp
  have hBK := isBK_unitIdent (thetaW a LL) ϖ hTriv b
  have hBK' := Pk.isBK
  have h1 := GlobalTheory.BKReal.Full.main BS l a e (↥(OL LL)) (↥LL.1) (thetaW a LL) ϖ Unit (Fin Pk.n)
    (unitMod l a e ↥(OL LL) ↥LL.1 Unit) Pk.D.toPhiMod
  have h2 := h1 (resF (unitLat (Gl l) : QLat LL) (ϖ.field a)) (resF (unitLat (Gl l) : QLat LL) (ϖ.field a))
    (unitIdent (thetaW a LL) ϖ _ b)
  have h3 := h2 (Pk.R.I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _))
  have h4 := h3 hBK
  have h5 := h4 hBK' (latId _)
  obtain ⟨F, hF⟩ := h5
  have hev : (fun _ _ => (1 : (↥LL.1)⟦X⟧) : Vec (↥LL.1) a Unit) ∈ (unitMod l a e ↥(OL LL) ↥LL.1 Unit).M :=
    mem_tot.2 fun _ _ => one_mem _
  have huM : F.app (fun _ _ => (1 : (↥LL.1)⟦X⟧) : Vec (↥LL.1) a Unit) ∈ Pk.D.M := F.app_mem_M hev
  let u : ME Pk.D.toPhiMod := ⟨_, mem_ME_of_mem_M huM⟩
  have h0 : toW (thetaW a LL) ϖ (unitMod l a e ↥(OL LL) ↥LL.1 Unit) ⟨_, mem_ME_of_mem_M hev⟩ =
      (unitIdent (thetaW a LL) ϖ _ b).ofT x' := by
    apply (unitIdent (thetaW a LL) ϖ _ b).j.injective
    refine Eq.trans ?_ ((unitIdent (thetaW a LL) ϖ _ b).j_ofT x').symm
    rw [unitIdent_j, Fintype.sum_unique, hb]
    congr 1
    rw [toW_apply, ← map_one (ϖ.iW (thetaW a LL) ↥LL.1)]
    exact congrArg _ (funext fun _ => Subtype.ext rfl)
  have h6 := homW_toW (thetaW a LL) ϖ F ⟨_, mem_ME_of_mem_M hev⟩
  have key : toW (thetaW a LL) ϖ Pk.D.toPhiMod u = Pk.R.I.ofT x :=
    h6.symm.trans ((congrArg (homW (thetaW a LL) ϖ F) h0).trans (IsMapOf.homW_ofT hF x'))
  refine ⟨u, x, rfl, (Descent.mem_invOf _).2 ⟨huM, fun γ => ?_⟩, ?_, key⟩
  · obtain ⟨k, -, hk⟩ := (GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL).2.2.1 γ
    have hkG : k ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
      intro y
      obtain ⟨y, hy⟩ := y
      obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hy
      exact k.commutes c
    have hv' : Pk.D.desc.act γ u.1 ∈ ME Pk.D.toPhiMod := mem_ME_of_mem_M (Pk.D.desc.act_mem_M γ _ huM)
    have h := Pk.R.desc ⟨k, hkG⟩ γ hk u ⟨_, hv'⟩ rfl
    have hx' : (unitLat (Gl l) : QLat LL).actT ⟨k, hkG⟩ x = x := Subtype.ext rfl
    have h10 : toW (thetaW a LL) ϖ Pk.D.toPhiMod ⟨_, hv'⟩ = toW (thetaW a LL) ϖ Pk.D.toPhiMod u :=
      h.symm.trans ((congrArg (Pk.R.I.act (sQ l ⟨k, hkG⟩) ⟨k, hkG⟩) key).trans
        ((Pk.R.I.act_ofT (sQ l ⟨k, hkG⟩) ⟨k, hkG⟩ x).trans ((congrArg Pk.R.I.ofT hx').trans key.symm)))
    exact congrArg Subtype.val (toW_injective (thetaW a LL) ϖ Pk.D.toPhiMod h10)
  · have h7 := toW_phi (thetaW a LL) ϖ Pk.D.toPhiMod huM
    have h8 : phiW (thetaW a LL) ϖ Pk.D.toPhiMod (Pk.R.I.ofT x) = Pk.R.I.ofT x := by
      rw [← mem_Treal, ← Pk.R.I.range_ofT]
      exact LinearMap.mem_range_self Pk.R.I.ofT x
    have h9 : toW (thetaW a LL) ϖ Pk.D.toPhiMod ⟨Pk.D.phi u.1, mem_ME_of_mem_L (Pk.D.phi_mem_L huM)⟩ =
        toW (thetaW a LL) ϖ Pk.D.toPhiMod u :=
      h7.trans ((congrArg (phiW (thetaW a LL) ϖ Pk.D.toPhiMod) key).trans (h8.trans key.symm))
    exact congrArg Subtype.val (toW_injective (thetaW a LL) ϖ Pk.D.toPhiMod h9)

end GlobalTheory.BKGal.UnitDatum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentUnitLatticeDatumStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.breuilKisinDescent_unitLattice_datum : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (Pk : Pack a ϖ η H (unitLat (Gl l) : QLat LL)), ∃ (u : ME Pk.D.toPhiMod) (x : ↥(unitLat (Gl l) : QLat LL).L.T), x.1 = (1 : ↥LL.1) ∧ u.1 ∈ Pk.D.Minv ∧ Pk.D.phi u.1 = u.1 ∧ toW (thetaW a LL) ϖ Pk.D.toPhiMod u = Pk.R.I.ofT x := by
  first | exact @GlobalTheory.BKGal.UnitDatum.main | exact GlobalTheory.BKGal.UnitDatum.main | (intros; apply GlobalTheory.BKGal.UnitDatum.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPreimageInvertedPrimeBreuilOfExactTripleStatement

section

@[expose] public section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.exists_preimage_invertedPrime_breuil_of_exactTriple : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NeZero e] [NormedAlgebra ℚ_[l] K] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : Hom P Q) (G : Hom Q T), IsExactTriple F G → ∀ v ∈ Q.ext (invL l (S O K e)), G.app v = 0 → ∃ w ∈ P.ext (invL l (S O K e)), F.app w = v := by
  first | exact @GlobalTheory.BK.exists_preimage_invL_S_of_exactTriple | exact GlobalTheory.BK.exists_preimage_invL_S_of_exactTriple | (intros; apply GlobalTheory.BK.exists_preimage_invL_S_of_exactTriple <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineClassFromMonodromyKernelElement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.ExtClass

theorem lift_phi_sub {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ]
    [DecidableEq μ] {η H : ℕ} {D₀ : BKDat O K l e a ι η H} {D₁ : BKDat O K l e a κ η H}
    {D₂ : BKDat O K l e a μ η H} (F : BKHom D₀ D₁) (G : BKHom D₁ D₂) (hex : IsExactTriple F.toHom G.toHom)
    {x : Vec K a κ} (hx : x ∈ D₁.Minv) (hG : G.app (D₁.phi x - x) = 0) :
    ∃ y ∈ D₀.Y, F.app y = D₁.phi x - x ∧ D₀.Mon y = 0 := by
  have hL : D₁.phi x ∈ D₁.L := D₁.phi_mem_L hx.1
  have hM : E K l e ^ η • (D₁.phi x - x) ∈ D₁.M := by
    rw [smul_sub]
    exact sub_mem (D₁.upper _ hL) (D₁.M.smul_mem (EIn l e (A O K) ^ η) hx.1)
  have hG0 : G.app (E K l e ^ η • (D₁.phi x - x)) = 0 := by rw [map_smul, hG, smul_zero]
  obtain ⟨w, hw, hFw⟩ := (hex.exact _ hM).1 hG0
  have hu : IsUnit (E K l e ^ η) := (isUnit_E l e).pow η
  set y₀ := Ezpow K l e (-(η : ℤ)) • w with hy₀def
  have hE : E K l e ^ η • y₀ = w := by
    rw [hy₀def, smul_smul, E_pow_mul_Ezpow_neg, one_smul]
  have hFy₀ : F.app y₀ = D₁.phi x - x := by
    refine (hu.smul_left_cancel).1 ?_
    rw [← map_smul, hE]
    exact hFw
  have hy₀ : y₀ ∈ D₀.EM η := by
    rw [mem_divE, hE]
    exact hw
  have hinj : ∀ v ∈ D₀.EM η, F.app v = 0 → v = 0 := fun v hv h =>
    (hu.smul_left_cancel).1 (by
      rw [smul_zero]
      exact hex.inj _ hv (by rw [map_smul, h, smul_zero]))
  have hinv2 : ∀ g, D₁.desc.act g (D₁.phi x - x) = D₁.phi x - x := fun g => by
    rw [map_sub, D₁.desc.act_phi, hx.2 g]
  refine ⟨y₀, ⟨hy₀, fun g => ?_⟩, hFy₀, ?_⟩
  · rw [← sub_eq_zero]
    refine hinj _ (sub_mem (D₀.desc.act_mem_EM g hy₀) hy₀) ?_
    rw [map_sub, F.app_act, hFy₀, hinv2, sub_self]
  · refine (GlobalTheory.T.breuilKisin_exactTriple_jumps_characters_lift O K l e a ι κ μ η H D₀ D₁ D₂ F G hex).2.2.1 ?_
    rw [map_zero, Hom.onPol_Mon, hFy₀, PhiMod.Mon_phi_sub,
      (D₁.cls_eq_zero_iff).2 (D₁.EN_mem_Man (D₁.M_le_Man hx.1)), neg_zero]

end GlobalTheory.BKGal.ExtClass

namespace GlobalTheory.BKGal.ExtClass

theorem xi_red_of_phi_eq {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PhiMod O K l e a ι) {u : Vec K a ι} (hu : P.phi u = u) : P.xi (red u) = u := by
  have := P.raises_phi.eq_zero (α := Unit) (σ := id) Function.surjective_id
    (δ := fun _ => u - P.xi (red u)) (fun _ => by rw [mem_uPow_one, map_sub, PhiMod.red_xi, sub_self])
    (fun _ => by rw [map_sub, hu, PhiMod.phi_xi, ← PhiMod.red_phi, hu]) ()
  exact (sub_eq_zero.1 this).symm



theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig U → ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∀ Pk : Pack a ϖ η H T, ∀ c ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, ∃ y ∈ Pk.D.Y, Pk.D.Mon y = 0 ∧ Pk.R.ClassOf y ((l : ↥LL.1) ^ GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig) • c) := by
  intro hBS hFB l _ a e _ _ ϖ LL _ _ Pl AI hStd N η H Sig U hN T hT Pk c hc
  have hl2 : l ≠ 2 := by
    have h1 := hN.large
    have h2 := hN.two_le
    rintro rfl
    have : 8 ≤ N ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ N ^ 3 := Nat.pow_le_pow_left h2 3
    omega
  obtain ⟨hUnit, hExt⟩ := GlobalTheory.T.extensionLattice_isCrysTameTypeWithJumps hFB l a e ϖ LL Pl AI hStd Sig U hN.zero_mem_Sig hN.zero_mem_U
  obtain ⟨Tp, f, g, v, hfg, hv, hgv, hcv, hTp⟩ := hExt T hT c hc
  obtain ⟨Pp, hPp⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFB l a e ϖ LL hl2 Pl AI hStd η H Sig U hN.range_U Tp hTp
  obtain ⟨Pu, hPu⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFB l a e ϖ LL hl2 Pl AI hStd η H Sig U hN.range_U _ hUnit
  obtain ⟨F, hF⟩ := GlobalTheory.T.latticeHom_lifts_breuilKisinDescentHom hBS l a e ϖ LL η H T Tp Pk Pp f
  have hG' := GlobalTheory.T.latticeHom_lifts_breuilKisinDescentHom hBS l a e ϖ LL η H Tp (unitLat (Gl l) : QLat LL) Pp Pu g
  obtain ⟨G, hG⟩ := hG'
  have hex : IsExactTriple F.toHom G.toHom :=
    GlobalTheory.T.isExactTriple_breuilKisin_of_shortExactLattices l a e ϖ LL _ _ _ Pk.D.toPhiMod Pp.D.toPhiMod Pu.D.toPhiMod T Tp (unitLat (Gl l) : QLat LL) Pk.R.I Pp.R.I Pu.R.I f g
      F.toHom G.toHom hfg hF hG
  have hB : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Bounds l e Sig U N η H :=
    ⟨hN.frob_mem, hN.zero_mem_Sig, hN.card_Sig, hN.two_le, hN.range_U, hN.zero_mem_U, hN.card_U, hN.one_le,
      hN.lt, hN.large⟩
  have hK := GlobalTheory.T.cokernel_latticeMap_killed_by_prime_pow (↥(OL LL)) (↥LL.1) l e a (Fin Pp.n) (Fin Pu.n) Sig U N η H hB Pp.D Pu.D hPp
    hPu.chars_subset G hex.finiteLength
  obtain ⟨u, x, hx1, hu, hφu, hux⟩ := GlobalTheory.T.breuilKisinDescent_unitLattice_datum hBS l a e ϖ LL η H Pu
  obtain ⟨x₂, hx₂, hGx₂⟩ := hK.2.2.2.1 u.1 hu
  have hG0 : G.app (Pp.D.phi x₂ - x₂) = 0 := by
    rw [map_sub, G.toHom.app_phi, hGx₂, map_nsmul, hφu, sub_self]
  obtain ⟨y, hy, hFy, hMon⟩ := lift_phi_sub F G hex hx₂ hG0
  refine ⟨y, hy, hMon, ?_⟩
  have hFinj := GlobalTheory.T.injective_of_phiModule_exact_triple _ _ _ _ _ _ _ _ _ _ _ F.toHom G.toHom hex
  set d := red (Pp.D.phi x₂) with hd
  have hL : Pp.D.phi x₂ ∈ Pp.D.L := Pp.D.phi_mem_L hx₂.1
  have hσp : Pp.D.phi x₂ - Pp.D.xi d ∈ Pp.D.MMl := by
    refine sub_mem (Pp.D.ext_mono ((A_le_S l e).trans (le_away _ _)) hL) ?_
    rw [PhiMod.xi_apply]
    refine ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor (↥(OL LL)) (↥LL.1) l e a (Fin Pp.n) Pp.D.toPhiMod).2 _).2 ?_
    exact mem_tot.2 fun τ i => by
      rw [cst_apply]
      exact HasK.C_mem _
  have hGσ : G.app (Pp.D.phi x₂ - Pp.D.xi d) = 0 := by
    rw [map_sub, Hom.app_xi, hd, ← Hom.red_app, G.toHom.app_phi, hGx₂, map_nsmul, hφu, map_nsmul, map_nsmul,
      xi_red_of_phi_eq _ hφu, sub_self]
  obtain ⟨σ, hσ, hFσ⟩ := GlobalTheory.T.exists_preimage_invertedPrime_breuil_of_exactTriple _ _ _ _ _ _ _ _ _ _ _ F.toHom G.toHom hex _ hσp hGσ
  have hσinv : σ ∈ Pk.D.desc.inv := fun γ => hFinj (by
    rw [F.app_act, hFσ, map_sub, Pp.D.desc.act_phi, hx₂.2 γ, Descent.act_xi, hd, ← Descent.red_act,
      Pp.D.desc.act_phi, hx₂.2 γ])
  exact GlobalTheory.T.extensionClass_eq_lPow_smul_galois l a e ϖ LL η H T Tp f g hfg Pk Pp Pu F G hF hG hex hFinj u x hx1 hu hφu hux
    (GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) x₂ hx₂ hGx₂ v c hv hgv hcv σ hσ hσinv hFσ y hy hFy

end GlobalTheory.BKGal.ExtClass
end
end
