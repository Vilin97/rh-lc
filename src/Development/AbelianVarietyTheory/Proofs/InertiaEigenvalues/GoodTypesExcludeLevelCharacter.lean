module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentMulMirabolicDetAverageEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteSpaceFormsFunctionalPrincipalTypeStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterLabelRootOfHarishChandraConstituent
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrrHarishChandraInductionThetaInvDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorConvMirabolicAvgEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesCentralIdempotentLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMirabolicDetAverageEqHarishChandraRestrictiStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMirabolicDetCharacterAverageVectorIndep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExistStatement
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterLabelRootOfHarishChandraConstituentStatement

section

@[expose] public section

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

theorem _root_.GlobalTheory.T.detCharacterLabel_root_of_harishChandraConstituent : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (ψ : Gn g (n + 1) → ℂ) (f : (ZMod g)[X]), IsIrr ψ →
    HasLabel L ψ f → ∀ (σ : Gn g n → ℂ), IsIrr σ → ∀ (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g), GlobalTheory.GLp.IsCharLab L θ c →
    (ip ψ (hc n 1 σ (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (n + 1)) ≠ 0 → f.IsRoot c) ∧
    (ip ψ (hc 1 n (fun y : Gn g 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) σ (n + 1)) ≠ 0 → f.IsRoot c) := by
  first | exact @GlobalTheory.GLq.DetRoot.root_of_hc_det | exact GlobalTheory.GLq.DetRoot.root_of_hc_det | (intros; apply GlobalTheory.GLq.DetRoot.root_of_hc_det <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrrHarishChandraInductionThetaInvDetStatement

section

@[expose] public section

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

theorem _root_.GlobalTheory.T.exists_irr_harishChandraInduction_thetaInv_det : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsIrr ψ → ∀ θ : (ZMod g)ˣ →* ℂˣ,
    (∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res n 1 ψ 1 x ≠ 0 →
      ∃ σ : Gn g n → ℂ, IsIrr σ ∧
        ip ψ (hc n 1 σ (fun y : Gn g 1 => ((θ⁻¹ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (n + 1)) ≠ 0) ∧
    (∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res 1 n ψ x 1 ≠ 0 →
      ∃ σ : Gn g n → ℂ, IsIrr σ ∧
        ip ψ (hc 1 n (fun y : Gn g 1 => ((θ⁻¹ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) σ (n + 1)) ≠ 0) := by
  first | exact @GlobalTheory.GLq.HCFrobWeight.exists_irr_hc_thetaInv | exact GlobalTheory.GLq.HCFrobWeight.exists_irr_hc_thetaInv | (intros; apply GlobalTheory.GLq.HCFrobWeight.exists_irr_hc_thetaInv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMirabolicDetCharacterAverageVectorIndepStatement

section

@[expose] public section

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

theorem _root_.GlobalTheory.T.trace_mirabolicDetCharacterAverage_vector_indep : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsClass ψ → ∀ (θ : (ZMod g)ˣ →* ℂˣ)
    (a : Fin (n + 1) → ZMod g), a ≠ 0 → ∀ b : Bool,
      tr (mirEl θ a b) ψ = tr (mirEl θ (if b then Pi.single 0 1 else Pi.single (Fin.last n) 1) b) ψ := by
  first | exact @GlobalTheory.MirAvg.tr_mirEl_indep | exact GlobalTheory.MirAvg.tr_mirEl_indep | (intros; apply GlobalTheory.MirAvg.tr_mirEl_indep <;> assumption)
end
end

-- Source module: Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqAct

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Lev

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

theorem levFn_flag_one : Formalism.L2.DIV.levFn β (flagL L) 1 = 1 := by
  have h1 : (1 : GL (Fin V.rank) (EAf D)) ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) := Subgroup.one_mem _
  exact (Formalism.L2.DIV.levChar D.sp.cm V.gram β (flagL L)).map_one

theorem levFn_conj {x y : GL (Fin V.rank) (EAf D)} (hx : x ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L)
    (hy : y ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L) :
    Formalism.L2.DIV.levFn β (flagL L) (x⁻¹ * y * x) = Formalism.L2.DIV.levFn β (flagL L) y := by
  have hxi : x⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := Subgroup.inv_mem _ hx
  have hxy : x⁻¹ * y ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := Subgroup.mul_mem _ hxi hy
  rw [levFn_flag_mul hxy hx, levFn_flag_mul hxi hy]
  have e : Formalism.L2.DIV.levFn β (flagL L) x⁻¹ * Formalism.L2.DIV.levFn β (flagL L) x = 1 := by
    rw [← levFn_flag_mul hxi hx, inv_mul_cancel, levFn_flag_one]
  calc Formalism.L2.DIV.levFn β (flagL L) x⁻¹ * Formalism.L2.DIV.levFn β (flagL L) y * Formalism.L2.DIV.levFn β (flagL L) x
      = Formalism.L2.DIV.levFn β (flagL L) y * (Formalism.L2.DIV.levFn β (flagL L) x⁻¹ * Formalism.L2.DIV.levFn β (flagL L) x) := by
        rw [mul_comm (Formalism.L2.DIV.levFn β (flagL L) x⁻¹), mul_assoc]
    _ = Formalism.L2.DIV.levFn β (flagL L) y := by rw [e, mul_one]

theorem mem_levG_flag1 {k : GA D V} :
    k ∈ levG V β (flag1L L) ↔ k ∈ GfC V ∧ finE V k ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L ∧
      Formalism.L2.DIV.rTup β L (finE V k) = 1 := by
  show (k ∈ GfC V ∧ (finE V k ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L ∧
      Formalism.L2.DIV.rTup β L (finE V k) ∈ (⊥ : Subgroup (Formalism.L2.DIV.G0 L.Pg L.r)))) ↔ _
  rw [Subgroup.mem_bot]

theorem levChi_flag1 (k : GA D V) : levChi V β (flag1L L) k = levChi V β (flagL L) k := by
  unfold levChi; rw [levFn_flag1]

theorem hasType_rTrc {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) {κ : GA D V} (hκ : κ ∈ GfC V)
    (hκ' : finE V κ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L) (c : ℂ) :
    HasType V β (flag1L L) (fun h => c * F (h * κ)) := by
  intro k hk h
  obtain ⟨hk1, hk2, hk3⟩ := mem_levG_flag1.1 hk
  have hki : (finE V κ)⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := Subgroup.inv_mem _ hκ'
  have hm1 : (finE V κ)⁻¹ * finE V k ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := Subgroup.mul_mem _ hki hk2
  have hk' : κ⁻¹ * k * κ ∈ levG V β (flag1L L) := by
    refine mem_levG_flag1.2 ⟨?_, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hκ) hk1) hκ
    · rw [map_mul, map_mul, map_inv]; exact Subgroup.mul_mem _ hm1 hκ'
    · rw [map_mul, map_mul, map_inv, Formalism.L2.DIV.rTup_mul hm1 hκ', Formalism.L2.DIV.rTup_mul hki hk2,
        Formalism.L2.DIV.rTup_inv hκ', hk3, mul_one, inv_mul_cancel]
  have e1 := hF _ hk' (h * κ)
  rw [show h * κ * (κ⁻¹ * k * κ) = h * k * κ by group] at e1
  have e2 : levChi V β (flag1L L) (κ⁻¹ * k * κ) = levChi V β (flag1L L) k := by
    rw [levChi_flag1, levChi_flag1]
    unfold levChi
    rw [map_mul, map_mul, map_inv, levFn_conj hκ' hk2]
  show c * F (h * k * κ) = levChi V β (flag1L L) k * (c * F (h * κ))
  rw [e1, e2]; ring

theorem level_action_eq_lift {g0 : Formalism.L2.DIV.G0 L.Pg L.r} {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) {κ : GA D V}
    (hκ : IsLevelLift V β L g0 κ) : actG0 V β L g0 F = fun h => (levChi V β (flagL L) κ)⁻¹ * F (h * κ) := by
  funext h
  exact level_action_spec hF ⟨κ, hκ⟩ κ hκ h

theorem has_type_of_level_action (hL : LiftsExist V β L) (g0 : Formalism.L2.DIV.G0 L.Pg L.r) {F : GA D V → ℂ}
    (hF : HasType V β (flag1L L) F) : HasType V β (flag1L L) (actG0 V β L g0 F) := by
  obtain ⟨κ, hκ⟩ := hL g0
  rw [level_action_eq_lift hF hκ]
  exact hasType_rTrc hF hκ.1 hκ.2.1 _

theorem levelGroupAction_mul_of_lifts (hL : LiftsExist V β L) (g1 g2 : Formalism.L2.DIV.G0 L.Pg L.r) {F : GA D V → ℂ}
    (hF : HasType V β (flag1L L) F) : actG0 V β L g1 (actG0 V β L g2 F) = actG0 V β L (g1 * g2) F := by
  obtain ⟨κ1, hκ1⟩ := hL g1
  obtain ⟨κ2, hκ2⟩ := hL g2
  have h12 : IsLevelLift V β L (g1 * g2) (κ1 * κ2) := by
    refine ⟨Subgroup.mul_mem _ hκ1.1 hκ2.1, ?_, ?_⟩
    · rw [map_mul]; exact Subgroup.mul_mem _ hκ1.2.1 hκ2.2.1
    · rw [map_mul, Formalism.L2.DIV.rTup_mul hκ1.2.1 hκ2.2.1, hκ1.2.2, hκ2.2.2]
  have hF2 := has_type_of_level_action hL g2 hF
  rw [level_action_eq_lift hF2 hκ1, level_action_eq_lift hF h12, level_action_eq_lift hF hκ2]
  funext h
  have e : levChi V β (flagL L) (κ1 * κ2) = levChi V β (flagL L) κ1 * levChi V β (flagL L) κ2 := by
    unfold levChi; rw [map_mul, levFn_flag_mul hκ1.2.1 hκ2.2.1, Units.val_mul]
  have ha := levChi_ne_zero (β := β) (flagL L) κ1
  have hb := levChi_ne_zero (β := β) (flagL L) κ2
  simp only [e, mul_assoc]
  field_simp

end Formalism.IndefR.Eqv.Act

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypesExcludeLevelCharacter

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.GoodTypeNoChi

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

theorem p_comp : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank),
    LiftsExist V β L → ∀ {G : Type} [Group G] [Fintype G] (eG : G ≃* Formalism.L2.DIV.G0 L.Pg L.r) (c c' : G → ℂ) (F : GA D V → ℂ),
    HasType V β (flag1L L) F →
      gaL V β L eG c (gaL V β L eG c' F) = gaL V β L eG (fun x => ∑ y, c y * c' (y⁻¹ * x)) F := by
  intro D V β L hL G _ _ eG c c' F hF
  have hm : ∀ y z : G, actL V β L (eG y) (actL V β L (eG z) F) = actL V β L (eG (y * z)) F := fun y z => by
    rw [map_mul]
    exact Formalism.IndefR.Eqv.Act.levelGroupAction_mul_of_lifts hL (eG y) (eG z) hF
  have lhs : gaL V β L eG c (gaL V β L eG c' F) =
      ∑ y : G, ∑ z : G, (c y * c' z) • actL V β L (eG (y * z)) F := by

    simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hm, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    rw [mul_comm]
  have rhs : gaL V β L eG (fun x => ∑ y, c y * c' (y⁻¹ * x)) F =
      ∑ y : G, ∑ x : G, (c y * c' (y⁻¹ * x)) • actL V β L (eG x) F := by
    simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_smul]
    exact Finset.sum_comm
  rw [lhs, rhs]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun z => by simp

theorem p_lifts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 →
    ∀ (i : Fin D.R.m) (t : T), LiftsExist (Vc D i) (R.βV i) (R.datVt i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h i t
  obtain ⟨c, hc⟩ := h.βV i
  refine GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_)
    (GlobalTheory.LevelRamif.ramif_at_levels D T R.toLevCh A.μ0 h t i).1
  obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
  rcases hP' with hP' | hP'
  · obtain ⟨k', hk'⟩ := (h.Pg PP').1 hP'
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  · intro hc
    obtain ⟨q, hq, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (h.Q_pl t) hP'
    exact GlobalTheory.LevelRamif.not_two_primes PP' hq (D.host.g_prime k) (hne k) hm
      (GlobalTheory.LevelRamif.natCast_mem_conj hc (GlobalTheory.LevelRamif.typePrime_mem hk))

theorem isClass_irr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, -, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem charLab_inv {g : ℕ} [Fact g.Prime] {L : LabelDatum g} {θ : (ZMod g)ˣ →* ℂˣ} {c : ZMod g}
    (h : GlobalTheory.GLp.IsCharLab L θ c) : GlobalTheory.GLp.IsCharLab L θ⁻¹ c⁻¹ := by
  obtain ⟨hc, hv⟩ := h
  refine ⟨inv_ne_zero hc, fun u hu => ?_⟩
  have e1 : ((θ⁻¹ u : ℂˣ) : ℂ) = ((θ u : ℂˣ) : ℂ)⁻¹ := by simp
  have hx : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective]
  have e2 : L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c⁻¹) = (L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c))⁻¹ := by
    rw [map_inv₀]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  rw [e1, hv u hu, e2]

theorem seriesKillsAvg : SeriesKillsAvg := by
  intro g _ L r f θ c hc hf hf' a b ha
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := by
    cases r with
    | zero => exact absurd (_root_.funext fun i : Fin 0 => Fin.elim0 i) ha
    | succ n => exact ⟨n, rfl⟩
  obtain ⟨hfin, -⟩ := irr_finite_and_finsum_zOf_eq_one (Gn g (n + 1))
  rw [eSerC_eq_sum L (n + 1) hfin f, Finset.sum_mul]
  refine Finset.sum_eq_zero fun ψ hψ => ?_
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hψ
  obtain ⟨hirr, hlab⟩ := hψ
  apply GlobalTheory.T.centralIdempotent_mul_mirabolicDetAverage_eq_zero g (n + 1) ψ hirr θ a b
  rw [GlobalTheory.T.trace_mirabolicDetCharacterAverage_vector_indep g n ψ (isClass_irr hirr) θ a ha b]
  have hinv := charLab_inv hc
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [(GlobalTheory.T.trace_mirabolicDetAverage_eq_harishChandraRestriction g n ψ θ).1]
    by_contra hne
    obtain ⟨σ, hσ, hip⟩ := (GlobalTheory.T.exists_irr_harishChandraInduction_thetaInv_det g n ψ hirr θ).1 (right_ne_zero_of_mul hne)
    exact hf' ((GlobalTheory.T.detCharacterLabel_root_of_harishChandraConstituent g L n ψ f hirr hlab σ hσ θ⁻¹ c⁻¹ hinv).1 hip)
  · simp only [if_true]
    rw [(GlobalTheory.T.trace_mirabolicDetAverage_eq_harishChandraRestriction g n ψ θ).2]
    by_contra hne
    obtain ⟨σ, hσ, hip⟩ := (GlobalTheory.T.exists_irr_harishChandraInduction_thetaInv_det g n ψ hirr θ).2 (right_ne_zero_of_mul hne)
    exact hf' ((GlobalTheory.T.detCharacterLabel_root_of_harishChandraConstituent g L n ψ f hirr hlab σ hσ θ⁻¹ c⁻¹ hinv).2 hip)

theorem goodNoChi : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GoodNoChi R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t
  have hc : GlobalTheory.Hk3.Core R F := hG.core
  have hl : R.toLevCh.Is A.μ0 := hc.lev
  have hL : LiftsExist (Vc D i) (R.βV i) (R.datVt i t) := p_lifts D G Pl0 T A Ks R hl i t
  intro y hy PP a ha b ε hε l
  have hT : HasType (Vc D i) (R.βV i) (flag1L (R.datVt i t)) (fun h => l (R.extV i t y h)) :=
    GlobalTheory.T.definiteSpace_forms_functional_principalType D G Pl0 T A Ks R F hc i t y l
  have hy' := hy l
  have e1 := p_comp _ _ _ hL R.eG (mirC R i PP a b ε) (RealDat.eC (A := A) (sg0 D A)) _ hT
  have e0 := congrArg (gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG (mirC R i PP a b ε)) hy'
  have h0 : (fun x => ∑ y, mirC R i PP a b ε y * RealDat.eC (A := A) (sg0 D A) (y⁻¹ * x)) = fun _ => 0 :=
    funext (GlobalTheory.T.goodProjector_conv_mirabolicAvg_eq_zero seriesKillsAvg D G Pl0 T A Ks R F hG i PP a ha b ε hε)
  have e2 := congrArg (fun c => gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG c (fun h => l (R.extV i t y h))) h0
  have e3 : gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG (fun _ : G => (0 : ℂ)) (fun h => l (R.extV i t y h)) = 0 := by
    simp only [gaL, zero_smul, Finset.sum_const_zero, LinearMap.zero_apply]
  exact e0.symm.trans (e1.trans (e2.trans e3))

end GlobalTheory.GoodTypeNoChi

end
end
end
