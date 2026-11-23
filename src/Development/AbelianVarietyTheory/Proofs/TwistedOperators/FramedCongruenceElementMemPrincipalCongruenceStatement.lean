module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOffStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.QuotientMetricDivisors.Statement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameCongruentSubOneMulVecMemIdealLatticeCompletStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqOfTwoOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPlNeOfIsSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegerOutsidePrimePowDvdMaximalIdealPowStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubMemLatticeCompletionOfSupportedPlacesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPlaceIdealMulLatticeCompletionEq

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

noncomputable section

namespace GlobalTheory.ConjPlaceLat



theorem cA_mul_mem_latV_smul : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (w : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e w →
  ∀ (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (𝔪 : Ideal (𝓞 D.host.E)), (∃ m ∈ 𝔪, m ∉ (Formalism.DivisionValues.conjPl w).asIdeal) →
  ∀ z : Fin S.rank → AE D, z ∈ latV S L (· = p.v) → (fun i => cA D p.e * z i) ∈ latV S (𝔪 • L) (· = p.v) := by
  intro D k _ _ _ _ p w hw S L 𝔪 hm z hz
  obtain ⟨m, hm𝔪, hmw⟩ := hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hmw (Ideal.zero_mem _)
  have hmE : (m : D.host.E) ≠ 0 := by exact_mod_cast hm0
  have hc := GlobalTheory.SplitHeckeAdj.idem_conj S hw
  have hu : finPart D (cA D p.e * incA D ((m : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hmw ((hc.2 m hm0).2 h)
  have h1 : ∀ y ∈ latV S L (· = p.v), (fun i => incA D (m : D.host.E) * y i) ∈ latV S (𝔪 • L) (· = p.v) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      refine AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, m • x, Submodule.smul_mem_smul hm𝔪 hx, ?_⟩
      funext i
      show (1 : AF D.host.F) ⊗ₜ[D.host.F] (m : D.host.E) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, one_mul, Pi.smul_apply, Algebra.smul_def]
    | zero =>
      convert zero_mem (latV S (𝔪 • L) (· = p.v)) using 1
      funext i
      simp
    | add y y' _ _ h h' =>
      convert add_mem h h' using 1
      funext i
      simp [mul_add]
    | neg y _ h =>
      convert neg_mem h using 1
      funext i
      simp
  have key : (fun i => cA D p.e * z i) =
      fun i => cA D p.e * incA D ((m : D.host.E)⁻¹) * (incA D (m : D.host.E) * z i) := by
    funext i
    rw [mul_assoc, ← mul_assoc (incA D _), ← map_mul, inv_mul_cancel₀ hmE, map_one, one_mul]
  rw [key]
  exact GlobalTheory.FinPl.LatIndHalf.mul_mem_latV hu (h1 z hz)

end GlobalTheory.ConjPlaceLat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPlaceIdealMulLatticeCompletionEqStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

theorem _root_.GlobalTheory.T.cA_smul_mem_latV_ideal_smul_of_conj_place : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (w : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e w →
  ∀ (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (𝔪 : Ideal (𝓞 D.host.E)), (∃ m ∈ 𝔪, m ∉ (Formalism.DivisionValues.conjPl w).asIdeal) →
  ∀ z : Fin S.rank → AE D, z ∈ latV S L (· = p.v) → (fun i => cA D p.e * z i) ∈ latV S (𝔪 • L) (· = p.v) := by
  first | exact @GlobalTheory.ConjPlaceLat.cA_mul_mem_latV_smul | exact GlobalTheory.ConjPlaceLat.cA_mul_mem_latV_smul | (intros; apply GlobalTheory.ConjPlaceLat.cA_mul_mem_latV_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridModulusExactOrderWitness

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
namespace GlobalTheory.ChiGrid.GridData

theorem modul_witness : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), ∀ v ∈ G.pl.S0,
  (∃ m ∈ G.modul, m ∉ (G.pl.w v).asIdeal ^ (G.pl.depth sc v + 1)) ∧ ∃ m ∈ G.modul, m ∉ (Formalism.DivisionValues.conjPl (G.pl.w v)).asIdeal := by
  intro D T L sc G v hv
  classical
  obtain ⟨e, he⟩ := G.pl.w_split v (Finset.mem_insert.2 (G.pl.mem_S0_of_sum_eq.1 hv))
  have hconj : Formalism.DivisionValues.conjPl (G.pl.w v) ≠ G.pl.w v := GlobalTheory.ModulusNorm.conjPl_ne_of_isIdemAt he

  have eqOf : ∀ (v' : HeightOneSpectrum (𝓞 D.host.F)) (Q : HeightOneSpectrum (𝓞 D.host.E)),
      (G.pl.w v').asIdeal ≤ Q.asIdeal → G.pl.w v' = Q := fun v' Q h =>
    HeightOneSpectrum.ext ((G.pl.w v').isMaximal.eq_of_le Q.isPrime.ne_top h)
  have hmod : G.modul = ∏ v' ∈ G.pl.S0, (G.pl.w v').asIdeal ^ G.pl.depth sc v' := rfl
  refine ⟨?_, ?_⟩
  · by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hle : G.modul ≤ (G.pl.w v).asIdeal ^ (G.pl.depth sc v + 1) := fun m hm => hcon m hm
    rw [hmod, ← Finset.mul_prod_erase _ _ hv] at hle
    set J := ∏ v' ∈ G.pl.S0.erase v, (G.pl.w v').asIdeal ^ G.pl.depth sc v'
    have hd : (G.pl.w v).asIdeal ^ G.pl.depth sc v * (G.pl.w v).asIdeal ∣
        (G.pl.w v).asIdeal ^ G.pl.depth sc v * J := by
      rw [← pow_succ]; exact Ideal.dvd_iff_le.2 hle
    have hJ : (G.pl.w v).asIdeal ∣ J :=
      (mul_dvd_mul_iff_left (pow_ne_zero _ (G.pl.w v).ne_bot)).1 hd
    have hJle : J ≤ (G.pl.w v).asIdeal := Ideal.le_of_dvd hJ
    obtain ⟨v', hv'S, hpow⟩ := (Ideal.IsPrime.prod_le (G.pl.w v).isPrime).1 hJle
    have hvv := Finset.mem_erase.1 hv'S
    have := eqOf v' (G.pl.w v) (Ideal.IsPrime.le_of_pow_le hpow)
    apply hvv.1
    rw [← G.pl.under_w hvv.2, ← G.pl.under_w hv, this]
  · by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hle : G.modul ≤ (Formalism.DivisionValues.conjPl (G.pl.w v)).asIdeal := fun m hm => hcon m hm
    rw [hmod] at hle
    obtain ⟨v', hv'S, hpow⟩ := (Ideal.IsPrime.prod_le (Formalism.DivisionValues.conjPl (G.pl.w v)).isPrime).1 hle
    have h1 := eqOf v' _ (Ideal.IsPrime.le_of_pow_le hpow)
    have h2 : v' = v := by
      rw [← G.pl.under_w hv'S, ← G.pl.under_w hv, h1, GlobalTheory.ChainTw.ParInv.under_conjPl]
    subst h2
    exact hconj h1.symm

end GlobalTheory.ChiGrid.GridData
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridModulusExactOrderWitnessStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

theorem _root_.GlobalTheory.T.gridModulus_exact_order_witness : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), ∀ v ∈ G.pl.S0,
  (∃ m ∈ G.modul, m ∉ (G.pl.w v).asIdeal ^ (G.pl.depth sc v + 1)) ∧ ∃ m ∈ G.modul, m ∉ (Formalism.DivisionValues.conjPl (G.pl.w v)).asIdeal := by
  first | exact @GlobalTheory.ChiGrid.GridData.modul_witness | exact GlobalTheory.ChiGrid.GridData.modul_witness | (intros; apply GlobalTheory.ChiGrid.GridData.modul_witness <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramedCongruenceElementMemPrincipalCongruence

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

open scoped Pointwise

namespace GlobalTheory.LevFrame

theorem gl_smul_pi_one {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n] [DecidableEq n] (k₀ : GL n 𝒪[k]) :
    Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ • (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) =
      Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k) := by
  have A : ∀ h : GL n 𝒪[k], ∀ y ∈ (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)),
      Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) h • y ∈ (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) := by
    intro h y hy
    have hy' : ∀ j, ∃ c : 𝒪[k], algebraMap 𝒪[k] k c = y j := fun j => Submodule.mem_one.1 (hy j (Set.mem_univ j))
    choose c hc using hy'
    intro i _
    refine Submodule.mem_one.2 ⟨∑ j, h.1 i j * c j, ?_⟩
    show _ = ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) h).1 *ᵥ y) i

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, ← hc]
    rfl
  refine Submodule.ext fun x => (Submodule.mem_smul_pointwise_iff_exists x _ _).trans ⟨?_, ?_⟩
  · rintro ⟨y, hy, rfl⟩
    exact A k₀ y hy
  · intro hx
    refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀⁻¹ • x, A _ x hx, ?_⟩
    rw [map_inv, smul_inv_smul]



theorem gl_mem_lev : All fun {D} _ _ {sc} {G} _ _ => ∀ (X : Node), IsSelfDualC (G.V X) (G.Λ X) → ∀ v ∈ G.pl.S0,
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k),
  p.v = v → Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) → ∀ (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p (G.V X) n),
  β.IsLat (G.Λ X) (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) → ∀ k₀ : GL n 𝒪[k],
  (∀ i j, (k₀.1 - 1) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v) →
  β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀) ∈ lev G X := by
  intro D hQ T L μ0 hL sc G W M hM X hsd v hv k _ _ _ _ p hpv hid n _ _ β hlat k₀ hk₀
  set g := β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀) with hg
  have hff := GlobalTheory.FrameAt.frame_facts D k p (G.V X) n β
  have hgrp : g ∈ grpAt (G.V X) (· = p.v) := (hff.1 g).2 ⟨_, rfl⟩
  have hinK : InK (G.V X) (G.Λ X) (· = p.v) g := by
    obtain ⟨Λ₀, -, hΛ₀, hK⟩ := hff.2.2.2.1 (G.Λ X) hsd
    have hΛeq : Λ₀ = Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k) :=
      Submodule.ext fun x => (hΛ₀ x).trans (hlat x).symm
    rw [hg, hK, hΛeq]
    exact gl_smul_pi_one k₀
  have hsupp : ∀ y, y ∈ latV (G.V X) (G.Λ X) (· = p.v) → ∀ i, y i ∈ idAt D (· = p.v) := fun y hy =>
    (((GlobalTheory.FinPl.localComponents D (· = p.v)).2 (G.V X)).2.2.2 (G.Λ X) y hsd.1).1 hy |>.1
  have hmov : ∀ κ, InK (G.V X) (G.Λ X) (· = p.v) κ → ∀ y, y ∈ latV (G.V X) (G.Λ X) (· = p.v) →
      (mt (G.V X) κ - 1) *ᵥ y ∈ latV (G.V X) (G.Λ X) (· = p.v) := by
    intro κ hκ y hy
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem ((hκ.2 y (hsupp y hy)).1 hy) hy
  show g ∈ Lev.levA (G.V X) (G.levCong X)
  refine Lev.mem_levA.2 ⟨GlobalTheory.SplitHecke.Stab.mem_GfC p.split (β.gl_supp _), ?_⟩
  show Lev.finE (G.V X) g ∈ congLev D.sp.cm (G.V X).gram (G.Λ X) G.modul
  refine mem_congLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun x hx => ?_⟩
  · have h1 := add_mem (GlobalTheory.T.sub_mem_lattice_completion_of_supported_places D (G.V X) _ (G.Λ X) (G.Λ X) g hgrp (hmov g hinK) x hx) hx
    rwa [sub_add_cancel] at h1
  · have h1 := add_mem (GlobalTheory.T.sub_mem_lattice_completion_of_supported_places D (G.V X) _ (G.Λ X) (G.Λ X) g⁻¹ (inv_mem hgrp) (hmov g⁻¹ (inK_inv hinK)) _ hx) hx
    rwa [sub_add_cancel, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at h1
  · obtain ⟨⟨m, hm, hm'⟩, m₂, hm₂, hm₂'⟩ := GlobalTheory.T.gridModulus_exact_order_witness G v hv
    refine GlobalTheory.T.sub_mem_lattice_completion_of_supported_places D (G.V X) _ (G.Λ X) (G.modul • G.Λ X) g hgrp (fun y hy => ?_) x hx
    have hz := hmov g hinK y hy
    obtain ⟨ε, hε, hsum⟩ := p.above
    have hsplit : (mt (G.V X) g - 1) *ᵥ y = (fun i => p.e * ((mt (G.V X) g - 1) *ᵥ y) i) +
        (fun i => cA D p.e * ((mt (G.V X) g - 1) *ᵥ y) i) := by
      funext i
      rw [Pi.add_apply, ← add_mul, hsum]
      exact (((GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D p.v ε hε).1 _).1 (hsupp _ hz i)).symm
    rw [hsplit]
    exact add_mem (GlobalTheory.T.frameCongruent_sub_one_mulVec_mem_idealLatticeCompletion D k p (G.V X) (G.Λ X) n β hlat G.modul (G.pl.depth sc v)
      ⟨m, hm, GlobalTheory.T.integer_outside_prime_pow_dvd_maximal_ideal_pow D k p (G.pl.w v) hid _ m hm'⟩ k₀ hk₀ y hy) (GlobalTheory.T.cA_smul_mem_latV_ideal_smul_of_conj_place D k p (G.pl.w v) hid (G.V X) (G.Λ X) G.modul ⟨m₂, hm₂, hm₂'⟩ _ hz)

end GlobalTheory.LevFrame
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramedCongruenceElementMemPrincipalCongruenceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

theorem _root_.GlobalTheory.T.framedCongruenceElement_mem_principalCongruence : All fun {D} _ _ {sc} {G} _ _ => ∀ (X : Node), IsSelfDualC (G.V X) (G.Λ X) → ∀ v ∈ G.pl.S0,
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k),
  p.v = v → Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) → ∀ (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p (G.V X) n),
  β.IsLat (G.Λ X) (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) → ∀ k₀ : GL n 𝒪[k],
  (∀ i j, (k₀.1 - 1) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v) →
  β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀) ∈ lev G X := by
  first | exact @GlobalTheory.LevFrame.gl_mem_lev | exact GlobalTheory.LevFrame.gl_mem_lev | (intros; apply GlobalTheory.LevFrame.gl_mem_lev <;> assumption)
end
end
