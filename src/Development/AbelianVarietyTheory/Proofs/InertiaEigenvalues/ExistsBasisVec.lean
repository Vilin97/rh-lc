module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenLevelGroupFiniteAdelic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiInvariantFunctionIntegrable
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralEqTsumRealPointsLevelCosetTranslatesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralLowestKTypeMatrixCoeffSqPosStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisIntegrandFactorisesOnLevelCosetStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoMulRankWLt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicityMapRightTranslateRealPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DimKKapAtWcPos
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryFundamentalDomainVolumePosFinite

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.DefVol

theorem fdV_measure_pos_lt_top : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F →
    ∀ (i : Fin D.R.m) (t : T), 0 < R.νV i t (R.fdV i t) ∧ R.νV i t (R.fdV i t) < ⊤ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F h i t
  have hm := h.models.νV i t
  have hH : (R.νV i t).IsHaarMeasure := hm.1.1
  have hfd : IsFundamentalDomain (GQ (Vc D i)) (R.fdV i t) (R.νV i t) := hm.2
  obtain ⟨hs, hp⟩ := h.posDef i
  have hc : GlobalTheory.Unf.CoCpt (Vc D i) := GlobalTheory.SeeSaw.Inh.coCpt_of_isDefinite hs (fun τ => Or.inl (hp τ))
  refine ⟨?_, GlobalTheory.Unf.vol_fund_lt_top hc ⟨_, _, hH, hfd⟩⟩
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ (Vc D i))
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ (Vc D i)) (R.νV i t)
  rw [pos_iff_ne_zero]
  intro h0
  have hu := hfd.measure_zero_of_invariant (t := Set.univ) (fun g => Set.smul_set_univ) (by simpa using h0)
  exact (Measure.measure_univ_ne_zero.2 (NeZero.ne (R.νV i t))) hu

end GlobalTheory.DefVol
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryFundamentalDomainVolumePosFiniteStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.definiteUnitaryFundamentalDomain_volume_pos_finite : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T), 0 < R.νV i t (R.fdV i t) ∧ R.νV i t (R.fdV i t) < ⊤ := by
  first | exact @GlobalTheory.DefVol.fdV_measure_pos_lt_top | exact GlobalTheory.DefVol.fdV_measure_pos_lt_top | (intros; apply GlobalTheory.DefVol.fdV_measure_pos_lt_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurL2PairingRealFiniteTranslate

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem schur_trPair_real_fin : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, LevProd R i → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x y : (R.HW i (sg0 D A)).H), ∀ u ∈ GinfC (Wc D i), ∀ γ ∈ GfC (Wc D i), dimProd A i * ∫ z in R.fdW i, star (val R i v x z) * val R i v y (z * (u * γ)) ∂(R.νW i) = trPair R i γ x y * ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ), (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u) ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL i hLP v x y u hu γ hγ
  have hθ : IsInfFam R.θ := hL.models.inf
  obtain ⟨-, hr, -⟩ := hL.models.HW i (sg0 D A)
  have hHaar : (R.νW i).IsHaarMeasure := (hL.models.νW i).1.1
  have hfd : IsFundamentalDomain (GQ (Wc D i)) (R.fdW i) (R.νW i) := (hL.models.νW i).2
  have hTm : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e x) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 (by
      have : (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := hr ▸ LinearMap.mem_range_self _ x
      exact this)
  have hTm' : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e y) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 (by
      have : (R.HW i (sg0 D A)).e y ∈ R.Wall i (sg0 D A) := hr ▸ LinearMap.mem_range_self _ y
      exact this)
  set J' : Set (GA D (Wc D i)) := {k | k ∈ levW R i ∧ γ⁻¹ * k * γ ∈ levW R i} with hJ'
  have hT1 : IsMultMap R.θ (R.MW i (sg0 D A)) J' (fun _ => 1) ((R.HW i (sg0 D A)).e x) :=
    ⟨hTm.aut, hTm.cusp, fun w k hk g => by rw [hTm.lev w k hk.1 g, hLP.2.1 k hk.1], hTm.equiv, hTm.cont⟩
  have hT2 : IsMultMap R.θ (R.MW i (sg0 D A)) J' (fun _ => 1)
      (heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y)) := by
    have hT3 : IsMultMap R.θ (R.MW i (sg0 D A)) J' (fun _ => 1) ((R.HW i (sg0 D A)).e y) :=
      ⟨hTm'.aut, hTm'.cusp, fun w k hk g => by rw [hTm'.lev w k hk.1 g, hLP.2.1 k hk.1], hTm'.equiv, hTm'.cont⟩
    refine GlobalTheory.SphericalOps.isMultMap_heckeOn hT3 (fun k hk => ?_) (fun w k hk g => ?_)
    · rw [Finset.mem_singleton] at hk
      exact hk ▸ hγ
    · simp only [heckeLin_apply, Finset.sum_singleton, one_mul]
      have e : g * k * γ = g * γ * (γ⁻¹ * k * γ) := by group
      rw [e, hTm'.lev w _ hk.2 (g * γ), hLP.2.1 _ hk.2, one_mul]
  obtain ⟨c, hc⟩ := GlobalTheory.MultFinite.schurMult (θ := R.θ) (M := R.MW i (sg0 D A)) (J := J') (χ := fun _ => 1) hP
    (R.νW i) (R.fdW i) hθ hHaar hfd _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 hT1) _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 hT2)
  have hip := ipM_spec _ _ _ _ _ ⟨c, hc⟩
  obtain ⟨v', hv', hmove⟩ := GlobalTheory.RealPointMove.translate_eq_move D R.θ hθ (Wc D i) _ (R.MW i (sg0 D A)) J' (fun _ => 1) _ hT2
    u hu (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))
  have htr : trPair R i γ x y = dimProd A i * ipM (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) ((R.HW i (sg0 D A)).e x)
      (heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y)) := rfl
  have hint : ∀ z, star (val R i v x z) * val R i v y (z * (u * γ)) =
      star ((R.HW i (sg0 D A)).e x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) z) *
        heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y) v' z := fun z => by
    rw [← hmove z]
    simp [val, heckeOn, postOn_apply, heckeLin_apply, mul_assoc]
  simp_rw [hint]
  rw [(hip (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) v').2, htr, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [hv' ρ]

end GlobalTheory.RawLift

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurL2PairingRealFiniteTranslateStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.schur_l2Pairing_realFiniteTranslate : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, LevProd R i → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x y : (R.HW i (sg0 D A)).H), ∀ u ∈ GinfC (Wc D i), ∀ γ ∈ GfC (Wc D i), dimProd A i * ∫ z in R.fdW i, star (val R i v x z) * val R i v y (z * (u * γ)) ∂(R.νW i) = trPair R i γ x y * ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ), (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u) ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ := by
  first | exact @GlobalTheory.RawLift.schur_trPair_real_fin | exact GlobalTheory.RawLift.schur_trPair_real_fin | (intros; apply GlobalTheory.RawLift.schur_trPair_real_fin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisVec

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def FinSumAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H)
    (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ x y,
    HasSum (fun q : GfC (Wc D i) ⧸ (levW R i).subgroupOf (GfC (Wc D i)) =>
      (a : ℂ) * (coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y))
      ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ

theorem jointVec_smul (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (c : ℂ)
    (w : (R.cV i).W) : jointVec R i t v (c • w) = c • jointVec R i t v w := by
  simp only [jointVec, RealDat.ptP, map_smul]

theorem thetaInner_self {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (f : WO S T' → ℂ) :
    thetaIP μ 𝓕 f f = ((∫ z in 𝓕, ‖f z‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  unfold thetaIP
  rw [← integral_complex_ofReal]
  congr 1
  funext z
  rw [Complex.ofReal_pow, ← Complex.conj_mul']
  rfl

theorem exists_basis_vec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i)))
    (h : ∃ v w, IsUnitVec R i v ∧ thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) ≠ 0) :
    ∃ v, IsUnitVec R i v ∧ ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (k0 : Fin n),
      thetaIP μ 𝓕 (jointVec R i t v (b k0)) (jointVec R i t v (b k0)) ≠ 0 := by
  obtain ⟨v, w, hv, hw⟩ := h
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hw
    have e : jointVec R i t v 0 = 0 := by simpa using jointVec_smul R i t v 0 0
    rw [e]
    simp [thetaIP]
  have hn : 0 < Module.finrank ℂ (R.cV i).W := by
    haveI : Nontrivial (R.cV i).W := ⟨⟨w, 0, hw0⟩⟩
    exact Module.finrank_pos
  have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw0
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ) (E := (R.cV i).W)
    (ι := Fin (Module.finrank ℂ (R.cV i).W)) (by simp) (v := fun _ => ((‖w‖⁻¹ : ℝ) : ℂ) • w)
    (s := {⟨0, hn⟩}) (by
      rw [orthonormal_iff_ite]
      rintro ⟨a, ha⟩ ⟨c, hc⟩
      rw [Set.mem_singleton_iff] at ha hc
      subst ha hc
      rw [if_pos rfl]
      show ⟪((‖w‖⁻¹ : ℝ) : ℂ) • w, ((‖w‖⁻¹ : ℝ) : ℂ) • w⟫_ℂ = 1
      rw [inner_self_eq_norm_sq_to_K, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ hwn]
      simp)
  refine ⟨v, hv, _, b, ⟨0, hn⟩, ?_⟩
  rw [hb _ rfl, jointVec_smul, thetaInner_smul_left, thetaInner_smul_right]
  have hc : ((‖w‖⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero hwn
  exact mul_ne_zero (star_ne_zero.2 hc) (mul_ne_zero hc hw)



theorem finSumAt_core (hC : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (hRal : RallisConv D) (i : Fin D.R.m) (t : T) (hAdj : AdjFormula R i t) (hLF : LevFix R i t)
    (hFI : FactInf R i t) (hRL : RealLow R i t) (hLP : LevProd R i) (hTL : TransLaws R i)
    (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) (hth : IsRaw R i t th) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i))) (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕)
    (hvP : thetaIP μ 𝓕 (R.vP i t) (R.vP i t) ≠ 0) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (hv : IsUnitVec R i v)
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (k0 : Fin n)
    (hk0 : thetaIP μ 𝓕 (jointVec R i t v (b k0)) (jointVec R i t v (b k0)) ≠ 0)
    (x₀ : (R.HW i (sg0 D A)).H) (hx₀ : x₀ ≠ 0) : FinSumAt R i t th μ 𝓕 := by
  obtain ⟨-, -, -, -, -, tF⟩ := hTL
  have hm := hL.models
  have hνV : (R.νV i t).IsHaarMeasure := (hm.νV i t).1.1
  have hfdV := (hm.νV i t).2
  have hνW : (R.νW i).IsHaarMeasure := (hm.νW i).1.1
  have hfdW := (hm.νW i).2
  have hpos := hL.posDef i

  have hmem : ∀ x, IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e x) := fun x =>
    (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 (by
      have e := (hm.HW i (sg0 D A)).2.1
      show _ ∈ R.Wall i (sg0 D A)
      rw [← e]
      exact LinearMap.mem_range_self _ x)

  have hR : ∀ k x y, Integrable (rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y) (R.νW i) ∧
      ∫ h in R.fdV i t, star (upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v x) h) *
          upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h ∂(R.νV i t) =
        ((R.νV i t (R.fdV i t)).toReal : ℂ) *
          ∫ g, rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y g ∂(R.νW i) := by
    intro k x y
    have := hRal R.θ R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) hm.inf (hL.thP.ωP i t) hpos.1 hpos.2
      (two_mul_rank_W_lt D i) (R.νV i t) (R.fdV i t) (R.νW i) (R.fdW i) μ 𝓕 hνV hfdV hνW hfdW hμ.1 hμ.2.1 hμ.2.2
      (jointVec R i t v (b k)) (jointVec R i t v (b k)) (val R i v x) (val R i v y)
      (hL.thP.pt_theta i t _) (hL.thP.pt_theta i t _) ((hmem x).aut _) ((hmem x).cusp _) ((hmem y).aut _)
      ((hmem y).cusp _)
    exact ⟨this.2.2.1, this.2.2.2⟩

  have hP := fun k x y => GlobalTheory.T.rallisIntegrand_factorises_on_levelCoset D G Pl0 T A Ks R F hL i t hLF hFI hRL hLP μ 𝓕 hμ v hv (b k) x y
    (GlobalTheory.T.schur_l2Pairing_realFiniteTranslate hC D G Pl0 T A Ks R F hL i hLP v x y)

  have hKo : IsOpen {g : GfC (Wc D i) | (g : GA D (Wc D i)) ∈ levW R i} :=
    GlobalTheory.LevelOpen.isOpen_levG _ _ _
  have hCo := fun k x y => GlobalTheory.T.integral_eq_tsum_realPoints_levelCoset_translates D (Wc D i) (R.νW i) (levW R i) hνW hLP.1 hKo _ (hR k x y).1
  have hmeas : MeasurableSet (realLev R i) := (hCo k0 x₀ x₀).1

  obtain ⟨Pr, hPr, hPc⟩ : ∃ Pr : ℝ, 0 < Pr ∧ dimProd A i = (Pr : ℂ) :=
    ⟨∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℝ),
      Finset.prod_pos fun ρ _ => by exact_mod_cast GlobalTheory.Mem.WeylDimPos.dimK_kapAt_Wc_pos D i _ ρ,
      by unfold dimProd; push_cast; rfl⟩
  have hPne : (Pr : ℂ) ≠ 0 := by exact_mod_cast hPr.ne'
  obtain ⟨nf, hnf⟩ : ∃ nf : Fin n → ℝ, ∀ k, thetaIP μ 𝓕 (jointVec R i t v (b k)) (jointVec R i t v (b k)) = nf k ∧
      0 ≤ nf k :=
    ⟨fun k => ∫ z in 𝓕, ‖jointVec R i t v (b k) z‖ ^ 2 ∂μ, fun k =>
      ⟨thetaInner_self _ _ _, integral_nonneg fun z => by positivity⟩⟩
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ h in realLev R i, lowCoefSq R i v h ∂(R.νW i) := ⟨_, rfl⟩

  have hq : ∀ k x y (γ : GfC (Wc D i)),
      ∫ h in realLev R i, rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y ((γ : GA D (Wc D i)) * h) ∂(R.νW i) =
        (Pr : ℂ)⁻¹ * ((nf k : ℂ) * coef R i t μ 𝓕 γ * trPair R i γ x y * (I : ℂ)) := by
    intro k x y γ
    have e : Set.EqOn (fun h => rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y ((γ : GA D (Wc D i)) * h))
        (fun h => ((Pr : ℂ)⁻¹ * ((nf k : ℂ) * coef R i t μ 𝓕 γ * trPair R i γ x y)) * (lowCoefSq R i v h : ℂ))
        (realLev R i) := by
      intro h hh
      have := hP k x y γ γ.2 h hh
      rw [hPc, (hnf k).1] at this
      simp only
      field_simp
      linear_combination this
    rw [setIntegral_congr_fun hmeas e, integral_const_mul, integral_complex_ofReal, ← hI]
    ring

  have hk : ∀ k x y, HasSum (fun q : GfC (Wc D i) ⧸ (levW R i).subgroupOf (GfC (Wc D i)) =>
      (Pr : ℂ)⁻¹ * ((nf k : ℂ) * coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y *
        (I : ℂ))) (∫ g, rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y g ∂(R.νW i)) := by
    intro k x y
    convert (hCo k x y).2 using 1
    funext q
    exact (hq k x y q.out).symm

  have hc1 : coef R i t μ 𝓕 1 = 1 := by
    unfold coef
    rw [show ((1 : GA D (Vc D i)), (1 : GA D (Wc D i))) = 1 from rfl, map_one, Module.End.one_apply]
    exact div_self hvP
  have hnf0 : (nf k0 : ℂ) ≠ 0 := by rw [← (hnf k0).1]; exact hk0
  have hx0 : trPair R i 1 x₀ x₀ ≠ 0 := by rw [tF]; exact inner_self_ne_zero.2 hx₀
  have hGint : IntegrableOn (lowCoefSq R i v) (realLev R i) (R.νW i) := by
    have hF : IntegrableOn (fun h => ((nf k0 : ℂ) * trPair R i 1 x₀ x₀)⁻¹ *
        ((Pr : ℂ) * rallisF R i t μ 𝓕 v (jointVec R i t v (b k0)) x₀ x₀ h)) (realLev R i) (R.νW i) :=
      ((hR k0 x₀ x₀).1.integrableOn.const_mul _).const_mul _
    have e : Set.EqOn (fun h => ((nf k0 : ℂ) * trPair R i 1 x₀ x₀)⁻¹ *
        ((Pr : ℂ) * rallisF R i t μ 𝓕 v (jointVec R i t v (b k0)) x₀ x₀ h))
        (fun h => (lowCoefSq R i v h : ℂ)) (realLev R i) := by
      intro h hh
      have := hP k0 x₀ x₀ 1 (GfC (Wc D i)).one_mem h hh
      rw [one_mul, hPc, (hnf k0).1, hc1] at this
      simp only
      rw [this]
      field_simp
    have h3 := (hF.congr_fun e hmeas).re
    change IntegrableOn (fun x => Complex.re (lowCoefSq R i v x : ℂ)) (realLev R i) (R.νW i) at h3
    simpa only [Complex.ofReal_re] using h3
  have hIpos : 0 < I := hI ▸ GlobalTheory.T.integral_lowestKTypeMatrixCoeff_sq_pos D G Pl0 T A Ks R F hL i hLP v hv hGint

  obtain ⟨a₀, ha₀, hA⟩ := hAdj th hth v hv n b
  have hvol := GlobalTheory.T.definiteUnitaryFundamentalDomain_volume_pos_finite D G Pl0 T A Ks R F hL i t
  have hvolpos : 0 < (R.νV i t (R.fdV i t)).toReal := ENNReal.toReal_pos hvol.1.ne' hvol.2.ne
  have hnfs : 0 < ∑ k, nf k := Finset.sum_pos' (fun k _ => (hnf k).2)
    ⟨k0, Finset.mem_univ _, lt_of_le_of_ne (hnf k0).2 fun h => hnf0 (by rw [← h]; simp)⟩
  refine ⟨a₀ * (R.νV i t (R.fdV i t)).toReal * (∑ k, nf k) * I / Pr, by positivity, fun x y => ?_⟩
  rw [hA x y]
  have h2 := (hasSum_sum (s := Finset.univ) fun k _ => hk k x y).mul_left
    ((a₀ : ℂ) * ((R.νV i t (R.fdV i t)).toReal : ℂ))
  have hfun : (fun q : GfC (Wc D i) ⧸ (levW R i).subgroupOf (GfC (Wc D i)) =>
      ((a₀ * (R.νV i t (R.fdV i t)).toReal * (∑ k, nf k) * I / Pr : ℝ) : ℂ) *
        (coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y)) =
      fun q => (a₀ : ℂ) * ((R.νV i t (R.fdV i t)).toReal : ℂ) * ∑ k, (Pr : ℂ)⁻¹ * ((nf k : ℂ) *
        coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y * (I : ℂ)) := by
    funext q
    have e1 : ∑ k, (Pr : ℂ)⁻¹ * ((nf k : ℂ) * coef R i t μ 𝓕 (q.out : GfC (Wc D i)) *
        trPair R i (q.out : GfC (Wc D i)) x y * (I : ℂ)) = (∑ k, (nf k : ℂ)) * ((Pr : ℂ)⁻¹ *
        coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y * (I : ℂ)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e1]
    push_cast
    field_simp
  have hval : (a₀ : ℂ) * ∑ k, ∫ h in R.fdV i t,
        star (upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v x) h) *
          upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h ∂(R.νV i t) =
      (a₀ : ℂ) * ((R.νV i t (R.fdV i t)).toReal : ℂ) *
        ∑ k, ∫ g, rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y g ∂(R.νW i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hR k x y).2]
    ring
  rw [hfun, hval]
  exact h2

theorem finSumAt_of (hC : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (hRal : RallisConv D) (i : Fin D.R.m) (t : T) (hAdj : AdjFormula R i t) (hLF : LevFix R i t)
    (hFI : FactInf R i t) (hRL : RealLow R i t) (hVN : VecNe R i t) (hLP : LevProd R i) (hTL : TransLaws R i)
    (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) (hth : IsRaw R i t th) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i))) (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕) : FinSumAt R i t th μ 𝓕 := by
  by_cases hx : ∃ x₀ : (R.HW i (sg0 D A)).H, x₀ ≠ 0
  · obtain ⟨x₀, hx₀⟩ := hx
    obtain ⟨v, hv, n, b, k0, hk0⟩ := exists_basis_vec R i t μ 𝓕 (hVN μ 𝓕 hμ).2
    exact finSumAt_core hC R F hL hRal i t hAdj hLF hFI hRL hLP hTL th hth μ 𝓕 hμ (hVN μ 𝓕 hμ).1 v hv n b k0 hk0
      x₀ hx₀
  · push_neg at hx
    obtain ⟨-, -, tC, -, -, -⟩ := hTL
    refine ⟨1, one_pos, fun x y => ?_⟩
    have ex : LinearMap.adjoint th x = 0 := by rw [hx x, map_zero]
    have hterm : ∀ q : GfC (Wc D i) ⧸ (levW R i).subgroupOf (GfC (Wc D i)),
        trPair R i (q.out : GfC (Wc D i)) x y = 0 := fun q => by
      obtain ⟨B, -, hB⟩ := tC _ (q.out).2
      rw [hB, hx x, inner_zero_left]
    simp only [ex, inner_zero_left, hterm, mul_zero]
    exact hasSum_zero

theorem finSum_of_rallis : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → RallisConv D → ∀ i t, AdjFormula R i t → LevFix R i t → FactInf R i t → RealLow R i t → VecNe R i t → LevProd R i → TransLaws R i → FinSum R i t :=
  fun hC _ _ _ _ _ _ _ _ _ _ _ R F hL _ hRal i t hAdj hLF hFI hRL hVN hLP hTL th hth μ 𝓕 hμ =>
    finSumAt_of hC R F hL hRal i t hAdj hLF hFI hRL hVN hLP hTL th hth μ 𝓕 hμ

end GlobalTheory.RawLift

end
end
end
