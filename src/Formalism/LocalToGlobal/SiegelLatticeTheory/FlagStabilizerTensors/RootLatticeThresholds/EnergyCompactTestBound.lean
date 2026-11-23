module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXJointAt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GridsRichITc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTCoef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvHoldsGen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPlace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierInOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObjInhab
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeNC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOf
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyNF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPinNorm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MSTypP
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeZhatTr

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.EnergyCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)

theorem normSq_cTorBase (g : ℝ) :
    star (-(Complex.I * (g : ℂ)) / (2 * (Real.pi : ℂ))) * (-(Complex.I * (g : ℂ)) / (2 * (Real.pi : ℂ))) =
      (((g / (2 * Real.pi)) ^ 2 : ℝ) : ℂ) := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have := Real.pi_pos; exact mul_ne_zero two_ne_zero (by exact_mod_cast this.ne')
  set a : ℝ := g / (2 * Real.pi) with ha
  have hk : -(Complex.I * (g : ℂ)) / (2 * (Real.pi : ℂ)) = -Complex.I * (a : ℂ) := by
    rw [ha]; push_cast; field_simp
  rw [hk, star_mul', star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_pow]
  linear_combination (-(a : ℂ) ^ 2) * Complex.I_sq

theorem zhatTr_carrierOf (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
      Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
      List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀))) :
    (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).FromX →
    0 < (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo).S.g →
    ∀ (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) (cv : Fin (D.R.rS + 1) → ℂ), cv ∈ GoodV u u' →
      RealObj.Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (Formalism.MainNotions.S.uMat g) = Matrix.diagonal cv →
      trG (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) g ∈
          Formalism.FourierDecayAlt.B.GV D.R.k D.R.rS ∧
        Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (T ((tauE X e).symm v)).base.z (T ((tauE X e).symm v)).base.z'
          (trG (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) g) =
          Matrix.diagonal (Fin.snoc (α := fun _ => ℂ)
            (Formalism.L2.SG.Pf.Carrier.EnergyPlace.phiQ
              (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo) rfl cv).1
            (Formalism.L2.SG.Pf.Carrier.EnergyPlace.phiQ
              (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo) rfl cv).2) ∧
        Formalism.L2.SG.Pf.Carrier.EnergyPlace.phiQ
                  (CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo) rfl cv ∈
          Formalism.FourierDecayAlt.JF.QDom D.R.k D.R.rS (T ((tauE X e).symm v)).base.z (T ((tauE X e).symm v)).base.z' := by
  intro hFX hg v g cv hcv hZ
  obtain ⟨hQ, hz, hz', -⟩ := hFX v
  set gg : ℕ := D.host.g 0 * D.host.g 1 with hgg
  set κ : ℂ := -(Complex.I * ((gg : ℝ) : ℂ)) / (2 * (Real.pi : ℂ)) with hκ
  have hTr : Bridge.TrHyp (PtRepPf.frU X u v) (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v))
      (fun a => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  have hTr' : Bridge.TrHyp (PtRepPf.frU X u' v) (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v))
      (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) (fun a => cTor (gg : ℝ) D.R.rS a) :=
    ⟨hQ.1, hQ.2.1, hQ.2.2.1, fun a => (hQ.2.2.2 a a rfl).1, fun a => (hQ.2.2.2 a a rfl).2⟩
  refine ⟨Bridge.delta_GV hTr (uMat_unitary g), ?_, ?_⟩
  · have hz2 : (T ((tauE X e).symm v)).base.z = Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u) := hz
    have hz2' : (T ((tauE X e).symm v)).base.z' = Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u') := hz'
    rw [hz2, hz2']
    have h1 := Bridge.zhat_cs hTr hTr' (sc := 1) one_ne_zero (Formalism.MainNotions.S.uMat g)
    have h1' : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u))
        (Formalism.L2.SG.LocWSOf.Qics C (X.pl v) *ᵥ rv X.B.I v (X.zR u'))
        (trG (Formalism.L2.SG.LocWSOf.Qcs C (X.pl v)) (Formalism.L2.SG.LocWSOf.Qics C (X.pl v)) g) =
        Matrix.diagonal (fun a => star (Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) 1 a)) *
          RealObj.Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (Formalism.MainNotions.S.uMat g) *
          Matrix.diagonal (Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) 1) := h1
    rw [h1', hZ, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    show _ = Matrix.diagonal (Fin.snoc (α := fun _ : Fin (D.R.rS + 1) => ℂ)
      (fun a : Fin D.R.rS => ((((gg : ℝ) / (2 * Real.pi)) ^ (2 * (D.R.rS - a.val)) : ℝ) : ℂ) * cv ⟨a.val, by omega⟩)
      (cv ⟨D.R.rS, by omega⟩))
    congr 1
    funext a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [Fin.snoc_last, Bridge.lam_last, star_one, one_mul, mul_one]
      rfl
    · rw [Fin.snoc_castSucc]
      have hl : Bridge.lam (fun a => cTor (gg : ℝ) D.R.rS a) 1 (Fin.castSucc i) = κ ^ (D.R.rS - i.val) := by
        unfold Bridge.lam
        rw [dite_eq_left (show ((Fin.castSucc i : Fin (D.R.rS + 1)) : ℕ) < D.R.rS from i.2)]
        simp [cTor, hκ]
      rw [hl, star_pow]
      have hcv' : cv (Fin.castSucc i) = cv ⟨i.val, by omega⟩ := rfl
      rw [hcv', show (star κ) ^ (D.R.rS - i.val) * cv ⟨i.val, by omega⟩ * κ ^ (D.R.rS - i.val) =
        (star κ * κ) ^ (D.R.rS - i.val) * cv ⟨i.val, by omega⟩ by ring, hκ, normSq_cTorBase, ← Complex.ofReal_pow,
        ← pow_mul]
  · have hg0 : (0 : ℝ) < gg := by exact_mod_cast hg
    refine ⟨fun a => ?_, ?_⟩
    · show ((((gg : ℝ) / (2 * Real.pi)) ^ (2 * (D.R.rS - a.val)) : ℝ) : ℂ) * cv ⟨a.val, by omega⟩ ≠ 0
      refine mul_ne_zero ?_ (hcv.1 _)
      have : (0 : ℝ) < (gg : ℝ) / (2 * Real.pi) := div_pos hg0 (by positivity)
      exact_mod_cast (pow_pos this _).ne'
    · rw [(hT _).1, (hT _).2]
      show ((D.mem u).A.T : ℝ) * ((D.mem u').A.T : ℝ) < Complex.normSq (cv ⟨D.R.rS, by omega⟩)
      have hG := hcv.2
      unfold Gv at hG
      rw [Dl_diagonal cv _ le_rfl, Dl_diagonal cv _ (Nat.le_succ _),
        Formalism.L2.SG.Pf.CarrierTop.prod_castLE_succ cv, norm_mul] at hG
      have hP : 0 < ‖∏ i : Fin D.R.rS, cv (Fin.castLE (Nat.le_succ D.R.rS) i)‖ :=
        norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hcv.1 _)
      have hlast : cv (Fin.last D.R.rS) = cv ⟨D.R.rS, by omega⟩ := rfl
      rw [hlast] at hG
      rw [Complex.normSq_eq_norm_sq]
      unfold Tw at hG
      nlinarith [sq_nonneg ‖∏ i : Fin D.R.rS, cv (Fin.castLE (Nat.le_succ D.R.rS) i)‖]

end Formalism.L2.SG.Pf.Carrier
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPinNormSt

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointPinNormSt

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointQuot
  Formalism.L2.SG.Pf.Carrier.JointPin Formalism.L2.SG.Pf.Carrier.JointPinNorm Formalism.L2.SG.HidaSetting

section Lin

variable {n r : ℕ} (ε : Fin n → Bool)

theorem hJ_add_r (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  simp [hJ, Matrix.mulVec_add, dotProduct_add]

theorem hJ_sub_r (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  simp [hJ, Matrix.mulVec_sub, dotProduct_sub]

theorem hJ_smul_r (x : Fin n → ℂ) (c : ℂ) (y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  simp [hJ, Matrix.mulVec_smul, dotProduct_smul]

theorem hJ_zero_r (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  simp [hJ]

theorem hJ_sum_r {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (f : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, f i) = ∑ i ∈ s, hJ ε x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hJ_zero_r]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hJ_add_r, ih]

theorem hJ_unit (M : Matrix (Fin n) (Fin n) ℂ) (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) (x y : Fin n → ℂ) :
    hJ ε (M *ᵥ x) (M *ᵥ y) = hJ ε x y := by
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]

theorem hJ_conj_swap (x y : Fin n → ℂ) : hJ ε x y = conj (hJ ε y x) :=
  Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_conj ε x y

theorem recon (e u : Fin r → Fin n → ℂ) (κ : Fin r → ℂ) (hκ : ∀ d, κ d ≠ 0)
    (hue : ∀ d c, hJ ε (u d) (e c) = if d = c then κ d else 0) (s : Finset (Fin r)) (w : Fin n → ℂ)
    (hw : w ∈ Submodule.span ℂ (e '' ↑s)) : w = ∑ c ∈ s, (hJ ε (u c) w / κ c) • e c := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    rw [Finset.sum_eq_single b]
    · rw [hue, if_pos rfl, div_self (hκ b), one_smul]
    · intro c _ hcb; rw [hue, if_neg hcb, zero_div, zero_smul]
    · intro h; exact absurd hb h
  | zero => simp [hJ_zero_r]
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [hJ_add_r, add_div, add_smul, Finset.sum_add_distrib]
  | smul t x _ hx =>
    conv_lhs => rw [hx]
    simp only [hJ_smul_r, Finset.smul_sum, smul_smul, mul_div_assoc]

theorem zero_of_pair (e u : Fin r → Fin n → ℂ) (κ : Fin r → ℂ) (hκ : ∀ d, κ d ≠ 0)
    (hue : ∀ d c, hJ ε (u d) (e c) = if d = c then κ d else 0) (s : Finset (Fin r)) (w : Fin n → ℂ)
    (hw : w ∈ Submodule.span ℂ (e '' ↑s)) (h0 : ∀ c ∈ s, hJ ε (u c) w = 0) : w = 0 := by
  rw [recon ε e u κ hκ hue s w hw]
  exact Finset.sum_eq_zero fun c hc => by rw [h0 c hc, zero_div, zero_smul]

theorem orth_span (e : Fin r → Fin n → ℂ) (x : Fin n → ℂ) (s : Set (Fin r)) (hx : ∀ c ∈ s, hJ ε x (e c) = 0)
    (w : Fin n → ℂ) (hw : w ∈ Submodule.span ℂ (e '' s)) : hJ ε x w = 0 := by
  induction hw using Submodule.span_induction with
  | mem y hy => obtain ⟨b, hb, rfl⟩ := hy; exact hx b hb
  | zero => exact hJ_zero_r ε x
  | add y y' _ _ hy hy' => rw [hJ_add_r, hy, hy', add_zero]
  | smul t y _ hy => rw [hJ_smul_r, hy, mul_zero]

theorem spanLt_eq (e : Fin r → Fin n → ℂ) (a : ℕ) :
    spanLt e a = Submodule.span ℂ (e '' ↑(Finset.univ.filter fun b : Fin r => b.1 < a)) := by
  unfold spanLt
  congr 2
  ext b
  simp

theorem st_one_lin (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (G Gi M : Matrix (Fin n) (Fin n) ℂ)
    (hGi : G * Gi = 1) (hG : Gᴴ * Formalism.REAL.Jm ε * G = Formalism.REAL.Jm ε)
    (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) (hee : ∀ a b, hJ ε (e a) (e b) = 0) (cv : Fin r → ℂ)
    (hcv : ∀ a, cv a ≠ 0) (hZ : ∀ a b, hJ ε (e a) (G *ᵥ e b) = if a = b then cv a else 0)
    (hN : InN ε e z M) (hN' : InN ε e z' (Gi * M * G)) : M = 1 := by
  classical
  have hGGi : ∀ x, G *ᵥ (Gi *ᵥ x) = x := fun x => by rw [Matrix.mulVec_mulVec, hGi, Matrix.one_mulVec]
  have hMG : ∀ x, G *ᵥ ((Gi * M * G) *ᵥ x) = M *ᵥ (G *ᵥ x) := fun x => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGi, Matrix.one_mul]

  have hu1 : ∀ d c, hJ ε (G *ᵥ e d) (e c) = if d = c then conj (cv d) else 0 := by
    intro d c
    rw [hJ_conj_swap, hZ]
    by_cases h : c = d
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), map_zero]
  have hu2 : ∀ d c, hJ ε (Gi *ᵥ e d) (e c) = if d = c then cv d else 0 := by
    intro d c
    rw [← hJ_unit ε G hG, hGGi, hZ]
  have hk1 : ∀ d, conj (cv d) ≠ 0 := fun d => by simpa using hcv d
  have hfx : ∀ x y, M *ᵥ x = x → hJ ε x (M *ᵥ y) = hJ ε x y := fun x y hx => by
    conv_lhs => rw [← hx]
    exact hJ_unit ε M hM x y

  have key : ∀ m : ℕ, ∀ c : Fin r, c.1 = m → M *ᵥ e c = e c ∧ M *ᵥ (G *ᵥ e c) = G *ᵥ e c := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro c hc
      have ih' : ∀ d : Fin r, d.1 < c.1 → M *ᵥ e d = e d ∧ M *ᵥ (G *ᵥ e d) = G *ᵥ e d :=
        fun d hd => ih d.1 (hc ▸ hd) d rfl
      have h1 : M *ᵥ e c = e c := by
        have hw := hN.1.1 c
        rw [spanLt_eq] at hw
        have h0 := zero_of_pair ε e (fun d => G *ᵥ e d) (fun d => conj (cv d)) hk1 hu1 _ _ hw (by
          intro d hd
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, hJ_sub_r, hfx _ _ (ih' d hd).2, sub_self])
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
        exact h0
      refine ⟨h1, ?_⟩
      have hw := hN'.1.1 c
      rw [spanLt_eq] at hw
      have h0 := zero_of_pair ε e (fun d => Gi *ᵥ e d) cv hcv hu2 _ _ hw (by
        intro d hd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        rw [← hJ_unit ε G hG, hGGi, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, hMG, hJ_sub_r,
          hfx _ _ (ih' d hd).1, sub_self])
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
      rw [← hMG, h0]
  have hfix1 : ∀ c, M *ᵥ e c = e c := fun c => (key c.1 c rfl).1
  have hfix2 : ∀ c, M *ᵥ (G *ᵥ e c) = G *ᵥ e c := fun c => (key c.1 c rfl).2

  have hall : ∀ v, M *ᵥ v = v := by
    intro v
    set S1 : Fin n → ℂ := ∑ c, (hJ ε (G *ᵥ e c) v / conj (cv c)) • e c with hS1
    set S2 : Fin n → ℂ := ∑ c, (hJ ε (e c) v / cv c) • (G *ᵥ e c) with hS2
    set v1 := v - S1 - S2 with hv1
    have hGe : ∀ d c, hJ ε (G *ᵥ e d) (G *ᵥ e c) = 0 := fun d c => by rw [hJ_unit ε G hG, hee]
    have ho1 : ∀ d, hJ ε (e d) v1 = 0 := by
      intro d
      rw [hv1, hJ_sub_r, hJ_sub_r, hS1, hS2, hJ_sum_r, hJ_sum_r]
      simp only [hJ_smul_r, hee, mul_zero, Finset.sum_const_zero, sub_zero, hZ]
      rw [Finset.sum_eq_single d (fun c _ hc => by rw [if_neg (Ne.symm hc), mul_zero]) (by simp), if_pos rfl,
        div_mul_cancel₀ _ (hcv d), sub_self]
    have ho2 : ∀ d, hJ ε (G *ᵥ e d) v1 = 0 := by
      intro d
      rw [hv1, hJ_sub_r, hJ_sub_r, hS1, hS2, hJ_sum_r, hJ_sum_r]
      simp only [hJ_smul_r, hGe, mul_zero, Finset.sum_const_zero, sub_zero, hu1]
      rw [Finset.sum_eq_single d (fun c _ hc => by rw [if_neg (Ne.symm hc), mul_zero]) (by simp), if_pos rfl,
        div_mul_cancel₀ _ (hk1 d), sub_self]
    have hv : v = v1 + S1 + S2 := by rw [hv1]; abel
    clear_value v1 S1 S2

    have hX : (M - 1) *ᵥ v1 ∈ spanLt e r := hN.2 v1 ho1
    have hGX : (Gi * M * G - 1) *ᵥ (Gi *ᵥ v1) ∈ spanLt e r :=
      hN'.2 _ (fun a => by rw [← hJ_unit ε G hG, hGGi]; exact ho2 a)
    have hw : (M - 1) *ᵥ v1 = G *ᵥ ((Gi * M * G - 1) *ᵥ (Gi *ᵥ v1)) := by
      rw [Matrix.sub_mulVec (Gi * M * G), Matrix.mulVec_sub, hMG, hGGi, Matrix.one_mulVec, hGGi,
        Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [spanLt_eq] at hX
    have h0 := zero_of_pair ε e (fun d => G *ᵥ e d) (fun d => conj (cv d)) hk1 hu1 _ _ hX (by
      intro d _
      rw [hw, hJ_unit ε G hG]
      exact orth_span ε e (e d) _ (fun c _ => hee d c) _ hGX)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    rw [hv, Matrix.mulVec_add, Matrix.mulVec_add, h0, hS1, hS2, Matrix.mulVec_sum, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hfix1, hfix2]
  exact Matrix.ext_of_mulVec_single fun i => by rw [hall, Matrix.one_mulVec]

end Lin

variable {D : D7}

theorem stOne_holds (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : StOne X u u' := by
  intro v g cv hcv hZ
  have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b => by
    rw [show X.eR a = X.crd (X.eX a) from rfl, show X.eR b = X.crd (X.eX b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, X.ee, map_zero]
  have hfrm : ∀ (w : D.what₂.Word) (c : Fin D.R.rS), frm X w 1 v (Fin.castSucc c) = rv X.B.I v (X.eR c) := by
    intro w c
    simp [frm, famSc, fam, Fin.snoc_castSucc]
  have hZ' : ∀ a b : Fin D.R.rS, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (uMat g *ᵥ rv X.B.I v (X.eR b)) =
      if a = b then cv (Fin.castSucc a) else 0 := by
    intro a b
    have := congrFun (congrFun hZ (Fin.castSucc a)) (Fin.castSucc b)
    unfold Formalism.L2.SG.RealObj.Zhat at this
    simp only [hfrm, Matrix.diagonal_apply, Fin.castSucc_inj] at this
    exact this
  have hmemUJ : ∀ y : Formalism.REAL.UJ (X.B.I.ε v), (uMat y)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat y = Formalism.REAL.Jm (X.B.I.ε v) :=
    fun y => y.2
  have hone : (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ StSet (NV X u v) (NV X u' v) g := by
    have h1 : ∀ w : D.what₂.Word, (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ NV X w v := by
      intro w
      show InN _ _ _ (uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)))
      have : uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) = 1 := rfl
      rw [this]
      refine ⟨⟨fun a => ?_, ?_⟩, fun y _ => ?_⟩ <;> simp [Submodule.zero_mem]
    refine ⟨h1 u, ?_⟩
    rw [mul_one, inv_mul_cancel]
    exact h1 u'
  ext y
  refine ⟨fun hy => ?_, fun hy => by rw [Set.mem_singleton_iff.1 hy]; exact hone⟩
  obtain ⟨hy1, hy2⟩ := hy
  have hcoe : uMat (g⁻¹ * y * g) = uMat g⁻¹ * uMat y * uMat g := by
    simp [uMat]
  have hGi : uMat g * uMat g⁻¹ = 1 := by
    simp [uMat]
  have hN' : InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat g⁻¹ * uMat y * uMat g) := by
    rw [← hcoe]; exact hy2
  have hM := st_one_lin (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u'))
    (uMat g) (uMat g⁻¹) (uMat y) hGi (hmemUJ g) (hmemUJ y) hee (fun a => cv (Fin.castSucc a))
    (fun a => hcv.1 _) hZ' hy1 hN'
  rw [Set.mem_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  exact hM

theorem normBridge_of_zhat {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word} (P : Parts X u u')
    (hr : P.S.G.r = D.R.rS) (hZ : ZhatTr P hr) : NormBridge P hr :=
  normBridge_of_two P hr (stOne_holds X u u') hZ

end Formalism.L2.SG.Pf.Carrier.JointPinNormSt
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EnergyCompactTestBound

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

theorem energy_compact_test_bound {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) {θ : ℝ} (C : Choice T.X θ) (u u' : D.what₂.Word)
    (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie T.X e) (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (a b : ∀ j : Fin (nfE D), T.X.B.H (tauE T.X e j)) (ξ : ∀ j : Fin (nfE D), T.X.Vloc u (tauE T.X e j))
    (ξ' : ∀ j : Fin (nfE D), T.X.Vloc u' (tauE T.X e j)) (cc : Fin (nfE D) → ℂ)
    (i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (T.X.Vloc u (tauE T.X e j)) (T.X.Vloc u' (tauE T.X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf T.X C u u' e j).base.π
      (towersOf T.X C u u' e j).base.z (m0E T.X C u u' e j *ᵥ nuE T.X C u' e i0' j)) (A₀ : ℝ)
    (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (sd Cb Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0b i0b' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf)
    (hpin : JointPin.PinCov (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))))
    (hBuilt : Formalism.FourierDecayAlt.D.IsBuilt (sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).χ (nuE T.X C u' e i0') (m0E T.X C u u' e) (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).top A₀) :
    (∏ v, (Formalism.FourierDecayAlt.B.normSq ((ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T v).base ((ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc v)).toReal /
        Formalism.FourierDecayAlt.D.GamLev (sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).G.k (sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).G.r (Formalism.FourierDecayAlt.D.kapG (sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).g (Formalism.FourierDecayAlt.S6.rd D.host.E))
          (Formalism.FourierDecayAlt.D.deG (sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).g (Formalism.FourierDecayAlt.S6.rd D.host.E)) 0) =
      (Formalism.L2.SG.SpectralTiesReal.massDataY T.X T.hb T.Y u u' X0 T.ψ sd Cb Th vR Q i0b i0b' νq).IntN := by
  have hFX : (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))).FromX :=
    BaseOf.fromX T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd.χ (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1))
      (nuE T.X C u' e i0') (m0E T.X C u u' e) (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf T.X C u u' e j) (nuE T.X C u' e i0' j)
        (m0E T.X C u u' e j) (Θ j) (TP j)) A₀ (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))
  have hg0 : 0 < (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))).S.g := by
    show 0 < D.host.g 0 * D.host.g 1
    exact Nat.mul_pos (Formalism.L2.SG.Pf.CarrierSz.g_pos D).1 (Formalism.L2.SG.Pf.CarrierSz.g_pos D).2
  have hZ := zhatTr_carrierOf T.X u u' e he hv C CA de de' l (gridT e l) (grid1T e l) (towersOf T.X C u u' e)
    (Tz_towersOf_base_eq_T T.X C u u' e) (fcT T.X C e u u' a b ξ ξ' cc) cutStd.χ (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1)) (nuE T.X C u' e i0') (m0E T.X C u u' e)
    (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf T.X C u u' e j) (nuE T.X C u' e i0' j)
        (m0E T.X C u u' e j) (Θ j) (TP j)) A₀ (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))
  have hPN := JointPin.placeNormG_of_pin (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))) rfl hpin
    (JointPinNormSt.normBridge_of_zhat _ rfl hZ) hFX hBuilt hg0
  have hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE Formalism.FourierDecayAlt.S6.rd
    rw [Int.cast_abs, one_div]
  have hk1 : 1 ≤ (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))).S.G.k := by
    show 1 ≤ D.R.k
    have := Formalism.MainNotions.BridgeLemma.five_le_k D
    omega
  exact EnergyNF.energy_norm_bound_third_form T.hb T.Y X0 T.ψ sd Cb Th vR Q i0b i0b' νq (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))) rfl rfl
    (fun v => Tz_towersOf_base_eq_T T.X C u u' e _) rfl hrd hg0 hk1 (Formalism.L2.SG.WConst.card_places T.X) T.ψ_char T.ψ_std
    (Formalism.L2.SG.Pf.ProdConvCut2.prodConv_holds T u u') (Formalism.L2.S.Pv.MSTypP.lemmaMSStd_holds T.X u u' T.ψ) hPN

end Formalism.L2.SG.Pf.CarrierXAll
end
end
end
