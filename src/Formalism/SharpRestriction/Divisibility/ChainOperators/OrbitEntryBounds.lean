module

public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.PeriodIntegrals.OrbJetBase
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.OrbitLabellings.KvalGeThetaOfShape
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EntAtD
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbAddOne
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbAddUp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.HidaSetting
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.AdmissibleOfJetBounds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.LossLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.SumWcLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.SummableTruncatedGeometric
import Mathlib.Tactic.Linter.Style
public import Formalism.PeriodIntegrals.OrbRestr
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetRestriction.ConstantCoeffZeroOfVanishing
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.OrbEmb
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.KillSubst
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbRestrOne
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SumOrbC

-- Source module: Development.AutomorphicArithmetic.OrbitLabellings.FInertSubEatILeOrbitAverageSubErrors

section

@[expose] public section

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Classical

theorem UpperTheory.fInert_sub_eatI_le_orbit_average_sub_errors :
    ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (E : OrbitPlaces.Ent D) (ce : ErrC) (C6 C : ℝ),
    OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge C6 C K ce → ce.Large →
    ∀ p : ℕ, p.Prime → 5 ≤ p → IsCs D p → (p : ℝ) ≤ L.sc.X'' D.R.n → ∀ i < D.R.m,
    FInert D (i + 1) p - EatI L K ce (i + 1) p ≤
      (∑ z ∈ kindBC D p, FOrb D (i + 1) p z) / (nP D p : ℝ) -
        ((D.R.k : ℝ) - 1) * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / (p : ℝ) ^ 3 - 8 * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / p -
        3 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a := by
  intro D L X K E ce C6 C hS hC hL p _ hp5 hcs _ i hi
  have hc6 : (12 : ℝ) ≤ ce.c6 := hL.1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < p := by linarith
  have ha : 1 < L.sc.a := hS.xa.2
  have hns : ¬ IsSg D p := fun h => by
    have h3 : D.host.cls p = PrimeClass.inertClass := hcs.1
    have h4 : D.host.cls p = PrimeClass.signal := h
    rw [h4] at h3; simp at h3
  have eF : FInert D (i + 1) p = (∑ z ∈ kindA D p, FOrb D (i + 1) p z) / (nP D p : ℝ) +
      (∑ z ∈ kindBC D p, FOrb D (i + 1) p z) / (nP D p : ℝ) := by
    unfold FInert
    rw [if_neg (fun h => hcs.2.2 h.2), ← add_div]
    congr 1
    have e : kindBC D p = (kindA D p)ᶜ := by
      ext z; rw [Finset.mem_compl]; exact OrbitPlaces.memBC_iff p z
    rw [e, Finset.sum_add_sum_compl]
  have eT : topsBC D p = ∅ := by
    unfold topsBC kindBC
    rw [Finset.filter_eq_empty_iff]
    intro z hz ht
    rw [Finset.mem_filter] at hz
    rcases hz.2 with h | h
    · exact hns h
    · have h1 := ht.1
      rw [h] at h1; simp at h1
  have hw : 0 ≤ ∑ z ∈ kindBC D p, wPl D (i + 1) z :=
    Finset.sum_nonneg fun z _ => (hS.wpos i hi z).le
  have hl1 : 0 ≤ Real.logb p L.sc.a := Real.logb_nonneg hp1 ha.le
  have hl2 : 0 ≤ Real.logb p (2 * L.sc.a) := Real.logb_nonneg hp1 (by linarith)
  have hl3 : 0 ≤ Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) := by
    unfold Nm
    rcases Nat.eq_zero_or_pos (D.R.N D.R.m) with h | h
    · rw [h]; simp
    · refine Real.logb_nonneg hp1 ?_
      have h1 : (1 : ℝ) ≤ (nP D p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (nP D p))
      have h2 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast h
      have h3 : (1 : ℝ) ≤ 4 * (nP D p : ℝ) := by linarith
      exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h3 h2) ha.le
  have t1 : 0 ≤ ((kindBC D p).card : ℝ) * (D.R.N (i + 1 - 1) : ℝ) * (D.R.N (i + 1) : ℝ) *
      (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) := by positivity
  have t2 : 0 ≤ K.dl1 * ((kindBC D p).card : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) := by
    have := hC.dl1nn
    positivity
  have t3 : 8 * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / (p : ℝ) ≤
      ce.c6 * (∑ z ∈ kindBC D p, wPl D (i + 1) z) / (p : ℝ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hw) hp0.le
  have t4 : 3 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a ≤
      ce.c6 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)) (sq_nonneg _)) hl1
  have hm := le_max_right (0 : ℝ) ((∑ z ∈ kindA D p, FOrb D (i + 1) p z) / (nP D p : ℝ))
  rw [eF]
  unfold EatI EatX
  rw [if_pos hcs, eT]
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul, add_zero]
  linarith
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.PrvFOfOrbitLetterBounds

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

namespace PI.OrbBoundFW

variable {D : D7} {L : SizeData₂ D}

theorem prvF_of_orbitLetterBounds : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : Ent D) (C6 C : ℝ),
    OrbitLetterBoundsAll C6 C → Shape D L X E → CLarge C6 C K ce → OrbitValuationBound E X K ce := by
  intro D L X K ce E C6 C hA hS hC
  intro p _ h _hcls hp u i hi r hr hk ep sg be hep hsg h1 h2 h3 h4 Th hB0
  have hAdm := admissible_of_jet_bounds h u i r Th ep sg be hep hsg h1 h2 h3 h4 hB0
  have hCor := (hA.1 _ hAdm).2 (L.sc.a ^ 2) (setting_sq hS h hp u hi r Th) D.R.k (wOrb D p i r)
    (eOrb E p u i r) (three_le_k D) (wOrb_pos hS p hi r) (eOrb_bounds hS p u hi r)
    (dl_off h u i r Th) (dl_on h u i r Th)
  refine kvalGe_mono hCor ?_
  have hg := orbit_place_term_le_sum hS K hC.dl1nn hC.dl2 h u hi hr hk Th
  have hw := sum_Wc_le hS h u hi r Th
  have hl := loss_le hS hC h hp hi r
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast h.five
  have hgam : Formalism.MainNotions.product_zeroth_first_parts.gam p = Formalism.MainNotions.G.gam p := rfl
  have hgpos : 0 ≤ Formalism.MainNotions.G.gam p := by
    unfold Formalism.MainNotions.G.gam
    apply div_nonneg (by linarith)
    nlinarith
  have hsw : 0 ≤ ∑ s, wOrb D p i r s := Finset.sum_nonneg fun s _ => (wOrb_pos hS p hi r s).le
  have hc6 : C6 * (∑ s, wOrb D p i r s) / (p : ℝ) ≤ ce.c6 * (∑ s, wOrb D p i r s) / (p : ℝ) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_right hC.c6 hsw
  have hgw : Formalism.MainNotions.G.gam p * ∑ s ∈ (orbLoc E p h u i r Th).TT, ((orbLoc E p h u i r Th).Wc s : ℝ) ≤
      Formalism.MainNotions.G.gam p * (topsOrb D p r : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hw hgpos
  have hi1 : i + 1 - 1 = i := by omega
  rw [hi1] at hl
  have hF : FOrb D (i + 1) p r = lpF p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wOrb D p i r s) := rfl
  have hE : errF L K ce (i + 1) p r = Formalism.MainNotions.G.gam p * (topsOrb D p r : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) +
      ce.c6 * (∑ s, wOrb D p i r s) / (p : ℝ) +
      ((nP D p : ℝ) * (D.R.N (i + 1 - 1) : ℝ) * (D.R.N (i + 1) : ℝ) *
          (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) +
        (K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) +
          K.dl2 * (topsOrb D p r : ℝ) * Real.logb p (2 * L.sc.a) ^ 2)) := by
    unfold errF; simp only [wOrb]; ring
  rw [hi1] at hE
  show g0Pl X K p (i + 1) r + FOrb D (i + 1) p r - errF L K ce (i + 1) p r ≤
    (∑ s ∈ (orbLoc E p h u i r Th).TT, (orbLoc E p h u i r Th).baseTerm s +
      lpF p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wOrb D p i r s)) - C6 * (∑ s, wOrb D p i r s) / (p : ℝ) -
      Formalism.MainNotions.product_zeroth_first_parts.gam p * ∑ s ∈ (orbLoc E p h u i r Th).TT, ((orbLoc E p h u i r Th).Wc s : ℝ) -
      C * ((nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * (Real.logb p (L.sc.a ^ 2) + 1))
  rw [hF, hE, hgam]
  linarith

end PI.OrbBoundFW
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbBoundF

section

@[expose] public section

theorem PI.OrbBoundF : ∀ (D : Formalism.BasicNotions.D7) (L : Formalism.BasicNotions.SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (K : Formalism.MainNotions.G.Consts) (ce : Formalism.BasicNotions.ErrC) (E : Formalism.MainNotions.OrbitPlaces.Ent D) (C6 C : ℝ), Formalism.MainNotions.OrbitPlaces.OrbitLetterBoundsAll C6 C → Formalism.MainNotions.OrbitPlaces.Shape D L X E → Formalism.MainNotions.OrbitPlaces.CLarge C6 C K ce → Formalism.MainNotions.OrbitPlaces.OrbitValuationBound E X K ce :=
  PI.OrbBoundFW.prvF_of_orbitLetterBounds
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetRestriction.RestrictedJetEquation

section

@[expose] public section

noncomputable section

open Classical

namespace PI.OrbJet.OrbW

open Formalism.BasicNotions Formalism.MainNotions.G MvPowerSeries Finsupp PI.OrbJet PI.OrbShared

theorem hasSubst_Clog (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (ep : ℂ_[p]) :
    HasSubst (fun v : Pl D × Fin N0 × Fin N1 => C ep * logPl D p v) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => by rw [map_mul, cc_logPl, mul_zero])

theorem hasSubst_log (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} :
    HasSubst (logPl D p (β := Fin N0 × Fin N1)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => cc_logPl D p v)

theorem hasSubst_Cjet (l d : ℕ) [Fact l.Prime] [NeZero d] {N0 N1 : ℕ} (ep : ℂ_[l]) :
    HasSubst (fun v : ZMod d × Fin N0 × Fin N1 => C ep * jetLogG l d v) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => by rw [map_mul, cc_jetLogG, mul_zero])

theorem hasSubst_jet (l d : ℕ) [Fact l.Prime] [NeZero d] {N0 N1 : ℕ} :
    HasSubst (jetLogG l d (β := Fin N0 × Fin N1)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => cc_jetLogG l d v)

theorem restricted_jet_equation (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (R : Finset (Pl D)) (hR : IsReps D p R)
    (ep : ℂ_[p]) (sg : Pl D → ℂ_[p]) (be : Pl D → MvPowerSeries (ZMod (nP D p)) ℂ_[p])
    (hcc : ∀ r ∈ R, constantCoeff (be r) = 0)
    (Th U : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p])
    (hEq : subst (fun v : Pl D × Fin N0 × Fin N1 => C ep * logPl D p v) Th =
      U * subst (logPl D p (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (beAll D p R sg be)))
    {r : Pl D} (hr : r ∈ R) :
    subst (fun v : ZMod (nP D p) × Fin N0 × Fin N1 => C ep * jetLogG p (nP D p) v) (restr D p r Th) =
      killCompl (orbEmb D p r (Fin N0 × Fin N1)) U *
        subst (jetLogG p (nP D p) (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (sg r • ∑ a : Fin N0, ∑ b : Fin N1,
          subst (fun s : ZMod (nP D p) =>
            (X (s, a, b) : MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p])) (be r))) := by
  set e := orbEmb D p r (Fin N0 × Fin N1) with he
  have hk := congrArg (killCompl e) hEq
  have hA : killCompl e (subst (fun v : Pl D × Fin N0 × Fin N1 => C ep * logPl D p v) Th) =
      subst (fun v : ZMod (nP D p) × Fin N0 × Fin N1 => C ep * jetLogG p (nP D p) v) (killCompl e Th) := by
    refine killCompl_subst_of e _ _ (hasSubst_Clog D p ep) (hasSubst_Cjet p (nP D p) ep) ?_ ?_ Th
    · intro w
      rw [map_mul, killCompl_C, he, killCompl_logPl_emb]
    · intro t ht
      rw [map_mul, killCompl_logPl_off D p r t ht, mul_zero]
  have hL : ∀ F : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p],
      killCompl e (subst (logPl D p (β := Fin N0 × Fin N1)) F) =
        subst (jetLogG p (nP D p) (β := Fin N0 × Fin N1)) (killCompl e F) := by
    intro F
    refine killCompl_subst_of e _ _ (hasSubst_log D p) (hasSubst_jet p (nP D p)) ?_ ?_ F
    · intro w; rw [he, killCompl_logPl_emb]
    · intro t ht; exact killCompl_logPl_off D p r t ht
  have hccAll : constantCoeff (beAll D p (N0 := N0) (N1 := N1) R sg be) = 0 := by
    unfold beAll

    rw [map_sum]
    have hsm : ∀ (c : ℂ_[p]) (f : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p]),
        constantCoeff f = 0 → constantCoeff (c • f) = 0 := by
      intro c f h
      rw [← coeff_zero_eq_constantCoeff_apply] at h ⊢
      simp [h]
    refine Finset.sum_eq_zero fun r' hr' => hsm _ _ ?_

    rw [map_sum]
    refine Finset.sum_eq_zero fun a _ => ?_

    rw [map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    exact constantCoeff_subst_eq_zero (hasSubst_orbX D p r' a b) (fun s => by simp) (hcc r' hr')
  have hE : killCompl e (OJ.expS ℂ_[p] (beAll D p (N0 := N0) (N1 := N1) R sg be)) =
      OJ.expS ℂ_[p] (killCompl e (beAll D p (N0 := N0) (N1 := N1) R sg be)) := by
    unfold OJ.expS PowerSeries.subst
    exact killCompl_subst e (hasSubst_of_constantCoeff_zero fun _ => hccAll) _
  rw [map_mul, hA, hL, hE, killCompl_beAll D p R hR sg be hcc hr] at hk
  rw [restr_eq_killCompl, ← he]
  exact hk

end PI.OrbJet.OrbW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetRestriction.OrbitRestriction

section

@[expose] public section

noncomputable section

open Classical

namespace PI.OrbJet.OrbW

open Formalism.BasicNotions Formalism.MainNotions.G MvPowerSeries Finsupp PI.OrbJet PI.OrbShared

theorem orbitRestriction : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitRestriction E := by
  intro D E
  unfold PI.OrbJet.OrbitRestriction
  intro p _ h u i R hR ep sg be hbe Th hB r hr
  obtain ⟨U, hU, hEq⟩ := hB
  obtain ⟨-, -, hb⟩ := hbe
  haveI : NeZero (nP D p) := ⟨by have := h.two; omega⟩

  have hcc : ∀ r ∈ R, MvPowerSeries.constantCoeff (be r) = 0 := fun r hr =>
    constant_coeff_zero_of_vanishing_alt p (nP D p) (be r) (hb r hr).2.2.1
  have key := restricted_jet_equation D p R hR ep sg be hcc Th U hEq hr
  unfold PI.OrbJet.OrbitThetaExpansion
  refine ⟨_, ?_, key⟩
  intro m
  change (ZMod (nP D p) × Fin (D.R.N i) × Fin (D.R.N (i + 1)) →₀ ℕ) at m
  change ‖MvPowerSeries.coeff m (killCompl (orbEmb D p r (Fin (D.R.N i) × Fin (D.R.N (i + 1)))) U)‖ ≤ 1
  rw [MvPowerSeries.coeff_killCompl]
  exact hU _

end PI.OrbJet.OrbW
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OrbRestr

section

@[expose] public section

theorem PI.OrbRestr : ∀ (D : Formalism.BasicNotions.D7) (E : PI.OrbJet.Ent D), PI.OrbJet.OrbitRestriction E :=
  PI.OrbJet.OrbW.orbitRestriction
end
end

-- Source module: Formalism.SharpRestriction.Divisibility.ChainOperators.OrbitEntryBounds

section

@[expose] public section

namespace Formalism.MainNotions.DIV.Lemmas.OrbitEntryBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

def toEnt {D : D7} (E : OrbitPlaces.Ent D) : PI.OrbJet.Ent D :=
  ⟨E.nu, E.nu_row, E.nu_rows, E.Th, E.ep, E.be, E.sg⟩

theorem addition_bound_holds (D : D7) (E : OrbitPlaces.Ent D) : OrbitPlaces.OrbitsAddLowerBound E := by
  intro p _ h u i hi R hR ep sg be hbe β hβ Th hTh
  exact PI.OrbAddUp D (toEnt E) p ⟨h.five, h.even, h.two⟩ u i hi R hR ep sg be hbe β hβ Th hTh

theorem orbitsAddAtConjugate_ent (D : D7) (E : OrbitPlaces.Ent D) : OrbitPlaces.OrbitsAddAtConjugate E :=
  PI.OrbAddOne D (toEnt E)

theorem restriction_bound_holds (D : D7) (E : OrbitPlaces.Ent D) : OrbitPlaces.OrbitRestriction E := by
  intro p _ h u i R hR ep sg be hbe Th hTh r hr
  exact PI.OrbRestr D (toEnt E) p ⟨h.five, h.even, h.two⟩ u i R hR ep sg be hbe Th hTh r hr

theorem orbit_restriction_at_conjugate (D : D7) (E : OrbitPlaces.Ent D) : OrbitPlaces.OrbitRestrictionAtConjugate E :=
  PI.OrbRestrOne D (toEnt E)

theorem entry_divisor_bound_holds (D : D7) (E : OrbitPlaces.Ent D) (Dx : DivX D) (hs : OrbitPlaces.ThetaKernelShapeAtD E Dx) : OrbitPlaces.EntriesAtDiscriminant E Dx := by
  intro u μ w hL hc i hi L L'
  exact _root_.jet_bound_ramified_prime D Dx E.nu E.nu_row E.nu_rows E.Th hs u μ w hL hc i hi L L'

private theorem entry_number_bound_holds (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (E : OrbitPlaces.Ent D) (ce : ErrC) (C6 C : ℝ)
    (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge C6 C K ce) : OrbitPlaces.ScaledGeneratorsInSup E L K ce := by
  intro p hp h5 hcs hpX u i hi
  exact ⟨fun Th hTh => UpperTheory.kvalGe_theta_of_shape D L X E hS p h5 hcs.1 hcs.2.2 hpX u i hi Th hTh,
    fun hL => UpperTheory.fInert_sub_eatI_le_orbit_average_sub_errors D L X K E ce C6 C hS hC hL p hp.out h5 hcs hpX i hi⟩

theorem orbit_entry_bounds_of_family (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (E : OrbitPlaces.Ent D) (ce : ErrC) (C6 C : ℝ)
    (hF : OrbitPlaces.OrbitValuationBound E X K ce) (hs : OrbitPlaces.ThetaKernelShapeAtD E Dx) (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge C6 C K ce) :
    OrbitPlaces.Core D L X K Dx E ce C :=
  ⟨addition_bound_holds D E, orbitsAddAtConjugate_ent D E, restriction_bound_holds D E, orbit_restriction_at_conjugate D E, hF, entry_divisor_bound_holds D E Dx hs,
    PI.SumOrbC D L X K ce E C6 C hS hC, entry_number_bound_holds D L X K E ce C6 C hS hC⟩

theorem orbit_entry_bounds_hold (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Dx : DivX D) (E : OrbitPlaces.Ent D) (ce : ErrC) (C6 C : ℝ)
    (hA : OrbitPlaces.OrbitLetterBoundsAll C6 C) (hs : OrbitPlaces.ThetaKernelShapeAtD E Dx) (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge C6 C K ce) :
    OrbitPlaces.Core D L X K Dx E ce C :=
  orbit_entry_bounds_of_family D L X K Dx E ce C6 C (PI.OrbBoundF D L X K ce E C6 C hA hS hC) hs hS hC

end Formalism.MainNotions.DIV.Lemmas.OrbitEntryBounds
end
end
