module

public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffApplyDPIvOfKvalGe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorLowerBoundOfPlaceBoundWittStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterCoordinatesSeriesOnePlaceStatement
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasSubstCoordZA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.AdmissibleOfJetBounds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.HidaSetting
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.LossLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.SumWcLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.SummableTruncatedGeometric
import Mathlib.Tactic.Linter.Style
public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ServedPrimeProperties
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockRowsOfFills

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory

theorem fock_rows_of_fills : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hT : GatTies D) (Y : LatInst D), FillsAll hT Y → (Y.Fl u w hg).t = D.R.t → ∀ (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (i : ℕ), i < D.R.m → ∀ r : ℕ, ((FormalGroupSystem.nu (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) (i + 1) s (r + 1) : ℤ) : ℝ) = if r < D.R.N i then DV.nuRow D u (i + 1) (hT.gat_pos u w hg ⟨v, s⟩) r else 0 := by
  intro D u w hg hT Y hF ht v s i hi r
  have hk : (D.gat u w hg).P.m + 1 = D.R.k := hT.gat_k u w hg
  have hw : ∀ b (hb : b < D.R.m), (((Y.Fl u w hg).w v (b + 1) s : ℤ) : ℝ) =
      ((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨b, hb⟩ : ℝ) - kaJ D (b + 1) := by
    intro b hb
    rw [hF u w hg v s (b + 1) (by simp [SizeData₂.lifts]; omega)]
    simp [wj, hb, D.hcW_e]
  have hwS : DV.wSz D (i + 1) (hT.gat_pos u w hg ⟨v, s⟩) = ((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨i, hi⟩ : ℝ) := by
    simp [DV.wSz, show 1 ≤ i + 1 ∧ i + 1 ≤ D.R.m by omega, D.hcW_e]
  unfold FormalGroupSystem.nu FormalGroupSystem.NN
  rw [ht]
  by_cases h1 : r < D.R.k
  · rw [if_pos (by omega), if_pos (show r < D.R.N i by simp [Ranks.N]; omega)]
    unfold FormalGroupSystem.lamI
    rw [dite_eq_left (by omega)]
    unfold DV.nuRow DV.srcPar
    rw [dite_eq_left h1, hwS]
    have hl : (((D.gat u w hg).P.lam0 v s ⟨r + 1 - 1, by omega⟩ : ℤ) : ℚ) =
        (D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).u ⟨r, h1⟩ - ((D.R.k : ℚ) - 1) / 2 + r := by
      rw [hT.gat_lam, (D.fm u).lam_eq 0 (Nat.zero_le _)]
      simp [hcToWeightQ, rhoVec, Ranks.N, h1]
      ring
    have hlR := congrArg (Rat.cast : ℚ → ℝ) hl
    push_cast at hlR ⊢
    rw [hlR, hw i hi]
    simp only [kaJ, Ranks.N, Nat.add_sub_cancel]
    push_cast
    ring
  · rw [if_neg (by omega)]
    obtain ⟨q, rfl⟩ : ∃ q, r = D.R.k + q := ⟨r - D.R.k, by omega⟩
    have hrk : D.R.k + q + 1 - ((D.gat u w hg).P.m + 2) = q := by omega
    rw [hrk]
    have ht1 : 0 < D.R.t + 1 := Nat.succ_pos _
    have hM : (i + 1) * (D.R.t + 1) = i * (D.R.t + 1) + (D.R.t + 1) := by ring
    have hNi : D.R.N i = D.R.k + i * (D.R.t + 1) := rfl
    by_cases h2 : q < i * (D.R.t + 1)
    · have hb : q / (D.R.t + 1) < i := by
        rw [Nat.div_lt_iff_lt_mul ht1]; exact h2
      rw [if_pos (by omega), if_pos (by omega)]
      unfold DV.nuRow DV.srcPar
      rw [dite_eq_right h1]
      simp only [Nat.add_sub_cancel_left]
      rw [dite_eq_left (by omega), hwS]
      have hr : q = q / (D.R.t + 1) * (D.R.t + 1) + q % (D.R.t + 1) := by
        have := Nat.div_add_mod q (D.R.t + 1); rw [mul_comm] at this; omega
      have hrR : (q : ℝ) = ((q / (D.R.t + 1) : ℕ) : ℝ) * ((D.R.t : ℝ) + 1) + ((q % (D.R.t + 1) : ℕ) : ℝ) := by
        exact_mod_cast hr
      push_cast
      rw [hw _ (by omega), hw i hi]
      simp only [kaJ, Ranks.N]
      push_cast
      rw [hrR]
      ring
    · rw [if_neg (show ¬ D.R.k + q < D.R.N i by omega)]
      by_cases h3 : q < i * (D.R.t + 1) + (D.R.t + 1)
      · have hb : q / (D.R.t + 1) = i := by
          apply le_antisymm
          · rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul ht1, Nat.succ_mul]; omega
          · rw [Nat.le_div_iff_mul_le ht1]; omega
        rw [if_pos (by omega), hb]
        simp
      · rw [if_neg (by omega)]
        simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockRowsOfFillsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.formalGroup_nu_cast_eq_ite_lt_N : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hT : GatTies D) (Y : LatInst D), FillsAll hT Y → (Y.Fl u w hg).t = D.R.t → ∀ (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (i : ℕ), i < D.R.m → ∀ r : ℕ, ((FormalGroupSystem.nu (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) (i + 1) s (r + 1) : ℤ) : ℝ) = if r < D.R.N i then DV.nuRow D u (i + 1) (hT.gat_pos u w hg ⟨v, s⟩) r else 0 := by
  first | exact @GlobalTheory.fock_rows_of_fills | exact GlobalTheory.fock_rows_of_fills | (intros; apply GlobalTheory.fock_rows_of_fills <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitBoundOverSecondEmbeddingAnyBasePoint

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical Formalism.MainNotions.OrbitPlaces PI.OrbBoundFW

namespace GlobalTheory.TwU

theorem orbitBound_overSecondEmbedding_anyBasePoint_alt : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D) (C6 C : ℝ), OrbitPlaces.OrbitLetterBoundsAll C6 C → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge C6 C K ce → ∀ (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p), IsResidueClassZero D p → hP D p ≠ 0 → (p : ℝ) ≤ L.sc.X'' D.R.n → ∀ u, ∀ i < D.R.m, ∀ (t : HH D) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 → (sg = 1 ∨ sg = -1) → product_zeroth_first_parts.B1 p (nP D p) be → product_zeroth_first_parts.B2 p (nP D p) be → product_zeroth_first_parts.B3 p (nP D p) be → product_zeroth_first_parts.B4 p (nP D p) be → OrbitPlaces.OrbGe E p h u i (true, t) ep sg be (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  intro D L X K ce E C6 C hA hS hC p _ h _hc0 _hP hp u i hi t ep sg be hep hsg h1 h2 h3 h4 Th hB0
  have hAdm := admissible_of_jet_bounds h u i (true, t) Th ep sg be hep hsg h1 h2 h3 h4 hB0
  have hCor := (hA.1 _ hAdm).2 (L.sc.a ^ 2) (setting_sq hS h hp u hi (true, t) Th) D.R.k (wOrb D p i (true, t))
    (eOrb E p u i (true, t)) (three_le_k D) (wOrb_pos hS p hi (true, t)) (eOrb_bounds hS p u hi (true, t))
    (dl_off h u i (true, t) Th) (dl_on h u i (true, t) Th)
  refine kvalGe_mono hCor ?_
  have hg : 0 ≤ ∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, (orbLoc E p h u i (true, t) Th).baseTerm s :=
    Finset.sum_nonneg fun s _ => orbit_local_term_nonneg _ s
  have hw := sum_Wc_le hS h u hi (true, t) Th
  have hl := loss_le hS hC h hp hi (true, t)
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast h.five
  have hgam : Formalism.MainNotions.product_zeroth_first_parts.gam p = Formalism.MainNotions.G.gam p := rfl
  have hgpos : 0 ≤ Formalism.MainNotions.G.gam p := by
    unfold Formalism.MainNotions.G.gam
    apply div_nonneg (by linarith)
    nlinarith
  have hsw : 0 ≤ ∑ s, wOrb D p i (true, t) s := Finset.sum_nonneg fun s _ => (wOrb_pos hS p hi (true, t) s).le
  have hc6 : C6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) ≤ ce.c6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_right hC.c6 hsw
  have hgw : Formalism.MainNotions.G.gam p * ∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, ((orbLoc E p h u i (true, t) Th).Wc s : ℝ) ≤
      Formalism.MainNotions.G.gam p * (topsOrb D p (true, t) : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hw hgpos
  have hi1 : i + 1 - 1 = i := by omega
  rw [hi1] at hl
  have hF : FOrb D (i + 1) p (true, t) = lpF p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wOrb D p i (true, t) s) := rfl
  have hE : errF L K ce (i + 1) p (true, t) = Formalism.MainNotions.G.gam p * (topsOrb D p (true, t) : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) +
      ce.c6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) +
      ((nP D p : ℝ) * (D.R.N (i + 1 - 1) : ℝ) * (D.R.N (i + 1) : ℝ) *
          (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) +
        (K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) +
          K.dl2 * (topsOrb D p (true, t) : ℝ) * Real.logb p (2 * L.sc.a) ^ 2)) := by
    unfold errF; simp only [wOrb]; ring
  rw [hi1] at hE
  show FOrb D (i + 1) p (true, t) - errF L K ce (i + 1) p (true, t) ≤
    (∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, (orbLoc E p h u i (true, t) Th).baseTerm s +
      lpF p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wOrb D p i (true, t) s)) - C6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) -
      Formalism.MainNotions.product_zeroth_first_parts.gam p * ∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, ((orbLoc E p h u i (true, t) Th).Wc s : ℝ) -
      C * ((nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * (Real.logb p (L.sc.a ^ 2) + 1))
  rw [hF, hE, hgam]
  linarith

end GlobalTheory.TwU
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitBoundOverSecondEmbeddingAnyBasePointStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.orbitBound_overSecondEmbedding_anyBasePoint : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D) (C6 C : ℝ), OrbitPlaces.OrbitLetterBoundsAll C6 C → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge C6 C K ce → ∀ (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p), IsResidueClassZero D p → hP D p ≠ 0 → (p : ℝ) ≤ L.sc.X'' D.R.n → ∀ u, ∀ i < D.R.m, ∀ (t : HH D) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 → (sg = 1 ∨ sg = -1) → product_zeroth_first_parts.B1 p (nP D p) be → product_zeroth_first_parts.B2 p (nP D p) be → product_zeroth_first_parts.B3 p (nP D p) be → product_zeroth_first_parts.B4 p (nP D p) be → OrbitPlaces.OrbGe E p h u i (true, t) ep sg be (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  first | exact @GlobalTheory.TwU.orbitBound_overSecondEmbedding_anyBasePoint_alt | exact GlobalTheory.TwU.orbitBound_overSecondEmbedding_anyBasePoint_alt | (intros; apply GlobalTheory.TwU.orbitBound_overSecondEmbedding_anyBasePoint_alt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ServedPrimePropertiesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.servedPrime_properties : ∀ (D : D7) (p : ℕ), p.Prime → IsResidueClassZero D p → HNeZero D.host p → hP D p ≠ 0 ∧ jacobiSym (-(D.host.d : ℤ)) p = -1 ∧ Nat.Coprime (Ideal.absNorm D.host.ccK) p := by
  first | exact @GlobalTheory.TwU.Served.served_facts | exact GlobalTheory.TwU.Served.served_facts | (intros; apply GlobalTheory.TwU.Served.served_facts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalModelBoundPlaceOverSecondEmbedding

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.TwU.LowF

theorem kval_orbit (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D)
    (hA : OrbitPlaces.OrbitLetterBoundsAll 11 1) (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge 11 1 K ce)
    (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p) (h0 : IsResidueClassZero D p) (hne : hP D p ≠ 0)
    (hX : (p : ℝ) ≤ L.sc.X'' D.R.n) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (t : HH D)
    [NeZero (nP D p)] (B : OmBasis p (nP D p)) (be : MvPowerSeries (Fin 2) (K0 p)) (hbe : BeProp p be)
    (U : MvPowerSeries (Eidx (nP D p) (D.R.N i) (D.R.N (i + 1)) ⊕ Eidx (nP D p) (D.R.N i) (D.R.N (i + 1))) (K0 p))
    (hU : IntS p (inParam p U)) :
    product_zeroth_first_parts.KvalGe (D.R.N i) (D.R.N (i + 1)) p (fun s : ZMod (nP D p) => E.nu u i (OrbitPlaces.orbMap D p (true, t) s))
      (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne B be U)))
      (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  obtain ⟨bv, h1, h2, h3, h4, hb⟩ := GlobalTheory.T.exists_letterCoordinates_series_onePlace_alt p h.five (nP D p) h.even B be hbe
  obtain ⟨U', hU', e⟩ := hb _ _ U hU
  exact GlobalTheory.T.orbitBound_overSecondEmbedding_anyBasePoint D L X K ce E 11 1 hA hS hC p h h0 hne hX u i hi t 1 (-1) bv (by simp) (Or.inr rfl) h1 h2 h3 h4 _
    ⟨U', hU', e⟩

theorem kval_general (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D)
    (hA : OrbitPlaces.OrbitLetterBoundsAll 11 1) (hS : OrbitPlaces.Shape D L X E) (hC : OrbitPlaces.CLarge 11 1 K ce)
    (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p) (h0 : IsResidueClassZero D p) (hne : hP D p ≠ 0)
    (hX : (p : ℝ) ≤ L.sc.X'' D.R.n) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (t : HH D)
    (n r0 r1 : ℕ) [NeZero n] (hn : n = nP D p) (h0' : r0 = D.R.N i) (h1' : r1 = D.R.N (i + 1))
    (B : OmBasis p n) (be : MvPowerSeries (Fin 2) (K0 p)) (hbe : BeProp p be)
    (U : MvPowerSeries (Eidx n r0 r1 ⊕ Eidx n r0 r1) (K0 p)) (hU : IntS p (inParam p U)) :
    product_zeroth_first_parts.KvalGe r0 r1 p (fun s : ZMod n => E.nu u i (posPl D p (true, t) s.val))
      (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne B be U)))
      (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  subst hn h0' h1'
  exact kval_orbit D L X K ce E hA hS hC p h h0 hne hX u i hi t B be hbe U hU

theorem lowBound_of_series_bound_one_place {p : ℕ} [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl)
    [NeZero (X.G.P.n' v)] (nu : ZMod (X.G.P.n' v) → YoungDiagram) (g : ℝ)
    (hcc : MvPowerSeries.constantCoeff be = 0)
    (hnu : ∀ s r, (((nu s).rowLen r : ℕ) : ℤ) = X.nuv v (j + 1) (toFin s) (r + 1))
    (hK : ∀ U : MvPowerSeries (Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) ⊕
        Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) (K0 p), IntS p (inParam p U) →
      product_zeroth_first_parts.KvalGe (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) p nu
        (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) (inLetters (thOne (X.om v) be U))) g) :
    IsPlaceCofactorValuationLowerBound X be j v g := by
  intro U hU I n
  obtain ⟨hU1, e⟩ := restr_onePlace p X be j v U hcc hU
  refine GlobalTheory.KvalAgree.coeff_applyD_PIv_of_KvalGe p X j v nu hnu _ g ?_ I n
  rw [e]
  exact hK _ hU1

theorem lowAt_F : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D), LatTied hT X Y → FillsAll hT Y → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → ((D.what₂.places.resChar w) : ℝ) ≤ L.sc.X'' D.R.n → ∀ (Lv : Levels (Y.Fl u w hg)) (Ch : Chain Lv) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _) (Y5 : FormalGroupSystem.Pend (FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) Lv Ch std vp unif eO eO_spec dG dG_spec om)), BeProp (D.what₂.places.resChar w) Y5.be → ∀ (v : Fin (D.gat u w hg).P.nV) (t : HH D), (D.gat u w hg).P.n' v = nP D (D.what₂.places.resChar w) → (∀ s : Fin ((D.gat u w hg).P.n' v), hT.gat_pos u w hg ⟨v, s⟩ = tauPl D (posPl D (D.what₂.places.resChar w) (true, t) s.val)) → ∀ i < D.R.m, Y5.LowAt i v (FOrb D (i + 1) (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce (i + 1) (D.what₂.places.resChar w) (true, t)) := by
  intro D u w hg L hT X Y K ce E hTied hFill hA hS hC hX Lv Ch std vp unif eO eO_spec dG dG_spec om Y5 hBe v t hn hpos i hi
  have h0 : IsResidueClassZero D (D.what₂.places.resChar w) := hg.2.2.1
  have hne := (GlobalTheory.T.servedPrime_properties D _ hg.1 h0 hg.2.2.2.1).1
  have hstd := std v
  have hOK : OrbitPlaces.OrbOK D (D.what₂.places.resChar w) := ⟨hg.2.1, hn ▸ hstd.even, hn ▸ hstd.two_le⟩
  have hcc : MvPowerSeries.constantCoeff Y5.be = 0 := by
    by_contra hc
    have := (hBe.ab 0 (by simpa using hc)).1
    simp at this
  haveI : NeZero ((D.gat u w hg).P.n' v) := ⟨by have := hstd.two_le; omega⟩
  have ht : (Y.Fl u w hg).t = D.R.t := (hTied u w hg).2.1
  have hk := hT.gat_k u w hg
  have hN : ∀ j, NN (D.gat u w hg).P.m (Y.Fl u w hg).t j = D.R.N j := fun j => by
    simp only [NN, Ranks.N, ht]
    omega
  refine GlobalTheory.T.lowAt_of_placeCofactorValuationLowerBound _ _ Y5 i v _ hcc ?_
  refine lowBound_of_series_bound_one_place (Sys.mk (D.gat u w hg) (Y.Fl u w hg) Lv Ch std vp unif eO eO_spec dG dG_spec om) Y5.be i v (fun s => E.nu u i (posPl D (D.what₂.places.resChar w) (true, t) s.val)) _ hcc ?_ ?_
  · intro s r
    have h1 := GlobalTheory.T.formalGroup_nu_cast_eq_ite_lt_N D u w hg hT Y hFill ht v (toFin s) i hi r
    have h2 := E.nu_row u i hi (posPl D (D.what₂.places.resChar w) (true, t) s.val) r
    have h3 := hpos (toFin s)
    rw [h3] at h1
    have h4 : (((E.nu u i (posPl D (D.what₂.places.resChar w) (true, t) s.val)).rowLen r : ℕ) : ℝ) =
        ((FormalGroupSystem.nu (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) (i + 1) (toFin s) (r + 1) : ℤ) : ℝ) := by
      rw [h2, h1]; rfl
    exact_mod_cast h4
  · intro U' hU1
    exact kval_general D L X K ce E hA hS hC _ hOK h0 hne hX u i hi t _ _ _ hn
      (hN i) (hN (i + 1)) _ _ hBe _ hU1

end GlobalTheory.TwU.LowF

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalModelBoundPlaceOverSecondEmbeddingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.local_model_bound_place_over_second_embedding : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D), LatTied hT X Y → FillsAll hT Y → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → ((D.what₂.places.resChar w) : ℝ) ≤ L.sc.X'' D.R.n → ∀ (Lv : Levels (Y.Fl u w hg)) (Ch : Chain Lv) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _) (Y5 : FormalGroupSystem.Pend (FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) Lv Ch std vp unif eO eO_spec dG dG_spec om)), BeProp (D.what₂.places.resChar w) Y5.be → ∀ (v : Fin (D.gat u w hg).P.nV) (t : HH D), (D.gat u w hg).P.n' v = nP D (D.what₂.places.resChar w) → (∀ s : Fin ((D.gat u w hg).P.n' v), hT.gat_pos u w hg ⟨v, s⟩ = tauPl D (posPl D (D.what₂.places.resChar w) (true, t) s.val)) → ∀ i < D.R.m, Y5.LowAt i v (FOrb D (i + 1) (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce (i + 1) (D.what₂.places.resChar w) (true, t)) := by
  first | exact @GlobalTheory.TwU.LowF.lowAt_F | exact GlobalTheory.TwU.LowF.lowAt_F | (intros; apply GlobalTheory.TwU.LowF.lowAt_F <;> assumption)
end
end
