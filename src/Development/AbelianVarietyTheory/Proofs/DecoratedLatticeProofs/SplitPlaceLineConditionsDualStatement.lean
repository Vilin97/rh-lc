module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSecAddCsec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodIdealZpowCompletionAdeleConjIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeHyperbolicLineIdealsAtPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationXiZeroEqOne
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineSimilitudeMapsSelfDualLattice

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralAdelesSplitPlacesIffHalves

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.FinPl.SplitHalves

variable {D : D7}

theorem sum_idem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → SplitPt D k} {I : List ι} {P : Pl D → Prop} [DecidableEq ι] (hP : Places p I P) :
    ∑ i ∈ I.toFinset, GlobalTheory.FinPlLoc.idem D (· = (p i).v) = GlobalTheory.FinPlLoc.idem D P := by
  classical
  rw [← sub_eq_zero]
  apply GlobalTheory.FinPlLoc.eq_zero_of_comp
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [GlobalTheory.FinPlLoc.idem, GlobalTheory.FinPlLoc.infPart_pair, Finset.sum_const_zero, sub_zero]
  · intro w

    rw [map_sub, map_sum]
    simp only [GlobalTheory.FinPlLoc.compAt_idem]
    by_cases hw : P w
    · obtain ⟨j, rfl⟩ := (hP.mem w).1 hw
      rw [Finset.sum_eq_single j (fun i _ hij => if_neg (fun h => hij (hP.inj h.symm)))
        (fun hj => absurd (List.mem_toFinset.2 (hP.all j)) hj), if_pos rfl, if_pos hw, sub_self]
    · rw [Finset.sum_eq_zero (fun i _ => if_neg (fun h => hw ((hP.mem w).2 ⟨i, h⟩))), if_neg hw, sub_self]

theorem mem_intAt_iff_halves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ a : AE D, a ∈ intAt D P ↔ a ∈ idAt D P ∧ ∀ i, (p i).pr a ∈ 𝒪[k] ∧ (p i).pr (cA D a) ∈ 𝒪[k] := by
  intro D k _ _ _ _ ι p I P hP a
  classical
  have hpr (q : SplitPt D k) (c : k) : q.pr (cA D (q.sec c)) = 0 := by
    have he : q.pr q.e = 1 := by rw [← GlobalTheory.FinPl.FrameLat.sec_one, q.pr_sec]
    have h0 : q.e * cA D (q.sec c) = 0 := by
      rw [← cA_cA q.e, ← map_mul, ← GlobalTheory.FinPl.FrameLat.e_mul_sec q c,
        ← mul_assoc, GlobalTheory.FinPl.FrameLat.cAe_mul_e, zero_mul, map_zero]
    have h1 := congrArg q.pr h0
    rwa [RingHom.map_mul, he, one_mul, RingHom.map_zero] at h1
  have hs (q : SplitPt D k) (a : AE D) (t : k) :
      a * q.sec t ∈ intAt D (· = q.v) ↔ q.pr a * t ∈ 𝒪[k] := by
    rw [mul_comm, GlobalTheory.FinPl.FrameLat.sec_mul_right,
      GlobalTheory.SeeSaw.CoreGlue.mem_intAt_iff q (GlobalTheory.FinPl.FrameLat.sec_mem_idAt q _),
      hpr, q.pr_sec, and_iff_left (zero_mem _), mul_comm]
  have hcs (q : SplitPt D k) (a : AE D) (t : k) :
      a * cA D (q.sec t) ∈ intAt D (· = q.v) ↔ q.pr (cA D a) * t ∈ 𝒪[k] := by
    have hm : cA D (q.sec t) * a = cA D (q.sec (t * q.pr (cA D a))) := by
      rw [← GlobalTheory.FinPl.FrameLat.sec_mul_right, RingHom.map_mul, GlobalTheory.SeeSaw.cA_cA]
    rw [mul_comm, hm, GlobalTheory.SeeSaw.CoreGlue.mem_intAt_iff q
      (GlobalTheory.FinPl.FrameLat.csec_mem_idAt _), hpr, GlobalTheory.SeeSaw.cA_cA, q.pr_sec,
      and_iff_right (zero_mem _), mul_comm]
  have hsec1 : ∀ i, (p i).sec 1 ∈ intAt D (· = (p i).v) := fun i => by
    simpa using (hs (p i) 1 1).2 (by simp)
  have hcsec1 : ∀ i, cA D ((p i).sec 1) ∈ intAt D (· = (p i).v) := fun i => by
    simpa using (hcs (p i) 1 1).2 (by simp)
  constructor
  · intro h
    have hr := (GlobalTheory.IwaIdeals.mem_intAt_iff.1 h).2
    refine ⟨h.1, fun i => ⟨?_, ?_⟩⟩
    · have h1 : a * (p i).sec 1 ∈ intAt D (· = (p i).v) := GlobalTheory.IwaIdeals.mem_intAt_iff.2
        ⟨Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.sec_mem_idAt _ _),
          mul_mem hr (GlobalTheory.IwaIdeals.mem_intAt_iff.1 (hsec1 i)).2⟩
      simpa using (hs (p i) a 1).1 h1
    · have h1 : a * cA D ((p i).sec 1) ∈ intAt D (· = (p i).v) := GlobalTheory.IwaIdeals.mem_intAt_iff.2
        ⟨Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.csec_mem_idAt (p := p i) 1),
          mul_mem hr (GlobalTheory.IwaIdeals.mem_intAt_iff.1 (hcsec1 i)).2⟩
      simpa using (hcs (p i) a 1).1 h1
  · rintro ⟨hid, hh⟩
    refine ⟨hid, ?_⟩
    have ha : a = ∑ i ∈ I.toFinset, (a * (p i).sec 1 + a * cA D ((p i).sec 1)) := by
      conv_lhs => rw [← (GlobalTheory.FinPlLoc.mem_idAt_iff P a).1 hid, ← sum_idem hP, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      set ε := GlobalTheory.FinPlLoc.idem D (· = (p i).v)
      have h1 : ε * a ∈ idAt D (· = (p i).v) := Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
      have h2 := (GlobalTheory.FinPl.FrameLat.idem_iff (p i) _).1 h1
      have he : ε * (p i).sec 1 = (p i).sec 1 :=
        (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.FrameLat.sec_mem_idAt _ _)
      have hce : ε * cA D ((p i).sec 1) = cA D ((p i).sec 1) :=
        (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.FrameLat.csec_mem_idAt (p := p i) 1)
      rw [GlobalTheory.FinPl.FrameLat.sec_one] at he hce ⊢
      calc ε * a = ((p i).e + cA D (p i).e) * (ε * a) := h2.symm
        _ = (ε * (p i).e) * a + (ε * cA D (p i).e) * a := by
          rw [add_mul, mul_left_comm, ← mul_assoc, mul_left_comm (cA D (p i).e), ← mul_assoc]
        _ = a * (p i).e + a * cA D (p i).e := by rw [he, hce, mul_comm (p i).e, mul_comm (cA D (p i).e)]

    rw [ha, map_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [map_add (f := _)]
    exact add_mem ((hs (p i) a 1).2 (by simpa using (hh i).1)).2
      ((hcs (p i) a 1).2 (by simpa using (hh i).2)).2

end GlobalTheory.FinPl.SplitHalves

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralAdelesSplitPlacesIffHalvesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ a : AE D, a ∈ intAt D P ↔ a ∈ idAt D P ∧ ∀ i, (p i).pr a ∈ 𝒪[k] ∧ (p i).pr (cA D a) ∈ 𝒪[k] := by
  first | exact @GlobalTheory.FinPl.SplitHalves.mem_intAt_iff_halves | exact GlobalTheory.FinPl.SplitHalves.mem_intAt_iff_halves | (intros; apply GlobalTheory.FinPl.SplitHalves.mem_intAt_iff_halves <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineConditionsDual

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section



namespace GlobalTheory.FinPl.ScalarDual

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GlobalTheory.FinPl.FrameLat

theorem idAt_mono {P Q : Pl D → Prop} (hPQ : ∀ w, P w → Q w) {a : AE D} (ha : a ∈ idAt D P) : a ∈ idAt D Q := by
  unfold idAt at ha ⊢
  obtain ⟨h0, hw⟩ := Ideal.mem_inf.1 ha
  exact Ideal.mem_inf.2 ⟨h0, (Submodule.mem_iInf _).2 fun w =>
    (Submodule.mem_iInf _).1 hw ⟨w.1, fun hp => w.2 (hPQ _ hp)⟩⟩

theorem pr_eq_zero (q : SplitPt D k) {w : Pl D} (hw : w ≠ q.v) {a : AE D} (ha : a ∈ idAt D (· = w)) : q.pr a = 0 := by
  have h1 : q.e * a ∈ idAt D (· = w) := Ideal.mul_mem_left _ _ ha
  have h2 : q.e * a ∈ idAt D (· = q.v) := Ideal.mul_mem_right _ _ (e_mem_idAt q)
  unfold idAt at h1 h2
  have h0 : q.e * a = 0 := by
    apply GlobalTheory.FinPlLoc.eq_zero_of_comp
    · exact RingHom.mem_ker.1 (Ideal.mem_inf.1 h1).1
    · intro u
      by_cases hu : u = w
      · subst hu
        exact RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 (Ideal.mem_inf.1 h2).2 ⟨u, hw⟩)
      · exact RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 (Ideal.mem_inf.1 h1).2 ⟨u, hu⟩)
  rw [← q.pr_sec (q.pr a), q.sec_pr, h0, map_zero]

theorem pr_cA_xi_int (q : SplitPt D k) (hU : q.UnitAA) :
    q.pr (cA D (incA D D.host.xi0)) ∈ 𝒪[k] ∧ q.pr (cA D (incA D D.host.xi0⁻¹)) ∈ 𝒪[k] := by
  have hid : cA D (q.sec 1) ∈ idAt D (· = q.v) := csec_mem_idAt (p := q) 1
  have hc : cA D (q.sec 1) ∈ intAt D (· = q.v) := by
    refine (GlobalTheory.SplitIntComp.mem_intAt_iff q hid).2 ⟨?_, ?_⟩
    · rw [GlobalTheory.SplitLineSim.pr_cA_sec]; exact zero_mem _
    · rw [Formalism.L2.Theta.cA_cA, q.pr_sec]; exact one_mem _
  have h2 := hU.1 _ hc
  have a1 := ((GlobalTheory.SplitIntComp.mem_intAt_iff q h2.1.1).1 h2.1).2
  have a2 := ((GlobalTheory.SplitIntComp.mem_intAt_iff q h2.2.1).1 h2.2).2
  rw [map_mul, Formalism.L2.Theta.cA_cA, map_mul, q.pr_sec, mul_one] at a1 a2
  exact ⟨a1, a2⟩

theorem cond_dual : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (h h' : D.host.E), h ≠ 0 → h' ≠ 0 → star h' = h' → h = D.host.xi0 * star D.host.xi0 * h' → ∀ d : AE D, d ∈ idAt D P → ((∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D h') ∈ 𝒪[k]) ↔ ∀ c : AE D, c ∈ idAt D P → (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D h) ∈ 𝒪[k]) → incA D (D.host.xi0⁻¹) * cA D d * c * incA D h ∈ intAt D P) := by
  intro D k _ _ _ _ ι p I P hP h h' hh hh' hs hhe d hd
  have hne : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hv : ∀ i, P (p i).v := fun i => (hP.mem _).2 ⟨i, rfl⟩
  have hne_v : ∀ i j, i ≠ j → (p i).v ≠ (p j).v := fun i j hij e => hij (hP.inj e)
  have hU := fun i => pr_cA_xi_int (p i) (hP.unit i)
  have hprod : ∀ i, (p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr (cA D (incA D D.host.xi0)) = 1 := by
    intro i
    rw [← map_mul, ← map_mul, ← map_mul, inv_mul_cancel₀ hne, map_one, map_one, map_one]
  have hch : cA D (incA D h) = incA D h := by
    rw [cA_incA, hhe, star_mul, star_mul, star_star, hs]
    ring_nf
  have hx1 : incA D D.host.xi0⁻¹ * incA D h = cA D (incA D D.host.xi0) * incA D h' := by
    rw [cA_incA, ← map_mul, ← map_mul, hhe, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hX : ∀ c, incA D D.host.xi0⁻¹ * cA D d * c * incA D h =
      cA D (incA D D.host.xi0) * (cA D d * incA D h') * c := fun c => by
    linear_combination (cA D d * c) * hx1
  have hcX : ∀ c, cA D (incA D D.host.xi0⁻¹ * cA D d * c * incA D h) =
      cA D (incA D D.host.xi0⁻¹) * d * (cA D c * incA D h) := fun c => by
    simp only [map_mul, Formalism.L2.Theta.cA_cA, hch]
    ring
  constructor
  · intro hdc c hc hcc
    refine (GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).2 ⟨Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hc), fun i => ⟨?_, ?_⟩⟩
    · rw [hX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr]
      exact mul_mem (mul_mem (hU i).1 (hdc i).2) (hcc i).1
    · rw [hcX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr]
      exact mul_mem (mul_mem (hU i).2 (hdc i).1) (hcc i).2
  · intro H i
    have hsup : ∀ {a : AE D}, a ∈ idAt D (· = (p i).v) → a ∈ idAt D P :=
      fun ha => idAt_mono (fun w hw => by rw [hw]; exact hv i) ha

    have hcond1 : ∀ j, (p j).pr ((p i).sec 1) ∈ 𝒪[k] ∧
        (p j).pr (cA D ((p i).sec 1)) * (p j).pr (incA D h) ∈ 𝒪[k] := by
      intro j
      by_cases hij : j = i
      · subst hij
        rw [(p j).pr_sec, GlobalTheory.SplitLineSim.pr_cA_sec, zero_mul]
        exact ⟨one_mem _, zero_mem _⟩
      · rw [pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (sec_mem_idAt (p i) 1),
          pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (csec_mem_idAt (p := p i) 1), zero_mul]
        exact ⟨zero_mem _, zero_mem _⟩
    have h1 := (((GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).1 (H _ (hsup (sec_mem_idAt (p i) 1)) hcond1)).2 i).1
    rw [hX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr, (p i).pr_sec, mul_one] at h1

    have hh0 : (p i).pr (incA D h) ≠ 0 := by
      intro h0
      have := congrArg (p i).pr (congrArg (incA D) (mul_inv_cancel₀ hh))
      rw [map_mul (incA D), map_mul (p i).pr, h0, zero_mul, map_one, map_one] at this
      exact zero_ne_one this
    have hcond2 : ∀ j, (p j).pr (cA D ((p i).sec ((p i).pr (incA D h))⁻¹)) ∈ 𝒪[k] ∧
        (p j).pr (cA D (cA D ((p i).sec ((p i).pr (incA D h))⁻¹))) * (p j).pr (incA D h) ∈ 𝒪[k] := by
      intro j
      rw [Formalism.L2.Theta.cA_cA]
      by_cases hij : j = i
      · subst hij
        rw [GlobalTheory.SplitLineSim.pr_cA_sec, (p j).pr_sec, inv_mul_cancel₀ hh0]
        exact ⟨zero_mem _, one_mem _⟩
      · rw [pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (sec_mem_idAt (p i) ((p i).pr (incA D h))⁻¹),
          pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (csec_mem_idAt (p := p i) ((p i).pr (incA D h))⁻¹), zero_mul]
        exact ⟨zero_mem _, zero_mem _⟩
    have h2 := (((GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).1 (H _ (hsup (csec_mem_idAt (p := p i) ((p i).pr (incA D h))⁻¹)) hcond2)).2 i).2
    rw [hcX, Formalism.L2.Theta.cA_cA] at h2
    have e3 : (p i).pr (cA D (incA D D.host.xi0⁻¹) * d * ((p i).sec ((p i).pr (incA D h))⁻¹ * incA D h)) =
        (p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr d := by
      simp only [map_mul, (p i).pr_sec]
      rw [inv_mul_cancel₀ hh0, mul_one]
    rw [e3] at h2
    refine ⟨?_, ?_⟩
    · have e2 : (p i).pr d = (p i).pr (cA D (incA D D.host.xi0)) *
          ((p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr d) := by
        linear_combination (-(p i).pr d) * hprod i
      rw [e2]; exact mul_mem (hU i).1 h2
    · have e1 : (p i).pr (cA D d) * (p i).pr (incA D h') = (p i).pr (cA D (incA D D.host.xi0⁻¹)) *
          ((p i).pr (cA D (incA D D.host.xi0)) * ((p i).pr (cA D d) * (p i).pr (incA D h'))) := by
        linear_combination (-((p i).pr (cA D d) * (p i).pr (incA D h'))) * hprod i
      rw [e1]; exact mul_mem (hU i).2 h1

end GlobalTheory.FinPl.ScalarDual

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineConditionsDualStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitPlace_lineConditions_dual : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (h h' : D.host.E), h ≠ 0 → h' ≠ 0 → star h' = h' → h = D.host.xi0 * star D.host.xi0 * h' → ∀ d : AE D, d ∈ idAt D P → ((∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D h') ∈ 𝒪[k]) ↔ ∀ c : AE D, c ∈ idAt D P → (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D h) ∈ 𝒪[k]) → incA D (D.host.xi0⁻¹) * cA D d * c * incA D h ∈ intAt D P) := by
  first | exact @GlobalTheory.FinPl.ScalarDual.cond_dual | exact GlobalTheory.FinPl.ScalarDual.cond_dual | (intros; apply GlobalTheory.FinPl.ScalarDual.cond_dual <;> assumption)
end
end
