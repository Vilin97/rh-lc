module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.JetRen
public import Formalism.PeriodIntegrals.OrbJetBase
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.ExpSum
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.ProdMonomialOne
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.ProdMonomialOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.ExpSum

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.LogInv

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.AO

open MvPowerSeries

variable (p : ℕ) [Fact p.Prime]

def Lp : PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => ∑ e ∈ Finset.range (n + 1), if n = (p ^ 2) ^ e then ((p : ℂ_[p]) ^ e)⁻¹ else 0

theorem Lp_const : PowerSeries.constantCoeff (Lp p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [Lp]

theorem Lp_one : PowerSeries.coeff 1 (Lp p) = 1 := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have h : (1 : ℕ) ≠ (p ^ 2) ^ 1 := by
    rw [pow_one]; exact (Nat.one_lt_pow two_ne_zero hp).ne
  simp [Lp, Finset.sum_range_succ]
  intro h'
  have := Nat.one_lt_pow two_ne_zero hp
  omega

instance Lp_inv : Invertible (PowerSeries.coeff 1 (Lp p)) :=
  invertibleOfNonzero (by rw [Lp_one]; exact one_ne_zero)

def Ep : PowerSeries ℂ_[p] := PowerSeries.substInv (Lp p)

theorem Ep_const : PowerSeries.constantCoeff (Ep p) = 0 := PowerSeries.constantCoeff_substInv _

theorem Ep_Lp : PowerSeries.subst (Lp p) (Ep p) = PowerSeries.X :=
  PowerSeries.subst_substInv_left _ (Lp_const p)

theorem Lp_Ep : PowerSeries.subst (Ep p) (Lp p) = PowerSeries.X :=
  PowerSeries.subst_substInv_right _ (Lp_const p)

theorem hs_Lp : PowerSeries.HasSubst (Lp p) := PowerSeries.HasSubst.of_constantCoeff_zero' (Lp_const p)
theorem hs_Ep : PowerSeries.HasSubst (Ep p) := PowerSeries.HasSubst.of_constantCoeff_zero' (Ep_const p)

variable {τ : Type*}

theorem cc_psubst (g : MvPowerSeries τ ℂ_[p]) (hg : constantCoeff g = 0) (f : PowerSeries ℂ_[p])
    (hf : PowerSeries.constantCoeff f = 0) : constantCoeff (PowerSeries.subst g f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hg f hf

def phiA (c : ℂ_[p]) : τ → MvPowerSeries τ ℂ_[p] :=
  fun v => C c * PowerSeries.subst (X v) (Lp p)

def psiA (c : ℂ_[p]) : τ → MvPowerSeries τ ℂ_[p] :=
  fun v => PowerSeries.subst (C c⁻¹ * X v) (Ep p)

variable [Finite τ]

theorem hs_phiA (c : ℂ_[p]) : HasSubst (phiA p c (τ := τ)) :=
  hasSubst_of_constantCoeff_zero fun v => by
    simp only [phiA, map_mul, cc_psubst p _ (constantCoeff_X v) _ (Lp_const p), mul_zero]

theorem hs_psiA (c : ℂ_[p]) : HasSubst (psiA p c (τ := τ)) :=
  hasSubst_of_constantCoeff_zero fun v => cc_psubst p _ (by simp) _ (Ep_const p)

theorem phi_psi_X (c : ℂ_[p]) (hc : c ≠ 0) (v : τ) :
    subst (phiA p c) (psiA p c v) = X v := by
  have hX : PowerSeries.HasSubst (C c⁻¹ * X v : MvPowerSeries τ ℂ_[p]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  rw [psiA, PI.OrbShared.ExpSum.subst_psubst (hs_phiA p c) hX, subst_mul (hs_phiA p c), subst_X (hs_phiA p c)]
  have hC : subst (phiA p c) (C c⁻¹ : MvPowerSeries τ ℂ_[p]) = C c⁻¹ := by
    exact subst_C _
  rw [hC, phiA, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul,
    ← PowerSeries.subst_comp_subst_apply (hs_Lp p) (PowerSeries.HasSubst.X v), Ep_Lp,
    PowerSeries.subst_X (PowerSeries.HasSubst.X v)]

theorem psi_phi_X (c : ℂ_[p]) (hc : c ≠ 0) (v : τ) :
    subst (psiA p c) (phiA p c v) = X v := by
  have hX : PowerSeries.HasSubst (X v : MvPowerSeries τ ℂ_[p]) := PowerSeries.HasSubst.X v
  have hX' : PowerSeries.HasSubst (C c⁻¹ * X v : MvPowerSeries τ ℂ_[p]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hC : subst (psiA p c) (C c : MvPowerSeries τ ℂ_[p]) = C c := by
    exact subst_C _
  rw [phiA, subst_mul (hs_psiA p c), hC, PI.OrbShared.ExpSum.subst_psubst (hs_psiA p c) hX,
    subst_X (hs_psiA p c), psiA, ← PowerSeries.subst_comp_subst_apply (hs_Ep p) hX', Lp_Ep,
    PowerSeries.subst_X hX', ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]

theorem phi_psi (c : ℂ_[p]) (hc : c ≠ 0) (F : MvPowerSeries τ ℂ_[p]) :
    subst (phiA p c) (subst (psiA p c) F) = F := by
  rw [subst_comp_subst_apply (hs_psiA p c) (hs_phiA p c)]
  simp only [phi_psi_X p c hc]
  exact congrFun subst_self F

theorem psi_phi (c : ℂ_[p]) (hc : c ≠ 0) (F : MvPowerSeries τ ℂ_[p]) :
    subst (psiA p c) (subst (phiA p c) F) = F := by
  rw [subst_comp_subst_apply (hs_phiA p c) (hs_psiA p c)]
  simp only [psi_phi_X p c hc]
  exact congrFun subst_self F

omit [Finite τ] in
theorem coeff_X_Lp (v : τ) (m : τ →₀ ℕ) :
    coeff m (PowerSeries.subst (X v : MvPowerSeries τ ℂ_[p]) (Lp p)) =
      ∑ e ∈ Finset.range (Formalism.BasicNotions.JetTdeg m + 1),
        if m = Finsupp.single v ((p ^ 2) ^ e) then ((p : ℂ_[p]) ^ e)⁻¹ else 0 := by
  by_cases h : ∃ n, m = Finsupp.single v n
  · obtain ⟨n, rfl⟩ := h
    rw [PowerSeries.coeff_subst_single, if_pos (by simp)]
    have hT : Formalism.BasicNotions.JetTdeg (Finsupp.single v n) = n := by
      simp [Formalism.BasicNotions.JetTdeg, Finsupp.sum_single_index]
    simp only [Finsupp.single_eq_same, Lp, PowerSeries.coeff_mk, hT]
    refine Finset.sum_congr rfl fun e _ => ?_
    have : Finsupp.single v n = Finsupp.single v ((p ^ 2) ^ e) ↔ n = (p ^ 2) ^ e :=
      ⟨fun h => by simpa using congrArg (fun f => f v) h, fun h => h ▸ rfl⟩
    simp only [this]
  · rw [PowerSeries.coeff_subst_single, if_neg (fun h' => h ⟨_, h'⟩)]
    symm
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [if_neg]
    exact fun h' => h ⟨_, h'⟩

theorem jetLogG_one {β : Type*} (v : ZMod 1 × β) :
    Formalism.BasicNotions.jetLogG p 1 v = PowerSeries.subst (X v : MvPowerSeries (ZMod 1 × β) ℂ_[p]) (Lp p) := by
  ext m
  rw [coeff_X_Lp]
  have h : ∀ e : ℕ, ((v.1 - 2 * (e : ZMod 1), v.2) : ZMod 1 × β) = v :=
    fun e => Prod.ext (Subsingleton.elim _ _) rfl
  show (∑ e ∈ Finset.range (Formalism.BasicNotions.JetTdeg m + 1),
    if m = Finsupp.single (v.1 - 2 * (e : ZMod 1), v.2) ((p ^ 2) ^ e) then ((p : ℂ_[p]) ^ e)⁻¹ else 0) = _
  simp only [h]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> first | rfl | (exfalso; tauto)

theorem logPl_one (D : Formalism.BasicNotions.D7) (hn : Formalism.MainNotions.G.nP D p = 1) {β : Type} (v : Pl D × β) :
    logPl D p v = PowerSeries.subst (X v : MvPowerSeries (Pl D × β) ℂ_[p]) (Lp p) := by
  ext m
  rw [coeff_X_Lp]
  have h : ∀ e : ℕ, ((backPl D p v.1 (2 * e), v.2) : Pl D × β) = v := by
    intro e
    refine Prod.ext ?_ rfl
    simp [backPl, hn, Formalism.BasicNotions.posPl_zero]
  show (∑ e ∈ Finset.range (Formalism.BasicNotions.JetTdeg m + 1),
    if m = Finsupp.single (backPl D p v.1 (2 * e), v.2) ((p ^ 2) ^ e) then ((p : ℂ_[p]) ^ e)⁻¹ else 0) = _
  simp only [h]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> first | rfl | (exfalso; tauto)

end PI.OrbJet.AO

end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.ConstantCoeffZeroOfBoundTwo

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.AO

open MvPowerSeries Formalism.BasicNotions Formalism.MainNotions.G PI.OrbJet.OJ

variable {p : ℕ} [Fact p.Prime]

def ptE (D : D7) (z : Pl D) : ZMod 1 ↪ Pl D := ⟨fun _ => z, fun a b _ => Subsingleton.elim a b⟩

@[simp] theorem ptE_apply (D : D7) (z : Pl D) (s : ZMod 1) : ptE D z s = z := rfl

def gSub {τ : Type*} (ep : ℂ_[p]) (v : τ) : ZMod 2 → MvPowerSeries τ ℂ_[p] :=
  fun s => if s = 0 then (X v : MvPowerSeries τ ℂ_[p]) else C ep * X v

theorem hs_gSub {τ : Type*} (ep : ℂ_[p]) (v : τ) : HasSubst (gSub ep v) := by
  have h0 : ∀ s, constantCoeff (gSub (p := p) ep v s) = 0 := fun s => by
    unfold gSub
    split_ifs <;> simp
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero h0
  | exact ⟨fun s => by rw [h0 s]; exact IsNilpotent.zero, fun d => Set.toFinite _⟩

theorem cc_gSub {τ : Type*} (ep : ℂ_[p]) (v : τ) (be : MvPowerSeries (ZMod 2) ℂ_[p])
    (hbe : constantCoeff be = 0) : constantCoeff (subst (gSub ep v) be) = 0 := by
  have h0 : ∀ s, constantCoeff (gSub (p := p) ep v s) = 0 := fun s => by
    unfold gSub
    split_ifs <;> simp
  first
  | exact MvPowerSeries.constantCoeff_subst_eq_zero (hs_gSub ep v) h0 hbe
  | exact MvPowerSeries.constantCoeff_subst_eq_zero (hs_gSub ep v) hbe h0
  | (rw [MvPowerSeries.constantCoeff_subst (hs_gSub ep v)]
     apply finsum_eq_zero_of_forall_eq_zero
     intro d
     by_cases hd : d = 0
     · subst hd
       simp [hbe]
     · obtain ⟨s, hs⟩ := Finsupp.ne_iff.1 hd
       simp only [Finsupp.coe_zero, Pi.zero_apply] at hs
       rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.2 hs)]
       · simp
       · simp [h0 s, zero_pow hs])

theorem constantCoeff_zero_of_bound_two (be : MvPowerSeries (ZMod 2) ℂ_[p]) (h : OJ.B3 p 2 be) : constantCoeff be = 0 := by
  by_contra hne
  have h0 := h 0 (by simpa using hne)
  simp [bideg] at h0

def f1 (N0 N1 : ℕ) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod 2) ℂ_[p]) :
    MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p] :=
  (sg / 2) • ∑ a : Fin N0, ∑ b : Fin N1, subst (gSub ep ((0 : ZMod 1), a, b)) be

def fAll (D : D7) (N0 N1 : ℕ) (ep sg : Pl D → ℂ_[p]) (be : Pl D → MvPowerSeries (ZMod 2) ℂ_[p]) :
    MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p] :=
  ∑ z : Pl D, (sg z / 2) • ∑ a : Fin N0, ∑ b : Fin N1, subst (gSub (ep z) (z, a, b)) (be z)

theorem constantCoeff_jet_series (N0 N1 : ℕ) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod 2) ℂ_[p]) (hbe : constantCoeff be = 0) :
    constantCoeff (f1 N0 N1 ep sg be) = 0 := by
  simp [f1, cc_gSub _ _ _ hbe]

theorem rename_jet_series (D : D7) (z : Pl D) (N0 N1 : ℕ) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod 2) ℂ_[p]) :
    rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (f1 N0 N1 ep sg be) =
      (sg / 2) • ∑ a : Fin N0, ∑ b : Fin N1, subst (gSub ep (z, a, b)) be := by

  simp only [f1, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [rename_subst' _ (hs_gSub _ _)]
  congr 1
  funext s
  unfold gSub
  split_ifs
  · rw [rename_X]
    rfl
  · simp [rename_X]
    left
    rfl

def Y1 (N0 N1 : ℕ) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod 2) ℂ_[p]) :
    MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p] :=
  subst (jetLogG p 1 (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (f1 N0 N1 ep sg be))

def T1 (N0 N1 : ℕ) (c ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod 2) ℂ_[p]) (j : ZMod 1 × Fin N0 × Fin N1 →₀ ℕ) :
    MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p] :=
  subst (psiA p c) (monomial j 1 * Y1 N0 N1 ep sg be)

theorem jetLog_eq_phiA (N0 N1 : ℕ) (c : ℂ_[p]) :
    (fun v : ZMod 1 × Fin N0 × Fin N1 => C c * jetLogG p 1 v) = phiA p c := by
  funext v
  simp [phiA, jetLogG_one]

theorem subst_log_jet_monomial (N0 N1 : ℕ) (c ep sg : ℂ_[p]) (hc : c ≠ 0) (be : MvPowerSeries (ZMod 2) ℂ_[p])
    (j : ZMod 1 × Fin N0 × Fin N1 →₀ ℕ) :
    subst (fun v : ZMod 1 × Fin N0 × Fin N1 => C c * jetLogG p 1 v) (T1 N0 N1 c ep sg be j) =
      monomial j 1 * Y1 N0 N1 ep sg be := by
  rw [jetLog_eq_phiA]
  unfold T1
  exact phi_psi (p := p) c hc _

end PI.OrbJet.AO

end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetLogarithm.ProdRenameExpJetSeries

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace PI.OrbJet.AO

open MvPowerSeries Formalism.BasicNotions Formalism.MainNotions.G PI.OrbJet.OJ

variable {p : ℕ} [Fact p.Prime]

theorem norm_coeff_monomial_one {τ : Type*} (j m : τ →₀ ℕ) :
    ‖coeff m (monomial j (1 : ℂ_[p]))‖ ≤ 1 := by
  rw [MvPowerSeries.coeff_monomial]
  split_ifs <;> simp

theorem admissible_jet_term {D : D7} (E : Ent D) (h5 : 5 ≤ p) (u : D.what₂.Word) (i : ℕ) (z : Pl D) (c : ℂ_[p])
    (hc : ‖c‖ = 1) (ep sg : ℂ_[p]) (hep : ‖ep‖ = 1) (hsg : sg = 1 ∨ sg = -1) (be : MvPowerSeries (ZMod 2) ℂ_[p])
    (hbe : OJ.B1 p 2 be ∧ OJ.B2 p 2 be ∧ OJ.B3 p 2 be ∧ OJ.B4 p 2 be)
    (j : ZMod 1 × Fin (D.R.N i) × Fin (D.R.N (i + 1)) →₀ ℕ) :
    (oneLoc E p h5 u i z (T1 (D.R.N i) (D.R.N (i + 1)) c ep sg be j)).AdmB := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  exact ⟨c, hc, be, ⟨ep, hep, sg, hsg, monomial j 1, fun m => norm_coeff_monomial_one j m,
    subst_log_jet_monomial _ _ c ep sg hc0 be j⟩, hbe⟩

def kz (D : D7) {N0 N1 : ℕ} (z : Pl D) (k : Pl D × Fin N0 × Fin N1 →₀ ℕ) : ZMod 1 × Fin N0 × Fin N1 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun w => k (z, w.2)

theorem sum_mapDomain_kz (D : D7) {N0 N1 : ℕ} (k : Pl D × Fin N0 × Fin N1 →₀ ℕ) :
    ∑ z, Finsupp.mapDomain (pEmb (ptE D z) (Fin N0 × Fin N1)) (kz D z k) = k := by
  ext ⟨z0, w⟩
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single z0]
  · have h : ((z0, w) : Pl D × Fin N0 × Fin N1) =
        pEmb (ptE D z0) (Fin N0 × Fin N1) ((0 : ZMod 1), w) := rfl
    rw [h, Finsupp.mapDomain_apply_of_injective (pEmb (ptE D z0) _).injective]
    rfl
  · intro z _ hz
    apply Finsupp.mapDomain_notin_range
    rintro ⟨⟨a, w'⟩, h⟩
    rw [pEmb_apply] at h
    exact hz (congrArg Prod.fst h)
  · intro h
    exact absurd (Finset.mem_univ z0) h

theorem hs_logPl (D : D7) (hn : nP D p = 1) (N0 N1 : ℕ) : HasSubst (logPl D p (β := Fin N0 × Fin N1)) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show logPl D p v 0 = 0
  simp only [logPl]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [if_neg]
  exact fun h => (pow_ne_zero e (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero))
    (Finsupp.single_eq_zero.1 h.symm)

theorem hasSubst_log_jet (N0 N1 : ℕ) : HasSubst (jetLogG p 1 (β := Fin N0 × Fin N1)) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show jetLogG p 1 v 0 = 0
  simp only [jetLogG]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [if_neg]
  exact fun h => (pow_ne_zero e (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero))
    (Finsupp.single_eq_zero.1 h.symm)

theorem prod_rename_exp_jet_series (D : D7) (hn : nP D p = 1) (N0 N1 : ℕ) (ep sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod 2) ℂ_[p]) (hcc : ∀ z, constantCoeff (be z) = 0) :
    ∏ z, rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (Y1 N0 N1 (ep z) (sg z) (be z)) =
      subst (logPl D p (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (fAll D N0 N1 ep sg be)) := by
  classical
  have hE : ∀ f : MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p],
      OJ.expS ℂ_[p] f = PI.OrbShared.ExpSum.eS f := fun f => rfl
  set g : Pl D → MvPowerSeries (Pl D × Fin N0 × Fin N1) ℂ_[p] := fun z =>
    (sg z / 2) • ∑ a : Fin N0, ∑ b : Fin N1, subst (gSub (ep z) (z, a, b)) (be z) with hg
  have hgc : ∀ z, constantCoeff (g z) = 0 := fun z => by
    simp only [hg]
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_smul]

    simp only [map_sum, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, cc_gSub _ _ _ (hcc z),
    Finset.sum_const_zero, smul_zero]
  have hz : ∀ z, rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (Y1 N0 N1 (ep z) (sg z) (be z)) =
      subst (logPl D p (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (g z)) := by
    intro z
    have hl : (fun v => rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (jetLogG p 1 v)) =
        fun v => logPl D p (pEmb (ptE D z) (Fin N0 × Fin N1) v) := by
      funext v
      rw [jetLogG_one, rename_psubst _ (PowerSeries.HasSubst.of_constantCoeff_zero
        (MvPowerSeries.constantCoeff_X v)), MvPowerSeries.rename_X, logPl_one p D hn]
    rw [Y1, rename_subst' _ (hasSubst_log_jet N0 N1), hl, ← subst_rename' _ (hs_logPl D hn N0 N1), OJ.expS,
      OJ.expS, rename_psubst _ (PowerSeries.HasSubst.of_constantCoeff_zero
        (constantCoeff_jet_series N0 N1 (ep z) (sg z) (be z) (hcc z))), rename_jet_series]
  rw [Finset.prod_congr rfl (fun z _ => hz z), ← MvPowerSeries.coe_substAlgHom (hs_logPl D hn N0 N1),
    ← map_prod]
  congr 1
  rw [show fAll D N0 N1 ep sg be = ∑ z, g z from rfl, hE,
    PI.OrbShared.ExpSum.eS_sum _ _ (fun z _ => hgc z)]
  rfl

private theorem prod_monomial_one_eq_monomial_sum {ι σ : Type*} (s : Finset ι) (m : ι → σ →₀ ℕ) :
    ∏ i ∈ s, (monomial (m i) (1 : ℂ_[p]) : MvPowerSeries σ ℂ_[p]) = monomial (∑ i ∈ s, m i) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    first | rfl | simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, MvPowerSeries.monomial_mul_monomial, one_mul]

theorem factor (D : D7) (hn : nP D p = 1) (N0 N1 : ℕ) (c : ℂ_[p]) (hc : c ≠ 0) (ep sg : Pl D → ℂ_[p])
    (be : Pl D → MvPowerSeries (ZMod 2) ℂ_[p]) (hcc : ∀ z, constantCoeff (be z) = 0)
    (k : Pl D × Fin N0 × Fin N1 →₀ ℕ) :
    subst (psiA p c) (monomial k 1 *
        subst (logPl D p (β := Fin N0 × Fin N1)) (OJ.expS ℂ_[p] (fAll D N0 N1 ep sg be))) =
      ∏ z, rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (T1 N0 N1 c (ep z) (sg z) (be z) (kz D z k)) := by
  classical
  have hpsi : ∀ z (s : ZMod 1 × Fin N0 × Fin N1),
      rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (psiA p c s) =
        psiA p c (pEmb (ptE D z) (Fin N0 × Fin N1) s) := by
    intro z s
    have hh : PowerSeries.HasSubst (C c⁻¹ * X s : MvPowerSeries (ZMod 1 × Fin N0 × Fin N1) ℂ_[p]) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
    simp only [psiA]
    rw [rename_psubst _ hh, map_mul, MvPowerSeries.rename_C, MvPowerSeries.rename_X]
  have hT : ∀ z, rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (T1 N0 N1 c (ep z) (sg z) (be z) (kz D z k)) =
      subst (psiA p c) (monomial (Finsupp.mapDomain (pEmb (ptE D z) (Fin N0 × Fin N1)) (kz D z k)) 1 *
        rename (pEmb (ptE D z) (Fin N0 × Fin N1)) (Y1 N0 N1 (ep z) (sg z) (be z))) := by
    intro z
    rw [T1, rename_subst' _ (hs_psiA p c), funext (hpsi z), ← subst_rename' _ (hs_psiA p c), map_mul,
      MvPowerSeries.rename_monomial]
  rw [Finset.prod_congr rfl (fun z _ => hT z), ← MvPowerSeries.coe_substAlgHom (hs_psiA p c), ← map_prod,
    Finset.prod_mul_distrib, prod_rename_exp_jet_series D hn N0 N1 ep sg be hcc, prod_monomial_one_eq_monomial_sum,
    sum_mapDomain_kz]

end PI.OrbJet.AO

end
end
end
