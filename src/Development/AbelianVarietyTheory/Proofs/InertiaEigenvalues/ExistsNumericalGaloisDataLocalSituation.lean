module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleCharacterHyp
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.InvariantsVanishing
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DiagonalQuotientEigen
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.BasicDefinitions.ExistsUnique

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCycOInvPow

section

@[expose] public section

noncomputable section

namespace GlobalTheory.AdmLoc.CycWitness

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct

section Line

variable {G Qp LL R : Type} [Group G] [Field Qp] [Field LL] [Algebra Qp LL] [CommRing R] [Algebra Qp R]

end Line

section Per

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

variable (hK : Function.Surjective (algebraMap Qp K)) (a : ℕ) (θ : G →* LLˣ)
  (hθ : ∀ g, (θ g : LL) = algebraMap Qp LL (((PD.χ g)⁻¹ ^ a : Qpˣ) : Qp))


include hK hθ

end Per

variable {l : ℕ} [Fact l.Prime]

def cycO (P : LocPrime l) (K LL : FinExt l) : ↥(GK K) →* (↥(OL LL))ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => ⟨_, GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.cyc_mem P K LL g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }

theorem cycO_val (P : LocPrime l) (K LL : FinExt l) (g : ↥(GK K)) :
    algebraMap ↥(OL LL) ↥LL.1 (cycO P K LL g) = algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g) := rfl

end GlobalTheory.AdmLoc.CycWitness
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopData

section

@[expose] public section

namespace GlobalTheory.TopWindow

open GlobalTheory.AdmLoc

def InWin (typ : Bool) (h η : ℕ) (u : ℤ) : Prop :=
  if typ then u ≤ (η : ℤ) else (h : ℤ) - η ≤ u

instance (typ : Bool) (h η : ℕ) : DecidablePred (InWin typ h η) := fun u => by
  unfold InWin; infer_instance

theorem count_block (w : ℤ) (t : ℕ) (a : ℤ) :
    (block w t).count a = if w ≤ a ∧ a < w + t then 1 else 0 := by
  split_ifs with ha
  · exact Multiset.count_eq_one_of_mem (Finset.Ico _ _).nodup (mem_block.2 ha)
  · exact Multiset.count_eq_zero.2 fun hm => ha (mem_block.1 hm)

def ofWindow {n r : ℕ} (t : ℕ) (h η : ZMod n → ℕ) (typ : ZMod n → Bool) (w : ZMod n → ℤ)
    (U : ZMod n → Multiset ℤ) (hh : ∀ i, 2 ≤ h i) (hη : ∀ i, 1 ≤ η i) (ht : 1 ≤ t)
    (hc : ∀ i, Multiset.card (U i) = r) (hU : ∀ i, ∀ u ∈ U i, 1 ≤ u ∧ u ≤ (h i : ℤ) - 1)
    (hB : ∀ i (β : ℤ), w i ≤ β → β < w i + t →
      1 ≤ β ∧ β ≤ (h i : ℤ) - 1 ∧ InWin (typ i) (h i) (η i) β) : TopData n r where
  h := h
  η := η
  ty := fun i => if typ i then LType.G else LType.Bd
  w := w
  t := t
  lows := fun i => (U i).filter (InWin (typ i) (h i) (η i))
  cloud := fun i => (U i).filter fun u => ¬ InWin (typ i) (h i) (η i) u
  two_le_h := hh
  one_le_η := hη
  one_le_letterBlockLength := ht
  card_eq := fun i => by rw [Multiset.filter_add_not, hc]
  range := fun i u hu => by
    rw [Multiset.filter_add_not, Multiset.mem_add, mem_block] at hu
    rcases hu with hu | hu
    · exact hU i u hu
    · exact ⟨(hB i u hu.1 hu.2).1, (hB i u hu.1 hu.2).2.1⟩
  lowG := fun i hi u hu => by
    have hi' : typ i = true := by by_contra hn; simp [hn] at hi
    rw [Multiset.mem_add, mem_block, Multiset.mem_filter] at hu
    rcases hu with hu | hu
    · exact ⟨(hU i u hu.1).1, by simpa [InWin, hi'] using hu.2⟩
    · exact ⟨(hB i u hu.1 hu.2).1, by simpa [InWin, hi'] using (hB i u hu.1 hu.2).2.2⟩
  cloudG := fun i hi u hu => by
    have hi' : typ i = true := by by_contra hn; simp [hn] at hi
    rw [Multiset.mem_filter] at hu
    simpa [InWin, hi'] using hu.2
  lowBd := fun i hi u hu => by
    have hi' : typ i = false := by by_contra hn; simp at hn; simp [hn] at hi
    rw [Multiset.mem_add, mem_block, Multiset.mem_filter] at hu
    rcases hu with hu | hu
    · exact ⟨by simpa [InWin, hi'] using hu.2, (hU i u hu.1).2⟩
    · exact ⟨by simpa [InWin, hi'] using (hB i u hu.1 hu.2).2.2, (hB i u hu.1 hu.2).2.1⟩
  cloudBd := fun i hi u hu => by
    have hi' : typ i = false := by by_contra hn; simp at hn; simp [hn] at hi
    rw [Multiset.mem_filter] at hu
    have := hu.2
    simp only [InWin, hi', Bool.false_eq_true, if_false, not_le] at this
    exact this

theorem exists_topData (l n t r : ℕ) (h η : ZMod n → ℕ) (typ : ZMod n → Bool) (w : ZMod n → ℤ)
    (U : ZMod n → Multiset ℤ) (hh : ∀ i, 2 ≤ h i) (hη : ∀ i, 1 ≤ η i) (ht : 1 ≤ t)
    (hc : ∀ i, Multiset.card (U i) = r) (hU : ∀ i, ∀ u ∈ U i, 1 ≤ u ∧ u ≤ (h i : ℤ) - 1)
    (hB : ∀ i (β : ℤ), w i ≤ β → β < w i + t →
      1 ≤ β ∧ β ≤ (h i : ℤ) - 1 ∧ InWin (typ i) (h i) (η i) β)
    (h1 : ∀ i, η i + 4 * GlobalTheory.PhiGam.sg l h i + 6 < l)
    (h2 : ∀ i, ∀ u ∈ U i, InWin (typ i) (h i) (η i) u → ∀ β : ℤ, w i ≤ β → β < w i + t →
      (GlobalTheory.PhiGam.sg l h i : ℤ) + 2 < |u - β|)
    (h3 : ∀ i, ∀ u ∈ U i, ¬ InWin (typ i) (h i) (η i) u → ∀ y : ℤ,
      -2 * (GlobalTheory.PhiGam.sg l h i : ℤ) - 2 ≤ y → y ≤ (η i : ℤ) + 2 * GlobalTheory.PhiGam.sg l h i + 3 →
        ¬ (if typ i then u else (h i : ℤ) - u) ≡ y [ZMOD l]) :
    ∃ Dt : TopData n r, Dt.t = t ∧
      (∀ i, Dt.w i = w i ∧ Dt.U i = U i ∧ ∀ a, ((Dt.Ut i).count a : ℤ) =
        ((U i).count a : ℤ) + if w i ≤ a ∧ a < w i + t then 1 else 0) ∧
      Dt.T1 l ∧ Dt.T2 l ∧ Dt.T3 l := by
  have hUeq : ∀ i, (ofWindow t h η typ w U hh hη ht hc hU hB).U i = U i := fun i =>
    Multiset.filter_add_not _ _
  refine ⟨ofWindow t h η typ w U hh hη ht hc hU hB, rfl, fun i => ⟨rfl, hUeq i, fun a => ?_⟩,
    h1, fun i u hu β hβ => ?_, fun i u hu y hy1 hy2 => ?_⟩
  · rw [TopData.Ut, hUeq, Multiset.count_add]
    change (((U i).count a + (block (w i) t).count a : ℕ) : ℤ) = _
    rw [count_block]
    push_cast
    rfl
  · have hu' := Multiset.mem_filter.1 hu
    have hβ' := mem_block.1 hβ
    exact h2 i u hu'.1 hu'.2 β hβ'.1 hβ'.2
  · have hu' := Multiset.mem_filter.1 hu
    have := h3 i u hu'.1 hu'.2 y hy1 hy2
    have he : (ofWindow t h η typ w U hh hη ht hc hU hB).cloudRes i u =
        if typ i then u else (h i : ℤ) - u := by
      cases hi : typ i <;> simp [TopData.cloudRes, ofWindow, hi]
    rw [he]
    exact this

end GlobalTheory.TopWindow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopDataOfSlotHyps

section

@[expose] public section

namespace GlobalTheory.TopWindow

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

theorem sg_cast_eq (l n : ℕ) (h : ZMod n → ℕ) (i : ZMod n) :
    (GlobalTheory.PhiGam.sg l h i : ℤ) = tableLineDegreeTwo.sg n l h i := by
  have h0 : (0 : ℝ) ≤ ∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) :=
    tsum_nonneg fun j => by positivity
  simp only [GlobalTheory.PhiGam.sg, tableLineDegreeTwo.sg, Formalism.WachCohomologyFacts.V2.sgN]
  exact Int.natCast_floor_eq_floor h0

theorem inWin_iff (typ : Bool) (h η : ℕ) (u : ℤ) (h1 : 1 ≤ u) (h2 : u ≤ (h : ℤ) - 1) :
    InWin typ h η u ↔ Formalism.WachCohomologyFacts.V2.InWinN typ h η u := by
  unfold InWin Formalism.WachCohomologyFacts.V2.InWinN
  cases typ <;> simp [h1, h2]

theorem exists_topData_of_positionHyps : ∀ (l n t r : ℕ) [NeZero n] (h w η : ZMod n → ℕ)
    (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), 2 ≤ l → 1 ≤ t →
    (∀ i, Multiset.card (U i) = r) → tableLineDegreeTwo.PositionHyps l n t h w η typ U →
    ∃ Dt : TopData n r, Dt.t = t ∧
      (∀ i, Dt.w i = w i ∧ Dt.U i = U i ∧ ∀ a, ((Dt.Ut i).count a : ℤ) = tableLineDegreeTwo.jTil U w t i a) ∧
      Dt.T1 l ∧ Dt.T2 l ∧ Dt.T3 l := by
  intro l n t r _ h w η typ U _ ht hc hS
  unfold tableLineDegreeTwo.PositionHyps at hS
  have hsg : ∀ i, (GlobalTheory.PhiGam.sg l h i : ℤ) = tableLineDegreeTwo.sg n l h i := fun i => sg_cast_eq l n h i
  obtain ⟨Dt, hDt, hw, h1, h2, h3⟩ := exists_topData l n t r h η typ (fun i => (w i : ℤ)) U
    (fun i => by obtain ⟨-, hw1, hw2, -⟩ := hS i; omega)
    (fun i => by
      obtain ⟨-, hw1, hw2, hG, hB, -⟩ := hS i
      by_cases hc : typ i = true
      · have := hG hc; omega
      · have := hB (by simpa using hc); omega)
    ht hc (fun i => (hS i).1)
    (fun i β hβ1 hβ2 => by
      obtain ⟨-, hw1, hw2, hG, hB, -⟩ := hS i
      refine ⟨by omega, by omega, ?_⟩
      unfold InWin
      split_ifs with hc
      · have := hG hc; omega
      · have := hB (by simpa using hc); omega)
    (fun i => by have := (hS i).2.2.2.2.2.1; have := hsg i; omega)
    (fun i u hu hin β hβ1 hβ2 => by
      have hr := (hS i).1 u hu
      have hlow := (hS i).2.2.2.2.2.2.1 u
        (by
          classical
          unfold tableLineDegreeTwo.lows
          exact Multiset.mem_filter.2 ⟨hu, (inWin_iff _ _ _ _ hr.1 hr.2).1 hin⟩) β
        (by rw [Formalism.WachCohomologyFacts.Top.GlobalTheory, Finset.mem_Icc]; omega)
      rw [hsg i]
      exact hlow)
    (fun i u hu hin y hy1 hy2 => by
      have hr := (hS i).1 u hu
      have hT := (hS i).2.2.2.2.2.2.2 u
        (by
          classical
          unfold Formalism.WachCohomologyFacts.V2.ClN
          exact Multiset.mem_filter.2 ⟨hu, fun h' => hin ((inWin_iff _ _ _ _ hr.1 hr.2).2 h')⟩) y
        (by have := hsg i; omega) (by have := hsg i; omega)
      intro hmod
      exact hT ((ZMod.intCast_eq_intCast_iff _ _ _).2 hmod))
  refine ⟨Dt, hDt, fun i => ⟨(hw i).1, (hw i).2.1, fun a => ?_⟩, h1, h2, h3⟩
  rw [(hw i).2.2 a]
  unfold tableLineDegreeTwo.jTil
  split_ifs <;> omega

end GlobalTheory.TopWindow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInvMultOfIsGenWith

section

@[expose] public section

noncomputable section

namespace GlobalTheory.SenCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

section Operators

variable {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D] [Module A D] [Module O D]
  [IsScalarTower O A D]

variable {π : A} {g : D →ₗ[O] D} {P Q : Submodule O D}

end Operators

section Residue

variable {O : Type} [CommRing O]

end Residue

section Sen

variable {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D] [Module A D] [Module O D]
  [IsScalarTower O A D] [IsDomain O] [IsDiscreteValuationRing O]

end Sen

section Wach

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

section RankOne

variable {r : ℕ} (hr : r = 1) (β : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (hβ : ∀ k, (β k : W.DD T) ∈ W.NΔ T)
include hr hβ

end RankOne

end Wach

section Prime

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P)

variable {K LL : FinExt l} (hA : CaseA K LL)

theorem standing_iff {hg : Good K 1 LL} (lam : ↥(OL LL)) :
    Standing P K LL (H.W K 1 LL hg).emb lam ↔ 5 ≤ l ∧ CaseA K LL ∧ Irreducible lam :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2.2.2.2⟩, fun h => ⟨h.1, h.2.1, by rw [show K0 K = K.1 from inf_eq_left.2 h.2.1.1],
    (H.W K 1 LL hg).emb_bij, (H.W K 1 LL hg).emb_σ, h.2.2⟩⟩

end Prime

end GlobalTheory.SenCompare
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNumericalGaloisDataLocalSituation

section

@[expose] public section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.TopWindow

theorem exists_topData_galData : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) (K LL : FinExt l)
    (hA : CaseA K LL) (lam : ↥(OL LL)), Irreducible lam → 5 ≤ (P.PD K).p →
    ∀ (t : ℕ) (h w η : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) (typ : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Bool)
      (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
      (χ : ℕ → ↥(GK K) →* (↥(OL LL))ˣ), tableLineDegreeTwo.TopHyp (P.PD K) (H.W K 1 LL hA.2.2).emb t h w η typ U T.ρ χ →
      (∀ i, Multiset.card (U i) = Module.finrank ↥LL.1 T.V) →
      ∃ (r : ℕ) (D : TopData (Module.finrank ℚ_[l] ↥(K0 K)) r) (ε : ↥(GK K) →* (↥(OL LL))ˣ),
        GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Hyp P K LL (H.W K 1 LL hA.2.2).emb D
          (GalData.mk lam T (χ 1) ε) ∧ D.t = t ∧
        (∀ i a, ((D.Ut i).count a : ℤ) = tableLineDegreeTwo.jTil U w t i a) ∧
        ∀ c ∈ Finset.Icc 1 t,
          (GalData.mk lam T (χ 1) ε : GalData ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)).chi c = χ c := by
  intro l _ P H K LL hA lam hlam h5 t h w η typ U T χ hyp hc
  have hp : (P.PD K).p = l := P.PD_p K
  have hS : Standing P K LL (H.W K 1 LL hA.2.2).emb lam :=
    (GlobalTheory.SenCompare.standing_iff P H lam).2 ⟨hp ▸ h5, hA, hlam⟩
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hS⟩
  obtain ⟨ht, hposition, -, hcrys, hmult, hchi⟩ := hyp
  rw [hp] at hposition
  obtain ⟨D, hDt, hD, t1, t2, t3⟩ := GlobalTheory.TopWindow.exists_topData_of_positionHyps l _ t _ h w η typ U
    (Fact.out : l.Prime).two_le ht hc hposition
  obtain ⟨-, hcont1, hcrys1, hjump1⟩ := hchi 1 (Finset.mem_Icc.2 ⟨le_rfl, ht⟩)
  have hcyc : ∀ g, tableLineDegreeTwo.charL (LL := ↥LL.1) (GlobalTheory.AdmLoc.CycWitness.cycO P K LL) g =
      Formalism.MainNotions.N.cycLL (P.PD K) ↥LL.1 g := fun g => Units.ext (GlobalTheory.AdmLoc.CycWitness.cycO_val P K LL g)
  refine ⟨_, D, GlobalTheory.AdmLoc.CycWitness.cycO P K LL,
    ⟨hS, ⟨rfl, ⟨hcrys, fun i τ hτ a => ?_⟩, ⟨hcont1, hcrys1, fun i τ hτ a => ?_⟩,
      GlobalTheory.AdmLoc.CycWitness.cycO_val P K LL⟩, t1, t2, t3⟩, hDt, fun i a => (hD i).2.2 a, fun c hc' => ?_⟩
  · rw [(hD i).2.1]
    exact hmult i τ (AlgHom.ext fun x => hτ x) a
  · refine (hjump1 i τ (AlgHom.ext fun x => hτ x) a).trans ?_
    show _ = ((Multiset.count a {D.w i} : ℕ) : ℤ)
    rw [(hD i).1, Multiset.count_singleton]
    push_cast
    simp only [add_sub_cancel_right]
  · obtain ⟨hχc, -⟩ := hchi c hc'
    refine MonoidHom.ext fun g => ?_
    apply Units.map_injective (f := (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom) Subtype.val_injective
    change tableLineDegreeTwo.charL (LL := ↥LL.1) (χ 1 * GlobalTheory.AdmLoc.CycWitness.cycO P K LL ^ (-((c : ℤ) - 1))) g =
      tableLineDegreeTwo.charL (LL := ↥LL.1) (χ c) g
    rw [hχc g, ← hcyc g]
    simp [tableLineDegreeTwo.charL, map_zpow]

end GlobalTheory.TopWindow
end
end
