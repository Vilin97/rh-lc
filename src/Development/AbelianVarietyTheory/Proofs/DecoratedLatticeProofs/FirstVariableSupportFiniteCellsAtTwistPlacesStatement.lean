module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocK
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSetStatement
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubleDescentOfParity
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepFinitelyManyCellsUniformProoStatement
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistCombinationSplitsSinglePlaceVacuumStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlacesGroupEqProductLocalGroupsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteLocalSupportExchangeDataTwistPlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QSuppTwo

theorem prod_mul_inv_mem {G : Type} [Group G] (H : Subgroup G) : ∀ (n : ℕ) (f : Fin n → G) (i : Fin n),
    (∀ i', i' ≠ i → f i' ∈ H) → (∀ y ∈ H, f i * y = y * f i) → (List.ofFn f).prod * (f i)⁻¹ ∈ H := by
  intro n
  induction n with
  | zero => intro f i; exact i.elim0
  | succ n ih =>
    intro f i
    refine Fin.cases ?_ (fun k => ?_) i
    · intro hf0 hc0
      have hP : (List.ofFn fun k : Fin n => f k.succ).prod ∈ H := by
        apply Subgroup.list_prod_mem
        intro x hx
        obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
        exact hf0 _ (Fin.succ_ne_zero k)
      rw [List.ofFn_succ, List.prod_cons, hc0 _ hP, mul_assoc, mul_inv_cancel, mul_one]
      exact hP
    · intro hfk hck
      rw [List.ofFn_succ, List.prod_cons, mul_assoc]
      exact mul_mem (hfk 0 (Fin.succ_ne_zero k).symm)
        (ih (fun k => f k.succ) k (fun k' hk' => hfk _ (fun e => hk' (Fin.succ_injective _ e))) hck)

theorem mem_support_conv {G : Type} [Monoid G] : ∀ (n : ℕ) (f : Fin n → (G →₀ ℂ)) (g : G),
    g ∈ (conv (List.ofFn f)).support → ∃ x : Fin n → G, (∀ i, x i ∈ (f i).support) ∧ g = (List.ofFn x).prod := by
  classical
  intro n
  induction n with
  | zero =>
    intro f g hg
    simp only [List.ofFn_zero, conv, List.foldr_nil] at hg
    have := Finsupp.support_single_subset hg
    rw [Finset.mem_singleton] at this
    exact ⟨Fin.elim0, fun i => i.elim0, by simp [this]⟩
  | succ n ih =>
    intro f g hg
    rw [List.ofFn_succ] at hg
    simp only [conv, List.foldr_cons] at hg
    have h1 := Finsupp.support_sum hg
    rw [Finset.mem_biUnion] at h1
    obtain ⟨g₀, hg₀, h2⟩ := h1
    have h3 := Finsupp.support_sum h2
    rw [Finset.mem_biUnion] at h3
    obtain ⟨g', hg', h4⟩ := h3
    have h5 := Finsupp.support_single_subset h4
    rw [Finset.mem_singleton] at h5
    obtain ⟨x, hx, hxe⟩ := ih (fun k => f k.succ) g' hg'
    refine ⟨Fin.cons g₀ x, fun i => Fin.cases hg₀ (fun k => hx k) i, ?_⟩
    rw [List.ofFn_succ, List.prod_cons, h5, hxe]
    simp

end GlobalTheory.QSuppTwo

open GlobalTheory.QSuppTwo in
theorem GlobalTheory.QSuppTwo.main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ A : ∀ i, Finset (GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∀ α, ∀ g ∈ (w.ε j α).support, ∃ a : ∀ i, GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k, ∀ i, a i ∈ A i ∧ g * ((F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) (a i))⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v) := by
  classical
  intro D c v t w F hF j σ h
  have hd : ∀ i, j + (2 * σ + 2) = (F.Q i).s := fun i => by have := (F.Q i).hs; omega
  choose e he using fun i (α' : (F.Q i).Ch j) => (F.Q i).εL_at j (σ + 1) h (2 * σ + 2) (hd i) α'
  refine ⟨fun i => Finset.univ.biUnion fun α' => (e i α').support, ?_⟩
  intro α g hg
  rw [hF.ε j (σ + 1) h α] at hg
  have hg' := Finsupp.support_smul hg
  obtain ⟨x, hx, rfl⟩ := mem_support_conv _ _ g hg'
  have hpt : ∀ i, ∃ a ∈ (e i (F.eqv j α i)).support,
      (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a = x i := by
    intro i
    have := hx i
    rw [(he i (F.eqv j α i)).2] at this
    have := Finsupp.mapDomain_support this
    rw [Finset.mem_image] at this
    exact this
  choose a ha hax using hpt
  refine ⟨a, fun i => ⟨Finset.mem_biUnion.2 ⟨F.eqv j α i, Finset.mem_univ _, ha i⟩, ?_⟩⟩
  have I := fun i => GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (F.Q i).k (F.Q i).q (c.V j) _ ((F.Q i).FY j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega))
    ((F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega)) ((F.Q i).gl_loc j _ _)
  rw [hax i]
  apply prod_mul_inv_mem _ _ x i
  · intro i' hi'
    rw [← hax i']
    have hr : (F.Q i').gl j (2 * σ + 2 + 1) (by have := (F.Q i').hs; omega) (a i') ∈ GlobalTheory.FinPl.grpAt (c.V j) (· = (F.Q i').q.v) := by
      rw [← (I i').2.1]; exact ⟨_, rfl⟩
    exact (GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V j) ∅).2.2.2.2.2.2.1 _ _ (fun p hp hn => hi' (hF.inj (hp.symm.trans hn))) hr
  · intro y hy
    rw [← hax i]
    exact (I i).2.2.2.1 (a i) y hy
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteLocalSupportExchangeDataTwistPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_finite_local_support_exchangeData_twistPlaces : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ A : ∀ i, Finset (GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∀ α, ∀ g ∈ (w.ε j α).support, ∃ a : ∀ i, GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k, ∀ i, a i ∈ A i ∧ g * ((F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) (a i))⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v) := by
  first | exact @GlobalTheory.QSuppTwo.main | exact GlobalTheory.QSuppTwo.main | (intros; apply GlobalTheory.QSuppTwo.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceFinitelyManyCells

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QFinOneAt



theorem core {D : D7} {c : Comm D} {v : VCom c} {t : Tup c} (hψ : IsStdChar D c.ψ (-1)) (hv : v.Is) (ht : t.Is)
    {χ : ℕ → (AE D)ˣ →* Circle} (Q' : QAt v χ) (χz : (AE D)ˣ →* Circle) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (V₁ : (t.sBF j (σ + 1) h).χV = χ j * χz) (W₁ : (t.sBF j (σ + 1) h).χW = χ j)
    (V₂ : (t.sFB j σ h).χV = χ (j + 1)) (W₂ : (t.sFB j σ h).χW = χ (j + 1) * χz)
    (ka : IsWeilDatumO c.ψ _ _ (χ j) (χ j) (t.kom j)) (kb : IsWeilDatumO c.ψ _ _ (χ (j + 1)) (χ (j + 1)) (t.kom (j + 1)))
    (a : GL (Q'.X j ⊕ Fin (2 * σ + 2 + 1)) Q'.k) :
    ∃ T : Finset (GL (Q'.X (j + 1) ⊕ Fin (2 * σ + 2)) Q'.k), ∀ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Q'.q.v) f₁ →
      ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = Q'.q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = Q'.q.v), ∀ x,
        flatBF (t.sBF j (σ + 1) h) (t.om j (g * Q'.gl j (2 * σ + 2 + 1) (by have := Q'.hs; omega) a,
          h₁ * Q'.gl (j + 1) (2 * σ + 2) (by have := Q'.hs; omega) x) (comb c.ψ _ _ (Q'.eL j) f₁)) ≠ 0 →
        ∃ τ ∈ T, ∃ r, Q'.gl (j + 1) (2 * σ + 2) (by have := Q'.hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧
          ∃ κ ∈ (Q'.T.lev (j + 1) (2 * σ + 2) (by have := Q'.hs; omega)).J, x = r * τ * κ := by
  classical
  haveI := Q'.unitVol.1
  have e0 : j + (2 * σ + 2 + 1) = Q'.s + 1 := by have := Q'.hs; omega
  have e1 : j + 1 + (2 * σ + 2) = Q'.s + 1 := by have := Q'.hs; omega
  have e2 : j + 1 + 1 + (2 * σ + 1) = Q'.s + 1 := by have := Q'.hs; omega
  have e01 : j + (2 * σ + 2) = Q'.s := by have := Q'.hs; omega
  have e12 : j + 1 + (2 * σ + 1) = Q'.s := by have := Q'.hs; omega
  let S : Dbl2 c.ψ σ :=
    { B := c.B j (σ + 1) h, J := c.J j (σ + 1) h, B' := c.B (j + 1 + 1) σ (idx_step h),
      s₁ := t.sBF j (σ + 1) h, s₂ := t.sFB j σ h, l := c.lnk j σ h, vL := c.vL j σ h,
      χ₁ := χ j, χ₂ := χ (j + 1), χz := χz, oma := t.kom j, omb := t.kom (j + 1),
      V₁ := V₁, W₁ := W₁, V₂ := V₂, W₂ := W₂, weila := ka, weilb := kb }
  let Fd : Dbl (ofSplit Q'.q) S.B S.J S.B' (Q'.X j) (Q'.X (j + 1)) (Q'.X (j + 1 + 1)) (2 * σ) :=
    { s := Q'.sc j, s_ne := Q'.sc_ne j, F₀ := Q'.FX j (by omega), F₁ := Q'.FX (j + 1) (by omega),
      F₂ := Q'.FX (j + 1 + 1) (by omega), G₀ := Q'.FY j _ e0, G₁ := Q'.FY (j + 1) _ e1, G₂ := Q'.FY (j + 1 + 1) _ e2,
      bes := Q'.bes j (σ + 1) h _ e0, jac := Q'.jac j (σ + 1) h _ e1,
      bes' := by rw [← Q'.sc_step j]; exact Q'.bes (j + 1 + 1) σ (idx_step h) _ e2 }
  have reg1 := (Q'.reg.2.2 (j + 1) _ e1)
  have reg2 := (Q'.reg.2.2 (j + 1 + 1) _ e2)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, A₁, A₂, cov₁, cov₂, d₁, d₂, ent₁, ent₂, e₀, e₂, one₀, one₂, m₁, m₂, haar₁, haar₂,
      vol₁, vol₂, -, -, -⟩ :=
    GlobalTheory.QPl.Inhab.exists_qstep hψ S Q'.ν Q'.unitVol Q'.q Q'.ψk Q'.char Q'.cond (Q'.X j) (Q'.X (j + 1)) (Q'.X (j + 1 + 1))
      (2 * σ) Fd (Q'.T.mu (j + 1)) (Q'.T.mu (j + 1 + 1)) (Q'.mu j (by omega)).1 (Q'.mu (j + 1) (by omega)).1
      (Q'.mu j (by omega)).2 (Q'.mu (j + 1) (by omega)).2 (Q'.T.lev j _ e0) (Q'.T.lev (j + 1) _ e1) (Q'.T.lev (j + 1 + 1) _ e2)
      (Q'.reg.2.2 j _ e0).1 ⟨reg1.1, reg1.2.1⟩ ⟨reg2.1, reg2.2.1⟩ (Q'.le _ _ e1) (Q'.le _ _ e2)
      ⟨Q'.T.Phi j _ e01, Q'.reg.1 _ _ e01⟩ ⟨Q'.T.Phi (j + 1) _ e12, Q'.reg.1 _ _ e12⟩ (Q'.laws.1 j _ e01) (Q'.laws.1 (j + 1) _ e12)
      a 1 1
  let Q : QStep S :=
    { k := Q'.k, ν := Q'.ν, unitVol := Q'.unitVol, q := Q'.q, ψk := Q'.ψk, char := Q'.char, cond := Q'.cond,
      n₀ := Q'.X j, n₁ := Q'.X (j + 1), n₂ := Q'.X (j + 1 + 1), c := 2 * σ, F := Fd,
      gl₀ := Q'.gl j _ e0, gl₁ := Q'.gl (j + 1) _ e1, gl₂ := Q'.gl (j + 1 + 1) _ e2,
      loc₀ := Q'.gl_loc j _ e0, loc₁ := Q'.gl_loc (j + 1) _ e1, loc₂ := Q'.gl_loc (j + 1 + 1) _ e2,
      μ₁ := Q'.T.mu (j + 1), μ₂ := Q'.T.mu (j + 1 + 1), comp₁ := (Q'.mu j (by omega)).1, comp₂ := (Q'.mu (j + 1) (by omega)).1,
      open₁ := (Q'.mu j (by omega)).2, open₂ := (Q'.mu (j + 1) (by omega)).2,
      L₀ := Q'.T.lev j _ e0, L₁ := Q'.T.lev (j + 1) _ e1, L₂ := Q'.T.lev (j + 1 + 1) _ e2,
      co₁ := ⟨reg1.1, reg1.2.1⟩, co₂ := ⟨reg2.1, reg2.2.1⟩, le₁ := Q'.le _ _ e1, le₂ := Q'.le _ _ e2,
      Φ₁ := ⟨Q'.T.Phi j _ e01, Q'.reg.1 _ _ e01⟩, Φ₂ := ⟨Q'.T.Phi (j + 1) _ e12, Q'.reg.1 _ _ e12⟩,
      ty₁ := Q'.laws.1 j _ e01, ty₂ := Q'.laws.1 (j + 1) _ e12,
      D₁ := Q'.eL j, D₂ := Q'.eL (j + 1), dat₁ := Q'.eL_at j _ e01, dat₂ := Q'.eL_at (j + 1) _ e12,
      α := a, A₁ := A₁, A₂ := A₂, cov₁ := cov₁, cov₂ := cov₂, d₁ := d₁, d₂ := d₂, ent₁ := ent₁, ent₂ := ent₂,
      e₀ := e₀, e₂ := e₂, one₀ := one₀, one₂ := one₂, m₁ := m₁, m₂ := m₂, haar₁ := haar₁, haar₂ := haar₂,
      vol₁ := vol₁, vol₂ := vol₂ }
  obtain ⟨T₁, hT₁, -⟩ := GlobalTheory.T.splitPlaceDoubleStepFinitelyManyCellsUniform_proof D c.ψ hψ σ S Q a
  refine ⟨T₁, fun f₁ hf₁ g hg h₁ hh₁ x hx => ?_⟩
  obtain ⟨Tm, hTm, hTmO⟩ := (GlobalTheory.LocMod.indicator_vac D Q'.k Q'.q Q'.unit (Q'.X (j + 1) ⊕ Fin (2 * σ + 2)) (Q'.X j ⊕ Fin (2 * σ + 2 + 1))
    (c.V j) (c.V (j + 1)) (Q'.FY j _ e0) (Q'.FY (j + 1) _ e1) c.ψ Q'.ψk hψ Q'.char Q'.cond (v.N j) (v.N (j + 1))
    (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) (Q'.latY j _ e0) (Q'.latY (j + 1) _ e1)).2 f₁ hf₁
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Q'.k) (Y := Q'.X (j + 1) ⊕ Fin (2 * σ + 2)) (Y' := Q'.X j ⊕ Fin (2 * σ + 2 + 1))
  obtain ⟨f₀, f₂, -, -, -, -, hv2⟩ := GlobalTheory.QPl.Inhab.exists_vac hψ (ι := Unit) (fun _ => Q) (fun _ _ _ => rfl)
  have hvac : Q.Vac f₁ f₂ := ⟨⟨Tm, O, hTm, hO, hTmO O hO⟩, (hv2 ()).2⟩
  have hom := (ht.sBF j (σ + 1) h).1
  obtain ⟨τ, hτ, r, hr, κ, hκ, hx'⟩ := hT₁ f₁ f₂ hvac g hg h₁ hh₁ x (by
    change flatBF (t.sBF j (σ + 1) h) ((t.sBF j (σ + 1) h).om _ _) ≠ 0
    rw [hom]; exact hx)
  exact ⟨τ, hτ, r, hr, κ, hκ, hx'⟩

theorem finOne_pin : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r) (a : GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∃ T : Finset (GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k), ∀ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f₁ → ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v), ∀ x, flatBF (t.sBF j (σ + 1) h) (t.om j (g * (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a, h₁ * (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) x) (comb c.ψ _ _ ((F.Q i).eL j) f₁)) ≠ 0 → ∃ τ ∈ T, ∃ r, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧ ∃ κ ∈ ((F.Q i).T.lev (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega)).J, x = r * τ * κ := by
  intro D c v t w F hc ht hv _ hP j σ h i a
  obtain ⟨χz, V₁, W₁, V₂, W₂⟩ := hP.mid j σ h
  exact core hc.std hv ht (F.Q i) χz j σ h V₁ W₁ V₂ W₂ (hP.kom j (by omega)) (hP.kom (j + 1) (by omega)) a

end GlobalTheory.QFinOneAt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceFinitelyManyCellsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_twistPlace_finitely_many_cells : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r) (a : GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∃ T : Finset (GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k), ∀ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f₁ → ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v), ∀ x, flatBF (t.sBF j (σ + 1) h) (t.om j (g * (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a, h₁ * (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) x) (comb c.ψ _ _ ((F.Q i).eL j) f₁)) ≠ 0 → ∃ τ ∈ T, ∃ r, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧ ∃ κ ∈ ((F.Q i).T.lev (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega)).J, x = r * τ * κ := by
  first | exact @GlobalTheory.QFinOneAt.finOne_pin | exact GlobalTheory.QFinOneAt.finOne_pin | (intros; apply GlobalTheory.QFinOneAt.finOne_pin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstVariableSupportFiniteCellsAtTwistPlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QFinSupp

theorem locK_congr {D : D7} {c : Comm D} {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle} (Q : QAt v χ) (j d d' : ℕ) (e : d = d')
    (h1 : j + d = Q.s + 1) (h2 : j + d' = Q.s + 1) :
    (Q.T.lev j d h1).J.map (Q.gl j d h1) = (Q.T.lev j d' h2).J.map (Q.gl j d' h2) := by
  subst e; rfl

theorem cells_at : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r) (a : GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∃ T : Finset (GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k), ∀ Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v), ∀ x, flatBF (t.sBF j (σ + 1) h) (t.om j (g * (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a, h₁ * (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) x) (comb c.ψ _ _ (w.eQ j) Ψ₁)) ≠ 0 → ∃ τ ∈ T, ∃ r, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧ ∃ κ ∈ ((F.Q i).T.lev (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega)).J, x = r * τ * κ := by
  intro D c v t w F hc ht hv hW hF j σ h i a
  obtain ⟨T, hT⟩ := GlobalTheory.T.seeSaw_twistPlace_finitely_many_cells D c v t w F hc ht hv hW hF j σ h i a
  refine ⟨T, fun Ψ₁ hΨ g hg h₁ hh x hne => ?_⟩
  obtain ⟨f₁, hf₁, e⟩ := GlobalTheory.T.twistCombination_splits_singlePlace_vacuum D c v t w F hc hv hF j (by omega) i Ψ₁ hΨ
  rw [e] at hne
  exact hT f₁ hf₁ g hg h₁ hh x hne

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ T₁ : Finset (GA D (c.V (j + 1))), (∀ q ∈ T₁, q ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) ∧ ∀ Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∀ α, ∀ g ∈ (w.ε j α).support, ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q), flatBF (t.sBF j (σ + 1) h) (t.om j (g, x) (comb c.ψ _ _ (w.eQ j) Ψ₁)) ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q) ∧ ∃ q ∈ T₁, ∃ k ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h, x = r * q * k := by
  intro D c v t w F hc ht hv hW hF j σ h
  classical
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_finite_local_support_exchangeData_twistPlaces D c v t w F hF j σ h
  choose T hT using fun i a => cells_at D c v t w F hc ht hv hW hF j σ h i a
  obtain ⟨P, hPH, hPat, hPdec⟩ := GlobalTheory.T.twistPlaces_group_eq_product_local_groups D c v t w F hF j σ h
  refine ⟨(Fintype.piFinset fun i => (A i).biUnion (T i)).image P, ?_, ?_⟩
  · intro q hq
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hq
    exact hPat y
  · intro Ψ₁ hΨ α g hg x hx hne
    obtain ⟨a, ha⟩ := hA α g hg
    obtain ⟨y, rfl, hy⟩ := hPdec x hx
    have key := fun i => hT i (a i) Ψ₁ hΨ _ (ha i).2 _ (hy i) (y i) (by simpa only [inv_mul_cancel_right] using hne)
    choose τ hτ r hr κ hκ hyeq using key
    have hyy : y = r * τ * κ := funext hyeq
    refine ⟨P r, hPH _ r hr, hPat r, P τ, Finset.mem_image.2 ⟨τ, Fintype.mem_piFinset.2 fun i =>
      Finset.mem_biUnion.2 ⟨a i, (ha i).1, hτ i⟩, rfl⟩, P κ, hPH _ κ fun i => ?_, by rw [hyy, map_mul, map_mul]⟩
    refine Subgroup.mem_iSup_of_mem i ?_
    rw [GlobalTheory.QuotientFiniteLevel.locK, locK_congr (F.Q i) (j + 1) _ (2 * σ + 2) (by have := (F.Q i).hs; omega) _ (by have := (F.Q i).hs; omega)]
    exact Subgroup.mem_map_of_mem _ (hκ i)

end GlobalTheory.QFinSupp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstVariableSupportFiniteCellsAtTwistPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.firstVariable_support_finite_cells_at_twist_places : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ T₁ : Finset (GA D (c.V (j + 1))), (∀ q ∈ T₁, q ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) ∧ ∀ Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∀ α, ∀ g ∈ (w.ε j α).support, ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q), flatBF (t.sBF j (σ + 1) h) (t.om j (g, x) (comb c.ψ _ _ (w.eQ j) Ψ₁)) ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q) ∧ ∃ q ∈ T₁, ∃ k ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h, x = r * q * k := by
  first | exact @GlobalTheory.QFinSupp.main | exact GlobalTheory.QFinSupp.main | (intros; apply GlobalTheory.QFinSupp.main <;> assumption)
end
end
