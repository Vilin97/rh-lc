module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelCombinationEqSinglePlaceOnVacuum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelElementEqProdLocalParts
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFlatMapContractionSupportAtLevelPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawProdLocalCellsDistinctPlacesStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsFoldr
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WithMuEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrivialAtPlaceCommSeeSawCombinationKeepsVacuum

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrderedProdLocalPartsSeparatesPlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.SepProd

variable {D : D7}

theorem list_ofFn_prod_eq {M : Type*} [Monoid M] : ∀ {n : ℕ} (f : Fin n → M) (i : Fin n), (∀ j, j ≠ i → f j = 1) →
    (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | n + 1, f, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · have hprod : (List.ofFn fun j : Fin n => f j.succ).prod = 1 :=
        List.prod_eq_one (List.forall_mem_ofFn_iff.mpr fun j => h _ (Fin.succ_ne_zero j))
      rw [hprod, mul_one]
    · rw [h 0 (Fin.succ_ne_zero i').symm, one_mul]
      exact list_ofFn_prod_eq (fun j => f j.succ) i' fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

theorem mem_grpOff_of_suppAt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) {V : HSp D} {g : GA D V} (hg : SuppAt p.e V g) {v : GlobalTheory.FinPl.Pl D} (hv : p.v ≠ v) :
    g ∈ grpOff V (· = v) := by
  rw [grpOff, congGrp, MonoidHom.mem_ker]
  ext i j
  change Ideal.Quotient.mk _ (Formalism.L2.Theta.mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j
  rw [← Matrix.map_one (Ideal.Quotient.mk (idOff D (· = v))) (map_zero _) (map_one _), Matrix.map_apply,
    Ideal.Quotient.eq]
  have hmem : Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ idAt D (· = p.v) := by
    have := hg i j
    rw [Matrix.sub_apply] at this
    rw [← this]
    exact Ideal.mul_mem_right _ _ (GlobalTheory.FinPl.FrameLat.sum_mem_idAt p)
  have h2 := (Ideal.mem_inf.1 hmem).2
  rw [Ideal.mem_iInf] at h2
  rw [idOff, Ideal.mem_iInf]
  rintro ⟨w, rfl⟩
  exact h2 ⟨w, fun e => hv e.symm⟩

end GlobalTheory.SeeSaw.SepProd


open GlobalTheory.SeeSaw.SepProd in
theorem GlobalTheory.SeeSaw.SepProd.prod_sep : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v), GPin G → ∀ (j' : ℕ) (xs : Fin n → GA D (c.V j')), (∀ i, SuppAt (G i).q.e (c.V j') (xs i)) → ∀ (i : Fin n), ∃ y ∈ grpOff (c.V j') (· = (G i).q.v), (List.ofFn xs).prod = xs i * y := by
  intro D c v n G hG j' xs hxs i
  refine ⟨(xs i)⁻¹ * (List.ofFn xs).prod, ?_, by rw [mul_inv_cancel_left]⟩
  have hoff : ∀ i', i' ≠ i → xs i' ∈ grpOff (c.V j') (· = (G i).q.v) := fun i' hi' =>
    mem_grpOff_of_suppAt (G i').q (hxs i') fun e => hi' (hG.inj e)
  rw [grpOff, congGrp, MonoidHom.mem_ker, map_mul, map_inv, map_list_prod, List.map_ofFn,
    list_ofFn_prod_eq (_ ∘ xs) i fun j hj => MonoidHom.mem_ker.1 (hoff j hj), Function.comp_apply, inv_mul_cancel]

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrderedProdLocalPartsSeparatesPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.ordered_prod_local_parts_separates_place : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v), GPin G → ∀ (j' : ℕ) (xs : Fin n → GA D (c.V j')), (∀ i, SuppAt (G i).q.e (c.V j') (xs i)) → ∀ (i : Fin n), ∃ y ∈ grpOff (c.V j') (· = (G i).q.v), (List.ofFn xs).prod = xs i * y := by
  first | exact @GlobalTheory.SeeSaw.SepProd.prod_sep | exact GlobalTheory.SeeSaw.SepProd.prod_sep | (intros; apply GlobalTheory.SeeSaw.SepProd.prod_sep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelCombinationEqSinglePlaceOnVacuumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_fixedLevel_combination_eq_single_place_on_vacuum : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ}, c.Is → v.Is → ∀ (G : Fin n → GLoc v), GPin G → ∀ (j : ℕ), j + 1 < D.R.m → ∀ (Ψ : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ → ∀ (i : Fin n), ∃ F, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) F ∧ comb c.ψ _ _ (v.eG j) Ψ = comb c.ψ _ _ ((G i).eg j) F := by
  first | exact @GlobalTheory.GSuppComb.comb_eq_at_place | exact GlobalTheory.GSuppComb.comb_eq_at_place | (intros; apply GlobalTheory.GSuppComb.comb_eq_at_place <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelElementEqProdLocalPartsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_fixedLevel_element_eq_prod_local_parts : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ}, c.Is → v.Is → ∀ (G : Fin n → GLoc v), GPin G → ∀ (j' : ℕ), ∀ x ∈ grpAt (c.V j') (· ∈ v.gP), ∃ xs : Fin n → GA D (c.V j'), (∀ i, SuppAt (G i).q.e (c.V j') (xs i)) ∧ x = (List.ofFn xs).prod := by
  first | exact @GlobalTheory.LevelCut.grpAt_eq_prod_local | exact GlobalTheory.LevelCut.grpAt_eq_prod_local | (intros; apply GlobalTheory.LevelCut.grpAt_eq_prod_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFirstFlatMapSupportAtLevelPlace

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.GSuppFirst

theorem gsupp1_at : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp1 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F → ∀ (x : GA D (c.V (j + 1))), SuppAt Gi.q.e (c.V (j + 1)) x → flatBF (t.sBF j (σ + 1) h) (t.om j (1, x) (comb c.ψ _ _ (Gi.eg j) F)) ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, SuppAt Gi.q.e (c.V (j + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  intro D c v hc hv hG t ht Gi hch j σ h F hF x hx hflat
  have hs := Gi.hs
  obtain ⟨Tm, hTm, hTmO⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Gi.k Gi.q Gi.unit _ _ (c.V j) (c.V (j + 1))
    (Gi.FY j (2 * σ + 1 + 1 + 1) (by omega)) (Gi.FY (j + 1) (2 * σ + 1 + 1) (by omega)) c.ψ Gi.S.ψ hc.std Gi.char Gi.S.cond
    (v.N j) (v.N (j + 1)) (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) (Gi.latY j _ _) (Gi.latY (j + 1) _ _)).2 F hF
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Gi.k)
    (Y := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
    (Y' := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (2 * σ + 1 + 1 + 1))
  have H2 : j + (2 * σ + 1 + 1) = Gi.s := by omega
  let Φ : GlobalTheory.SplitWeil.SB _ := ⟨_, (GModel.phi_sb Gi).1 j (2 * σ + 1 + 1) H2⟩
  have hcomb : Tm Φ = comb c.ψ _ _ (Gi.eg j) F := by
    rw [← hTmO O hO]; exact (Gi.eg_is j (2 * σ + 1 + 1) H2).2 Tm hTm O Φ hO rfl
  obtain ⟨μ, hμt, hμu, hBF, -⟩ := hch
  have hW := MuUnits.withMu_eq Gi.k Gi.s D.R.k Gi.S (Fin D.R.t) μ hμt hμu
  let Fd : GlobalTheory.LocMod.Dbl (GlobalTheory.LocMod.ofSplit Gi.q) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1 + 1)) (2 * σ) :=
    { s := Gi.sc j
      s_ne := fun h0 => by have := Gi.sc_unit j; rw [h0, map_zero] at this; exact zero_ne_one this
      F₀ := Gi.FX j (by omega)
      F₁ := Gi.FX (j + 1) (by omega)
      F₂ := Gi.FX (j + 1 + 1) (by omega)
      G₀ := Gi.FY j (2 * σ + 1 + 1 + 1) (by omega)
      G₁ := Gi.FY (j + 1) (2 * σ + 1 + 1) (by omega)
      G₂ := Gi.FY (j + 1 + 1) (2 * σ + 1) (by omega)
      bes := Gi.bes j (σ + 1) h _ _
      jac := Gi.jac j (σ + 1) h _ _
      bes' := by rw [← Gi.sc_step j]; exact Gi.bes (j + 1 + 1) σ (idx_step h) _ _ }
  have hΦ : Φ.1 = ((withMu Gi.S μ hμt).T (Fin D.R.t)).Phi j (2 * σ + 1 + 1) (by omega) := (hW.1 j _ _).symm
  have hflat' : flatBF (t.sBF j (σ + 1) h) ((t.sBF j (σ + 1) h).om (1, x) (Tm Φ)) ≠ 0 := by
    rw [(ht.sBF j (σ + 1) h).1, hcomb]; exact hflat
  obtain ⟨r, hr, hrs, u, uk, hloc, huk, hxr⟩ := hG Gi.k (GlobalTheory.LocMod.ofSplit Gi.q) Gi.s D.R.k (withMu Gi.S μ hμt) (Fin D.R.t) c.ψ
    Gi.char j (2 * σ) (by omega) σ _ _ _ Fd (t.sBF j (σ + 1) h) (hBF j (σ + 1) h).1 Tm hTm Φ hΦ x hx hflat'
  refine ⟨r, hr, hrs, u, uk, hloc, ?_, hxr⟩
  rw [← (hW.2 (j + 1) (2 * σ + 1 + 1) (by omega)).1]; exact huk

end GlobalTheory.SeeSaw.GSuppFirst
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFirstFlatMapSupportAtLevelPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seesaw_first_flatMap_support_at_level_place : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp1 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F → ∀ (x : GA D (c.V (j + 1))), SuppAt Gi.q.e (c.V (j + 1)) x → flatBF (t.sBF j (σ + 1) h) (t.om j (1, x) (comb c.ψ _ _ (Gi.eg j) F)) ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, SuppAt Gi.q.e (c.V (j + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  first | exact @GlobalTheory.SeeSaw.GSuppFirst.gsupp1_at | exact GlobalTheory.SeeSaw.GSuppFirst.gsupp1_at | (intros; apply GlobalTheory.SeeSaw.GSuppFirst.gsupp1_at <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrivialAtPlaceCommSeeSawCombinationKeepsVacuumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trivialAtPlace_comm_seeSawCombination_keeps_vacuum : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → ∀ (Gi : GLoc v) (j : ℕ), j + 1 < D.R.m → ∀ (χS χT : (AE D)ˣ →* Circle) (om : Om (c.V j) (c.V (j + 1))), IsWeilDatumO c.ψ _ _ χS χT om → ∀ (F : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F → ∀ y ∈ grpOff (c.V (j + 1)) (· = Gi.q.v), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) (om (1, y) F) ∧ om (1, y) (comb c.ψ _ _ (Gi.eg j) F) = comb c.ψ _ _ (Gi.eg j) (om (1, y) F) := by
  first | exact @GlobalTheory.OffPlaceWeil.main | exact GlobalTheory.OffPlaceWeil.main | (intros; apply GlobalTheory.OffPlaceWeil.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedSupportFixedLevelPlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.GSuppAsm

theorem gsupp_of_local : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → GlobalTheory.LocMod.GSupp1 D → GlobalTheory.LocMod.GSupp2 D → FlatLaw D → ∀ t : Tup c, t.Is → (∀ i, (G i).Chars t) → GSupp (t := t) v := by
  intro D c v n G hc hv hG h1 h2 _hfl t ht hch j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂
  have hj : j + 1 < D.R.m := by omega
  have hj2 : j + 1 + 1 < D.R.m := by omega
  refine ⟨fun x hx hne => ?_, fun x hx hne => ?_⟩
  · obtain ⟨xs, hxs, rfl⟩ := GlobalTheory.T.seeSaw_fixedLevel_element_eq_prod_local_parts hc hv G hG (j + 1) x hx
    have hb : ∀ i, j + 1 + (2 * σ + 1 + 1) = (G i).s + 1 := fun i => by have := (G i).hs; omega
    refine GlobalTheory.T.seeSaw_prod_local_cells_distinct_places G hG (j + 1) hj (jacGrp (c.jac j (σ + 1) h).d) (fun _ => 2 * σ + 1 + 1) hb xs (fun i => ?_)
    obtain ⟨F, hF, hcomb⟩ := GlobalTheory.T.seeSaw_fixedLevel_combination_eq_single_place_on_vacuum hc hv G hG j hj Ψ₁ hΨ₁ i
    obtain ⟨y, hy, hprod⟩ := GlobalTheory.T.ordered_prod_local_parts_separates_place G hG (j + 1) xs hxs i
    have hw : IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) (t.sBF j (σ + 1) h).χV (t.sBF j (σ + 1) h).χW (t.om j) := by
      have := (t.sBF j (σ + 1) h).weil
      rw [(ht.sBF j (σ + 1) h).1] at this
      exact this
    obtain ⟨hF', hcm⟩ := GlobalTheory.T.trivialAtPlace_comm_seeSawCombination_keeps_vacuum hc hv (G i) j hj _ _ (t.om j) hw F hF y hy
    refine GlobalTheory.T.seesaw_first_flatMap_support_at_level_place hc hv h1 t ht (G i) (hch i) j σ h _ hF' (xs i) (hxs i) ?_
    rw [hprod, hcomb] at hne
    have e : t.om j (1, xs i * y) = t.om j (1, xs i) * t.om j (1, y) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e, Module.End.mul_apply, hcm] at hne
    exact hne
  · obtain ⟨xs, hxs, rfl⟩ := GlobalTheory.T.seeSaw_fixedLevel_element_eq_prod_local_parts hc hv G hG (j + 1 + 1) x hx
    have hb : ∀ i, j + 1 + 1 + (2 * σ + 1) = (G i).s + 1 := fun i => by have := (G i).hs; omega
    refine GlobalTheory.T.seeSaw_prod_local_cells_distinct_places G hG (j + 1 + 1) (by omega) (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o)
      (fun _ => 2 * σ + 1) hb xs (fun i => ?_)
    obtain ⟨F₁, hF₁, hcomb₁⟩ := GlobalTheory.T.seeSaw_fixedLevel_combination_eq_single_place_on_vacuum hc hv G hG j hj Ψ₁ hΨ₁ i
    obtain ⟨F₂, hF₂, hcomb₂⟩ := GlobalTheory.T.seeSaw_fixedLevel_combination_eq_single_place_on_vacuum hc hv G hG (j + 1) hj2 Ψ₂ hΨ₂ i
    obtain ⟨y, hy, hprod⟩ := GlobalTheory.T.ordered_prod_local_parts_separates_place G hG (j + 1 + 1) xs hxs i
    have hw : IsWeilDatumO c.ψ (c.V (j + 1)) (c.V (j + 1 + 1)) (t.sFB j σ h).χV (t.sFB j σ h).χW (t.om (j + 1)) := by
      have := (t.sFB j σ h).weil
      rw [(ht.sFB j σ h).1] at this
      exact this
    obtain ⟨hF₂', hcm⟩ := GlobalTheory.T.trivialAtPlace_comm_seeSawCombination_keeps_vacuum hc hv (G i) (j + 1) hj2 _ _ (t.om (j + 1)) hw F₂ hF₂ y hy
    refine GlobalTheory.T.seeSaw_flatMap_contraction_support_at_level_place hc hv h2 t ht (G i) (hch i) j σ h F₁ hF₁ _ hF₂' (xs i) (hxs i) ?_
    rw [hprod, hcomb₁, hcomb₂] at hne
    have e : t.om (j + 1) (1, xs i * y) = t.om (j + 1) (1, xs i) * t.om (j + 1) (1, y) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e, Module.End.mul_apply, hcm] at hne
    exact hne

end GlobalTheory.SeeSaw.GSuppAsm

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedSupportFixedLevelPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_unfoldedSupport_fixedLevelPlaces : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → GlobalTheory.LocMod.GSupp1 D → GlobalTheory.LocMod.GSupp2 D → FlatLaw D → ∀ t : Tup c, t.Is → (∀ i, (G i).Chars t) → GSupp (t := t) v := by
  first | exact @GlobalTheory.SeeSaw.GSuppAsm.gsupp_of_local | exact GlobalTheory.SeeSaw.GSuppAsm.gsupp_of_local | (intros; apply GlobalTheory.SeeSaw.GSuppAsm.gsupp_of_local <;> assumption)
end
end
