module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellFaceRestrictionStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierDimFanCellExistsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdBalancedFormMemCellConeStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdBalancedFormVanishesLowRankStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimLeOfAddCellGenerators
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSummandsOfEvalZAdditiveCellStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvFunEvalZAddOfLinearOnRealConeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanMarkedFormUniqueInCell
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRankLeOfInRealConePolyhedralCellStatement
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormIndicatorValueInvariantHostFixingAut
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormIndicatorZeroOneBarycentresPolyFan
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsStarSubdivisionStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BarycentricSubdivisionStarStepCells
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimLeOfAddCellGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionBarycentreCellNextStageStatement

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierLabelMarkedFaceBound

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.MarkedFaces

theorem genRank_le_of_label_le {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (q : ℕ)
    (ψ lab : InvFun O) (i : ℕ) (hlab : IsCarrierDim bar q ψ lab)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (hX : Module.finrank O X ≤ q) {m : ℕ} (v : Fin m → LinearMap.BilinForm ℤ X) (hv : IsCell bar ψ v)
    (hb : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) :
    genRank v ≤ i + 1 := by
  set σ := ∑ j, v j with hσ
  have hσ1 : σ ∈ balForms bar X := Submodule.sum_mem _ fun j _ => hv.mem j
  have hσ2 : ∀ y, 0 ≤ σ y y := fun y => by
    simp only [hσ, LinearMap.sum_apply]; exact Finset.sum_nonneg fun j _ => hv.nonneg j y
  have hσv : InRCone v σ := ⟨fun _ => 1, fun _ => zero_le_one, toReal_sum' v⟩
  have hl := hb σ hσ1 hσ2 hσv
  rw [hlab X hX σ hσ1 hσ2] at hl
  have hS : ({k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ σ ∧
      genRank γ = k}).Nonempty := ⟨_, m, v, hv, hσv, rfl⟩
  obtain ⟨m', γ, hγ, hσγ, hrk⟩ := Nat.sInf_mem hS
  have hψσ : ψ.evalZ σ = ∑ j, ψ.evalZ (v j) := by
    have := (linearOn_iff ψ v).1 hv.linear (fun _ => 1) fun _ => zero_le_one
    rw [← toReal_sum', evalR_toReal] at this
    simpa using this
  have hin := GlobalTheory.T.inRealCone_summands_of_evalZ_additive_cell O bar ψ X m' γ hγ m v hv.mem hv.nonneg hσγ hψσ.le
  have hr := GlobalTheory.T.spanRank_le_of_inRealCone_polyhedralCell O bar ψ X m' m γ v hγ hv.mem hv.nonneg hin
  have h2 : sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ σ ∧
      genRank γ = k} ≤ i + 1 := by exact_mod_cast hl
  rw [hrk] at hr
  exact hr.trans h2

theorem inFace_iff_of_isMarked {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (hO : CMOrd O bar) (q : ℕ)
    (ψ lab : InvFun O) (i : ℕ) (hψ : IsPolyFan bar q ψ) (hlab : IsCarrierDim bar q ψ lab)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (hX : Module.finrank O X ≤ q) (hDom : Dominates bar X) {m : ℕ} (v : Fin m → LinearMap.BilinForm ℤ X)
    (hv : IsCell bar ψ v)
    (hb : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ))
    {β : LinearMap.BilinForm ℤ X} (hβ : IsMarked bar ψ lab i X β) (hβv : InRCone v β) (x : LinearMap.BilinForm ℤ X) :
    InFace bar ψ lab β x ↔ x ∈ balForms bar X ∧ (∀ y, 0 ≤ x y y) ∧ InRCone v x := by
  obtain ⟨hβ1, hβ2, -, hβl, -⟩ := hβ
  constructor
  · rintro ⟨hx1, hx2, -, hx4, hx5⟩
    exact ⟨hx1, hx2, GlobalTheory.T.psd_balanced_form_mem_cell_cone O bar hO q ψ lab hψ hlab X hX hDom m v hv β hβ1 hβ2 hβv x hx1 hx2 hx4 hx5⟩
  · rintro ⟨hx1, hx2, hxv⟩
    have hrk := genRank_le_of_label_le bar q ψ lab i hlab X hX v hv hb
    have hvan := GlobalTheory.T.psd_balanced_form_vanishes_low_rank O bar hO q ψ lab hψ hlab X hX hDom m v hv β hβ1 hβ2 hβv (by rw [hβl]; exact_mod_cast hrk)
    have hsum := inRCone_add' hβv hxv
    have hs1 : β + x ∈ balForms bar X := add_mem hβ1 hx1
    have hs2 : ∀ y, 0 ≤ (β + x) y y := fun y => by
      simp only [LinearMap.add_apply]; exact add_nonneg (hβ2 y) (hx2 y)
    refine ⟨hx1, hx2, fun y hy => inRCone_apply_self_eq_zero hxv y fun j => hvan j y hy,
      GlobalTheory.T.invFun_evalZ_add_of_linearOn_realCone O ψ X m v hv.linear β x hβv hxv, le_antisymm ?_ ?_⟩
    · rw [hβl]; exact hb _ hs1 hs2 hsum
    · obtain ⟨c, hc, e⟩ := hxv
      exact carrierDim_le_of_add_cell O bar q ψ lab hlab X hX m v hv β hβ1 hβ2 (β + x) hs1 hs2 hβv 1 c one_pos hc
        (by rw [toReal_add', e, one_smul])

theorem eq_of_isMarked_of_inRCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β β' : LinearMap.BilinForm ℤ X, IsMarked bar ψ lab i X β → IsMarked bar ψ lab i X β' → InRCone v β → InRCone v β' → β = β' := by
  intro O _ _ _ _ bar hO q ψ lab i hDom hψ hlab X _ _ _ _ hX m v hv hb β β' hβ hβ' hβv hβ'v
  have hiff : ∀ x, InFace bar ψ lab β x ↔ InFace bar ψ lab β' x := fun x => by
    rw [inFace_iff_of_isMarked bar hO q ψ lab i hψ hlab X hX (hDom X) v hv hb hβ hβv x,
      inFace_iff_of_isMarked bar hO q ψ lab i hψ hlab X hX (hDom X) v hv hb hβ' hβ'v x]
  have hind : ∀ x, IsIndec bar ψ lab β x ↔ IsIndec bar ψ lab β' x := fun x => by
    simp only [IsIndec, hiff]
  obtain ⟨-, -, hp, -, S, hS, k, hk, hkS⟩ := hβ
  obtain ⟨-, -, hp', -, S', hS', k', -, hkS'⟩ := hβ'
  have hSS : S = S' := Finset.ext fun x => by rw [hS, hS', hind]
  exact eq_of_primitive_of_smul_eq hp hp' hk (by rw [hkS, hkS', hSS])

end GlobalTheory.CompanionTheory.Ar.Fan.MarkedFaces
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierLabelMarkedFaceBoundStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.isMarked_unique_of_inRCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β β' : LinearMap.BilinForm ℤ X, IsMarked bar ψ lab i X β → IsMarked bar ψ lab i X β' → InRCone v β → InRCone v β' → β = β' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.MarkedFaces.eq_of_isMarked_of_inRCone | exact GlobalTheory.CompanionTheory.Ar.Fan.MarkedFaces.eq_of_isMarked_of_inRCone | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.MarkedFaces.eq_of_isMarked_of_inRCone <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MarkingValueGaloisInvariant

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm

variable {O : Type} [CommRing O]

def twPi (σ : O ≃+* O) (n : ℕ) : (Fin n → O) ≃+ (Fin n → O) :=
  AddEquiv.piCongrRight fun _ => σ.toAddEquiv

def twForm (σ : O ≃+* O) (n : ℕ) :
    LinearMap.BilinForm ℤ (Fin n → O) ≃+ LinearMap.BilinForm ℤ (Fin n → O) where
  toFun β := β.compl₁₂ (twPi σ n).toIntLinearEquiv.toLinearMap (twPi σ n).toIntLinearEquiv.toLinearMap
  invFun β := β.compl₁₂ (twPi σ.symm n).toIntLinearEquiv.toLinearMap (twPi σ.symm n).toIntLinearEquiv.toLinearMap
  left_inv β := LinearMap.ext₂ fun a b => by
    change β (fun j => σ (σ.symm (a j))) (fun j => σ (σ.symm (b j))) = β a b
    simp only [RingEquiv.apply_symm_apply]
  right_inv β := LinearMap.ext₂ fun a b => by
    change β (fun j => σ.symm (σ (a j))) (fun j => σ.symm (σ (b j))) = β a b
    simp only [RingEquiv.symm_apply_apply]
  map_add' _ _ := LinearMap.ext₂ fun a b => by simp

@[simp] theorem twForm_apply (σ : O ≃+* O) (n : ℕ) (β : LinearMap.BilinForm ℤ (Fin n → O)) (a b : Fin n → O) :
    twForm σ n β a b = β (fun j => σ (a j)) (fun j => σ (b j)) := rfl

theorem twForm_mem_balForms {bar : O → O} (hb : CMOrd O bar) (σ : O ≃+* O) {n : ℕ}
    {β : LinearMap.BilinForm ℤ (Fin n → O)}
    (h : β ∈ balForms bar (Fin n → O)) : twForm σ n β ∈ balForms bar (Fin n → O) := by
  refine ⟨fun y z => by simp only [twForm_apply]; exact h.1 _ _, fun a y z => ?_⟩
  simp only [twForm_apply]
  have e1 : (fun j => σ ((a • y) j)) = σ a • fun j => σ (y j) := funext fun j => by simp
  have e2 : (fun j => σ ((bar a • z) j)) = bar (σ a) • fun j => σ (z j) := funext fun j => by
    simp [hb.comm]
  rw [e1, e2]
  exact h.2 _ _ _

theorem twForm_symm_twForm (σ : O ≃+* O) {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → O)) :
    twForm σ.symm n (twForm σ n β) = β := LinearMap.ext₂ fun a b => by simp

theorem twForm_mem_balForms_iff {bar : O → O} (hb : CMOrd O bar) (σ : O ≃+* O) {n : ℕ}
    (β : LinearMap.BilinForm ℤ (Fin n → O)) :
    twForm σ n β ∈ balForms bar (Fin n → O) ↔ β ∈ balForms bar (Fin n → O) :=
  ⟨fun h => by simpa [twForm_symm_twForm] using twForm_mem_balForms hb σ.symm h, twForm_mem_balForms hb σ⟩

theorem evalZ_twForm {w0 : O} {φ : InvFun O} (hφ : IsTwG w0 φ) {σ : O ≃+* O} (hσ : σ w0 = w0)
    {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → O)) : φ.evalZ (twForm σ n β) = φ.evalZ β := by
  unfold InvFun.evalZ
  rw [InvFun.eval_pi, InvFun.eval_pi]
  exact hφ σ hσ n fun a b => (β a b : ℝ)

theorem markVal_twist : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (w0 : O), CMOrd O bar → ∀ (ψ lab : InvFun O) (i : ℕ), IsTwG w0 ψ → IsTwG w0 lab →
    ∀ σ : O ≃+* O, σ w0 = w0 → ∀ (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ),
      markVal bar ψ lab i n (fun a b => B (fun j => σ (a j)) (fun j => σ (b j))) = markVal bar ψ lab i n B := by
  intro O _ _ _ _ bar w0 hb ψ lab i hψ hlab σ hσ n B
  classical
  unfold markVal
  by_cases h2 : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B a b = β a b
  · have h1 : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B (fun j => σ (a j)) (fun j => σ (b j)) = β a b :=
      ⟨twForm σ n h2.choose, fun a b => h2.choose_spec _ _⟩
    rw [dite_eq_left h1, dite_eq_left h2]
    have e : h1.choose = twForm σ n h2.choose := LinearMap.ext₂ fun a b => by
      have := (h1.choose_spec a b).symm.trans (h2.choose_spec _ _)
      exact_mod_cast this
    rw [e, isMarked_transport (T := (twPi σ n).toEquiv) (fun _ _ _ => rfl) (twForm_mem_balForms_iff hb σ)
      (evalZ_twForm hψ hσ) (evalZ_twForm hlab hσ)]
  · have h1 : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b,
        B (fun j => σ (a j)) (fun j => σ (b j)) = β a b := fun ⟨β, hβ⟩ =>
      h2 ⟨twForm σ.symm n β, fun a b => by
        have := hβ (fun j => σ.symm (a j)) (fun j => σ.symm (b j))
        simpa using this⟩
    rw [dite_eq_right h1, dite_eq_right h2]

end GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MarkingValueGaloisInvariantStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.marking_value_galois_invariant : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (ψ lab : InvFun O) (i : ℕ), IsTwG w0 ψ → IsTwG w0 lab → ∀ σ : O ≃+* O, σ w0 = w0 → ∀ (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ), markVal bar ψ lab i n (fun a b => B (fun j => σ (a j)) (fun j => σ (b j))) = markVal bar ψ lab i n B := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm.markVal_twist | exact GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm.markVal_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm.markVal_twist <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsMarkingCentreFunction

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.MarkingFunction

theorem exists_markFun_props_gen : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → IsTwG w0 lab → IsCarrierDim bar q ψ lab → ∃ w : InvFun O, IsTwG w0 w ∧ ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 0 ∨ w.evalZ β = 1) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → lab.evalZ β = ((i + 1 : ℕ) : ℝ)) ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) → w.evalZ β = 1 → w.evalZ β' = 1 → InRCone v β → InRCone v β' → β = β') ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone v β₀) := by
  intro O _ _ _ _ bar w0 hb q ψ lab i hD hψ htψ htlab hlab
  classical
  obtain ⟨w, hw⟩ := GlobalTheory.PolFan.Mark.exists_markFun bar ψ lab i
  have ev := fun {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (β : LinearMap.BilinForm ℤ X) => GlobalTheory.PolFan.Mark.evalZ_markFun hw (X := X) β
  have mk : ∀ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
      (β : LinearMap.BilinForm ℤ X), w.evalZ β = 1 → GlobalTheory.PolFan.Mark.IsMarked bar ψ lab i X β := fun β h => by
    rw [ev] at h
    split_ifs at h with h'
    · exact h'
    · norm_num at h
  refine ⟨w, fun σ hσ n B => by rw [hw, hw]; exact GlobalTheory.T.marking_value_galois_invariant O bar w0 hb ψ lab i htψ htlab σ hσ n B, ?_⟩
  intro X _ _ _ _ hX
  refine ⟨fun β _ _ => ?_, fun β _ _ h1 => (mk β h1).2.2.1, fun β _ _ h1 => (mk β h1).2.2.2.1,
    fun m v hv hle β _ _ β' _ _ h1 h1' hc hc' =>
      GlobalTheory.T.isMarked_unique_of_inRCone O bar hb q ψ lab i hD hψ hlab X hX m v hv hle β β' (mk β h1) (mk β' h1') hc hc',
    fun m v hv β hβ hp hc hl => ?_⟩
  · rw [ev]
    split_ifs <;> simp
  · obtain ⟨β₀, h0, hc0⟩ := GlobalTheory.T.exists_isMarked_inRCone_of_isCell_of_evalZ_eq O bar hb q ψ lab i hD hψ hlab X hX m v hv β hβ hp hc hl
    exact ⟨β₀, h0.1, h0.2.1, by rw [ev, if_pos h0], hc0⟩

end GlobalTheory.CompanionTheory.Ar.Fan.MarkingFunction
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsMarkingCentreFunctionStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.exists_marking_centre_function : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → IsTwG w0 lab → IsCarrierDim bar q ψ lab → ∃ w : InvFun O, IsTwG w0 w ∧ ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 0 ∨ w.evalZ β = 1) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → lab.evalZ β = ((i + 1 : ℕ) : ℝ)) ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) → w.evalZ β = 1 → w.evalZ β' = 1 → InRCone v β → InRCone v β' → β = β') ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone v β₀) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.MarkingFunction.exists_markFun_props_gen | exact GlobalTheory.CompanionTheory.Ar.Fan.MarkingFunction.exists_markFun_props_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.MarkingFunction.exists_markFun_props_gen <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.BarycentricStageExtension

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.BarycentricSubdivision

theorem baryStep : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ lab φ : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → IsTwG w0 lab → IsCarrierDim bar q ψ lab → IsTwG w0 φ → IsBaryStage bar q ψ lab φ (i + 1) → ∃ φ' : InvFun O, IsTwG w0 φ' ∧ IsBaryStage bar q ψ lab φ' i := by
  intro O _ _ _ _ bar w0 hO q ψ lab φ i hdom hψ hψt hlt hcar hφt hst
  obtain ⟨w, hwt, hw⟩ := GlobalTheory.T.exists_marking_centre_function O bar w0 hO q ψ lab i hdom hψ hψt hlt hcar
  obtain ⟨hφp, hφs, hφc⟩ := hst
  have hcen : IsCentreSet bar q φ w := by
    intro X _ _ _ _ hX
    obtain ⟨h1, h2, h3, h4, -⟩ := hw X hX
    refine ⟨h1, h2, fun m γ hγ β hβ hp β' hβ' hp' hw1 hw2 hc hc' => ?_⟩
    obtain ⟨b, a, v, u, -, hv, hcov, -, -, hvl, hoff, -⟩ := hφc X hX m γ hγ
    have inv : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → InRCone γ β → InRCone v β := by
      intro β hβ hp hw1 hc
      by_contra hn
      have := hoff β hβ hp (inRCone_trans hcov hc) hn
      rw [h3 β hβ hp hw1] at this
      exact lt_irrefl _ this
    exact h4 b v hv hvl β hβ hp β' hβ' hp' hw1 hw2 (inv β hβ hp hw1 hc) (inv β' hβ' hp' hw2 hc')
  obtain ⟨φ', hp', ht', hsub, hs1, hs2, hs3⟩ := GlobalTheory.T.exists_star_subdivision O bar w0 hO q φ w hdom hφp hφt hwt hcen
  refine ⟨φ', ht', hp', hsub.trans hφs, fun X _ _ _ _ hX n γ' hγ' => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw X hX
  have hnat : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℕ, lab.evalZ β = n :=
    fun β hβ hp => ⟨_, hcar X hX β hβ hp⟩
  have core : ∀ (b a : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X),
      IsCell bar φ (Fin.append v u) → IsCell bar ψ v → Function.Injective (fun j => lab.evalZ (u j)) →
      (∀ j, ((i + 1 : ℕ) : ℝ) < lab.evalZ (u j)) →
      (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) →
      (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → ¬ InRCone v β →
        ((i + 1 : ℕ) : ℝ) < lab.evalZ β) →
      (∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0) →
      ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone (Fin.append v u) β₀ →
      ∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
        IsFaceCut (Fin.append v u) s h → 0 < h β₀ →
      ∃ (b' a' : ℕ) (v' : Fin b' → LinearMap.BilinForm ℤ X) (u' : Fin a' → LinearMap.BilinForm ℤ X),
        IsCell bar φ' (Fin.append v' u') ∧ IsCell bar ψ v' ∧
        (∀ k, InRCone (Fin.append v' u') ((Fin.cons β₀ fun j => Fin.append v u (s j) : Fin (m' + 1) → _) k)) ∧
        Function.Injective (fun j => lab.evalZ (u' j)) ∧ (∀ j, (i : ℝ) < lab.evalZ (u' j)) ∧
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v' β → lab.evalZ β ≤ i) ∧
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v' u') β → ¬ InRCone v' β →
          (i : ℝ) < lab.evalZ β) ∧
        ∀ (d : Fin b' → ℤ) (c : Fin a' → ℤ), ∑ j, c j • u' j = ∑ k, d k • v' k → c = 0 := by
    intro b a v u hγ hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 hin0
    exact GlobalTheory.T.starSubdivision_barycentre_cell_next_stage O bar ψ lab φ' w i X b a v u hv hinj hlu hvl hoff hind hnat
      (fun m' s h hh => GlobalTheory.T.cell_face_restriction O bar hO q ψ hψ X hX (hdom X) b v hv m' s h hh) h5
      (fun β hβ hp β' hβ' hp' hw1 hw2 hc hc' => (hcen X hX).2.2 _ _ hγ β hβ hp β' hβ' hp' hw1 hw2 hc hc')
      (fun β₀ hb0 hp0 β hβ hp hin c₀ c hc₀ hc e =>
        GlobalTheory.T.carrierDim_le_of_add_cell_generators O bar q ψ lab hcar X hX b v hv β₀ hb0 hp0 β hβ hp hin c₀ c hc₀ hc e)
      β₀ hb0 hp0 hw0 (h3 β₀ hb0 hp0 hw0) hin0
      (fun m' s h hh hpos => hs2 X hX _ _ hγ β₀ hb0 hp0 hw0 hin0 m' s h hh hpos)
  rcases hs3 X hX n γ' hγ' with ⟨m, γ, hγ, hno, hcov'⟩ | ⟨m, δ, β₀, m', s, h, hδ, hb0, hp0, hw0, hin0, hcut, hpos, hcov'⟩
  · obtain ⟨b, a, v, u, hG, hv, hcov, hinj, hlu, hvl, hoff, hind⟩ := hφc X hX m γ hγ
    by_cases hc : ∃ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone (Fin.append v u) β₀
    · obtain ⟨β₀, hb0, hp0, hw0, hin0⟩ := hc
      have hnin : ¬ InRCone γ β₀ := fun hh => by
        have := hno β₀ hb0 hp0 hh
        rw [hw0] at this
        exact one_ne_zero this
      obtain ⟨m', s, h, hcut, hpos, hsub'⟩ := reduce_of_not_mem hG hγ hcov hb0 hp0 hin0 hnin
      obtain ⟨b', a', v', u', r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
        core b a v u hG hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 hin0 m' s h hcut hpos
      exact ⟨b', a', v', u', r1, r2, fun j => inRCone_trans r3 (inRCone_cons_of (n := 0) β₀
        (inRCone_trans hsub' (hcov' j))), r4, r5, r6, r7, r8⟩
    · push_neg at hc
      have hw0 : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → w.evalZ β = 0 :=
        fun β hβ hp hin => (h1 β hβ hp).resolve_right fun e => hc β hβ hp e hin
      refine ⟨b, a, v, u, hs1 X hX _ _ hG hw0, hv, fun j => inRCone_trans hcov (hcov' j), hinj,
        fun j => ?_, fun β hβ hp hin => ?_, fun β hβ hp hin hn => ?_, hind⟩
      · have := hlu j; push_cast at this ⊢; linarith
      · obtain ⟨k, hk⟩ := hnat β hβ hp
        have hle := hvl β hβ hp hin
        rw [hk] at hle ⊢
        have hle' : k ≤ i + 1 := by exact_mod_cast hle
        rcases hle'.lt_or_eq with hl | hl
        · exact_mod_cast Nat.lt_succ_iff.1 hl
        · obtain ⟨β₁, hb1, hp1, hw1, hin1⟩ := h5 b v hv β hβ hp hin (by rw [hk, hl])
          exact absurd (inRCone_append_left v u hin1) (hc β₁ hb1 hp1 hw1)
      · have := hoff β hβ hp hin hn; push_cast at this ⊢; linarith
  · obtain ⟨b, a, v, u, hG, hv, hcov, hinj, hlu, hvl, hoff, hind⟩ := hφc X hX m δ hδ
    obtain ⟨m'', s', h', hcut', hpos', hsub'⟩ := reduce_of_mem hG hδ hcov hin0 hcut hpos
    obtain ⟨b', a', v', u', r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
      core b a v u hG hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 (inRCone_trans hcov hin0) m'' s' h' hcut' hpos'
    exact ⟨b', a', v', u', r1, r2, fun j => inRCone_trans r3 (inRCone_trans (inRCone_cons_mono β₀ hsub') (hcov' j)),
      r4, r5, r6, r7, r8⟩

end GlobalTheory.CompanionTheory.Ar.Fan.BarycentricSubdivision
end
end
end
