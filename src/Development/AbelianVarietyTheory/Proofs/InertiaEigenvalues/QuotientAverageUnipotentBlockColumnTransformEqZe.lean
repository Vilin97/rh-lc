module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PosMApplyNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousQuotientAveragePeriodicFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageMapLatticeEquivStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageProdFubini
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageProdFubiniStatement
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageMapLatticeEquivStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageTranslateInvariantStatement
import Mathlib.CategoryTheory.Countable
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageAdelicRationalPointsComm

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

section General

variable {G₁ G₂ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂]

variable [IsTopologicalAddGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁]
  [IsTopologicalAddGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂]

def swapEquiv (G₁ G₂ : Type) [AddCommGroup G₁] [TopologicalSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂] :
    (G₂ × G₁) ≃ₜ+ (G₁ × G₂) :=
  { AddEquiv.prodComm with
    continuous_toFun := continuous_swap
    continuous_invFun := continuous_swap }

theorem avg_comm_of_isCoLat {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} (h₁ : IsCoLat Γ₁) (h₂ : IsCoLat Γ₂)
    (Φ : G₁ × G₂ → ℂ) (hΦ : Per (Γ₁.prod Γ₂) Φ) :
    avg Γ₁ (fun x => avg Γ₂ (fun y => Φ (x, y))) = avg Γ₂ (fun y => avg Γ₁ (fun x => Φ (x, y))) := by
  have hs : Per (Γ₂.prod Γ₁) (fun p : G₂ × G₁ => Φ (p.2, p.1)) := by
    refine ⟨hΦ.1.comp continuous_swap, fun γ hγ x => ?_⟩
    exact hΦ.2 (γ.2, γ.1) ⟨hγ.2, hγ.1⟩ (x.2, x.1)
  have a := GlobalTheory.T.quotientAverage_prod_fubini G₁ G₂ Γ₁ Γ₂ h₁ h₂ Φ hΦ
  have b := GlobalTheory.T.quotientAverage_prod_fubini G₂ G₁ Γ₂ Γ₁ h₂ h₁ _ hs
  have c := GlobalTheory.T.quotientAverage_map_lattice_equiv (G₂ × G₁) (G₁ × G₂) (Γ₂.prod Γ₁) (Γ₁.prod Γ₂) (isCoLat_prod h₂ h₁) (isCoLat_prod h₁ h₂) (swapEquiv G₁ G₂)
    (fun x => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩) Φ hΦ
  exact a.symm.trans (c.symm.trans b)

end General

theorem avg_comm (E : Type) [Field E] [NumberField E] (ι κ : Type) [Fintype ι] [Fintype κ]
    (Φ : (ι → Ad E) × (κ → Ad E) → ℂ) (hΦ : Per ((ratV E ι).prod (ratV E κ)) Φ) :
    avg (ratV E ι) (fun x => avg (ratV E κ) (fun y => Φ (x, y))) =
      avg (ratV E κ) (fun y => avg (ratV E ι) (fun x => Φ (x, y))) :=
  avg_comm_of_isCoLat (isCoLat_ratV E ι) (isCoLat_ratV E κ) Φ hΦ

end GlobalTheory.CuspGeneric
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageAdelicRationalPointsCommStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.quotientAverage_adelicRationalPoints_comm : ∀ (E : Type) [Field E] [NumberField E] (ι κ : Type) [Fintype ι] [Fintype κ] (Φ : (ι → Ad E) × (κ → Ad E) → ℂ), Per ((ratV E ι).prod (ratV E κ)) Φ → avg (ratV E ι) (fun x => avg (ratV E κ) (fun y => Φ (x, y))) = avg (ratV E κ) (fun y => avg (ratV E ι) (fun x => Φ (x, y))) := by
  first | exact @GlobalTheory.CuspGeneric.avg_comm | exact GlobalTheory.CuspGeneric.avg_comm | (intros; apply GlobalTheory.CuspGeneric.avg_comm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageSumIndexFubini

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

def sumArrowAddHomeo (A ι κ : Type) [AddCommGroup A] [TopologicalSpace A] :
    ((ι → A) × (κ → A)) ≃ₜ+ (ι ⊕ κ → A) where
  toFun p := Sum.elim p.1 p.2
  invFun f := (fun i => f (Sum.inl i), fun j => f (Sum.inr j))
  left_inv _ := rfl
  right_inv f := by ext (i | j) <;> rfl
  map_add' p q := by ext (i | j) <;> rfl
  continuous_toFun := by
    refine continuous_pi fun s => ?_
    rcases s with i | j
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply j).comp continuous_snd
  continuous_invFun :=
    (continuous_pi fun i => continuous_apply _).prodMk (continuous_pi fun j => continuous_apply _)

theorem sum_elim_mem_ratV (E : Type) [Field E] [NumberField E] (ι κ : Type) (x : ι → Ad E) (y : κ → Ad E) :
    Sum.elim x y ∈ ratV E (ι ⊕ κ) ↔ x ∈ ratV E ι ∧ y ∈ ratV E κ := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨⟨fun i => c (Sum.inl i), funext fun i => congrFun hc (Sum.inl i)⟩,
      ⟨fun j => c (Sum.inr j), funext fun j => congrFun hc (Sum.inr j)⟩⟩
  · rintro ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩
    refine ⟨Sum.elim c d, funext fun s => ?_⟩
    rcases s with i | j <;> rfl

theorem avg_sum_index : ∀ (E : Type) [Field E] [NumberField E] (ι κ : Type) [Fintype ι] [Fintype κ]
    (Φ : (ι ⊕ κ → Ad E) → ℂ), Per (ratV E (ι ⊕ κ)) Φ →
    avg (ratV E (ι ⊕ κ)) Φ = avg (ratV E ι) (fun x => avg (ratV E κ) (fun y => Φ (Sum.elim x y))) := by
  intro E _ _ ι κ _ _ Φ hΦ
  have hι := isCoLat_ratV E ι
  have hκ := isCoLat_ratV E κ
  have hs := isCoLat_ratV E (ι ⊕ κ)
  have hp : IsCoLat ((ratV E ι).prod (ratV E κ)) := by
    obtain ⟨d₁, K₁, hK₁, c₁⟩ := hι
    obtain ⟨d₂, K₂, hK₂, c₂⟩ := hκ
    refine ⟨?_, K₁ ×ˢ K₂, hK₁.prod hK₂, fun x => ?_⟩
    · let f : ↥((ratV E ι).prod (ratV E κ)) → ratV E ι × ratV E κ := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
      have hf : Continuous f :=
        (continuous_subtype_val.fst.subtype_mk _).prodMk (continuous_subtype_val.snd.subtype_mk _)
      refine DiscreteTopology.of_continuous_injective hf fun p q h => ?_
      have e₁ := congrArg (fun r => (r.1 : ι → Ad E)) h
      have e₂ := congrArg (fun r => (r.2 : κ → Ad E)) h
      exact Subtype.ext (Prod.ext e₁ e₂)
    · obtain ⟨γ₁, m₁, k₁⟩ := c₁ x.1
      obtain ⟨γ₂, m₂, k₂⟩ := c₂ x.2
      exact ⟨(γ₁, γ₂), ⟨m₁, m₂⟩, k₁, k₂⟩
  let e := sumArrowAddHomeo (Ad E) ι κ
  have he : ∀ p, e p ∈ ratV E (ι ⊕ κ) ↔ p ∈ (ratV E ι).prod (ratV E κ) := fun p =>
    (sum_elim_mem_ratV E ι κ p.1 p.2).trans AddSubgroup.mem_prod.symm
  have hper : Per ((ratV E ι).prod (ratV E κ)) (fun p => Φ (e p)) := by
    refine ⟨hΦ.1.comp e.continuous_toFun, fun γ hγ x => ?_⟩
    have : e (γ + x) = e γ + e x := map_add e γ x
    simp only [this]
    exact hΦ.2 _ ((he γ).2 hγ) _
  have h1 := GlobalTheory.T.quotientAverage_map_lattice_equiv _ _ _ _ hp hs e he Φ hΦ
  have h2 := GlobalTheory.T.quotientAverage_prod_fubini _ _ _ _ hι hκ _ hper
  rw [← h1, h2]
  rfl

end GlobalTheory.CuspGeneric
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageSumIndexFubiniStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.quotientAverage_sum_index_fubini : ∀ (E : Type) [Field E] [NumberField E] (ι κ : Type) [Fintype ι] [Fintype κ] (Φ : (ι ⊕ κ → Ad E) → ℂ), Per (ratV E (ι ⊕ κ)) Φ → avg (ratV E (ι ⊕ κ)) Φ = avg (ratV E ι) (fun x => avg (ratV E κ) (fun y => Φ (Sum.elim x y))) := by
  first | exact @GlobalTheory.CuspGeneric.avg_sum_index | exact GlobalTheory.CuspGeneric.avg_sum_index | (intros; apply GlobalTheory.CuspGeneric.avg_sum_index <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageUnipotentBlockColumnTransformEqZe

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric.ColSplit

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem mem_ratV_iff {ι : Type} (x : ι → Ad E) : x ∈ ratV E ι ↔ ∀ t, ∃ c : E, algebraMap E (Ad E) c = x t := by
  constructor
  · rintro ⟨c, rfl⟩ t
    exact ⟨c t, rfl⟩
  · intro h
    choose c hc using h
    exact ⟨c, funext hc⟩


variable (E) in
def reix {ι κ : Type} (τ : κ ≃ ι) : (κ → Ad E) ≃ₜ+ (ι → Ad E) where
  toFun w := w ∘ τ.symm
  invFun x := x ∘ τ
  left_inv w := by funext t; simp
  right_inv x := by funext t; simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

theorem reix_mem {ι κ : Type} (τ : κ ≃ ι) (w : κ → Ad E) : reix E τ w ∈ ratV E ι ↔ w ∈ ratV E κ := by
  simp only [mem_ratV_iff]
  change (∀ t, ∃ c : E, algebraMap E (Ad E) c = w (τ.symm t)) ↔ _
  exact ⟨fun h s => by simpa using h (τ s), fun h t => h _⟩

theorem per_reix {ι κ : Type} (τ : κ ≃ ι) {Φ : (ι → Ad E) → ℂ} (h : Per (ratV E ι) Φ) :
    Per (ratV E κ) (fun w => Φ (w ∘ τ.symm)) := by
  refine ⟨h.1.comp (reix E τ).continuous, fun γ hγ w => ?_⟩
  have := h.2 (reix E τ γ) ((reix_mem τ γ).2 hγ) (reix E τ w)
  exact this

theorem avg_reix {ι κ : Type} [Fintype ι] [Fintype κ] (τ : κ ≃ ι) {Φ : (ι → Ad E) → ℂ} (h : Per (ratV E ι) Φ) :
    avg (ratV E ι) Φ = avg (ratV E κ) (fun w => Φ (w ∘ τ.symm)) :=
  (GlobalTheory.T.quotientAverage_map_lattice_equiv _ _ _ _ (isCoLat_ratV E κ) (isCoLat_ratV E ι) (reix E τ) (reix_mem τ) Φ h).symm

theorem avg_sum_reix {ι κ₁ κ₂ : Type} [Fintype ι] [Fintype κ₁] [Fintype κ₂] (τ : κ₁ ⊕ κ₂ ≃ ι)
    {Φ : (ι → Ad E) → ℂ} (h : Per (ratV E ι) Φ) :
    avg (ratV E ι) Φ = avg (ratV E κ₁) (fun z => avg (ratV E κ₂) (fun y => Φ (Sum.elim z y ∘ τ.symm))) := by
  rw [avg_reix τ h]
  exact GlobalTheory.T.quotientAverage_sum_index_fubini E κ₁ κ₂ _ (per_reix τ h)

end Gen

end GlobalTheory.CuspGeneric.ColSplit

namespace GlobalTheory.CuspGeneric.ColSplit

section Main

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem sumElim_add_left {κ₁ κ₂ : Type} (c : κ₁ → E) (n : κ₁ → Ad E) (w : κ₂ → Ad E) :
    Sum.elim ((fun t => algebraMap E (Ad E) (c t)) + n) w =
      (fun s => algebraMap E (Ad E) (Sum.elim c 0 s)) + Sum.elim n w := by
  funext s; cases s <;> simp

theorem sumElim_add_right {κ₁ κ₂ : Type} (c : κ₂ → E) (n : κ₁ → Ad E) (w : κ₂ → Ad E) :
    Sum.elim n ((fun t => algebraMap E (Ad E) (c t)) + w) =
      (fun s => algebraMap E (Ad E) (Sum.elim 0 c s)) + Sum.elim n w := by
  funext s; cases s <;> simp

theorem blk_rat {r' m' : ℕ} {κ : Type} [Fintype κ] (σ : κ ≃ UnipotentBlockColumnIndex a r' m') {f : GA E a → ℂ}
    (hl : ∀ (c : UnipotentBlockColumnIndex a r' m' → E) g, f (ratGL E a (blkU c) * g) = f g) (c : κ → E) (v : κ → Ad E) (h : GA E a) :
    f (blkU (((fun t => algebraMap E (Ad E) (c t)) + v) ∘ σ.symm) * h) = f (blkU (v ∘ σ.symm) * h) := by
  have e : blkU (((fun t => algebraMap E (Ad E) (c t)) + v) ∘ σ.symm) =
      ratGL E a (blkU (c ∘ σ.symm)) * blkU (v ∘ σ.symm) := by
    rw [ratGL_blkU]
    exact posU_add _ _ _
  rw [e, mul_assoc, hl]

theorem continuous_sumElim_right {κ₁ κ₂ : Type} (n : κ₁ → Ad E) :
    Continuous fun w : κ₂ → Ad E => Sum.elim n w :=
  continuous_pi fun s => match s with
    | Sum.inl _ => continuous_const
    | Sum.inr l => continuous_apply l

theorem continuous_sumElim {κ₁ κ₂ : Type} : Continuous fun p : (κ₁ → Ad E) × (κ₂ → Ad E) => Sum.elim p.1 p.2 :=
  continuous_pi fun s => match s with
    | Sum.inl l => (continuous_apply l).comp continuous_fst
    | Sum.inr l => (continuous_apply l).comp continuous_snd

theorem per_position {r' m' : ℕ} {κ₁ κ₂ : Type} [Fintype κ₁] [Fintype κ₂] (σ : κ₁ ⊕ κ₂ ≃ UnipotentBlockColumnIndex a r' m')
    {f : GA E a → ℂ} (hc : Continuous f) (hl : ∀ (c : UnipotentBlockColumnIndex a r' m' → E) g, f (ratGL E a (blkU c) * g) = f g)
    (n : κ₁ → Ad E) (h : GA E a) : Per (ratV E κ₂) (fun w => f (blkU (Sum.elim n w ∘ σ.symm) * h)) := by
  refine ⟨hc.comp (((continuous_posU _).comp ((reix E σ).continuous.comp (continuous_sumElim_right n))).mul
    continuous_const), ?_⟩
  rintro _ ⟨c, rfl⟩ w
  change f (blkU (Sum.elim n ((fun t => algebraMap E (Ad E) (c t)) + w) ∘ σ.symm) * h) = _
  rw [sumElim_add_right, blk_rat σ hl]

theorem dot_col {r m : ℕ} (hr : r ≤ m) (z : HiIx a r (m + 1) → Ad E) (y : LoIx a r (m + 1) → Ad E) :
    dot (eLast a (m + 1)) (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm) =
      dot (eLast a (m + 1)) (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) := by
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : r ≤ (t.1.1 : ℕ)
  · have e : (colEquiv a r (m + 1)).symm t = Sum.inl ⟨t, h⟩ := Equiv.sumCompl_symm_apply_of_pos (p := fun t : UnipotentBlockColumnIndex a (m + 1) (m + 1) => r ≤ (t.1.1 : ℕ)) h
    simp only [Function.comp, e, Sum.elim_inl]
  · have : (eLast a (m + 1) t : E) = 0 := by
      simp only [eLast]
      rw [if_neg]
      omega
    simp [this]

theorem colT_avg_blk_eq_zero (hψ : StdPsi ψ) (m : ℕ) (f : GA E a → ℂ) (hf : Good ψ (m + 1) f)
    (r : ℕ) (h0 : 0 < r) (hr : r ≤ m) (g : GA E a) :
    avg (ratV E (UnipotentBlockColumnIndex a r m)) (fun n => colT ψ (m + 1) f (blkU n * g)) = 0 := by
  have hr1 : r ≤ m + 1 := by omega
  have hl : ∀ {r' : ℕ} (c : UnipotentBlockColumnIndex a r' (m + 1) → E) g, f (ratGL E a (blkU c) * g) = f g :=
    fun c g => hf.left _ (isMir_blkU c) g

  have hA : ∀ n : UnipotentBlockColumnIndex a r m → Ad E, colT ψ (m + 1) f (blkU n * g) =
      avg (ratV E (HiIx a r (m + 1))) (fun z => avg (ratV E (LoIx a r (m + 1))) (fun y =>
        ψ (-dot (eLast a (m + 1)) (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm)) *
          f (blkU (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm) * (blkU n * g)))) := by
    intro n
    unfold colT coefF
    exact avg_sum_reix (colEquiv a r (m + 1)) (per_coef hψ _ hf.cont hl _)
  have hB : ∀ (n : UnipotentBlockColumnIndex a r m → Ad E) (z : HiIx a r (m + 1) → Ad E),
      avg (ratV E (LoIx a r (m + 1))) (fun y =>
        ψ (-dot (eLast a (m + 1)) (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm)) *
          f (blkU (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm) * (blkU n * g))) =
      ψ (-dot (eLast a (m + 1)) (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm)) *
        avg (ratV E (LoIx a r (m + 1))) (fun w => f (blkU (Sum.elim n w ∘ (blkEquiv a r m hr1).symm) *
          (blkU (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) * g))) := by
    intro n z
    have e : ∀ y : LoIx a r (m + 1) → Ad E,
        ψ (-dot (eLast a (m + 1)) (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm)) *
          f (blkU (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm) * (blkU n * g)) =
        ψ (-dot (eLast a (m + 1)) (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm)) *
          f (blkU (Sum.elim n (y + -corr n z) ∘ (blkEquiv a r m hr1).symm) *
            (blkU (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) * g)) := by
      intro y
      rw [dot_col hr, ← mul_assoc, blkU_col_mul_blkU hr1, mul_assoc, sub_eq_add_neg]
    simp_rw [e]
    rw [avg_const_mul]
    exact congrArg _ (GlobalTheory.T.quotientAverage_translate_invariant _ _ (isCoLat_ratV _ _)
      (fun w => f (blkU (Sum.elim n w ∘ (blkEquiv a r m hr1).symm) *
          (blkU (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) * g)))
      (per_position (blkEquiv a r m hr1) hf.cont hl n _) (-corr n z))

  obtain ⟨Φ₂, hΦ₂⟩ : ∃ Φ₂ : (UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E) → ℂ, ∀ p, Φ₂ p =
      avg (ratV E (LoIx a r (m + 1))) (fun y =>
        ψ (-dot (eLast a (m + 1)) (Sum.elim p.2 y ∘ (colEquiv a r (m + 1)).symm)) *
          f (blkU (Sum.elim p.2 y ∘ (colEquiv a r (m + 1)).symm) * (blkU p.1 * g))) := ⟨_, fun _ => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : (UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E) → ℂ, ∀ p, H p =
      avg (ratV E (LoIx a r (m + 1))) (fun w => f (blkU (Sum.elim p.1 w ∘ (blkEquiv a r m hr1).symm) *
          (blkU (Sum.elim p.2 0 ∘ (colEquiv a r (m + 1)).symm) * g))) := ⟨_, fun _ => rfl⟩
  have hΦH : ∀ p, Φ₂ p = ψ (-dot (eLast a (m + 1)) (Sum.elim p.2 0 ∘ (colEquiv a r (m + 1)).symm)) * H p := by
    intro p
    rw [hΦ₂, hH, hB]
  have hHc : Continuous H := by
    have e : H = fun p => avg (ratV E (LoIx a r (m + 1))) (fun w =>
        (fun q : ((UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E)) × (LoIx a r (m + 1) → Ad E) =>
          f (blkU (Sum.elim q.1.1 q.2 ∘ (blkEquiv a r m hr1).symm) *
            (blkU (Sum.elim q.1.2 0 ∘ (colEquiv a r (m + 1)).symm) * g))) (p, w)) := funext hH
    rw [e]
    refine GlobalTheory.T.continuous_quotientAverage_periodic_family (LoIx a r (m + 1) → Ad E) (ratV E (LoIx a r (m + 1))) (isCoLat_ratV E _)
      ((UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E))
      (fun q => f (blkU (Sum.elim q.1.1 q.2 ∘ (blkEquiv a r m hr1).symm) *
            (blkU (Sum.elim q.1.2 0 ∘ (colEquiv a r (m + 1)).symm) * g))) ?_ ?_
    · have c₁ : Continuous fun q : ((UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E)) × (LoIx a r (m + 1) → Ad E) =>
          Sum.elim q.1.1 q.2 := continuous_sumElim.comp (continuous_fst.fst.prodMk continuous_snd)
      have c₂ : Continuous fun q : ((UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E)) × (LoIx a r (m + 1) → Ad E) =>
          Sum.elim q.1.2 (0 : LoIx a r (m + 1) → Ad E) :=
        continuous_sumElim.comp (continuous_fst.snd.prodMk continuous_const)
      exact hf.cont.comp (((continuous_posU _).comp ((reix E (blkEquiv a r m hr1)).continuous.comp c₁)).mul
        (((continuous_posU _).comp ((reix E (colEquiv a r (m + 1))).continuous.comp c₂)).mul continuous_const))
    · intro x γ hγ y
      exact (per_position (blkEquiv a r m hr1) hf.cont hl x.1 _).2 γ hγ y
  have hψc : Continuous fun p : (UnipotentBlockColumnIndex a r m → Ad E) × (HiIx a r (m + 1) → Ad E) =>
      ψ (-dot (eLast a (m + 1)) (Sum.elim p.2 0 ∘ (colEquiv a r (m + 1)).symm)) :=
    hψ.cont.comp ((continuous_dot _).comp ((reix E (colEquiv a r (m + 1))).continuous.comp
      (continuous_sumElim.comp (continuous_snd.prodMk continuous_const)))).neg
  have hPer : Per ((ratV E (UnipotentBlockColumnIndex a r m)).prod (ratV E (HiIx a r (m + 1)))) Φ₂ := by
    refine ⟨?_, ?_⟩
    · rw [funext hΦH]
      exact hψc.mul hHc
    · intro γ hγ p
      rw [AddSubgroup.mem_prod] at hγ
      obtain ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ := hγ
      have e₁ : γ.1 = fun t => algebraMap E (Ad E) (c₁ t) := hc₁.symm
      have e₂ : γ.2 = fun t => algebraMap E (Ad E) (c₂ t) := hc₂.symm
      have s₁ : Φ₂ (γ + p) = Φ₂ (p.1, γ.2 + p.2) := by
        rw [show γ + p = (γ.1 + p.1, γ.2 + p.2) from rfl, hΦH, hΦH]
        congr 1
        rw [hH, hH]
        congr 1
        funext w
        change f (blkU (Sum.elim (γ.1 + p.1) w ∘ _) * _) = _
        rw [e₁, sumElim_add_left, blk_rat _ hl]
      have s₂ : Φ₂ (p.1, γ.2 + p.2) = Φ₂ p := by
        rw [hΦ₂, hΦ₂]
        congr 1
        funext y
        change ψ (-dot _ (Sum.elim (γ.2 + p.2) y ∘ _)) * f (blkU (Sum.elim (γ.2 + p.2) y ∘ _) * _) = _
        have hm := hψ.map_dot (eLast a (m + 1)) (Sum.elim c₂ 0 ∘ (colEquiv a r (m + 1)).symm)
          (Sum.elim p.2 y ∘ (colEquiv a r (m + 1)).symm)
        rw [e₂, sumElim_add_left, blk_rat _ hl, AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv]
        congr 1
        exact congrArg _ hm
      rw [s₁, s₂]
  have hD : ∀ z : HiIx a r (m + 1) → Ad E, avg (ratV E (UnipotentBlockColumnIndex a r m)) (fun n => Φ₂ (n, z)) = 0 := by
    intro z
    simp_rw [hΦH]
    rw [avg_const_mul]
    have e : avg (ratV E (UnipotentBlockColumnIndex a r m)) (fun n => H (n, z)) =
        avg (ratV E (UnipotentBlockColumnIndex a r (m + 1))) (fun w => f (blkU w * (blkU (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) * g))) := by
      rw [avg_sum_reix (blkEquiv a r m hr1) (per_blk hf.cont hl _)]
      simp_rw [hH]
    rw [e, hf.van r h0 hr1, mul_zero]
  have hA' : (fun n => colT ψ (m + 1) f (blkU n * g)) = fun n => avg (ratV E (HiIx a r (m + 1))) (fun z => Φ₂ (n, z)) := by
    funext n
    rw [hA]
    simp_rw [hΦ₂]
  rw [hA', GlobalTheory.T.quotientAverage_adelicRationalPoints_comm E _ _ Φ₂ hPer]
  simp_rw [hD]
  simpa using avg_const_mul (ratV E (HiIx a r (m + 1))) 0 (fun _ => (1 : ℂ))

end Main

theorem _root_.GlobalTheory.CuspGeneric.avg_colT_blk_eq_zero : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ),
    StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → ∀ r, 0 < r → r ≤ m → ∀ g : GA E a,
      avg (ratV E (UnipotentBlockColumnIndex a r m)) (fun n => colT ψ (m + 1) f (blkU n * g)) = 0 :=
  fun _ _ _ _ _ hψ m f _ hf r h0 hr g => colT_avg_blk_eq_zero hψ m f hf r h0 hr g

end GlobalTheory.CuspGeneric.ColSplit
end
end
end
