module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimpLabMinValOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultCellsAmongOfIsPolyFan
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantOrbitCentreMarkingPolyFanStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntLinearFormCuttingSubcell
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyFanFaceCutByIntLinearFormIsCellStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarLabEvalZOfEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantPolyhedralFanStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionNoNewCellOfMaximalMultiplicityFanStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultCellsAmongOfIsPolyFanStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_multCellsAmong_of_isPolyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ : InvFun (𝓞 E)),
    IsPolyFan H.bar q φ → ∀ M : ℕ, ∃ n : ℕ, MultCellsAmong H.bar q φ M n := by
  first | exact @GlobalTheory.PolFan.CellClass.multCellsAmong_of_isPolyFan | exact GlobalTheory.PolFan.CellClass.multCellsAmong_of_isPolyFan | (intros; apply GlobalTheory.PolFan.CellClass.multCellsAmong_of_isPolyFan <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantLabelling

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.StarLab

theorem exists_isTwInv_simpLab_star : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H lab → SimpLab H.bar q φ lab → IsTwInv H w → IsCentreSet H.bar q φ w →
    IsPolyFan H.bar q ψ' → Subordinate H.bar q ψ' φ → IsStarOf H.bar q φ w ψ' →
    ∃ lab' : InvFun (𝓞 E), IsTwInv H lab' ∧ SimpLab H.bar q ψ' lab' := by
  intro E _ _ _ H q φ lab w ψ' hDom hφ hlab hSL hw hC _ _ hS
  refine ⟨starLab lab w, isTwInv_starLab H hlab hw,
    fun X _ _ _ _ hX β hβ hp k hk => starLab_evalZ_smul lab w β hk (hSL.1 X hX β hβ hp k hk),
    fun X _ _ _ _ hX n γ' hγ' => ?_⟩
  rcases hS.2.2 X hX n γ' hγ' with ⟨m, γ, hγ, hfree, hin⟩ | ⟨m, γ, β₀, m', s, h, hγ, hb₀, hp₀, hw₀, hin₀, hf, hpos, hin⟩
  · obtain ⟨m₁, δ, hδ, hli, hinj, hγδ⟩ := hSL.2 X hX m γ hγ
    obtain ⟨g, hg1, hg2, hg3⟩ := exists_cut_of_cell_le (𝓞 E) H.bar φ X m₁ m δ γ hδ hγ hγδ
    obtain ⟨m₂, s, hfs⟩ := exists_isFaceCut δ g hg1
    have hδs : IsCell H.bar φ (fun j => δ (s j)) := GlobalTheory.T.polyFan_face_cut_by_intLinearForm_isCell E H q φ hφ X hX (hDom X) m₁ δ hδ m₂ s g hfs
    have hfree' : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone (fun j => δ (s j)) β → w.evalZ β = 0 :=
      fun β hb hp hc => hfree β hb hp (hg3 β hb hp (inRCone_of_sub s hc) (IsFaceCut.apply_eq_zero hfs hc))
    have hcell' := hS.1 X hX m₂ _ hδs hfree'
    have hnc : ∀ j, ¬ IsCentreRay w X (fun a b => (δ (s j) a b : ℝ)) := fun j hc => by
      obtain ⟨t, ht, β', hb', hp', hw', e⟩ := exists_of_isCentreRay w (hδs.mem j) (hδs.nonneg j) hc
      have := hfree' β' hb' hp' (InRCone.of_toReal_eq_smul (inRCone_self (fun j => δ (s j)) j) ht.le e)
      rw [hw'] at this
      norm_num at this
    refine ⟨m₂, _, hcell', hli.comp _ s.injective, fun i j hij => ?_, fun j => ?_⟩
    · simp only [starLab_evalZ_of_not lab w (hnc i), starLab_evalZ_of_not lab w (hnc j)] at hij
      exact s.injective (hinj (Real.exp_injective (by linarith)))
    · exact inRCone_trans (fun k => inRCone_face hfs (hγδ k) (hg2 k)) (hin j)
  · obtain ⟨m₁, δ, hδ, hli, hinj, hγδ⟩ := hSL.2 X hX m γ hγ
    have hγs : IsCell H.bar φ (fun j => γ (s j)) := GlobalTheory.T.polyFan_face_cut_by_intLinearForm_isCell E H q φ hφ X hX (hDom X) m γ hγ m' s h hf
    obtain ⟨g, hg1, hg2, hg3⟩ :=
      exists_cut_of_cell_le (𝓞 E) H.bar φ X m₁ m' δ (fun j => γ (s j)) hδ hγs (fun k => hγδ (s k))
    obtain ⟨m₂, s', hfs⟩ := exists_isFaceCut δ g hg1
    have hβ₀δ : InRCone δ β₀ := inRCone_trans hγδ hin₀
    have hgpos : 0 < g β₀ := by
      rcases (hβ₀δ.apply_nonneg g hg1).lt_or_eq with h' | h'
      · exact h'
      · exact (hpos.ne' (IsFaceCut.apply_eq_zero hf (hg3 β₀ hb₀ hp₀ hβ₀δ h'.symm))).elim
    have hcell' := hS.2.1 X hX m₁ δ hδ β₀ hb₀ hp₀ hw₀ hβ₀δ m₂ s' g hfs hgpos
    have hnc : ∀ j, ¬ IsCentreRay w X (fun a b => (δ (s' j) a b : ℝ)) := fun j hc => by
      obtain ⟨t, ht, β', hb', hp', hw', e⟩ := exists_of_isCentreRay w (hδ.mem (s' j)) (hδ.nonneg (s' j)) hc
      have hβ'δ : InRCone δ β' := InRCone.of_toReal_eq_smul (inRCone_self δ (s' j)) ht.le e
      have heq : β' = β₀ := (hC X hX).2.2 m₁ δ hδ β' hb' hp' β₀ hb₀ hp₀ hw' hw₀ hβ'δ hβ₀δ
      have h0 : g β' = 0 := IsFaceCut.apply_eq_zero hfs (InRCone.of_toReal_eq_smul (inRCone_self (fun j => δ (s' j)) j) ht.le e)
      rw [heq] at h0
      exact hgpos.ne' h0
    have hv0 : (starLab lab w).evalZ β₀ = -1 := starLab_evalZ_of_eq_one lab w hw₀
    have hvs : ∀ j, (starLab lab w).evalZ (δ (s' j)) = Real.exp (lab.evalZ (δ (s' j))) - 1 :=
      fun j => starLab_evalZ_of_not lab w (hnc j)
    have hsp : Submodule.span ℤ (Set.range fun j => δ (s' j)) ≤ LinearMap.ker g :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact LinearMap.mem_ker.2 ((hfs.2 (s' j)).2 ⟨j, rfl⟩))
    have hself : ∀ j, InRCone (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) (δ (s' j)) :=
      fun j => by simpa using inRCone_self (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) j.succ
    refine ⟨m₂ + 1, Fin.cons β₀ fun j => δ (s' j), hcell', ?_, ?_, fun j => ?_⟩
    · refine LinearIndependent.finCons' β₀ _ (hli.comp _ s'.injective) fun c y hy hz => ?_
      have h1 : g y = 0 := LinearMap.mem_ker.1 (hsp hy)
      have h2 := congrArg g hz
      rw [map_add (f := _), map_smul, h1, add_zero, map_zero, smul_eq_mul] at h2
      exact (mul_eq_zero.1 h2).resolve_right hgpos.ne'
    · intro i j hij
      simp only at hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j =>
          simp only [Fin.cons_zero, Fin.cons_succ, hv0, hvs] at hij
          linarith [Real.exp_pos (lab.evalZ (δ (s' j)))]
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ, hv0, hvs] at hij
          linarith [Real.exp_pos (lab.evalZ (δ (s' i)))]
        | succ j =>
          simp only [Fin.cons_succ, hvs] at hij
          exact congrArg Fin.succ (s'.injective (hinj (Real.exp_injective (by linarith))))
    · refine inRCone_trans (fun k => ?_) (hin j)
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using inRCone_self (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) 0
      · simp only [Fin.cons_succ]
        exact inRCone_trans hself (inRCone_face hfs (hγδ (s k)) (hg2 k))

end GlobalTheory.PolFan.StarLab
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantLabellingStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_starSubdivision_invariant_labelling : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H lab → SimpLab H.bar q φ lab → IsTwInv H w → IsCentreSet H.bar q φ w →
    IsPolyFan H.bar q ψ' → Subordinate H.bar q ψ' φ → IsStarOf H.bar q φ w ψ' →
    ∃ lab' : InvFun (𝓞 E), IsTwInv H lab' ∧ SimpLab H.bar q ψ' lab' := by
  first | exact @GlobalTheory.PolFan.StarLab.exists_isTwInv_simpLab_star | exact GlobalTheory.PolFan.StarLab.exists_isTwInv_simpLab_star | (intros; apply GlobalTheory.PolFan.StarLab.exists_isTwInv_simpLab_star <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionRemovesMaxMultiplicityCells

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_star_drop_multCells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → ∀ M n : ℕ, 2 ≤ M →
    maxMult H.bar q φ ≤ M → MultCellsAmong H.bar q φ M (n + 1) →
    ∃ φ' lab' : InvFun (𝓞 E), IsPolyFan H.bar q φ' ∧ IsTwInv H φ' ∧ IsTwInv H lab' ∧ SimpLab H.bar q φ' lab' ∧
      Subordinate H.bar q φ' φ ∧ maxMult H.bar q φ' ≤ M ∧ MultCellsAmong H.bar q φ' M n := by
  intro E _ _ _ H q φ lab hDom hφ hφtw hlabtw hsl M n hM hmax hcells
  obtain ⟨R, hR⟩ := hcells
  obtain ⟨w, hwtw, hwc, hcov, hdrop⟩ := GlobalTheory.T.exists_invariant_orbitCentre_marking_polyFan E H q φ lab hDom hφ hφtw hlabtw hsl M hM hmax (R 0)
  obtain ⟨ψ', hψ', hψ'tw, hsub, hstar⟩ := GlobalTheory.T.exists_starSubdivision_invariant_polyhedral_fan E H q φ w hDom hφ hφtw hwtw hwc
  obtain ⟨lab', hlab'tw, hsl'⟩ := GlobalTheory.T.exists_starSubdivision_invariant_labelling E H q φ lab w ψ' hDom hφ hlabtw hsl hwtw hwc hψ' hsub hstar
  obtain ⟨hmax', hc'⟩ := GlobalTheory.T.starSubdivision_no_new_cell_of_maximal_multiplicity_fan E H q φ lab w ψ' hDom hφ hsl hwc hdrop hψ' hsub hstar M hmax
  refine ⟨ψ', lab', hψ', hψ'tw, hlab'tw, hsl', hsub, hmax', fun k => R k.succ, ?_⟩
  intro X _ _ _ _ hX m δ hδ
  obtain ⟨hδφ, hnoc⟩ := hc' X hX m δ hδ
  obtain ⟨k, hk⟩ := hR X hX m δ hδφ
  induction k using Fin.cases with
  | zero =>
    obtain ⟨β, hβ, hp, hw1, hin⟩ := hcov X hX m δ hδφ hk
    exact absurd hw1 (hnoc β hβ hp hin)
  | succ k => exact ⟨k, hk⟩

end GlobalTheory.PolFan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionRemovesMaxMultiplicityCellsStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_starSubdivision_removes_maxMultiplicity_cells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → ∀ M n : ℕ, 2 ≤ M →
    maxMult H.bar q φ ≤ M → MultCellsAmong H.bar q φ M (n + 1) →
    ∃ φ' lab' : InvFun (𝓞 E), IsPolyFan H.bar q φ' ∧ IsTwInv H φ' ∧ IsTwInv H lab' ∧ SimpLab H.bar q φ' lab' ∧
      Subordinate H.bar q φ' φ ∧ maxMult H.bar q φ' ≤ M ∧ MultCellsAmong H.bar q φ' M n := by
  first | exact @GlobalTheory.PolFan.exists_star_drop_multCells | exact GlobalTheory.PolFan.exists_star_drop_multCells | (intros; apply GlobalTheory.PolFan.exists_star_drop_multCells <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionLowersMaxCellMultiplicity

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Main

variable {O : Type} [CommRing O] {bar : O → O}

theorem maxMult_lt_of_among_zero {q M : ℕ} {φ : InvFun O} (hM : 1 ≤ M) (h : maxMult bar q φ ≤ M)
    (h0 : MultCellsAmong bar q φ M 0) : maxMult bar q φ < M := by
  obtain ⟨R, hR⟩ := h0
  have key : maxMult bar q φ ≤ ((M - 1 : ℕ) : ℕ∞) := by
    unfold maxMult
    refine iSup_le fun X => iSup_le fun i1 => iSup_le fun i2 => iSup_le fun i3 => iSup_le fun i4 => iSup_le fun hX =>
      iSup_le fun m => iSup_le fun δ => iSup_le fun hc => iSup_le fun hli => iSup_le fun hp => ?_
    have hle : ((cellMult bar fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) : ℕ∞) ≤ M := by
      refine le_trans ?_ h
      unfold maxMult
      exact le_iSup_of_le X <| le_iSup_of_le i1 <| le_iSup_of_le i2 <| le_iSup_of_le i3 <| le_iSup_of_le i4 <|
        le_iSup_of_le hX <| le_iSup_of_le m <| le_iSup_of_le δ <| le_iSup_of_le hc <| le_iSup_of_le hli <|
        le_iSup_of_le hp le_rfl
    have hne : cellMult bar (fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) ≠ M := fun he =>
      (hR X hX m δ ⟨hc, hli, hp, he⟩).elim fun k _ => k.elim0
    have hle' : cellMult bar (fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) ≤ M := by exact_mod_cast hle
    exact_mod_cast (show cellMult bar (fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) ≤ M - 1 by omega)
  exact key.trans_lt (by exact_mod_cast (show M - 1 < M by omega))

end Main

theorem exists_round_lt_maxMult : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ lab : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → maxMult H.bar q φ < ⊤ →
    2 ≤ maxMult H.bar q φ → ∃ φ' lab' : InvFun (𝓞 E), IsPolyFan H.bar q φ' ∧ IsTwInv H φ' ∧ IsTwInv H lab' ∧
      SimpLab H.bar q φ' lab' ∧ Subordinate H.bar q φ' φ ∧ maxMult H.bar q φ' < maxMult H.bar q φ := by
  intro E _ _ _ H q φ lab hD hP hT hL hS hfin h2
  set M := (maxMult H.bar q φ).toNat with hMdef
  have hMe : maxMult H.bar q φ = M := (ENat.coe_toNat hfin.ne).symm
  have hM2 : 2 ≤ M := by rw [hMe] at h2; exact_mod_cast h2
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_multCellsAmong_of_isPolyFan E H q φ hP M
  have key : ∀ (n : ℕ) (φ lab : InvFun (𝓞 E)), IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab →
      SimpLab H.bar q φ lab → maxMult H.bar q φ ≤ M → MultCellsAmong H.bar q φ M n →
      ∃ φ' lab' : InvFun (𝓞 E), IsPolyFan H.bar q φ' ∧ IsTwInv H φ' ∧ IsTwInv H lab' ∧ SimpLab H.bar q φ' lab' ∧
        Subordinate H.bar q φ' φ ∧ maxMult H.bar q φ' < M := by
    intro n
    induction n with
    | zero =>
      intro φ lab hP hT hL hS hle h0
      exact ⟨φ, lab, hP, hT, hL, hS, Subordinate.refl φ, maxMult_lt_of_among_zero (by omega) hle h0⟩
    | succ n ih =>
      intro φ lab hP hT hL hS hle h0
      obtain ⟨φ₁, lab₁, hP₁, hT₁, hL₁, hS₁, hs₁, hle₁, h₁⟩ := GlobalTheory.T.exists_starSubdivision_removes_maxMultiplicity_cells E H q φ lab hD hP hT hL hS M n hM2 hle h0
      obtain ⟨φ', lab', hP', hT', hL', hS', hs', hlt⟩ := ih φ₁ lab₁ hP₁ hT₁ hL₁ hS₁ hle₁ h₁
      exact ⟨φ', lab', hP', hT', hL', hS', hs'.trans hs₁, hlt⟩
  obtain ⟨φ', lab', hP', hT', hL', hS', hs', hlt⟩ := key n φ lab hP hT hL hS hMe.le hn
  exact ⟨φ', lab', hP', hT', hL', hS', hs', hMe ▸ hlt⟩

end GlobalTheory.PolFan
end
end
end
