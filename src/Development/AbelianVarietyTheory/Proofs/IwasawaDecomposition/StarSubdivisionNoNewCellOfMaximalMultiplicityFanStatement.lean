module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionNewCellMultiplicityLt
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedFormCellMultiplicityPosStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqSubfamilyOfFaceSimplicialConePrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinFormCutFaceOfCellInConeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinFormCutFaceOfFaceOfConeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescalePrimitiveLinearIndependentCellStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardTorsionQuotSpanDvdOfRangeSubsetStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyFanFaceCutByIntLinearFormIsCellStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionNewCellMultiplicityLtStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.starSubdivision_newCell_multiplicity_lt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    SimpLab H.bar q φ lab → IsCentreSet H.bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
          ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    ∀ M : ℕ, maxMult H.bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell H.bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim H.bar (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (β₀ : LinearMap.BilinForm ℤ X) (m' : ℕ) (s : Fin m' ↪ Fin m)
          (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar φ γ → β₀ ∈ balForms H.bar X → (∀ y, 0 ≤ β₀ y y) →
          w.evalZ β₀ = 1 → InRCone γ β₀ → IsFaceCut γ s h → 0 < h β₀ →
          IsCell H.bar ψ' (Fin.cons β₀ fun j => γ (s j)) → (∀ j, InRCone (Fin.cons β₀ fun j => γ (s j)) (γ' j)) →
          cellMult H.bar (fun i => (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) < M := by
  first | exact @GlobalTheory.PolFan.cellMult_lt_of_star_new | exact GlobalTheory.PolFan.cellMult_lt_of_star_new | (intros; apply GlobalTheory.PolFan.cellMult_lt_of_star_new <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionOldCellMultiplicityLe

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem starOld_cell_mult_le (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ lab w ψ' : InvFun (𝓞 E))
    (hDom : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Dominates H.bar X)
    (hφ : IsPolyFan H.bar q φ) (hlab : SimpLab H.bar q φ lab) (M : ℕ) (hM : maxMult H.bar q φ ≤ M)
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X]
    (hX : Module.finrank (𝓞 E) X ≤ q) (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell H.bar ψ' γ')
    (hli' : LinearIndependent ℤ γ') (hp' : ∀ i, IsPrim H.bar (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X))
    (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (hγφ : IsCell H.bar φ γ) (hγψ : IsCell H.bar ψ' γ)
    (hw : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0)
    (hin : ∀ j, InRCone γ (γ' j)) :
    ∃ hφ' : IsCell H.bar φ γ', cellMult H.bar (fun i => (⟨γ' i, hφ'.mem i⟩ : balForms H.bar X)) ≤ M ∧
      ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ' β → w.evalZ β ≠ 1 := by

  obtain ⟨m', δ, hδ, hδli, -, hδγ⟩ := hlab.2 X hX m γ hγφ
  obtain ⟨δ₁, hδ₁, hδ₁li, hδ₁p, hδδ₁⟩ := GlobalTheory.T.exists_rescale_primitive_linearIndependent_cell H.bar φ δ hδ hδli
  have hγδ₁ : ∀ k, InRCone δ₁ (γ k) := fun k => hδδ₁ _ (hδγ k)

  obtain ⟨h₂, h₂n, h₂z, h₂c⟩ := GlobalTheory.T.exists_linForm_cut_face_of_cell_in_cone H.bar φ δ₁ γ hδ₁ hγφ hγδ₁
  obtain ⟨h₁, h₁n, h₁z, h₁c⟩ := GlobalTheory.T.exists_linForm_cut_face_of_cell_in_cone H.bar ψ' γ γ' hγψ hγ' hin
  obtain ⟨h, hn, hz, hc⟩ := GlobalTheory.T.exists_linForm_cut_face_of_face_of_cone H.bar δ₁ γ γ' h₂ h₁ hδ₁.mem hδ₁.nonneg hin h₂n h₂z h₂c h₁n h₁z h₁c
  have hin₁ : ∀ j, InRCone δ₁ (γ' j) := fun j => inRCone_trans hγδ₁ (hin j)
  obtain ⟨s, hs, hsf⟩ := GlobalTheory.T.eq_subfamily_of_face_simplicialCone_primitive H.bar δ₁ γ' hδ₁.mem hγ'.mem h hδ₁li hli' hδ₁p hp' hin₁ hn hz
    (fun i hi => hc _ (hδ₁.mem i) (hδ₁.nonneg i) (inRCone_self δ₁ i) hi)
  have hγ'eq : γ' = fun j => δ₁ (s j) := funext hs
  have hcut : IsFaceCut δ₁ s h := ⟨hn, hsf⟩
  have hφ' : IsCell H.bar φ γ' := by
    rw [hγ'eq]; exact GlobalTheory.T.polyFan_face_cut_by_intLinearForm_isCell E H q φ hφ X hX (hDom X) m' δ₁ hδ₁ _ s h hcut
  refine ⟨hφ', ?_, fun β hβ hβn hβc h1 => ?_⟩
  ·
    have hliB : LinearIndependent ℤ (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms H.bar X)) :=
      LinearIndependent.of_comp (balForms H.bar X).subtype hδ₁li
    have hrange : Set.range (fun j => (⟨γ' j, hφ'.mem j⟩ : balForms H.bar X)) ⊆
        Set.range (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms H.bar X)) := by
      rintro _ ⟨j, rfl⟩
      exact ⟨s j, Subtype.ext (hs j).symm⟩
    have hdvd := GlobalTheory.T.natCard_torsion_quot_span_dvd_of_range_subset' (balForms H.bar X) _ _ hliB hrange
    have hpos := GlobalTheory.T.balancedFormCellMultiplicity_pos H.bar (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms H.bar X))
    have hle := SmoothEnd.cellMult_le_maxMult hX hδ₁ hδ₁li hδ₁p
    have hle' : cellMult H.bar (fun i => (⟨δ₁ i, hδ₁.mem i⟩ : balForms H.bar X)) ≤ M := by
      exact_mod_cast hle.trans hM
    exact (Nat.le_of_dvd hpos hdvd).trans hle'
  ·
    rw [hw β hβ hβn (inRCone_trans hin hβc)] at h1
    exact zero_ne_one h1

end GlobalTheory.PolFan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionOldCellMultiplicityLeStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.starSubdivision_oldCell_multiplicity_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → SimpLab H.bar q φ lab → ∀ M : ℕ, maxMult H.bar q φ ≤ M →
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X) (hγ' : IsCell H.bar ψ' γ'),
        LinearIndependent ℤ γ' → (∀ i, IsPrim H.bar (⟨γ' i, hγ'.mem i⟩ : balForms H.bar X)) →
        ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ γ → IsCell H.bar ψ' γ →
          (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (∀ j, InRCone γ (γ' j)) →
          ∃ hφ : IsCell H.bar φ γ', cellMult H.bar (fun i => (⟨γ' i, hφ.mem i⟩ : balForms H.bar X)) ≤ M ∧
            ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ' β → w.evalZ β ≠ 1 := by
  first | exact @GlobalTheory.PolFan.starOld_cell_mult_le | exact GlobalTheory.PolFan.starOld_cell_mult_le | (intros; apply GlobalTheory.PolFan.starOld_cell_mult_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionNoNewCellOfMaximalMultiplicityFan

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem GlobalTheory.PolFan.starMult : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → SimpLab H.bar q φ lab → IsCentreSet H.bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
          ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    IsPolyFan H.bar q ψ' → Subordinate H.bar q ψ' φ → IsStarOf H.bar q φ w ψ' → ∀ M : ℕ, maxMult H.bar q φ ≤ M →
    maxMult H.bar q ψ' ≤ M ∧
      ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell H.bar ψ' M δ →
          IsMultCell H.bar φ M δ ∧ ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → w.evalZ β ≠ 1 := by
  intro E _ _ _ H q φ lab w ψ' hD hφ hSL hW hC hψ' hSub hStar M hM
  have cI := GlobalTheory.T.starSubdivision_oldCell_multiplicity_le E H q φ lab w ψ' hD hφ hSL M hM
  have cII := GlobalTheory.T.starSubdivision_newCell_multiplicity_lt E H q φ lab w ψ' hSL hW hC M hM
  refine ⟨?_, ?_⟩
  · refine iSup_le fun X => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun hX =>
      iSup_le fun n => iSup_le fun γ' => iSup_le fun hγ' => iSup_le fun hli => iSup_le fun hpr => ?_
    rcases hStar.2.2 X hX n γ' hγ' with ⟨m, γ, hγ, hw, hin⟩ | ⟨m, γ, β₀, m', s, h, hγ, hb, hp, hw1, hin0, hcut, hpos, hin⟩
    · obtain ⟨hφγ, hle, -⟩ := cI X hX n γ' hγ' hli hpr m γ hγ (hStar.1 X hX m γ hγ hw) hw hin
      exact_mod_cast hle
    · have := cII X hX n γ' hγ' hli hpr m γ β₀ m' s h hγ hb hp hw1 hin0 hcut hpos
        (hStar.2.1 X hX m γ hγ β₀ hb hp hw1 hin0 m' s h hcut hpos) hin
      exact_mod_cast this.le
  · intro X _ _ _ _ hX n γ' ⟨hγ', hli, hpr, heq⟩
    rcases hStar.2.2 X hX n γ' hγ' with ⟨m, γ, hγ, hw, hin⟩ | ⟨m, γ, β₀, m', s, h, hγ, hb, hp, hw1, hin0, hcut, hpos, hin⟩
    · obtain ⟨hφγ, -, hno⟩ := cI X hX n γ' hγ' hli hpr m γ hγ (hStar.1 X hX m γ hγ hw) hw hin
      exact ⟨⟨hφγ, hli, hpr, heq⟩, hno⟩
    · have := cII X hX n γ' hγ' hli hpr m γ β₀ m' s h hγ hb hp hw1 hin0 hcut hpos
        (hStar.2.1 X hX m γ hγ β₀ hb hp hw1 hin0 m' s h hcut hpos) hin
      omega
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionNoNewCellOfMaximalMultiplicityFanStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.starSubdivision_no_new_cell_of_maximal_multiplicity_fan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → SimpLab H.bar q φ lab → IsCentreSet H.bar q φ w →
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
          ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) →
    IsPolyFan H.bar q ψ' → Subordinate H.bar q ψ' φ → IsStarOf H.bar q φ w ψ' → ∀ M : ℕ, maxMult H.bar q φ ≤ M →
    maxMult H.bar q ψ' ≤ M ∧
      ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell H.bar ψ' M δ →
          IsMultCell H.bar φ M δ ∧ ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → w.evalZ β ≠ 1 := by
  first | exact @GlobalTheory.PolFan.starMult | exact GlobalTheory.PolFan.starMult | (intros; apply GlobalTheory.PolFan.starMult <;> assumption)
end
end
