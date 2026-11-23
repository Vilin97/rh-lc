module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesExistsMarkedFormInConeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMarkedFormPiecesRaysOfSimplicialCellsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosRatMultipleOfPosRealMultipleIntFormStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveIntBilinFormEqOfPositiveRealRayStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumMulEqOfSumToRealEq
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveBalancedFormFracCoordsOfCellMultStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveBalancedFormPrimitiveAmongIntFormsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedOrbitFormPrimitiveStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfMarkedFormsInSameCellSimplicialFan

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem eq_of_orbMark_of_inRCone_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)), IsTwInv H φ → IsTwInv H lab →
  SimpLab H.bar q φ lab →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell H.bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, h₀.mem i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ γ →
      ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms H.bar X, (∀ y, 0 ≤ β' y y) →
        (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β = 1 → (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β' = 1 →
        InRCone γ β → InRCone γ β' → β = β' := by
  intro E _ _ _ H q φ lab hφ hlab hS X₀ _ _ _ m₀ δ₀ h₀ hli₀ hprim₀ v t hv ht hvt X _ _ _ _ hX m γ hγ β hβ hβn β' hβ' hβ'n
    hm hm' hin hin'
  obtain ⟨m', δ, hδ, hδli, hδinj, hγδ⟩ := hS.2 X hX m γ hγ
  have hcδ : ∀ j, InRCone δ (γ j) := hγδ
  obtain ⟨c, hc, hβc⟩ := inRCone_trans hcδ hin
  obtain ⟨c', hc', hβc'⟩ := inRCone_trans hcδ hin'
  obtain ⟨p, hp, hpi, hpc⟩ := GlobalTheory.T.exists_markedForm_pieces_rays_of_simplicialCells E H φ hφ δ₀ h₀ hli₀ hprim₀ v t hv ht hvt β hm
  obtain ⟨p', hp', hpi', hpc'⟩ := GlobalTheory.T.exists_markedForm_pieces_rays_of_simplicialCells E H φ hφ δ₀ h₀ hli₀ hprim₀ v t hv ht hvt β' hm'
  have hlabray : ∀ (x : LinearMap.BilinForm ℤ X) (j : Fin m') (d : ℝ), 0 < d → x ∈ balForms H.bar X →
      (∀ y, 0 ≤ x y y) → toReal x = d • toReal (δ j) → lab.evalZ x = lab.evalZ (δ j) := by
    intro x j d hd hxb hxn hx
    obtain ⟨a, b, ha, hb, hab⟩ := GlobalTheory.T.exists_pos_rat_multiple_of_pos_real_multiple_intForm x (δ j) d hd (hδli.ne_zero j) hx
    have h1 := hS.1 X hX x hxb hxn a ha
    have h2 := hS.1 X hX (δ j) (hδ.mem j) (hδ.nonneg j) b hb
    rw [← h1, ← h2, hab]
  have hpeq : ∀ i, 0 < t i → p i = p' i := by
    intro i hti
    obtain ⟨hpb, hpn, hpp, hpl⟩ := hpi i hti
    obtain ⟨hpb', hpn', hpp', hpl'⟩ := hpi' i hti
    obtain ⟨j, -, d, hd, hpd⟩ := (hpc m' δ hδ hδli c hc hβc).1 i hti
    obtain ⟨j', -, d', hd', hpd'⟩ := (hpc' m' δ hδ hδli c' hc' hβc').1 i hti
    have hjj : j = j' := hδinj (by
      show lab.evalZ (δ j) = lab.evalZ (δ j')
      rw [← hlabray _ j d hd hpb hpn hpd, ← hlabray _ j' d' hd' hpb' hpn' hpd', hpl lab hlab, hpl' lab hlab])
    subst hjj
    have : toReal (p i) = (d / d') • toReal (p' i) := by
      rw [hpd, hpd', smul_smul, div_mul_cancel₀ _ hd'.ne']
    exact (GlobalTheory.T.primitive_intBilinForm_eq_of_positive_real_ray (p i) (p' i) (d / d') (div_pos hd hd') hpp hpp' this).1
  apply toReal_injective
  rw [hp, hp']
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases (ht i).lt_or_eq with h | h
  · rw [hpeq i h]
  · rw [← h, zero_smul, zero_smul]

end GlobalTheory.PolFan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfMarkedFormsInSameCellSimplicialFanStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.eq_of_markedForms_in_same_cell_simplicialFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)), IsTwInv H φ → IsTwInv H lab →
  SimpLab H.bar q φ lab →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell H.bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, h₀.mem i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ γ →
      ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms H.bar X, (∀ y, 0 ≤ β' y y) →
        (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β = 1 → (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β' = 1 →
        InRCone γ β → InRCone γ β' → β = β' := by
  first | exact @GlobalTheory.PolFan.eq_of_orbMark_of_inRCone_cell | exact GlobalTheory.PolFan.eq_of_orbMark_of_inRCone_cell | (intros; apply GlobalTheory.PolFan.eq_of_orbMark_of_inRCone_cell <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormCoordinateLtOneInPrimitiveCell

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem orbMark_coord_lt_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell H.bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, h₀.mem i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i ∧ t i < 1) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
    LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β = 1 →
    ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1 := by
  intro E _ _ _ H φ hφ X₀ _ _ _ m₀ δ₀ h₀ hli₀ hprim₀ v t hv ht hvsum X _ _ _ m δ h hli hprim
    β _ _ hβ1 c hc hβsum j
  obtain ⟨p, -, hpos, hcells⟩ :=
    GlobalTheory.T.exists_markedForm_pieces_rays_of_simplicialCells E H φ hφ δ₀ h₀ hli₀ hprim₀ v t hv (fun i => (ht i).1) hvsum β hβ1
  rcases (hc j).lt_or_eq with hcj | hcj
  · obtain ⟨i, hti, d, hd, hpd, hcd⟩ := (hcells m δ h hli c hc hβsum).2 j hcj
    have hpi := (hpos i hti).2.2.1
    have hδj := GlobalTheory.T.isPrimitiveBalancedForm_primitive_among_intForms H.bar (δ j) (h.mem j) (hprim j)
    have hd1 := (GlobalTheory.T.primitive_intBilinForm_eq_of_positive_real_ray (p i) (δ j) d hd hpi hδj hpd).2
    rw [hcd, hd1, mul_one]
    exact (ht i).2
  · rw [← hcj]; exact zero_lt_one

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormCoordinateLtOneInPrimitiveCellStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.markedForm_coordinate_lt_one_in_primitiveCell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell H.bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, h₀.mem i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i ∧ t i < 1) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
    LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β = 1 →
    ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1 := by
  first | exact @GlobalTheory.orbMark_coord_lt_one | exact GlobalTheory.orbMark_coord_lt_one | (intros; apply GlobalTheory.orbMark_coord_lt_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantOrbitCentreMarkingPolyFan

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.OrbMark

theorem centres_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → ∀ M : ℕ, 2 ≤ M →
    maxMult H.bar q φ ≤ M → ∀ c : FormFamily (𝓞 E),
    ∃ w : InvFun (𝓞 E), IsTwInv H w ∧ IsCentreSet H.bar q φ w ∧
      (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell H.bar φ M δ → c.Carries δ →
          ∃ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) ∧ w.evalZ β = 1 ∧ InRCone δ β) ∧
      (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
          ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) := by
  intro E _ _ _ H q φ lab _hdom _hfan hφ hlab hsl M hM _hmax c
  classical
  by_cases hex : ∃ (X : Type) (_ : AddCommGroup X) (_ : Module (𝓞 E) X) (_ : Module.Finite (𝓞 E) X)
      (_ : Module.Projective (𝓞 E) X), Module.finrank (𝓞 E) X ≤ q ∧
      ∃ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell H.bar φ M δ ∧ c.Carries δ
  · obtain ⟨X₀, _, _, _, _, -, m₀, δ₀, hM₀, hc₀⟩ := hex
    obtain ⟨v, hv, hvp, hvn, t, ht, htv⟩ := GlobalTheory.T.exists_primitiveBalancedForm_fracCoords_of_cellMult H.bar φ M δ₀ hM₀ hM
    obtain ⟨h₀, hli, hpr, -⟩ := hM₀
    have hv0 : v ≠ 0 := fun h => by
      have e : (⟨v, hv⟩ : balForms H.bar X₀) = 0 := Subtype.ext h
      rw [e] at hvp
      exact not_isPrim_zero hvp
    refine ⟨OrbMark.orbFun (𝓞 E) H.w0 v, OrbMark.isTwInv_orbFun H v,
      fun X _ _ _ _ hX => ⟨fun β _ _ => OrbMark.orbFun_eval_eq_zero_or_one _ _ _,
        fun β _ _ h1 => GlobalTheory.T.markedOrbit_form_primitive H.bar H.w0 v hv hvp β h1,
        fun m γ hγ β hβ hβp β' hβ' hβp' h1 h1' hc hc' =>
          GlobalTheory.T.eq_of_markedForms_in_same_cell_simplicialFan E H q φ lab hφ hlab hsl δ₀ h₀ hli hpr v t hv0 (fun i => (ht i).1) htv X hX m γ hγ β hβ hβp β' hβ' hβp'
            h1 h1' hc hc'⟩,
      fun X _ _ _ _ _ m δ _ hδ => ?_,
      fun X _ _ _ _ _ m δ h hδ hδp β hβ hβp h1 c' hc' hβc =>
        GlobalTheory.T.markedForm_coordinate_lt_one_in_primitiveCell E H φ hφ δ₀ h₀ hli hpr v t hv0 ht htv X m δ h hδ hδp β hβ hβp h1 c' hc' hβc⟩
    obtain ⟨β, hβ, hβp, h1, hin⟩ := GlobalTheory.T.carries_exists_marked_form_in_cone H.bar H.w0 c δ₀ v t hv hv0 hvn hc₀ (fun i => (ht i).1) htv X m δ hδ
    exact ⟨β, hβ, hβp, h1, hin⟩
  · refine ⟨zeroFun (𝓞 E), fun _ _ _ _ => rfl, fun X _ _ _ _ _ =>
      ⟨fun β _ _ => Or.inl (zeroFun_evalZ β), fun β _ _ h => by simp at h,
        fun _ _ _ β _ _ _ _ _ h => by simp at h⟩,
      fun X _ _ _ _ hX m δ hδ hc => (hex ⟨X, inferInstance, inferInstance, inferInstance, inferInstance, hX, m, δ, hδ, hc⟩).elim,
      fun X _ _ _ _ _ m δ _ _ _ β _ _ h => by simp at h⟩

end GlobalTheory.PolFan.OrbMark
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantOrbitCentreMarkingPolyFanStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_invariant_orbitCentre_marking_polyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → ∀ M : ℕ, 2 ≤ M →
    maxMult H.bar q φ ≤ M → ∀ c : FormFamily (𝓞 E),
    ∃ w : InvFun (𝓞 E), IsTwInv H w ∧ IsCentreSet H.bar q φ w ∧
      (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell H.bar φ M δ → c.Carries δ →
          ∃ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) ∧ w.evalZ β = 1 ∧ InRCone δ β) ∧
      (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
          ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) := by
  first | exact @GlobalTheory.PolFan.OrbMark.centres_exists | exact GlobalTheory.PolFan.OrbMark.centres_exists | (intros; apply GlobalTheory.PolFan.OrbMark.centres_exists <;> assumption)
end
end
