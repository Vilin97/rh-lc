module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesFlagsIffAdaptedFrameAtImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFrameTriangularThroughStalkFrames

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions
  Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.GoodMetric GlobalTheory.LieBase

namespace GlobalTheory.ShFam.CarriesAt

theorem diag_mul_of_blockTriangular {R : Type} [CommRing R] {n : ℕ} {A B : Matrix (Fin n) (Fin n) R}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA h, zero_mul]
  · rw [hB h, mul_zero]

theorem isUnit_diag_of_blockTriangular {R : Type} [CommRing R] {n : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : A.BlockTriangular id) (hd : IsUnit A.det) (i : Fin n) : IsUnit (A i i) := by
  rw [Matrix.det_of_upperTriangular hA] at hd
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => A j j) (Finset.mem_univ i)) hd

theorem tri_of_carries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (k : Type) [Field k] (φ : c.F →+* k) (x : Sp k ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp k ⟶ C.Y.X), C.Carries p g → ∀ (y : C.Y.X) (ψ : C.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* C.Y.X.presheaf.stalk y) (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), p = spMap ψ ≫ stalkPt C.Y y → f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t → ∃ t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri ψ g t' := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C k _ φ x g p hC y ψ φ₁ f t hp hf
  obtain ⟨y₁, ψ₁, φ₂, f₁, t₁, t₁', hp₁, hf₁, hg₁⟩ := hC

  have hsp : p (IsLocalRing.closedPoint k) ⤳ y := by
    have : p (IsLocalRing.closedPoint k) ∈ Set.range (C.Y.X.fromSpecStalk y) := by
      rw [hp]
      exact ⟨spMap ψ (IsLocalRing.closedPoint k), rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hsp₁ : p (IsLocalRing.closedPoint k) ⤳ y₁ := by
    have : p (IsLocalRing.closedPoint k) ∈ Set.range (C.Y.X.fromSpecStalk y₁) := by
      rw [hp₁]
      exact ⟨spMap ψ₁ (IsLocalRing.closedPoint k), rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hψ : ψ = (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
    refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 ?_)
    have e1 := spMap_stalkClosedPointTo p
    have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ C.Y.X.fromSpecStalk y = C.Y.X.fromSpecStalk _ :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
    have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom) =
        spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom ≫ spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
      simp [spMap, Spec.map_comp]
    rw [e3, Category.assoc, e2, e1]
    exact hp.symm
  have hψ₁ : ψ₁ = (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp₁).hom := by
    refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y₁)).1 ?_)
    have e1 := spMap_stalkClosedPointTo p
    have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp₁).hom ≫ C.Y.X.fromSpecStalk y₁ = C.Y.X.fromSpecStalk _ :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp₁
    have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp₁).hom) =
        spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom ≫ spMap (C.Y.X.presheaf.stalkSpecializes hsp₁).hom := by
      simp [spMap, Spec.map_comp]
    rw [e3, Category.assoc, e2, e1]
    exact hp₁.symm
  set ψp := (Scheme.stalkClosedPointTo (R := CommRingCat.of k) p).hom with hψpdef
  set ρ := (C.Y.X.presheaf.stalkSpecializes hsp).hom with hρdef
  set ρ₁ := (C.Y.X.presheaf.stalkSpecializes hsp₁).hom with hρ₁def
  set alg := algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint k))) C.Y.X.functionField with halgdef
  have hinj : Function.Injective alg := IsFractionRing.injective _ _
  have halg : algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField = alg.comp ρ := algebraMap_eq_comp_specializes hsp
  have halg₁ : algebraMap (C.Y.X.presheaf.stalk y₁) C.Y.X.functionField = alg.comp ρ₁ :=
    algebraMap_eq_comp_specializes hsp₁
  have hxp : spMap ρ ≫ stalkPt C.Y y = stalkPt C.Y (p (IsLocalRing.closedPoint k)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hxp₁ : spMap ρ₁ ≫ stalkPt C.Y y₁ = stalkPt C.Y (p (IsLocalRing.closedPoint k)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp₁
  have hpp : spMap ψp ≫ stalkPt C.Y (p (IsLocalRing.closedPoint k)) = p := spMap_stalkClosedPointTo p

  have c1 : alg.comp (ρ.comp φ₁) = constF e C.Y := by rw [← RingHom.comp_assoc, ← halg, hf.2.1]
  have c2 : alg.comp (ρ₁.comp φ₂) = constF e C.Y := by rw [← RingHom.comp_assoc, ← halg₁, hf₁.2.1]
  have hρφ : ρ₁.comp φ₂ = ρ.comp φ₁ := RingHom.ext fun a => hinj
    ((RingHom.congr_fun c2 a).trans (RingHom.congr_fun c1 a).symm)
  have hgen : genericPt C.Y ≫ C.π ≫ genι Z = spMap alg ≫ stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z := by
    rw [hf.1, halg, ← hxp]
    simp [spMap, Spec.map_comp]
  have hx0 : x = p ≫ C.π ≫ genι Z := by rw [hg₁.1, hp₁, Category.assoc]
  have hxk : x = spMap ψp ≫ stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z := by
    rw [hx0, ← Category.assoc (spMap ψp), hpp]
  have hxψ : x = spMap ψ ≫ stalkPt C.Y y ≫ C.π ≫ genι Z := by
    rw [hx0, hp, Category.assoc]
  have hφk : φ = ψ.comp φ₁ := by
    rw [hg₁.2.1, hψ₁, hψ, RingHom.comp_assoc, RingHom.comp_assoc, hρφ]

  obtain ⟨f', hf'⟩ := f.exists_isMap ρ (x' := stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z) rfl
    (by rw [← hxp, Category.assoc])
  obtain ⟨f₁', hf₁'⟩ := f₁.exists_isMap ρ₁ (x' := stalkPt C.Y (p (IsLocalRing.closedPoint k)) ≫ C.π ≫ genι Z) hρφ.symm
    (by rw [← hxp₁, Category.assoc])
  obtain ⟨fF, hfF⟩ := f'.exists_isMap alg c1.symm hgen
  obtain ⟨f₁F, hf₁F⟩ := f₁'.exists_isMap alg c1.symm hgen
  obtain ⟨fk, hfk⟩ := f.exists_isMap ψ hφk hxψ
  obtain ⟨f₁k, hf₁k⟩ := f₁.exists_isMap ψ₁ hg₁.2.1 hg₁.1
  have iF : (_root_.GlobalTheory.ShFam.EigFrame.IsMap f) (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) fF := fun τ i => by
    rw [hfF τ i, hf' τ i, ← Category.assoc (spMap (Formalism.L2.Pj.dualMap alg)), ← spMap_dualMap_comp, ← halg]
  have i₁F : f₁.IsMap (algebraMap (C.Y.X.presheaf.stalk y₁) C.Y.X.functionField) f₁F := fun τ i => by
    rw [hf₁F τ i, hf₁' τ i, ← Category.assoc (spMap (Formalism.L2.Pj.dualMap alg)), ← spMap_dualMap_comp, ← halg₁]
  have ik : f'.IsMap ψp fk := fun τ i => by
    rw [hfk τ i, hf' τ i, ← Category.assoc (spMap (Formalism.L2.Pj.dualMap ψp)), ← spMap_dualMap_comp, ← hψ]
  have i₁k : f₁'.IsMap ψp f₁k := fun τ i => by
    rw [hf₁k τ i, hf₁' τ i, ← Category.assoc (spMap (Formalism.L2.Pj.dualMap ψp)), ← spMap_dualMap_comp, ← hψ₁]

  have key : ∀ τ, (fk.co g τ).BlockTriangular id ∧ ∀ i, IsUnit (fk.co g τ i i) := by
    intro τ
    have hU := EigFrame.Tri.co (τ := τ) hf iF
    have hU₁ := EigFrame.Tri.co (τ := τ) hf₁ i₁F
    have hU₁t : (f₁F.co C.f0 τ).BlockTriangular id := fun a i h => hU₁.1 a i h
    have hU₁d : IsUnit (f₁F.co C.f0 τ).det := f₁F.isUnit_det_co C.f0 τ
    have hW : fF.co f₁F τ = fF.co C.f0 τ * (f₁F.co C.f0 τ)⁻¹ := by
      rw [← fF.co_mul f₁F C.f0 τ, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU₁d, Matrix.mul_one]
    have hWt : (fF.co f₁F τ).BlockTriangular id := by
      haveI := Matrix.invertibleOfIsUnitDet _ hU₁d
      rw [hW]
      exact Matrix.BlockTriangular.mul (fun a i h => hU.1 a i h) (Matrix.blockTriangular_inv_of_blockTriangular hU₁t)
    have hM : fF.co f₁F τ = (f'.co f₁' τ).map alg := EigFrame.IsMap.co τ hfF hf₁F hgen
    have hMt : (f'.co f₁' τ).BlockTriangular id := fun a i h => hinj (by
      have := hWt h
      rw [hM, Matrix.map_apply] at this
      rw [this, map_zero])
    have hMu : ∀ i, IsUnit (f'.co f₁' τ i i) := isUnit_diag_of_blockTriangular hMt (f'.isUnit_det_co f₁' τ)
    have hN := EigFrame.Tri.co (τ := τ) hg₁ hf₁k
    have hNt : (f₁k.co g τ).BlockTriangular id := fun a i h => hN.1 a i h
    have hMk : fk.co f₁k τ = (f'.co f₁' τ).map ψp := EigFrame.IsMap.co τ ik i₁k hxk
    have hMkt : (fk.co f₁k τ).BlockTriangular id := fun a i h => by
      rw [hMk, Matrix.map_apply, hMt h, map_zero]
    have hQ : fk.co g τ = fk.co f₁k τ * f₁k.co g τ := (fk.co_mul f₁k g τ).symm
    refine ⟨hQ ▸ hMkt.mul hNt, fun i => ?_⟩
    rw [hQ, diag_mul_of_blockTriangular hMkt hNt, hMk, Matrix.map_apply, hN.2 i]
    exact ((hMu i).map ψp).mul (Units.isUnit _)
  refine ⟨fun τ i => ((key τ).2 i).unit, hxψ, hφk, fun τ i => ⟨fun a => fk.co g τ a i, ((key τ).2 i).unit_spec.symm,
    fun a ha => (key τ).1 ha, ?_⟩⟩
  rw [← funext (hfk τ)]
  exact fk.co_spec g τ i

end GlobalTheory.ShFam.CarriesAt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFrameTriangularThroughStalkFramesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.carried_frame_triangular_through_stalkFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (k : Type) [Field k] (φ : c.F →+* k) (x : Sp k ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp k ⟶ C.Y.X), C.Carries p g → ∀ (y : C.Y.X) (ψ : C.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* C.Y.X.presheaf.stalk y) (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), p = spMap ψ ≫ stalkPt C.Y y → f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t → ∃ t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri ψ g t' := by
  first | exact @GlobalTheory.ShFam.CarriesAt.tri_of_carries | exact GlobalTheory.ShFam.CarriesAt.tri_of_carries | (intros; apply GlobalTheory.ShFam.CarriesAt.tri_of_carries <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperTriangularMul

section

@[expose] public section

namespace GlobalTheory.UpperTriangularMul

theorem upperTriangular_mul :
    ∀ {n : ℕ} {R : Type} [inst : CommRing R] {M N : Matrix (Fin n) (Fin n) R},
      (∀ (a i : Fin n), i < a → M a i = (0 : R)) →
      (∀ (a i : Fin n), i < a → N a i = (0 : R)) →
      (∀ (a i : Fin n), i < a → (M * N) a i = (0 : R)) ∧
        ∀ (i : Fin n), (M * N) i i = M i i * N i i := by
  intro n R _ M N hM hN
  refine ⟨fun a i hia => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases lt_or_ge j a with h | h
    · rw [hM a j h, zero_mul]
    · rw [hN j i (lt_of_lt_of_le hia h), mul_zero]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hM i j h, zero_mul]
    · rw [hN j i h, mul_zero]

end GlobalTheory.UpperTriangularMul
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpecOfAnypoint

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.CarrySpec

theorem upper_mul {n : ℕ} {R : Type} [CommRing R] {M N : Matrix (Fin n) (Fin n) R}
    (hM : ∀ a i, i < a → M a i = 0) (hN : ∀ a i, i < a → N a i = 0) :
    (∀ a i, i < a → (M * N) a i = 0) ∧ ∀ i, (M * N) i i = M i i * N i i := by
  first
  | exact @_root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul
  | exact _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul
  | (apply _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul ..)

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (ρ : R →+* R') (ψ : R' →+* R'') :
    spMap (ψ.comp ρ) = spMap ψ ≫ spMap ρ := by
  simp [spMap, Spec.map_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem isMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} {f : EigFrame Z φ x}
    {f' : EigFrame Z φ' x'} {f'' : EigFrame Z φ'' x''} {ρ : R →+* R'} {ψ : R' →+* R''}
    (h1 : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) ρ f') (h2 : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f' embτ basisIdx) ψ f'') : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) (ψ.comp ρ) f'' := fun τ i => by
  rw [h2 τ i, h1 τ i, GlobalTheory.ShFam.CarriesAt.spMap_dualMap_comp, Category.assoc]

theorem tri_of_co {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'} {x : Sp R ⟶ Z.X}
    {x' : Sp R' ⟶ Z.X} {f : EigFrame Z φ x} {ψ : R →+* R'} {f' g : EigFrame Z φ' x'} (hf : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) ψ f')
    (hx : x' = spMap ψ ≫ x) (hφ : φ' = ψ.comp φ) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ)
    (hu : ∀ τ a i, i < a → f'.co g τ a i = 0) (hd : ∀ τ i, f'.co g τ i i = t τ i) : f.Tri ψ g t :=
  ⟨hx, hφ, fun τ i => ⟨fun a => f'.co g τ a i, hd τ i, fun k hk => hu τ k i hk, by
    have := f'.co_spec g τ i
    rwa [funext (hf τ)] at this⟩⟩

theorem tri_spec {R V L k : Type} [CommRing R] [CommRing V] [CommRing L] [CommRing k]
    {φ₁ : c.F →+* R} {x₁ : Sp R ⟶ Z.X} (f : EigFrame Z φ₁ x₁) (ρ : R →+* V) (ν : V →+* L)
    (hν : Function.Injective ν) (r : V →+* k) {φV : c.F →+* V} {xV : Sp V ⟶ Z.X} (hxV : xV = spMap ρ ≫ x₁)
    (gV : EigFrame Z φV xV) {φL : c.F →+* L} {xL : Sp L ⟶ Z.X} (gL : EigFrame Z φL xL)
    (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (hL : gV.Tri ν gL tL)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (hfL : f.Tri (ν.comp ρ) gL t')
    {φk : c.F →+* k} {xk : Sp k ⟶ Z.X} (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ)
    (hk : gV.Tri r gk tk) : ∃ t'' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri (r.comp ρ) gk t'' := by
  have hφV : φV = ρ.comp φ₁ := RingHom.ext fun a => hν (by
    have := RingHom.congr_fun (hL.2.1.symm.trans hfL.2.1) a
    simpa using this)
  obtain ⟨h, hh⟩ := EigFrame.exists_isMap f ρ hφV hxV
  obtain ⟨gVL, hgVL⟩ := EigFrame.exists_isMap gV ν hL.2.1 hL.1
  obtain ⟨hLf, hhL⟩ := EigFrame.exists_isMap h ν hL.2.1 hL.1
  have hfhL : (_root_.GlobalTheory.ShFam.EigFrame.IsMap f) (ν.comp ρ) hLf := isMap_comp hh hhL

  have hA : ∀ τ, (∀ a i, i < a → h.co gV τ a i = 0) := fun τ a i hia => by
    obtain ⟨hU, -⟩ := EigFrame.Tri.co τ hfL hfhL
    obtain ⟨hW, -⟩ := EigFrame.Tri.co τ hL hgVL
    have hmap := EigFrame.IsMap.co τ hhL hgVL hL.1
    have hmul := EigFrame.co_mul hLf gVL gL τ
    have hWu := EigFrame.isUnit_det_co gVL gL τ
    set W := gVL.co gL τ
    have hWt : W.BlockTriangular id := fun a b h => hW a b h
    letI := Matrix.invertibleOfIsUnitDet W hWu
    have hWi : W⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hWt
    have hM : hLf.co gVL τ = hLf.co gL τ * W⁻¹ := by
      rw [← hmul, Matrix.mul_nonsing_inv_cancel_right _ _ hWu]
    have hP : (hLf.co gL τ * W⁻¹).BlockTriangular id :=
      Matrix.BlockTriangular.mul (fun a b h => hU a b h) hWi
    apply hν
    have := hP hia
    rw [← hM, hmap, Matrix.map_apply] at this
    rw [this, map_zero]
  have hAd : ∀ τ i, IsUnit (h.co gV τ i i) := fun τ i => by
    have hdet := EigFrame.isUnit_det_co h gV τ
    rw [Matrix.det_of_upperTriangular (fun a b hab => hA τ a b hab)] at hdet
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => h.co gV τ j j) (Finset.mem_univ i)) hdet

  obtain ⟨hkf, hhk⟩ := EigFrame.exists_isMap h r hk.2.1 hk.1
  obtain ⟨gVk, hgVk⟩ := EigFrame.exists_isMap gV r hk.2.1 hk.1
  have hfhk : (_root_.GlobalTheory.ShFam.EigFrame.IsMap f) (r.comp ρ) hkf := isMap_comp hh hhk
  have hco : ∀ τ, hkf.co gk τ = (h.co gV τ).map r * gVk.co gk τ := fun τ => by
    rw [← EigFrame.IsMap.co τ hhk hgVk hk.1, EigFrame.co_mul]
  have key : ∀ τ, (∀ a i, i < a → hkf.co gk τ a i = 0) ∧ ∀ i, hkf.co gk τ i i = r (h.co gV τ i i) * tk τ i := by
    intro τ
    obtain ⟨hN, hNd⟩ := EigFrame.Tri.co τ hk hgVk
    have hm := upper_mul (M := (h.co gV τ).map r) (fun a i hia => by rw [Matrix.map_apply, hA τ a i hia, map_zero]) hN
    rw [hco]
    exact ⟨hm.1, fun i => by rw [hm.2, Matrix.map_apply, hNd]⟩
  refine ⟨fun τ i => ((hAd τ i).map r).unit * tk τ i, tri_of_co hfhk ?_ ?_ _ (fun τ => (key τ).1) fun τ i => ?_⟩
  · rw [hk.1, hxV, spMap_comp, Category.assoc]
  · rw [hk.2.1, hφV, RingHom.comp_assoc]
  · rw [(key τ).2, Units.val_mul, IsUnit.unit_spec]

end GlobalTheory.CarrySpec

namespace GlobalTheory.CarrySpec

open MvPolynomial GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem spec_of_anypoint (hany : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (k : Type) [Field k] (φ : c.F →+* k) (x : Sp k ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp k ⟶ C.Y.X), C.Carries p g → ∀ (y : C.Y.X) (ψ : C.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* C.Y.X.presheaf.stalk y) (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), p = spMap ψ ≫ stalkPt C.Y y → f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t → ∃ t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri ψ g t') : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Type) [CommRing V] [IsLocalRing V] (L : Type) [Field L] (ν : V →+* L), Function.Injective ν → ∀ (k : Type) [Field k] (r : V →+* k), RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ (q : Sp V ⟶ C.Y.X) (φV : c.F →+* V) (xV : Sp V ⟶ Z.X), xV = q ≫ C.π ≫ genι Z → ∀ (gV : EigFrame Z φV xV) (φL : c.F →+* L) (xL : Sp L ⟶ Z.X) (gL : EigFrame Z φL xL) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ), gV.Tri ν gL tL → C.Carries (spMap ν ≫ q) gL → ∀ (φk : c.F →+* k) (xk : Sp k ⟶ Z.X) (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), gV.Tri r gk tk → C.Carries (spMap r ≫ q) gk := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C V _ _ L _ ν hν k _ r _ q φV xV hxV gV φL xL gL tL hL hcar φk xk gk tk hk
  set y₀ := q (IsLocalRing.closedPoint V)
  set ρ := (Scheme.stalkClosedPointTo (R := CommRingCat.of V) q).hom
  have hq : spMap ρ ≫ stalkPt C.Y y₀ = q := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of V) q
  obtain ⟨φ₁, f, t, hf, -⟩ := C.gr_spec y₀
  have hpL : spMap ν ≫ q = spMap (ν.comp ρ) ≫ stalkPt C.Y y₀ :=
    (congrArg (spMap ν ≫ ·) hq).symm.trans (by rw [spMap_comp, Category.assoc])
  obtain ⟨t', hfL⟩ := hany E H Dw l Xo c O β Z F e C L φL xL gL (spMap ν ≫ q) hcar y₀ (ν.comp ρ) φ₁ f t hpL hf
  have hxV' : xV = spMap ρ ≫ (stalkPt C.Y y₀ ≫ C.π ≫ genι Z) :=
    hxV.trans ((congrArg (· ≫ C.π ≫ genι Z) hq).symm.trans (Category.assoc _ _ _))
  obtain ⟨t'', htri⟩ := tri_spec f ρ ν hν r hxV' gV gL tL hL t' hfL gk tk hk
  exact ⟨y₀, r.comp ρ, φ₁, f, t, t'',
    (congrArg (spMap r ≫ ·) hq).symm.trans (by rw [spMap_comp, Category.assoc]), hf, htri⟩

end GlobalTheory.CarrySpec
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFramesSpecialiseFlagComponentLocalRing

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.CarrySpec

theorem carries_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Type) [CommRing V] [IsLocalRing V] (L : Type) [Field L] (ν : V →+* L), Function.Injective ν → ∀ (k : Type) [Field k] (r : V →+* k), RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ (q : Sp V ⟶ C.Y.X) (φV : c.F →+* V) (xV : Sp V ⟶ Z.X), xV = q ≫ C.π ≫ genι Z → ∀ (gV : EigFrame Z φV xV) (φL : c.F →+* L) (xL : Sp L ⟶ Z.X) (gL : EigFrame Z φL xL) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ), gV.Tri ν gL tL → C.Carries (spMap ν ≫ q) gL → ∀ (φk : c.F →+* k) (xk : Sp k ⟶ Z.X) (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), gV.Tri r gk tk → C.Carries (spMap r ≫ q) gk :=
  GlobalTheory.CarrySpec.spec_of_anypoint GlobalTheory.T.carried_frame_triangular_through_stalkFrames

end GlobalTheory.CarrySpec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFramesSpecialiseFlagComponentLocalRingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.carriedFrames_specialise_flagComponent_localRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Type) [CommRing V] [IsLocalRing V] (L : Type) [Field L] (ν : V →+* L), Function.Injective ν → ∀ (k : Type) [Field k] (r : V →+* k), RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ (q : Sp V ⟶ C.Y.X) (φV : c.F →+* V) (xV : Sp V ⟶ Z.X), xV = q ≫ C.π ≫ genι Z → ∀ (gV : EigFrame Z φV xV) (φL : c.F →+* L) (xL : Sp L ⟶ Z.X) (gL : EigFrame Z φL xL) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ), gV.Tri ν gL tL → C.Carries (spMap ν ≫ q) gL → ∀ (φk : c.F →+* k) (xk : Sp k ⟶ Z.X) (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), gV.Tri r gk tk → C.Carries (spMap r ≫ q) gk := by
  first | exact @GlobalTheory.CarrySpec.carries_spec | exact GlobalTheory.CarrySpec.carries_spec | (intros; apply GlobalTheory.CarrySpec.carries_spec <;> assumption)
end
end
