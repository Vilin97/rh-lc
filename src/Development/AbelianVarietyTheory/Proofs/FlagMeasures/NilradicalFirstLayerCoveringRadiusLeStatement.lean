module

public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexSpanAtRealPlaceAutPointLatticePropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStabilizerNilradicalLiftOfIsotropic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPointStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubquotientCoveringRadiusRealPlacesStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStabilizerNilradicalIntegralLiftOfOrthogon

section

@[expose] public section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

noncomputable section

namespace GlobalTheory.NilLift

theorem exists_projector {O K V : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (Λ P : Submodule O V) (hfg : Λ.FG) (hspan : Submodule.span K (Λ : Set V) = ⊤)
    (hsat : ∀ c : O, c ≠ 0 → ∀ v ∈ Λ, c • v ∈ P → v ∈ P) :
    ∃ g : V →ₗ[K] V, (∀ z ∈ Λ, g z ∈ P) ∧ ∀ z ∈ Λ, z ∈ P → g z = z := by
  have hu : ∀ x : nonZeroDivisors O, IsUnit (algebraMap O (Module.End O V) x) := fun s => by
    have := isLocalizedModule_id (nonZeroDivisors O) V K
    exact IsLocalizedModule.map_units (S := nonZeroDivisors O) (LinearMap.id : V →ₗ[O] V) s
  have hloc : IsLocalizedModule (nonZeroDivisors O) Λ.subtype :=
    { map_units := hu
      surj := fun y => by
        have hy : y ∈ Submodule.span K (Λ : Set V) := by rw [hspan]; trivial
        obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K (Λ : Set V) y hy
        rw [Submodule.span_eq] at hs
        exact ⟨(⟨_, hs⟩, s), rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }
  have : Module.Finite O Λ := Module.Finite.iff_fg.2 hfg
  let Q : Submodule O Λ := P.comap Λ.subtype
  have : Module.Flat O (Λ ⧸ Q) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨v, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨c, hc⟩ := hq
    have h1 : Q.mkQ ((c : O) • v) = 0 := by rw [map_smul]; exact hc
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsat c (nonZeroDivisors.coe_ne_zero c) v v.2 h1
  have : Module.FinitePresentation O (Λ ⧸ Q) := Module.finitePresentation_of_finite _ _
  have : Module.Projective O (Λ ⧸ Q) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective
  let π : Λ →ₗ[O] Λ := LinearMap.id - s ∘ₗ Q.mkQ
  have hπ : ∀ v, π v ∈ Q := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 : Q.mkQ (s (Q.mkQ v)) = Q.mkQ v := LinearMap.congr_fun hs _
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  have hπ' : ∀ v ∈ Q, π v = v := by
    intro v hv
    have h1 : Q.mkQ v = 0 := by rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  let g : V →ₗ[K] V := LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) K
      (IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype (Λ.subtype ∘ₗ π) hu)
  have hg : ∀ y : Λ, g y = π y := fun y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype _ hu y
  refine ⟨g, fun z hz => ?_, fun z hz hP => ?_⟩
  · rw [hg ⟨z, hz⟩]
    exact hπ _
  · rw [hg ⟨z, hz⟩, hπ' ⟨z, hz⟩ hP]

section Form

variable {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

local notation "𝒽" => Formalism.UG.hform (starRingEnd E) J

theorem form_eq (x y : Fin n → E) : 𝒽 x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply,
    starRingEnd_apply]

theorem form_star (hJ : Formalism.UG.IsHerm (starRingEnd E) J) (x y : Fin n → E) :
    star (𝒽 x y) = 𝒽 y x := by
  have h : ∀ i j, star (J i j) = J j i := fun i j => congrFun (congrFun hJ j) i
  simp only [Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem form_adj (hJ : J.det ≠ 0) (Ψ : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    𝒽 x ((J⁻¹ * Ψᴴ * J) *ᵥ y) = 𝒽 (Ψ *ᵥ x) y := by
  rw [form_eq, form_eq, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Ne.isUnit hJ), Matrix.one_mul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem eq_zero_of_form (hJ : J.det ≠ 0) (y : Fin n → E) (h : ∀ x, 𝒽 x y = 0) : y = 0 := by
  have h1 : J *ᵥ y = 0 := by
    funext i
    have := h (Pi.single i 1)
    rw [form_eq] at this
    simpa [Pi.star_single] using this
  exact Matrix.eq_zero_of_mulVec_eq_zero hJ h1

theorem form_span_left (S : Set (Fin n → E)) (y : Fin n → E) (h : ∀ s ∈ S, 𝒽 s y = 0)
    (w : Fin n → E) (hw : w ∈ Submodule.span E S) : 𝒽 w y = 0 := by
  simp only [form_eq] at h ⊢
  induction hw using Submodule.span_induction with
  | mem s hs => exact h s hs
  | zero => simp
  | add a b _ _ ha hb => rw [star_add, add_dotProduct, ha, hb, add_zero]
  | smul c a _ ha => rw [star_smul, smul_dotProduct, ha, smul_zero]

theorem inNil_sub_adj (hJ : Formalism.UG.IsHerm (starRingEnd E) J) (hdet : J.det ≠ 0)
    (W : Submodule E (Fin n → E)) (hW : ∀ w ∈ W, w ∈ perpSet (starRingEnd E) J W)
    (Ψ : Matrix (Fin n) (Fin n) E) (h1 : ∀ u, Ψ *ᵥ u ∈ W) (h2 : ∀ u ∈ W, Ψ *ᵥ u = 0) :
    InNil (starRingEnd E) J W (Ψ - J⁻¹ * Ψᴴ * J) ∧
      ∀ u ∈ perpSet (starRingEnd E) J W, (J⁻¹ * Ψᴴ * J) *ᵥ u = 0 := by
  have hA : ∀ u ∈ perpSet (starRingEnd E) J W, (J⁻¹ * Ψᴴ * J) *ᵥ u = 0 := fun u hu =>
    eq_zero_of_form J hdet _ fun v => by rw [form_adj J hdet]; exact hu _ (h1 v)
  have hsr : ∀ a b c : Fin n → E, 𝒽 a (b - c) = 𝒽 a b - 𝒽 a c := fun a b c => by
    simp only [form_eq, Matrix.mulVec_sub, dotProduct_sub]
  have hsl : ∀ a b c : Fin n → E, 𝒽 (b - c) a = 𝒽 b a - 𝒽 c a := fun a b c => by
    simp only [form_eq, star_sub, sub_dotProduct]
  refine ⟨⟨fun u u' => ?_, fun u w hw => ?_, fun u hu => ?_, fun u hu => ?_⟩, hA⟩
  · rw [Matrix.sub_mulVec, Matrix.sub_mulVec, hsr, hsl, form_adj J hdet,
      ← form_star J hJ u' ((J⁻¹ * Ψᴴ * J) *ᵥ u), form_adj J hdet, form_star J hJ]
    ring
  · rw [Matrix.sub_mulVec, hsr, form_adj J hdet, h2 w hw, hW _ (h1 u) w hw, form_eq]
    simp
  · rw [Matrix.sub_mulVec, hA u hu, sub_zero]
    exact h1 u
  · rw [Matrix.sub_mulVec, hA u (hW u hu), sub_zero]
    exact h2 u hu

end Form

theorem mem_perpIn_iff (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) (y : Fin I.n → I.E) :
    y ∈ perpIn I x S ↔ y ∈ lamX I x ∧ ∀ s ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨zero_mem _, fun s _ => by simp [form_eq]⟩
  | add y z _ _ hy hz =>
    exact ⟨add_mem hy.1 hz.1, fun s hs => by
      rw [form_eq, Matrix.mulVec_add, dotProduct_add, ← form_eq, ← form_eq, hy.2 s hs, hz.2 s hs, add_zero]⟩
  | smul c y _ hy =>
    exact ⟨Submodule.smul_mem _ _ hy.1, fun s hs => by
      rw [form_eq, Matrix.mulVec_smul, dotProduct_smul, ← form_eq, hy.2 s hs, smul_zero]⟩

theorem exists_nilInt_lift : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), R ≤ perpIn I x R → ∀ Φ : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ R, Φ *ᵥ y = 0) → (∀ y ∈ perpIn I x R, Φ *ᵥ y ∈ R) → ∃ Y ∈ nilInt I x R, ∀ y ∈ perpIn I x R, Y *ᵥ y = Φ *ᵥ y := by
  intro I x R hR Φ hΦ0 hΦ
  obtain ⟨-, hfg, hspan, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  obtain ⟨g, hg, hg'⟩ := exists_projector (lamX I x) (perpIn I x R) hfg hspan (fun c hc v hv h => by
    refine (mem_perpIn_iff I x R v).2 ⟨hv, fun s hs => ?_⟩
    have h1 := ((mem_perpIn_iff I x R _).1 h).2 s hs
    rw [form_eq, Matrix.mulVec_smul, dotProduct_smul, ← form_eq] at h1
    exact (smul_eq_zero.1 h1).resolve_left hc)
  set W := Submodule.span I.E (R : Set (Fin I.n → I.E)) with hWdef
  let Ψ : Matrix (Fin I.n) (Fin I.n) I.E := Φ * LinearMap.toMatrix' g
  have hΨ : ∀ u, Ψ *ᵥ u = Φ *ᵥ g u := fun u => by
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
  have hPΛ : ∀ y ∈ perpIn I x R, y ∈ lamX I x := fun y hy => ((mem_perpIn_iff I x R y).1 hy).1
  have hΨP : ∀ y ∈ perpIn I x R, Ψ *ᵥ y = Φ *ᵥ y := fun y hy => by rw [hΨ, hg' y (hPΛ y hy) hy]
  have hΨΛ : ∀ y ∈ lamX I x, Ψ *ᵥ y ∈ R := fun y hy => by rw [hΨ]; exact hΦ _ (hg y hy)
  have hP : ∀ y ∈ perpIn I x R, y ∈ perpSet (starRingEnd I.E) I.J W := fun y hy =>
    form_span_left I.J _ y ((mem_perpIn_iff I x R y).1 hy).2
  have hW : ∀ w ∈ W, w ∈ perpSet (starRingEnd I.E) I.J W := fun w hw w' hw' => by
    rw [← form_star I.J I.J_herm, form_span_left I.J _ w' (fun s hs => ?_) w hw, star_zero]
    rw [← form_star I.J I.J_herm, hP s (hR hs) w' hw', star_zero]
  have h1 : ∀ u, Ψ *ᵥ u ∈ W := fun u => by
    have : Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) ≤ W.comap (Matrix.mulVecLin Ψ) :=
      Submodule.span_le.2 fun y hy => Submodule.subset_span (hΨΛ y hy)
    exact this (hspan ▸ Submodule.mem_top)
  have h2 : ∀ u ∈ W, Ψ *ᵥ u = 0 := fun u hu => by
    have : W ≤ LinearMap.ker (Matrix.mulVecLin Ψ) :=
      Submodule.span_le.2 fun y hy => (hΨP y (hR hy)).trans (hΦ0 y hy)
    exact this hu
  obtain ⟨hN, hA⟩ := inNil_sub_adj I.J I.J_herm I.J_det W hW Ψ h1 h2
  refine ⟨_, ⟨hN, fun u hu => ?_⟩, fun y hy => ?_⟩
  · rw [Matrix.sub_mulVec]
    refine sub_mem (hPΛ _ (hR (hΨΛ u hu))) ((hdual _).2 fun z hz => ?_)
    rw [form_adj I.J I.J_det]
    exact (hdual u).1 hu _ (hPΛ _ (hR (hΨΛ z hz)))
  · rw [Matrix.sub_mulVec, hA y (hP y hy), sub_zero, hΨP y hy]

end GlobalTheory.NilLift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStabilizerNilradicalIntegralLiftOfOrthogonStatement

section

@[expose] public section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

theorem _root_.GlobalTheory.T.exists_stabilizerNilradicalIntegral_lift_of_orthogonal : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), R ≤ perpIn I x R → ∀ Φ : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ R, Φ *ᵥ y = 0) → (∀ y ∈ perpIn I x R, Φ *ᵥ y ∈ R) → ∃ Y ∈ nilInt I x R, ∀ y ∈ perpIn I x R, Y *ᵥ y = Φ *ᵥ y := by
  first | exact @GlobalTheory.NilLift.exists_nilInt_lift | exact GlobalTheory.NilLift.exists_nilInt_lift | (intros; apply GlobalTheory.NilLift.exists_nilInt_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStabilizerNilradicalLiftOfIsotropicStatement

section

@[expose] public section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

theorem _root_.GlobalTheory.T.exists_stabilizerNilradical_lift_of_isotropic : ∀ (n : ℕ) (ε : Fin n → Bool) (H G D : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)), IsUnit G.det → Gᴴ * H * G = Jm ε → (∀ u ∈ W, u ∈ perpSet (starRingEnd ℂ) H W) → (∀ u ∈ W, D *ᵥ u = 0) → (∀ u ∈ perpSet (starRingEnd ℂ) H W, D *ᵥ u ∈ W) → ∃ A : Matrix (Fin n) (Fin n) ℂ, InNil (starRingEnd ℂ) H W A ∧ (∀ u ∈ perpSet (starRingEnd ℂ) H W, A *ᵥ u = D *ᵥ u) ∧ hs (G⁻¹ * A * G) ≤ 2 * hs (G⁻¹ * D * G) := by
  first | exact @GlobalTheory.NilLift.exists_lift | exact GlobalTheory.NilLift.exists_lift | (intros; apply GlobalTheory.NilLift.exists_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NilradicalFirstLayerCoveringRadiusLe

section

@[expose] public section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

noncomputable section

namespace GlobalTheory.Count.FirstLayer

theorem inNil_sub {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (W : Submodule A (Fin n → A)) (Y Y' : Matrix (Fin n) (Fin n) A)
    (h : InNil s J W Y) (h' : InNil s J W Y') : InNil s J W (Y - Y') := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := h'
  have l1 : ∀ a b c : Fin n → A, Formalism.UG.hform s J (a - b) c = Formalism.UG.hform s J a c - Formalism.UG.hform s J b c := by
    intro a b c
    simp [Formalism.UG.hform, sub_mul, Finset.sum_sub_distrib]
  have l2 : ∀ a b c : Fin n → A, Formalism.UG.hform s J c (a - b) = Formalism.UG.hform s J c a - Formalism.UG.hform s J c b := by
    intro a b c
    simp [Formalism.UG.hform, mul_sub, Finset.sum_sub_distrib]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u u'
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, l1, l2]
    have a := h1 u u'
    have b := g1 u u'
    linear_combination a - b
  · intro u w hw
    rw [Matrix.sub_mulVec, l2, h2 u w hw, g2 u w hw, sub_zero]
  · intro u hu
    rw [Matrix.sub_mulVec]
    exact W.sub_mem (h3 u hu) (g3 u hu)
  · intro u hu
    rw [Matrix.sub_mulVec, h4 u hu, g4 u hu, sub_zero]

theorem map_mulVec_emb (I : AutInst) (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) I.E)
    (y : Fin I.n → I.E) :
    M.map (I.φ v) *ᵥ (fun i => I.φ v (y i)) = fun i => I.φ v ((M *ᵥ y) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

theorem mem_spanAt (I : AutInst) (v : InfinitePlace I.F) (R : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (y : Fin I.n → I.E) (hy : y ∈ R) : (fun i => I.φ v (y i)) ∈ spanAt I R v :=
  Submodule.subset_span ⟨y, hy, rfl⟩

theorem mulVec_mem_of_span (I : AutInst) (v : InfinitePlace I.F) (A : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (M : Matrix (Fin I.n) (Fin I.n) ℂ) (W : Submodule ℂ (Fin I.n → ℂ))
    (h : ∀ y ∈ A, M *ᵥ (fun i => I.φ v (y i)) ∈ W) : ∀ u ∈ spanAt I A v, M *ᵥ u ∈ W := by
  have : spanAt I A v ≤ W.comap (Matrix.mulVecLin M) := by
    unfold spanAt
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  intro u hu
  exact this hu

theorem frame_inv (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) ℂ) :
    uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * M * I.P v * uMat (x.1 v) =
      (I.P v * uMat (x.1 v))⁻¹ * M * (I.P v * uMat (x.1 v)) := by
  rw [Matrix.mul_inv_rev]
  have : uMat (x.1 v)⁻¹ = (uMat (x.1 v))⁻¹ := by
    simp only [uMat, Subgroup.coe_inv, Matrix.coe_units_inv]
  rw [this]
  simp only [Matrix.mul_assoc]

theorem frame_det (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) :
    IsUnit (I.P v * uMat (x.1 v)).det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  exact (I.P_unit v).mul (Units.isUnit _)

theorem frame_spec (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) :
    (I.P v * uMat (x.1 v))ᴴ * I.J.map (I.φ v) * (I.P v * uMat (x.1 v)) = Jm (I.ε v) := by
  have h : (uMat (x.1 v))ᴴ * Jm (I.ε v) * uMat (x.1 v) = Jm (I.ε v) := (x.1 v).2
  rw [← h, ← I.P_spec v, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem arith (n f k j rd lo hi rho : ℝ) (hf : 0 < f) (hrd : 0 ≤ rd) (hkj : k + j = n) (hlo : 0 < lo)
    (hhi : 0 < hi) (hr : hi ≤ rho * lo) :
    Real.sqrt 2 * ((k - j) * j * Real.sqrt f * rd * hi / (2 * lo)) ≤
      (n ^ 2 * f) / 8 * rd * rho / Real.sqrt (2 * f) := by
  have h1 : (k - j) * j ≤ n ^ 2 / 8 := by
    rw [← hkj]; nlinarith [sq_nonneg (k - 3 * j)]
  have h2 : hi / lo ≤ rho := by rwa [div_le_iff₀ hlo]
  have h3 : 0 < hi / lo := div_pos hhi hlo
  have hs : 0 < Real.sqrt (2 * f) := Real.sqrt_pos.2 (by linarith)
  have e : Real.sqrt 2 * Real.sqrt f = Real.sqrt (2 * f) := (Real.sqrt_mul (by norm_num) f).symm
  have e2 : Real.sqrt (2 * f) * Real.sqrt (2 * f) = 2 * f := Real.mul_self_sqrt (by linarith)
  have e3 : (n ^ 2 * f) / 8 * rd * rho / Real.sqrt (2 * f) =
      n ^ 2 / 8 * rho * (Real.sqrt (2 * f) * rd / 2) := by
    rw [div_eq_iff hs.ne']
    linear_combination (-(n ^ 2 / 8 * rho * rd / 2)) * e2
  have e4 : Real.sqrt 2 * ((k - j) * j * Real.sqrt f * rd * hi / (2 * lo)) =
      (k - j) * j * (hi / lo) * (Real.sqrt (2 * f) * rd / 2) := by
    rw [← e]; field_simp
  rw [e3, e4]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc (k - j) * j * (hi / lo) ≤ n ^ 2 / 8 * (hi / lo) := mul_le_mul_of_nonneg_right h1 h3.le
    _ ≤ n ^ 2 / 8 * rho := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem main : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi rho : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) → 0 < lo → hi ≤ rho * lo → ∀ Y ∈ nilReal I R, ∃ Y₀ ∈ nilInt I x R, ∃ Z ∈ cenReal I R, normAt I x (Y - diagEmb I Y₀ - Z) ≤ ((I.n : ℝ) ^ 2 * I.f) / 8 * I.rd * rho / Real.sqrt (2 * I.f) := by
  intro I x R lo hi rho hsat hiso hhi hlarge hlow hlo hr Y hY
  have hpl : perpIn I x R ≤ lamX I x := by
    unfold perpIn
    rw [Submodule.span_le]
    exact fun y hy => hy.1
  have hfg : (lamX I x).FG := (GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x).2.1
  have hsat' : IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x R) R := by
    refine ⟨hiso, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hiso hy, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩ hz
      exact hsat.2.2 _ ⟨y, hpl hy, rfl⟩ hz
  obtain ⟨-, -, hperp, hnil, -⟩ := GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties I x R
  have hP : ∀ v u, u ∈ perpSet (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) ↔
      u ∈ spanAt I (perpIn I x R) v := by
    intro v u
    rw [← hperp v]; rfl
  have hmono : ∀ v, spanAt I R v ≤ spanAt I (perpIn I x R) v := fun v =>
    Submodule.span_mono (Set.image_mono hiso)
  obtain ⟨Φ, hΦ0, hΦ1, D, hD, hDn⟩ := GlobalTheory.T.subquotient_covering_radius_real_places I x (perpIn I x R) R R lo hi (hfg.of_le hpl) hsat'
    (hfg.of_le hsat.1) hlo hhi (fun N h1 h2 => hlow N h1 (h2.trans hpl)) hlarge Y
    (fun v y hy => (hY v).2.2.2 _ (mem_spanAt I v R y hy))
    (fun v y hy => (hY v).2.2.1 _ ((hP v _).2 (mem_spanAt I v _ y hy)))
  obtain ⟨Y₀, hY₀, hY₀Φ⟩ := GlobalTheory.T.exists_stabilizerNilradicalIntegral_lift_of_orthogonal I x R hiso Φ hΦ0 hΦ1
  have hA : ∀ v, ∃ A : Matrix (Fin I.n) (Fin I.n) ℂ,
      InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) A ∧
      (∀ u ∈ perpSet (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v), A *ᵥ u = D v *ᵥ u) ∧
      hs ((I.P v * uMat (x.1 v))⁻¹ * A * (I.P v * uMat (x.1 v))) ≤
        2 * hs ((I.P v * uMat (x.1 v))⁻¹ * D v * (I.P v * uMat (x.1 v))) := by
    intro v
    refine GlobalTheory.T.exists_stabilizerNilradical_lift_of_isotropic I.n (I.ε v) _ _ (D v) _ (frame_det I x v) (frame_spec I x v)
      (fun u hu => (hP v u).2 (hmono v hu)) ?_ ?_
    · intro u hu
      have h0 : Φ.map (I.φ v) *ᵥ u ∈ (⊥ : Submodule ℂ (Fin I.n → ℂ)) := by
        refine mulVec_mem_of_span I v R _ ⊥ ?_ u hu
        intro y hy
        rw [map_mulVec_emb, hΦ0 y hy, Submodule.mem_bot]
        funext i; simp
      rw [hD v u (hmono v hu), Matrix.sub_mulVec, (hY v).2.2.2 u hu, (Submodule.mem_bot ℂ).1 h0, sub_zero]
    · intro u hu
      have h0 : Φ.map (I.φ v) *ᵥ u ∈ spanAt I R v := by
        refine mulVec_mem_of_span I v _ _ _ ?_ u ((hP v u).1 hu)
        intro y hy
        rw [map_mulVec_emb]
        exact mem_spanAt I v R _ (hΦ1 y hy)
      rw [hD v u ((hP v u).1 hu), Matrix.sub_mulVec]
      exact Submodule.sub_mem _ ((hY v).2.2.1 u hu) h0
  choose A hA1 hA2 hA3 using hA
  refine ⟨Y₀, hY₀, Y - diagEmb I Y₀ - A, ?_, ?_⟩
  · intro v
    refine ⟨inNil_sub _ _ _ _ _ (inNil_sub _ _ _ _ _ (hY v) (hnil Y₀ hY₀.1 v)) (hA1 v), ?_⟩
    intro u hu
    have h0 : (Y₀.map (I.φ v) - Φ.map (I.φ v)) *ᵥ u ∈ (⊥ : Submodule ℂ (Fin I.n → ℂ)) := by
      refine mulVec_mem_of_span I v _ _ ⊥ ?_ u ((hP v u).1 hu)
      intro y hy
      rw [Matrix.sub_mulVec, map_mulVec_emb, map_mulVec_emb, hY₀Φ y hy, sub_self]
      exact Submodule.zero_mem _
    rw [Submodule.mem_bot, Matrix.sub_mulVec, sub_eq_zero] at h0
    show (Y v - Y₀.map (I.φ v) - A v) *ᵥ u = 0
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, hA2 v u hu, hD v u ((hP v u).1 hu), Matrix.sub_mulVec, h0,
      sub_self]
  · rw [sub_sub_cancel]
    have hAD : normAt I x A ≤ Real.sqrt 2 * normAt I x D := by
      unfold normAt
      rw [← Real.sqrt_mul (by norm_num), Finset.mul_sum]
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro v _
      rw [frame_inv, frame_inv]
      exact hA3 v
    have hrk : rkK (perpIn I x R) + rkK R = I.n :=
      ((GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint I x).2.2.2 R R hsat hsat le_rfl).2.1
    have hf : (0 : ℝ) < I.f := by
      have : 0 < I.f := Module.finrank_pos
      exact_mod_cast this
    have hrd : 0 ≤ I.rd := Real.rpow_nonneg (abs_nonneg _) _
    refine hAD.trans ((mul_le_mul_of_nonneg_left hDn (Real.sqrt_nonneg _)).trans ?_)
    exact arith _ _ _ _ _ _ _ _ hf hrd (by exact_mod_cast hrk) hlo hhi hr

end GlobalTheory.Count.FirstLayer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NilradicalFirstLayerCoveringRadiusLeStatement

section

@[expose] public section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

theorem _root_.GlobalTheory.T.nilradical_first_layer_covering_radius_le : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi rho : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) → 0 < lo → hi ≤ rho * lo → ∀ Y ∈ nilReal I R, ∃ Y₀ ∈ nilInt I x R, ∃ Z ∈ cenReal I R, normAt I x (Y - diagEmb I Y₀ - Z) ≤ ((I.n : ℝ) ^ 2 * I.f) / 8 * I.rd * rho / Real.sqrt (2 * I.f) := by
  first | exact @GlobalTheory.Count.FirstLayer.main | exact GlobalTheory.Count.FirstLayer.main | (intros; apply GlobalTheory.Count.FirstLayer.main <;> assumption)
end
end
