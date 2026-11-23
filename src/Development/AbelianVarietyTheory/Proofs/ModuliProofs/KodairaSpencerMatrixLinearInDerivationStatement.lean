module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAnalyticKodairaSpencerClassStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EntireAntilinearLatticePeriodsConst
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnVerticalVectorFieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueUniformisingVectorVerticalTangentStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.FderivFnAddLattice

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Uniq

section
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}

theorem ex_add_lattice (z : Fin g → ℂ) (l : u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem mem_dom_add_lattice (m : A₀.left ⟶ X) (W : X.Opens) (z : Fin g → ℂ) (l : u.Λ) :
    z + l ∈ dom u m W ↔ z ∈ dom u m W := by
  show ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ W ↔ ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W
  rw [ex_add_lattice]

theorem fderiv_fn_add_lattice (m : A₀.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) (z : Fin g → ℂ) (l : u.Λ) :
    fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fn u m W f) z := by
  have h : (fun w => fn u m W f (w + (l : Fin g → ℂ))) = fn u m W f := by
    funext w
    unfold fn
    rw [ex_add_lattice]
  calc fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fun w => fn u m W f (w + (l : Fin g → ℂ))) z :=
        (fderiv_comp_add_right (l : Fin g → ℂ)).symm
    _ = fderiv ℂ (fn u m W f) z := by rw [h]

theorem ptDer_sub {y : Sp ℂ ⟶ X} {δ δ' : ∀ W : X.Opens, Γ(X, W) → ℂ} (h : PtDer y δ) (h' : PtDer y δ') :
    PtDer y (fun W f => δ W f - δ' W f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro W hW f f'
    rw [h.add W hW f f', h'.add W hW f f']
    ring
  · intro W hW f f'
    rw [h.mul W hW f f', h'.mul W hW f f']
    ring
  · intro W W' hle hW' f
    rw [h.res W W' hle hW' f, h'.res W W' hle hW' f]
end

theorem ks_unique : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D Θ Θ' s s', KSRel u p m D Θ s → KSRel u p m D Θ' s' → Θ = Θ' := by
  intro P₀ u Hm χ hG R _ x₀ X p m hp hpb D Θ Θ' s s' hs hs'
  obtain ⟨w, hwd, hw⟩ := GlobalTheory.T.exists_differentiableOn_verticalVectorField P₀ u Hm χ hG R x₀ X p m hp hpb P₀.g Set.univ id
    (fun z W f => s z W f - s' z W f) isOpen_univ differentiable_id
    (fun z _ => ⟨ptDer_sub (hs.der z) (hs'.der z), fun r => by
      show s z ⊤ (constFn p ⊤ r) - s' z ⊤ (constFn p ⊤ r) = 0
      rw [hs.base, hs'.base, sub_self]⟩)
    (fun W f => ((hs.hol W f).sub (hs'.hol W f)).mono fun z hz => hz.2)
  have hw' : ∀ z W f, z ∈ dom u m W → s z W f - s' z W f = fderiv ℂ (fn u m W f) z (w z) :=
    fun z W f hz => hw z (Set.mem_univ z) W f hz
  have hper : ∀ (l : u.Λ) z, w (z + l) = w z + (Θ - Θ').mulVec (star (l : Fin P₀.g → ℂ)) := by
    intro l z
    obtain ⟨v, -, huniq⟩ := GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hG R x₀ X p m hp hpb z
      (fun W f => s z W f - s' z W f) (ptDer_sub (hs.der z) (hs'.der z)) (fun r => by
        show s z ⊤ (constFn p ⊤ r) - s' z ⊤ (constFn p ⊤ r) = 0
        rw [hs.base, hs'.base, sub_self])
    have e1 := huniq (w z) (fun W f hz => hw' z W f hz)
    have e2 := huniq (w (z + l) - (Θ - Θ').mulVec (star (l : Fin P₀.g → ℂ))) (fun W f hz => by
      have a1 := hw' (z + l) W f ((mem_dom_add_lattice u m W z l).2 hz)
      have a2 := hs.per l W f z hz
      have a3 := hs'.per l W f z hz
      rw [fderiv_fn_add_lattice] at a1
      show s z W f - s' z W f = _
      rw [map_sub, Matrix.sub_mulVec, map_sub]
      linear_combination a1 - a2 + a3)
    rw [← e1] at e2
    exact sub_eq_iff_eq_add.mp e2
  have hdisc : DiscreteTopology u.Λ := u.discrete
  have hspan : Submodule.span ℝ (u.Λ : Set (Fin P₀.g → ℂ)) = ⊤ := u.full
  have hwd' : Differentiable ℂ w := differentiableOn_univ.mp hwd
  ext i j
  have key := GlobalTheory.entire_antilinear_periods_const P₀.g u.Λ hdisc hspan (fun z => w z i) ((Θ - Θ') i)
    (differentiable_pi.mp hwd' i) (fun l z => congrFun (hper l z) i)
  have hij := congrFun key.1 j
  simp only [Matrix.sub_apply, Pi.zero_apply, sub_eq_zero] at hij
  exact hij

end GlobalTheory.KS.Uniq
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerMatrixLinearInDerivation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.Lin

section
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} {u : HolUnif A₀ L₀ g} {X : Scheme.{0}}
  {R : Type} [CommRing R] {p : X ⟶ Sp R} {m : A₀.left ⟶ X}

theorem ksRel_add {D D' : R → ℂ} {Θ Θ' : Matrix (Fin g) (Fin g) ℂ}
    {s s' : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ}
    (h : KSRel u p m D Θ s) (h' : KSRel u p m D' Θ' s') :
    KSRel u p m (fun r => D r + D' r) (Θ + Θ') (fun z W f => s z W f + s' z W f) := by
  refine { der := ?_, base := ?_, hol := ?_, per := ?_ }
  · intro z
    refine { add := ?_, mul := ?_, res := ?_ }
    · intro W hW f f'
      simp only [(h.der z).add W hW, (h'.der z).add W hW]
      ring
    · intro W hW f f'
      simp only [(h.der z).mul W hW, (h'.der z).mul W hW]
      ring
    · intro W W' hle hW' f
      simp only [(h.der z).res W W' hle hW', (h'.der z).res W W' hle hW']
  · intro z r
    simp only [h.base, h'.base]
  · intro W f
    exact (h.hol W f).add (h'.hol W f)
  · intro l W f z hz
    simp only [h.per l W f z hz, h'.per l W f z hz, Matrix.add_mulVec, map_add (f := _)]
    ring

theorem ksRel_smul (c : ℂ) {D : R → ℂ} {Θ : Matrix (Fin g) (Fin g) ℂ}
    {s : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ} (h : KSRel u p m D Θ s) :
    KSRel u p m (fun r => c * D r) (c • Θ) (fun z W f => c * s z W f) := by
  refine { der := ?_, base := ?_, hol := ?_, per := ?_ }
  · intro z
    refine { add := ?_, mul := ?_, res := ?_ }
    · intro W hW f f'
      simp only [(h.der z).add W hW]
      ring
    · intro W hW f f'
      simp only [(h.der z).mul W hW]
      ring
    · intro W W' hle hW' f
      simp only [(h.der z).res W W' hle hW']
  · intro z r
    simp only [h.base]
  · intro W f
    exact (h.hol W f).const_mul c
  · intro l W f z hz
    simp only [h.per l W f z hz, Matrix.smul_mulVec, map_smul, smul_eq_mul]
    ring
end

theorem ks_linear : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (o R : Type) [CommRing o] [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap (algebraMap R ℂ)) → ∃ κ : Derivation o R ℂ →ₗ[ℂ] Matrix (Fin P₀.g) (Fin P₀.g) ℂ, ∀ D : Derivation o R ℂ, ∃ s, KSRel u p m (fun r => D r) (κ D) s := by
  intro P₀ u Hm χ hG o R _ _ _ _ _ _ X p m hs hpb
  have hder : ∀ D : Derivation o R ℂ, IsDer (algebraMap R ℂ) (fun r => D r) := fun D =>
    ⟨fun a b => D.map_add a b, fun a b => by
      show D (a * b) = _
      rw [D.leibniz, Algebra.smul_def, Algebra.smul_def]⟩
  have hex : ∀ D : Derivation o R ℂ, ∃ Θ s, KSRel u p m (fun r => D r) Θ s := fun D =>
    GlobalTheory.T.exists_analytic_kodairaSpencer_class P₀ u Hm χ hG R (algebraMap R ℂ) X p m hs hpb _ (hder D)
  choose Θ s hΘ using hex
  have huniq : ∀ (D : Derivation o R ℂ) Θ' s', KSRel u p m (fun r => D r) Θ' s' → Θ D = Θ' :=
    fun D Θ' s' h => GlobalTheory.KS.Uniq.ks_unique P₀ u Hm χ hG R (algebraMap R ℂ) X p m hs hpb _ _ _ _ _ (hΘ D) h
  refine ⟨{ toFun := Θ, map_add' := ?_, map_smul' := ?_ }, fun D => ⟨s D, hΘ D⟩⟩
  · intro D D'
    apply huniq (D + D')
    have e : (fun r => (D + D') r) = fun r => D r + D' r := funext (add_apply D D')
    rw [e]
    exact ksRel_add (hΘ D) (hΘ D')
  · intro c D
    rw [RingHom.id_apply]
    apply huniq (c • D)
    have e : (fun r => (c • D) r) = fun r => c * D r := funext fun r => by
      rw [smul_apply, smul_eq_mul]
    rw [e]
    exact ksRel_smul c (hΘ D)

end GlobalTheory.KS.Lin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerMatrixLinearInDerivationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

theorem _root_.GlobalTheory.T.kodairaSpencer_matrix_linear_in_derivation : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (o R : Type) [CommRing o] [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap (algebraMap R ℂ)) → ∃ κ : Derivation o R ℂ →ₗ[ℂ] Matrix (Fin P₀.g) (Fin P₀.g) ℂ, ∀ D : Derivation o R ℂ, ∃ s, KSRel u p m (fun r => D r) (κ D) s := by
  first | exact @GlobalTheory.KS.Lin.ks_linear | exact GlobalTheory.KS.Lin.ks_linear | (intros; apply GlobalTheory.KS.Lin.ks_linear <;> assumption)
end
end
