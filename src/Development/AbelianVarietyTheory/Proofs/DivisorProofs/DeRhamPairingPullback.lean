module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieCombIffIsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassMemHodgeFiltrationOfCechRepZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsilonPartDeformationFormClassEqCoboundaryOfLifStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsOfCechKodairaSpencerDeformationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernEqSumCupInvariantFormsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderDeformationFormLiftValuesSub
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechRepresentativeChernClassTangentValue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeField
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassMemHodgeFiltrationOfCechRepZeroStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.crystallineClass_mem_hodgeFiltration_of_cechRep_zero : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (W : J → X.Opens), ⨆ j, W j = ⊤ → ∀ c : Z1 (O (dp0 R) s), IsRep W c 0 → H1.mk _ c ∈ F1 s := by
  first | exact @GlobalTheory.CechKS.h1_mk_mem_f1_of_isRep_zero | exact GlobalTheory.CechKS.h1_mk_mem_f1_of_isRep_zero | (intros; apply GlobalTheory.CechKS.h1_mk_mem_f1_of_isRep_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformationClassPullbackEqConstantAddEps

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham

theorem exists_const_add_eps_const {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
    (z : TensorProduct K (DualNumber K) (primDR A)) :
    ∃ a b : primDR A, liftSemi (constMor A).pull z =
      (constMor A).pull a + (DualNumber.eps : DualNumber K) • (constMor A).pull b := by
  induction z with
  | add x y hx hy =>
    obtain ⟨a, b, e⟩ := hx
    obtain ⟨a', b', e'⟩ := hy
    refine ⟨a + a', b + b', ?_⟩
    rw [map_add (f := _), e, e', map_add (f := _), map_add (f := _), smul_add]
    abel
  | tmul r c =>
    refine ⟨r.fst • c, r.snd • c, ?_⟩
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, smul_smul]
    have e1 : (TrivSqZeroExt.inl r.fst : DualNumber K) = algebraMap K (DualNumber K) r.fst := rfl
    have e2 : (TrivSqZeroExt.inr r.snd : DualNumber K) = DualNumber.eps * algebraMap K (DualNumber K) r.snd := by
      rw [DualNumber.inr_eq_smul_eps, Algebra.smul_def, mul_comm]
    have er : r = algebraMap K (DualNumber K) r.fst + DualNumber.eps * algebraMap K (DualNumber K) r.snd := by
      rw [← e1, ← e2, TrivSqZeroExt.inl_fst_add_inr_snd_eq]
    conv_lhs => rw [er]
    exact add_smul _ _ _

theorem liftMor_pull_eq_const_add_eps : GlobalTheory.Published.AbelianDeRham → ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A]
    (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A' →
    SmoothOfRelativeDimension g A'.hom → ∀ x : primDR A', ∃ b : primDR A,
      (liftMor (epsDP K) h).pull x = (constMor A).pull ((fibMor h).pull x) +
        (DualNumber.eps : DualNumber K) • (constMor A).pull b := by
  intro P K _ A _ A' _ i h g hA hg x
  have a₀ : IsAbelianScheme A := by
    haveI := hA.comm
    haveI : IsCommMonObj A := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
        ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected⟩
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  obtain ⟨z, hz⟩ := constMor_surjective P a₀ g₀ ((liftMor (epsDP K) h).pull x)
  obtain ⟨a, b, e⟩ := exists_const_add_eps_const z
  rw [hz] at e
  have red : (redMor A).pull ((liftMor (epsDP K) h).pull x) = (fibMor h).pull x :=
    GrpMor.pull_pull (liftMor (epsDP K) h) (redMor A) (fibMor h) (fun _ => rfl) (by simp) x
  have ra : (fibMor h).pull x = a := by
    rw [← red, e, map_add (f := _), LinearMap.map_smulₛₗ, redMor_constMor, redMor_constMor]
    have : (TrivSqZeroExt.fstHom K K K).toRingHom (DualNumber.eps : DualNumber K) = 0 := rfl
    rw [this, zero_smul, add_zero]
  exact ⟨b, by rw [ra]; exact e⟩

end GlobalTheory.CechKS
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformationClassPullbackEqConstantAddEpsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.deformation_class_pullback_eq_constant_add_eps : GlobalTheory.Published.AbelianDeRham → ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ x : primDR A', ∃ b : primDR A, (liftMor (epsDP K) h).pull x = (constMor A).pull ((fibMor h).pull x) + (DualNumber.eps : DualNumber K) • (constMor A).pull b := by
  first | exact @GlobalTheory.CechKS.liftMor_pull_eq_const_add_eps | exact GlobalTheory.CechKS.liftMor_pull_eq_const_add_eps | (intros; apply GlobalTheory.CechKS.liftMor_pull_eq_const_add_eps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderDeformationFormLiftValuesSubStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.firstOrderDeformation_form_lift_values_sub : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsAbelianScheme A → ∀ (ω : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K)))) (U : A'.left.Opens), IsAffineOpen U → ∀ (P : GPt A), P.In (i ⁻¹ᵁ U) → ∀ (y₁ y₂ : Sp (DualNumber P.B) ⟶ A'.left) (h₁ : IsLift i P y₁) (h₂ : IsLift i P y₂) (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (c : Fin n → P.B), (∀ a, IsTangent (u a)) → (∀ f : Γ(A'.left, U), valR y₁ U f - valR y₂ U f = (TrivSqZeroExt.inr (∑ a, c a * (valR (P.trx (u a)) (i ⁻¹ᵁ U) ((i.app U).hom f)).snd) : DualNumber P.B)) → (liftVal h ω.1 h₁ - liftVal h ω.1 h₂).snd = -∑ a, c a * algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω)) := by
  first | exact @GlobalTheory.CechKS.LiftDiff.liftVal_sub_snd | exact GlobalTheory.CechKS.LiftDiff.liftVal_sub_snd | (intros; apply GlobalTheory.CechKS.LiftDiff.liftVal_sub_snd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechRepresentativeChernClassTangentValueStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isCechRepresentative_chernClass_tangentValue : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → ∀ (I : Type) [Fintype I] (c : I → Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) (ω : I → Form (A.hom ≫ 𝟙 (Sp K))), IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (H1.mk _ (c k)) (Form.cl _ (ω k))) → ∀ v : epsR K ⟶ A, IsTangent v → ∀ (J : Type) (V : J → A.left.affineOpens) (τ : J → L.ι), (∀ j, (V j).1 ≤ L.U (τ j)) → IsRep (fun j => (V j).1) (∑ k, tanVal v (ω k) • c k) (fun j j' => dlog L v (τ j) (τ j')) := by
  first | exact @GlobalTheory.CechKS.isRep_chern_tanVal | exact GlobalTheory.CechKS.isRep_chern_tanVal | (intros; apply GlobalTheory.CechKS.isRep_chern_tanVal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPairingPullback

section

@[expose] public section

set_option autoImplicit false

noncomputable section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace

namespace GlobalTheory.CechKS



theorem exists_isRep_eps {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (DeRham.epsRed K) i) (hA : IsAbelianScheme A)
    (L : LB A.left) {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) (hu : ∀ a, IsTangent (u a))
    (H : IsCechKS A A' i L u θ) (ω' : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K))))
    (b : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))))
    (e : (liftMor (epsDP K) h).isMor.pull1 (Form.cl _ ω') =
      (constMor A).isMor.pull1 (Form.cl _ ((fibMor h).isMor.pullForm ω')) +
        (DualNumber.eps : DualNumber K) • (constMor A).isMor.pull1 (H1.mk _ b)) :
    ∃ (J : Type) (V : J → A.left.affineOpens) (τ : J → L.ι), ⨆ j, (V j).1 = ⊤ ∧ (∀ j, (V j).1 ≤ L.U (τ j)) ∧
      IsRep (fun j ↦ (V j).1) b fun j j' P ↦ -∑ a, (∑ c, algebraMap K P.B (θ a c) * dlog L (u c) (τ j) (τ j') P) *
        algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω')) := by
  classical
  obtain ⟨J, W, c, y, hW, hc, hl, hn, hd⟩ := GlobalTheory.T.exists_lifts_of_cechKodairaSpencerDeformation K A A' i L n u θ hu H
  obtain ⟨G, hG⟩ := GlobalTheory.T.epsilonPart_deformationForm_class_eq_coboundary_of_lifts K A A' i h ω' _ b e
  let J' : Type := {p : J × A'.left.affineOpens × A.left.affineOpens // p.2.2.1 ≤ W p.1 ⊓ i ⁻¹ᵁ p.2.1.1}
  refine ⟨J', fun j ↦ j.1.2.2, fun j ↦ c j.1.1, ?_, fun j ↦ (j.2.trans inf_le_left).trans (hc _), ?_⟩
  · refine eq_top_iff.2 fun p _ ↦ ?_
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hW.ge (Set.mem_univ p))
    obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ := A'.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (i p)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hle⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open
      (show p ∈ W k ⊓ i ⁻¹ᵁ U from ⟨hk, hpU⟩) (W k ⊓ i ⁻¹ᵁ U).isOpen
    exact Opens.mem_iSup.2 ⟨⟨(k, ⟨U, hU⟩, ⟨V, hV⟩), hle⟩, hpV⟩
  · have hin : ∀ (j : J') (P : GPt A), P.In j.1.2.2.1 → P.In (W j.1.1) := fun j P hP ↦
      hP.mono (j.2.trans inf_le_left)
    refine ⟨fun j P ↦ if hP : P.In (W j.1.1) then (liftVal h ω'.1 (hl _ P hP)).snd + G P else 0,
      fun j P Q φ hP ↦ ?_, fun j j' P hj hj' ↦ ?_⟩
    · simp only [dif_pos (hin j P hP), dif_pos (hin j Q (hP.map φ))]
      exact hG P Q φ _ _ _ _ (hn _ P Q φ (hin j P hP))
    · simp only [dif_pos (hin j P hj), dif_pos (hin j' P hj')]
      have hU : P.In (i ⁻¹ᵁ j.1.2.1.1) := hj.mono (j.2.trans inf_le_right)
      rw [add_sub_add_right_eq_sub, ← TrivSqZeroExt.snd_sub]
      exact GlobalTheory.T.firstOrderDeformation_form_lift_values_sub K A A' i h hA ω' _ j.1.2.1.2 P hU _ _ _ _ n u _ hu
        fun f ↦ hd _ _ P _ f (hin j P hj) (hin j' P hj') hU

theorem eval_eq_zero {K M I : Type*} [Field K] [AddCommGroup M] [Module K M] [Fintype I] {n : ℕ}
    (f k : Module.Dual K M) (b x : M) (c : I → M) (θ : Matrix (Fin n) (Fin n) K) (hb : Fin n → Module.Dual K M)
    (α p : Fin n → K) (t : Fin n → I → K) (e4 : ∀ a, hb a x = α a) (e5 : ∀ b, p b = ∑ k, f (c k) * t b k)
    (e1 : f (b + ∑ a, ∑ b, (θ a b * α a) • ∑ k, t b k • c k) = 0)
    (e2 : (TrivSqZeroExt.inl (f x) + TrivSqZeroExt.inr (k x) : DualNumber K) +
      (DualNumber.eps : DualNumber K) • (TrivSqZeroExt.inl (f b) + TrivSqZeroExt.inr (k b) : DualNumber K) = 0) :
    (k - ∑ a, (∑ b, θ a b * p b) • hb a) x = 0 := by
  have e3 := congrArg TrivSqZeroExt.snd e2
  have e6 : ∀ b, ∑ k, t b k * f (c k) = p b := fun b ↦
    (Finset.sum_congr rfl fun k _ ↦ mul_comm _ _).trans (e5 b).symm

  simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul, e6] at e1
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, e4, Finset.sum_mul]
  simp at e3
  have e7 : ∑ a, ∑ b, θ a b * p b * α a = ∑ a, ∑ b, θ a b * α a * p b :=
    Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring
  rw [e7]
  linear_combination e3 - e1



theorem isKSValue_of_isCechKS (P : GlobalTheory.Published.AbelianDeRham) {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
    {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (DeRham.epsRed K) i)
    {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hA' : IsAbelianScheme A')
    (hg' : SmoothOfRelativeDimension g A'.hom) (L : LB A.left) (hL : L.IsLB) (ψ : LinearMap.BilinForm K (HdR A))
    (hψ : IsPolForm (dp0 K) (𝟙 _) A L ψ) {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K)
    (hu : ∀ a, IsTangent (u a)) (H : IsCechKS A A' i L u θ) (hb : Fin n → HdR A)
    (hhb : ∀ b, DeRham.IsLieImage (hb b) (u b)) {f : HdR A} (hf : f ∈ Fil A) :
    IsKSValue h f (FlagTan.lieComb (fun a ↦ ∑ b, θ a b * ψ f (hb b)) u) := by
  classical
  obtain ⟨v, k, ⟨d, hd, hdk⟩, -⟩ := IsKSValue.exists_of_isAbelianScheme P h hA' hg' hf
  obtain ⟨I, _, c, ω, hω, hch, hψf⟩ := GlobalTheory.T.firstChern_eq_sum_cup_invariantForms P K A g hA hg L hL ψ hψ
  choose z hz using fun k ↦ H1.mk_surjective _ (c k).1
  have key : k - ∑ a, (∑ b, θ a b * ψ f (hb b)) • hb a ∈ Fil A := by
    letI : Algebra (DualNumber K) K := (TrivSqZeroExt.fstHom K K K).toRingHom.toAlgebra
    obtain ⟨-, hF⟩ := P.2.2.1 (DualNumber K) A' g hA' hg' K A i h
    rw [Fil, hF, Submodule.mem_dualAnnihilator]
    intro x hx
    refine (Submodule.span_le (p := LinearMap.ker (k - ∑ a, (∑ b, θ a b * ψ f (hb b)) • hb a))).2
      (fun x hx ↦ ?_) hx
    obtain ⟨⟨x, hx'⟩, hx, rfl⟩ := hx
    have hx0 := hx
    change x ∈ F1 _ at hx
    rw [hodgeFiltration_eq_range] at hx
    obtain ⟨ω', rfl⟩ := hx
    obtain ⟨b, hbe⟩ := GlobalTheory.T.deformation_class_pullback_eq_constant_add_eps P K A A' i h g hA' hg' ⟨_, hx'⟩
    obtain ⟨zb, hzb⟩ := H1.mk_surjective _ b.1
    let ω₀ := (fibMor h).isMor.pullForm ω'
    have hω₀ : Form.cl _ ω₀ ∈ primDR A := (fibMor h).pullback_mem_primitive hx'
    obtain ⟨J, V, τ, hV, hτ, hrep⟩ := exists_isRep_eps h hA L u θ hu H ω' zb (by
      rw [hzb]; exact congrArg Subtype.val hbe)
    have hch' : IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (H1.mk _ (z k)) (Form.cl _ (ω k))) := by
      simpa only [hz] using hch
    have hr := fun a ↦ GlobalTheory.T.isCechRepresentative_chernClass_tangentValue K A hA L hL I z ω hch' (u a) (hu a) J V τ hτ
    have hsum := hrep.add (IsRep.sum Finset.univ fun a _ ↦ IsRep.sum Finset.univ fun b _ ↦
      (hr b).smul (θ a b * tanVal (u a) ω₀))
    have hF1 := GlobalTheory.T.crystallineClass_mem_hodgeFiltration_of_cechRep_zero K _ _ J _ hV _ (hsum.congr (F' := 0) fun j j' Q _ _ ↦ by
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, map_mul,
        Finset.sum_mul]
      rw [neg_add_eq_zero]
      exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ mul_right_comm _ _ _)
    have hmem : b + ∑ a, ∑ b, (θ a b * tanVal (u a) ω₀) • ∑ k, tanVal (u b) (ω k) • c k ∈ PrimitiveSubmodule A := by
      refine Submodule.mem_comap.2 ?_

      simp only [map_add (f := _), map_sum, map_smul, hz, hzb] at hF1

      simp only [map_add (f := _), map_sum, map_smul]
      exact hF1
    have e1 := (Submodule.mem_dualAnnihilator _).1 hf _ hmem
    have e2 : d ((liftMor (epsDP K) h).pull ⟨_, hx'⟩) = 0 :=
      (Submodule.mem_dualAnnihilator _).1 hd _ hx0
    rw [hbe, map_add (f := _), map_smul, hdk, hdk] at e2
    have e4 : ∀ a, hb a ⟨_, hω₀⟩ = tanVal (u a) ω₀ := fun a ↦ (hhb a).2 ω₀ hω₀
    have e5 : ∀ b, ψ f (hb b) = ∑ k, f (c k) * tanVal (u b) (ω k) := fun b ↦
      (hψf f hf (hb b)).trans (Finset.sum_congr rfl fun k _ ↦ congrArg (f (c k) * ·) ((hhb b).2 (ω k) (hω k)))
    exact eval_eq_zero f k b ⟨_, hω₀⟩ c θ hb _ _ _ e4 e5 e1 e2
  refine ⟨k, ⟨d, hd, hdk⟩, ?_⟩
  have := (FlagTan.isLieImage_lieComb (fun a ↦ ∑ b, θ a b * ψ f (hb b)) hhb).add (isLieImage_one_iff.2 key)
  rwa [add_sub_cancel, _root_.mul_one] at this

end GlobalTheory.CechKS

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem GlobalTheory.CechKS.exists_const_isKSValue : GlobalTheory.CovTop.Hypotheses₂ → ∃ s : ℚ, s ≠ 0 ∧ ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A), GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A L ψ → ∀ (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K), (∀ a, IsTangent (u a)) → GlobalTheory.CechKS.IsCechKS A A' i L u θ → ∀ (hb : Fin n → GlobalTheory.DeRham.HdR A), (∀ b, GlobalTheory.DeRham.IsLieImage (hb b) (u b)) → ∀ f ∈ GlobalTheory.DeRham.Fil A, ∀ w : epsR K ⟶ A, IsLieComb (fun a => (s : K) * ∑ b, θ a b * ψ f (hb b)) u w → GlobalTheory.DeRham.IsKSValue h f w := by
  intro P
  refine ⟨1, one_ne_zero, ?_⟩
  intro K _ _ A _ A' _ i h g hA hg hA' hg' L hL ψ hψ n u θ hu H hb hhb f hf w hw
  obtain ⟨u', hu', rfl⟩ := hw
  have := GlobalTheory.CechKS.isKSValue_of_isCechKS P.p5 h hA hg hA' hg' L hL ψ hψ u θ hu H hb hhb hf
  convert this using 1
  rw [GlobalTheory.FlagTan.lieComb]
  congr 2
  funext a
  refine Over.OverMorphism.ext ((hu' a).trans ?_)
  simp only [Rat.cast_one, one_mul]
  rfl

end
end
end
end
