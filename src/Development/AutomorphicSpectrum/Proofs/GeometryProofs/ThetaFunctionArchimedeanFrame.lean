module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogenyStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSpaceEquivHolUnif
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexAbelianFibreAmpleStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsArchimedeanFrameStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartCoordinatesStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaBasisOfFactorStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FnFactor
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoordinatesUniqueStatement
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionUniqueStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionsFiniteDimStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierNormalFormStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformizationDimEqPpDimStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformizationIsoTransferStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArchimedeanFrameOfPullback

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameLen

theorem len_sq_eq_pi_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ D.t.G.left) (g : ℕ) (u : HolUnif A (D.t.PP.L.pull φ) g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), IsAbelianScheme A → IsGrpPullback A D.t.G (emb σ) φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → u.IsAH Hm χ → ∀ (a : D.Frame σ) (x : D.B.carrier) (c : Fin D.g → ℂ), D.IsVec a x c → D.len σ x ^ 2 = Real.pi * (a.herm c c).re := by
  intro E _ _ _ H L _ _ D σ A _ φ g u Hm χ hab hp h1 h2 hah a x c hvec
  obtain ⟨v, hlift, v', hv', hdiff⟩ := hvec
  have e : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L)) = emb σ := Category.comp_id _
  let v₀ : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) ⟶ D.t.G :=
    Over.homMk v.left (by simpa using Over.w v)
  have hl₀ : (v₀.left ≫ (𝟙 D.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left) := hlift
  obtain ⟨hL, hvt, -, A', _, φ', g', u', Hm', χ', p, q, a', b', hp', hah', ep, eq', dp, dq, hval⟩ :=
    D.fib σ x x v₀ v₀ hl₀ hl₀
  have hp₀ : IsGrpPullback A D.t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) φ :=
    IsGrpPullback.congr hp e.symm rfl
  have hpz : IsGrpPullback A' D.t.G (emb σ) φ' := IsGrpPullback.congr hp' e rfl
  let x₁ : epsR ℂ ⟶ A := (HodgeLin.tanEquiv hp₀).symm v₀
  have hx₁ : HodgeLin.tanEquiv hp₀ x₁ = v₀ := (HodgeLin.tanEquiv hp₀).apply_symm_apply _
  have tx₁ : IsTangent x₁ := (HodgeLin.isTangent_iff hp₀ x₁).2 (by rw [hx₁]; exact hvt)
  have lx₁ : x₁.left ≫ φ = v.left := congrArg (fun r => r.left) hx₁
  obtain ⟨w, hw, -⟩ := h1 x₁ tx₁
  have T1 := GlobalTheory.T.hol_unif_compare_isogeny (Sp (𝓞 L)) D.t.G D.t.PP.L (emb σ) A a.A φ a.φ g D.g u a.u Hm a.Hm χ a.χ D.t.PP.isLB hab hp
    a.cart h1 h2 hah a.ah x₁ x₁ v' v' w w c c tx₁ tx₁ (hv'.trans lx₁.symm) (hv'.trans lx₁.symm) hw hw hdiff hdiff
  have T2 := GlobalTheory.T.hol_unif_compare_isogeny (Sp (𝓞 L)) D.t.G D.t.PP.L (emb σ) A A' φ φ' g g' u u' Hm Hm' χ χ' D.t.PP.isLB hab hp
    hpz h1 h2 hah hah' x₁ x₁ q p w w b' a' tx₁ tx₁ (eq'.trans lx₁.symm) (ep.trans lx₁.symm) hw hw dq dp
  have hH : a.herm c c = hermForm Hm' b' a' := T1.trans T2.symm
  have hin : ((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) : ℂ) =
      Real.pi * a.herm c c := by
    rw [hH]; exact hval
  have hnn : 0 ≤ ((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x)
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) : ℂ).re := (D.B.metric.form σ).re_inner_nonneg _
  unfold PPData.len
  rw [Real.sq_sqrt hnn, hin, Complex.re_ofReal_mul]

end GlobalTheory.CompanionTheory.Ar.Sl.FrameLen
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArchimedeanFrameOfPullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.archimedean_frame_of_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ D.t.G.left) (g : ℕ) (u : HolUnif A (D.t.PP.L.pull φ) g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), IsAbelianScheme A → IsGrpPullback A D.t.G (emb σ) φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → u.IsAH Hm χ → ∀ (a : D.Frame σ) (x : D.B.carrier) (c : Fin D.g → ℂ), D.IsVec a x c → D.len σ x ^ 2 = Real.pi * (a.herm c c).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.FrameLen.len_sq_eq_pi_herm | exact GlobalTheory.CompanionTheory.Ar.Sl.FrameLen.len_sq_eq_pi_herm | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.FrameLen.len_sq_eq_pi_herm <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FnFactorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.theta_add_lattice_eq_of_isFn : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ), a.IsFn s θ → ∀ (l : a.u.Λ) (w : Fin g → ℂ), θ (w + l) = (a.χ l * Complex.exp (Real.pi * a.herm w l + Real.pi / 2 * a.herm l l)) ^ n * θ w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Fac.fn_factor | exact GlobalTheory.CompanionTheory.Ar.Sl.Fac.fn_factor | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Fac.fn_factor <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroCoordsOfNonzeroVector

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameZero

theorem tmul_one_injective {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ)
    (M : Type) [AddCommGroup M] [Module (𝓞 L) M] [Module.Projective (𝓞 L) M] (x : M)
    (h : (1 : ComplexAt σ) ⊗ₜ[𝓞 L] x = 0) : x = 0 := by
  have hinj : Function.Injective (Algebra.linearMap (𝓞 L) (ComplexAt σ)) := by
    intro a b hab
    have h1 : σ (a : L) = σ (b : L) := hab
    exact RingOfIntegers.coe_injective (σ.injective h1)
  have hr := Module.Flat.rTensor_preserves_injective_linearMap (M := M) _ hinj
  have h2 : (Algebra.linearMap (𝓞 L) (ComplexAt σ)).rTensor M ((1 : 𝓞 L) ⊗ₜ[𝓞 L] x) =
      (Algebra.linearMap (𝓞 L) (ComplexAt σ)).rTensor M 0 := by
    rw [LinearMap.rTensor_tmul, map_zero, Algebra.linearMap_apply, map_one, h]
  have h3 := hr h2
  have h4 := congrArg (TensorProduct.lid (𝓞 L) M) h3
  simpa using h4

theorem core_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] (C : InnerProductSpace.Core ℂ V)
    (v : V) (h : (C.inner v v : ℂ).re = 0) : v = 0 := by
  apply C.definite
  have him : (C.inner v v : ℂ).im = 0 := by
    have h1 := C.conj_inner_symm v v
    have h2 := congrArg Complex.im h1
    simp only [Complex.conj_im] at h2
    linarith
  exact Complex.ext h him

theorem coord_ne_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type)
    [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (x : D.B.carrier)
    (c : Fin D.g → ℂ) (hlen : D.len σ x ^ 2 = Real.pi * (a.herm c c).re) (hx : x ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply hx
  have hherm : a.herm 0 0 = 0 := by simp [ArchFrame.herm]
  rw [hherm, Complex.zero_re, mul_zero] at hlen
  have hl : D.len σ x = 0 := by simpa using hlen
  have hnn : 0 ≤ (((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x)
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) : ℂ)).re :=
    (D.B.metric.form σ).re_inner_nonneg _
  have hle := Real.sqrt_eq_zero'.mp hl
  exact tmul_one_injective σ D.B.carrier x (core_eq_zero _ _ (le_antisymm hle hnn))

end GlobalTheory.CompanionTheory.Ar.Sl.FrameZero
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroCoordsOfNonzeroVectorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.nonzero_coords_of_nonzero_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (x : D.B.carrier) (c : Fin D.g → ℂ), D.len σ x ^ 2 = Real.pi * (a.herm c c).re → x ≠ 0 → c ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.FrameZero.coord_ne_zero | exact GlobalTheory.CompanionTheory.Ar.Sl.FrameZero.coord_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.FrameZero.coord_ne_zero <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionDifferentiable

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl

theorem isFn_differentiable : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ), a.IsFn s θ → Differentiable ℂ θ := by
  intro S G _ _ P z g a n s θ hθ w₀
  have hm : a.pt w₀ (default : PrimeSpectrum ℂ) ∈ ⨆ i, P.L.U i := by
    rw [P.isLB.cover]; trivial
  obtain ⟨i, hi'⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  have hi : ⊤ ≤ a.pt w₀ ⁻¹ᵁ P.L.U i := (GlobalTheory.top_le_preimage_iff_mem _ _).2 hi'
  let W : G.left.Opens := LB.wchart P.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i)
  let Q : a.A.left.Opens := (P.L.pull a.φ).U (fun _ => i)
  let C : Set (Fin g → ℂ) := {w | ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ Q}
  have hCpt : ∀ w, w ∈ C → ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i := fun w h y hy =>
    Set.mem_iInter.1 (h hy) PUnit.unit
  have hptC : ∀ w, ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i → w ∈ C := fun w h y hy =>
    Set.mem_iInter.2 fun _ => h hy
  have hCV : ∀ w, w ∈ C → ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ (a.φ ⁻¹ᵁ W) := fun w h y hy =>
    Set.mem_iInter.2 fun _ => hCpt w h hy
  have ho : IsOpen C := (a.u.hol Q 0).1
  have hv : DifferentiableOn ℂ (fun w => valAt' (a.u.ex w).left (a.φ ⁻¹ᵁ W) ((a.φ.app W).hom (s.f fun _ => i))) C :=
    (a.u.hol _ _).2.mono hCV
  have hfr : DifferentiableOn ℂ (fun w => a.u.fr (fun _ => i) w ^ n) C := (a.u.fr_hol _).pow n
  have hne : ∀ w ∈ C, a.u.fr (fun _ => i) w ^ n ≠ 0 := fun w hw => pow_ne_zero n (a.u.fr_ne _ w hw)
  have hq : DifferentiableOn ℂ θ C := by
    refine (hv.mul (hfr.inv hne)).congr fun w hw => ?_
    have e := hθ i w (hCpt w hw)
    have e' : valF (a.pt w) W (s.f fun _ => i) = valAt' (a.pt w) W (s.f fun _ => i) := rfl
    have e4 : valAt' (a.u.ex w).left (a.φ ⁻¹ᵁ W) ((a.φ.app W).hom (s.f fun _ => i)) = θ w * a.u.fr (fun _ => i) w ^ n :=
      (GlobalTheory.valAt'_comp (a.u.ex w).left a.φ W (s.f fun _ => i)).trans (e'.symm.trans e)
    exact (mul_inv_cancel_right₀ (hne w hw) (θ w)).symm.trans (congrArg (· * (a.u.fr (fun _ => i) w ^ n)⁻¹) e4.symm)
  exact (hq.differentiableAt (ho.mem_nhds (hptC w₀ hi)))

end GlobalTheory.CompanionTheory.Ar.Sl
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionDifferentiableStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.theta_function_differentiable : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ), a.IsFn s θ → Differentiable ℂ θ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.isFn_differentiable | exact GlobalTheory.CompanionTheory.Ar.Sl.isFn_differentiable | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.isFn_differentiable <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionArchimedeanFrame

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameEx

theorem exists_goodUnif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X)
    (z : Sp ℂ ⟶ X) (t' : SAB H (Sp ℂ)) (m : SABMap t' t z), IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L →
    IsAbelianScheme t'.G ∧ ∃ (g : ℕ) (u : HolUnif t'.G (t.PP.L.pull m.φ) g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
      u.IsAH Hm χ ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) := by
  intro E _ _ _ H X t z t' m hP hA
  have hab : IsAbelianScheme t'.G := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ t'.G hab
  obtain ⟨u₀, hc⟩ := GlobalTheory.T.exists_exp_chart_coordinates t'.G t'.PP.L g hab hA hg
  obtain ⟨u, Hm, χ, hex, hH, hχ, hlaw⟩ := GlobalTheory.T.theta_multiplier_normal_form t'.G t'.PP t'.cub g u₀
  obtain ⟨N, J, Θ, hN, hd, hq, hne, hsep⟩ := GlobalTheory.T.exists_theta_basis_of_factor t'.G t'.PP.L g u Hm χ t'.PP.isLB hab hA hlaw
  have hpos := GlobalTheory.T.theta_functions_finite_dim g u.Λ u.discrete u.full Hm χ N J Θ hH hχ hN hd hq hne hsep
  have hAH : u.IsAH Hm χ := ⟨hH, hpos, hχ, hlaw⟩
  obtain ⟨ht₁, ht₂⟩ := @GlobalTheory.TangentOrigin.tangent_bijection_of_values @GlobalTheory.valAt'_rules t'.G _ t'.PP.L g u
    (by simpa only [hex] using hc)
  obtain ⟨w₀, hw₀, -⟩ := m.lin
  have hL := t'.PP.isLB
  have hM := pull_isLB t.PP.isLB m.φ
  exact ⟨hab, g, GlobalTheory.ArchMetricCompare.carry u hL hM hw₀, Hm, χ, GlobalTheory.ArchMetricCompare.carry_isAH hL hM hw₀ hAH, ht₁, ht₂⟩

end GlobalTheory.CompanionTheory.Ar.Sl.FrameEx


open GlobalTheory.CompanionTheory.Ar.Sl.FrameEx in
theorem GlobalTheory.CompanionTheory.Ar.Sl.frames_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ), Nonempty (D.Frame σ) ∧ ∀ a : D.Frame σ, (∀ (n : ℕ) (s : Out.H0 D.t.PP.L n), ∃! θ, a.IsFn s θ) ∧ (∀ (n : ℕ) (s : Out.H0 D.t.PP.L n) θ, a.IsFn s θ → a.IsTheta n θ) ∧ ∀ x : D.B.carrier, (∃! c, D.IsVec a x c) ∧ ∀ c, D.IsVec a x c → D.len σ x ^ 2 = Real.pi * (a.herm c c).re ∧ (x ≠ 0 → c ≠ 0) := by
  intro E _ _ _ H L _ _ D σ
  obtain ⟨t', m, hP, hA⟩ := GlobalTheory.T.complex_abelian_fibre_ample E H L D σ
  obtain ⟨hab, g, u, Hm, χ, hAH, d₁, d₂⟩ := exists_goodUnif E H _ D.t (emb σ) t' m hP hA
  have hcart : IsGrpPullback t'.G D.t.G (emb σ) m.φ := m.cart
  have hg : D.g = g := GlobalTheory.T.uniformization_dim_eq_pp_dim E H L D σ t'.G m.φ _ g u hcart d₁ d₂
  subst hg
  refine ⟨GlobalTheory.T.exists_archimedean_frame _ D.t.G D.t.PP (emb σ) t'.G m.φ D.g u Hm χ hcart hAH, fun a => ?_⟩
  obtain ⟨e, hmon, -⟩ := grpPullback_iso a.cart hcart
  haveI := hmon
  obtain ⟨a₁, a₂⟩ := GlobalTheory.T.uniformization_iso_transfer t'.G a.A _ _ D.g u a.u e hab d₁ d₂
  refine ⟨fun n s => GlobalTheory.T.theta_function_unique _ D.t.G D.t.PP (emb σ) D.g a n s,
    fun n s θ h => ⟨GlobalTheory.T.theta_function_differentiable _ D.t.G D.t.PP (emb σ) D.g a n s θ h,
      GlobalTheory.T.theta_add_lattice_eq_of_isFn _ D.t.G D.t.PP (emb σ) D.g a n s θ h⟩,
    fun x => ⟨GlobalTheory.T.frame_coordinates_unique E H L D σ a a₁ a₂ x, fun c hc => ?_⟩⟩
  have hl := GlobalTheory.T.archimedean_frame_of_pullback E H L D σ t'.G m.φ D.g u Hm χ hab hcart d₁ d₂ hAH a x c hc
  exact ⟨hl, GlobalTheory.T.nonzero_coords_of_nonzero_vector E H L D σ a x c hl⟩

end
end
end
