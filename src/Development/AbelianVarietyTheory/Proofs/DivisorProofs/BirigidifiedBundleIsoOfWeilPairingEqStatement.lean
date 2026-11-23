module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreExponentialKernelFullLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicUniformisationOfExponentialLatt
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoSymmetricBirigidifiedComplStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsAddOfFactorProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoOfSameFactor
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealEqOfExpNegTwoPiIDivEqStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqExpRiemannFormAppellHumbertFrame
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELObjectOfPrimitivePeriodMapUniformised
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Mathlib.Tactic.Basify
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicUniformisationOfExponentialLattStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
open GlobalTheory.PELU

theorem _root_.GlobalTheory.T.exists_holomorphic_uniformisation_of_exponential_lattice : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A))
    (Λ : Submodule ℤ (Fin g → ℂ)), IsExp (𝟙 (Sp ℂ)) e → DiscreteTopology Λ →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z, e z = 1 ↔ z ∈ Λ) →
    ∃ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g), u₀.ex = e := by
  first | exact @GlobalTheory.exists_holUnif_of_isExp | exact GlobalTheory.exists_holUnif_of_isExp | (intros; apply GlobalTheory.exists_holUnif_of_isExp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEqOfImDotProductMulVecStarEqOnSpan

section

@[expose] public section

open scoped Matrix

namespace GlobalTheory

theorem matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span :
    ∀ (g : ℕ) (H H' : Matrix (Fin g) (Fin g) ℂ) (S : Set (Fin g → ℂ)),
    Submodule.span ℝ S = ⊤ →
    (∀ a ∈ S, ∀ b ∈ S, (a ⬝ᵥ H.mulVec (star b)).im = (a ⬝ᵥ H'.mulVec (star b)).im) → H = H' := by
  intro g H H' S hS h
  set D := H - H' with hD
  have hS0 : ∀ a ∈ S, ∀ b ∈ S, (a ⬝ᵥ D.mulVec (star b)).im = 0 := by
    intro a ha b hb
    simp only [hD, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im, h a ha b hb, sub_self]
  let B : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun a b => (a ⬝ᵥ D.mulVec (star b)).im)
      (by intro a a' b; simp [add_dotProduct])
      (by intro r a b; simp [smul_dotProduct])
      (by intro a b b'; simp [star_add, Matrix.mulVec_add, dotProduct_add])
      (by intro r a b; simp [star_smul, Matrix.mulVec_smul, dotProduct_smul])
  have hB : B = 0 := by
    apply LinearMap.ext_on hS
    intro a ha
    apply LinearMap.ext_on hS
    intro b hb
    simpa [B] using hS0 a ha b hb
  have hall : ∀ a b, (a ⬝ᵥ D.mulVec (star b)) = 0 := by
    intro a b
    have h1 : (a ⬝ᵥ D.mulVec (star b)).im = 0 := by
      have := congrArg (fun f => f a b) hB
      simpa [B] using this
    have h2 : ((Complex.I • a) ⬝ᵥ D.mulVec (star b)).im = 0 := by
      have := congrArg (fun f => f (Complex.I • a) b) hB
      simpa [B] using this
    rw [smul_dotProduct, smul_eq_mul, Complex.mul_im] at h2
    simp at h2
    exact Complex.ext h2 h1
  have hDz : D = 0 := by
    ext i j
    have := hall (Pi.single i 1) (Pi.single j 1)
    simpa [Matrix.mulVec_single_one, Pi.star_single] using this
  exact sub_eq_zero.mp hDz

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEqOfImDotProductMulVecStarEqOnSpanStatement

section

@[expose] public section

open scoped Matrix

theorem _root_.GlobalTheory.T.matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span' : ∀ (g : ℕ) (H H' : Matrix (Fin g) (Fin g) ℂ) (S : Set (Fin g → ℂ)),
    Submodule.span ℝ S = ⊤ →
    (∀ a ∈ S, ∀ b ∈ S, (a ⬝ᵥ H.mulVec (star b)).im = (a ⬝ᵥ H'.mulVec (star b)).im) → H = H' := by
  first | exact @GlobalTheory.matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span | exact GlobalTheory.matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span | (intros; apply GlobalTheory.matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoOfSameAppellHumbertForm

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory


open GlobalTheory.TorusRM.LamAdd GlobalTheory.ProdUnifSq in
theorem GlobalTheory.TorusRM.lbIso_lam_of_same_form : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M M' : LB A.left) (u : HolUnif A M g) (u' : HolUnif A M' g) (Hm : Matrix (Fin g) (Fin g) ℂ)
      (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ), M.IsLB → M'.IsLB → u'.ex = u.ex →
    GlobalTheory.TorusRM.IsFactorAH u Hm χ → GlobalTheory.TorusRM.IsFactorAH u' Hm χ' → LBIso (abelian₂ A M) (abelian₂ A M') := by
  intro g A _ hA hP M M' u u' Hm χ χ' h1 h2 he f1 f2
  haveI : IsCommMonObj A := hA.comm
  have hl1 : (abelian₂ A M).IsLB := LB.isLB_linComb h1 _ _
  have hl2 : (abelian₂ A M').IsLB := LB.isLB_linComb h2 _ _
  have hPP : IsProjOver (A ⊗ A).hom := GlobalTheory.ProjSpace.isProjOver_pullback hP hP
  refine GlobalTheory.HolUnifSec.hasGen_of_periodic (A ⊗ A) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) hPP _
    (LB.isLB_div hl2 hl1) (g + g)
    (GlobalTheory.SameFactor.divUnif (lamUnif u u rfl) (lamUnif u u' he) rfl)
    (fun _ => 1) (differentiable_const _) (fun _ => one_ne_zero) ?_
  intro l hl p z hz
  obtain ⟨hz2, hz1⟩ := (GlobalTheory.top_le_preimage_inf _ _ _).1 hz
  have hexl : (sqUnif A u).ex (z + l) = (sqUnif A u).ex z := by
    rw [(sqUnif A u).ex_add, ((sqUnif A u).ker l).2 hl, _root_.mul_one]
  have e1 := lam_shift u u rfl h1 f1 p.2 z l hl hz1
  have e2 := lam_shift u u' he h2 f2 p.1 z l hl hz2
  have n1 := (lamUnif u u rfl).fr_ne p.2 (z + l) (by rw [lamUnif_ex, hexl]; exact hz1)
  have n2 := (lamUnif u u' he).fr_ne p.1 (z + l) (by rw [lamUnif_ex, hexl]; exact hz2)
  show 1 * ((lamUnif u u' he).fr p.1 (z + l) * ((lamUnif u u rfl).fr p.2 (z + l))⁻¹) =
    1 * ((lamUnif u u' he).fr p.1 z * ((lamUnif u u rfl).fr p.2 z)⁻¹)
  rw [e1, e2]
  have q1 := Complex.exp_ne_zero (Q Hm z l)
  field_simp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoOfSameAppellHumbertFormStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem _root_.GlobalTheory.T.mumfordBundleIso_of_same_appellHumbert_form : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M M' : LB A.left) (u : HolUnif A M g) (u' : HolUnif A M' g) (Hm : Matrix (Fin g) (Fin g) ℂ)
      (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ), M.IsLB → M'.IsLB → u'.ex = u.ex →
    GlobalTheory.TorusRM.IsFactorAH u Hm χ → GlobalTheory.TorusRM.IsFactorAH u' Hm χ' → LBIso (abelian₂ A M) (abelian₂ A M') := by
  first | exact @GlobalTheory.TorusRM.lbIso_lam_of_same_form | exact GlobalTheory.TorusRM.lbIso_lam_of_same_form | (intros; apply GlobalTheory.TorusRM.lbIso_lam_of_same_form <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqExpRiemannFormAppellHumbertFrameStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem _root_.GlobalTheory.T.weilPairing_eq_exp_riemannForm_appellHumbert_frame : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left), L.IsLB →
    ∀ (n : ℕ) (u : HolUnif A L n) (Hm : Matrix (Fin n) (Fin n) ℂ) (χ : u.Λ → ℂ), GlobalTheory.TorusRM.IsFactorAH u Hm χ →
      ∀ (k : ℕ) (a b : Fin n → ℂ) (c : ℂˣ), 0 < k → a ∈ u.Λ → b ∈ u.Λ →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((a ⬝ᵥ Hm.mulVec (star b)).im : ℝ) : ℂ) / k) →
        Out.WeilIs A L k (u.ex ((k : ℂ)⁻¹ • a)) (u.ex ((k : ℂ)⁻¹ • b)) (unitOn c) := by
  first | exact @GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm | exact GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm | (intros; apply GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleIsoOfWeilPairingEq

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem GlobalTheory.biIso_of_weil : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P P' : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → P'.IsLB → (∃ t : (P'.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd A A) (fst A A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P'.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → LBIso P P' := by
  intro A _ _ g hA hs P P' hP hP1 hP2 hPs hP' hP'1 hP'2 hP's e La _ Q EF he hQ hker hW hW'
  obtain ⟨Λ, hd, hf, hk⟩ := GlobalTheory.T.complexFibreExponential_kernel_full_lattice (Sp ℂ) A g hA hs (𝟙 _) e he
  obtain ⟨L₀, u₀, hu₀⟩ := GlobalTheory.T.exists_holomorphic_uniformisation_of_exponential_lattice A g e Λ he hd hf hk
  obtain ⟨M, hM, hPM⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hs P hP hP1 hP2 hPs
  obtain ⟨M', hM', hPM'⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hs P' hP' hP'1 hP'2 hP's
  obtain ⟨u, Hm, χ, hue, hF⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M hM
  obtain ⟨u', Hm', χ', hue', hF'⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M' hM'
  have hp : IsProjOver A.hom := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  have hL : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hL' : (abelian₂ A M').IsLB := LB.isLB_linComb hM' _ _

  have key : ∀ (M : LB A.left) (P : LB (G2 A).left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ)
      (χ : u.Λ → ℂ), M.IsLB → P.IsLB → u.ex = e → GlobalTheory.TorusRM.IsFactorAH u Hm χ →
      LBIso P (cubeLB A ![fst A A, snd A A] M) →
      (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k →
        (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
        Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) →
      ∀ a b : La, ((Q a) ⬝ᵥ ((2 : ℂ) • Hm).mulVec (star (Q b))).im = (EF a b : ℝ) := by
    intro M P u Hm χ hM hP hue hF hPM hW a b
    have hLM : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
    obtain ⟨ud, χd, hude, hFd⟩ := GlobalTheory.TorusRM.exists_isFactorAH_lam_diag g A hA M u Hm χ hM hF
    have mem : ∀ x : La, Q x ∈ ud.Λ := fun x => (ud.ker _).1 (by rw [hude, hue]; exact (hker _).2 ⟨x, rfl⟩)
    refine GlobalTheory.T.eq_of_forall_cexp_neg_two_pi_I_mul_div_eq _ _ fun k hk => ?_
    have h1 := hW k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have h2 := GlobalTheory.T.weilPairing_eq_exp_riemannForm_appellHumbert_frame A hA _ (pull_isLB hLM _) g ud _ χd hFd k (Q a) (Q b)
      (Units.mk0 _ (Complex.exp_ne_zero _)) hk (mem a) (mem b) rfl
    rw [hude, hue] at h2
    have hiso : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left)
        (((abelian₂ A M).pull (lift (𝟙 A) (𝟙 A)).left).pull (𝟙 A : A ⟶ A).left) := by
      refine LBIso.trans (pull_isLB hP _) (pull_isLB hLM _) (pull_isLB (pull_isLB hLM _) _)
        (GlobalTheory.RigidBundleGlue.LBIso.pull hPM _) ?_
      exact GlobalTheory.ThetaAffineGlue.lbIso_pull_id (pull_isLB hLM _)
    have h3 := GlobalTheory.PeriodObject.weilIs_of_lbIso GlobalTheory.globalFns_holds hA (pull_isLB hP _)
      (pull_isLB hLM _) hiso h2
    have := GlobalTheory.weilIs_unique_fieldPoint (Sp ℂ) A _ (pull_isLB hP _) ℂ (𝟙 _) k _ _ _ _ h1 h3
    have := congrArg Units.val this
    simpa using this.symm
  have hH : Hm = Hm' := by
    have e2 := GlobalTheory.T.matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span' g ((2 : ℂ) • Hm) ((2 : ℂ) • Hm') (Set.range Q) ?_ ?_
    · have := congrArg (fun X => (1 / 2 : ℂ) • X) e2
      simpa [smul_smul] using this
    · have hR : Set.range Q = (Λ : Set (Fin g → ℂ)) := by
        ext z
        rw [SetLike.mem_coe, ← hk, hker]
        rfl
      rw [hR]; exact hf
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [key M P u Hm χ hM hP (hue.trans hu₀) hF hPM hW a b,
        key M' P' u' Hm' χ' hM' hP' (hue'.trans hu₀) hF' hPM' hW' a b]
  subst hH
  have hlam := GlobalTheory.T.mumfordBundleIso_of_same_appellHumbert_form g A hA hp M M' u u' Hm χ χ' hM hM' (hue'.trans hue.symm) hF hF'
  exact LBIso.trans hP hL hP' hPM (LBIso.trans hL hL' hP' hlam (LBIso.symm hPM'))
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleIsoOfWeilPairingEqStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.birigidified_bundle_iso_of_weil_pairing_eq : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P P' : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → P'.IsLB → (∃ t : (P'.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd A A) (fst A A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P'.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → LBIso P P' := by
  first | exact @GlobalTheory.biIso_of_weil | exact GlobalTheory.biIso_of_weil | (intros; apply GlobalTheory.biIso_of_weil <;> assumption)
end
end
