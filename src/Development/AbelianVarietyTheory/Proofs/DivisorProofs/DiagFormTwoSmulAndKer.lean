module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorOfHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfExponential
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfLineBundleIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoSymmetricBirigidifiedComplStatement
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierTrivialization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierIntegralImaginary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierTrivialization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingComplexValueUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsRapoportOfBasis
import Mathlib.Tactic.Basify
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertDiagonalReal

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM
open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RiemInt

open GlobalTheory.AppellHumbertTrivial

theorem im_hermForm_int {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (hL : L.IsLB) (u : HolUnif A L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : IsFactorAH u Hm χ) (l m : u.Λ) :
    ∃ n : ℤ, (hermForm Hm l m).im = n := by
  have hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex 0).left hL
  have hil : ⊤ ≤ (u.ex (0 + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have him : ⊤ ≤ (u.ex (0 + m)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have hlm : ⊤ ≤ (u.ex (0 + l + m)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have h1 := h.2.2 l i 0 hi
  have h2 := h.2.2 m i _ hil
  have h3 := h.2.2 m i 0 hi
  have h4 := h.2.2 l i _ him
  have hne := u.fr_ne i _ hlm
  have hs : hermForm Hm m l = star (hermForm Hm l m) := by
    unfold hermForm
    rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, h.1.eq, Matrix.dotProduct_mulVec]
  have hχl : χ l ≠ 0 := norm_ne_zero_iff.1 (by rw [h.2.1]; exact one_ne_zero)
  have hχm : χ m ≠ 0 := norm_ne_zero_iff.1 (by rw [h.2.1]; exact one_ne_zero)
  rw [h2] at h1
  rw [h4, h1] at h3
  simp only [zero_add, zero_dotProduct, mul_zero] at h3 hne
  rw [add_comm (m : Fin g → ℂ) l] at h3
  unfold hermForm at hs ⊢
  rw [hs] at h3
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)) = a at h3
  generalize (m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = b at h3
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = c at h3 ⊢
  simp only [Complex.exp_add] at h3
  have he : Complex.exp (Real.pi * c) = Complex.exp (Real.pi * star c) := by
    refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hχl hχm)
      (Complex.exp_ne_zero (Real.pi / 2 * a))) (Complex.exp_ne_zero (Real.pi / 2 * b))) hne) ?_
    linear_combination h3
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  have hp := Real.pi_pos
  refine mul_left_cancel₀ (a := 2 * Real.pi) (by positivity) ?_
  linear_combination this

variable {g : ℕ}

end GlobalTheory.RiemInt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfComplexExponential

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.ExpUnifAH

theorem exists_unif_isFactorAH_of_isExp : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (M : LB A.left), M.IsLB → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsExp (𝟙 (Sp ℂ)) e → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), (∀ z, u.ex z = e z) ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  intro A _ _ g hA hg M hM e he
  exact GlobalTheory.ExpFrame.exists_isFactorAH_frame_of_isExp A g hA hg e he M hM

end GlobalTheory.ExpUnifAH
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfComplexExponentialStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_appellHumbertFrame_of_complexExponential : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (M : LB A.left), M.IsLB → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsExp (𝟙 (Sp ℂ)) e → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), (∀ z, u.ex z = e z) ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  first | exact @GlobalTheory.ExpUnifAH.exists_unif_isFactorAH_of_isExp | exact GlobalTheory.ExpUnifAH.exists_unif_isFactorAH_of_isExp | (intros; apply GlobalTheory.ExpUnifAH.exists_unif_isFactorAH_of_isExp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackTrivialOfImFormInt

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

namespace GlobalTheory.TorusRM.KerTriv

open GlobalTheory.TorusRM.TransFrame

theorem dot_herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (a b : Fin g → ℂ) :
    a ⬝ᵥ Hm *ᵥ star b = star (b ⬝ᵥ Hm *ᵥ star a) := by
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH.apply i j, star_star]
  ring

theorem exp_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (w l : Fin g → ℂ) (n : ℤ)
    (hn : (w ⬝ᵥ Hm *ᵥ star l).im = n) :
    Complex.exp (Real.pi * (l ⬝ᵥ Hm *ᵥ star w)) = Complex.exp (Real.pi * (w ⬝ᵥ Hm *ᵥ star l)) := by
  rw [dot_herm_swap hH l w]
  set a := w ⬝ᵥ Hm *ᵥ star l
  have e : (star a : ℂ) = a + (-n : ℤ) * (2 * Complex.I) := by
    apply Complex.ext <;> simp [hn, Complex.conj_re, Complex.conj_im] <;> ring
  rw [e, mul_add, Complex.exp_add]
  have : (Real.pi : ℂ) * ((-n : ℤ) * (2 * Complex.I)) = ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I, _root_.mul_one]

end GlobalTheory.TorusRM.KerTriv


open GlobalTheory.TorusRM.TransFrame GlobalTheory.TorusRM.KerTriv in
theorem GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ w : Fin g → ℂ, (∀ l ∈ u.Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n) → ∃ t : ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left).Gen, t.IsGen := by
  intro A _ _ g hA M u Hm χ hM hF w hw
  have hp : IsProjOver A.hom :=
    (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1 (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  have hL : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hL' : ((abelian₂ A M).pull (pairRight (u.ex w)).left).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨t, ht⟩ := GlobalTheory.HolUnifSec.hasGen_of_periodic A hA hp _ hL' g (transUnif u w)
    (fun z => Complex.exp (Real.pi * (z ⬝ᵥ Hm *ᵥ star w))) (by
      have hd : Differentiable ℂ (fun z : Fin g → ℂ => z ⬝ᵥ Hm *ᵥ star w) := by
        simp only [dotProduct]; fun_prop
      exact ((differentiable_const _).mul hd).cexp) (fun z => Complex.exp_ne_zero _) (by
      intro l hl i z hz
      obtain ⟨n, hn⟩ := hw l hl
      rw [transUnif_factor u hF w ⟨l, hl⟩ i z hz, add_dotProduct, mul_add, Complex.exp_add,
        exp_swap hF.1 w l n hn]
      ring)
  have hρ : fst A (𝟙_ (Over (Sp ℂ))) ≫ pairRight (u.ex w) =
      lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w) := by
    simp only [pairRight, comp_lift, Category.comp_id]
    rw [← Category.assoc, toUnit_unique (fst A (𝟙_ (Over (Sp ℂ))) ≫ toUnit A) (snd A (𝟙_ (Over (Sp ℂ))))]
  have key : (fun _ : PUnit => (fst A (𝟙_ (Over (Sp ℂ)))).left ≫ (pairRight (u.ex w)).left) =
      (fun _ : PUnit => (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left) := by
    funext _
    rw [← Over.comp_left, hρ]
  have H : ∃ t : (LB.LinComb (abelian₂ A M) (fun _ : PUnit => (fst A (𝟙_ (Over (Sp ℂ)))).left ≫
      (pairRight (u.ex w)).left) (fun _ => 1)).Gen, t.IsGen :=
    ⟨_, ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen (abelian₂ A M) _ _ t ht (fst A (𝟙_ (Over (Sp ℂ)))).left⟩
  rw [key] at H
  exact H
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackTrivialOfImFormIntStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem _root_.GlobalTheory.T.mumfordBundle_pullback_trivial_of_im_form_int : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ w : Fin g → ℂ, (∀ l ∈ u.Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n) → ∃ t : ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex w)).left).Gen, t.IsGen := by
  first | exact @GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int | exact GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int | (intros; apply GlobalTheory.TorusRM.hasGen_lam_pull_of_im_int <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFormTwoSmulAndKer

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT


open GlobalTheory.CechPic in
theorem GlobalTheory.SymBirig.diag_form_two_smul_and_ker : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → ∃ E₁ : LinearMap.BilinForm ℤ La, EF = (2 : ℤ) • E₁ ∧ ∀ (k : ℕ) (a : La), 0 < k → ((∀ y, (k : ℤ) ∣ E₁ a y) ↔ ∃ t : (P.pull (lift (snd A (Over.mk (𝟙 (Sp ℂ))) ≫ e ((k : ℂ)⁻¹ • Q a)) (fst A (Over.mk (𝟙 (Sp ℂ))))).left).Gen, t.IsGen) := by
  intro A _ _ g hA hg P hP h1 h2 hsym hamp e La _ Q EF hexp hQ hker hW
  obtain ⟨M, hM, hPM⟩ := GlobalTheory.T.exists_mumford_bundle_iso_symmetric_birigidified_complex A g hA hg P hP h1 h2 hsym
  have hPM' : LBIso P (abelian₂ A M) := hPM
  obtain ⟨u, Hm, χ, hue, hF⟩ := GlobalTheory.T.exists_appellHumbertFrame_of_complexExponential A g hA hg M hM e hexp
  obtain ⟨u', χ', hue', hF'⟩ := GlobalTheory.TorusRM.exists_isFactorAH_lam_diag g A hA M u Hm χ hM hF
  have hlam : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  have hD := GlobalTheory.GenSpread.lbIso_pullback hPM' (lift (𝟙 A) (𝟙 A)).left
  obtain ⟨v, ψ, hve, hFv⟩ := GlobalTheory.T.exists_appellHumbertFrame_of_lineBundleIso A g _ _ u' _ χ' (pull_isLB hP _) (pull_isLB hlam _) hD hF'
  have hpos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple A hA _ (pull_isLB hP _) hamp g v _ ψ hFv.1 hFv.2.1 hFv.2.2
  have hAH := GlobalTheory.TorusRM.isAH_of_isFactorAH hFv hpos
  have hmemu : ∀ z, z ∈ u.Λ ↔ z ∈ Q.range := fun z => by rw [← u.ker, hue]; exact hker z
  have hmemv : ∀ z, z ∈ v.Λ ↔ z ∈ Q.range := fun z => by rw [← v.ker, hve, hue', hue]; exact hker z
  have hvx : ∀ z, v.ex z = e z := fun z => by rw [hve, hue', hue]
  have hNex : ∀ a b : La, ∃ n : ℤ, (hermForm Hm (Q a) (Q b)).im = n := fun a b =>
    GlobalTheory.RiemInt.im_hermForm_int hM u hF ⟨Q a, (hmemu _).2 ⟨a, rfl⟩⟩ ⟨Q b, (hmemu _).2 ⟨b, rfl⟩⟩
  choose N hN using hNex
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have key : ∀ a b : La, EF a b = 2 * N a b := by
    intro a b
    have hk : ∀ k : ℕ, 0 < k → ∃ n : ℤ, ((EF a b : ℂ) - 2 * N a b) / k = n := by
      intro k hk
      let c₁ : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k)) (Complex.exp_ne_zero _)
      let c₂ : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) *
        (((Q a ⬝ᵥ ((2 : ℂ) • Hm) *ᵥ star (Q b)).im : ℝ) : ℂ) / k)) (Complex.exp_ne_zero _)
      have w1 := hW k a b c₁ hk rfl
      have w2 := GlobalTheory.AHWeilAny.weilIs_exp_riemannForm A hA _ (pull_isLB hP _) g v _ ψ hAH k (Q a) (Q b) c₂ hk
        ((hmemv _).2 ⟨a, rfl⟩) ((hmemv _).2 ⟨b, rfl⟩) rfl
      rw [hvx, hvx] at w2
      have h3 := congrArg (fun c : ℂˣ => (c : ℂ)) (GlobalTheory.T.weilPairing_complex_value_unique (Sp ℂ) A g hA hg _ (pull_isLB hP _) (𝟙 (Sp ℂ)) k _ _ c₁ c₂ w1 w2)
      simp only [c₁, c₂, Units.val_mk0] at h3
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h3
      have h2 : ((Q a ⬝ᵥ ((2 : ℂ) • Hm) *ᵥ star (Q b)).im) = 2 * (N a b : ℝ) := by
        have h4 := hN a b
        unfold hermForm at h4
        have h5 : ((2 : ℂ) • Hm) *ᵥ star (Q b) = (2 : ℂ) • (Hm *ᵥ star (Q b)) := by
          rw [Matrix.smul_mulVec]
        rw [h5, dotProduct_smul, smul_eq_mul, Complex.mul_im, h4]
        simp
      rw [h2] at hn
      refine ⟨-n, mul_left_cancel₀ hpi ?_⟩
      push_cast at hn ⊢
      linear_combination (-1 : ℂ) * hn
    obtain ⟨K, hK⟩ : ∃ K : ℕ, K = (EF a b - 2 * N a b).natAbs + 1 := ⟨_, rfl⟩
    obtain ⟨n, hn⟩ := hk K (by omega)
    have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
    rw [div_eq_iff hK0] at hn
    have e2 : EF a b - 2 * N a b = (K : ℤ) * n := Int.cast_injective (α := ℂ) (by push_cast; rw [hn]; ring)
    have e3 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨n, e2⟩ (by rw [Int.natAbs_natCast]; omega)
    omega
  have hadd : ∀ a a' b, N (a + a') b = N a b + N a' b := by
    intro a a' b
    have h := key (a + a') b
    rw [map_add (f := _), LinearMap.add_apply, key, key] at h
    omega
  have hadd' : ∀ a b b', N a (b + b') = N a b + N a b' := by
    intro a b b'
    have h := key a (b + b')
    rw [map_add (f := _), key, key] at h
    omega
  have hsm : ∀ (c : ℤ) a b, N (c • a) b = c * N a b := by
    intro c a b
    have h := key (c • a) b
    rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul, key] at h
    have h' : 2 * (N (c • a) b - c * N a b) = 0 := by linear_combination -h
    linear_combination (mul_eq_zero.1 h').resolve_left two_ne_zero
  have hsm' : ∀ (c : ℤ) a b, N a (c • b) = c * N a b := by
    intro c a b
    have h := key a (c • b)
    rw [map_zsmul, smul_eq_mul, key] at h
    have h' : 2 * (N a (c • b) - c * N a b) = 0 := by linear_combination -h
    linear_combination (mul_eq_zero.1 h').resolve_left two_ne_zero
  refine ⟨LinearMap.mk₂ ℤ N hadd (fun c a b => by rw [hsm, smul_eq_mul]) hadd' (fun c a b => by rw [hsm', smul_eq_mul]), ?_, ?_⟩
  · ext a b
    simp [key]
  · intro k a hk
    simp only [LinearMap.mk₂_apply]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hwl : ∀ y, (((k : ℂ)⁻¹ • Q a) ⬝ᵥ Hm *ᵥ star (Q y)).im = (N a y : ℝ) / k := by
      intro y
      have h4 := hN a y
      unfold hermForm at h4
      rw [smul_dotProduct, smul_eq_mul, show ((k : ℂ)⁻¹) = (((k : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
        Complex.im_ofReal_mul, h4, div_eq_inv_mul]
    have stepA : (∀ y, (k : ℤ) ∣ N a y) ↔
        ∀ l ∈ u.Λ, ∃ n : ℤ, (((k : ℂ)⁻¹ • Q a) ⬝ᵥ Hm.mulVec (star l)).im = n := by
      constructor
      · rintro h l hl
        obtain ⟨y, rfl⟩ := (hmemu l).1 hl
        obtain ⟨n, hn⟩ := h y
        exact ⟨n, by rw [hwl, hn]; push_cast; field_simp⟩
      · intro h y
        obtain ⟨n, hn⟩ := h (Q y) ((hmemu _).2 ⟨y, rfl⟩)
        rw [hwl, div_eq_iff hk0] at hn
        exact ⟨n, by exact_mod_cast (show (N a y : ℝ) = (k : ℝ) * n by rw [hn]; ring)⟩
    have stepB := (show _ ↔ _ from ⟨GlobalTheory.T.mumfordBundle_pullback_trivial_of_im_form_int A g hA M u Hm χ hM hF ((k : ℂ)⁻¹ • Q a), fun h => by
      obtain ⟨θ, hθ, h0, hp⟩ := GlobalTheory.TorusRM.exists_theta_of_hasGen_lam_pull g A hA M u Hm χ hM hF _ h
      exact GlobalTheory.ThetaLiouville.im_form_mem_int g u.Λ u.full Hm hF.1 _ θ hθ h0 hp⟩)
    refine stepA.trans (stepB.trans ?_)
    have c1 := GlobalTheory.RealMult.Elliptic.cls_pull_lam hM (fst A (𝟙_ (Over (Sp ℂ))))
      (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex ((k : ℂ)⁻¹ • Q a)) (pull_isLB hlam _)
    have c2 := GlobalTheory.RealMult.Elliptic.cls_pull_lam hM (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex ((k : ℂ)⁻¹ • Q a))
      (fst A (𝟙_ (Over (Sp ℂ)))) (pull_isLB hlam _)
    have c3 : cls (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex ((k : ℂ)⁻¹ • Q a)) (fst A (𝟙_ (Over (Sp ℂ))))).left)
        (pull_isLB hP _) = cls ((abelian₂ A M).pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ u.ex ((k : ℂ)⁻¹ • Q a))
          (fst A (𝟙_ (Over (Sp ℂ))))).left) (pull_isLB hlam _) := by
      rw [cls_pull hP, cls_pull hlam, (cls_eq_iff hP hlam).2 hPM']
    rw [← cls_eq_zero_iff (pull_isLB hlam _), c1, lam_comm, ← c2, ← c3, cls_eq_zero_iff, hue]
    exact Iff.rfl
end
end
