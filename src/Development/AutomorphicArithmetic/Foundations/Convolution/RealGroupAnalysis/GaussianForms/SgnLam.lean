module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.LamFour
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.LamGen
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.LamReal
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.SplitA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.LamOne

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.lamOne :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (g : FiniteAdeleRing (𝓞 F) F → ℂ), ∃ C : FiniteAdeleRing (𝓞 F) F → ℂ, ∀ b : (A F)ˣ, Lam1 (b : A F) (g1 g) = C (b : A F).2 * ∏ w, lamR (TR.pInf F (b : A F) w) := by
  intro F _ _ _ g
  obtain ⟨⟨e, c, he, hmap⟩, hψ⟩ := splitA F
  refine ⟨fun β => ((c.toReal : ℝ) : ℂ) ^ 2 * abelian₂ (finiteAdeleMeasure F)
    (fun x => ((finiteAdelicChar F (β * x ^ 2) : Circle) : ℂ)) g, fun b => ?_⟩
  have hne : ∀ w, TR.pInf F (b : A F) w ≠ 0 := by
    intro w h0
    have h1 : TR.pInf F (b : A F) * TR.pInf F ((b⁻¹ : (A F)ˣ) : A F) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 := congrFun h1 w
    rw [Pi.mul_apply, h0, zero_mul] at h2
    exact zero_ne_one h2
  let γi : InfinitePlace F → ℝ → ℂ := fun w x =>
    Complex.exp (-(2 * Real.pi * Complex.I) * ((TR.pInf F (b : A F) w : ℝ) : ℂ) * (x : ℂ) ^ 2)
  let φi : InfinitePlace F → ℝ → ℂ := fun _ x => Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)
  let γf : FiniteAdeleRing (𝓞 F) F → ℂ := fun x => ((finiteAdelicChar F ((b : A F).2 * x ^ 2) : Circle) : ℂ)
  have hadd : ∀ x y, e (x + y) = e x + e y := by
    intro x y
    simp only [he, map_add (f := _)]
    rfl
  have h3 := (lamGen.2.2 (A F) ((InfinitePlace F → ℝ) × FiniteAdeleRing (𝓞 F) F) (adeleMeasure F) _ e c hadd hmap
    (fun p => (∏ w, γi w (p.1 w)) * γf p.2) (fun p => (∏ w, φi w (p.1 w)) * g p.2)).1
  have h1 := lamGen.1 (InfinitePlace F → ℝ) (FiniteAdeleRing (𝓞 F) F) volume (finiteAdeleMeasure F)
    (fun v => ∏ w, γi w (v w)) (fun v => ∏ w, φi w (v w)) γf g
  have h2 := lamGen.2.1 (InfinitePlace F) ℝ volume γi φi
  have h4 : ∀ w, abelian₂ (volume : Measure ℝ) (γi w) (φi w) = lamR (TR.pInf F (b : A F) w) :=
    fun w => lamReal _ (hne w)
  have hγ : (fun x : A F => ψ ((b : A F) * x ^ 2)) =
      fun x => (∏ w, γi w ((e x).1 w)) * γf (e x).2 := by
    funext x
    rw [hψ, he]
    congr 1
    · refine Finset.prod_congr rfl fun w _ => ?_
      have : TR.pInf F ((b : A F) * x ^ 2) w = TR.pInf F (b : A F) w * (TR.pInf F x w) ^ 2 := by
        rw [map_mul, map_pow]
        rfl
      simp only [γi]
      rw [this]
      push_cast
      ring_nf
  have hφ : g1 g = fun x : A F => (∏ w, φi w ((e x).1 w)) * g (e x).2 := by
    funext x
    rw [he]
    rfl
  have hL : Lam1 (b : A F) (g1 g) = abelian₂ (adeleMeasure F) (fun x : A F => ψ ((b : A F) * x ^ 2)) (g1 g) := rfl
  have hv : (volume : Measure (InfinitePlace F → ℝ)) = Measure.pi fun _ => volume := volume_pi
  rw [hL, hγ, hφ, h3, h1, hv, h2]
  simp only [h4]
  ring
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.SgnLam

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem lamR_quad (β r : ℝ) (hβ : β ≠ 0) (hr : 0 < r) :
    lamR (-β) * lamR β * lamR (-β) * lamR (-(r * β)) = -(lamR β * lamR (-β) * lamR β * lamR (r * β)) := by
  have h1 : |r * β| = r * |β| := by rw [abs_mul, abs_of_pos hr]
  have h2 : |r * -β| = r * |β| := by rw [abs_mul, abs_of_pos hr, abs_neg]
  have hs : ∀ x : ℝ, ((SignType.sign (r * x) : SignType) : ℂ) = ((SignType.sign x : SignType) : ℂ) := by
    intro x
    rw [sign_mul, sign_pos hr, one_mul]
  have hneg : ∀ x : ℝ, ((SignType.sign (-x) : SignType) : ℂ) = -((SignType.sign x : SignType) : ℂ) := by
    intro x
    rcases lt_trichotomy x 0 with h | h | h
    · simp [sign_neg h, sign_pos (neg_pos.2 h)]
    · simp [h]
    · simp [sign_pos h, sign_neg (neg_neg_of_pos h)]
  have hsq : ((SignType.sign β : SignType) : ℂ) ^ 2 = 1 := by
    rcases lt_or_gt_of_ne hβ with h | h
    · simp [sign_neg h]
    · simp [sign_pos h]
  unfold lamR
  rw [show -(r * β) = r * -β by ring, hs (-β), hs β, hneg β, h1, h2, abs_neg]
  generalize ((SignType.sign β : SignType) : ℂ) = s at hsq ⊢
  generalize ((2 * √|β| : ℝ) : ℂ) = D
  generalize ((2 * √(r * |β|) : ℝ) : ℂ) = D'
  have h : (1 - Complex.I * -s) * (1 - Complex.I * -s) = -((1 - Complex.I * s) * (1 - Complex.I * s)) := by
    linear_combination (2 * s ^ 2) * Complex.I_sq - 2 * hsq
  linear_combination ((1 - Complex.I * -s) * (1 - Complex.I * s) * D⁻¹ ^ 3 * D'⁻¹) * h

theorem UpperTheory.ConvolutionTheory.R2.C.sgnLam :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), (∀ φ : F →+* ℝ, φ δ < 0) → ∀ a b : (A F)ˣ, IsSgn a → ∀ g : FiniteAdeleRing (𝓞 F) F → ℂ,
    Lam4 δ ((a * b : (A F)ˣ) : A F) (four (g1 g)) = -Lam4 δ (b : A F) (four (g1 g)) := by
  intro F _ _ _ δ hδ a b ha g
  obtain ⟨ha2, w₀, haw⟩ := ha
  let e : F →+* ℝ := (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w₀).comp ((TR.pInf F).comp (algebraMap F (A F)))
  have he : TR.pInf F (rt δ) w₀ < 0 := hδ e
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have h0 := hδ e
    simp at h0
  obtain ⟨C, hC⟩ := lamOne F g
  let d : (A F)ˣ := Units.map (algebraMap F (A F)).toMonoidHom (Units.mk0 δ hδ0)
  have hd : (d : A F) = rt δ := rfl
  have key : ∀ c : (A F)ˣ, Lam4 δ (c : A F) (four (g1 g)) =
      (C (c : A F).2 * C ((-c : (A F)ˣ) : A F).2 * C (c : A F).2 * C ((-(d * c) : (A F)ˣ) : A F).2) *
      ∏ w, (lamR (TR.pInf F (c : A F) w) * lamR (-TR.pInf F (c : A F) w) * lamR (TR.pInf F (c : A F) w) *
        lamR (-(TR.pInf F (rt δ) w * TR.pInf F (c : A F) w))) := by
    intro c
    have h1 := hC c
    have h2 := hC (-c)
    have h3 := hC (-(d * c))
    have e2 : ((-c : (A F)ˣ) : A F) = -(c : A F) := Units.val_neg c
    have e3 : ((-(d * c) : (A F)ˣ) : A F) = -(rt δ * (c : A F)) := by
      rw [Units.val_neg, Units.val_mul, hd]
    rw [lamFour, ← e3, ← e2, h1, h2, h3, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have p2 : ∀ w, TR.pInf F ((-c : (A F)ˣ) : A F) w = -TR.pInf F (c : A F) w := by
      intro w; rw [e2, map_neg, Pi.neg_apply]
    have p3 : ∀ w, TR.pInf F ((-(d * c) : (A F)ˣ) : A F) w = -(TR.pInf F (rt δ) w * TR.pInf F (c : A F) w) := by
      intro w; rw [e3, map_neg, map_mul, Pi.neg_apply, Pi.mul_apply]
    simp only [p2, p3]
    ring
  have pm : ∀ w, TR.pInf F ((a * b : (A F)ˣ) : A F) w = TR.pInf F (a : A F) w * TR.pInf F (b : A F) w := by
    intro w; rw [Units.val_mul, map_mul, Pi.mul_apply]
  let pf : A F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
  have ha2' : pf (a : A F) = 1 := ha2
  have f0 : pf ((a * b : (A F)ˣ) : A F) = pf (b : A F) := by
    rw [Units.val_mul, map_mul, ha2', one_mul]
  have f1 : ((a * b : (A F)ˣ) : A F).2 = (b : A F).2 := f0
  have f2 : ((-(a * b) : (A F)ˣ) : A F).2 = ((-b : (A F)ˣ) : A F).2 := by
    have h : pf ((-(a * b) : (A F)ˣ) : A F) = pf ((-b : (A F)ˣ) : A F) := by
      rw [Units.val_neg, Units.val_neg, map_neg, map_neg, f0]
    exact h
  have f3 : ((-(d * (a * b)) : (A F)ˣ) : A F).2 = ((-(d * b) : (A F)ˣ) : A F).2 := by
    have h : pf ((-(d * (a * b)) : (A F)ˣ) : A F) = pf ((-(d * b) : (A F)ˣ) : A F) := by
      rw [Units.val_neg, Units.val_neg, map_neg, map_neg, Units.val_mul, Units.val_mul d b, map_mul, map_mul, f0]
    exact h
  have hβ : TR.pInf F (b : A F) w₀ ≠ 0 := by
    intro h0
    have h1 : TR.pInf F (b : A F) * TR.pInf F ((b⁻¹ : (A F)ˣ) : A F) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 := congrFun h1 w₀
    rw [Pi.mul_apply, h0, zero_mul] at h2
    exact zero_ne_one h2
  have hP : ∀ w ∈ Finset.univ.erase w₀,
      lamR (TR.pInf F ((a * b : (A F)ˣ) : A F) w) * lamR (-TR.pInf F ((a * b : (A F)ˣ) : A F) w) *
        lamR (TR.pInf F ((a * b : (A F)ˣ) : A F) w) *
        lamR (-(TR.pInf F (rt δ) w * TR.pInf F ((a * b : (A F)ˣ) : A F) w)) =
      lamR (TR.pInf F (b : A F) w) * lamR (-TR.pInf F (b : A F) w) * lamR (TR.pInf F (b : A F) w) *
        lamR (-(TR.pInf F (rt δ) w * TR.pInf F (b : A F) w)) := by
    intro w hw
    simp only [pm, haw, if_neg (Finset.ne_of_mem_erase hw), one_mul]
  have hq := lamR_quad (TR.pInf F (b : A F) w₀) (-TR.pInf F (rt δ) w₀) hβ (neg_pos.2 he)
  have h0 : lamR (TR.pInf F ((a * b : (A F)ˣ) : A F) w₀) * lamR (-TR.pInf F ((a * b : (A F)ˣ) : A F) w₀) *
        lamR (TR.pInf F ((a * b : (A F)ˣ) : A F) w₀) *
        lamR (-(TR.pInf F (rt δ) w₀ * TR.pInf F ((a * b : (A F)ˣ) : A F) w₀)) =
      -(lamR (TR.pInf F (b : A F) w₀) * lamR (-TR.pInf F (b : A F) w₀) * lamR (TR.pInf F (b : A F) w₀) *
        lamR (-(TR.pInf F (rt δ) w₀ * TR.pInf F (b : A F) w₀))) := by
    have t1 : TR.pInf F ((a * b : (A F)ˣ) : A F) w₀ = -TR.pInf F (b : A F) w₀ := by
      rw [pm, haw, if_pos rfl, neg_one_mul]
    rw [t1, neg_neg, show -(TR.pInf F (rt δ) w₀ * -TR.pInf F (b : A F) w₀) =
      -(-TR.pInf F (rt δ) w₀ * TR.pInf F (b : A F) w₀) by ring, hq, neg_mul]
  rw [key (a * b), key b, f1, f2, f3,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₀),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₀ : w₀ ∈ Finset.univ),
    Finset.prod_congr rfl hP, h0]
  ring
end
end
