module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CauchyRiemannIffDifferentiableOnComplex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorusEllipticSystemSolvableStatement
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PeriodicCechCocycleSmoothCoboundaryStatement
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.CauchyRiemannIffDifferentiableOnComplexStatement

section

@[expose] public section

open Complex Matrix
open scoped ContDiff BigOperators Real
theorem _root_.GlobalTheory.T.cauchyRiemann_iff_differentiableOn : ∀ (g : ℕ) (U : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → ℂ), IsOpen U → (DifferentiableOn ℝ f U → ((∀ a, ∀ z ∈ U, (fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))) = 0) ↔ DifferentiableOn ℂ f U)) ∧ (DifferentiableOn ℂ f U → ContDiffOn ℝ ∞ f U ∧ ∀ v, DifferentiableOn ℂ (fun z => fderiv ℂ f z v) U) := by
  first | exact @GlobalTheory.cauchyRiemann_iff_differentiableOn_complex | exact GlobalTheory.cauchyRiemann_iff_differentiableOn_complex | (intros; apply GlobalTheory.cauchyRiemann_iff_differentiableOn_complex <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.DbarSolveComplexTorus

section

@[expose] public section

open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

theorem exists_equiv_latticeCoords (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    ∃ (n : ℕ) (T : (Fin n → ℝ) ≃L[ℝ] (Fin g → ℂ)),
      (∀ ν : Fin n → ℤ, T (fun k => (ν k : ℝ)) ∈ Λ) ∧
      ∀ l : Λ, ∃ ν : Fin n → ℤ, T.symm l = fun k => (ν k : ℝ) := by
  haveI : IsZLattice ℝ Λ := ⟨hΛ⟩
  let b0 := Module.finBasis ℤ Λ
  let b := b0.ofZLatticeBasis ℝ Λ
  refine ⟨_, b.equivFunL.symm, ?_, ?_⟩
  · intro ν
    have : b.equivFunL.symm (fun k => (ν k : ℝ)) = ∑ k, (ν k : ℝ) • b k :=
      b.equivFun_symm_apply _
    rw [this]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    refine Submodule.smul_mem _ _ ?_
    simp [b]
  · intro l
    refine ⟨fun k => b0.repr l k, ?_⟩
    funext k
    have := Module.Basis.ofZLatticeBasis_repr_apply ℝ Λ b0 l k
    simpa [b] using this

theorem realLinear_eq_sum_single {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℂ) (u : Fin n → ℝ) :
    L u = ∑ k, (u k : ℂ) * L (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single u]

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (Pi.single k (u k) : Fin n → ℝ) = u k • (Pi.single k 1 : Fin n → ℝ) := by
    rw [← Pi.single_smul]; simp
  rw [this, map_smul]; simp

theorem dbar_comp_equiv {n g : ℕ} (T : (Fin n → ℝ) ≃L[ℝ] (Fin g → ℂ)) (h : (Fin g → ℂ) → ℂ)
    (x : Fin n → ℝ) (u v : Fin g → ℂ) :
    ∑ k, ((T.symm u k : ℂ) + I * (T.symm v k : ℂ)) * fderiv ℝ (h ∘ T) x (Pi.single k 1) =
      fderiv ℝ h (T x) u + I * fderiv ℝ h (T x) v := by
  have e : ∀ y, fderiv ℝ h (T x) y = fderiv ℝ (h ∘ T) x (T.symm y) := by
    intro y
    rw [ContinuousLinearEquiv.comp_right_fderiv]; simp
  rw [e u, e v, realLinear_eq_sum_single _ (T.symm u), realLinear_eq_sum_single _ (T.symm v),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem dbar_symbol_elliptic {n g : ℕ} (T : (Fin n → ℝ) ≃L[ℝ] (Fin g → ℂ)) (ξ : Fin n → ℝ)
    (h : ∀ a, ∑ k, ((T.symm (Pi.single a 1) k : ℂ) +
      I * (T.symm (I • (Pi.single a 1 : Fin g → ℂ)) k : ℂ)) * (ξ k : ℂ) = 0) : ξ = 0 := by
  have h1 : ∀ a, T.symm (Pi.single a 1) ⬝ᵥ ξ = 0 := fun a => by
    have := congrArg Complex.re (h a)
    simpa [Complex.re_sum, dotProduct] using this
  have h2 : ∀ a, T.symm (I • (Pi.single a 1 : Fin g → ℂ)) ⬝ᵥ ξ = 0 := fun a => by
    have := congrArg Complex.im (h a)
    simpa [Complex.im_sum, dotProduct] using this
  have h3 : ∀ z : Fin g → ℂ, T.symm z ⬝ᵥ ξ = 0 := fun z => by
    have hz : z = ∑ a, ((z a).re • (Pi.single a 1 : Fin g → ℂ) +
        (z a).im • (I • (Pi.single a 1 : Fin g → ℂ))) := by
      conv_lhs => rw [← Finset.univ_sum_single z]
      refine Finset.sum_congr rfl fun a _ => ?_
      funext c
      by_cases hc : c = a
      · subst hc; simp
      · simp [hc]

    rw [hz, map_sum, sum_dotProduct]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [map_add (f := _), map_smul, map_smul, add_dotProduct, smul_dotProduct, smul_dotProduct, h1, h2]
    simp
  have := h3 (T ξ)
  rw [T.symm_apply_apply] at this
  exact dotProduct_self_eq_zero.mp this

theorem dbar_solve_complexTorus : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ w : Fin g → (Fin g → ℂ) → ℂ, (∀ a, ContDiff ℝ ∞ (w a) ∧ ∀ (l : Λ) z, w a (z + l) = w a z) → (∀ a b z, (fderiv ℝ (w b) z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ (w b) z (I • (Pi.single a 1 : Fin g → ℂ))) = (fderiv ℝ (w a) z (Pi.single b 1 : Fin g → ℂ) + I * fderiv ℝ (w a) z (I • (Pi.single b 1 : Fin g → ℂ)))) → ∃ (t : Fin g → ℂ) (f : (Fin g → ℂ) → ℂ), ContDiff ℝ ∞ f ∧ (∀ (l : Λ) z, f (z + l) = f z) ∧ ∀ a z, (fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))) = w a z - t a := by
  intro g Λ hd hΛ w hw hc
  obtain ⟨n, T, hT1, hT2⟩ := exists_equiv_latticeCoords g Λ hΛ
  obtain ⟨t, f, hf, hper, heq⟩ := GlobalTheory.T.exists_periodic_smooth_solution_torus_system n g
    (fun a k => (T.symm (Pi.single a 1) k : ℂ) +
      I * (T.symm (I • (Pi.single a 1 : Fin g → ℂ)) k : ℂ))
    (dbar_symbol_elliptic T) (fun a => w a ∘ T)
    (fun a => ⟨(hw a).1.comp T.contDiff, fun ν x => by
      simp only [Function.comp, map_add (f := _)]
      exact (hw a).2 ⟨_, hT1 ν⟩ _⟩)
    (fun a b x => by
      rw [dbar_comp_equiv, dbar_comp_equiv]
      exact hc a b _)
  refine ⟨t, f ∘ T.symm, hf.comp T.symm.contDiff, fun l z => ?_, fun a z => ?_⟩
  · obtain ⟨ν, hν⟩ := hT2 l
    simp only [Function.comp, map_add (f := _), hν]
    exact hper ν _
  · have h1 := dbar_comp_equiv T (f ∘ T.symm) (T.symm z) (Pi.single a 1)
      (I • (Pi.single a 1 : Fin g → ℂ))
    have h2 : (f ∘ T.symm) ∘ T = f := by funext y; simp
    rw [h2, T.apply_symm_apply] at h1
    rw [← h1, heq a]
    simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.DbarSolveComplexTorusStatement

section

@[expose] public section

open Complex Matrix
open scoped ContDiff BigOperators Real

theorem _root_.GlobalTheory.T.exists_periodic_dbar_solution : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ w : Fin g → (Fin g → ℂ) → ℂ, (∀ a, ContDiff ℝ ∞ (w a) ∧ ∀ (l : Λ) z, w a (z + l) = w a z) → (∀ a b z, (fderiv ℝ (w b) z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ (w b) z (I • (Pi.single a 1 : Fin g → ℂ))) = (fderiv ℝ (w a) z (Pi.single b 1 : Fin g → ℂ) + I * fderiv ℝ (w a) z (I • (Pi.single b 1 : Fin g → ℂ)))) → ∃ (t : Fin g → ℂ) (f : (Fin g → ℂ) → ℂ), ContDiff ℝ ∞ f ∧ (∀ (l : Λ) z, f (z + l) = f z) ∧ ∀ a z, (fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))) = w a z - t a := by
  first | exact @GlobalTheory.dbar_solve_complexTorus | exact GlobalTheory.dbar_solve_complexTorus | (intros; apply GlobalTheory.dbar_solve_complexTorus <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicPeriodicCocycleCoboundary

section

@[expose] public section

open Complex Matrix
open scoped ContDiff BigOperators Real Topology

namespace GlobalTheory.PeriodicCousin

variable {g : ℕ}

noncomputable def dbar (a : Fin g) (f : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) : ℂ :=
  fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))

theorem dbar_congr {a : Fin g} {f f' : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ} (h : f =ᶠ[𝓝 z] f') :
    dbar a f z = dbar a f' z := by
  unfold dbar; rw [h.fderiv_eq]

theorem dbar_sub {a : Fin g} {f f' : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : DifferentiableAt ℝ f z) (h' : DifferentiableAt ℝ f' z) :
    dbar a (fun x => f x - f' x) z = dbar a f z - dbar a f' z := by
  unfold dbar
  rw [fderiv_fun_sub h h']
  simp only [ContinuousLinearMap.sub_apply]
  ring

theorem contDiffAt_fderiv {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ} (h : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (fderiv ℝ f) z :=
  h.fderiv_right (m := ∞) (by norm_cast)

theorem contDiffAt_dbar {a : Fin g} {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : ContDiffAt ℝ ∞ f z) : ContDiffAt ℝ ∞ (dbar a f) z := by
  have h1 := contDiffAt_fderiv h
  exact (h1.clm_apply contDiffAt_const).add (contDiffAt_const.mul (h1.clm_apply contDiffAt_const))

theorem fderiv_dbar {a : Fin g} {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : ContDiffAt ℝ ∞ f z) (v : Fin g → ℂ) :
    fderiv ℝ (dbar a f) z v = fderiv ℝ (fderiv ℝ f) z v (Pi.single a 1 : Fin g → ℂ) +
      I * fderiv ℝ (fderiv ℝ f) z v (I • (Pi.single a 1 : Fin g → ℂ)) := by
  have h1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((contDiffAt_fderiv h).differentiableAt (by simp)).hasFDerivAt
  have h2 := fun u : Fin g → ℂ =>
    (ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt.comp z h1
  have h3 := (h2 (Pi.single a 1)).add ((h2 (I • (Pi.single a 1 : Fin g → ℂ))).const_mul I)
  have h4 : fderiv ℝ (dbar a f) z = _ := h3.fderiv
  rw [h4]
  simp

theorem dbar_comm {a b : Fin g} {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : ContDiffAt ℝ ∞ f z) : dbar a (dbar b f) z = dbar b (dbar a f) z := by
  have hs : IsSymmSndFDerivAt ℝ f z := h.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have e : ∀ u v, fderiv ℝ (fderiv ℝ f) z u v = fderiv ℝ (fderiv ℝ f) z v u := hs
  show fderiv ℝ (dbar b f) z _ + I * fderiv ℝ (dbar b f) z _ =
    fderiv ℝ (dbar a f) z _ + I * fderiv ℝ (dbar a f) z _
  rw [fderiv_dbar h, fderiv_dbar h, fderiv_dbar h, fderiv_dbar h,
    e (Pi.single b 1) (Pi.single a 1), e (Pi.single b 1) (I • (Pi.single a 1 : Fin g → ℂ)),
    e (I • (Pi.single b 1 : Fin g → ℂ)) (Pi.single a 1),
    e (I • (Pi.single b 1 : Fin g → ℂ)) (I • (Pi.single a 1 : Fin g → ℂ))]
  ring

noncomputable def antilin (t : Fin g → ℂ) : (Fin g → ℂ) →L[ℝ] ℂ :=
  ∑ a, t a • ((conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj a))

theorem antilin_apply (t z : Fin g → ℂ) : antilin t z = t ⬝ᵥ star z := by
  simp [antilin, dotProduct]

theorem dbar_antilin (t z : Fin g → ℂ) (a : Fin g) : dbar a (antilin t) z = 2 * t a := by
  unfold dbar
  rw [ContinuousLinearMap.fderiv, antilin_apply, antilin_apply]
  have h1 : star (Pi.single a 1 : Fin g → ℂ) = Pi.single a 1 := by
    ext j; by_cases h : j = a
    · subst h; simp
    · simp [h]
  rw [star_smul, h1]
  simp only [dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul, star_def, conj_I]
  linear_combination (-t a) * I_mul_I

end GlobalTheory.PeriodicCousin

namespace GlobalTheory
open PeriodicCousin

theorem holomorphic_periodic_cocycle_coboundary : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (ι : Type) (U : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → (∀ i j, DifferentiableOn ℂ (c i j) (U i ∩ U j)) → (∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, c i j (z + l) = c i j z) → (∀ i j k, ∀ z ∈ U i ∩ U j ∩ U k, c i j z + c j k z = c i k z) → ∃ (t : (Fin g → ℂ)) (h : ι → (Fin g → ℂ) → ℂ), (∀ i, DifferentiableOn ℂ (h i) (U i) ∧ ∀ (l : Λ), ∀ z ∈ U i, h i (z + l) = h i z + t ⬝ᵥ star (l : (Fin g → ℂ))) ∧ ∀ i j, ∀ z ∈ U i ∩ U j, c i j z = h j z - h i z := by
  intro g Λ hd hs ι U c hU hUΛ hcov hc hcΛ hcoc
  have hcs : ∀ i j, ContDiffOn ℝ ∞ (c i j) (U i ∩ U j) := fun i j =>
    ((GlobalTheory.T.cauchyRiemann_iff_differentiableOn g _ (c i j) ((hU i).inter (hU j))).2 (hc i j)).1
  obtain ⟨b, hb, hcb⟩ := GlobalTheory.T.exists_periodic_smooth_coboundary_of_cech_cocycle g Λ hd hs ι U c hU hUΛ hcov hcs hcΛ hcoc
  choose k hk using hcov
  have hbAt : ∀ i, ∀ z ∈ U i, ContDiffAt ℝ ∞ (b i) z := fun i z hz =>
    (hb i).1.contDiffAt ((hU i).mem_nhds hz)
  have hind : ∀ a i j, ∀ z ∈ U i, z ∈ U j → dbar a (b j) z = dbar a (b i) z := by
    intro a i j z hi hj
    have ho := (hU i).inter (hU j)
    have h0 : dbar a (c i j) z = 0 :=
      ((GlobalTheory.T.cauchyRiemann_iff_differentiableOn g _ (c i j) ho).1 ((hcs i j).differentiableOn (by simp))).2 (hc i j) a z ⟨hi, hj⟩
    have h1 : c i j =ᶠ[𝓝 z] fun x => b j x - b i x := by
      filter_upwards [ho.mem_nhds ⟨hi, hj⟩] with x hx using hcb i j x hx
    rw [dbar_congr h1, dbar_sub ((hbAt j z hj).differentiableAt (by simp))
      ((hbAt i z hi).differentiableAt (by simp))] at h0
    exact sub_eq_zero.1 h0
  let w : Fin g → (Fin g → ℂ) → ℂ := fun a z => dbar a (b (k z)) z
  have hw : ∀ a i, ∀ z ∈ U i, w a z = dbar a (b i) z := fun a i z hz => hind a i (k z) z hz (hk z)
  have hw' : ∀ a i, ∀ z ∈ U i, w a =ᶠ[𝓝 z] dbar a (b i) := by
    intro a i z hz
    filter_upwards [(hU i).mem_nhds hz] with x hx using hw a i x hx
  obtain ⟨t, f, hf, hfΛ, hft⟩ := GlobalTheory.T.exists_periodic_dbar_solution g Λ hd hs w (by
    intro a
    refine ⟨contDiff_iff_contDiffAt.2 fun z =>
      (contDiffAt_dbar (hbAt _ z (hk z))).congr_of_eventuallyEq (hw' a _ z (hk z)), fun l z => ?_⟩
    rw [hw a (k z) _ (hUΛ _ l z (hk z)), hw a (k z) z (hk z)]
    have h1 : (fun x => b (k z) (x + l)) =ᶠ[𝓝 z] b (k z) := by
      filter_upwards [(hU _).mem_nhds (hk z)] with x hx using (hb _).2 l x hx
    rw [← dbar_congr h1]
    unfold dbar
    rw [fderiv_comp_add_right]) (by
    intro a a' z
    show dbar a (w a') z = dbar a' (w a) z
    rw [dbar_congr (hw' a' _ z (hk z)), dbar_congr (hw' a _ z (hk z))]
    exact dbar_comm (hbAt _ z (hk z)))
  have hfd : ∀ z, DifferentiableAt ℝ f z := fun z => (hf.differentiable (by simp)) z
  refine ⟨-((1 / 2 : ℂ) • t), fun i z => b i z - f z - antilin ((1 / 2 : ℂ) • t) z,
    fun i => ⟨?_, ?_⟩, ?_⟩
  · have hbd : ∀ z ∈ U i, DifferentiableAt ℝ (b i) z := fun z hz =>
      (hbAt i z hz).differentiableAt (by simp)
    refine ((GlobalTheory.T.cauchyRiemann_iff_differentiableOn g _ _ (hU i)).1 ?_).1 ?_
    · intro z hz
      exact (((hbd z hz).sub (hfd z)).sub (antilin _).differentiableAt).differentiableWithinAt
    · intro a z hz
      show dbar a (fun z => (b i z - f z) - antilin ((1 / 2 : ℂ) • t) z) z = 0
      have h3 : dbar a f z = w a z - t a := hft a z
      rw [dbar_sub ((hbd z hz).fun_sub (hfd z)) (antilin _).differentiableAt,
        dbar_sub (hbd z hz) (hfd z), dbar_antilin, h3, hw a i z hz]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  · intro l z hz
    simp only [(hb i).2 l z hz, hfΛ l z, map_add (f := _), antilin_apply _ (l : Fin g → ℂ), neg_dotProduct]
    ring
  · intro i j z hz
    rw [hcb i j z hz]
    ring

end GlobalTheory
end
end
