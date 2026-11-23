module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCasA
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCasB
public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCasC

section

@[expose] public section

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

section SlopeTestRemainingChoices

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [Fintype J] in
theorem updInv (s : J) : Function.Involutive
    (fun x : (J → I) × I => (Function.update x.1 s x.2, x.1 s)) := by
  rintro ⟨w, i⟩
  simp [Function.update_idem, Function.update_self, Function.update_eq_self]

theorem sum_upd {β : Type} [AddCommMonoid β] (s : J) (g : (J → I) → I → β) :
    ∑ w, ∑ j, g w j = ∑ w, ∑ j, g (Function.update w s j) (w s) := by
  calc ∑ w, ∑ j, g w j = ∑ x : (J → I) × I, g x.1 x.2 := (Fintype.sum_prod_type' g).symm
    _ = ∑ x : (J → I) × I, g (Function.update x.1 s x.2) (x.1 s) :=
        (Equiv.sum_comp (Function.Involutive.toPerm _ (PositivityTheory.KReal.updInv s))
          (fun x => g x.1 x.2)).symm
    _ = ∑ w, ∑ j, g (Function.update w s j) (w s) :=
        Fintype.sum_prod_type' (fun w j => g (Function.update w s j) (w s))

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def positionA (m : Matrix I I ℂ) (Θ : (J → I) → V) : (J → I) → V :=
  fun w => ∑ s, ∑ j, m (w s) j • Θ (Function.update w s j)

def formT (Θ Θ' : (J → I) → V) : ℂ := ∑ w, ⟪Θ w, Θ' w⟫_ℂ

theorem formT_positionA (m : Matrix I I ℂ) (Θ Θ' : (J → I) → V) :
    formT (positionA mᴴ Θ) Θ' = formT Θ (positionA m Θ') := by
  unfold PositivityTheory.KReal.formT PositivityTheory.KReal.positionA
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Matrix.conjTranspose_apply,
    starRingEnd_apply, star_star]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  conv_rhs => rw [PositivityTheory.KReal.sum_upd s]
  simp only [Function.update_self, Function.update_idem, Function.update_eq_self]

theorem formT_self_nonneg (a : (J → I) → V) : 0 ≤ (formT a a).re := by
  unfold PositivityTheory.KReal.formT
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun w _ => by
    have h := inner_self_nonneg (𝕜 := ℂ) (x := a w)
    rwa [RCLike.re_to_complex] at h

end SlopeTestRemainingChoices

theorem cas_tensor {K I J : Type} [Fintype K] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty J]
    (σ : K → K) (hσ : Function.Involutive σ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (e : K → Module.End ℂ M)
    (c : K → Matrix I I ℂ) (c0 : ℝ) (h3 : ∀ k, c (σ k) = (c k)ᴴ)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : K → Module.End ℂ V) (hadj : ∀ k u v, ⟪ρ k u, v⟫_ℂ = ⟪u, ρ (σ k) v⟫_ℂ)
    (hc0 : ∑ k, ρ k * ρ (σ k) = (c0 : ℂ) • (1 : Module.End ℂ V))
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v))
    (W : (J → I) → Module.End ℂ M)
    (hW : ∀ k w, e k * W w = W w * e k + ∑ i, ∑ j, c k j (w i) • W (Function.update w i j))
    (φ : M →ₗ[ℂ] ℂ) (Ψ : (J → I) → V) (hΨ : ∀ w v, ⟪Ψ w, v⟫_ℂ = φ (W w (ι v)))
    (hφ : ∀ w v, φ ((∑ k, e k * e (σ k)) (W w (ι v)) - (c0 : ℂ) • W w (ι v)) = 0)
    (hpos : ∀ (s : J) (w : J → I),
      0 ≤ (∑ k, ∑ i, ∑ j, ⟪Ψ (Function.update w s i), c k i j • ρ (σ k) (Ψ (Function.update w s j))⟫_ℂ).re ∧
      ((∑ k, ∑ i, ∑ j, ⟪Ψ (Function.update w s i), c k i j • ρ (σ k) (Ψ (Function.update w s j))⟫_ℂ).re = 0 →
        (fun i => Ψ (Function.update w s i)) = 0)) : Ψ = 0 := by
  have hc : ∀ k u x, e k (W u x) = W u (e k x) + ∑ i, ∑ j, c k j (u i) • W (Function.update u i j) x := by
    intro k u x
    have h := LinearMap.congr_fun (hW k u) x
    simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply] using h
  have hk : ∀ k u x, e k (e (σ k) (W u x)) = W u (e k (e (σ k) x)) +
      (∑ i, ∑ j, c k j (u i) • W (Function.update u i j) (e (σ k) x) +
        ∑ i, ∑ j, c (σ k) j (u i) • (W (Function.update u i j) (e k x) +
          ∑ i', ∑ j', c k j' (Function.update u i j i') •
            W (Function.update (Function.update u i j) i' j') x)) := by
    intro k u x

    simp only [hc, map_add (f := _), map_sum, map_smul, add_assoc]
  have hΨ' : ∀ u v, φ (W u (ι v)) = ⟪Ψ u, v⟫_ℂ := fun u v => (hΨ u v).symm
  have hΨe : ∀ k u v, φ (W u (e k (ι v))) = ⟪Ψ u, ρ k v⟫_ℂ := by
    intro k u v
    rw [← hι, hΨ]
  have hcas : ∀ v, ∑ k, e k (e (σ k) (ι v)) = (c0 : ℂ) • ι v := by
    intro v
    have h := congrArg ι (LinearMap.congr_fun hc0 v)

    simpa only [LinearMap.sum_apply, Module.End.mul_apply, map_sum, hι, LinearMap.smul_apply,
    Module.End.one_apply, map_smul] using h
  have hA : ∀ u v, ∑ k, φ (W u (e k (e (σ k) (ι v)))) = (c0 : ℂ) * ⟪Ψ u, v⟫_ℂ := by
    intro u v
    calc ∑ k, φ (W u (e k (e (σ k) (ι v)))) = φ (W u (∑ k, e k (e (σ k) (ι v)))) := by

          simp only [map_sum]
      _ = (c0 : ℂ) * ⟪Ψ u, v⟫_ℂ := by rw [hcas, map_smul, map_smul, hΨ', smul_eq_mul]
  have hF : ∀ w, ∑ k, (⟪PositivityTheory.KReal.positionA (c (σ k)) Ψ w, ρ (σ k) (Ψ w)⟫_ℂ +
      ⟪PositivityTheory.KReal.positionA (c k) Ψ w, ρ k (Ψ w)⟫_ℂ +
      ⟪PositivityTheory.KReal.positionA (c k) (PositivityTheory.KReal.positionA (c (σ k)) Ψ) w, Ψ w⟫_ℂ) = 0 := by
    intro w
    have h := hφ w (Ψ w)
    have h' := hA w (Ψ w)

    simp only [map_sub, LinearMap.sum_apply, map_sum, Module.End.mul_apply, hk, map_add (f := _), map_smul,
    smul_eq_mul, hΨ', hΨe, h3, Matrix.conjTranspose_apply, starRingEnd_apply, star_star,
    Finset.mul_sum, mul_add, Finset.sum_add_distrib] at h
    simp only [PositivityTheory.KReal.positionA, sum_inner, inner_smul_left, h3, Matrix.conjTranspose_apply,
      starRingEnd_apply, star_star, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    linear_combination h - h'
  have hsum : ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c (σ k)) Ψ) (fun w => ρ (σ k) (Ψ w)) +
      ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w)) +
      ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) (PositivityTheory.KReal.positionA (c (σ k)) Ψ)) Ψ = 0 := by
    have h := Finset.sum_eq_zero (s := Finset.univ) (fun w _ => hF w)
    rw [Finset.sum_comm] at h
    simpa only [PositivityTheory.KReal.formT, Finset.sum_add_distrib] using h
  have hT1 : ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c (σ k)) Ψ) (fun w => ρ (σ k) (Ψ w)) =
      ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w)) :=
    Fintype.sum_equiv (Function.Involutive.toPerm σ hσ) _ _ (fun _ => rfl)
  have hck : ∀ k, c k = (c (σ k))ᴴ := fun k => by rw [← h3 (σ k), hσ k]
  have hT3 : 0 ≤ (∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k)
      (PositivityTheory.KReal.positionA (c (σ k)) Ψ)) Ψ).re := by
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun k _ => ?_
    rw [hck k, PositivityTheory.KReal.formT_positionA]
    exact PositivityTheory.KReal.formT_self_nonneg _
  have hre2 : (∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w))).re ≤ 0 := by
    have h := congrArg Complex.re hsum
    rw [hT1, Complex.add_re, Complex.add_re, Complex.zero_re] at h
    linarith
  obtain ⟨q, hq⟩ : ∃ q : J → (J → I) → ℂ, ∀ s w, q s w = ∑ k, ∑ i, ∑ j,
      ⟪Ψ (Function.update w s i), c k i j • ρ (σ k) (Ψ (Function.update w s j))⟫_ℂ :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : J → (J → I) → ℂ, ∀ s w, H s w = ∑ k, ∑ j,
      ⟪Ψ w, c k (w s) j • ρ (σ k) (Ψ (Function.update w s j))⟫_ℂ :=
    ⟨_, fun _ _ => rfl⟩
  have hpos' : ∀ s w, 0 ≤ (q s w).re ∧ ((q s w).re = 0 → (fun i => Ψ (Function.update w s i)) = 0) := by
    intro s w
    rw [hq]
    exact hpos s w
  have hqH : ∀ s w, q s w = ∑ i, H s (Function.update w s i) := by
    intro s w
    simp only [hq, hH, Function.update_self, Function.update_idem]
    exact Finset.sum_comm
  have hsumH : ∀ s, ∑ w, q s w = (Fintype.card I : ℂ) * ∑ w, H s w := by
    intro s
    have h := PositivityTheory.KReal.sum_upd s (fun w i => H s (Function.update w s i))
    simp only [Function.update_idem, Function.update_eq_self] at h
    simp only [hqH, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
  have hHc : ∀ s w, H s w = starRingEnd ℂ (∑ k, ∑ j, starRingEnd ℂ (c k (w s) j) *
      ⟪Ψ (Function.update w s j), ρ k (Ψ w)⟫_ℂ) := by
    intro s w
    rw [hH]

    simp only [map_sum, map_mul, Complex.conj_conj, inner_conj_symm, inner_smul_right, ← hadj]
  have hT2 : ∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w)) =
      ∑ w, ∑ s, ∑ k, ∑ j, starRingEnd ℂ (c k (w s) j) * ⟪Ψ (Function.update w s j), ρ k (Ψ w)⟫_ℂ := by
    simp only [PositivityTheory.KReal.formT, PositivityTheory.KReal.positionA, sum_inner, inner_smul_left]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_comm
  have hHT : (∑ s, ∑ w, H s w).re =
      (∑ k, PositivityTheory.KReal.formT (PositivityTheory.KReal.positionA (c k) Ψ) (fun w => ρ k (Ψ w))).re := by
    rw [hT2, Finset.sum_comm]
    have e1 : ∑ w, ∑ s, H s w = starRingEnd ℂ (∑ w, ∑ s, ∑ k, ∑ j, starRingEnd ℂ (c k (w s) j) *
        ⟪Ψ (Function.update w s j), ρ k (Ψ w)⟫_ℂ) := by

      simp only [hHc, map_sum]
    rw [e1, Complex.conj_re]
  have hQle : ∑ s, ∑ w, (q s w).re ≤ 0 := by
    have e2 : ∑ s, ∑ w, (q s w).re = (Fintype.card I : ℝ) * (∑ s, ∑ w, H s w).re := by
      calc ∑ s, ∑ w, (q s w).re = ∑ s, ((Fintype.card I : ℂ) * ∑ w, H s w).re := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [← Complex.re_sum, hsumH]
        _ = ((Fintype.card I : ℂ) * ∑ s, ∑ w, H s w).re := by
            rw [Finset.mul_sum, Complex.re_sum]
        _ = (Fintype.card I : ℝ) * (∑ s, ∑ w, H s w).re := by
            rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    rw [e2, hHT]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hre2
  have hQ0 : ∀ s w, (q s w).re = 0 := by
    intro s w
    have h1 : (q s w).re ≤ ∑ w', (q s w').re :=
      Finset.single_le_sum (f := fun w' => (q s w').re) (fun w' _ => (hpos' s w').1) (Finset.mem_univ w)
    have h2 : ∑ w', (q s w').re ≤ ∑ s', ∑ w', (q s' w').re :=
      Finset.single_le_sum (f := fun s' => ∑ w', (q s' w').re)
        (fun s' _ => Finset.sum_nonneg fun w' _ => (hpos' s' w').1) (Finset.mem_univ s)
    linarith [(hpos' s w).1]
  funext w
  have h := congrFun ((hpos' (Classical.arbitrary J) w).2 (hQ0 _ w)) (w (Classical.arbitrary J))
  simpa using h

end PositivityTheory.KReal

end
end
end

-- Source module: Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCas

section

@[expose] public section

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem cas_bound {K I : Type} [Fintype K] [Fintype I] [DecidableEq I] (σ : K → K) (hσ : Function.Involutive σ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M)
    (c : K → Matrix I I ℂ) (d c0 : ℝ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j)
    (h2 : ∀ i j, X i * X j - X j * X i ∈ Submodule.span ℂ (Set.range e))
    (h3 : ∀ k, c (σ k) = (c k)ᴴ)
    (h4 : ∑ k, c k * c (σ k) = (d : ℂ) • (1 : Matrix I I ℂ))
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : K → Module.End ℂ V) (hadj : ∀ k u v, ⟪ρ k u, v⟫_ℂ = ⟪u, ρ (σ k) v⟫_ℂ)
    (hc0 : ∑ k, ρ k * ρ (σ k) = (c0 : ℂ) • (1 : Module.End ℂ V))
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v))
    (h5 : ∀ t : ℝ, t ≤ c0 + d → ∀ x ∈ Submodule.span ℂ {y | ∃ i v, y = X i (ι v)},
      (∑ k, e k * e (σ k)) x = (t : ℂ) • x → x = 0)
    (G : Submodule ℂ M)
    (hG : G = sInf {N | LinearMap.range ι ≤ N ∧ (∀ k, ∀ x ∈ N, e k x ∈ N) ∧ ∀ i, ∀ x ∈ N, X i x ∈ N}) :
    (∀ x ∈ G, (∑ k, e k * e (σ k)) x - (c0 : ℂ) • x ∈ LinearMap.range ι → x ∈ LinearMap.range ι) ∧
    ∀ x ∈ G, ∃ F : Submodule ℂ M, FiniteDimensional ℂ F ∧ x ∈ F ∧ ∀ k, ∀ y ∈ F, e k y ∈ F := by
  classical
  have hFe : ∀ n k, ∀ x ∈ filtX X ι n, e k x ∈ filtX X ι n := fun n k => filtX_e e X c h1 ρ ι hι n k
  have hGF : ∀ x ∈ G, ∃ n, x ∈ filtX X ι n := by
    intro x hx
    have hdir : Directed (· ≤ ·) (filtX X ι) := (Monotone.directed_le fun _ _ h => filtX_mono X ι h)
    have hle : G ≤ ⨆ n, filtX X ι n := by
      rw [hG]
      refine sInf_le ⟨?_, ?_, ?_⟩
      · rw [← filtX_zero X ι]; exact le_iSup (filtX X ι) 0
      · intro k y hy
        obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hy
        exact Submodule.mem_iSup_of_mem n (hFe n k y hn)
      · intro i y hy
        obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hy
        exact Submodule.mem_iSup_of_mem (n + 1) (filtX_X X ι n i y hn)
    exact (Submodule.mem_iSup_of_directed _ hdir).1 (hle hx)
  refine ⟨?_, fun x hx => ?_⟩
  swap
  · obtain ⟨n, hn⟩ := hGF x hx
    exact ⟨filtX X ι n, filtX_fd X ι n, hn, hFe n⟩
  set C : Module.End ℂ M := (∑ k, e k * e (σ k)) - (c0 : ℂ) • (1 : Module.End ℂ M) with hC
  have hCa : ∀ x, C x = (∑ k, e k * e (σ k)) x - (c0 : ℂ) • x := fun x => by simp [hC]
  have hCF : ∀ n, ∀ x ∈ filtX X ι n, C x ∈ filtX X ι n := by
    intro n x hx
    rw [hCa, LinearMap.sum_apply]
    exact Submodule.sub_mem _ (Submodule.sum_mem _ fun k _ => hFe n k _ (hFe n _ x hx)) (Submodule.smul_mem _ _ hx)

  have hsurj : ∀ n, filtX X ι (n + 1) ≤ filtX X ι n ⊔ (filtX X ι (n + 1)).map C := by
    intro n
    by_contra hcon
    obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.1 hcon
    obtain ⟨φ, hφx, hφ0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxn inferInstance
    have hφz : ∀ y ∈ filtX X ι n ⊔ (filtX X ι (n + 1)).map C, φ y = 0 := by
      intro y hy
      have : φ y ∈ (filtX X ι n ⊔ (filtX X ι (n + 1)).map C).map φ := Submodule.mem_map_of_mem hy
      rw [hφ0] at this
      exact (Submodule.mem_bot ℂ).1 this
    let W : (Fin (n + 1) → I) → Module.End ℂ M := fun w => wordX X (List.ofFn w)
    have hex : ∀ w : Fin (n + 1) → I, ∃ u : V, ∀ v, ⟪u, v⟫_ℂ = φ (W w (ι v)) := by
      intro w
      haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
      refine ⟨(InnerProductSpace.toDual ℂ V).symm
        (LinearMap.toContinuousLinearMap (φ ∘ₗ (W w) ∘ₗ ι)), fun v => ?_⟩
      rw [InnerProductSpace.toDual_symm_apply]
      rfl
    choose Ψ hΨ using hex
    have hWm : ∀ w v, W w (ι v) ∈ filtX X ι (n + 1) := fun w v =>
      Submodule.subset_span ⟨List.ofFn w, v, by simp, rfl⟩
    have hΨ0 : Ψ = 0 := by
      refine cas_tensor σ hσ e c c0 h3 ρ hadj hc0 ι hι W (fun k w => wordX_comm e X c h1 k (n + 1) w) φ Ψ hΨ
        (fun w v => ?_) (fun s w => ?_)
      · rw [← hCa]
        exact hφz _ (Submodule.mem_sup_right (Submodule.mem_map_of_mem (hWm w v)))
      · refine cas_one σ hσ e X c d c0 h1 h3 h4 ρ hadj hc0 ι hι h5 (fun i => Ψ (Function.update w s i))
          (fun Θ hΘ => ?_)
        have key : ∀ i, ⟪Ψ (Function.update w s i), Θ i⟫_ℂ =
            φ (wordX X ((List.ofFn w).eraseIdx s) (X i (ι (Θ i)))) := by
          intro i
          rw [hΨ]
          have hp : (List.ofFn (Function.update w s i)).Perm ((List.ofFn w).eraseIdx s ++ [i]) := by
            have e1 : List.ofFn (Function.update w s i) = (List.ofFn w).set s i := by
              apply List.ext_getElem
              · simp
              · intro m h1 h2
                rw [List.getElem_set, List.getElem_ofFn, List.getElem_ofFn]
                by_cases hm : (s : ℕ) = m
                · subst hm; simp
                · rw [if_neg hm, Function.update_of_ne]
                  intro h; exact hm (by rw [← h])
            rw [e1]
            exact (List.set_perm_cons_eraseIdx (by simpa using s.2) i).trans
              (List.perm_append_singleton _ _).symm
          have hm := filtX_perm e X c h1 h2 ρ ι hι hp n (by simp) (Θ i)
          have h0 := hφz _ (Submodule.mem_sup_left hm)
          rw [map_sub, sub_eq_zero] at h0
          refine h0.trans ?_
          simp [wordX]
        simp only [key]

        rw [← map_sum, ← map_sum, hΘ, map_zero, map_zero]
    apply hφx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (filtX_succ_le X ι n hx)
    rw [map_add (f := _), hφz y (Submodule.mem_sup_left hy), zero_add]
    have : Submodule.span ℂ {y | ∃ (w : Fin (n + 1) → I) (v : V), y = wordX X (List.ofFn w) (ι v)} ≤
        LinearMap.ker φ := by
      rw [Submodule.span_le]
      rintro _ ⟨w, v, rfl⟩
      have := hΨ w v
      rw [hΨ0] at this
      rw [Pi.zero_apply, inner_zero_left] at this
      exact this.symm
    exact this hz
  have hstep : ∀ n, ∀ x ∈ filtX X ι (n + 1), C x ∈ filtX X ι n → x ∈ filtX X ι n := by
    intro n x hx hCx
    haveI := filtX_fd X ι (n + 1)
    let P : Submodule ℂ (filtX X ι (n + 1)) := (filtX X ι n).comap (filtX X ι (n + 1)).subtype
    let C1 : Module.End ℂ (filtX X ι (n + 1)) := C.restrict (hCF (n + 1))
    have hP : P ≤ P.comap C1 := fun y hy => hCF n y hy
    have hs : Function.Surjective (P.mapQ P C1 hP) := by
      intro z
      obtain ⟨y, rfl⟩ := P.mkQ_surjective z
      obtain ⟨a, ha, _, ⟨b, hb, rfl⟩, hab⟩ := Submodule.mem_sup.1 (hsurj n y.2)
      refine ⟨P.mkQ ⟨b, hb⟩, ?_⟩
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq]
      show C b - (y : M) ∈ filtX X ι n
      rw [← hab]
      simpa using ha
    have hi : Function.Injective (P.mapQ P C1 hP) := LinearMap.injective_iff_surjective.2 hs
    have : P.mkQ ⟨x, hx⟩ = 0 := by
      apply hi
      rw [map_zero, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hCx
    exact (Submodule.Quotient.mk_eq_zero P).1 this
  intro x hx hCx
  rw [← hCa, ← filtX_zero X ι] at hCx
  rw [← filtX_zero X ι]
  obtain ⟨n, hn⟩ := hGF x hx
  induction n with
  | zero => exact hn
  | succ n ih => exact ih (hstep n x hn (filtX_mono X ι (Nat.zero_le n) hCx))

end PositivityTheory.KReal

end
end
end
