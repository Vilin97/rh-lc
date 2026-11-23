module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ParamDeriv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ParamSmooth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.PoinPt
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
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ConeD

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.coneD :
    UpperTheory.V.Cj.H.ConeD := by
  intro V F _ _ _ _ _ _ Y hYo hYc p hp q w hw
  have hseg : ∀ x ∈ Y, ∀ t ∈ Set.Icc (0:ℝ) 1, p + t • (x - p) ∈ Y := by
    intro x hx t ht
    have h := hYc hp hx (sub_nonneg.2 ht.2) ht.1 (by ring)
    convert h using 1
    rw [smul_sub, sub_smul, one_smul]
    abel
  let g : V × ℝ → V := fun z => p + z.2 • (z.1 - p)
  have hg : ContDiff ℝ ⊤ g := by
    exact contDiff_const.add (contDiff_snd.smul (contDiff_fst.sub contDiff_const))
  let W : Set (V × ℝ) := g ⁻¹' Y
  have hW : IsOpen W := hYo.preimage hg.continuous
  let Φ : V × ℝ → V [⋀^Fin q]→L[ℝ] F :=
    fun z => z.2 ^ q • (w (p + z.2 • (z.1 - p))).curryLeft (z.1 - p)
  have hΦ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ W := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => w (g z)) W :=
      hw.comp (hg.of_le le_top).contDiffOn (fun z hz => hz)
    let L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap
    have hfst : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => z.1 - p) :=
      contDiff_fst.sub contDiff_const
    have h2 := (L.contDiff.comp_contDiffOn h1).clm_apply (hfst.contDiffOn (s := W))
    have hsnd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => z.2 ^ q) :=
      contDiff_snd.pow q
    exact hsnd.contDiffOn.smul h2
  have hsub : Y ×ˢ Set.Icc (0:ℝ) 1 ⊆ W := fun z hz => hseg z.1 hz.1 z.2 hz.2
  refine ⟨UpperTheory.V.Lit.Dr.paramSmooth V (V [⋀^Fin q]→L[ℝ] F) Y W Φ hYo hW hsub hΦ, ?_⟩
  intro hcl x hx
  have hd := UpperTheory.V.Lit.Dr.paramDeriv V (V [⋀^Fin q]→L[ℝ] F) x W Φ hW (fun t ht => hseg x hx t ht) hΦ
  have hI : Set.uIcc (0:ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  let A := ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V F (n := q)
  have hint : IntervalIntegrable (fun t => fderiv ℝ (fun y => Φ (y, t)) x) MeasureTheory.volume 0 1 :=
    (hI ▸ hd.1).intervalIntegrable
  have hcont' : ContinuousOn (fun t => A (fderiv ℝ (fun y => Φ (y, t)) x)) (Set.uIcc 0 1) :=
    hI ▸ (A.continuous.comp_continuousOn hd.1)
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => r ^ (q + 1) • w (p + r • (x - p))) (A (fderiv ℝ (fun y => Φ (y, t)) x)) t := by
    intro t ht
    rw [hI] at ht
    have hm := hseg x hx t ht
    have hdiff : DifferentiableAt ℝ w (p + t • (x - p)) :=
      (hw.contDiffAt (hYo.mem_nhds hm)).differentiableAt (by simp)
    exact UpperTheory.V.Lit.Dr.poinPt V F q w p x t hdiff (hcl _ hm)
  have hfd : fderiv ℝ (UpperTheory.V.Cj.H.coneOp p w) x = ∫ t in (0:ℝ)..1, fderiv ℝ (fun y => Φ (y, t)) x :=
    hd.2.fderiv
  have key : extDeriv (UpperTheory.V.Cj.H.coneOp p w) x = A (fderiv ℝ (UpperTheory.V.Cj.H.coneOp p w) x) := rfl
  rw [key, hfd, ← A.intervalIntegral_comp_comm hint,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont'.intervalIntegrable)]
  simp
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ConeLim

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.coneLim :
    UpperTheory.V.Cj.H.ConeLim := by
  intro V F _ _ _ _ Y hY p hp q w hw K hKY hK
  obtain ⟨C, hC⟩ := (hK.image (continuous_id.sub continuous_const :
    Continuous fun x : V => x - p)).isBounded.exists_norm_le
  set K' : Set V := (fun z : ℝ × V => p + z.1 • (z.2 - p)) '' (Set.Icc (0 : ℝ) 1 ×ˢ K)
  have hK'c : IsCompact K' := (isCompact_Icc.prod hK).image (by fun_prop)
  have hK'Y : K' ⊆ Y := by
    rintro _ ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    exact hY.add_smul_sub_mem hp (hKY hx) ht
  have hwK := hw K' hK'Y hK'c
  rw [Metric.tendstoUniformlyOn_iff] at hwK ⊢
  intro ε hε
  have hR : 0 < |C| + 1 := by positivity
  filter_upwards [hwK (ε / 2 / (|C| + 1)) (by positivity)] with k hk x hx
  simp only [Pi.zero_apply, dist_zero_left] at hk ⊢
  have hxp : ‖x - p‖ ≤ |C| + 1 := by
    have h0 := hC (x - p) ⟨x, hx, rfl⟩
    linarith [le_abs_self C]
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖t ^ q • (w k (p + t • (x - p))).curryLeft (x - p)‖ ≤ ε / 2 / (|C| + 1) * (|C| + 1) := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hy : p + t • (x - p) ∈ K' := ⟨(t, x), ⟨⟨ht.1.le, ht.2⟩, hx⟩, rfl⟩
    have h1 := hk _ hy
    rw [norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos ht.1]
    have h2 : t ^ q ≤ 1 := pow_le_one₀ ht.1.le ht.2
    have h3 : ‖(w k (p + t • (x - p))).curryLeft (x - p)‖
        ≤ ‖w k (p + t • (x - p))‖ * ‖x - p‖ := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans_eq ?_
      rw [ContinuousAlternatingMap.norm_curryLeft]
    have h4 : ‖w k (p + t • (x - p))‖ * ‖x - p‖ ≤ ε / 2 / (|C| + 1) * (|C| + 1) :=
      mul_le_mul h1.le hxp (norm_nonneg _) (by positivity)
    calc t ^ q * ‖(w k (p + t • (x - p))).curryLeft (x - p)‖
        ≤ 1 * ‖(w k (p + t • (x - p))).curryLeft (x - p)‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ ε / 2 / (|C| + 1) * (|C| + 1) := by
          rw [one_mul]
          exact h3.trans h4
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have e : ε / 2 / (|C| + 1) * (|C| + 1) = ε / 2 := by field_simp
  rw [e] at hint
  simp only [sub_zero, abs_one, mul_one] at hint
  calc ‖UpperTheory.V.Cj.H.coneOp p (w k) x‖
      = ‖∫ t in (0 : ℝ)..1, t ^ q • (w k (p + t • (x - p))).curryLeft (x - p)‖ := rfl
    _ ≤ ε / 2 := hint
    _ < ε := by linarith
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.PoinOp

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} (G : Dr.Geo Γ V S d)

private theorem tr_tr (q : ℕ) (γ δ : Γ) (h : γ * δ = 1) (m : V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) :
    G.tr q γ (G.tr q δ m) = m := by
  have hδ : δ = γ⁻¹ := eq_inv_of_mul_eq_one_right h
  subst hδ
  ext v
  rw [Geo.tr_apply, Geo.tr_apply, Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one,
    Matrix.one_mulVec]
  have hv : (fun i => (G.ρ γ⁻¹⁻¹) ((G.ρ γ⁻¹) (v i))) = v := by
    funext i
    exact Geo.ρ_inv_apply G γ⁻¹ (v i)
  rw [hv]

private theorem tr_coneOp (q : ℕ) (γ : Γ) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) (p x : V) :
    G.tr q γ (coneOp p w (G.ρ γ⁻¹ x)) = coneOp (G.ρ γ p) (fun y => G.tr (q + 1) γ (w (G.ρ γ⁻¹ y))) x := by
  let L : (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ≃L[ℝ] (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) :=
    ContinuousLinearEquiv.equivOfInverse (G.tr q γ) (G.tr q γ⁻¹)
      (fun m => tr_tr G q γ⁻¹ γ (inv_mul_cancel γ) m)
      (fun m => tr_tr G q γ γ⁻¹ (mul_inv_cancel γ) m)
  have hL : ∀ m, L m = G.tr q γ m := fun m => rfl
  have key : ∀ f : ℝ → (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)),
      L (∫ t in (0:ℝ)..1, f t) = ∫ t in (0:ℝ)..1, L (f t) := by
    intro f
    simp only [intervalIntegral, map_sub, L.integral_comp_comm]
  have hpt : ∀ t : ℝ, G.ρ γ⁻¹ (G.ρ γ p + t • (x - G.ρ γ p)) = p + t • (G.ρ γ⁻¹ x - p) := by
    intro t
    simp [map_add (f := _), map_smul, map_sub, Geo.ρ_inv_apply]
  rw [← hL]
  unfold coneOp
  rw [key]
  congr 1
  funext t
  rw [map_smul]
  beta_reduce
  rw [hpt]
  congr 1
  ext v
  rw [hL, Geo.tr_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply, Geo.tr_apply]
  congr 2
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [Geo.ρ_inv_apply]
  · intro j
    simp

end

theorem UpperTheory.V.Cj.H.poinOp :
    UpperTheory.V.Cj.H.PoinOp := by
  intro Γ V S _ _ _ _ d G hconv q
  classical
  have hD := coneD V (Fin d → ℂ) G.Y G.isOpen hconv
  let f : V → G.Om (q + 1) → S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ) :=
    fun p w s x => if x ∈ G.Y then coneOp p ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) x else 0
  have hwm : ∀ (w : G.Om (q + 1)) (s : S),
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
        ∀ x ∉ G.Y, (w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s x = 0 := fun w => w.2
  have hf : ∀ p ∈ G.Y, ∀ w, f p w ∈ G.Om q := by
    intro p hp w
    refine fun s => ⟨?_, ?_⟩
    · exact ((hD p hp q _ (hwm w s).1).1).congr (fun x hx => if_pos hx)
    · intro x hx
      exact if_neg hx
  let K : V → G.Om (q + 1) → G.Om q := fun p w => if hp : p ∈ G.Y then ⟨f p w, hf p hp w⟩ else 0
  have hK : ∀ p (hp : p ∈ G.Y) w, ((K p w : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) = f p w := by
    intro p hp w
    simp [K, hp]
  refine ⟨K, ?_, ?_, ?_⟩
  · intro p hp w hw0
    apply Subtype.ext
    funext s x
    by_cases hx : x ∈ G.Y
    · rw [Geo.dOm_apply G (K p w) s hx, hK p hp w]
      have hclosed : ∀ y ∈ G.Y, extDeriv ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) y = 0 := by
        intro y hy
        have h0 := congrArg
          (fun u : G.Om (q + 1 + 1) => (u : S → V → V [⋀^Fin (q + 1 + 1)]→L[ℝ] (Fin d → ℂ)) s y) hw0
        rw [Geo.dOm_apply G w s hy] at h0
        simpa using h0
      have hloc : extDeriv (f p w s) x =
          extDeriv (coneOp p ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s)) x := by
        rw [← extDerivWithin_univ, ← extDerivWithin_univ]
        apply Filter.EventuallyEq.extDerivWithin_eq_of_mem _ (Set.mem_univ x)
        rw [nhdsWithin_univ]
        exact Filter.eventually_of_mem (G.isOpen.mem_nhds hx) (fun y hy => if_pos hy)
      rw [hloc]
      exact (hD p hp q _ (hwm w s).1).2 hclosed x hx
    · have h1 := ((G.dOm q (K p w)).2 s).2 x hx
      have h2 := (hwm w s).2 x hx
      rw [h1, h2]
  · intro γ p hp w
    have hp' : G.ρ γ p ∈ G.Y := G.maps γ p hp
    apply Subtype.ext
    funext s x
    show G.tr q γ (((K p w : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x)) =
      ((K (G.ρ γ p) (G.act (q + 1) γ w) : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x
    rw [hK p hp, hK _ hp']
    by_cases hx : x ∈ G.Y
    · have hx' : G.ρ γ⁻¹ x ∈ G.Y := G.maps γ⁻¹ x hx
      simp only [f, if_pos hx, if_pos hx']
      exact tr_coneOp G q γ _ p x
    · have hx' : G.ρ γ⁻¹ x ∉ G.Y := by
        intro h
        apply hx
        have h2 := G.maps γ _ h
        have h3 := Geo.ρ_inv_apply G γ⁻¹ x
        rw [inv_inv] at h3
        rwa [h3] at h2
      simp only [f, if_neg hx, if_neg hx', map_zero]
  · intro p hp w hw s C hC hCc
    have h := coneLim V (Fin d → ℂ) G.Y hconv p hp q
      (fun k => ((w k : G.Om (q + 1)) : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s)
      (fun C' hC' hC'c => hw s C' hC' hC'c) C hC hCc
    refine h.congr ?_
    filter_upwards with k
    intro x hx
    rw [hK p hp]
    simp [f, hC hx]
end
end
