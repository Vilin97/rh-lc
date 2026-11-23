module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.ExistsNearSmooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.KsetMulConj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.SigLamSmoothOfGenSub
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.SumFlatMapMap
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DSWSigLamCoe

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

section Gen

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem nuJ_nonneg (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Ws : List (List (Matrix (Fin n) (Fin n) ℂ)))
    (v : H) : 0 ≤ nuJ σ Ws v := by
  unfold nuJ
  apply List.sum_nonneg
  intro a ha
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 ha
  exact norm_nonneg _

theorem nuJ_cons_nil (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Ws : List (List (Matrix (Fin n) (Fin n) ℂ)))
    (v : H) : nuJ σ ([] :: Ws) v = ‖v‖ + nuJ σ Ws v := by
  simp [nuJ, dSW]

theorem nuJ_le_add_of (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (a b c : H) :
    ∀ Ws : List (List (Matrix (Fin n) (Fin n) ℂ)),
      (∀ w ∈ Ws, ‖dSW σ w a‖ ≤ ‖dSW σ w b‖ + ‖dSW σ w c‖) → nuJ σ Ws a ≤ nuJ σ Ws b + nuJ σ Ws c
  | [], _ => by simp [nuJ]
  | w :: Ws, h => by
    have h1 := h w List.mem_cons_self
    have h2 := nuJ_le_add_of σ a b c Ws (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))
    simp only [nuJ, List.map_cons, List.sum_cons] at h2 ⊢
    linarith

theorem NE_nonneg' {D : Submodule ℂ H} (E : Fin n → Fin n → Module.End ℂ D) (j : ℕ) (x : D) : 0 ≤ NE E j x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

end Gen

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem dS_sigLam_coe (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (y : Hlam ε Ψ v₀) :
    ((dS (sigLam ε Ψ v₀) X y : Hlam ε Ψ v₀) : L2 ε) = dS (rreg ε) X (y : L2 ε) := by
  unfold dS
  set f : ℝ → Hlam ε Ψ v₀ := fun t => sigLam ε Ψ v₀ (NormedSpace.exp ((t : ℂ) • X)) y with hfdef
  have hf : (fun t : ℝ => rreg ε (NormedSpace.exp ((t : ℂ) • X)) (y : L2 ε)) = fun t => ((f t : Hlam ε Ψ v₀) : L2 ε) := by
    funext t
    rw [hfdef, sigLam_coe hgap hP hv₀ (exp_smul_mem_UJset hX t)]
  rw [hf]
  let Ir : Hlam ε Ψ v₀ →L[ℝ] L2 ε := ((Hlam ε Ψ v₀).subtypeL).restrictScalars ℝ
  let Pr : L2 ε →L[ℝ] Hlam ε Ψ v₀ := ((Hlam ε Ψ v₀).orthogonalProjectionOnto).restrictScalars ℝ
  by_cases hd : DifferentiableAt ℝ f 0
  · exact ((Ir.hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hd.hasDerivAt).deriv).symm
  · have hd' : ¬ DifferentiableAt ℝ (fun t => ((f t : Hlam ε Ψ v₀) : L2 ε)) 0 := by
      intro h
      apply hd
      have h2 := Pr.differentiableAt.comp (0 : ℝ) h
      have e : (Pr ∘ fun t => ((f t : Hlam ε Ψ v₀) : L2 ε)) = f := by
        funext t
        exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (f t)
      rw [e] at h2
      exact h2
    have h0 : deriv f 0 = 0 := deriv_zero_of_not_differentiableAt hd
    have h1 : deriv (fun t => ((f t : Hlam ε Ψ v₀) : L2 ε)) 0 = 0 := deriv_zero_of_not_differentiableAt hd'
    exact (congrArg Subtype.val h0).trans h1.symm

theorem dSW_sigLam_coe (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∀ (w : List (Matrix (Fin n) (Fin n) ℂ)), (∀ X ∈ w, inG ε X) → ∀ y : Hlam ε Ψ v₀,
      ((dSW (sigLam ε Ψ v₀) w y : Hlam ε Ψ v₀) : L2 ε) = dSW (rreg ε) w (y : L2 ε)
  | [], _, _ => rfl
  | X :: w, hw, y => by
    simp only [dSW]
    rw [dS_sigLam_coe hgap hP hv₀ (hw X List.mem_cons_self),
      dSW_sigLam_coe hgap hP hv₀ w (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) y]

theorem nuJ_sigLam_coe (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    {Ws : List (List (Matrix (Fin n) (Fin n) ℂ))} (hWs : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X) (y : Hlam ε Ψ v₀) :
    nuJ (rreg ε) Ws (y : L2 ε) = nuJ (sigLam ε Ψ v₀) Ws y := by
  unfold nuJ
  congr 1
  refine List.map_congr_left fun w hw => ?_
  rw [← dSW_sigLam_coe hgap hP hv₀ w (hWs w hw) y, Submodule.coe_norm]

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJSigLam

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem decBoundJ_sigLam {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hlam : S7.IsHCParam lam) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (m N : ℕ)
    (hM : ∃ C : ℝ, ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∀ g ∈ UJset ε,
        Real.sqrt (S7.hs g) ^ m * ‖inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε))‖ ≤
          C * NE (smE ε (rreg ε)) N x * NE (smE ε (rreg ε)) N y) :
    DecBoundJ ε (sigLam ε Ψ v₀) m N := by
  obtain ⟨C, hC⟩ := hM
  obtain ⟨Ws, C', hWs, hNE⟩ := NE_le_nuJ (rreg_isURepOn ε) N
  have hU : IsURepOn (UJset ε) (sigLam ε Ψ v₀) := sigLam_isURepOn hgap hP hv₀
  have hWsG : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X := fun w hw => (hWs w hw).2
  have hVs : ∀ w ∈ ([] :: Ws), w.length ≤ N ∧ ∀ X ∈ w, inG ε X := by
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · simp
    · exact hWs w hw
  have hVsG : ∀ w ∈ ([] :: Ws), ∀ X ∈ w, inG ε X := fun w hw => (hVs w hw).2
  have hnn : ∀ z : Hlam ε Ψ v₀, 0 ≤ nuJ (sigLam ε Ψ v₀) ([] :: Ws) z := fun z =>
    nuJ_nonneg _ _ _
  have hnorm : ∀ z : Hlam ε Ψ v₀, ‖z‖ ≤ nuJ (sigLam ε Ψ v₀) ([] :: Ws) z := by
    intro z
    rw [nuJ_cons_nil]
    linarith [nuJ_nonneg (sigLam ε Ψ v₀) Ws z]
  have hC₁ : 0 ≤ max C' 0 := le_max_right _ _
  have hK : 0 ≤ max C 0 * max C' 0 * max C' 0 :=
    mul_nonneg (mul_nonneg (le_max_right _ _) hC₁) hC₁
  have hNE' : ∀ (x : smD ε (rreg ε)) (hx : ((x : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀),
      NE (smE ε (rreg ε)) N x ≤
        max C' 0 * nuJ (sigLam ε Ψ v₀) ([] :: Ws) (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀) := by
    intro x hx
    have h1 := hNE x
    have h2 : nuJ (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε) =
        nuJ (sigLam ε Ψ v₀) Ws (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀) :=
      nuJ_sigLam_coe hgap hP hv₀ hWsG (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀)
    have h3 := nuJ_nonneg (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε)
    have h4 : nuJ (sigLam ε Ψ v₀) ([] :: Ws) (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀) =
        ‖(⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀)‖ +
          nuJ (sigLam ε Ψ v₀) Ws (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀) :=
      nuJ_cons_nil _ _ _
    rw [h4, ← h2]
    calc NE (smE ε (rreg ε)) N x ≤ C' * nuJ (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε) := h1
      _ ≤ max C' 0 * nuJ (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h3
      _ ≤ max C' 0 * (‖(⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀)‖ +
            nuJ (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) hC₁
  have hfin : ∀ (x : smD ε (rreg ε)), x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) →
      ∀ (hx : ((x : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀),
      ∀ (y : smD ε (rreg ε)), y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) →
      ∀ (hy : ((y : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀), ∀ g ∈ UJset ε,
        Real.sqrt (S7.hs g) ^ m *
            ‖inner ℂ (⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩ : Hlam ε Ψ v₀)
              (sigLam ε Ψ v₀ g ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩)‖ ≤
          max C 0 * max C' 0 * max C' 0 *
            nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ *
            nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩ := by
    intro x hxg hx y hyg hy g hg
    have he : inner ℂ (⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩ : Hlam ε Ψ v₀)
        (sigLam ε Ψ v₀ g ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩) =
        inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε)) := by
      rw [Submodule.coe_inner, sigLam_coe hgap hP hv₀ hg]
    rw [he]
    have hb := hC x hxg y hyg g hg
    have hx0 := NE_nonneg' (smE ε (rreg ε)) N x
    have hy0 := NE_nonneg' (smE ε (rreg ε)) N y
    have hxb := hNE' x hx
    have hyb := hNE' y hy
    calc _ ≤ C * NE (smE ε (rreg ε)) N x * NE (smE ε (rreg ε)) N y := hb
      _ ≤ max C 0 * NE (smE ε (rreg ε)) N x * NE (smE ε (rreg ε)) N y :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0) hy0
      _ ≤ max C 0 * (max C' 0 * nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩) *
            (max C' 0 * nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩) := by
          have hm := le_max_right C 0
          exact mul_le_mul (mul_le_mul_of_nonneg_left hxb hm) hyb hy0
            (mul_nonneg hm (mul_nonneg hC₁ (hnn _)))
      _ = _ := by ring
  refine ⟨max C 0 * max C' 0 * max C' 0, [] :: Ws, hVs, ?_⟩
  intro u v hu hv g hg
  have hA : 0 ≤ Real.sqrt (S7.hs g) ^ m := pow_nonneg (Real.sqrt_nonneg _) _
  have hiso : ∀ z : Hlam ε Ψ v₀, ‖sigLam ε Ψ v₀ g z‖ = ‖z‖ := fun z => hU.2.1 g hg z
  have hnear : ∀ (w : Hlam ε Ψ v₀), IsSmoothVecU ε (sigLam ε Ψ v₀) w → ∀ (e : ℝ), 0 < e →
      ∃ (x : smD ε (rreg ε)) (_ : x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))
        (hx : ((x : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀),
        ‖w - ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩‖ ≤ e ∧
        nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ ≤
          nuJ (sigLam ε Ψ v₀) ([] :: Ws) w + e := by
    intro w hw e he
    obtain ⟨x, hxg, hx, hlt⟩ := exists_near_smooth hlam hgap hP hv₀ ([] :: Ws) hVsG w hw he
    refine ⟨x, hxg, hx, (hnorm _).trans hlt.le, ?_⟩
    have hxs := sigLam_smooth_of_genSub (ε := ε) (Ψ := Ψ) (v₀ := v₀) hx
    have htri := nuJ_le_add_of (sigLam ε Ψ v₀) ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ w
      (w - ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩) ([] :: Ws) (by
        intro W hW
        rw [dSW_sub hU (hVsG W hW) hw hxs]
        set a := dSW (sigLam ε Ψ v₀) W w
        set b := dSW (sigLam ε Ψ v₀) W ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩
        calc ‖b‖ = ‖a - (a - b)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖a‖ + ‖a - b‖ := norm_sub_le _ _)
    linarith
  have hbound : ∀ e : ℝ, 0 < e →
      Real.sqrt (S7.hs g) ^ m * ‖inner ℂ v (sigLam ε Ψ v₀ g u)‖ ≤
        Real.sqrt (S7.hs g) ^ m * (e * ‖u‖ + (‖v‖ + e) * e) +
          max C 0 * max C' 0 * max C' 0 * (nuJ (sigLam ε Ψ v₀) ([] :: Ws) u + e) *
            (nuJ (sigLam ε Ψ v₀) ([] :: Ws) v + e) := by
    intro e he
    obtain ⟨x, hxg, hx, hux, hnx⟩ := hnear u hu e he
    obtain ⟨y, hyg, hy, hvy, hny⟩ := hnear v hv e he
    set x' : Hlam ε Ψ v₀ := ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ with hx'
    set y' : Hlam ε Ψ v₀ := ⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩ with hy'
    have hsplit : inner ℂ v (sigLam ε Ψ v₀ g u) =
        inner ℂ (v - y') (sigLam ε Ψ v₀ g u) +
          (inner ℂ y' (sigLam ε Ψ v₀ g (u - x')) + inner ℂ y' (sigLam ε Ψ v₀ g x')) := by
      rw [map_sub, inner_sub_left, inner_sub_right]
      ring
    have h1 : ‖inner ℂ (v - y') (sigLam ε Ψ v₀ g u)‖ ≤ e * ‖u‖ := by
      calc _ ≤ ‖v - y'‖ * ‖sigLam ε Ψ v₀ g u‖ := norm_inner_le_norm _ _
        _ = ‖v - y'‖ * ‖u‖ := by rw [hiso]
        _ ≤ e * ‖u‖ := mul_le_mul_of_nonneg_right hvy (norm_nonneg _)
    have hy'n : ‖y'‖ ≤ ‖v‖ + e := by
      calc ‖y'‖ = ‖v - (v - y')‖ := by rw [sub_sub_cancel]
        _ ≤ ‖v‖ + ‖v - y'‖ := norm_sub_le _ _
        _ ≤ ‖v‖ + e := by linarith
    have h2 : ‖inner ℂ y' (sigLam ε Ψ v₀ g (u - x'))‖ ≤ (‖v‖ + e) * e := by
      calc _ ≤ ‖y'‖ * ‖sigLam ε Ψ v₀ g (u - x')‖ := norm_inner_le_norm _ _
        _ = ‖y'‖ * ‖u - x'‖ := by rw [hiso]
        _ ≤ (‖v‖ + e) * e := mul_le_mul hy'n hux (norm_nonneg _) (by linarith [norm_nonneg v])
    have h3 := hfin x hxg hx y hyg hy g hg
    have h3' : Real.sqrt (S7.hs g) ^ m * ‖inner ℂ y' (sigLam ε Ψ v₀ g x')‖ ≤
        max C 0 * max C' 0 * max C' 0 * (nuJ (sigLam ε Ψ v₀) ([] :: Ws) u + e) *
          (nuJ (sigLam ε Ψ v₀) ([] :: Ws) v + e) := by
      refine h3.trans ?_
      exact mul_le_mul (mul_le_mul_of_nonneg_left hnx hK) hny (hnn _)
        (mul_nonneg hK (by linarith [hnn u]))
    rw [hsplit]
    calc _ ≤ Real.sqrt (S7.hs g) ^ m * (‖inner ℂ (v - y') (sigLam ε Ψ v₀ g u)‖ +
            (‖inner ℂ y' (sigLam ε Ψ v₀ g (u - x'))‖ + ‖inner ℂ y' (sigLam ε Ψ v₀ g x')‖)) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))) hA
      _ = Real.sqrt (S7.hs g) ^ m * (‖inner ℂ (v - y') (sigLam ε Ψ v₀ g u)‖ +
            ‖inner ℂ y' (sigLam ε Ψ v₀ g (u - x'))‖) +
            Real.sqrt (S7.hs g) ^ m * ‖inner ℂ y' (sigLam ε Ψ v₀ g x')‖ := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hA) h3'
  have hlim : Filter.Tendsto (fun e : ℝ => Real.sqrt (S7.hs g) ^ m * (e * ‖u‖ + (‖v‖ + e) * e) +
        max C 0 * max C' 0 * max C' 0 * (nuJ (sigLam ε Ψ v₀) ([] :: Ws) u + e) *
          (nuJ (sigLam ε Ψ v₀) ([] :: Ws) v + e))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (max C 0 * max C' 0 * max C' 0 * nuJ (sigLam ε Ψ v₀) ([] :: Ws) u *
        nuJ (sigLam ε Ψ v₀) ([] :: Ws) v)) := by
    have hc : Continuous (fun e : ℝ => Real.sqrt (S7.hs g) ^ m * (e * ‖u‖ + (‖v‖ + e) * e) +
        max C 0 * max C' 0 * max C' 0 * (nuJ (sigLam ε Ψ v₀) ([] :: Ws) u + e) *
          (nuJ (sigLam ε Ψ v₀) ([] :: Ws) v + e)) := by
      fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun e he => hbound e he)

end ReciprocityTheory.ChartRestriction.DS.DecInf
end
end
end
