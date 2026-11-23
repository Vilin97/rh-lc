module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaC
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsKfin
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaI
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaL
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ClosureK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ExistsExpEqOfMemKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Taylor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RightDerivativeToL2

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaL

section

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem tf_kstable_fin (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V0 : Submodule ℂ D}
    (hVf : FiniteDimensional ℂ V0) (hVK : IsKStableSub ε E V0) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {v : D} (hv : v ∈ V0) : σ k (v : H) ∈ V0.map D.subtype := by
  apply ReciprocityTheory.ChartRestriction.DS.tf_kstable_fin <;> assumption

theorem tf_tensGrp_kDiag (dual : Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (f : Fin n → H) :
    tensGrp dual σ k f = kDiag dual σ k f := by
  have hu : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hu
  funext c
  simp only [tensGrp, kDiag, hinv, Matrix.conjTranspose_apply]

theorem tf_kirr_map {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    {E₁ : Fin n → Fin n → Module.End ℂ M} {E₂ : Fin n → Fin n → Module.End ℂ M'} {Λ : Fin n → ℝ}
    {V : Submodule ℂ M} (hV : IsKIrrHW ε E₁ Λ V) (Ψ : M →ₗ[ℂ] M')
    (hΨ : ∀ a b, ∀ x ∈ V, Ψ (E₁ a b x) = E₂ a b (Ψ x)) (hinj : ∀ x ∈ V, Ψ x = 0 → x = 0) :
    IsKIrrHW ε E₂ Λ (V.map Ψ) := by
  apply ReciprocityTheory.ChartRestriction.DS.tf_kirr_map <;> assumption

theorem tf_kfin_tens (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    (hVf : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V) {f : Fin n → D} (hf : f ∈ tensSub (genSub E V)) :
    ∃ W : Submodule ℂ (Fin n → D), FiniteDimensional ℂ W ∧ f ∈ W ∧ W ≤ tensSub (genSub E V) ∧
      ∀ k ∈ Kset ε, ∀ w ∈ W, ∃ w' ∈ W,
        (fun c => ((w' c : D) : H)) = kDiag dual σ k (fun c => ((w c : D) : H)) := by
  apply ReciprocityTheory.ChartRestriction.DS.tf_kfin_tens <;> assumption

section Datum

variable [CompleteSpace H]

theorem tf_phi (dual : Bool) {lam : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v) {V : Submodule ℂ D} (hgap : StdGap ε lam)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) {y : D} (hy : y ∈ genSub E V) :
    ∃ Φ : tensSub (n := n) (genSub E V) →ₗ[ℂ] smD ε (tfRdiag ε),
      (∀ f, ((Φ f : smD ε (tfRdiag ε)) : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((f.1 c : D) : H))) ∧
      ∀ a b (f : tensSub (n := n) (genSub E V)), smE ε (tfRdiag ε) a b (Φ f) =
        Φ ⟨tensF dual E a b f.1, tensSub_stable dual a b f.1 f.2⟩ := by
  have hce := fun c f hf => coef_embed dual hσ hD hsm hgap hV hc hVK hW _
    (tf_single_smul_mem c (tfSgn ε c) hy) f hf
  simp only [tf_coe_single] at hce
  let Φ : tensSub (n := n) (genSub E V) →ₗ[ℂ] smD ε (tfRdiag ε) :=
    { toFun := fun f => ⟨tfPh dual ε σ (y : H) (fun c => ((f.1 c : D) : H)),
        tfRdiag_smooth fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1⟩
      map_add' := fun f f' => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_add_smooth ε ((hce c f.1 f.2).1.2 []) ((hce c f'.1 f'.2).1.2 []))
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        simp [coefMap, tensGrp, sum_add_distrib])
      map_smul' := fun a f => Subtype.ext (vectorL2_ext fun c => by
        refine Eq.trans ?_ (toL2_smul_smooth ε a _)
        refine toL2_congr_of_eq_on_UJset fun g _ => ?_
        simp only [coefMap, tensGrp, Submodule.coe_smul, Pi.smul_apply, map_smul,
          smul_comm _ a, ← Finset.smul_sum, inner_smul_right, smul_eq_mul, ← Finset.mul_sum]) }
  refine ⟨Φ, fun f => rfl, fun a b f => Subtype.ext (vectorL2_ext fun c => ?_)⟩
  refine (tfRdiag_smE (fun c => toL2_mem_smD_of_isSmoothL2 (hce c f.1 f.2).1) a b c).trans ?_
  refine (rightDerivative_toL2 (hce c f.1 f.2).1 a b).trans (toL2_congr_of_eq_on_UJset fun g hg => ?_)
  exact (hce c f.1 f.2).2.1 a b g hg

end Datum

end ReciprocityTheory.ChartRestriction.DS.G2
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaM

section

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem tf_datum2 (dual : Bool) {lam lam' : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v) {V : Submodule ℂ D} (hgap : StdGap ε lam)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d) {y : D} (hy : y ∈ genSub E V)
    (hy0 : (y : H) ≠ 0) {V' : Submodule ℂ D} (hV' : IsKIrrHW ε E (lowK ε lam') V')
    (hc' : ∀ v ∈ V', casimir E v = (casVal lam' : ℂ) • v)
    (hVK' : ∀ k ∈ Kset ε, ∀ v ∈ V', ∃ w ∈ V', (w : H) = σ k v)
    {ι : D →ₗ[ℂ] (Fin n → D)} (hι : IsGKEmb dual ε σ E (genSub E V) (genSub E V') ι) :
    ∃ V₂ : Submodule ℂ (smD ε (tfRdiag ε)), IsKIrrHW ε (smE ε (tfRdiag ε)) (lowK ε lam') V₂ ∧
      (∀ v ∈ V₂, casimir (smE ε (tfRdiag ε)) v = (casVal lam' : ℂ) • v) ∧
      (∀ k ∈ Kset ε, ∀ v ∈ V₂, ∃ w ∈ V₂, (w : tfL2n ε) = tfRdiag ε k v) ∧ V₂ ≠ ⊥ ∧
      (∀ v ∈ genSub (smE ε (tfRdiag ε)) V₂, ∃ x ∈ genSub E V',
        (v : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H))) ∧
      (∀ x ∈ genSub E V', ∃ v ∈ genSub (smE ε (tfRdiag ε)) V₂,
        (v : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H))) := by
  obtain ⟨Φ, hΦ, hΦE⟩ := tf_phi dual hσ hD hsm hgap hV hc hVK hW hy
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (tensSub (n := n) (genSub E V))
  let π := Submodule.projectionOnto _ q hq
  let Ψ : D →ₗ[ℂ] smD ε (tfRdiag ε) := Φ ∘ₗ π ∘ₗ ι
  have hΨ : ∀ x (hx : x ∈ genSub E V'), Ψ x = Φ ⟨ι x, hι.1 x hx⟩ := by
    intro x hx
    show Φ (π (ι x)) = _
    congr 1
    exact Submodule.projectionOnto_apply_left hq ⟨ι x, hι.1 x hx⟩
  have hΨc : ∀ x ∈ genSub E V', (Ψ x : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H)) :=
    fun x hx => by rw [hΨ x hx, hΦ]
  have hΨE : ∀ a b, ∀ x ∈ genSub E V', Ψ (E a b x) = smE ε (tfRdiag ε) a b (Ψ x) := by
    intro a b x hx
    rw [hΨ _ (tset_genSub_E E V' a b hx), hΨ x hx, hΦE]
    congr 1
    exact Subtype.ext (hι.2.2.1 a b x hx)
  have hV'le : V' ≤ genSub E V' := fun x hx => Submodule.mem_sInf.mpr fun _ hT => hT.1 hx
  have hinj : ∀ x ∈ genSub E V', Ψ x = 0 → x = 0 := by
    intro x hx h
    have h1 : tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H)) = 0 := by
      rw [← hΨc x hx, h]; rfl
    exact hι.2.1 x hx (tf_ph_inj dual hσ hD hsm hgap hV hc hVK hW hd hy hy0 (hι.1 x hx) h1)
  have hK2 := tf_kirr_map hV' Ψ (fun a b x hx => hΨE a b x (hV'le hx)) (fun x hx => hinj x (hV'le hx))
  refine ⟨V'.map Ψ, hK2, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxG := hV'le hx
    have e : casimir (smE ε (tfRdiag ε)) (Ψ x) = Ψ (casimir E x) := by

      simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [hΨE a b _ (tset_genSub_E E V' b a hxG), hΨE b a x hxG]
    rw [e, hc' x hx, map_smul]
  · rintro k hk _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hxx'⟩ := hVK' k hk x hx
    refine ⟨Ψ x', ⟨x', hx', rfl⟩, ?_⟩
    have hk' : k ∈ UJset ε := closure_inUJ_of_mem_Kset hk
    rw [hΨc x' (hV'le hx'), hΨc x (hV'le hx), tfRdiag_tfPh dual hσ hk', tf_tensGrp_kDiag dual hk,
      ← hι.2.2.2 k hk x (hV'le hx) x' (hV'le hx') hxx']
  · intro h
    obtain ⟨w, hw, hw0, -⟩ := hK2.2.2.2
    apply hw0
    have hwb : w ∈ (⊥ : Submodule ℂ (smD ε (tfRdiag ε))) := h ▸ hw
    exact (Submodule.mem_bot ℂ).1 hwb
  · intro v hv
    have hle : genSub (smE ε (tfRdiag ε)) (V'.map Ψ) ≤ (genSub E V').map Ψ := by
      refine sInf_le ⟨Submodule.map_mono hV'le, ?_⟩
      rintro a b _ ⟨x, hx, rfl⟩
      exact ⟨E a b x, tset_genSub_E E V' a b hx, hΨE a b x hx⟩
    obtain ⟨x, hx, rfl⟩ := hle hv
    exact ⟨x, hx, hΨc x hx⟩
  · intro x hx
    have hle : genSub E V' ≤ (genSub (smE ε (tfRdiag ε)) (V'.map Ψ)).comap Ψ ⊓ genSub E V' := by
      refine sInf_le ⟨fun z hz => ⟨Submodule.mem_sInf.mpr fun _ hT => hT.1 ⟨z, hz, rfl⟩, hV'le hz⟩, ?_⟩
      rintro a b z ⟨hz1, hz2⟩
      refine ⟨?_, tset_genSub_E E V' a b hz2⟩
      show Ψ (E a b z) ∈ genSub (smE ε (tfRdiag ε)) (V'.map Ψ)
      rw [hΨE a b z hz2]
      exact tset_genSub_E _ _ a b hz1
    exact ⟨Ψ x, (hle hx).1, hΨc x hx⟩

theorem tf_eq_case (dual : Bool) {lam lam' : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hsm : ∀ v : D, IsSmoothVecU ε σ v) {V : Submodule ℂ D} (hgap : StdGap ε lam)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg (Formalism.REAL.muG ε) (tfClRep σ (closGen E V)) d) {y : D} (hy : y ∈ genSub E V)
    (hy0 : (y : H) ≠ 0) {P : Module.End ℂ (Fin n → D)} (hP : IsGKEndo dual ε σ E (genSub E V) P)
    {V' : Submodule ℂ D} {ι : D →ₗ[ℂ] (Fin n → D)} (hι : ∀ x ∈ genSub E V', ι x ∈ tensSub (genSub E V))
    (hgap' : StdGap ε lam') {V₂ : Submodule ℂ (smD ε (tfRdiag ε))}
    (hV₂ : IsKIrrHW ε (smE ε (tfRdiag ε)) (lowK ε lam') V₂)
    (hc₂ : ∀ v ∈ V₂, casimir (smE ε (tfRdiag ε)) v = (casVal lam' : ℂ) • v)
    (hVK₂ : ∀ k ∈ Kset ε, ∀ v ∈ V₂, ∃ w ∈ V₂, (w : tfL2n ε) = tfRdiag ε k v)
    (hgen : ∀ v ∈ genSub (smE ε (tfRdiag ε)) V₂, ∃ x ∈ genSub E V',
        (v : tfL2n ε) = tfPh dual ε σ (y : H) (fun c => ((ι x c : D) : H)))
    (hin : ∀ f ∈ tensSub (genSub E V),
      tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H)) ∈ closGen (smE ε (tfRdiag ε)) V₂) :
    ∀ f ∈ tensSub (genSub E V), ∃ x ∈ genSub E V', P f = ι x := by
  obtain ⟨Φ, hΦ, -⟩ := tf_phi dual hσ hD hsm hgap hV hc hVK hW hy
  intro f hf
  obtain ⟨W, hWf, hfW, hWle, hWK⟩ := tf_kfin_tens dual hσ hD hV.1 hV.2.1 hf
  let P' : Module.End ℂ (tensSub (n := n) (genSub E V)) := P.restrict hP.1
  let W' : Submodule ℂ (tensSub (n := n) (genSub E V)) := W.comap (tensSub (genSub E V)).subtype
  have hW'f : FiniteDimensional ℂ W' := Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe hWle).symm
  let S0 : Submodule ℂ (tfL2n ε) := W'.map ((smD ε (tfRdiag ε)).subtype ∘ₗ Φ ∘ₗ P')
  have hS0v : ∀ w : tensSub (n := n) (genSub E V),
      ((smD ε (tfRdiag ε)).subtype ∘ₗ Φ ∘ₗ P') w = tfPh dual ε σ (y : H) (fun c => ((P w.1 c : D) : H)) :=
    fun w => hΦ (P' w)
  have hS0 : S0 ≤ closGen (smE ε (tfRdiag ε)) V₂ := by
    rintro _ ⟨w, -, rfl⟩
    rw [hS0v]
    exact hin w.1 w.2
  have hS0f : FiniteDimensional ℂ S0 := Module.Finite.map _ _
  have hS0K : ∀ k ∈ Kset ε, ∀ x ∈ S0, tfRdiag ε k x ∈ S0 := by
    rintro k hk _ ⟨w, hw, rfl⟩
    obtain ⟨w', hw', hww'⟩ := hWK k hk w.1 hw
    refine ⟨⟨w', hWle hw'⟩, hw', ?_⟩
    rw [hS0v, hS0v, tfRdiag_tfPh dual hσ (closure_inUJ_of_mem_Kset hk), tf_tensGrp_kDiag dual hk,
      hP.2.2 k hk w.1 w.2 w' (hWle hw') hww']
  have hkf := data_kfin_le hgap' (tfRdiag_isURepOn ε) (isDerivedOn_smE (tfRdiag_isURepOn ε)) hV₂ hc₂ hVK₂
    S0 hS0 hS0f hS0K
  have hfS0 : tfPh dual ε σ (y : H) (fun c => ((P f c : D) : H)) ∈ S0 :=
    ⟨⟨f, hf⟩, hfW, hS0v ⟨f, hf⟩⟩
  obtain ⟨v, hv, hve⟩ := hkf hfS0
  obtain ⟨x, hx, hxe⟩ := hgen v hv
  refine ⟨x, hx, ?_⟩
  have hd0 : (P f - ι x) ∈ tensSub (genSub E V) := Submodule.sub_mem _ (hP.1 f hf) (hι x hx)
  have e1 : Φ ⟨P f - ι x, hd0⟩ = Φ ⟨P f, hP.1 f hf⟩ - Φ ⟨ι x, hι x hx⟩ := by
    rw [← map_sub]; rfl
  have h0 : tfPh dual ε σ (y : H) (fun c => (((P f - ι x) c : D) : H)) = 0 := by
    calc tfPh dual ε σ (y : H) (fun c => (((P f - ι x) c : D) : H))
        = ((Φ ⟨P f - ι x, hd0⟩ : smD ε (tfRdiag ε)) : tfL2n ε) := (hΦ ⟨P f - ι x, hd0⟩).symm
      _ = ((Φ ⟨P f, hP.1 f hf⟩ : smD ε (tfRdiag ε)) : tfL2n ε) -
          ((Φ ⟨ι x, hι x hx⟩ : smD ε (tfRdiag ε)) : tfL2n ε) := by rw [e1, Submodule.coe_sub]
      _ = 0 := by
        rw [sub_eq_zero]
        exact ((hΦ ⟨P f, hP.1 f hf⟩).trans hve.symm).trans (hxe.trans (hΦ ⟨ι x, hι x hx⟩).symm)
  exact sub_eq_zero.1 (tf_ph_inj dual hσ hD hsm hgap hV hc hVK hW hd hy hy0 hd0 h0)

end ReciprocityTheory.ChartRestriction.DS.G2
end
end
end
