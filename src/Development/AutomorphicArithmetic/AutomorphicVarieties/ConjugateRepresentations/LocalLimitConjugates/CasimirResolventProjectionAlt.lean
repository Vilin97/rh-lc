module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AbsProj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasSym
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ClFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CommOfZalg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.GardFacts
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ClFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.IsOpenMapVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestBump
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestOps
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Approx

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.approx :
    UpperTheory.V.Cj.H.Approx := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ F hF
  by_contra hF0
  have hpos : 0 < ‖F‖ := norm_pos_iff.mpr hF0
  have hcont := GlobalTheory.AutomorphicL2Unitary.continuous_R (Γ := Γ) (μ := μ) F
  obtain ⟨f, hfc, hfs, hfr, hf1, hfW, hfF⟩ :=
    hF {g | ‖GlobalTheory.AutomorphicL2Unitary.R Γ μ g F - F‖ < ‖F‖ / 2} (by
      apply (isOpen_lt (continuous_norm.comp (hcont.sub continuous_const))
        continuous_const).mem_nhds
      show ‖GlobalTheory.AutomorphicL2Unitary.R Γ μ 1 F - F‖ < ‖F‖ / 2
      rw [map_one, ContinuousLinearMap.one_apply, sub_self, norm_zero]
      positivity)
  have hfre : ∀ y, f y = ((f y).re : ℂ) := by
    intro y
    obtain ⟨t, _, ht⟩ := hfr y
    rw [ht, Complex.ofReal_re]
  have hfnn : ∀ y, 0 ≤ (f y).re := by
    intro y
    obtain ⟨t, ht0, ht⟩ := hfr y
    rw [ht, Complex.ofReal_re]
    exact ht0
  have hint : MeasureTheory.Integrable f μ := hfc.integrable_of_hasCompactSupport hfs
  have hrep := (GlobalTheory.AutomorphicL2Unitary.isRepOp_Rop (Γ := Γ) (μ := μ) hint) F
  have hφ := hrep.1
  have hzero : ∫ g, f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F ∂μ = 0 := hrep.2.symm.trans hfF
  have hI : ∫ g, RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)) ∂μ = 0 := by
    rw [integral_re (hφ.const_inner F), integral_inner hφ F, hzero, inner_zero_right]
    simp
  have hbound : ∀ g, ‖F‖ ^ 2 / 2 * (f g).re
      ≤ RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)) := by
    intro g
    have hre : RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F))
        = (f g).re * (inner ℂ F (GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)).re := by
      rw [inner_smul_right]
      conv_lhs => rw [hfre g]
      simp
    rw [hre]
    by_cases hg : ‖GlobalTheory.AutomorphicL2Unitary.R Γ μ g F - F‖ < ‖F‖ / 2
    · have e1 : inner ℂ F (GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)
          = inner ℂ F F - inner ℂ F (F - GlobalTheory.AutomorphicL2Unitary.R Γ μ g F) := by
        rw [inner_sub_right]
        ring
      have e2 : (inner ℂ F F).re = ‖F‖ ^ 2 := by
        simpa using inner_self_eq_norm_sq (𝕜 := ℂ) F
      have e3 := re_inner_le_norm (𝕜 := ℂ) F (F - GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)
      rw [norm_sub_rev] at e3
      have e4 : ‖F‖ ^ 2 / 2 ≤ (inner ℂ F (GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)).re := by
        rw [e1, Complex.sub_re, e2]
        have e3' : (inner ℂ F (F - GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)).re ≤ ‖F‖ * (‖F‖ / 2) := by
          simp only [RCLike.re_to_complex] at e3
          exact e3.trans (mul_le_mul_of_nonneg_left hg.le (norm_nonneg F))
        nlinarith
      have h5 := mul_le_mul_of_nonneg_left e4 (hfnn g)
      linarith
    · have h0 : f g = 0 := hfW g hg
      rw [h0]
      simp
  have hpos2 : 0 < ∫ g, (f g).re ∂μ :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (Complex.continuous_re.comp hfc) (hfs.comp_left Complex.zero_re) (fun y => hfnn y)
      (by
        intro h
        apply hf1
        rw [hfre 1, h, Complex.ofReal_zero])
  have hmono : ∫ g, ‖F‖ ^ 2 / 2 * (f g).re ∂μ
      ≤ ∫ g, RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)) ∂μ :=
    MeasureTheory.integral_mono (hint.re.const_mul _) ((hφ.const_inner F).re) hbound
  rw [hI, MeasureTheory.integral_const_mul] at hmono
  have h6 : 0 < ‖F‖ ^ 2 / 2 * ∫ g, (f g).re ∂μ := mul_pos (by positivity) hpos2
  linarith
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.GardSep

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.gardSep :
    UpperTheory.V.Cj.H.GardSep := by
  open scoped Pointwise in
  intro E _ _ _ a μ _ _ W hW h
  rw [Submodule.eq_bot_iff]
  intro F hF
  refine approx (GA E a) (latticeGL E a) μ F fun U hU => ?_
  have hU' : (interior U)⁻¹ ∈ 𝓝 (1 : GA E a) := inv_mem_nhds_one _ (interior_mem_nhds.2 hU)
  obtain ⟨ψ, hψ, hpos, hne, hout⟩ := testBump E a {1} (interior U)⁻¹ isCompact_singleton isOpen_interior.inv
    (Set.singleton_subset_iff.2 (mem_of_mem_nhds hU'))
  have hc : Continuous ψ.1 := ((testOps E a ψ).1 hψ.2).1
  have hc' : Continuous fun y => ψ.1 y⁻¹ := hc.comp continuous_inv
  have hs : HasCompactSupport fun y => ψ.1 y⁻¹ := hψ.1.comp_homeomorph (Homeomorph.inv (GA E a))
  refine ⟨fun y => ψ.1 y⁻¹, hc', hs, fun y => hpos _, by simpa using hne 1 rfl, fun y hy => hout _ ?_, ?_⟩
  · intro hh
    exact hy (interior_subset (by simpa using hh))
  · have e := (clFacts E a μ).2.2.2 ψ ⟨cv ψ.1 F, cvSm E a μ ψ hψ F⟩ F hψ rfl
    rw [← e]
    refine h _ (Submodule.subset_span ⟨ψ, F, hψ, rfl⟩) ?_
    rw [e]
    exact hW.Rop_mem (hc'.integrable_of_hasCompactSupport hs) hF
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjectionAlt

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem transport {G H M : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup M] [Module ℂ M] (R : G →* (H →L[ℂ] H)) (f : M →ₗ[ℂ] H) (hf : Function.Injective f)
    (B : M →ₗ[ℂ] M) (ρ : G → M → M) (hR : ∀ g v, ‖R g v‖ = ‖v‖) (hρ : ∀ g m, f (ρ g m) = R g (f m))
    (hB : ∀ g m, B (ρ g m) = ρ g (B m)) (hs : ∀ m m', inner ℂ (f (B m)) (f m') = inner ℂ (f m) (f (B m')))
    (hW : ∀ W : Submodule ℂ H, GlobalTheory.AutomorphicL2Unitary.IsSubrep R W → (∀ m, f m ∈ W → f m = 0) → W = ⊥) :
    ∃ (P : H →L[ℂ] H) (Q S : ℕ → H →L[ℂ] H), (∀ g w, P (R g w) = R g (P w)) ∧ (∀ k g w, Q k (R g w) = R g (Q k w)) ∧
      (∀ k g w, S k (R g w) = R g (S k w)) ∧ (∀ k m, f m - Q k (f m) = S k (f (B m))) ∧
      (∀ w m, inner ℂ (P w) (f (B m)) = 0) ∧ ∀ w, Tendsto (fun k => Q k w) atTop (𝓝 (P w)) := by
  let ε : M ≃ₗ[ℂ] LinearMap.range f := LinearEquiv.ofInjective f hf
  let A : LinearMap.range f →ₗ[ℂ] LinearMap.range f := ε.toLinearMap ∘ₗ B ∘ₗ ε.symm.toLinearMap
  have hε : ∀ m, (ε m : H) = f m := fun _ => rfl
  have hA : ∀ m, (A (ε m) : H) = f (B m) := fun m => by
    simp only [A, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hε]
  have hD : ∀ g, ∀ v ∈ LinearMap.range f, R g v ∈ LinearMap.range f := by
    rintro g _ ⟨m, rfl⟩
    exact ⟨ρ g m, hρ g m⟩
  obtain ⟨P, Q, S, h1, h2, h3, h4, h5, h6⟩ := absProj G H R (LinearMap.range f) A hD hR
    (by
      intro g v
      obtain ⟨m, rfl⟩ := ε.surjective v
      have : (⟨R g (ε m), hD g _ (ε m).2⟩ : LinearMap.range f) = ε (ρ g m) := Subtype.ext (hρ g m).symm
      rw [this, hA, hA, hB, hρ])
    (by
      intro v w
      obtain ⟨m, rfl⟩ := ε.surjective v
      obtain ⟨m', rfl⟩ := ε.surjective w
      rw [hA, hA, hε, hε, hs])
    (by
      intro W hs h
      refine hW W hs fun m hm => ?_
      have : f m ∈ W ⊓ LinearMap.range f := ⟨hm, m, rfl⟩
      rwa [h, Submodule.mem_bot] at this)
  refine ⟨P, Q, S, h1, h2, h3, fun k m => ?_, fun w m => ?_, h6⟩
  · rw [← hA]; exact h4 k (ε m)
  · rw [← hA]; exact h5 w (ε m)

theorem UpperTheory.V.Cj.H.casimir_resolvent_projection :
    UpperTheory.V.Cj.H.CasimirResolventProjection := by
  intro E _ _ _ a ha μ _ _ n e he c
  have hg := gardFacts E a ha μ
  obtain ⟨c1, c2, c3, -⟩ := clFacts E a μ
  obtain ⟨-, o2, o3⟩ := casOp E a n e he 0 c
  have hm : ∀ φ ∈ gard μ, casA 0 c e φ ∈ gard μ := (o3 (gard μ) fun X φ h => (hg φ h).2.2.2.1 X).1
  let f : gard μ →ₗ[ℂ] HL μ :=
    { toFun := fun φ => cl μ φ.1
      map_add' := fun φ ψ => by
        have := (c1 φ.1 ψ.1 1 1 (hg _ φ.2).2.1 (hg _ ψ.2).2.1).2
        simpa only [one_smul, Submodule.coe_add] using this
      map_smul' := fun s φ => by
        have := (c1 φ.1 φ.1 s 0 (hg _ φ.2).2.1 (hg _ φ.2).2.1).2
        simpa only [zero_smul, add_zero, Submodule.coe_smul, RingHom.id_apply] using this }
  have hf : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro φ h
    exact Subtype.ext (c2 φ.1 (hg _ φ.2).1 (hg _ φ.2).2.1 h)
  obtain ⟨P, Q, S, h1, h2, h3, h4, h5, h6⟩ := transport (GlobalTheory.AutomorphicL2Unitary.R (latticeGL E a) μ) f hf
    ((casA 0 c e).restrict hm) (fun g φ => ⟨rt E a g φ.1, (hg _ φ.2).2.2.2.2 g⟩)
    (fun g v => GlobalTheory.AutomorphicL2Unitary.norm_R g v)
    (fun g φ => c3 φ.1 g (hg _ φ.2).2.1)
    (fun g φ => Subtype.ext (LinearMap.congr_fun (o2 g).eq φ.1).symm)
    (fun φ ψ => casSym E a ha μ n e c φ.1 φ.2 ψ.1 ψ.2)
    (fun W hW h => gardSep E a μ W hW fun φ hφ => h ⟨φ, hφ⟩)
  exact ⟨P, Q, S, h1, h2, h3, fun k φ hφ => h4 k ⟨φ, hφ⟩, fun F φ hφ => h5 F ⟨φ, hφ⟩, h6⟩
end
end
