module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.RealSt
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.FiniteAdelicEstimatesHolds
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PureSt
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsNhdsInvariant
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.IndicatorMem
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfActs
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictAd
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MCPure
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MCReal
import Mathlib.Algebra.Module.Torsion.Prod
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MCGlue

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Mix

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.KCo
  GlobalTheory.CompanionTheory.Ar.RT.Move

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

abbrev stdL (F : Type) [Field F] [NumberField F] (κ : Type) (v : Pl F) : (κ → Fv F v) → ℂ :=
  Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

def Dat (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : Type :=
  {p : SInf F κ × ∀ v : Pl F, (κ → Fv F v) → ℂ // ∀ᶠ v in cofinite, p.2 v = stdL F κ v}

theorem rel_inf (ei : SInf F κ →ₗ[ℂ] SInf F κ) {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → SInf F κ)
    (φ : ι → ∀ v : Pl F, (κ → Fv F v) → ℂ) (h : ∑ j ∈ s, c j • pure (f j) (φ j) = 0) :
    ∑ j ∈ s, c j • pure (ei (f j)) (φ j) = 0 := by
  funext x
  have h1 : ∑ j ∈ s, (c j * ∏ᶠ v, φ j v fun i => evFin F v (x i)) • f j = 0 := by
    refine DFunLike.ext _ _ fun y => ?_
    let z : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), (x i).2)
    have := congrFun h z
    have e : (fun i => evI F (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), (x i).2) : AF F)) = y :=
      funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
    rw [sum_apply, zero_apply]
    refine Eq.trans ?_ this
    refine Eq.trans ?_ (Finset.sum_apply z s fun j => c j • pure (f j) (φ j)).symm
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_apply, smul_eq_mul, mul_assoc, mul_comm _ (f j y)]
    exact congrArg (fun z => c j * (f j z * ∏ᶠ v, φ j v fun i => evFin F v (x i))) e.symm
  have h2 := DFunLike.congr_fun (congrArg ei h1) fun i => evI F (x i)

  rw [map_sum, map_zero, sum_apply, zero_apply] at h2
  rw [Finset.sum_apply, Pi.zero_apply, ← h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc,
    mul_comm (ei (f j) _)]

theorem rel_fin (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)) (hev : ∀ᶠ v in cofinite, ev v (stdL F κ v) = stdL F κ v)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → SInf F κ) (φ : ι → ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hφ : ∀ j, ∀ᶠ v in cofinite, φ j v = stdL F κ v) (h : ∑ j ∈ s, c j • pure (f j) (φ j) = 0) :
    ∑ j ∈ s, c j • pure (f j) (fun v => ev v (φ j v)) = 0 := by
  classical
  have key : ∀ T : Finset (Pl F), ∑ j ∈ s, c j • pure (f j) (fun v => if v ∈ T then ev v (φ j v) else φ j v) = 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using h
    | insert v T hv ih =>
      have h1 := congrArg (opL v (ev v)) ih

      rw [map_sum, map_zero] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h2 : ∀ᶠ w in cofinite, (fun w => if w ∈ T then ev w (φ j w) else φ j w) w = stdL F κ w := by
        filter_upwards [hφ j, T.eventually_cofinite_notMem] with w e1 e2
        simp only [ite_eq_right e2, e1]
      have hop (g : SInf F κ) {θ : ∀ w : Pl F, (κ → Fv F w) → ℂ}
          (hθ : ∀ᶠ w in cofinite, θ w = stdL F κ w) :
          opL v (ev v) (pure g θ) = pure g (Function.update θ v (ev v (θ v))) := by
        let r := pure g (Function.update θ v 1)
        have hr (x : κ → AF F) (y : κ → Fv F v) : r (repl v x y) = r x := by
          unfold r GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
          congr 1
          refine finprod_congr fun w => ?_
          by_cases e : w = v
          · subst w
            simp
          · rw [Function.update_of_ne e]
            congr 1
            funext i
            change evalV F w ((x i).2 - singleFin v _ + singleFin v _) = _
            rw [map_add (f := _), map_sub, evalV_singleFin_ne e, evalV_singleFin_ne e,
              sub_zero, add_zero]
            rfl
        have hu (η : (κ → Fv F v) → ℂ) :
            pure g (Function.update θ v η) = tens (evFin F v) η r := by
          funext x
          have hθ₁ : ∀ᶠ w in cofinite, Function.update θ v 1 w = stdL F κ w := by
            filter_upwards [hθ, eventually_cofinite_ne v] with w hw e
            rw [Function.update_of_ne e, hw]
          have hsupport := finite_mulSupport (vac := stdL F κ)
            (Eventually.of_forall fun _ => rfl) hθ₁ x
          let t (w : Pl F) := if w = v then η (fun i => evFin F v (x i)) else 1
          have ht : (Function.mulSupport t).Finite :=
            (Set.finite_singleton v).subset fun w hw => by
              by_contra e
              exact hw (ite_eq_right e)
          have hprod (w : Pl F) :
              Function.update θ v η w (fun i => evFin F w (x i)) =
                t w * Function.update θ v 1 w (fun i => evFin F w (x i)) := by
            by_cases e : w = v
            · subst w
              simp [t]
            · simp [t, e]
          unfold tens r GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
          rw [funext hprod, finprod_mul_distrib ht hsupport,
            finprod_eq_single t v (fun w e => ite_eq_right e)]
          simp only [t, if_true]
          ac_rfl
        funext x
        have hs : (fun y => pure g θ (repl v x y)) = r x • θ v := by
          have hself := hu (θ v)
          rw [Function.update_eq_self] at hself
          funext y
          rw [hself, tens, piK_repl, hr, Pi.smul_apply, smul_eq_mul, mul_comm]
        change ev v (fun y => pure g θ (repl v x y)) (piK v (finPart x)) = _
        rw [hs, map_smul, hu, tens, Pi.smul_apply, smul_eq_mul, mul_comm]
        rfl
      rw [map_smul, hop _ h2]
      congr 2
      funext w
      rcases eq_or_ne w v with rfl | e
      · simp [hv]
      · simp [e]
  have hfin : {v | ¬ (ev v (stdL F κ v) = stdL F κ v ∧ ∀ j ∈ s, φ j v = stdL F κ v)}.Finite :=
    eventually_cofinite.1 (hev.and ((eventually_all_finset s).2 fun j _ => hφ j))
  rw [← key hfin.toFinset]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 2
  funext v
  split_ifs with e
  · rfl
  · rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at e
    rw [e.2 j hj, e.1]

theorem exists_glue (ei : SInf F κ →ₗ[ℂ] SInf F κ) (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ))
    (hev : ∀ᶠ v in cofinite, ev v (stdL F κ v) = stdL F κ v) : ∃ e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ),
    ∀ f φ, (∀ᶠ v in cofinite, φ v = stdL F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v) := by
  let a : (Dat F κ →₀ ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) := Finsupp.linearCombination ℂ fun p => pure p.1.1 p.1.2
  let b : (Dat F κ →₀ ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) := Finsupp.linearCombination ℂ fun p => pure (ei p.1.1) fun v => ev v (p.1.2 v)
  have hk : LinearMap.ker a ≤ LinearMap.ker b := fun z hz =>
    rel_fin ev hev z.support z (fun p => ei p.1.1) (fun p => p.1.2) (fun p => p.2) (rel_inf ei z.support z _ _ hz)
  obtain ⟨e, he⟩ := ((LinearMap.ker a).liftQ b hk ∘ₗ a.quotKerEquivRange.symm.toLinearMap).exists_extend
  refine ⟨e, fun f φ hφ => ?_⟩
  have h1 : a (Finsupp.single ⟨(f, φ), hφ⟩ 1) = pure f φ := (Finsupp.linearCombination_single ℂ 1 _).trans (one_smul _ _)
  have h2 := LinearMap.congr_fun he ⟨_, LinearMap.mem_range_self a (Finsupp.single ⟨(f, φ), hφ⟩ 1)⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply] at h2
  rw [← h1, h2]
  exact (Finsupp.linearCombination_single ℂ 1 _).trans (one_smul _ _)

theorem adelSt_of (hP : PureSt) (hF : FinSt) (hI : InfSt) : AdelSt := by
  intro F _ _ ψ hψ κ _ S hS
  obtain ⟨ev, hb, hi, hs⟩ := hF F ψ hψ κ S hS
  obtain ⟨ei, hei⟩ := hI F κ S hS
  obtain ⟨e, he'⟩ := exists_glue (ei : SInf F κ →L[ℂ] SInf F κ).toLinearMap ev hs
  have he : ∀ f φ, (∀ᶠ v in cofinite, φ v = stdL F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v) := he'
  have hstd : ∀ φ : ∀ v : Pl F, (κ → Fv F v) → ℂ, (∀ᶠ v in cofinite, φ v = stdL F κ v) →
      ∀ᶠ v in cofinite, ev v (φ v) = stdL F κ v := fun φ h => by
    filter_upwards [h, hs] with v e1 e2
    rw [e1, e2]
  refine ⟨e, ei, ev, fun Φ hΦ => schA_le ((schA F κ).comap e) (fun f φ h1 h2 => ?_) hΦ, fun w Φ hΦ => ?_, hb,
    fun v w hw φ hφ φ₁ h₁ => ?_, hs, fun f φ _ h => he f φ h⟩
  · rw [Submodule.mem_comap, he f φ h2]
    exact pure_mem_schA _ _ (fun v => (hb v).1 (h1 v)) (hstd φ h2)
  · let L : ∀ u : (κ → AF F) × (κ → AF F), ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) := fun u =>
      { toFun := schr ψ u
        map_add' := fun _ _ => funext fun _ => by simp [schr, mul_add]
        map_smul' := fun _ _ => funext fun _ => by simp [schr, mul_left_comm] }
    refine schA_le (LinearMap.eqLocus (e ∘ₗ L w) (L (S w) ∘ₗ e)) (fun f φ h1 h2 => ?_) hΦ
    change e (schr ψ w _) = schr ψ (S w) (e _)
    obtain ⟨⟨g, hg⟩, h⟩ := hP F ψ hψ κ w f
    rw [(h φ h2).2 g hg, he _ _ (h φ h2).1, he f φ h2, ((hP F ψ hψ κ (S w) (ei f)).2 _ (hstd φ h2)).2 _ (hei w f g hg)]
    congr 1
    funext v
    exact hi v w _ (h1 v)
  · have hw' : At (evFin F v) (S w) := fun u hu => by rw [← map_smul, hw u hu, map_zero]
    rw [action_uniqueness F κ v _ φ hφ _ _ h₁ (ad_heis ψ w hw φ), hi v w φ hφ]
    exact ad_heis ψ (S w) hw' (ev v φ)

end PositivityTheory.Mix
end
end
end

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.TraceNondeg

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Mix

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open mixedEmbedding
open scoped Classical

namespace Inf

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def rho (F : Type) [Field F] [NumberField F] : AF F →+* mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

def li (a : mixedSpace F) : AF F := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0)

theorem rho_li (a : mixedSpace F) : rho F (li a) = a := (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply a

theorem li_add (a b : mixedSpace F) : li (a + b) = li a + li b := Prod.ext (map_add _ a b) (add_zero _).symm

theorem li_mul (a b : mixedSpace F) : li (a * b) = li a * li b := Prod.ext (map_mul _ a b) (mul_zero _).symm

theorem li_rho (z : AF F) : li (rho F z) = li 1 * z :=
  Prod.ext (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _).trans (by
    change z.1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 1 * z.1
    rw [map_one, one_mul])) (zero_mul _).symm

def pr (w : (κ → AF F) × (κ → AF F)) : (κ → mixedSpace F) × (κ → mixedSpace F) := (fun i => rho F (w.1 i), fun i => rho F (w.2 i))

def lf (y : (κ → mixedSpace F) × (κ → mixedSpace F)) : (κ → AF F) × (κ → AF F) := (fun i => li (y.1 i), fun i => li (y.2 i))

omit [Fintype κ] in
theorem pr_lf (y : (κ → mixedSpace F) × (κ → mixedSpace F)) : pr (lf y) = y :=
  Prod.ext (funext fun _ => rho_li _) (funext fun _ => rho_li _)

omit [Fintype κ] in
theorem pr_smul (c : AF F) (w : (κ → AF F) × (κ → AF F)) : pr (c • w) = rho F c • pr w :=
  Prod.ext (funext fun _ => map_mul _ _ _) (funext fun _ => map_mul _ _ _)

omit [Fintype κ] in
theorem lf_pr (w : (κ → AF F) × (κ → AF F)) : lf (pr w) = li (1 : mixedSpace F) • w :=
  Prod.ext (funext fun _ => li_rho _) (funext fun _ => li_rho _)

def loc (T : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F))) :
    ((κ → mixedSpace F) × (κ → mixedSpace F)) →ₗ[mixedSpace F] ((κ → mixedSpace F) × (κ → mixedSpace F)) where
  toFun y := pr (T (lf y))
  map_add' y z := by
    have e : lf (y + z) = lf y + lf z := Prod.ext (funext fun _ => li_add _ _) (funext fun _ => li_add _ _)
    rw [e, map_add (f := _)]
    exact Prod.ext (funext fun _ => map_add _ _ _) (funext fun _ => map_add _ _ _)
  map_smul' c y := by
    have e : lf (c • y) = li c • lf y := Prod.ext (funext fun _ => li_mul _ _) (funext fun _ => li_mul _ _)
    rw [e, map_smul, pr_smul, rho_li]
    rfl

omit [Fintype κ] in
theorem loc_pr (T : ((κ → AF F) × (κ → AF F)) →ₗ[AF F] ((κ → AF F) × (κ → AF F))) (w : (κ → AF F) × (κ → AF F)) :
    loc T (pr w) = pr (T w) := by
  change pr (T (lf (pr w))) = _
  rw [lf_pr, map_smul, pr_smul, rho_li, one_smul]

theorem pr_dot (x y : κ → AF F) : (fun i => rho F (x i)) ⬝ᵥ (fun i => rho F (y i)) = rho F (x ⬝ᵥ y) := by

  simp [dotProduct, map_sum]

theorem trace_nondeg (a : mixedSpace F) (h : ∀ b, Algebra.trace ℝ (mixedSpace F) (a * b) = 0) : a = 0 := by
  let b : mixedSpace F := (fun w => (a.1 w)⁻¹, fun w => (a.2 w)⁻¹)
  have h1 : a * b * a = a := Prod.ext (funext fun w => mul_inv_mul_cancel (a.1 w)) (funext fun w => mul_inv_mul_cancel (a.2 w))
  have h2 : IsIdempotentElem (Algebra.lmul ℝ (mixedSpace F) (a * b)) := by
    unfold IsIdempotentElem
    rw [← map_mul, ← mul_assoc, h1]
  have h3 := (LinearMap.IsIdempotentElem.isProj_range _ h2).trace
  have h4 : LinearMap.trace ℝ _ (Algebra.lmul ℝ (mixedSpace F) (a * b)) = 0 := h b
  rw [h4] at h3
  have h5 : LinearMap.range (Algebra.lmul ℝ (mixedSpace F) (a * b)) = ⊥ :=
    Submodule.finrank_eq_zero.1 (by exact_mod_cast h3.symm)
  have h6 : a * b * a ∈ LinearMap.range (Algebra.lmul ℝ (mixedSpace F) (a * b)) := ⟨a, rfl⟩
  rwa [h5, h1, Submodule.mem_bot] at h6

def betaL (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : (κ → mixedSpace F) →ₗ[ℝ] (κ → mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (beta F κ) (fun x y z => by simp only [beta, add_dotProduct, map_add (f := _)]) (fun c x y => by simp [beta, smul_dotProduct])
    (fun x y z => by simp only [beta, dotProduct_add, map_add (f := _)]) fun c x y => by simp [beta, dotProduct_smul]

end Inf

open Inf

theorem infSt_of (h : RealSt) : InfSt := by
  intro F _ _ κ _ S hS
  let S₀ : ((κ → mixedSpace F) × (κ → mixedSpace F)) ≃ₗ[mixedSpace F] ((κ → mixedSpace F) × (κ → mixedSpace F)) :=
    LinearEquiv.ofLinear (loc S.toLinearMap) (loc S.symm.toLinearMap)
      (LinearMap.ext fun y => by
        change loc S.toLinearMap (pr (S.symm (lf y))) = y
        rw [loc_pr]; simp [pr_lf])
      (LinearMap.ext fun y => by
        change loc S.symm.toLinearMap (pr (S (lf y))) = y
        rw [loc_pr]; simp [pr_lf])
  have hp : ∀ w, (S₀.restrictScalars ℝ) (pr w) = pr (S w) := fun w => loc_pr S.toLinearMap w
  obtain ⟨T, hT⟩ := h (κ → mixedSpace F) (betaL F κ) (fun x y => congrArg (Algebra.trace ℝ (mixedSpace F)) (dotProduct_comm x y))
    (fun x hx => funext fun i => trace_nondeg _ fun b => by
      have e : beta F κ x (Pi.single i b) = 0 := hx _
      rwa [beta, dotProduct_single] at e)
    (S₀.restrictScalars ℝ) fun y z => by
      rw [← pr_lf y, ← pr_lf z, hp, hp]
      change beta F κ _ _ - beta F κ _ _ = beta F κ _ _ - beta F κ _ _
      simp only [beta, pr, pr_dot, ← map_sub, hS]
  refine ⟨T, fun w f g hg x => ?_⟩
  have := hT (pr w) f g hg x
  rw [hp] at this
  exact this

end PositivityTheory.Mix
end
end
end

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdelicEstimatesHolds

section

@[expose] public section

theorem PositivityTheory.Mix.adelic_estimates_holds : PositivityTheory.Mix.AdelSt :=
  PositivityTheory.Mix.adelSt_of PositivityTheory.Mix.pure_tensor_estimates_holds PositivityTheory.Mix.finite_adelic_estimates_holds (PositivityTheory.Mix.infSt_of PositivityTheory.Mix.real_estimates_holds)
end
end
