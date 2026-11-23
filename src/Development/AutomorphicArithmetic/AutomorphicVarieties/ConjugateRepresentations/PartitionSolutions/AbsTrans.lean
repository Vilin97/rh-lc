module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartHOfSs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.AbsTransOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PartOp
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.CoverEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.HdFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.LevCorr
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.PullB
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SatClosed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SuppBwd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SandCpt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFactsAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
import Mathlib.Tactic.Polynomial.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.ZigBwd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.ZigFormal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.ZigFwd
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.BwdLast

section

@[expose] public section

open UpperTheory.V.Cj.A UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Cj.A.bwdLast :
    BwdLast := by
  intro Γ V S I _ _ _ _ d G φ hφ C F hC q u hu hhd hvan
  obtain ⟨P, hP1, hPeq, hPvan⟩ := partOp Γ V S I d G φ hφ q
  have hconst : ∀ i j : I, u [i] = u [j] := by
    intro i j
    have h := hhd [i, j] rfl
    simp [UpperTheory.V.Lit.Geo.hd, Finset.sum_range_succ] at h
    have h' : u [j] - u [i] = 0 := by
      rw [sub_eq_add_neg]
      simpa using h
    exact (sub_eq_zero.mp h').symm
  refine ⟨P (fun i => u [i]), ?_, ?_, ?_⟩
  · intro γ
    have hinv : (fun i => (G.act q) γ (u [γ⁻¹ • i])) = fun i => u [i] := by
      funext i
      have h := hu γ [γ⁻¹ • i] rfl
      simp only [List.map_cons, List.map_nil, smul_inv_smul] at h
      exact h.symm
    rw [← hPeq γ (fun i => u [i]), hinv]
  · intro x hx
    match x, hx with
    | [i], _ =>
      have hfun : (fun j => u [j]) = fun _ => u [i] := by
        funext j
        exact hconst j i
      rw [hfun, hP1]
  · intro s p hp
    apply hPvan
    intro i hne
    refine hvan [i] rfl s p hp ?_
    intro i' hi'
    rw [List.mem_singleton] at hi'
    rw [hi']
    exact hC i s p hp hne
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PullAct

section

@[expose] public section

open UpperTheory.V.Cj.A UpperTheory.V.Lit.Dr Matrix

theorem UpperTheory.V.Cj.A.pullAct :
    PullAct := by
  intro Γ V S _ _ _ d G _hcone l hl q P hP γ w
  have hinv : ∀ x : V, G.ρ γ (G.ρ γ⁻¹ x) = x := by
    intro x
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
  have hinv' : ∀ x : V, G.ρ γ⁻¹ (G.ρ γ x) = x := by
    intro x
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
  have hinvS : ∀ s : S, G.σ γ (G.σ γ⁻¹ s) = s := by
    intro s
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  apply Subtype.ext
  funext s p
  by_cases hp : p ∈ G.Y
  · have hp' : G.ρ γ⁻¹ p ∈ G.Y := G.maps _ _ hp
    have hleq : l (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) = l s p := by
      have := hl.2 γ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) hp'
      rw [hinvS, hinv] at this
      exact this.symm
    have hdiff : DifferentiableAt ℝ (l s) p :=
      ((hl.1 s).1.contDiffAt (G.isOpen.mem_nhds hp)).differentiableAt (by simp)
    have hf : HasFDerivAt (fun x => l s x • x) (fderiv ℝ (fun x => l s x • x) p) (G.ρ γ (G.ρ γ⁻¹ p)) := by
      rw [hinv]
      exact (hdiff.smul differentiableAt_id).hasFDerivAt
    have hcomp := (G.ρ γ⁻¹).hasFDerivAt.comp (G.ρ γ⁻¹ p) (hf.comp (G.ρ γ⁻¹ p) (G.ρ γ).hasFDerivAt)
    have heq : (fun x => l (G.σ γ⁻¹ s) x • x) =ᶠ[nhds (G.ρ γ⁻¹ p)]
        (⇑(G.ρ γ⁻¹) ∘ ((fun x => l s x • x) ∘ ⇑(G.ρ γ))) := by
      filter_upwards [G.isOpen.mem_nhds hp'] with x hx
      have := hl.2 γ (G.σ γ⁻¹ s) x hx
      rw [hinvS] at this
      simp only [Function.comp_apply, map_smul, hinv', this]
    have hder : ∀ u : V, fderiv ℝ (fun x => l (G.σ γ⁻¹ s) x • x) (G.ρ γ⁻¹ p) (G.ρ γ⁻¹ u)
        = G.ρ γ⁻¹ (fderiv ℝ (fun x => l s x • x) p u) := by
      intro u
      rw [(hcomp.congr_of_eventuallyEq heq).fderiv]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, hinv]
    ext v
    rw [G.act_apply, hP w _ _ hp', hP _ s p hp]
    simp only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply, G.act_apply]
    rw [hleq, map_smul]
    simp only [Function.comp_def, hder]
  · have hnot : G.ρ γ⁻¹ p ∉ G.Y := by
      intro h
      exact hp (hinv p ▸ G.maps γ _ h)
    have h1 := ((P w).2 (G.σ γ⁻¹ s)).2 _ hnot
    have h2 := ((P (G.act q γ w)).2 s).2 p hp
    rw [h2]
    ext v
    rw [G.act_apply, h1]
    simp
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PullOp

section

@[expose] public section

open UpperTheory.V.Cj.A UpperTheory.V.Lit.Dr
open scoped ContDiff

theorem UpperTheory.V.Cj.A.pullOp :
    PullOp := by
  intro Γ V S _ _ _ _ d G hC l hl
  have hY : IsOpen G.Y := G.isOpen
  have hpos : ∀ s, ∀ p ∈ G.Y, l s p • p ∈ G.Y := fun s p hp => hC _ ((hl.1 s).2.1 p hp) p hp
  have hw : ∀ q (w : G.Om q) (s : S),
      ContDiffOn ℝ ∞ ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
        ∀ p ∉ G.Y, (w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0 := fun q w => w.2
  have mem : ∀ q (w : G.Om q), (fun s => G.Y.indicator
      (pull (l s) ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s))) ∈ G.Om q := by
    intro q w s
    refine ⟨?_, fun p hp => Set.indicator_apply_eq_zero.2 fun h => absurd h hp⟩
    exact (pullB V (Fin d → ℂ) G.Y hY hC (l s) (hl.1 s) q _ (hw q w s).1).1.congr
      fun p hp => Set.indicator_of_mem hp _
  have padd : ∀ q (s : S) (a b : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (p : V),
      pull (l s) (a + b) p = pull (l s) a p + pull (l s) b p := by
    intro q s a b p
    ext v
    simp [pull]
  have psmul : ∀ q (s : S) (c : ℂ) (a : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (p : V),
      pull (l s) (c • a) p = c • pull (l s) a p := by
    intro q s c a p
    ext v
    simp [pull]
  have ext_ind : ∀ q (om : V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) p, p ∈ G.Y →
      extDeriv (G.Y.indicator om) p = extDeriv om p := by
    intro q om p hp
    simp only [extDeriv]
    rw [Filter.EventuallyEq.fderiv_eq
      (Filter.eventuallyEq_of_mem (hY.mem_nhds hp) fun x hx => Set.indicator_of_mem hx om)]
  let P : ∀ q, G.Om q →ₗ[ℂ] G.Om q := fun q =>
    { toFun := fun w => ⟨_, mem q w⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        funext s p
        simp only [Submodule.coe_add, Pi.add_apply]
        by_cases hp : p ∈ G.Y
        · simp only [Set.indicator_of_mem hp]
          exact padd q s _ _ p
        · simp [Set.indicator, hp]
      map_smul' := by
        intro c a
        apply Subtype.ext
        funext s p
        simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
        by_cases hp : p ∈ G.Y
        · simp only [Set.indicator_of_mem hp]
          exact psmul q s c _ p
        · simp [Set.indicator, hp] }
  refine ⟨P, ?_, ?_, ?_⟩
  · intro q w s p hp
    exact Set.indicator_of_mem hp _
  · intro q w
    apply Subtype.ext
    funext s p
    by_cases hp : p ∈ G.Y
    · rw [Geo.dOm_apply G _ s hp]
      change extDeriv (G.Y.indicator _) p = G.Y.indicator _ p
      rw [ext_ind _ _ _ hp, Set.indicator_of_mem hp,
        (pullB V (Fin d → ℂ) G.Y hY hC (l s) (hl.1 s) q _ (hw q w s).1).2 p hp]
      simp only [pull]
      rw [Geo.dOm_apply G w s (hpos s p hp)]
    · exact ((hw _ _ s).2 p hp).trans ((hw _ _ s).2 p hp).symm
  · intro f
    apply Subtype.ext
    funext s p
    by_cases hp : p ∈ G.Y
    · change G.Y.indicator _ p = _
      rw [Set.indicator_of_mem hp]
      ext v
      simp only [pull, ContinuousAlternatingMap.compContinuousLinearMap_apply]
      rw [Geo.incl_apply G f s (hpos s p hp), Geo.incl_apply G f s hp]
    · exact ((hw _ _ s).2 p hp).trans ((hw _ _ s).2 p hp).symm
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SatFacts

section

@[expose] public section

open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.satFacts :
    SatFacts := by
  intro Γ V S _ _ _ d G T K
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ s p
    simp only [UpperTheory.V.Cj.A.sat, Set.mem_setOf_eq]
    constructor
    · rintro ⟨δ, t, ht, hT, hK⟩
      refine ⟨δ * γ, t, ht, ?_, ?_⟩
      · rw [map_mul, Equiv.Perm.mul_apply]
        exact hT
      · rw [map_mul, ContinuousLinearMap.mul_apply]
        exact hK
    · rintro ⟨δ, t, ht, hT, hK⟩
      refine ⟨δ * γ⁻¹, t, ht, ?_, ?_⟩
      · rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel_right]
        exact hT
      · rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_right]
        exact hK
  · intro hK s
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨γ, t, ht, hT, hp⟩
    have hc : Continuous fun q : V => t • (G.ρ γ) q :=
      continuous_const.smul (G.ρ γ).continuous
    filter_upwards [(hK.preimage hc).mem_nhds hp] with q hq
    exact ⟨γ, t, ht, hT, hq⟩
  · rintro K' hKK' s p ⟨γ, t, ht, hT, hp⟩
    exact ⟨γ, t, ht, hT, hKK' hp⟩
  · intro s p t ht
    simp only [UpperTheory.V.Cj.A.sat, Set.mem_setOf_eq, map_smul, smul_smul]
    constructor
    · rintro ⟨γ, u, hu, hT, hK⟩
      exact ⟨γ, u * t, mul_pos hu ht, hT, hK⟩
    · rintro ⟨γ, u, hu, hT, hK⟩
      refine ⟨γ, u / t, div_pos hu ht, hT, ?_⟩
      rwa [div_mul_cancel₀ u ht.ne']
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SuppFwd

section

@[expose] public section

open UpperTheory.V.Cj.A
open Matrix NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Cj.A.suppFwd :
    SuppFwd := by
  intro E _ _ _ a ho U hU Ξ q α w h hα
  obtain ⟨R, hR⟩ := hα
  obtain ⟨C, hC, hC'⟩ := (qhtFacts E a).2.2.2 R
  have h1 : Continuous (pInf E) := continuous_pi fun v =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).continuous.comp
      ((continuous_apply v).comp continuous_fst)
  have h2 : Continuous (pFin E) := continuous_snd
  have hi : Continuous fun g : GA E a => GeneralLinearGroup.map (pInf E) g :=
    Continuous.units_map _ (continuous_id.matrix_map h1)
  have hf : Continuous fun g : GA E a => GeneralLinearGroup.map (pFin E) g :=
    Continuous.units_map _ (continuous_id.matrix_map h2)
  haveI : DiscreteTopology (GL (Fin a) (Af E) ⧸ U) := QuotientGroup.discreteTopology hU
  refine ⟨(fun g : GA E a => ((GeneralLinearGroup.map (pFin E) g : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U)) '' C,
    (fun g : GA E a => sand (GeneralLinearGroup.map (pInf E) g) (hOne E a)) '' C,
    (hC.image (QuotientGroup.continuous_mk.comp hf)).finite_of_discrete,
    hC.image ((sandCpt E a).1.comp hi), ?_, ?_⟩
  · rintro _ ⟨g, -, rfl⟩
    exact ⟨_, rfl⟩
  · rintro s _ ⟨g, rfl⟩ hp
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    have hlt : R < qht (infGL E a g * finGL E a x) := by
      by_contra hle
      obtain ⟨γ, t, hm⟩ := hC' _ (not_lt.1 hle)
      obtain ⟨e1, r, hr, e2⟩ := (splitFacts E a).1 t
      refine hp ⟨⟨γ, Subgroup.mem_top γ⟩, r, hr, ⟨_, hm, ?_⟩, ⟨_, hm, ?_⟩⟩
      · simp only [map_mul, e1, pFin_infGL, pFin_finGL, one_mul, mul_one]
        rfl
      · simp only [map_mul, pInf_infGL, pInf_finGL, mul_one, ContinuousLinearMap.mul_apply, e2, map_smul, geo_ρ]
    refine ContinuousAlternatingMap.ext fun v => ?_
    have hv' : v = fun i => (2 : ℝ) • sand g (hv (hv.symm ((2 : ℝ)⁻¹ • sand g⁻¹ (v i)))) := by
      funext i
      rw [LinearEquiv.apply_symm_apply, map_smul, smul_smul, ← ContinuousLinearMap.mul_apply, ← map_mul,
        mul_inv_cancel, map_one]
      simp
    rw [hv', h, hR _ _ hlt, Matrix.mulVec_zero]
    rfl
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.ZigMap

section

@[expose] public section

open UpperTheory.V.Cj.A UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Cj.A.zigMap :
    ZigMap := by
  intro Γ V S _ _ _ d G P hd' hi ha q
  induction q with
  | zero =>
    intro k u c h x hx
    show P 0 (u x) = G.incl (c x)
    rw [h x hx, hi]
  | succ q ih =>
    rintro k u c ⟨b, hb, hdb, hz⟩
    refine ⟨fun x => P q (b x), fun γ x hx => ?_, fun x hx => ?_, ?_⟩
    · show P q (b (x.map (γ * ·))) = G.act q γ (P q (b x))
      rw [hb γ x hx, ha]
    · show G.dOm q (P q (b x)) = P (q + 1) (u x)
      rw [hd', hdb x hx]
    · have e : hd (fun x => P q (b x)) = fun x => P q (hd b x) :=
        funext fun x => hdFacts.2.2.2.1 Γ _ _ (P q).toAddMonoidHom b x
      rw [e]
      exact ih (k + 1) (hd b) c hz
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.AbsTrans

section

@[expose] public section

namespace UpperTheory.V.Cj

theorem A.absTrans : A.AbsTrans :=
  A.absTrans_of A.hdFacts A.zigFwd A.zigBwd A.bwdLast A.zigFormal A.pullOp A.pullAct A.zigMap A.coverEx A.satClosed A.satFacts

theorem partA : PartA := A.partA_of A.absTrans A.suppFwd A.suppBwd A.levCorr

end UpperTheory.V.Cj
end
end
