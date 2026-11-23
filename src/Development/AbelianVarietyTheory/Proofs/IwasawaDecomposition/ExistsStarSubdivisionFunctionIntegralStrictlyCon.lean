module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllEqOfInRCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalRStarDepthLeOfCentreBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinRepsProjectiveFinrankLeNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionFunctionLinearOnCellsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionSubordinateToFan
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthCommonDenominatorRankLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeOnCentreCellStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeStrictnessGapOffCentres
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionEstimateOffCentreCell

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedGeneratorsStarSubdivisionCone

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarGens

section General

variable {O : Type} [CommRing O] {bar : O → O} {X Y : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
  [AddCommGroup Y] [Module O Y] [Module.Finite O Y]

theorem transport {φ χ : InvFun O} {b : ℕ} (e : X ≃ₗ[O] Y) {β : LinearMap.BilinForm ℤ Y}
    (h : ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧
      φ.LinearOn u ∧ χ.LinearOn u ∧ (∀ i, φ.evalZ (u i) ≤ b) ∧ (∀ i, χ.evalZ (u i) ≤ 1) ∧
      InRCone u (pull e.toLinearMap β)) :
    ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ Y), (∀ i, u i ∈ balForms bar Y) ∧ (∀ i y, 0 ≤ u i y y) ∧
      φ.LinearOn u ∧ χ.LinearOn u ∧ (∀ i, φ.evalZ (u i) ≤ b) ∧ (∀ i, χ.evalZ (u i) ≤ 1) ∧ InRCone u β := by
  obtain ⟨n, u, h1, h2, h3, h4, h5, h6, c, hc, h7⟩ := h
  refine ⟨n, fun i => pull e.symm.toLinearMap (u i), fun i => pull_mem _ (h1 i), fun i y => h2 i _,
    (linearOn_pull_iff e.symm.surjective).2 h3, (linearOn_pull_iff e.symm.surjective).2 h4,
    fun i => by rw [evalZ_pull φ e.symm.surjective]; exact h5 i,
    fun i => by rw [evalZ_pull χ e.symm.surjective]; exact h6 i, c, hc, LinearMap.ext₂ fun x y => ?_⟩
  have := LinearMap.congr_fun₂ h7 (e.symm x) (e.symm y)
  simpa [LinearMap.sum_apply] using this

theorem linearOn_starDepth {ψ w : InvFun O} {n : ℕ} {u : Fin n → LinearMap.BilinForm ℤ X}
    (h : (starFun bar ψ w 0 1).LinearOn u) : (starDepth bar ψ w).LinearOn u := by
  rw [linearOn_iff] at h ⊢
  intro c hc
  simpa [starFun_evalR, starFun_evalZ] using h c hc


omit [Module O X] [Module.Finite O X] in
theorem mul_le_of_sub_mem_rcone {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hγ : ∀ i, 0 ≤ h (γ i)) {β v : LinearMap.BilinForm ℤ X} {t : ℝ} (hm : toReal β - t • toReal v ∈ rcone γ) :
    t * (h v : ℝ) ≤ h β := by
  obtain ⟨g, hg, hBg⟩ := hm
  have key := apply_eq_of_toReal_eq (β := β) (γ := Fin.cons v γ) (c := Fin.cons t g) (by
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [← hBg]; abel) h
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at key
  have hpos : 0 ≤ ∑ i, g i * (h (γ i) : ℝ) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hg i) (by exact_mod_cast hγ i)
  linarith

theorem exists_nat_bound {α : Type} {S : Set α} (hS : S.Finite) (f : α → ℝ) : ∃ b : ℕ, ∀ x ∈ S, f x ≤ b := by
  obtain ⟨r, hr⟩ := (hS.image f).bddAbove
  exact ⟨⌈r⌉₊, fun x hx => (hr ⟨x, hx, rfl⟩).trans (Nat.le_ceil r)⟩

end General

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {q : ℕ} {ψ w : InvFun (𝓞 E)}

theorem centres_finite (hw : IsCentreSet H.bar q ψ w) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (hX : Module.finrank (𝓞 E) X ≤ q)
    {S : Set (LinearMap.BilinForm ℤ X)} (hS : S.Finite) :
    {v | v ∈ balForms H.bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X),
      IsCell H.bar ψ γ ∧ (∀ i, γ i ∈ S) ∧ InRCone γ v}.Finite := by
  refine (hS.finite_subsets.biUnion (t := fun T => {v | v ∈ balForms H.bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧
    ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ Set.range γ = T ∧ InRCone γ v})
    fun T _ => Set.Subsingleton.finite ?_).subset ?_
  · rintro v ⟨a1, a2, a3, m, γ, a4, a5, a6⟩ v' ⟨b1, b2, b3, m', γ', -, b5, b6⟩
    refine (hw X hX).2.2 m γ a4 v a1 a2 v' b1 b2 a3 b3 a6 (inRCone_trans (fun j => ?_) b6)
    obtain ⟨i, hi⟩ : γ' j ∈ Set.range γ := by rw [a5, ← b5]; exact ⟨j, rfl⟩
    rw [← hi]; exact inRCone_self γ i
  · rintro v ⟨a1, a2, a3, m, γ, a4, a5, a6⟩
    exact Set.mem_biUnion (x := Set.range γ) (by rintro _ ⟨i, rfl⟩; exact a5 i) ⟨a1, a2, a3, m, γ, a4, rfl, a6⟩

theorem of_cell (hw : IsCentreSet H.bar q ψ w) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (hX : Module.finrank (𝓞 E) X ≤ q) {b m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCell H.bar ψ γ) (hb : ∀ i, ψ.evalZ (γ i) ≤ b)
    (hb' : ∀ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → ψ.evalZ v ≤ b)
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β) :
    ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms H.bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧
      ψ.LinearOn u ∧ (starDepth H.bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧
      (∀ i, (starDepth H.bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β := by
  obtain ⟨hC1, hC2, hC3⟩ := hw X hX
  obtain ⟨lin1, lin2⟩ := GlobalTheory.T.starSubdivision_function_linearOn_cells E H q ψ w 0 1 hw
  by_cases hc : ∃ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v
  · obtain ⟨v, hv, hvp, hvw, hvin⟩ := hc
    have hne : v ≠ 0 := by
      rintro rfl
      have := hC2 0 hv hvp hvw 2 0 (by simp)
      norm_num at this
    obtain ⟨m', s, h, hcut, hh, hin⟩ := GlobalTheory.StarCover.star_cover X m γ v (toReal β) (fun i => (hγ.mem i).1)
      hγ.nonneg hne hvin hβ
    have hh' : (0 : ℝ) < h v := by exact_mod_cast hh
    have hmem : ∀ j, InRCone γ ((Fin.cons v fun j => γ (s j) : Fin (m' + 1) → _) j) := fun j =>
      Fin.cases (by simpa using hvin) (fun k => by simpa using inRCone_self γ (s k)) j
    have hle : ∀ j, (h ((Fin.cons v fun j => γ (s j) : Fin (m' + 1) → _) j) : ℝ) ≤ h v := fun j =>
      Fin.cases (by simp) (fun k => by
        simp only [Fin.cons_succ]; rw [(hcut.2 (s k)).2 ⟨k, rfl⟩]; simpa using hh.le) j
    refine ⟨m' + 1, Fin.cons v fun j => γ (s j), fun j => Fin.cases hv (fun k => hγ.mem (s k)) j,
      fun j => Fin.cases hvp (fun k => hγ.nonneg (s k)) j, linearOn_of_forall_inRCone ψ hγ.linear hmem,
      linearOn_starDepth (lin2 X hX m γ hγ v hv hvp hvw hvin m' s h hcut hh),
      fun j => Fin.cases (hb' v hv hvp hvw hvin) (fun k => hb (s k)) j, fun j => ?_, hin⟩
    rw [← evalR_toReal]
    refine evalR_starDepth_le _ H.bar ψ w X m γ _ 1 hγ (hmem j) zero_le_one fun v' a1 a2 a3 a4 t _ ht => ?_
    rw [hC3 m γ hγ v' a1 a2 v hv hvp a3 hvw a4 hvin] at ht
    have := (mul_le_of_sub_mem_rcone hcut.1 ht).trans (hle j)
    nlinarith
  · have hno : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0 := fun v a1 a2 a3 =>
      (hC1 v a1 a2).resolve_right fun a4 => hc ⟨v, a1, a2, a4, a3⟩
    refine ⟨m, γ, hγ.mem, hγ.nonneg, hγ.linear, linearOn_starDepth (lin1 X hX m γ hγ hno), hb, fun j => ?_, hβ⟩
    rw [← evalR_toReal]
    exact evalR_starDepth_le _ H.bar ψ w X m γ _ 1 hγ (inRCone_self γ j) zero_le_one fun v' a1 a2 a3 a4 _ _ _ =>
      (hc ⟨v', a1, a2, a3, a4⟩).elim

theorem per_module (hψ : IsPolyFan H.bar q ψ) (hw : IsCentreSet H.bar q ψ w) (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (hX : Module.finrank (𝓞 E) X ≤ q) :
    ∃ b : ℕ, ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) →
      ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms H.bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧
      ψ.LinearOn u ∧ (starDepth H.bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧
      (∀ i, (starDepth H.bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β := by
  obtain ⟨S, hS, hcov⟩ := (hψ X hX).finite
  obtain ⟨b, hb⟩ := exists_nat_bound (hS.union (centres_finite H hw X hX hS)) fun v => ψ.evalZ v
  refine ⟨b, fun β hβ hp => ?_⟩
  obtain ⟨e, m, γ, c, hγ, hγS, hc, hsum⟩ := hcov _ (toReal_mem_psdCone_of_nonneg E H X β hβ hp)
  refine transport e (of_cell H hw X hX hγ (fun i => hb _ (Or.inl (hγS i)))
    (fun v a1 a2 a3 a4 => hb _ (Or.inr ⟨a1, a2, a3, m, γ, hγ, hγS, a4⟩)) ⟨c, hc, ?_⟩)
  rw [← hsum]
  exact LinearMap.ext₂ fun x y => by simp

end CM

theorem exists_bounded_gens : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∃ b : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms H.bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧ ψ.LinearOn u ∧ (starDepth H.bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧ (∀ i, (starDepth H.bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β := by
  intro E _ _ _ H q ψ w hψ hw
  obtain ⟨n, R, hR, hiso⟩ := GlobalTheory.exists_fin_reps_projective_finrank_le E q
  have key := fun k => @per_module E _ _ _ H q ψ w hψ hw (R k) _ _ (hR k).1 (hR k).2.1 (hR k).2.2
  choose b hb using key
  refine ⟨Finset.univ.sup b, fun X _ _ _ _ hX β hβ hp => ?_⟩
  obtain ⟨k, ⟨f⟩⟩ := hiso X hX
  haveI := (hR k).1
  obtain ⟨m, u, h1, h2, h3, h4, h5, h6, h7⟩ := hb k (pull f.symm.toLinearMap β) (pull_mem _ hβ) fun y => hp _
  have hk : (b k : ℝ) ≤ (Finset.univ.sup b : ℕ) := by exact_mod_cast Finset.le_sup (f := b) (Finset.mem_univ k)
  exact transport f.symm ⟨m, u, h1, h2, h3, h4, fun i => (h5 i).trans hk, h6, h7⟩

end GlobalTheory.PolFan.StarGens
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedGeneratorsStarSubdivisionConeStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.exists_bounded_generators_star_subdivision_cone : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∃ b : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms H.bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧ ψ.LinearOn u ∧ (starDepth H.bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧ (∀ i, (starDepth H.bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β := by
  first | exact @GlobalTheory.PolFan.StarGens.exists_bounded_gens | exact GlobalTheory.PolFan.StarGens.exists_bounded_gens | (intros; apply GlobalTheory.PolFan.StarGens.exists_bounded_gens <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBoundsStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.exists_uniform_strictness_and_face_cut_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → ∃ N₀ C₀ : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ N ≤ N₀ ∧ StrictWith H.bar ψ N ℓ γ ∧ ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → ∃ h' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, IsFaceCut γ s h' ∧ (∀ β, InRCone γ β → 0 < h β → 0 < h' β) ∧ ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → -(h' β) ≤ C₀ * ℓ β := by
  first | exact @GlobalTheory.PolFan.StrictData.exists_strict_data | exact GlobalTheory.PolFan.StrictData.exists_strict_data | (intros; apply GlobalTheory.PolFan.StrictData.exists_strict_data <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthCommonDenominatorRankLeStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.starDepth_common_denominator_rank_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∃ D₀ : ℕ, 0 < D₀ ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (D₀ : ℝ) * (starDepth H.bar ψ w).evalZ β = n := by
  first | exact @GlobalTheory.PolFan.StarDen.starDepth_den | exact GlobalTheory.PolFan.StarDen.starDepth_den | (intros; apply GlobalTheory.PolFan.StarDen.starDepth_den <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeStrictnessGapOffCentresStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.starDepth_le_strictnessGap_off_centres : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → 0 < N → StrictWith H.bar ψ N ℓ γ → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (starDepth H.bar ψ w).evalZ β ≤ ℓ β - N * ψ.evalZ β := by
  first | exact @GlobalTheory.PolFan.StarGap.starDepth_le_gap | exact GlobalTheory.PolFan.StarGap.starDepth_le_gap | (intros; apply GlobalTheory.PolFan.StarGap.starDepth_le_gap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionEstimateOffCentreCellStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.star_subdivision_estimate_off_centre_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)) (b : ℕ), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms H.bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧ ψ.LinearOn u ∧ (starDepth H.bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧ (∀ i, (starDepth H.bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → 0 < N → StrictWith H.bar ψ N ℓ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → ∀ C : ℕ, (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → -(h β) ≤ C * ℓ β) → ∀ K : ℕ, N + N * C + N ^ 2 * C * b + 1 ≤ K → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ¬ InRCone γ β → (N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ β - N * h β < K * h β₀ * (ℓ β - N * ψ.evalZ β) := by
  first | exact @GlobalTheory.PolFan.StarKey.OffCell.off_cell | exact GlobalTheory.PolFan.StarKey.OffCell.off_cell | (intros; apply GlobalTheory.PolFan.StarKey.OffCell.off_cell <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionFunctionIntegralStrictlyCon

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarKey

theorem exists_starFun_strict : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∃ K D : ℕ, 0 < K ∧ 0 < D ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (starFun H.bar ψ w K D).evalZ β = n) ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsStrict H.bar (starFun H.bar ψ w K D) γ) ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsStrict H.bar (starFun H.bar ψ w K D) (Fin.cons β₀ fun j => γ (s j))) := by
  intro E _ _ _ H q ψ w hdom hψ hcs
  obtain ⟨D₀, hD₀, hint⟩ := GlobalTheory.T.starDepth_common_denominator_rank_le E H q ψ w hψ hcs
  obtain ⟨N₀, C₀, hdata⟩ := GlobalTheory.T.exists_uniform_strictness_and_face_cut_bounds E H q ψ hdom hψ
  obtain ⟨b, hgens⟩ := GlobalTheory.T.exists_bounded_generators_star_subdivision_cone E H q ψ w hψ hcs
  have hD₀r : (0 : ℝ) < D₀ := by exact_mod_cast hD₀
  refine ⟨N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1, D₀, by omega, hD₀, ?_, ?_, ?_⟩
  · intro X _ _ _ _ hX β hβ hp
    obtain ⟨n₁, hn₁⟩ := (hψ X hX).integral β hβ hp
    obtain ⟨n₂, hn₂⟩ := hint X hX β hβ hp
    refine ⟨D₀ * (N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1) * n₁ + n₂, ?_⟩
    rw [starFun_evalZ, hn₁]
    push_cast
    linear_combination hn₂
  · intro X _ _ _ _ hX m γ hγ hnoc
    obtain ⟨N, ℓ, hN, hNN, hsw, -⟩ := hdata X hX m γ hγ
    have hgap := GlobalTheory.T.starDepth_le_strictnessGap_off_centres E H q ψ w hψ hcs X hX m γ N ℓ hγ hnoc hN hsw
    have hnn : ∀ β : LinearMap.BilinForm ℤ X, 0 ≤ (starDepth H.bar ψ w).evalZ β := fun β =>
      starDepth_eval_nonneg (fun a b => (β a b : ℝ))
    set K := N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1 with hKdef
    have hKN : (N : ℝ) + 1 ≤ K := by
      have : N + 1 ≤ K := by rw [hKdef]; omega
      exact_mod_cast this
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    refine ⟨N, ((D₀ * K : ℕ) : ℤ) • ℓ, hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
    · have h0 := hsw.1 i
      have hps : (starDepth H.bar ψ w).evalZ (γ i) = 0 :=
        le_antisymm (by have := hgap (γ i) (hγ.mem i) (hγ.nonneg i); linarith) (hnn _)
      rw [starFun_evalZ, hps]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      push_cast
      rw [h0]; ring
    · have hg := hgap β hβ hp
      have hf := hsw.2.1 β hβ hp
      have hps := hnn β
      rw [starFun_evalZ]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      push_cast
      set P := (starDepth H.bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      set L : ℝ := (ℓ β : ℝ)
      have k1 : (N : ℝ) * P ≤ K * (L - N * Ψ) := by nlinarith [mul_le_mul_of_nonneg_left hg hN0]
      nlinarith [mul_le_mul_of_nonneg_left k1 hD₀r.le]
    · have hg := hgap β hβ hp
      have hf := hsw.2.1 β hβ hp
      have hps := hnn β
      rw [starFun_evalZ] at he
      simp only [LinearMap.smul_apply, smul_eq_mul] at he
      push_cast at he
      set P := (starDepth H.bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      set L : ℝ := (ℓ β : ℝ)
      have e1 : (N : ℝ) * P = K * (L - N * Ψ) := by
        have := mul_left_cancel₀ hD₀r.ne' (show (D₀ : ℝ) * (N * P) = D₀ * (K * (L - N * Ψ)) by linear_combination he)
        exact this
      have e2 : L - N * Ψ = 0 := by nlinarith [mul_le_mul_of_nonneg_left hg hN0]
      exact hsw.2.2 β hβ hp (by linarith)
  · intro X _ _ _ _ hX m γ hγ β₀ hβ₀ hp₀ hw₀ hin₀ m' s h hcut hpos
    obtain ⟨N, ℓ, hN, hNN, hsw, hcuts⟩ := hdata X hX m γ hγ
    obtain ⟨h', hcut', hpos', hdom'⟩ := hcuts m' s h hcut
    have hp' : 0 < h' β₀ := hpos' β₀ hin₀ hpos
    obtain ⟨hin, hone, hzero, heq⟩ :=
      GlobalTheory.T.starDepth_le_on_centre_cell E H q ψ w hψ hcs X hX m γ hγ β₀ hβ₀ hp₀ hw₀ hin₀ m' s h' hcut' hp'
    set K := N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1 with hKdef
    have hKb : N + N * C₀ + N ^ 2 * C₀ * b + 1 ≤ K := by
      rw [hKdef]
      have h1 : N * C₀ ≤ N₀ * C₀ := Nat.mul_le_mul_right _ hNN
      have h2 : N ^ 2 * C₀ * b ≤ N₀ ^ 2 * C₀ * b :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hNN 2))
      omega
    have hoff := GlobalTheory.T.star_subdivision_estimate_off_centre_cell E H q ψ w b hψ hcs X hX (hgens X hX) m γ N ℓ hγ hN hsw β₀ hβ₀ hp₀ hw₀ hin₀ m' s h'
      hcut' hp' C₀ hdom' K hKb
    have hlinγ : ∀ β, InRCone γ β → (ℓ β : ℝ) = N * ψ.evalZ β := fun β hβ => StarKey.ell_eq_of_inRCone hγ.linear hsw hβ
    have hcast : (((h' β₀).toNat : ℕ) : ℝ) = (h' β₀ : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hp'.le]
    have hH0 : (0 : ℝ) < h' β₀ := by exact_mod_cast hp'
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    refine ⟨N * (h' β₀).toNat, (D₀ : ℤ) • (((K : ℤ) * h' β₀) • ℓ + (N : ℤ) • h'), by
      have : 0 < (h' β₀).toNat := by omega
      positivity, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        rw [starFun_evalZ, hone]
        have hl := hlinγ β₀ hin₀
        simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
        push_cast
        rw [hcast, hl]; ring
      · simp only [Fin.cons_succ]
        have hh : h' (γ (s j)) = 0 := (hcut'.2 (s j)).2 ⟨j, rfl⟩
        rw [starFun_evalZ, hzero j]
        simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul, hh]
        push_cast
        rw [hcast, hsw.1 (s j)]; ring
    · rw [starFun_evalZ]
      simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
      push_cast
      rw [hcast]
      set P := (starDepth H.bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      by_cases hc : InRCone γ β
      · have hl := hlinγ β hc
        have hi := hin β hβ hp hc
        rw [hl]
        nlinarith [mul_le_mul_of_nonneg_left hi (mul_nonneg hD₀r.le hN0.le)]
      · have ho := hoff β hβ hp hc
        nlinarith [mul_lt_mul_of_pos_left ho hD₀r]
    · rw [starFun_evalZ] at he
      simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul] at he
      push_cast at he
      rw [hcast] at he
      set P := (starDepth H.bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      by_cases hc : InRCone γ β
      · have hl := hlinγ β hc
        rw [hl] at he
        refine heq β hβ hp hc ?_
        have : ((D₀ : ℝ) * N) * ((h' β₀ : ℝ) * P) = ((D₀ : ℝ) * N) * (h' β : ℝ) := by linear_combination he
        exact mul_left_cancel₀ (mul_pos hD₀r hN0).ne' this
      · have ho := hoff β hβ hp hc
        nlinarith [mul_lt_mul_of_pos_left ho hD₀r]

end GlobalTheory.PolFan.StarKey
end
end
