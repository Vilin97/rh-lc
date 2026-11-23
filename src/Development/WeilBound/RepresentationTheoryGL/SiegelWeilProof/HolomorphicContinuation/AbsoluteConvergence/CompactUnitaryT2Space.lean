module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ClmCircleIntegral
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FactorL
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BanachHol
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LamLocal
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LamLocal
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TopSing
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMapBis
import Mathlib.Tactic.Polynomial.Basic
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacCore
import Mathlib.Tactic.Linter.Style

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LamCont

section

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] {ε : Fin m → Bool} {c t : ℝ}
  {sL : PX m n →ₗ[ℂ] (GR n → ℂ)} {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ}
  {Ht : G → ℝ≥0} {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem lam_cont (hBH : BanachHol) (hFL : FactorL) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    (l : (G → ℂ) → ℂ) (hl : l ∈ Λ) {B : Set ℂ} (hB : IsOpen B) {w : ℂ} (hw : w ∈ B) (F : ℂ → G → ℂ)
    (hFc : ContinuousOn (fun y : ℂ × G => F y.1 y.2) (B ×ˢ univ)) (hFh : ∀ g, DifferentiableOn ℂ (F · g) B)
    (hFi : ∀ z ∈ B, ∀ γ ∈ Γ, ∀ g, F z (γ * g) = F z g) : ContinuousAt (fun z => l (F z)) w := by
  obtain ⟨C, hCc, hCb⟩ := hG.Λbd l hl
  obtain ⟨L, hL⟩ := hFL G (invSub Γ) l C hCc (fun F hF => hF.1)
    (fun a F hF F' hF' => hG.Λadd l hl a F F' hF.1 hF'.1 hF.2 hF'.2)
    (fun F hF M hM => hCb F M hF.1 hF.2 hM)
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  have hFcont : ∀ z ∈ B, Continuous (F z) := by
    intro z hzB
    exact hFc.comp_continuous (continuous_const.prodMk continuous_id) (fun g => ⟨hzB, mem_univ g⟩)
  obtain ⟨Φ, hΦd, hΦ⟩ := hBH C B (fun z x => F z x) hB
    (hFc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun y hy => ⟨hy.1, mem_univ _⟩))
    (fun x => hFh x)
  have hfeq : ∀ z ∈ B, l (F z) = L (Φ z) := by
    intro z hzB
    have hmem : F z ∈ invSub Γ := ⟨hFcont z hzB, hFi z hzB⟩
    rw [hL (F z) hmem (hFcont z hzB)]
    congr 1
    ext x
    rw [hΦ z hzB x]
    rfl
  have hd : DifferentiableOn ℂ (fun z => l (F z)) B :=
    (L.differentiable.comp_differentiableOn hΦd).congr hfeq
  exact (hd.differentiableAt (hB.mem_nhds hw)).continuousAt

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RootsBound

section

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem roots_bound (d : Polynomial ℂ) (hd : d ≠ 0) : ∃ σ : ℝ, ∀ z : ℂ, σ < z.re → d.eval z ≠ 0 := by
  refine ⟨∑ r ∈ d.roots.toFinset, |r.re|, fun z hz h0 => ?_⟩
  have hm : z ∈ d.roots.toFinset := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hd).mpr h0)
  have h1 : |z.re| ≤ ∑ r ∈ d.roots.toFinset, |r.re| :=
    Finset.single_le_sum (f := fun r : ℂ => |r.re|) (fun r _ => abs_nonneg _) hm
  linarith [le_abs_self z.re]

theorem top_E [MeasurableSpace (KR n)] [BorelSpace (KR n)] [CompactSpace (KR n)] (μ : Measure (KR n))
    [IsFiniteMeasure μ] (hL : LocData ε c t p q e sL ρ) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (hD : CayleyBlocksInvertible)
    (hHP : HolParam) {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n} (hnbc : Continuous nb)
    {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) {cz : ℂ → ℂ}
    (hczd : Differentiable ℂ cz)
    (hceig : ∀ (w : ℂ) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * a * nb x * b) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) ∂μ = cz w * ((hLoc y : ℂ) ^ w * F0 p q e y))
    {U : Set ℂ} {d : Polynomial ℂ} {E : ℂ → G → ℂ} {σ : ℝ} (hUo : IsOpen U) (hUr : GlobalTheory.Cont.IsRightDomain U)
    (hd : d ≠ 0) (hEh : ∀ g, DifferentiableOn ℂ (fun z => E z g) U)
    (hEc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ univ))
    (hEr : ∀ z : ℂ, σ < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ q,
        ‖GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g q‖ ≤ u q) ∧
      ∀ g, E z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x) g) :
    ∀ z ∈ U, ∀ g, Top μ ι p q e a b nb ψ (E z) g = cz (z - s₀) * E z g := by
  have hsm : ∀ (c : ℂ) (F : G → ℂ) (g : G),
      Top μ ι p q e a b nb ψ (fun x => c * F x) g = c * Top μ ι p q e a b nb ψ F g := by
    intro c F g
    simp only [Top, mul_assoc c]
    simp_rw [integral_const_mul, mul_left_comm _ c, integral_const_mul]
  intro z hzU g
  have hdiff : DifferentiableOn ℂ
      (fun w => Top μ ι p q e a b nb ψ (E w) g - cz (w - s₀) * E w g) U := by
    have h1 : DifferentiableOn ℂ (fun w => Top μ ι p q e a b nb ψ (E w) g) U :=
      top_hol (p := p) (q := q) (e := e) (a := a) (b := b) μ hD hHP hG.ιcont hnbc hψc hψs hUo E hEc hEh g
    have h2 : DifferentiableOn ℂ (fun w => cz (w - s₀)) U :=
      (hczd.comp (differentiable_id.sub_const s₀)).differentiableOn
    exact h1.sub (h2.mul (hEh g))
  have hVo : IsOpen (connectedComponentIn U z) := hUo.connectedComponentIn
  have hVU : connectedComponentIn U z ⊆ U := connectedComponentIn_subset U z
  have han := (hdiff.mono hVU).analyticOnNhd hVo
  have hray : (fun t : ℝ => z + (t : ℂ)) '' Ici 0 ⊆ connectedComponentIn U z := by
    apply IsPreconnected.subset_connectedComponentIn
    · exact isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ => z + (t : ℂ)).continuousOn
    · exact ⟨0, Set.mem_Ici.mpr le_rfl, by simp⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact hUr.2 z hzU t ht
  have hT : (0 : ℝ) ≤ max 0 (σ - z.re) + 1 := by
    have := le_max_left 0 (σ - z.re)
    linarith
  have hw0 : z + ((max 0 (σ - z.re) + 1 : ℝ) : ℂ) ∈ connectedComponentIn U z := hray ⟨_, hT, rfl⟩
  have hre : σ < (z + ((max 0 (σ - z.re) + 1 : ℝ) : ℂ)).re := by
    have := le_max_right 0 (σ - z.re)
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hev : (fun w => Top μ ι p q e a b nb ψ (E w) g - cz (w - s₀) * E w g)
      =ᶠ[𝓝 (z + ((max 0 (σ - z.re) + 1 : ℝ) : ℂ))] 0 := by
    have hopen : IsOpen {w : ℂ | σ < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hre] with w hw
    have hEw : E w = fun x => d.eval w * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w) x :=
      funext fun x => (hEr w hw).2 x
    have hs := top_sum μ hL hG hD hG.ιcont hnbc hψc hψs hceig w (hEr w hw).1 g
    simp only [Pi.zero_apply]
    rw [hEw, hsm (d.eval w) (fun x => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ w) x), hs]
    ring
  have h := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_connectedComponentIn
    hw0 hev (mem_connectedComponentIn hzU)
  simp only [Pi.zero_apply] at h
  exact sub_eq_zero.mp h

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TopTheta

section

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem top_theta [MeasurableSpace (KR n)] [BorelSpace (KR n)] [CompactSpace (KR n)] (μ : Measure (KR n))
    [IsFiniteMeasure μ] (hD : CayleyBlocksInvertible) (hιc : Continuous ι) {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n}
    (hnbc : Continuous nb) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) {cz : ℂ → ℂ}
    (hceig : ∀ (w : ℂ) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * a * nb x * b) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) ∂μ = cz w * ((hLoc y : ℂ) ^ w * F0 p q e y))
    (I1 : G → ℂ) (hIc : Continuous I1)
    (hTS : ∀ (g : G) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * I1 (g * ι ((k : GR n) * y)) ∂μ =
      I1 g * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * y) ∂μ) (g : G) :
    Top μ ι p q e a b nb ψ I1 g = cz 0 * I1 g := by
  have hswap : ∀ Φ : GR n → ℂ, Continuous Φ →
      ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, Φ ((k : GR n) * a * nb x * b) * ψ x) ∂μ =
      ∫ x, (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * Φ ((k : GR n) * (a * nb x * b)) ∂μ) * ψ x := by
    intro Φ hΦ
    have hcont : Continuous (fun z : KR n × (Fin n → Fin n → ℝ) =>
        (F0 p q e (z.1 : GR n))⁻¹ * (Φ ((z.1 : GR n) * a * nb z.2 * b) * ψ z.2)) := by
      refine Continuous.mul ?_ (Continuous.mul ?_ (hψc.comp continuous_snd))
      · exact ((continuous_weight_factor hD p q e).comp (continuous_subtype_val.comp continuous_fst)).inv₀
          (fun z => spherical_section_ne_zero hD p q e _)
      · exact hΦ.comp ((((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
          (hnbc.comp continuous_snd)).mul continuous_const)
    have hsupp : HasCompactSupport (fun z : KR n × (Fin n → Fin n → ℝ) =>
        (F0 p q e (z.1 : GR n))⁻¹ * (Φ ((z.1 : GR n) * a * nb z.2 * b) * ψ z.2)) := by
      refine HasCompactSupport.intro' (K := univ ×ˢ tsupport ψ) (isCompact_univ.prod hψs)
        (isClosed_univ.prod (isClosed_tsupport ψ)) ?_
      intro z hz
      have hz2 : z.2 ∉ tsupport ψ := fun h => hz ⟨mem_univ _, h⟩
      simp [image_eq_zero_of_notMem_tsupport hz2]
    have hint := hcont.integrable_of_hasCompactSupport (μ := μ.prod volume) hsupp
    calc _ = ∫ k : KR n, (∫ x, (F0 p q e (k : GR n))⁻¹ * (Φ ((k : GR n) * a * nb x * b) * ψ x)) ∂μ := by
          congr 1
          funext k
          exact (integral_const_mul _ _).symm
      _ = ∫ x, (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (Φ ((k : GR n) * a * nb x * b) * ψ x) ∂μ) :=
          integral_integral_swap
            (f := fun (k : KR n) (x : Fin n → Fin n → ℝ) =>
              (F0 p q e (k : GR n))⁻¹ * (Φ ((k : GR n) * a * nb x * b) * ψ x)) hint
      _ = _ := by
          congr 1
          funext x
          rw [← integral_mul_const]
          congr 1
          funext k
          simp only [mul_assoc]
  have h1 := hswap (fun y => I1 (g * ι y)) (hIc.comp (continuous_const.mul hιc))
  have h2 := hswap (F0 p q e) (continuous_weight_factor hD p q e)
  have hc := hceig 0 1
  simp only [Complex.cpow_zero, one_mul, mul_one, weight_factor_one] at hc
  unfold Top
  rw [h1]
  simp_rw [hTS g]
  have hpull : ∫ x, (I1 g * ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (a * nb x * b)) ∂μ) * ψ x =
      I1 g * ∫ x, (∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * F0 p q e ((k : GR n) * (a * nb x * b)) ∂μ) * ψ x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hpull, ← h2, hc, mul_comm]

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CompactUnitaryT2Space

section

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.Vac

private theorem vacOut_of'_lemma (n : ℕ) : CompactSpace (KR n) := by
  have hb : ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ, Matrix.conjTranspose g * g = 1 → ∀ i j, ‖g i j‖ ≤ 1 := by
    intro g hg i j
    exact entry_norm_bound_of_unitary (Matrix.mem_unitaryGroup_iff'.mpr hg) i j
  have hS : IsCompact {g : M2 n | InG g ∧ Matrix.conjTranspose g * g = 1} := by
    have hbox : IsCompact (Set.pi univ fun _ : Fin n ⊕ Fin n => Set.pi univ fun _ : Fin n ⊕ Fin n => Metric.closedBall (0 : ℂ) 1) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
    refine hbox.of_isClosed_subset ?_ ?_
    · change IsClosed ({g : M2 n | InG g} ∩ {g : M2 n | Matrix.conjTranspose g * g = 1})
      refine IsClosed.inter ?_ ?_
      · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const
      · exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
    · intro g hg i _ j _
      simpa using hb g hg.2 i j
  have hcl : IsClosed (range fun k : KR n => mR (k : GR n)) := by
    convert hS.isClosed using 1
    ext g
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k.1.2, k.2.2⟩
    · rintro ⟨hG, hg⟩
      let u : GL (Fin n ⊕ Fin n) ℂ := ⟨g, Matrix.conjTranspose g, mul_eq_one_comm.mp hg, hg⟩
      exact ⟨⟨⟨u, hG⟩, ⟨hG, hg⟩⟩, rfl⟩
  constructor
  rw [(kr_inducing n).isCompact_iff, Set.image_univ]
  refine hS.of_isClosed_subset hcl ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨k.1.2, k.2.2⟩

theorem vacOut_of' (hD : CayleyBlocksInvertible) (hLO : LocOp) (hHP : HolParam) (hTS : ThSph) : VacOut := by
  intro m n ε c t p q e sL ρ hL hGS G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I Λ hG
  haveI := vacOut_of'_lemma n
  letI : MeasurableSpace (KR n) := borel _
  haveI : BorelSpace (KR n) := ⟨rfl⟩
  let μ : Measure (KR n) := Measure.haarMeasure ⊤
  haveI : μ.IsHaarMeasure := by infer_instance
  haveI : IsProbabilityMeasure μ := ⟨by simpa using Measure.haarMeasure_self (G := KR n) (K₀ := ⊤)⟩
  obtain ⟨ψ, a, b, nb, cz, hψ, hnb, hnbc, hcz, hcz0, hid⟩ := hLO n p q e hGS μ
  obtain ⟨U, d, E, σ, hU, hR, hs, hd, hEd, hEc, hEi, hEs⟩ := hG.eis
  have hψc := hψ.1
  have hψs := hψ.2.1
  obtain ⟨d1, hdd, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd d hd s₀
  have hd1 : Polynomial.eval s₀ d1 ≠ 0 := fun h => hnd (Polynomial.dvd_iff_isRoot.mpr h)
  set k₀ := d.rootMultiplicity s₀
  have hdeval : ∀ z, Polynomial.eval z d = (z - s₀) ^ k₀ * Polynomial.eval z d1 := by
    intro z
    conv_lhs => rw [hdd]
    simp [Polynomial.eval_mul, Polynomial.eval_pow]
  have hTE : ∀ z ∈ U, ∀ g, Vac.Top μ ι p q e a b nb ψ (E z) g = cz (z - s₀) * E z g :=
    top_E μ hL hG hD hHP hnbc hψc hψs hcz hid hU hR hd hEd hEc hEs
  have hTI : ∀ g, Vac.Top μ ι p q e a b nb ψ (I 1) g = cz 0 * I 1 g :=
    top_theta μ hD hG.ιcont hnbc hψc hψs hid (I 1) hG.Icont
      (fun g y => hTS m n ε c t p q e sL ρ hL G Pp Γ ι s₀ Ht sec I Λ hG μ g y)
  have hloc := lam_local banachHol factorL hG hU hR hs hd hEd hEc hEi (fun z hz g => (hEs z hz).2 g)
  have hloc' : ∀ l ∈ Λ, ∃ H : ℂ → ℂ, ContinuousAt H s₀ ∧ H s₀ = l (I 1) ∧
      ∀ᶠ z in 𝓝[≠] s₀, l (E z) = (z - s₀) ^ k₀ * Polynomial.eval z d1 * H z := by
    intro l hl
    obtain ⟨H, hHa, hH0, hHe⟩ := hloc l hl
    refine ⟨H, hHa.continuousAt, hH0, ?_⟩
    filter_upwards [hHe] with z hz
    rw [hz, hdeval]
  obtain ⟨Ek, hEkc, hEkd, hEk, hEk0⟩ := core Γ Λ (Vac.Top μ ι p q e a b nb ψ) (I 1) s₀ U hU hs E cz k₀
    (fun z => Polynomial.eval z d1) dslopeFam hcz.continuous hcz0 (Polynomial.continuous d1).continuousAt
    hG.Λadd (fun l hl F hFc hFd hFi => lam_cont banachHol factorL hG l hl hU hs F hFc hFd hFi) hloc'
    (fun F hF hFi hΛ g => top_sing μ hG hψ hnb F hF hFi hΛ g)
    (fun a' F F' hF hF' g => top_linear μ hD hG.ιcont hnbc hψc hψs F F' hF hF' a' g)
    hG.Icont hG.Ileft hTI
    (fun F hFc hFd g => (top_hol μ hD hHP hG.ιcont hnbc hψc hψs hU F hFc hFd g).continuousOn)
    hEc hEd hEi hTE
  have hnear : ∀ᶠ z in 𝓝 s₀, z ∈ U ∧ Polynomial.eval z d1 ≠ 0 :=
    (show ∀ᶠ z in 𝓝 s₀, z ∈ U from hU.mem_nhds hs).and
      ((Polynomial.continuous d1).continuousAt.eventually_ne hd1)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hsub : Metric.ball s₀ r ⊆ U := fun z hz => (hball hz).1
  have hFd : ∀ g, DifferentiableOn ℂ (fun z => Ek z g / Polynomial.eval z d1) (Metric.ball s₀ r) :=
    fun g => ((hEkd g).mono hsub).div (Polynomial.differentiable d1).differentiableOn
      (fun z hz => (hball hz).2)
  obtain ⟨σ2, hσ2⟩ := roots_bound d hd
  have hmain : ∀ g, ∀ z ∈ Metric.ball s₀ r, GlobalTheory.Cont.HolValueAt
      (fun w => GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (w - s₀) * sec 1 x) g) z
      (Ek z g / Polynomial.eval z d1) := by
    intro g z hz
    have hext : GlobalTheory.Cont.IsExtAt
        (fun w => GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (w - s₀) * sec 1 x) g) z
        (fun w => E w g / Polynomial.eval w d) := by
      refine ⟨U, hsub hz, hR, ?_, ?_⟩
      · intro w hw
        exact (((hEd g).analyticAt (hU.mem_nhds hw)).meromorphicAt).div
          ((Polynomial.differentiable d).analyticAt w).meromorphicAt
      · refine ⟨max σ σ2, fun w hw => ?_⟩
        have hw1 : σ < w.re := lt_of_le_of_lt (le_max_left _ _) hw
        have hw2 : σ2 < w.re := lt_of_le_of_lt (le_max_right _ _) hw
        show E w g / Polynomial.eval w d = _
        rw [(hEs w hw1).2 g, mul_div_cancel_left₀ _ (hσ2 w hw2)]
    rw [hext.holValueAt_iff]
    have hFc : ContinuousAt (fun w => Ek w g / Polynomial.eval w d1) z :=
      (hFd g).continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hz)
    refine (hFc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    have hev : ∀ᶠ w in 𝓝[≠] z, w ∈ Metric.ball s₀ r ∧ w ≠ s₀ := by
      by_cases hzs : z = s₀
      · subst hzs
        exact eventually_mem_ne z _ Metric.isOpen_ball hz
      · exact nhdsWithin_le_nhds ((Metric.isOpen_ball.inter isOpen_ne).mem_nhds ⟨hz, hzs⟩)
    filter_upwards [hev] with w hw
    have hpow : (w - s₀) ^ k₀ ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hw.2)
    show Ek w g / Polynomial.eval w d1 = E w g / Polynomial.eval w d
    rw [hEk w (hsub hw.1) g, hdeval w, mul_div_mul_left _ _ hpow]
  have hval : ∀ g, Ek s₀ g / Polynomial.eval s₀ d1 = I 1 g := fun g => by
    rw [hEk0 g, mul_div_cancel_left₀ _ hd1]
  refine ⟨r, 0, fun z g => Ek z g / Polynomial.eval z d1, hr, subset_union_right, ?_, hFd, hval, ?_, hmain⟩
  · exact (hEkc.mono (prod_mono hsub subset_rfl)).div
      ((Polynomial.continuous d1).comp continuous_fst).continuousOn (fun y hy => (hball hy.1).2)
  · intro g
    have h0 := hmain g s₀ (Metric.mem_ball_self hr)
    rwa [hval g] at h0

end PositivityTheory.Rg.Sw.AbsSt
end
end
end
