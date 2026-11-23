module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PReproB
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.BridgeSt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.MultHasCompactSupport
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarRightInvariantCompact
import Mathlib.Topology.Compactness.Paracompact
import GroundTheory.AutomorphicForms.RealGroups
import GroundTheory.AutomorphicForms.ReductionMeasure
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PReproCa

section

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.RgBcC

namespace PositivityTheory.Rg.BcB.CG.ReproL

theorem norm_cosh_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖Complex.cosh z - 1‖ ≤ 2 * ‖z‖ := by
  have h1 := Complex.norm_exp_sub_one_le hz
  have h2 := Complex.norm_exp_sub_one_le (x := -z) (by rwa [norm_neg])
  rw [norm_neg] at h2
  have e : Complex.cosh z - 1 = ((Complex.exp z - 1) + (Complex.exp (-z) - 1)) / 2 := by
    rw [show Complex.cosh z = (Complex.exp z + Complex.exp (-z)) / 2 from rfl]; ring
  rw [e, norm_div]
  have h3 := norm_add_le (Complex.exp z - 1) (Complex.exp (-z) - 1)
  have h4 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h4]
  linarith

theorem continuous_cas (N : ℕ) : Continuous fun χ : Inf N => cas χ := by
  have hA : ∀ f : Inf N → Fin N → ℂ, Continuous f → Continuous fun χ => Formalism.REAL.Amat (f χ) := by
    intro f hf
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    split_ifs
    · exact (continuous_apply a).comp hf
    · exact continuous_const
    · exact continuous_const
  have hg : ∀ s : Bool, Continuous fun χ : Inf N => GlobalTheory.Dec.gelfVal (χ s) 2 := by
    intro s
    unfold GlobalTheory.Dec.gelfVal
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
    have hf : Continuous fun χ : Inf N => fun c : Fin N => χ s c + ((N : ℂ) - 1) / 2 :=
      continuous_pi fun c => (continuous_apply_apply s c).add continuous_const
    exact ((hA _ hf).pow 2).matrix_elem a b
  unfold cas
  exact continuous_const.mul ((hg true).add (hg false))

theorem exists_bump (N : ℕ) (R : ℝ) : ∃ (g : ℝ → ℝ) (T : ℝ), 0 < T ∧ IsBump g T ∧
    ∀ χ : Inf N, (∀ s i, ‖χ s i‖ ≤ R) → 1 / 2 ≤ ‖coshT g (cas χ)‖ := by
  have hS : IsCompact {χ : Inf N | ∀ s i, ‖χ s i‖ ≤ R} := by
    have e : {χ : Inf N | ∀ s i, ‖χ s i‖ ≤ R} =
        Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) R := by
      ext χ; simp [Set.mem_pi]
    rw [e]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (continuous_cas N).continuousOn
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set s := Real.sqrt C' with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set T : ℝ := 1 / (4 * (s + 1)) with hT
  have hT0 : 0 < T := by positivity
  have hTs : T * s ≤ 1 / 4 := by
    rw [hT, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  let f : ContDiffBump (0 : ℝ) := ⟨T / 2, T, by positivity, by linarith⟩
  set g : ℝ → ℝ := f.normed volume with hg
  have hsupp : ∀ t, g t ≠ 0 → |t| < T := by
    intro t ht
    have : t ∈ Function.support g := ht
    rw [hg, ContDiffBump.support_normed_eq] at this
    simpa [Metric.mem_ball, Real.dist_eq] using this
  refine ⟨g, T, hT0, ⟨ContDiffBump.contDiff_normed f, fun t => ?_, fun t ht => ?_⟩, ?_⟩
  · have := ContDiffBump.normed_neg f (μ := volume) t
    simpa [hg] using this
  · by_contra h
    exact absurd (hsupp t h) (not_lt.2 ht.le)
  intro χ hχ
  set c := cas χ with hc
  have hcC : ‖c‖ ≤ C' := (hC χ hχ).trans (le_max_left _ _)
  have hroot : ‖c ^ (1 / 2 : ℂ)‖ ≤ s := by
    have e : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_cpow_real, ← Real.sqrt_eq_rpow, hs]
    exact Real.sqrt_le_sqrt hcC
  have hgc : Continuous g := (ContDiffBump.contDiff_normed f (n := 0)).continuous
  have hgcs : HasCompactSupport g := ContDiffBump.hasCompactSupport_normed f
  have hgC : HasCompactSupport fun t => (g t : ℂ) := hgcs.comp_left Complex.ofReal_zero
  have hcont1 : Continuous fun t : ℝ => Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) :=
    Complex.continuous_cosh.comp (Complex.continuous_ofReal.mul continuous_const)
  have hi1 : Integrable fun t : ℝ => (g t : ℂ) * Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) :=
    ((Complex.continuous_ofReal.comp hgc).mul hcont1).integrable_of_hasCompactSupport (hgC.mul_right)
  have hi2 : Integrable fun t : ℝ => (g t : ℂ) :=
    (Complex.continuous_ofReal.comp hgc).integrable_of_hasCompactSupport hgC
  have hone : ∫ t, (g t : ℂ) = 1 := by
    rw [integral_complex_ofReal, hg, ContDiffBump.integral_normed]; simp
  have h3 : ∫ t, (g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1) =
      (∫ t, (g t : ℂ) * Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ))) - ∫ t, (g t : ℂ) := by
    rw [← integral_sub hi1 hi2]; congr 1; funext t; ring
  have hdiff : coshT g c - 1 = ∫ t, (g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1) := by
    rw [h3, hone]; rfl
  have hbound : ∀ t, ‖(g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1)‖ ≤ g t * (1 / 2) := by
    intro t
    by_cases h0 : g t = 0
    · simp [h0]
    have ht := hsupp t h0
    have hz : ‖(t : ℂ) * c ^ (1 / 2 : ℂ)‖ ≤ 1 / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |t| * ‖c ^ (1 / 2 : ℂ)‖ ≤ T * s := mul_le_mul ht.le hroot (norm_nonneg _) hT0.le
        _ ≤ 1 / 4 := hTs
    have hgt : 0 ≤ g t := ContDiffBump.nonneg_normed f t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgt]
    refine mul_le_mul_of_nonneg_left ?_ hgt
    calc ‖Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1‖ ≤ 2 * ‖(t : ℂ) * c ^ (1 / 2 : ℂ)‖ :=
          norm_cosh_sub_one_le (hz.trans (by norm_num))
      _ ≤ 1 / 2 := by linarith
  have hle : ‖coshT g c - 1‖ ≤ 1 / 2 := by
    rw [hdiff]
    calc ‖∫ t, (g t : ℂ) * (Complex.cosh ((t : ℂ) * c ^ (1 / 2 : ℂ)) - 1)‖ ≤ ∫ t, g t * (1 / 2) :=
          norm_integral_le_of_norm_le ((hgc.mul continuous_const).integrable_of_hasCompactSupport hgcs.mul_right)
            (Filter.Eventually.of_forall hbound)
      _ = 1 / 2 := by rw [integral_mul_const, hg, ContDiffBump.integral_normed]; ring
  have := norm_sub_norm_le (1 : ℂ) (1 - coshT g c)
  rw [sub_sub_cancel, norm_one, norm_sub_rev] at this
  linarith

theorem exists_enum {N : ℕ} (m : Multiset ℂ) (h : Multiset.card m = N) :
    ∃ e : Fin N → ℂ, Multiset.map e Finset.univ.val = m := by
  subst h
  refine ⟨fun i => m.toList.get (Fin.cast (by simp) i), ?_⟩
  rw [Fin.univ_val_map]
  have e : List.ofFn (fun i : Fin (Multiset.card m) => m.toList.get (Fin.cast (by simp) i)) = m.toList :=
    List.ext_get (by simp) (by simp)
  rw [e, Multiset.coe_toList]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem exists_chi (hB : Bridge.BridgeSt) (R : ℝ) (v : InfinitePlace E) (φ : Sm E N)
    (hR : PositivityTheory.Rg.BcB.SpectralAccumulation.InfBdd R (Submodule.span ℂ {φ})) :
    ∃ χ : Inf N, (∀ s i, ‖χ s i‖ ≤ R) ∧ ∀ g : GA E N, IsEig χ (Bridge.along v g φ.1) := by
  obtain ⟨m1, h1, b1⟩ := hR v.embedding
  obtain ⟨m2, h2, b2⟩ := hR (ComplexEmbedding.conjugate v.embedding)
  obtain ⟨e1, he1⟩ := exists_enum m1 h1.1
  obtain ⟨e2, he2⟩ := exists_enum m2 h2.1
  refine ⟨fun s => if s then e1 else e2, ?_, ?_⟩
  · intro s i
    cases s
    · exact b2 _ (he2 ▸ Multiset.mem_map_of_mem e2 (Finset.mem_univ_val i))
    · exact b1 _ (he1 ▸ Multiset.mem_map_of_mem e1 (Finset.mem_univ_val i))
  · intro g
    have key := (hB E N (Submodule.span ℂ {φ}) v (fun s => if s then e1 else e2)).2
      ⟨by simpa [he1] using h1, by simpa [he2] using h2⟩
    exact key φ (Submodule.mem_span_singleton_self φ) g

end PositivityTheory.Rg.BcB.CG.ReproL
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PReproCb

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField GlobalTheory.CuspRep
open scoped Pointwise
open PositivityTheory.RgTw (G)

namespace PositivityTheory.Rg.BcB.CG.ReproL

open Classical

section Gen

variable {G U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  [TopologicalSpace U] [CompactSpace U] [T2Space U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
  (ν : Measure U) [IsFiniteMeasure ν]
  (K : Subgroup G) (hK : IsCompact (K : Set G)) (ι : U → G) (hι : Continuous ι) (hιK : ∀ u, ι u ∈ K)

include hK in
theorem integral_mul_mem (k : G) (hk : k ∈ K) (F : G → ℂ) : ∫ y, F (y * k) ∂μ = ∫ y, F y ∂μ := by
  have e : Measure.map (⇑(MeasurableEquiv.mulRight k)) μ = μ :=
    GlobalTheory.CompactRight.map_mul_right_eq_of_mem_compact μ K hK k hk
  conv_rhs => rw [← e]
  rw [(MeasurableEquiv.mulRight k).measurableEmbedding.integral_map]
  rfl

include hK hι hιK in
theorem swap_right (c : G → U → ℂ) (hc : Continuous (Function.uncurry c)) (Kc : Set G) (hKc : IsCompact Kc)
    (hcK : ∀ y u, y ∉ Kc → c y u = 0) (h : G → ℂ) (hh : Continuous h) :
    ∫ y, (∫ u, c y u * h (y * ι u) ∂ν) ∂μ = ∫ y, (∫ u, c (y * (ι u)⁻¹) u ∂ν) * h y ∂μ := by
  have hKK : IsCompact (Kc * (K : Set G)) := hKc.mul hK
  have i1 : Integrable (Function.uncurry fun y u => c y u * h (y * ι u)) (μ.prod ν) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hc.mul (hh.comp (continuous_fst.mul (hι.comp continuous_snd)))
    · refine HasCompactSupport.intro (hKc.prod isCompact_univ) fun p hp => ?_
      have : p.1 ∉ Kc := fun h1 => hp ⟨h1, Set.mem_univ _⟩
      simp [Function.uncurry, hcK _ _ this]
  have i2 : Integrable (Function.uncurry fun y u => c (y * (ι u)⁻¹) u * h y) (μ.prod ν) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hc.comp ((continuous_fst.mul (hι.comp continuous_snd).inv).prodMk continuous_snd)).mul
        (hh.comp continuous_fst)
    · refine HasCompactSupport.intro (hKK.prod isCompact_univ) fun p hp => ?_
      have : p.1 * (ι p.2)⁻¹ ∉ Kc := fun h1 =>
        hp ⟨⟨p.1 * (ι p.2)⁻¹, h1, ι p.2, hιK p.2, by simp⟩, Set.mem_univ _⟩
      simp [Function.uncurry, hcK _ _ this]
  rw [integral_integral_swap i1]
  have e : ∀ u, ∫ y, c y u * h (y * ι u) ∂μ = ∫ y, c (y * (ι u)⁻¹) u * h y ∂μ := by
    intro u
    have := integral_mul_mem μ K hK (ι u) (hιK u) (fun y => c (y * (ι u)⁻¹) u * h y)
    simpa using this
  simp_rw [e]
  rw [← integral_integral_swap i2]
  congr 1
  funext y
  rw [integral_mul_const]

include hK hι hιK in
theorem avg_cont_supp (c : G → U → ℂ) (hc : Continuous (Function.uncurry c)) (Kc : Set G) (hKc : IsCompact Kc)
    (hcK : ∀ y u, y ∉ Kc → c y u = 0) :
    Continuous (fun y => ∫ u, c (y * (ι u)⁻¹) u ∂ν) ∧ HasCompactSupport (fun y => ∫ u, c (y * (ι u)⁻¹) u ∂ν) := by
  constructor
  · have := continuous_parametric_integral_of_continuous (μ := ν) (f := fun y u => c (y * (ι u)⁻¹) u)
      (hc.comp ((continuous_fst.mul (hι.comp continuous_snd).inv).prodMk continuous_snd)) isCompact_univ
    simpa [Measure.restrict_univ] using this
  · refine HasCompactSupport.intro (hKc.mul hK) fun y hy => ?_
    have : ∀ u, c (y * (ι u)⁻¹) u = 0 := fun u => hcK _ _ fun h1 => hy ⟨_, h1, ι u, hιK u, by simp⟩
    simp [this]

end Gen

theorem continuous_toUnitsU (N : ℕ) :
    Continuous (fun u : Matrix.unitaryGroup (Fin N) ℂ => (Unitary.toUnits u : G N)) := by
  rw [Units.continuous_iff]
  constructor
  · exact continuous_subtype_val
  · exact continuous_star.comp continuous_subtype_val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem continuous_along_infP (v : InfinitePlace E) (g : GA E N) (φ : GA E N → ℂ) (hs : φ ∈ Sm E N) :
    Continuous fun t : G N => φ (g * infP N (Pi.mulSingle v t)) := by
  let Mt : (InfinitePlace E → G N) → GL (Fin N) (Cinf E) := fun y =>
    Units.map (Matrix.piRingEquiv (n := Fin N) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
      (MulEquiv.piUnits.symm y)
  have hM : Continuous Mt := by
    refine Continuous.units_map _ ?_ |>.comp (ContinuousMulEquiv.piUnits (M := fun _ : InfinitePlace E =>
      Matrix (Fin N) (Fin N) ℂ)).symm.continuous
    exact continuous_pi fun i => continuous_pi fun j => continuous_pi fun v => (continuous_apply v).matrix_elem i j
  have hL : Continuous fun x : Matrix (Fin N) (Fin N) (Cinf E) => (toL x : Lie E N) := continuous_id
  have e : (fun t : G N => φ (g * infP N (Pi.mulSingle v t))) =
      fun t => chart φ g (toL (Mt (Pi.mulSingle v t)).val) := by
    funext t
    rw [chart_val]
    rfl
  rw [e]
  exact (hs g).continuousOn.comp_continuous
    (hL.comp ((Units.continuous_val (M := Matrix (Fin N) (Fin N) (Cinf E))).comp (hM.comp (continuous_mulSingle (A := fun _ : InfinitePlace E => G N) v))))
    fun t => val_mem_invSet _

end PositivityTheory.Rg.BcB.CG.ReproL
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PReproC

section

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open scoped ContDiff ComplexConjugate InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PositivityTheory.Rg.BcB.CG.ReproL

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

instance scUN (N : ℕ) : SecondCountableTopology (UN N) :=
  (Topology.IsEmbedding.subtypeVal (p := fun x => x ∈ Matrix.unitaryGroup (Fin N) ℂ)).secondCountableTopology

theorem one_mem_GLs' : (1 : Mat N) ∈ GLs N := by simp [GLs]

theorem local_repro (hK : KerEx) (hM : MultAlg) (hB : Bridge.BridgeSt) (W : Submodule ℂ (Kinf E N → ℂ))
    (hW : FiniteDimensional ℂ W) (R : ℝ) (v : InfinitePlace E) [MeasurableSpace (G N)] [BorelSpace (G N)]
    (μ0 : Measure (G N)) [μ0.IsHaarMeasure] :
    ∃ a : G N → ℂ, Continuous a ∧ HasCompactSupport a ∧ ∀ φ : Sm E N,
      (∀ g, (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) ∈ W) →
      PositivityTheory.Rg.BcB.SpectralAccumulation.InfBdd R (Submodule.span ℂ {φ}) →
      ∃ s : ℂ, 1 / 2 ≤ ‖s‖ ∧ ∀ g : GA E N, ∫ t, a t * φ.1 (g * infP N (Pi.mulSingle v t)) ∂μ0 = s * φ.1 g := by
  obtain ⟨g, T, hT, hg, hval⟩ := exists_bump N R
  obtain ⟨c0, hc0⟩ := hK N
  obtain ⟨k, hk⟩ := (hc0 μ0 (Mv W hW v)).1 [] g T hg
  have hmult : IsMult μ0 (Mv W hW v) k (fun χ => coshT g (cas χ)) T :=
    ⟨1, fun _ => 1, fun _ => [], fun _ => g, fun _ => k, fun _ => ⟨hg, hk⟩, fun y _ => by simp,
      fun χ => by simp [zVal]⟩
  have hact := (hM N μ0 (Mv W hW v) k k _ _ T T hmult hmult).2.2.2
  have : CompleteSpace (Mv W hW v).V := FiniteDimensional.complete ℂ _
  set b : G N → (Mv W hW v).V := fun y =>
    (InnerProductSpace.toDual ℂ (Mv W hW v).V).symm ((evL W hW v 1).comp (k y.val)) with hbdef
  have hb : ∀ y w, ⟪b y, w⟫_ℂ = toFun W v (k y.val w) 1 := fun y w => by
    rw [hbdef, InnerProductSpace.toDual_symm_apply]; rfl
  have hbc : Continuous b :=
    (InnerProductSpace.toDual ℂ (Mv W hW v).V).symm.continuous.comp
      ((ContinuousLinearMap.compL ℂ _ _ ℂ (evL W hW v 1)).continuous.comp (mult_continuous hmult))
  set c : G N → UN N → ℂ := fun y u => conj (toFun W v (b y) u) with hcdef
  have hcc : Continuous (Function.uncurry c) :=
    Complex.continuous_conj.comp ((continuous_toFun₂ W hW v).comp ((hbc.comp continuous_fst).prodMk continuous_snd))
  set Kc := tsupport fun y : G N => k y.val with hKcdef
  have hKc : IsCompact Kc := mult_hasCompactSupport hmult
  have hk0 : ∀ y, y ∉ Kc → k y.val = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (f := fun y : G N => k y.val) hy
  have hcK : ∀ y u, y ∉ Kc → c y u = 0 := by
    intro y u hy
    have hb0 : b y = 0 := by simp [hbdef, hk0 y hy]
    have ht : toFun W v (b y) = 0 := by rw [hb0]; exact (toFun W v).map_zero
    simp [hcdef, ht]
  set ι : UN N → G N := fun u => Unitary.toUnits u with hιdef
  have hι : Continuous ι := continuous_toUnitsU N
  set Ku : Subgroup (G N) := (Unitary.toUnits (R := Mat N)).range with hKudef
  have hKu : IsCompact (Ku : Set (G N)) := by
    have : (Ku : Set (G N)) = Set.range ι := by ext x; simp [Ku, ι]
    rw [this]; exact isCompact_range hι
  have hιK : ∀ u, ι u ∈ Ku := fun u => ⟨u, rfl⟩
  obtain ⟨ha1, ha2⟩ := avg_cont_supp (nuN N) Ku hKu ι hι hιK c hcc Kc hKc hcK
  refine ⟨_, ha1, ha2, ?_⟩
  intro φ hφ hR
  obtain ⟨χ, hχb, hχ⟩ := exists_chi hB R v φ hR
  refine ⟨coshT g (cas χ), hval χ hχb, fun g0 => ?_⟩
  set F := sec W hW v φ.1 φ.2 hφ g0 with hFdef
  have hF := sec_mem_CE W hW v φ.1 φ.2 hφ g0
  have hE := sec_isEig W hW v φ.1 φ.2 hφ g0 χ (hχ g0)
  have h1 := hact χ F hF hE 1 one_mem_GLs'
  set h : G N → ℂ := fun t => φ.1 (g0 * infP N (Pi.mulSingle v t)) with hhdef
  have hh : Continuous h := continuous_along_infP v g0 φ.1 φ.2
  have hFc : Continuous fun y : G N => F y.val :=
    hF.1.continuousOn.comp_continuous Units.continuous_val val_mem_GLs
  have hint : Integrable (fun y : G N => k y.val (F (1 * y.val))) μ0 := by
    simp only [one_mul]
    refine Continuous.integrable_of_hasCompactSupport ((mult_continuous hmult).clm_apply hFc) ?_
    exact HasCompactSupport.intro hKc fun y hy => by simp [hk0 y hy]
  have h2 := congrArg (evL W hW v 1) h1
  simp only [PositivityTheory.RgBcC.act] at h2
  rw [← ContinuousLinearMap.integral_comp_comm _ hint] at h2
  have hL : ∀ y : G N, evL W hW v 1 (k y.val (F (1 * y.val))) = ∫ u, c y u * h (y * ι u) ∂nuN N := by
    intro y
    rw [one_mul, evL_apply, ← hb]
    refine (inner_eq W v (b y) (F y.val)).trans (integral_congr_ae (Filter.Eventually.of_forall fun u => ?_))
    simp only [hcdef, hhdef]
    rw [toFun_sec W hW v φ.1 φ.2 hφ g0 (val_mem_GLs y) u]
    congr 1
    rw [show y.val * u.1 = (y * ι u).val from rfl, along_val]
  have hRHS : evL W hW v 1 (coshT g (cas χ) • F 1) = coshT g (cas χ) * φ.1 g0 := by
    rw [map_smul, evL_apply, toFun_sec W hW v φ.1 φ.2 hφ g0 one_mem_GLs' 1, smul_eq_mul]
    congr 1
    simpa using along_one' v g0 φ.1
  simp_rw [hL] at h2
  rw [hRHS] at h2
  rw [← h2, swap_right μ0 (nuN N) Ku hKu ι hι hιK c hcc Kc hKc hcK h hh]

end PositivityTheory.Rg.BcB.CG.ReproL
end
end
end
