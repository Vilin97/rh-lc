module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfContinuousTrace
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPseudoCharacterOfApproximatedByTracesStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproximatedTraceSystemLocallyCauchy

section

@[expose] public section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory

theorem polyApprox_trc_locally_cauchy : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (J : Type) (x : J → Γ) (θ : J → PadicAlgCl l) (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), (∀ ρ ∈ C, Continuous ρ) → PolyApprox θ ((fun ρ j => trc ρ (x j)) '' C) → ∀ ε : ℝ, 0 < ε → ∀ g : Γ, ∃ V ∈ nhds g, ∀ i j, x i ∈ V → x j ∈ V → ‖θ i - θ j‖ ≤ ε := by
  intro l _ Γ _ _ _ _ a J x θ C hC hA ε hε g
  obtain ⟨s, c, hs, hP⟩ := hA (ε / 2) (by linarith)
  have hmem : ∀ η ∈ s, ∃ ρ ∈ C, (fun j => trc ρ (x j)) = η := fun η hη => hs hη
  choose! R hRC hRη using hmem
  set F : Γ → PadicAlgCl l := fun h => ∑ η ∈ s, c η * trc (R η) h with hF
  have hFc : Continuous F := by
    refine continuous_finsetSum _ fun η hη => continuous_const.mul ?_
    exact (Units.continuous_val.comp (hC _ (hRC η hη))).matrix_trace
  refine ⟨F ⁻¹' Metric.ball (F g) (ε / 4), hFc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by linarith)), ?_⟩
  intro i j hi hj
  have key := hP (MvPolynomial.X i - MvPolynomial.X j)
  simp only [map_sub, MvPolynomial.aeval_X] at key
  have hsum : ∑ η ∈ s, c η * (η i - η j) = F (x i) - F (x j) := by
    rw [hF]; simp only
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun η hη => ?_
    have hi2 : η i = trc (R η) (x i) := (congrFun (hRη η hη) i).symm
    have hj2 : η j = trc (R η) (x j) := (congrFun (hRη η hη) j).symm
    rw [hi2, hj2]; ring
  rw [hsum] at key
  have hi' : ‖F (x i) - F g‖ < ε / 4 := by simpa [dist_eq_norm] using hi
  have hj' : ‖F (x j) - F g‖ < ε / 4 := by simpa [dist_eq_norm] using hj
  have hd : ‖F (x i) - F (x j)‖ ≤ ε / 2 := by
    have e : F (x i) - F (x j) = (F (x i) - F g) - (F (x j) - F g) := by ring
    rw [e]; linarith [norm_sub_le (F (x i) - F g) (F (x j) - F g)]
  have e2 : θ i - θ j = (θ i - θ j - (F (x i) - F (x j))) + (F (x i) - F (x j)) := by ring
  rw [e2]; linarith [norm_add_le (θ i - θ j - (F (x i) - F (x j))) (F (x i) - F (x j))]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproximatedTraceSystemLocallyCauchyStatement

section

@[expose] public section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

theorem _root_.GlobalTheory.T.approximatedTraceSystem_locally_cauchy : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (J : Type) (x : J → Γ) (θ : J → PadicAlgCl l) (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), (∀ ρ ∈ C, Continuous ρ) → PolyApprox θ ((fun ρ j => trc ρ (x j)) '' C) → ∀ ε : ℝ, 0 < ε → ∀ g : Γ, ∃ V ∈ nhds g, ∀ i j, x i ∈ V → x j ∈ V → ‖θ i - θ j‖ ≤ ε := by
  first | exact @GlobalTheory.polyApprox_trc_locally_cauchy | exact GlobalTheory.polyApprox_trc_locally_cauchy | (intros; apply GlobalTheory.polyApprox_trc_locally_cauchy <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtendOfLocallyCauchy

section

@[expose] public section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

open Filter Topology

namespace GlobalTheory.Cong

theorem extend_of_locallyCauchy : ∀ (l : ℕ) [Fact l.Prime] (Γ J : Type) [TopologicalSpace Γ] (x : J → Γ), DenseRange x → ∀ (θ : J → PadicAlgCl l) (L : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] L → (∀ j, θ j ∈ L) → (∀ ε : ℝ, 0 < ε → ∀ g : Γ, ∃ V ∈ nhds g, ∀ i j, x i ∈ V → x j ∈ V → ‖θ i - θ j‖ ≤ ε) → ∃ T : Γ → PadicAlgCl l, Continuous T ∧ ∀ j, T (x j) = θ j := by
  intro l _ Γ J _ x hx θ L hL hθL hC
  have hLc : IsComplete (L : Set (PadicAlgCl l)) := by
    haveI : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule L.toSubalgebra) := hL
    exact Submodule.complete_of_finiteDimensional (Subalgebra.toSubmodule L.toSubalgebra)
  have hnb : ∀ g : Γ, (comap x (𝓝 g)).NeBot := by
    intro g
    refine comap_neBot_iff.2 fun t ht => ?_
    obtain ⟨_, hyt, j, rfl⟩ := mem_closure_iff_nhds.1 (hx g) t ht
    exact ⟨j, hyt⟩
  have hex : ∀ g : Γ, ∃ t : PadicAlgCl l, Tendsto θ (comap x (𝓝 g)) (𝓝 t) := by
    intro g
    haveI : (comap x (𝓝 g)).NeBot := hnb g
    have hcau : Cauchy (map θ (comap x (𝓝 g))) := by
      rw [Metric.cauchy_iff]
      refine ⟨inferInstance, fun ε hε => ?_⟩
      obtain ⟨V, hV, hVc⟩ := hC (ε / 2) (by positivity) g
      refine ⟨θ '' (x ⁻¹' V), image_mem_map (preimage_mem_comap hV), ?_⟩
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (hVc i j hi hj) (by linarith)
    have hle : map θ (comap x (𝓝 g)) ≤ 𝓟 (L : Set (PadicAlgCl l)) :=
      le_principal_iff.2 (mem_map.2 (univ_mem' fun j => hθL j))
    obtain ⟨t, -, ht⟩ := hLc _ hcau hle
    exact ⟨t, ht⟩
  choose T hT using hex
  refine ⟨T, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g => ?_
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨V, hV, hVc⟩ := hC (ε / 2) (by positivity) g
    filter_upwards [interior_mem_nhds.2 hV] with g' hg'
    have hV' : V ∈ 𝓝 g' := mem_interior_iff_mem_nhds.1 hg'
    haveI : (comap x (𝓝 g')).NeBot := hnb g'
    haveI : (comap x (𝓝 g)).NeBot := hnb g
    have hlim : Tendsto (fun p : J × J => dist (θ p.1) (θ p.2))
        (comap x (𝓝 g') ×ˢ comap x (𝓝 g)) (𝓝 (dist (T g') (T g))) :=
      ((hT g').comp tendsto_fst).dist ((hT g).comp tendsto_snd)
    have hev : ∀ᶠ p : J × J in comap x (𝓝 g') ×ˢ comap x (𝓝 g), dist (θ p.1) (θ p.2) ≤ ε / 2 := by
      filter_upwards [prod_mem_prod (preimage_mem_comap hV') (preimage_mem_comap hV)] with p hp
      rw [dist_eq_norm]
      exact hVc p.1 p.2 hp.1 hp.2
    have := le_of_tendsto hlim hev
    linarith
  · intro j
    haveI : (comap x (𝓝 (x j))).NeBot := hnb (x j)
    refine tendsto_nhds_unique (hT (x j)) ?_
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨V, hV, hVc⟩ := hC (ε / 2) (by positivity) (x j)
    filter_upwards [preimage_mem_comap hV] with i hi
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hVc i j hi (mem_of_mem_nhds hV)) (by linarith)

end GlobalTheory.Cong
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolyApproxOfDenseRange

section

@[expose] public section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem continuous_aeval_comp {Γ k : Type} [TopologicalSpace Γ] [CommRing k] [TopologicalSpace k]
    [IsTopologicalRing k] (f : Γ → k) (hf : Continuous f) (P : MvPolynomial Γ ℤ) :
    Continuous fun u : Γ → Γ => MvPolynomial.aeval (f ∘ u) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.aeval_X, Function.comp_apply]
    exact hp.mul (hf.comp (continuous_apply j))

theorem polyApprox_of_denseRange : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] (a : ℕ) (J : Type) (x : J → Γ), DenseRange x → ∀ (T : Γ → PadicAlgCl l), Continuous T →
    ∀ (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), (∀ ρ ∈ C, Continuous ρ) →
    PolyApprox (fun j => T (x j)) ((fun ρ j => trc ρ (x j)) '' C) → PolyApprox T (trc '' C) := by
  intro l _ Γ _ _ _ _ a J x hx T hT C hC h ε hε
  classical
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  have hch : ∀ η ∈ s, ∃ ρ ∈ C, (fun j => trc ρ (x j)) = η := fun η hη => hs hη
  choose! ρ hρC hρη using hch
  have inj : Set.InjOn (fun η => trc (ρ η)) (s : Set (J → PadicAlgCl l)) := by
    intro η₁ h₁ η₂ h₂ e
    rw [← hρη η₁ h₁, ← hρη η₂ h₂]
    simp only at e
    rw [e]
  refine ⟨s.image (fun η => trc (ρ η)), fun σ => c (fun j => σ (x j)), ?_, fun P => ?_⟩
  · intro σ hσ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hσ
    obtain ⟨η, hη, rfl⟩ := hσ
    exact ⟨ρ η, hρC η hη, rfl⟩
  rw [Finset.sum_image inj]
  have hc : ∀ η ∈ s, c (fun j => trc (ρ η) (x j)) = c η := fun η hη => by rw [hρη η hη]
  rw [Finset.sum_congr rfl (fun η hη => by rw [show (fun σ : Γ → PadicAlgCl l => c fun j => σ (x j)) (trc (ρ η)) = c η from hc η hη])]
  have htr : ∀ η ∈ s, Continuous (trc (ρ η)) := fun η hη =>
    (Units.continuous_val.comp (hC _ (hρC η hη))).matrix_trace
  let F : (Γ → Γ) → PadicAlgCl l := fun u =>
    MvPolynomial.aeval (T ∘ u) P - ∑ η ∈ s, c η * MvPolynomial.aeval (trc (ρ η) ∘ u) P
  have hF : Continuous F := by
    refine (continuous_aeval_comp T hT P).sub (continuous_finsetSum _ fun η hη => ?_)
    exact continuous_const.mul (continuous_aeval_comp _ (htr η hη) P)
  have key : ‖F id‖ ≤ ε := by
    refine (DenseRange.piMap (fun _ : Γ => hx)).induction_on (p := fun u => ‖F u‖ ≤ ε) id
      (isClosed_le (continuous_norm.comp hF) continuous_const) fun v => ?_
    have e1 : MvPolynomial.aeval (T ∘ Pi.map (fun _ : Γ => x) v) P =
        MvPolynomial.aeval (fun j => T (x j)) (MvPolynomial.rename v P) := by
      rw [MvPolynomial.aeval_rename]; rfl
    have e2 : ∀ η ∈ s, MvPolynomial.aeval (trc (ρ η) ∘ Pi.map (fun _ : Γ => x) v) P =
        MvPolynomial.aeval η (MvPolynomial.rename v P) := fun η hη => by
      have e3 : trc (ρ η) ∘ Pi.map (fun _ : Γ => x) v = η ∘ v := by
        funext i
        simp only [Function.comp_apply, Pi.map_apply]
        exact congrFun (hρη η hη) (v i)
      rw [MvPolynomial.aeval_rename, e3]
    have := hP (MvPolynomial.rename v P)
    simp only [F]
    rw [e1, Finset.sum_congr rfl (fun η hη => by rw [e2 η hη])]
    exact this
  exact key

end GlobalTheory.Cong
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitRep

section

@[expose] public section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem exists_limit_rep : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (J : Type) (x : J → Γ), DenseRange x → ∀ (θ : J → PadicAlgCl l) (L : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] L → (∀ j, θ j ∈ L) → ∀ (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), (∀ ρ ∈ C, Continuous ρ) → PolyApprox θ ((fun ρ j => trc ρ (x j)) '' C) → ∃ r : Γ →* GL (Fin a) (PadicAlgCl l), Continuous r ∧ IsSSRep r ∧ (∀ j, trc r (x j) = θ j) ∧ PolyApprox (trc r) (trc '' C) := by
  intro l _ Γ _ _ _ _ a J x hx θ L hL hθL C hC hA
  have hU := GlobalTheory.T.approximatedTraceSystem_locally_cauchy l Γ a J x θ C hC hA
  obtain ⟨T, hTc, hTx⟩ := GlobalTheory.Cong.extend_of_locallyCauchy l Γ J x hx θ L hL hθL hU
  have hA' : PolyApprox (fun j => T (x j)) ((fun ρ j => trc ρ (x j)) '' C) := by
    have : (fun j => T (x j)) = θ := funext hTx
    rw [this]; exact hA
  have hT : PolyApprox T (trc '' C) := GlobalTheory.Cong.polyApprox_of_denseRange l Γ a J x hx T hTc C hC hA'
  have hP : IsPsChar a T := GlobalTheory.T.isPseudoCharacter_of_approximatedByTraces l Γ a T C hT
  obtain ⟨r, hr, htr⟩ := GlobalTheory.PsChar.exists_ssRep Γ (PadicAlgCl l) a T hP
  have htrc : trc r = T := funext fun g => htr g
  refine ⟨r, ?_, hr, fun j => by rw [htrc]; exact hTx j, by rw [htrc]; exact hT⟩
  refine GlobalTheory.SSCont.continuous_of_continuous_trace Γ (PadicAlgCl l) a r hr ?_
  have : (fun g => ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)).trace) = T := htrc
  rw [this]; exact hTc

end GlobalTheory.Cong
end
end
