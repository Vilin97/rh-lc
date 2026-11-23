module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PLocPrjGOfNotMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGoodReduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairInvolutionContinuous
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairLocalAuxiliaryStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceLocalElement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabilizerIndexNeZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedOrbitalSwapConvolutionStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactConjugacyTransversal

section

@[expose] public section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.OrbitalCount

theorem exists_compact_reps_of_finite_doubleCosets :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K : Subgroup H) (N : H),
      IsCompact (K : Set H) →
      (∀ C : Set H, IsCompact C →
        {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (K : Set H) |
          ∃ k ∈ K, (Quotient.out q * k)⁻¹ * N * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
      ∀ C : Set H, IsCompact C →
        ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C →
          ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d := by
  intro H _ _ _ K N hK hfin C hC
  refine ⟨⋃ q ∈ {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (K : Set H) |
      ∃ k ∈ K, (Quotient.out q * k)⁻¹ * N * MonoidHom.id H (Quotient.out q * k) ∈ C},
      (fun k => Quotient.out q * k) '' (K : Set H), ?_, ?_⟩
  · exact (hfin C hC).isCompact_biUnion fun q _ =>
      hK.image (continuous_const.mul continuous_id)
  · intro x hx
    obtain ⟨h, hh, k, hk, hout⟩ :=
      DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id H) N) K x
    have hcomm : h * N = N * h := hh
    have hconj : (h * x)⁻¹ * N * (h * x) = x⁻¹ * N * x := by
      have : h⁻¹ * N * h = N := by
        rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
      calc (h * x)⁻¹ * N * (h * x) = x⁻¹ * (h⁻¹ * N * h) * x := by group
        _ = x⁻¹ * N * x := by rw [this]
    set q := DoubleCoset.mk (twCent (MonoidHom.id H) N) K x with hq
    have hd : Quotient.out q * k⁻¹ = h * x := by
      rw [hout]; group
    refine ⟨h⁻¹, inv_mem hh, Quotient.out q * k⁻¹, ?_, ?_⟩
    · refine Set.mem_biUnion (x := q) ?_ ⟨k⁻¹, inv_mem hk, rfl⟩
      refine ⟨k⁻¹, inv_mem hk, ?_⟩
      rw [MonoidHom.id_apply, hd, hconj]
      exact hx
    · rw [hd, inv_mul_cancel_left]

end GlobalTheory.CompanionTheory.OrbitalCount
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactConjugacyTransversalStatement

section

@[expose] public section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

theorem _root_.GlobalTheory.T.exists_compact_conjugacy_transversal : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K : Subgroup H) (N : H), IsCompact (K : Set H) →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * N * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  ∀ C : Set H, IsCompact C → ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C → ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d := by
  first | exact @GlobalTheory.CompanionTheory.OrbitalCount.exists_compact_reps_of_finite_doubleCosets | exact GlobalTheory.CompanionTheory.OrbitalCount.exists_compact_reps_of_finite_doubleCosets | (intros; apply GlobalTheory.CompanionTheory.OrbitalCount.exists_compact_reps_of_finite_doubleCosets <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedOrbitalPairConvolution

section

@[expose] public section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitConvF

def twistEquiv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (σ : H →* H)
    (hc : Continuous σ) (hσ : ∀ g, σ (σ g) = g) : H × H ≃ₜ* H × H where
  toFun y := (y.1, σ y.2)
  invFun y := (y.1, σ y.2)
  left_inv y := by simp [hσ]
  right_inv y := by simp [hσ]
  map_mul' a b := by simp
  continuous_toFun := continuous_fst.prodMk (hc.comp continuous_snd)
  continuous_invFun := continuous_fst.prodMk (hc.comp continuous_snd)

theorem twOrb_conj_of_biinv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G)
    (K K' : Subgroup G) (δ g : G) (F : G → ℂ) (hθ : Continuous θ) (hK : IsCompact (K : Set G))
    (hK' : IsOpen (K' : Set G)) (hF : ∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x) :
    twOrb θ K (g⁻¹ * δ * θ g) F = twOrb θ K δ F :=
  GlobalTheory.TwOrbConj.twOrb_twConj G θ K δ g F
    (GlobalTheory.CompanionTheory.SplitIndex.rStab_index_ne_zero_of_compact θ K K' δ F hθ hK hK' hF)

theorem splitConv_of_finite : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → IsOpen (K : Set H) → IsCompact (K : Set H) → ∀ (d d' : H) (f₁ f₂ : H → ℂ) (K' : Subgroup H),
  IsOpen (K' : Set H) → K' ≤ K → (∀ k ∈ K', σ k ∈ K') → IsHecke K' f₁ → IsHecke K' f₂ →
  Good (MonoidHom.id H) K (d * σ d') →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  twOrb ((MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (d, d') (fun y => f₁ y.1 * f₂ (σ y.2)) =
    twOrb (MonoidHom.id H) K (d * σ d') (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  intro H _ _ _ _ σ K hc hσ hσK hKo hKc d d' f₁ f₂ K' hK'o hK'K hσK' h₁ h₂ hG hfin
  set θ := (MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom with hθ
  have hθc : Continuous θ := (hc.comp continuous_snd).prodMk (hc.comp continuous_fst)
  have hKKc : IsCompact ((K.prod K : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hKc.prod hKc
  have hK'K'o : IsOpen ((K'.prod K' : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_prod]; exact hK'o.prod hK'o
  have hinv : ∀ k ∈ K'.prod K', ∀ x : H × H,
      (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) (k * x) = (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) x ∧
      (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) (x * k) = (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) x := by
    rintro ⟨k₁, k₂⟩ hk ⟨x₁, x₂⟩
    obtain ⟨hk₁, hk₂⟩ := Subgroup.mem_prod.1 hk
    have hk₂' : σ k₂ ∈ K' := hσK' _ hk₂
    constructor
    · show f₁ (k₁ * x₁) * f₂ (σ (k₂ * x₂)) = f₁ x₁ * f₂ (σ x₂)
      rw [(h₁.2 k₁ hk₁ x₁).1, map_mul, (h₂.2 _ hk₂' _).1]
    · show f₁ (x₁ * k₁) * f₂ (σ (x₂ * k₂)) = f₁ x₁ * f₂ (σ x₂)
      rw [(h₁.2 k₁ hk₁ x₁).2, map_mul, (h₂.2 _ hk₂' _).2]
  have hconj : ((1, d') : H × H)⁻¹ * (d, d') * θ (1, d') = (d * σ d', 1) := by
    have e : θ (1, d') = (σ d', 1) := by simp [hθ]
    rw [e]
    ext <;> simp
  have step₁ := twOrb_conj_of_biinv θ (K.prod K) (K'.prod K') (d, d') (1, d')
    (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) hθc hKKc hK'K'o hinv
  rw [hconj] at step₁
  rw [← step₁]
  have step₂ := GlobalTheory.EulerTw.Transport.twOrb_transport (H × H) (H × H) (twistEquiv σ hc hσ) θ
    (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom (K.prod K) (K.prod K) (d * σ d', 1)
    (fun y : H × H => f₁ y.1 * f₂ (σ y.2)) (fun y : H × H => f₁ y.1 * f₂ y.2)
    (by
      rintro ⟨x₁, x₂⟩
      show (σ x₂, σ (σ x₁)) = (σ x₂, x₁)
      rw [hσ])
    (by
      rintro ⟨x₁, x₂⟩
      show x₁ ∈ K ∧ x₂ ∈ K ↔ x₁ ∈ K ∧ σ x₂ ∈ K
      refine and_congr_right fun _ => ⟨hσK _, fun h => ?_⟩
      simpa [hσ] using hσK _ h)
    (fun _ => rfl)
  have he : (twistEquiv σ hc hσ) (d * σ d', 1) = (d * σ d', 1) := by
    show (d * σ d', σ 1) = (d * σ d', 1)
    rw [map_one]
  rw [he] at step₂
  rw [step₂]
  exact GlobalTheory.T.twisted_orbital_swap_convolution H K K' (d * σ d') f₁ f₂ hKo hKc hK'o hK'K h₁ h₂ hG
    (GlobalTheory.T.exists_compact_conjugacy_transversal H K (d * σ d') hKc hfin)

end GlobalTheory.CompanionTheory.SplitConvF
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedOrbitalPairConvolutionStatement

section

@[expose] public section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

theorem _root_.GlobalTheory.T.twisted_orbital_pair_convolution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → IsOpen (K : Set H) → IsCompact (K : Set H) → ∀ (d d' : H) (f₁ f₂ : H → ℂ) (K' : Subgroup H),
  IsOpen (K' : Set H) → K' ≤ K → (∀ k ∈ K', σ k ∈ K') → IsHecke K' f₁ → IsHecke K' f₂ →
  Good (MonoidHom.id H) K (d * σ d') →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  twOrb ((MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (d, d') (fun y => f₁ y.1 * f₂ (σ y.2)) =
    twOrb (MonoidHom.id H) K (d * σ d') (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  first | exact @GlobalTheory.CompanionTheory.SplitConvF.splitConv_of_finite | exact GlobalTheory.CompanionTheory.SplitConvF.splitConv_of_finite | (intros; apply GlobalTheory.CompanionTheory.SplitConvF.splitConv_of_finite <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonSplit

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses

namespace GlobalTheory.CompanionTheory.LcSplit

theorem level_pick {H : Type} [Group H] [TopologicalSpace H] (σ : H →* H) (hc : Continuous σ) (hi : ∀ g, σ (σ g) = g)
    (K A₁ A₂ : Subgroup H) (f₁ f₂ : H → ℂ) (ho₁ : IsOpen (A₁ : Set H)) (ho₂ : IsOpen (A₂ : Set H)) (hK : A₁ ≤ K)
    (h₁ : IsHecke A₁ f₁) (h₂ : IsHecke A₂ f₂) :
    ∃ L : Subgroup H, IsOpen (L : Set H) ∧ L ≤ K ∧ (∀ k ∈ L, σ k ∈ L) ∧ IsHecke L f₁ ∧ IsHecke L f₂ := by
  have hAo : IsOpen ((A₁ ⊓ A₂ : Subgroup H) : Set H) := by
    rw [Subgroup.coe_inf]; exact ho₁.inter ho₂
  refine ⟨(A₁ ⊓ A₂) ⊓ (A₁ ⊓ A₂).comap σ, ?_, fun x hx => hK hx.1.1, fun k hk => ⟨hk.2, ?_⟩,
    ⟨h₁.1, fun k hk => h₁.2 k hk.1.1⟩, ⟨h₂.1, fun k hk => h₂.2 k hk.1.2⟩⟩
  · rw [Subgroup.coe_inf]
    exact hAo.inter (hAo.preimage hc)
  · show σ (σ k) ∈ A₁ ⊓ A₂
    rw [hi]; exact hk.1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem exists_level (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (hφ₁ : IsTestP φ₁) (hφ₂ : IsTestP φ₂) (w : Pl E) :
    ∃ L : Subgroup (GLw a w × GLw b w), IsOpen (L : Set (GLw a w × GLw b w)) ∧ L ≤ K2 a b w ∧ (∀ k ∈ L, sgP a b w k ∈ L) ∧
      IsHecke L (φ₁ w) ∧ IsHecke L (φ₂ w) := by
  obtain ⟨hc, hi, hk⟩ := sgP_facts E a b w
  obtain ⟨K₁, K₂, hl₁, hl₂, ht⟩ := hφ₁
  obtain ⟨K₁', K₂', hl₁', hl₂', ht'⟩ := hφ₂
  refine level_pick (sgP a b w) hc hi (K2 a b w) ((K₁ w).prod (K₂ w)) ((K₁' w).prod (K₂' w)) _ _ ?_ ?_ ?_ (ht.1 w) (ht'.1 w)
  · rw [Subgroup.coe_prod]; exact (hl₁.1 w).1.prod (hl₂.1 w).1
  · rw [Subgroup.coe_prod]; exact (hl₁'.1 w).1.prod (hl₂'.1 w).1
  · exact Subgroup.prod_mono (hl₁.1 w).2.1 (hl₂.1 w).2.1

theorem fv_split (S : Set (Pl E)) (hS : IsSection S) (w : Pl E) (hw : w ∈ S) (hs : IsSplitAt w)
    (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    fv S φ₁ φ₂ _ y = φ₁ w (evw ⟨w, rfl⟩ y) * φ₂ w (evw ⟨w, rfl⟩ (thv a b _ y)) := by
  unfold fv
  have key : ∀ u : Above (w.under (𝓞 (maximalRealSubfield E))), u.1 ∈ S → u = ⟨w, rfl⟩ := by
    intro u hu
    exact Subtype.ext ((hS w).unique ⟨hu, u.2⟩ ⟨hw, rfl⟩)
  rw [finprod_eq_single _ (⟨w, rfl⟩ : Above (w.under (𝓞 (maximalRealSubfield E))))]
  · rw [finprod_eq_if, if_pos hw, if_pos hs]
  · intro u hu
    rw [finprod_eq_if, if_neg (fun h => hu (key u h))]

theorem th_split (a b : ℕ) (w : Pl E) (hs : IsSplitAt w) :
    (thL a w).prodMap (thL b w) = MonoidHom.id (GLw a w × GLw b w) := by
  unfold thL
  rw [if_pos hs, if_pos hs]
  ext x <;> rfl

theorem seen_split (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (w : Pl E) (hs : IsSplitAt w) :
    seen φ₁ φ₂ w = fun y => hint (K2 a b w) fun z => φ₁ w z * φ₂ w (z⁻¹ * y) := by
  funext y
  unfold seen
  rw [if_pos hs]

theorem locEl_sep {n : ℕ} (w : Pl E) (hs : IsSplitAt w) (δ : GL (Fin n) E) (h : polE δ ∈ Ell E n) :
    (nrmL n w (locEl n w δ)).val.charpoly.Separable := by
  have : (nrmL n w (locEl n w δ)).val.charpoly = (polE δ).map (algebraMap E (w.adicCompletion E)) := by
    unfold nrmL locEl polE
    rw [if_pos hs, if_pos hs]
    exact Matrix.charpoly_map _ _
  rw [this]
  exact h.2.2.1.map

theorem target_side (hU : GlobalTheory.BCT.Unr E) (w : Pl E) (hs : IsSplitAt w)
    (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) (hδ₁ : polE δ₁ ∈ Ell E a) (hδ₂ : polE δ₂ ∈ Ell E b) :
    Good (MonoidHom.id _) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) ∧
    ∀ C : Set (GLw a w × GLw b w), IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (GLw a w × GLw b w)) (locEl a w δ₁, locEl b w δ₂) : Set _)
      (K2 (E := E) a b w : Set (GLw a w × GLw b w)) | ∃ k ∈ K2 (E := E) a b w,
        (Quotient.out q * k)⁻¹ * (locEl a w δ₁, locEl b w δ₂) * MonoidHom.id (GLw a w × GLw b w) (Quotient.out q * k) ∈ C}.Finite := by
  have h1 := GlobalTheory.CompanionTheory.LocGoodProof.locGood E hU a b w (locEl a w δ₁, locEl b w δ₂) (locEl_sep w hs δ₁ hδ₁) (locEl_sep w hs δ₂ hδ₂)
  have h2 := (GlobalTheory.CompanionTheory.TwistOrbit.locSupp E hU a b w (locEl a w δ₁, locEl b w δ₂) (locEl_sep w hs δ₁ hδ₁) (locEl_sep w hs δ₂ hδ₂)).1
  rw [th_split a b w hs] at h1 h2
  exact ⟨h1, h2⟩

theorem pair_integral_points_open_compact (a b : ℕ) (w : Pl E) :
    IsOpen ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) ∧ IsCompact ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) := by
  obtain ⟨hKo₁, hKc₁⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨hKo₂, hKc₂⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  rw [Subgroup.coe_prod]
  exact ⟨hKo₁.prod hKo₂, hKc₁.prod hKc₂⟩

theorem locCompareSplit : LocCompareSplit := by
  intro hCj E _ _ _ hU a b S hS φ₁ φ₂ hφ₁ hφ₂ δ₁ δ₂ hδ₁ hδ₂ w hw hs
  obtain ⟨e, he1, he3, he4, heδ⟩ := GlobalTheory.CompanionTheory.SplitIso.split_iso hCj E a b _ ⟨w, rfl⟩ hs
  obtain ⟨hc, hi, hk⟩ := sgP_facts E a b w
  obtain ⟨L, hLo, hLK, hLs, hH₁, hH₂⟩ := exists_level φ₁ φ₂ hφ₁ hφ₂ w
  obtain ⟨hKo, hKc⟩ := pair_integral_points_open_compact (E := E) a b w
  obtain ⟨hG, hF⟩ := target_side hU w hs δ₁ δ₂ hδ₁ hδ₂
  set y := pv a b (w.under (𝓞 (maximalRealSubfield E))) (ratF E a δ₁, ratF E b δ₂) with hy
  have hN : (e y).1 * sgP a b w (e y).2 = (locEl a w δ₁, locEl b w δ₂) := by
    rw [hy, heδ]
    exact Prod.ext (GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL E a w δ₁ hs) (GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL E b w δ₂ hs)
  have ht := GlobalTheory.EulerTw.Transport.twOrb_transport _ _ e (thv a b _) (swTw (sgP a b w))
    (Kv a b _) ((K2 a b w).prod (K2 a b w)) y (fv S φ₁ φ₂ _) (fun z => φ₁ w z.1 * φ₂ w (sgP a b w z.2))
    he3 he4 (fun g => by
      have h2 : evw ⟨w, rfl⟩ (thv a b _ g) = sgP a b w (e g).2 := by
        rw [← he1, he3]; rfl
      show φ₁ w (e g).1 * φ₂ w (sgP a b w (e g).2) = _
      rw [he1, ← h2, fv_split S hS w hw hs])
  rw [ht, seen_split φ₁ φ₂ w hs, th_split a b w hs]
  have hsc := GlobalTheory.T.twisted_orbital_pair_convolution _ (sgP a b w) (K2 a b w) hc hi hk hKo hKc (e y).1 (e y).2 (φ₁ w) (φ₂ w) L hLo hLK hLs hH₁ hH₂
    (by rw [hN]; exact hG) (by rw [hN]; exact hF)
  rw [hN] at hsc
  exact hsc

end GlobalTheory.CompanionTheory.LcSplit

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonSplitStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.local_comparison_split : PositivityTheory.Rg.BcB.G8.Fin.LocCompareSplit := by
  first | exact @GlobalTheory.CompanionTheory.LcSplit.locCompareSplit | exact GlobalTheory.CompanionTheory.LcSplit.locCompareSplit | (intros; apply GlobalTheory.CompanionTheory.LcSplit.locCompareSplit <;> assumption)
end
end
