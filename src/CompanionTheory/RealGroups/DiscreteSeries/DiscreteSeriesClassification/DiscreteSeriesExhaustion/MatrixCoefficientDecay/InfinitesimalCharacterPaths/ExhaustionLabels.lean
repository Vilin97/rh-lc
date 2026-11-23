module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentLeftRuleStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentRightRuleStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FamilyFiltration
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FamilyInduction
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.JacquetBasis
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.JacquetDegree
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.JacquetInitial
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.AbsoluteL2Bound
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PolynomialNilpotentPath
import Mathlib.RingTheory.PiTensorProduct
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.JacquetTensorDecomposition
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.JacquetTransport

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.HasCharPath

section

@[expose] public section

noncomputable section

namespace CompanionTheory.RgExh.Dec.J

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem nset_congr (ε : Fin n → Bool) {V : Type} [AddCommGroup V] [Module ℂ V] {ι κ : Type}
    (c : ι → V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (d : κ → V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (h1 : ∀ i, ∃ k, c i = d k) (h2 : ∀ k, ∃ i, d k = c i) (A : Matrix (Fin n) (Fin n) ℂ)
    (μ : MeasureTheory.Measure (ReciprocityTheory.ChartRestriction.DS.S7.UJ ε)) (s : ℝ) : NSet ε c A μ s = NSet ε d A μ s := by
  ext u
  constructor
  · intro hu k
    obtain ⟨i, hi⟩ := h2 k
    rw [hi]; exact hu i
  · intro hu i
    obtain ⟨k, hk⟩ := h1 i
    rw [hk]; exact hu k



theorem along (hT : Transport) (hSC : StepChar) (hTD : TensDecomp) (hFF : FamFilt) (hSF : StepFam)
    (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (μ : MeasureTheory.Measure (ReciprocityTheory.ChartRestriction.DS.S7.UJ ε))
    (hA : IsGrad ε A) (hμ : IsParHaar ε A μ) (B : GradBasis A) :
    ∀ (ss : List (Fin n)) (X : GMod n) (ι : Type) (c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ))
      (χ : Fin n → ℂ) (Λ : Set (Fin n → Fin 3)) (F : Filt X A),
      IsCoefFam ε X c → (∀ s u, u ∈ F.N s ↔ u ∈ NSet ε c A μ s) → HasChar X χ → GoodPath χ ss → PP F B χ Λ →
      ∃ F' : Filt (path X χ ss) A,
        (∀ s u, u ∈ F'.N s ↔ u ∈ NSet ε (fun p : ι × List (Fin n) => pathCoef X (c p.1) χ ss p.2) A μ s) ∧
        PP F' B (pathEnd χ ss) (moveIter χ Λ ss) := by
  intro ss
  induction ss with
  | nil =>
    intro X ι c χ Λ F _ hF _ _ hP
    refine ⟨F, fun s u => (hF s u).trans ?_, hP⟩
    exact Set.ext_iff.1 (nset_congr ε c (fun p : ι × List (Fin n) => pathCoef X (c p.1) χ [] p.2)
      (fun i => ⟨(i, []), rfl⟩) (fun k => ⟨k.1, rfl⟩) A μ s) u
  | cons s ss ih =>
    intro X ι c χ Λ F hc hF hX hG hP
    obtain ⟨hc', hsand⟩ := hSF n ε X ι c (χ s) A μ hc hA
    obtain ⟨s0, hs0⟩ := F.top
    have htop : ∃ t, ∀ u, u ∈ NSet ε (fun p : ι × Fin n => stepCoef X (χ s) (c p.1) p.2) A μ t :=
      ⟨s0 + 1, fun u => (hsand (s0 + 1) u).1 fun i => by
        rw [← hF]; simp [add_sub_cancel_right, hs0]⟩
    obtain ⟨F1, hF1⟩ := hFF n ε (step X (χ s)) (ι × Fin n) _ A μ hc' hA hμ htop
    have hSS : SandStep F (χ s) F1 := fun t u =>
      ⟨fun h => (hF1 t u).2 ((hsand t u).1 fun i => (hF (t - 1) _).1 (h i)),
        fun h i => (hF (t + 1) _).2 ((hsand t u).2 ((hF1 t u).1 h) i)⟩
    have hP1 := hT hSC hTD n X A F B χ s F1 Λ hX hG.1 hSS hP
    obtain ⟨F', hF', hP'⟩ := ih (step X (χ s)) (ι × Fin n) _ (χ + Pi.single s 1) (move χ Λ s) F1 hc' hF1
      (hSC n X χ s hX) hG.2 hP1
    refine ⟨F', fun t u => ?_, hP'⟩
    have e := Set.ext_iff.1 (nset_congr (V := (path X χ (s :: ss)).V) ε
      (fun p : (ι × Fin n) × List (Fin n) =>
        pathCoef (step X (χ s)) (stepCoef X (χ s) (c p.1.1) p.1.2) (χ + Pi.single s 1) ss p.2)
      (fun p : ι × List (Fin n) => pathCoef X (c p.1) χ (s :: ss) p.2)
      (fun k => ⟨(k.1.1, k.1.2 :: k.2), rfl⟩) (fun k => ⟨((k.1, k.2.headD s), k.2.tail), rfl⟩) A μ t) u
    exact (hF' t u).trans e

theorem hasChar_path (hSC : StepChar) : ∀ (ss : List (Fin n)) (X : GMod n) (χ : Fin n → ℂ), HasChar X χ →
    HasChar (path X χ ss) (pathEnd χ ss) := by
  intro ss
  induction ss with
  | nil => intro X χ h; exact h
  | cons s ss ih => intro X χ h; exact ih _ _ (hSC n X χ s h)

theorem labels_of (hLF : LocFin) (hTD : TensDecomp) (hT : Transport) (hFF : FamFilt) (hSF : StepFam) (hBF : BaseFam)
    (hS1 : Start1) (hD : Degree) (hB : Basis) (hLT : LabelTrack) : Labels := by
  intro hSC n
  refine ⟨1, fun ε H _ _ _ σ D E hK χ ss hU hC hG hFL A μ hA hμ h0 => ?_⟩
  obtain ⟨B⟩ := hB n ε A hA
  have hc := hBF n ε H σ D E hK hU
  obtain ⟨F0, hF0⟩ := hFF n ε ⟨D, E, hK.gl⟩ D (fun ξ : D => baseCoef σ D (ξ : H)) A μ hc hA hμ ⟨-rhoA A, h0⟩
  have htop : F0.N (-rhoA A) = ⊤ := by
    ext u; simp only [Submodule.mem_top, iff_true]; exact (hF0 _ u).2 (h0 u)
  have hP0 := hS1 n ⟨D, E, hK.gl⟩ A F0 B χ (hLF n ε _ A F0 χ hA hC) hC htop
  obtain ⟨F', hF', hP'⟩ := along hT hSC hTD hFF hSF ε A μ hA hμ B ss ⟨D, E, hK.gl⟩ D
    (fun ξ : D => baseCoef σ D (ξ : H)) χ _ F0 hc hF0 hC hG hP0
  have hlab : ∀ L ∈ moveIter χ {L | IsLabel B.j L ∧ (deg χ L).re < 0} ss,
      (deg (pathEnd χ ss) L).re < (-rhoA A - 1) + rhoA A := by
    intro L hL
    have := hLT n χ ss 1 B.j hG hFL L hL
    linarith
  have hN := hD n _ A F' B (pathEnd χ ss) _ (-rhoA A - 1) (hLF n ε _ A F' _ hA (hasChar_path hSC ss _ χ hC)) (hasChar_path hSC ss _ χ hC) hP' hlab
  intro u
  have hu : u ∈ F'.N (-rhoA A - 1) := by rw [hN]; exact Submodule.mem_top
  exact (hF' _ u).1 hu

end CompanionTheory.RgExh.Dec.J
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BaseFamilyAlt

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.BaseFamily

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J ReciprocityTheory.ChartRestriction.DS

theorem baseFam : CompanionTheory.RgExh.Dec.J.BaseFam := by
  intro n ε H _ _ _ σ D E hK hσ
  refine ⟨fun ξ u Y hY g hg => ?_, fun ξ => ?_⟩
  · have h := GlobalTheory.T.NilpotentRightRule n ε H σ D E hK 0 [] hσ ((ξ, []) : D × List (Fin n)) u Y hY g hg
    have e : actM E Y u = ∑ a, ∑ b, Y a b • E a b u := by
      simp [actM, LinearMap.sum_apply]
    show HasDerivAt _ (baseCoef σ D (ξ : H) (actM E Y u) g) 0
    rw [e]
    exact h
  · obtain ⟨l, hl⟩ := GlobalTheory.T.NilpotentLeftRule n ε H σ D E hK 0 [] hσ ((ξ, []) : D × List (Fin n))
    refine ⟨fun c d => (l c d).mapDomain Prod.fst, fun a b u g hg => ?_⟩
    have h := hl a b u g hg
    refine h.trans (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_)
    congr 1
    rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring)]
    rfl

end GlobalTheory.CompanionTheory.BaseFamily
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.JacquetLocallyFinite

section

@[expose] public section

noncomputable section

open Polynomial

namespace GlobalTheory.CompanionTheory.LocFinFilt

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem aeval_mul_of_intertwine (T Y : Module.End ℂ V) (c : ℂ)
    (h : T * Y = Y * (T + algebraMap ℂ _ c)) (f : ℂ[X]) :
    aeval T f * Y = Y * aeval (T + algebraMap ℂ _ c) f := by
  induction f using Polynomial.induction_on with
  | C a =>
    simp only [aeval_C]
    exact (Algebra.commutes a Y)
  | add p q hp hq => simp only [map_add (f := _), add_mul, mul_add, hp, hq]
  | monomial m a ih =>
    have e : ∀ S : Module.End ℂ V, aeval S (C a * X ^ (m + 1)) = aeval S (C a * X ^ m) * S := by
      intro S
      simp only [map_mul, map_pow, aeval_X, pow_succ, mul_assoc]
    rw [e, e, mul_assoc, h, ← mul_assoc, ih, mul_assoc]

theorem actM_intertwine {E : Fin n → Fin n → Module.End ℂ V} (hE : Formalism.REAL.GlRel E)
    {A Y : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (h : A * Y - Y * A = c • Y) :
    actM E A * actM E Y = actM E Y * (actM E A + algebraMap ℂ _ c) := by
  have hb := GlobalTheory.CompanionTheory.PolyNilGrad.actM_bracket E hE A Y
  have hs : actM E (c • Y) = c • actM E Y :=
    (GlobalTheory.CompanionTheory.PolyNilGrad.actL E).map_smul c Y
  rw [h, hs] at hb
  rw [mul_add, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  exact sub_eq_iff_eq_add'.mp hb

theorem aeval_shift (T : Module.End ℂ V) (c d : ℂ) (h : c + d = 0) (f : ℂ[X]) :
    aeval (T + algebraMap ℂ _ c) (f.comp (X + C d)) = aeval T f := by
  have e : aeval (T + algebraMap ℂ _ c) (X + C d : ℂ[X]) = T := by
    rw [map_add (f := _), aeval_X, aeval_C, add_assoc, ← map_add (f := _), h, map_zero, add_zero]
  rw [aeval_comp, e]

theorem step_down {M : GMod n} {A : Matrix (Fin n) (Fin n) ℂ} (F : Filt M A) (p q : ℂ[X])
    (hnil : ∀ u : M.V, ∃ (m : ℕ) (Y : Fin m → Matrix (Fin n) (Fin n) ℂ) (v : Fin m → M.V),
      (∀ k, Y k ∈ L.nilpC A) ∧ aeval (actM M.E A) p u = ∑ k, actM M.E (Y k) (v k))
    (s : ℝ) (hq : ∀ u : M.V, aeval (actM M.E A) q u ∈ F.N s) (u : M.V) :
    aeval (actM M.E A) (q.comp (X + C 1) * q.comp (X + C 2) * p) u ∈ F.N (s - 1) := by
  set T := actM M.E A with hT
  set g : ℂ[X] := q.comp (X + C 1) * q.comp (X + C 2) with hg
  obtain ⟨m, Y, v, hY, hu⟩ := hnil u
  have key : aeval T (g * p) u = ∑ k, aeval T g (actM M.E (Y k) (v k)) := by

    rw [map_mul, mul_apply_eq_comp, hu, map_sum]
  rw [key]
  refine Submodule.sum_mem _ fun k _ => ?_
  obtain ⟨Y₁, Y₂, hk, h₁, h₂⟩ := hY k
  have hadd : actM M.E (Y k) = actM M.E Y₁ + actM M.E Y₂ := by
    rw [hk]; exact (GlobalTheory.CompanionTheory.PolyNilGrad.actL M.E).map_add Y₁ Y₂
  rw [hadd, LinearMap.add_apply, map_add (f := _)]
  refine Submodule.add_mem _ ?_ ?_
  · have h₁' : A * Y₁ - Y₁ * A = (-1 : ℂ) • Y₁ := by rw [h₁, neg_smul, one_smul]
    have hc := aeval_mul_of_intertwine T (actM M.E Y₁) (-1) (actM_intertwine M.gl h₁') g
    have e : aeval T g (actM M.E Y₁ (v k)) =
        actM M.E Y₁ (aeval T q (aeval (T + algebraMap ℂ _ (-1)) (q.comp (X + C 2)) (v k))) := by
      have := congrArg (fun f : Module.End ℂ M.V => f (v k)) hc
      simp only [mul_apply_eq_comp] at this
      rw [this, hg, map_mul, aeval_shift T (-1) 1 (by norm_num), mul_apply_eq_comp]
    rw [e]
    have := F.shift Y₁ (-1) (by simpa using h₁') s _ (hq (aeval (T + algebraMap ℂ _ (-1)) (q.comp (X + C 2)) (v k)))
    simpa [sub_eq_add_neg] using this
  · have h₂' : A * Y₂ - Y₂ * A = (-2 : ℂ) • Y₂ := by rw [h₂, neg_smul]
    have hc := aeval_mul_of_intertwine T (actM M.E Y₂) (-2) (actM_intertwine M.gl h₂') g
    have e : aeval T g (actM M.E Y₂ (v k)) =
        actM M.E Y₂ (aeval T q (aeval (T + algebraMap ℂ _ (-2)) (q.comp (X + C 1)) (v k))) := by
      have := congrArg (fun f : Module.End ℂ M.V => f (v k)) hc
      simp only [mul_apply_eq_comp] at this
      rw [this, hg, mul_comm, map_mul, aeval_shift T (-2) 2 (by norm_num), mul_apply_eq_comp]
    rw [e]
    have := F.shift Y₂ (-2) (by simpa using h₂') s _ (hq (aeval (T + algebraMap ℂ _ (-2)) (q.comp (X + C 1)) (v k)))
    refine F.mono _ _ ?_ this
    push_cast
    linarith

theorem exists_monic_descend {M : GMod n} {A : Matrix (Fin n) (Fin n) ℂ} (F : Filt M A) (p : ℂ[X])
    (hp : p.Monic)
    (hnil : ∀ u : M.V, ∃ (m : ℕ) (Y : Fin m → Matrix (Fin n) (Fin n) ℂ) (v : Fin m → M.V),
      (∀ k, Y k ∈ L.nilpC A) ∧ aeval (actM M.E A) p u = ∑ k, actM M.E (Y k) (v k))
    (s : ℝ) (hs : F.N s = ⊤) (K : ℕ) :
    ∃ q : ℂ[X], q.Monic ∧ ∀ u : M.V, aeval (actM M.E A) q u ∈ F.N (s - K) := by
  induction K with
  | zero => exact ⟨1, monic_one, fun u => by simp [hs]⟩
  | succ K ih =>
    obtain ⟨q, hq, hu⟩ := ih
    refine ⟨q.comp (X + C 1) * q.comp (X + C 2) * p,
      (hq.comp_X_add_C 1 |>.mul (hq.comp_X_add_C 2)).mul hp, fun u => ?_⟩
    have := step_down F p q hnil _ hu u
    have e : s - ((K + 1 : ℕ) : ℝ) = s - K - 1 := by push_cast; ring
    rwa [e]

theorem locFin : LocFin := by
  intro n ε M A F χ hA hχ t
  obtain ⟨p, hp, hnil⟩ := GlobalTheory.CompanionTheory.PolyNilGrad.polyNilPath n ε M χ A hχ hA
  obtain ⟨s, hs⟩ := F.top
  obtain ⟨K, hK⟩ := exists_nat_ge (s - t)
  obtain ⟨q, hq, hu⟩ := exists_monic_descend F p hp hnil s hs K
  exact ⟨q, hq, fun u => F.mono _ _ (by linarith) (hu u)⟩

end GlobalTheory.CompanionTheory.LocFinFilt
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LabelTracking

section

@[expose] public section

open Finset

namespace GlobalTheory.CompanionTheory.Labels

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec.J

variable {n : ℕ}

theorem tie_step {χ₀ χ : Fin n → ℂ} {t : Fin n}
    (hT : ∀ r s, r ≠ s → χ r = χ s → χ r = χ₀ r ∧ χ s = χ₀ s) (hg : ∀ r, χ r ≠ χ t + 1) :
    ∀ r s, r ≠ s → (χ + Pi.single t 1 : Fin n → ℂ) r = (χ + Pi.single t 1 : Fin n → ℂ) s →
      (χ + Pi.single t 1 : Fin n → ℂ) r = χ₀ r ∧ (χ + Pi.single t 1 : Fin n → ℂ) s = χ₀ s := by
  intro r s hrs h
  by_cases hr : r = t
  · subst hr
    have hs : s ≠ r := hrs.symm
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hs, add_zero] at h
    exact absurd h.symm (hg s)
  by_cases hs : s = t
  · subst hs
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hr, add_zero] at h
    exact absurd h (hg r)
  simp only [Pi.add_apply, Pi.single_eq_of_ne hr, Pi.single_eq_of_ne hs, add_zero] at h ⊢
  exact hT r s hrs h

theorem apply_swap_of_eq (χ : Fin n → ℂ) {r s : Fin n} (h : χ r = χ s) (i : Fin n) :
    χ i = χ (Equiv.swap r s i) := by
  by_cases h1 : i = r
  · subst h1; simp [h]
  by_cases h2 : i = s
  · subst h2; simp [h]
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem sum_filter_swap (χ : Fin n → ℂ) (L : Fin n → Fin 3) {r s : Fin n} (h : χ r = χ s) (a : Fin 3) :
    ∑ i ∈ univ.filter (fun i => (L ∘ Equiv.swap r s) i = a), χ i = ∑ i ∈ univ.filter (fun i => L i = a), χ i :=
  Finset.sum_equiv (Equiv.swap r s) (by simp) fun i _ => apply_swap_of_eq χ h i

theorem deg_swap (χ : Fin n → ℂ) (L : Fin n → Fin 3) {r s : Fin n} (h : χ r = χ s) :
    deg χ (L ∘ Equiv.swap r s) = deg χ L := by
  simp only [deg, sum_filter_swap χ L h]

theorem isLabel_swap {j : ℕ} {L : Fin n → Fin 3} (h : IsLabel j L) (r s : Fin n) :
    IsLabel j (L ∘ Equiv.swap r s) := by
  intro a
  rw [← h a]
  exact Finset.card_equiv (Equiv.swap r s) (by simp)

theorem moved_labels (χ₀ : Fin n → ℂ) (j : ℕ) : ∀ (ss : List (Fin n)) (χ : Fin n → ℂ) (Λ : Set (Fin n → Fin 3)),
    GoodPath χ ss → (∀ r s, r ≠ s → χ r = χ s → χ r = χ₀ r ∧ χ s = χ₀ s) →
    (∀ L ∈ Λ, IsLabel j L ∧ (deg χ₀ L).re < 0) →
    ∀ L ∈ moveIter χ Λ ss, IsLabel j L ∧ (deg χ₀ L).re < 0 := by
  intro ss
  induction ss with
  | nil =>
    intro χ Λ _ _ hΛ L hL
    exact hΛ L hL
  | cons t ss ih =>
    intro χ Λ hg hT hΛ L hL
    refine ih (χ + Pi.single t 1) (move χ Λ t) hg.2 (tie_step hT hg.1) ?_ L hL
    rintro _ ⟨L₀, hL₀, r, hr, rfl⟩
    obtain ⟨hl, hd⟩ := hΛ L₀ hL₀
    refine ⟨isLabel_swap hl r t, ?_⟩
    by_cases hrt : r = t
    · subst hrt
      simpa using hd
    · obtain ⟨h1, h2⟩ := hT r t hrt hr
      rw [deg_swap χ₀ L₀ (h1.symm.trans (hr.trans h2))]
      exact hd

theorem labelTrack : LabelTrack := by
  intro n χ ss B j hg hf L hL
  obtain ⟨hl, hd⟩ := moved_labels χ j ss χ _ hg (fun _ _ _ _ => ⟨rfl, rfl⟩) (fun _ h => h) L hL
  refine hf (univ.filter fun s => L s = 2) (univ.filter fun s => L s = 0) ?_ ?_ hd
  · refine Finset.disjoint_filter.2 fun x _ h1 h2 => ?_
    rw [h1] at h2
    exact absurd h2 (by decide)
  · rw [hl 2, hl 0]
    simp [dims]

end GlobalTheory.CompanionTheory.Labels
end
end

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.ExhaustionLabels

section

@[expose] public section

namespace CompanionTheory.RgExh.Dec.J

theorem exhaustion_labels : CompanionTheory.RgExh.Dec.Labels := by
  exact labels_of GlobalTheory.CompanionTheory.LocFinFilt.locFin GlobalTheory.CompanionTheory.TensStep.tensDecomp GlobalTheory.CompanionTheory.RgTransport.transport
    GlobalTheory.CompanionTheory.CoefFilt.famFilt GlobalTheory.CompanionTheory.RgStepFam.stepFam GlobalTheory.CompanionTheory.BaseFamily.baseFam GlobalTheory.CompanionTheory.RgStartOne.start1
    GlobalTheory.CompanionTheory.RgExhDec.DegreeP.degree GlobalTheory.CompanionTheory.GradEig.basis GlobalTheory.CompanionTheory.Labels.labelTrack

end CompanionTheory.RgExh.Dec.J
end
end
