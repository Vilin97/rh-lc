module

public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.XiOfSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLat
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DescentCore
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixHomLatticeLeSpanIdealHomImageStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemClosureIffMapMemMatrixHomLatticeCompletionStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumberFieldCompletionRingEquivOfDenseUnramifiedStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RelIndexMatrixHomLatticeRatioEqResiduePowStatement
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesTrivial
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdealMulHomMapMemMatrixHomLattice

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt

noncomputable section

namespace GlobalTheory.TwU

theorem map_mem_homLat_of_mem_YYl : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : D.host.E →+* Qq) (hA : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E)) (h1 : ∀ x : 𝓞 D.host.E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) {k k' : ℕ} (N : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin k' → D.host.E)) (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq) (hNa : Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → D.host.E))) = colSpan W a) (hNb : Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → D.host.E))) = colSpan W b), ∀ A ∈ TaylorLogMetric.YYl D N N', A.map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
  intro D P W Qq _ _ _ _ _ _ p hp ρ hA h1 k k' N N' a b hNa hNb

  have hsc : ∀ (c : D.host.E) (M : Matrix (Fin k') (Fin k) D.host.E), (∃ y : W, ρ c = algebraMap W Qq y) →
      M.map ρ ∈ homLat W (colSpan W a) (colSpan W b) → (c • M).map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
    rintro c M ⟨y, hy⟩ hM z hz
    have e : (c • M).map ρ = y • M.map ρ := by
      ext i j
      simp [Matrix.map_apply, map_mul, hy, Algebra.smul_def]
    rw [e, Matrix.smul_mulVec]
    exact (colSpan W b).smul_mem y (hM z hz)
  have hO : ∀ c : 𝓞 D.host.E, ∃ y : W, ρ (c : D.host.E) = algebraMap W Qq y := fun c =>
    (h1 c).imp fun y hy => hy.1

  have hAA : ∀ x ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ y : W, ρ x = algebraMap W Qq y := by
    intro x hx
    have hx' : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) :=
      ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using hx⟩
    rw [hA] at hx'
    obtain ⟨s, hs, hsx⟩ := hx'
    obtain ⟨t, ht⟩ := Submodule.mem_one.1 hsx
    obtain ⟨ys, hys, hsP⟩ := h1 s
    obtain ⟨yt, hyt⟩ := hO t
    have hu : IsUnit ys := by
      have hmax : IsLocalRing.maximalIdeal W = Ideal.span {(p : W)} :=
        (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hp
      by_contra hn
      have : ys ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal ys).2 hn
      rw [hmax, Ideal.mem_span_singleton] at this
      exact hs (hsP.2 this)
    refine ⟨hu.unit⁻¹ * yt, ?_⟩
    have e1 : ρ (algebraMap (𝓞 D.host.E) D.host.E t) = ρ (s : D.host.E) * ρ x := by
      rw [ht, Algebra.smul_def, map_mul]
    have e2 : algebraMap W Qq ys ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective W Qq)]
      exact hu.ne_zero
    rw [map_mul, ← hyt]
    change _ = _ * ρ (t : D.host.E)
    rw [show ((t : D.host.E)) = algebraMap (𝓞 D.host.E) D.host.E t from rfl, e1, hys, ← mul_assoc, ← map_mul,
      IsUnit.val_inv_mul, map_one, one_mul]

  have hHom : ∀ A ∈ TaylorLogMetric.homL D N N', A.map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
    intro A hA'
    induction hA' using Submodule.span_induction with
    | mem A hA0 =>
      intro z hz
      rw [← hNa] at hz
      rw [← hNb]
      induction hz using Submodule.span_induction with
      | mem z hz0 =>
        obtain ⟨x, hx, rfl⟩ := hz0
        refine Submodule.subset_span ⟨A *ᵥ x, hA0 x hx, ?_⟩
        funext i

        simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
      | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
      | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hz hz'
      | smul c z _ hz => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hz
    | zero => rw [Matrix.map_zero _ (map_zero ρ)]; exact Submodule.zero_mem _
    | add A B _ _ hA hB => rw [Matrix.map_add _ (map_add ρ)]; exact Submodule.add_mem _ hA hB
    | smul c A _ hA => exact hsc (c : D.host.E) A (hO c) hA
  intro A hA'
  induction hA' using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨c, hc, A, hA0, rfl⟩ := hB
    exact hsc c A (hAA c hc) (hHom A hA0)
  | zero => rw [Matrix.map_zero _ (map_zero ρ)]; exact Submodule.zero_mem _
  | add A B _ _ hA hB => rw [Matrix.map_add _ (map_add ρ)]; exact Submodule.add_mem _ hA hB
  | smul c A _ hA => exact hsc (c : D.host.E) A (hO c) hA

end GlobalTheory.TwU

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdealMulHomMapMemMatrixHomLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt

theorem _root_.GlobalTheory.T.ideal_mul_hom_map_mem_matrixHomLattice : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : D.host.E →+* Qq) (hA : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E)) (h1 : ∀ x : 𝓞 D.host.E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) {k k' : ℕ} (N : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin k' → D.host.E)) (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq) (hNa : Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → D.host.E))) = colSpan W a) (hNb : Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → D.host.E))) = colSpan W b), ∀ A ∈ TaylorLogMetric.YYl D N N', A.map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
  first | exact @GlobalTheory.TwU.map_mem_homLat_of_mem_YYl | exact GlobalTheory.TwU.map_mem_homLat_of_mem_YYl | (intros; apply GlobalTheory.TwU.map_mem_homLat_of_mem_YYl <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HomLatticeVolumeCompletionSplitPlace

section

@[expose] public section

noncomputable section

namespace GlobalTheory.VolAt

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix

theorem latAt_lattice {p : ℕ} [Fact p.Prime] (X : Sys p) (v : X.Pl) (j : ℕ) (L : (X.Pj j).Tup)
    (hL : (X.Pj j).IsLatTup L) :
    ∃ g : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v), IsUnit g.det ∧
      X.latAt v j L = colSpan (X.G.P.W v) g ∧ len X v j L = -ordP (X.G.P.W v) p g.det := by
  have hS := X.G.P.setting v
  haveI := hS.frac_alt
  cases j with
  | zero =>
    have h0 : IsLattice (X.G.P.W v) (X.latAt v 0 L) := hL v
    obtain ⟨g, hg, hL'⟩ := h0
    refine ⟨g, hg, hL', ?_⟩
    change lenLat (X.G.P.W v) p (X.latAt v 0 L) = _
    rw [hL']
    exact lenLat_colSpan hS.p_unif g hg
  | succ j =>
    have h0 : IsLattice (X.G.P.W v) (X.latAt v (j + 1) L) := hL v
    obtain ⟨g, hg, hL'⟩ := h0
    refine ⟨g, hg, hL', ?_⟩
    change lenLat (X.G.P.W v) p (X.latAt v (j + 1) L) = _
    rw [hL']
    exact lenLat_colSpan hS.p_unif g hg

theorem Pj_m_succ {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) : (X.Pj j).m + 1 = NN X.G.P.m X.t j := by
  cases j with
  | zero => simp [NN, Sys.Pj, Fills.Pj]
  | succ j =>
    simp only [NN, Sys.Pj, Fills.Pj, Places.withWt, Sys.t]
    ring

theorem homLat_conj {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k k' : ℕ}
    (M g : Matrix (Fin k) (Fin k) Qq) (M' g' : Matrix (Fin k') (Fin k') Qq) (hM' : IsUnit M'.det)
    (z : Matrix (Fin k') (Fin k) Qq) :
    z ∈ homLat W (colSpan W (M * g)) (colSpan W (M' * g')) ↔
      ∀ y ∈ colSpan W g, (M'⁻¹ * z * M) *ᵥ y ∈ colSpan W g' := by
  rw [← colSpan_mul, ← colSpan_mul, mem_homLat]
  have hinv : M'⁻¹ * M' = 1 := Matrix.nonsing_inv_mul M' hM'
  have hinv' : M' * M'⁻¹ = 1 := Matrix.mul_nonsing_inv M' hM'
  constructor
  · intro h y hy
    obtain ⟨u, hu, hu'⟩ := h (M *ᵥ y) (Submodule.mem_map_of_mem hy)
    have e : (M'⁻¹ * z * M) *ᵥ y = u := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have : z *ᵥ (M *ᵥ y) = M' *ᵥ u := hu'.symm
      rw [this, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    rw [e]
    exact hu
  · rintro h _ ⟨y, hy, rfl⟩
    have e : z *ᵥ ((M.mulVecLin.restrictScalars W) y) = M' *ᵥ ((M'⁻¹ * z * M) *ᵥ y) := by
      change z *ᵥ (M *ᵥ y) = _
      simp only [Matrix.mulVec_mulVec]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv', Matrix.one_mul]
    rw [e]
    exact Submodule.mem_map_of_mem (h y hy)

theorem vol_main : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (v : X.Pl) (j : ℕ) (ρ : D.host.E →+* X.G.P.Qq v) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) → (∀ x : 𝓞 D.host.E, ∃ y : X.G.P.W v, ρ x = algebraMap _ _ y ∧ (x ∈ P.asIdeal ↔ (p : X.G.P.W v) ∣ y)) → (∀ (y : X.G.P.W v) (n : ℕ), ∃ (x : 𝓞 D.host.E) (z : X.G.P.W v), ρ x = algebraMap _ _ (y + (p : X.G.P.W v) ^ n * z)) → ∃ φ : GL3Theta.EP D P ≃+* X.G.P.Qq v, (∀ x : D.host.E, φ (algebraMap _ _ x) = ρ x) ∧ ∀ (M : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (M' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)), IsUnit M.det → IsUnit M'.det → ∀ (N : (X.Pj j).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E)) (N' : (X.Pj (j + 1)).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E)) (S : Set ((X.Pj j).Tup × (X.Pj (j + 1)).Tup)), (∀ q ∈ S, (X.Pj j).IsLatTup q.1 ∧ (X.Pj (j + 1)).IsLatTup q.2 ∧ TaylorLogMetric.admitted D _ _ (N q.1) (N' q.2) ∧ Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N q.1 : Set (Fin ((X.Pj j).m + 1) → D.host.E))) = (X.latAt v j q.1).map ((M.mulVecLin).restrictScalars (X.G.P.W v)) ∧ Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N' q.2 : Set (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))) = (X.latAt v (j + 1) q.2).map ((M'.mulVecLin).restrictScalars (X.G.P.W v))) → ∀ q ∈ S, (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ X.ind v j q.1 q.2 (M'⁻¹ * y.map φ * M) = 1) ∧ ∀ q₀ ∈ S, GL3Theta.volP (GL3Theta.YP D P (N q₀.1) (N' q₀.2)) (GL3Theta.YP D P (N q.1) (N' q.2)) = (p : ℝ) ^ ((X.G.P.n' v : ℤ) * (volE X v j q.1 q.2 - volE X v j q₀.1 q₀.2)) := by
  intro D p _ X v j ρ P hA h1 h2
  have hS := X.G.P.setting v
  haveI := hS.frac_alt
  obtain ⟨φ, hφ, hop, hnb⟩ := GlobalTheory.T.numberField_completion_ringEquiv_of_dense_unramified P p hS.p_unif hS.eq_sum_herm_smul_frame_of_inW ρ h1 h2
  refine ⟨φ, hφ, ?_⟩
  intro M M' hM hM' N N' S hSq
  have key : ∀ q ∈ S, ∃ (g : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
      (g' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)),
      IsUnit (M * g).det ∧ IsUnit (M' * g').det ∧
      (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ y.map φ ∈ homLat (X.G.P.W v) (colSpan (X.G.P.W v) (M * g))
        (colSpan (X.G.P.W v) (M' * g'))) ∧
      (∀ z, X.ind v j q.1 q.2 (M'⁻¹ * z * M) = 1 ↔ z ∈ homLat (X.G.P.W v) (colSpan (X.G.P.W v) (M * g))
        (colSpan (X.G.P.W v) (M' * g'))) ∧
      ordP (X.G.P.W v) p (M * g).det = ordP (X.G.P.W v) p M.det - len X v j q.1 ∧
      ordP (X.G.P.W v) p (M' * g').det = ordP (X.G.P.W v) p M'.det - len X v (j + 1) q.2 := by
    intro q hq
    obtain ⟨hL, hL', hAdm, hsp, hsp'⟩ := hSq q hq
    obtain ⟨g, hg, hgL, hlen⟩ := latAt_lattice X v j q.1 hL
    obtain ⟨g', hg', hgL', hlen'⟩ := latAt_lattice X v (j + 1) q.2 hL'
    have hMg : IsUnit (M * g).det := by rw [Matrix.det_mul]; exact hM.mul hg
    have hMg' : IsUnit (M' * g').det := by rw [Matrix.det_mul]; exact hM'.mul hg'
    have hNa : Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N q.1 : Set (Fin ((X.Pj j).m + 1) → D.host.E))) =
        colSpan (X.G.P.W v) (M * g) := by rw [hsp, hgL, colSpan_mul]
    have hNb : Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N' q.2 : Set (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))) =
        colSpan (X.G.P.W v) (M' * g') := by rw [hsp', hgL', colSpan_mul]
    obtain ⟨-, -, ⟨hFG, hspan, -⟩, ⟨hFG', hspan', -⟩⟩ := hAdm
    refine ⟨g, g', hMg, hMg', fun y => ?_, fun z => ?_, ?_, ?_⟩
    · exact GlobalTheory.T.mem_closure_iff_map_mem_matrixHomLattice_completion P p hS.p_unif ρ h2 φ hφ hop hnb (TaylorLogMetric.YYl D (N q.1) (N' q.2)) _ _ hMg hMg'
        (GlobalTheory.T.ideal_mul_hom_map_mem_matrixHomLattice D P p hS.p_unif ρ hA h1 _ _ _ _ hNa hNb)
        (GlobalTheory.T.matrixHomLattice_le_span_ideal_hom_image D P p hS.p_unif ρ hA h1 _ _ hFG hFG' hspan hspan' _ _ hMg hMg' hNa hNb) y
    · rw [homLat_conj M g M' g' hM' z, ← hgL, ← hgL']
      unfold Sys.ind
      split_ifs with h
      · exact iff_of_true rfl h
      · exact iff_of_false (by norm_num) h
    · rw [Matrix.det_mul, ordP_mul hS.p_unif hM.ne_zero hg.ne_zero, hlen]
      ring
    · rw [Matrix.det_mul, ordP_mul hS.p_unif hM'.ne_zero hg'.ne_zero, hlen']
      ring
  intro q hq
  obtain ⟨g, g', hMg, hMg', hY, hind, ho, ho'⟩ := key q hq
  refine ⟨fun y => (hY y).trans (hind _).symm, fun q₀ hq₀ => ?_⟩
  obtain ⟨g₀, g₀', hMg₀, hMg₀', hY₀, -, ho₀, ho₀'⟩ := key q₀ hq₀
  let e : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (GL3Theta.EP D P) →+
      Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) :=
    φ.toAddEquiv.toAddMonoidHom.mapMatrix
  have he : Function.Surjective e := fun z => ⟨z.map φ.symm, by ext i l; simp [e]⟩
  have hYc : ∀ (A : Submodule (X.G.P.W v) _), (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ y.map φ ∈ A) →
      GL3Theta.YP D P (N q.1) (N' q.2) = A.toAddSubgroup.comap e := fun A h => by
    ext y; exact h y
  have hYc₀ : ∀ (A : Submodule (X.G.P.W v) _), (∀ y, y ∈ GL3Theta.YP D P (N q₀.1) (N' q₀.2) ↔ y.map φ ∈ A) →
      GL3Theta.YP D P (N q₀.1) (N' q₀.2) = A.toAddSubgroup.comap e := fun A h => by
    ext y; exact h y
  have hrel : ∀ A B : AddSubgroup (Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)),
      ((A.comap e).addSubgroupOf (B.comap e)).index = A.relIndex B := fun A B => by
    change (A.comap e).relIndex (B.comap e) = _
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective he]
  unfold GL3Theta.volP
  rw [hYc _ hY, hYc₀ _ hY₀, hrel, hrel,
    GlobalTheory.T.relIndex_matrixHomLattice_ratio_eq_residue_pow p (X.G.P.n' v) hS.p_unif hS.res_card _ _ _ _ hMg₀ hMg hMg₀' hMg', ho, ho', ho₀, ho₀']
  congr 1
  unfold volE
  rw [← Pj_m_succ X j, ← Pj_m_succ X (j + 1)]
  push_cast
  ring

end GlobalTheory.VolAt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HomLatticeVolumeCompletionSplitPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

theorem _root_.GlobalTheory.T.homLattice_volume_completion_splitPlace : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (v : X.Pl) (j : ℕ) (ρ : D.host.E →+* X.G.P.Qq v) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) → (∀ x : 𝓞 D.host.E, ∃ y : X.G.P.W v, ρ x = algebraMap _ _ y ∧ (x ∈ P.asIdeal ↔ (p : X.G.P.W v) ∣ y)) → (∀ (y : X.G.P.W v) (n : ℕ), ∃ (x : 𝓞 D.host.E) (z : X.G.P.W v), ρ x = algebraMap _ _ (y + (p : X.G.P.W v) ^ n * z)) → ∃ φ : GL3Theta.EP D P ≃+* X.G.P.Qq v, (∀ x : D.host.E, φ (algebraMap _ _ x) = ρ x) ∧ ∀ (M : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (M' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)), IsUnit M.det → IsUnit M'.det → ∀ (N : (X.Pj j).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E)) (N' : (X.Pj (j + 1)).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E)) (S : Set ((X.Pj j).Tup × (X.Pj (j + 1)).Tup)), (∀ q ∈ S, (X.Pj j).IsLatTup q.1 ∧ (X.Pj (j + 1)).IsLatTup q.2 ∧ TaylorLogMetric.admitted D _ _ (N q.1) (N' q.2) ∧ Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N q.1 : Set (Fin ((X.Pj j).m + 1) → D.host.E))) = (X.latAt v j q.1).map ((M.mulVecLin).restrictScalars (X.G.P.W v)) ∧ Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N' q.2 : Set (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))) = (X.latAt v (j + 1) q.2).map ((M'.mulVecLin).restrictScalars (X.G.P.W v))) → ∀ q ∈ S, (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ X.ind v j q.1 q.2 (M'⁻¹ * y.map φ * M) = 1) ∧ ∀ q₀ ∈ S, GL3Theta.volP (GL3Theta.YP D P (N q₀.1) (N' q₀.2)) (GL3Theta.YP D P (N q.1) (N' q.2)) = (p : ℝ) ^ ((X.G.P.n' v : ℤ) * (volE X v j q.1 q.2 - volE X v j q₀.1 q₀.2)) := by
  first | exact @GlobalTheory.VolAt.vol_main | exact GlobalTheory.VolAt.vol_main | (intros; apply GlobalTheory.VolAt.vol_main <;> assumption)
end
end
