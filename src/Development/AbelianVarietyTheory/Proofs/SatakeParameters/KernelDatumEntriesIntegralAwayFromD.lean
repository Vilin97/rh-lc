module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CombOfTied
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsNormalisedThetaCombinationsAwayDStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.GaussJetBounds.StatementN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralEigenCombination
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeJetsIntegralIffIntegralFrames
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DerivationCoordinateChange
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsRBasisOfLocBasis
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
import Mathlib.Topology.Sheaves.Init
import Formalism.GaussJetBounds.StatementH
import Mathlib.Tactic.ReduceModChar
public import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixUnitIntegralCombEmbeddedHoms

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.EntryHomComb

open Matrix

variable {p : ℕ} [Fact p.Prime]

theorem det_map_isUnit (D : D7) (ρ : D.host.E →+* ℂ_[p]) {N : ℕ} {P : Matrix (Fin N) (Fin N) D.host.E}
    (h : P.det ≠ 0) : IsUnit (P.map ρ).det := by
  have := ρ.map_det P
  rw [RingHom.mapMatrix_apply] at this
  rw [← this]
  exact Ne.isUnit ((map_ne_zero ρ).2 h)

theorem coord_le_one (D : D7) (ρ : D.host.E →+* ℂ_[p]) {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {P : Matrix (Fin N) (Fin N) D.host.E} (hP : LocBasisW D ρ L P) {x : Fin N → D.host.E} (hx : x ∈ L) (m : Fin N) :
    ‖((P.map ρ)⁻¹ *ᵥ fun i => ρ (x i)) m‖ ≤ 1 := by
  obtain ⟨s, hs, c, hc⟩ := hP.2.2 x hx
  have hs0 : ρ (s : D.host.E) ≠ 0 := by
    intro h; rw [h, norm_zero] at hs; exact zero_ne_one hs
  have e : ∀ i, (s : D.host.E) * x i = ∑ a, (c a : D.host.E) * P i a := fun i => by
    have := congrFun hc i
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply] at this
    exact this
  have h1 : (fun i => ρ (x i)) = (P.map ρ) *ᵥ fun a => (ρ (s : D.host.E))⁻¹ * ρ (c a : D.host.E) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    have h2 := congrArg ρ (e i)

    rw [map_mul, map_sum] at h2
    simp only [map_mul] at h2
    calc ρ (x i) = (ρ (s : D.host.E))⁻¹ * (ρ (s : D.host.E) * ρ (x i)) := by field_simp
      _ = _ := by
        rw [h2, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
  rw [h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (det_map_isUnit D ρ hP.1), Matrix.one_mulVec, norm_mul,
    norm_inv, hs, inv_one, one_mul]
  exact GlobalTheory.JetTieCompare.norm_int_le ρ (c m)

theorem inv_mul_le_one (D : D7) {lm : Qbar →+* ℂ_[p]} {τ : D.what₂.Tau} (ρ : D.host.E →+* ℂ_[p]) (hρ : tauEmb D lm τ = ρ)
    {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {B P : Matrix (Fin N) (Fin N) _}
    (hB : GL3Columns.BasR D lm τ L B) (hP : LocBasisW D ρ L P) (m b : Fin N) : ‖((P.map ρ)⁻¹ * B) m b‖ ≤ 1 := by
  obtain ⟨n, r, x, hr, hx, hcol⟩ := hB.2.2 b
  have : ((P.map ρ)⁻¹ * B) m b = ∑ k, r k * ((P.map ρ)⁻¹ *ᵥ fun i => ρ (x k i)) m := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hcol, hρ, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hr k) (norm_nonneg _) (coord_le_one D ρ hP (hx k) m)

theorem inv_mul_le_one' (D : D7) {lm : Qbar →+* ℂ_[p]} {τ : D.what₂.Tau} (ρ : D.host.E →+* ℂ_[p]) (hρ : tauEmb D lm τ = ρ)
    {N : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {B : Matrix (Fin N) (Fin N) ℂ_[p]}
    {P : Matrix (Fin N) (Fin N) D.host.E}
    (hB : GL3Columns.BasR D lm τ L B) (hP : LocBasisW D ρ L P) (a i : Fin N) : ‖(B⁻¹ * P.map ρ) a i‖ ≤ 1 := by
  obtain ⟨s, hs, hmem⟩ := hP.2.1 i
  have h := hB.2.1 _ hmem a
  rw [hρ] at h
  have e : (fun j => ρ ((s • P.transpose i) j)) = ρ (s : D.host.E) • fun j => ρ (P j i) := by
    funext j
    change ρ ((s : D.host.E) * P j i) = ρ (s : D.host.E) * ρ (P j i)
    rw [map_mul]
  rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, hs, one_mul] at h
  convert h using 2
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem entry_comb : ∀ (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (τ : D.what₂.Tau) (B : Matrix (Fin N) (Fin N) ℂ_[p]) (B' : Matrix (Fin N') (Fin N') ℂ_[p]), GL3Columns.BasR D lm τ L B → GL3Columns.BasR D lm τ L' B' → ∀ (a : Fin N) (b : Fin N'), ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (A : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, A j ∈ homL D L L') ∧ ∀ k l, B' k b * B⁻¹ a l = ∑ j, r j * tauEmb D lm τ (A j k l) := by
  intro D N N' L L' hA p _ lm τ B B' hB hB' a b
  obtain ⟨ρ, hρ⟩ := GlobalTheory.JetTieCompare.exists_tauHom D lm τ
  obtain ⟨P, hP⟩ := GlobalTheory.JetTieCompare.exists_locBasis D ρ L hA.2.2.1.1 hA.2.2.1.2.1
  obtain ⟨P', hP'⟩ := GlobalTheory.JetTieCompare.exists_locBasis D ρ L' hA.2.2.2.1 hA.2.2.2.2.1
  have hex : ∀ q : Fin N' × Fin N, ∃ s : D.host.E, ‖ρ s‖ = 1 ∧
      (Matrix.of fun i j => s * (P' i q.1 * P⁻¹ q.2 j)) ∈ homL D L L' := fun q =>
    GlobalTheory.Proof.DirectionalDerivative.exists_smul_mem_homL D ρ hA.2.2.1.1 hP hP' q.2 q.1
  choose s hs hsA using hex
  have hs0 : ∀ q, ρ (s q) ≠ 0 := fun q h => by rw [← norm_eq_zero, hs q] at h; exact one_ne_zero h
  let e := Fintype.equivFin (Fin N' × Fin N)
  have hdet := det_map_isUnit D ρ hP.1
  have hdet' := det_map_isUnit D ρ hP'.1
  have hinv : (P.map ρ)⁻¹ = (P⁻¹).map ρ := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hP.1), Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  refine ⟨Fintype.card (Fin N' × Fin N),
    fun j => ((P'.map ρ)⁻¹ * B') (e.symm j).1 b * (B⁻¹ * P.map ρ) a (e.symm j).2 * (ρ (s (e.symm j)))⁻¹,
    fun j => Matrix.of fun k l => s (e.symm j) * (P' k (e.symm j).1 * P⁻¹ (e.symm j).2 l), fun j => ?_,
    fun j => hsA _, fun k l => ?_⟩
  · rw [norm_mul, norm_mul, norm_inv, hs, inv_one, mul_one]
    exact mul_le_one₀ (inv_mul_le_one D ρ hρ hB' hP' _ b) (norm_nonneg _) (inv_mul_le_one' D ρ hρ hB hP a _)
  · have e1 : B' k b = ∑ m, ρ (P' k m) * ((P'.map ρ)⁻¹ * B') m b := by
      conv_lhs => rw [← Matrix.mul_nonsing_inv_cancel_left (P'.map ρ) B' hdet']
      rw [Matrix.mul_apply]
      simp only [Matrix.map_apply]
    have e2 : B⁻¹ a l = ∑ i, (B⁻¹ * P.map ρ) a i * ρ (P⁻¹ i l) := by
      conv_lhs => rw [← Matrix.mul_nonsing_inv_cancel_right (P.map ρ) B⁻¹ hdet, hinv]
      rw [Matrix.mul_apply]
      simp only [Matrix.map_apply]
    rw [e1, e2, Finset.sum_mul_sum, ← Fintype.sum_prod_type', hρ, ← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.of_apply, map_mul]
    field_simp [hs0 (e.symm j)]

end GlobalTheory.EntryHomComb
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixUnitIntegralCombEmbeddedHomsStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

theorem _root_.GlobalTheory.T.matrixUnit_integral_comb_embedded_homs : ∀ (D : D7) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (τ : D.what₂.Tau) (B : Matrix (Fin N) (Fin N) ℂ_[p]) (B' : Matrix (Fin N') (Fin N') ℂ_[p]), GL3Columns.BasR D lm τ L B → GL3Columns.BasR D lm τ L' B' → ∀ (a : Fin N) (b : Fin N'), ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (A : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, A j ∈ homL D L L') ∧ ∀ k l, B' k b * B⁻¹ a l = ∑ j, r j * tauEmb D lm τ (A j k l) := by
  first | exact @GlobalTheory.EntryHomComb.entry_comb | exact GlobalTheory.EntryHomComb.entry_comb | (intros; apply GlobalTheory.EntryHomComb.entry_comb <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsRealPlaceLocalBases

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.Proof.integral_jets_realPlace_local_bases

theorem tauEmb_ringHom (D : D7) {p : ℕ} [Fact p.Prime] (lm : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) :
    ∃ g : D.host.E →+* ℂ_[p], ∀ x, tauEmb D lm τ x = g x := by
  have hm : ∀ x, embT D τ x ∈ Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom)
  exact ⟨lm.comp ((embT D τ).codRestrict Qbar hm), fun x => dif_pos (hm x)⟩

theorem jetsIntegral_basR : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (B : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ_[p]) (B' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ_[p]) (κ : D.what₂.Tau → ℂ_[p]), (∀ τ, GL3Columns.BasR D lm τ L (B τ)) → (∀ τ, GL3Columns.BasR D lm τ L' (B' τ)) → (∀ τ, ‖κ τ‖ ≤ ‖lamC lm (cD τ)‖) → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], JetsInt D lm (YYl D L L') F → JetsIntegral (atLin (fun (k : D.what₂.Tau × Fin N' × Fin N) (j : (Bool × HH D) × Fin N × Fin N') => if tauPl D j.1 = k.1 then κ k.1 * B' k.1 k.2.1 j.2.2 * (B k.1)⁻¹ j.2.1 k.2.2 else 0) (fun j => MvPowerSeries.X j) F) := by
  intro D cD hD N N' L L' hA p _ lm B B' κ hB hB' hκ F hF
  refine (GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames.jetsInt_frames D N N' p lm (YYl D L L') F).2 hF _ _ ?_
  rintro ⟨j1, a, b⟩
  by_cases h0 : lamC lm (cD (tauPl D j1)) = 0
  · refine ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, fun ⟨τ, k1, k2⟩ => ?_⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    split_ifs with h
    · subst h
      have : κ (tauPl D j1) = 0 := by
        have := hκ (tauPl D j1); rw [h0, norm_zero] at this; exact norm_le_zero_iff.1 this
      simp [this]
    · rfl
  · set τ0 := tauPl D j1 with hτ0
    set c := κ τ0 / lamC lm (cD τ0) with hc
    have hcn : ‖c‖ ≤ 1 := by
      rw [hc, norm_div]; exact div_le_one_of_le₀ (hκ τ0) (norm_nonneg _)
    obtain ⟨n, r, aa, hr, haa, hsum⟩ := GlobalTheory.Proof.IntegralEigenCombination.eigGen_integral_comb D cD hD p lm τ0
    obtain ⟨m, r', A, hr', hA', hAsum⟩ :=
      GlobalTheory.T.matrixUnit_integral_comb_embedded_homs D N N' L L' hA p lm τ0 (B τ0) (B' τ0) (hB τ0) (hB' τ0) a b
    refine ⟨n * m, fun t => c * r (finProdFinEquiv.symm t).1 * r' (finProdFinEquiv.symm t).2,
      fun t => aa (finProdFinEquiv.symm t).1 • A (finProdFinEquiv.symm t).2, ?_, ?_, ?_⟩
    · intro t
      rw [norm_mul, norm_mul]
      calc ‖c‖ * ‖r _‖ * ‖r' _‖ ≤ 1 * 1 * 1 := by
            gcongr
            · exact hr _
            · exact hr' _
        _ = 1 := by norm_num
    · intro t
      exact Submodule.subset_span ⟨aa _, haa _, A _, hA' _, rfl⟩
    · rintro ⟨τ, k1, k2⟩
      obtain ⟨g, hg⟩ := tauEmb_ringHom D lm τ
      rw [← finProdFinEquiv.sum_comp]
      simp only [Equiv.symm_apply_apply]
      rw [Fintype.sum_prod_type]
      have key : ∑ i : Fin n, ∑ j : Fin m, c * r i * r' j * tauEmb D lm τ ((aa i • A j) k1 k2)
          = c * ((∑ i, r i * tauEmb D lm τ (aa i)) * (∑ j, r' j * tauEmb D lm τ (A j k1 k2))) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hg, Matrix.smul_apply, smul_eq_mul, map_mul]
        ring
      rw [key, hsum τ]
      split_ifs with h1 h2 h2
      · subst h2
        rw [← hAsum k1 k2, hc, ← mul_assoc, div_mul_cancel₀ _ h0, mul_assoc]
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
end GlobalTheory.Proof.integral_jets_realPlace_local_bases
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsRealPlaceLocalBasesStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

theorem _root_.GlobalTheory.T.integral_jets_realPlace_local_bases : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (B : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ_[p]) (B' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ_[p]) (κ : D.what₂.Tau → ℂ_[p]), (∀ τ, GL3Columns.BasR D lm τ L (B τ)) → (∀ τ, GL3Columns.BasR D lm τ L' (B' τ)) → (∀ τ, ‖κ τ‖ ≤ ‖lamC lm (cD τ)‖) → ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], JetsInt D lm (YYl D L L') F → JetsIntegral (atLin (fun (k : D.what₂.Tau × Fin N' × Fin N) (j : (Bool × HH D) × Fin N × Fin N') => if tauPl D j.1 = k.1 then κ k.1 * B' k.1 k.2.1 j.2.2 * (B k.1)⁻¹ j.2.1 k.2.2 else 0) (fun j => MvPowerSeries.X j) F) := by
  first | exact @GlobalTheory.Proof.integral_jets_realPlace_local_bases.jetsIntegral_basR | exact GlobalTheory.Proof.integral_jets_realPlace_local_bases.jetsIntegral_basR | (intros; apply GlobalTheory.Proof.integral_jets_realPlace_local_bases.jetsIntegral_basR <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KvalGeZeroOfIntegralJets

section

@[expose] public section

open Formalism.MainNotions Classical

namespace GlobalTheory.Proof.kvalGe_zero_of_integral_jets

theorem kvalGe_zero : ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime]
    (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]),
    Formalism.DworkPowerSeriesWeights.JetsIntegral Th → product_zeroth_first_parts.KvalGe N0 N1 l nu Th 0 := by
  intro Lt _ _ N0 N1 l _ nu Th hTh I m
  rw [neg_zero, Real.rpow_zero]
  unfold product_zeroth_first_parts.applyAt0
  rw [MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun μ _ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · rw [mul_assoc, norm_mul]
    refine mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one ℂ_[l] _) (norm_nonneg _) ?_
    have h := hTh (Finsupp.sumFinsuppEquivProdFinsupp μ).2
    unfold Formalism.DworkPowerSeriesWeights.mfact at h
    simpa [Finsupp.prod, Nat.cast_prod] using h
  · simp

end GlobalTheory.Proof.kvalGe_zero_of_integral_jets
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KvalGeZeroOfIntegralJetsStatement

section

@[expose] public section

open Formalism.MainNotions Classical

theorem _root_.GlobalTheory.T.kvalGe_zero_of_integral_jets : ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime] (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]), Formalism.DworkPowerSeriesWeights.JetsIntegral Th → product_zeroth_first_parts.KvalGe N0 N1 l nu Th 0 := by
  first | exact @GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero | exact GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero | (intros; apply GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumEntriesIntegralAwayFromD

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical

namespace GlobalTheory.Ggeo.AdmEntInt

theorem mod_three_eq_two_of_jacobiSym_neg_eq_one (d : ℕ) (h : jacobiSym (-(d : ℤ)) 3 = 1) : d % 3 = 2 := by
  rw [jacobiSym.mod_left] at h
  simp only [Nat.cast_ofNat] at h
  have : (-(d : ℤ)) % 3 = 0 ∨ (-(d : ℤ)) % 3 = 1 ∨ (-(d : ℤ)) % 3 = 2 := by omega
  rcases this with h0 | h0 | h0 <;> rw [h0] at h
  · norm_num at h
  · omega
  · norm_num at h

end GlobalTheory.Ggeo.AdmEntInt

theorem GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → 3 ≤ D.host.splitBound → ∀ ep be sg, OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  intro hIn D L hT Gi Gl K Y cX ex t hHyp h3 ep be sg
  intro u μ w hlf hd i hi _heven c c'
  have hlf' : LevFree Y u μ w := hlf
  obtain ⟨hAdm, hComb⟩ := GlobalTheory.Ggeo.KerComb.comb_of_tied hIn.algT D L hT Gi Gl K Y cX ex t hHyp u μ w hlf' i hi c c'
  have hd3 : D.what₂.places.resChar w = 3 → D.host.d % 3 = 2 := fun _ =>
    GlobalTheory.Ggeo.AdmEntInt.mod_three_eq_two_of_jacobiSym_neg_eq_one _ (D.host.split_small 3 Nat.prime_three (by norm_num) h3)
  have hJ := GlobalTheory.T.integralJets_normalisedThetaCombinations_away_d hIn D t.cc t.δ t.cc_ok t.δ_ok t.B t.χ t.χ_ok t.X t.seam t.seam_ok _ _ _ _ hAdm
    (D.what₂.places.resChar w) (t.ent.lam w) hd hd3 _ hComb
  let T := t.kf u μ w hlf'
  have hB := T.B_bas i hi.le c
  have hB' := T.B_bas (i + 1) hi c'
  have hK := GlobalTheory.T.integral_jets_realPlace_local_bases D (t.O u μ).dgen (t.O u μ).dgen_gen _ _ _ _ hAdm (D.what₂.places.resChar w) (t.ent.lam w)
    (T.B i c) (T.B (i + 1) c') (fun τ => T.c0 i c c' τ * TaylorLogMetric.lamC (t.ent.lam w) ((t.O u μ).dgen τ)) hB hB'
    (fun τ => by rw [norm_mul, T.unitAbs_eq_one, one_mul]) _ hJ
  rw [← T.th i hi c c'] at hK
  exact GlobalTheory.T.kvalGe_zero_of_integral_jets _ _ _ _ _ _ hK
end
end
