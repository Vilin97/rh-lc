module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpOrbOfAmpDD
public import CompanionTheory.AutomorphicTheory.RankOneEstimates.DecSender
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BeBessel
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.GrowthSphericalBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothAdd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.QuotMeasExists
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
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
import Mathlib.Tactic.Linter.Style
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
public import Formalism.HermitianCurvature.StatementB
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSmoothA

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MultiplicityDescent.JScaleMoveB

section

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Down.ScaleMoveB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Mult1.SmoothA

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section sm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end sm

theorem lie_conj {t X : Mat k r} (ht : t ∈ GV k r) (hX : Formalism.MainNotions.S.InLieHpk k r X) :
    Formalism.MainNotions.S.InLieHpk k r (t⁻¹ * X * t) := by
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hh : ∀ A : Mat k r, Hpk k r * (Hpk k r * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hpk_sq, Matrix.one_mul]
  have key : (t⁻¹ * X * t)ᴴ * Hpk k r + Hpk k r * (t⁻¹ * X * t) = tᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * t := by
    rw [gv_inv_eq ht]
    simp only [conjTranspose_mul, hpk_conjT, conjTranspose_conjTranspose, Matrix.mul_assoc, hpk_sq,
      Matrix.mul_one, hh, Matrix.add_mul, Matrix.mul_add]
  show (t⁻¹ * X * t)ᴴ * Hpk k r + Hpk k r * (t⁻¹ * X * t) = 0
  rw [key, hX', Matrix.mul_zero, Matrix.zero_mul]

theorem dsig_conj {σ : Mat k r → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (GV k r) σ) {t : Mat k r}
    (ht : t ∈ GV k r) {X : Mat k r} (hX : Formalism.MainNotions.S.InLieHpk k r X) (u : H) :
    Formalism.MainNotions.S.dsig (k := k) (r := r) σ X (σ t u) = σ t (Formalism.MainNotions.S.dsig (k := k) (r := r) σ (t⁻¹ * X * t) u) := by
  have hti := gv_inv_mem ht
  have hu : IsUnit t := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (gv_mul_inv ht))
  have hfun : (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (σ t u)) =
      fun s : ℝ => σ t (σ (NormedSpace.exp ((s : ℂ) • (t⁻¹ * X * t))) u) := by
    funext s
    have hE : NormedSpace.exp ((s : ℂ) • X) ∈ GV k r := by rw [cast_smul]; exact exp_mem hX s
    have hconj : (s : ℂ) • (t⁻¹ * X * t) = t⁻¹ * ((s : ℂ) • X) * t := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [hconj, Matrix.exp_conj' _ _ hu]
    have h1 : σ (NormedSpace.exp ((s : ℂ) • X)) (σ t u) = σ (NormedSpace.exp ((s : ℂ) • X) * t) u := by
      rw [hσ.1.2 _ hE _ ht]; rfl
    have h2 : σ t (σ (t⁻¹ * NormedSpace.exp ((s : ℂ) • X) * t) u) =
        σ (t * (t⁻¹ * NormedSpace.exp ((s : ℂ) • X) * t)) u := by
      rw [hσ.1.2 _ ht _ (gv_mul (gv_mul hti hE) ht)]; rfl
    rw [h1, h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, gv_mul_inv ht, Matrix.one_mul]
  unfold Formalism.MainNotions.S.dsig
  rw [hfun]
  set f := fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • (t⁻¹ * X * t))) u with hf
  by_cases hd : DifferentiableAt ℝ f 0
  · exact (((σ t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt).deriv
  · have hnd : ¬ DifferentiableAt ℝ (fun s => σ t (f s)) 0 := by
      intro hd'
      apply hd
      have hinv : ∀ y : H, σ t⁻¹ (σ t y) = y := fun y => by
        rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ hti _ ht, gv_inv_mul ht, hσ.1.1]; rfl
      have : f = fun s => σ t⁻¹ (σ t (f s)) := by funext s; rw [hinv]
      rw [this]
      exact ((σ t⁻¹).restrictScalars ℝ).differentiableAt.comp (0 : ℝ) hd'
    rw [deriv_zero_of_not_differentiableAt hnd, deriv_zero_of_not_differentiableAt hd, map_zero]

end ReciprocityTheory.ChartRestriction.DS.Mult1.Down.ScaleMoveB
end
end
end

-- Source module: CompanionTheory.AutomorphicTheory.RankOneTori.NzTranslate

section

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.MainStatements.RankOne

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}

theorem dsigW_conj (hσ : IsURepOn (UH (Hpk k r)) σ) {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r)) :
    ∀ ws : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), (∀ X ∈ ws, PI.UpqRep.InLieHpk k r X) → ∀ u : H,
      PI.UpqRep.dsigW (k := k) (r := r) σ ws (σ t u) =
        σ t (PI.UpqRep.dsigW (k := k) (r := r) σ (ws.map fun X => t⁻¹ * X * t) u)
  | [], _, _ => rfl
  | X :: w, hw, u => by
    simp only [PI.UpqRep.dsigW, List.map_cons]
    rw [dsigW_conj hσ ht w (fun Y hY => hw Y (List.mem_cons_of_mem X hY)) u]
    exact ReciprocityTheory.ChartRestriction.DS.Mult1.Down.ScaleMoveB.dsig_conj hσ ht (hw X List.mem_cons_self) _

theorem nz_translate (hKD : Pv.AmpDD.KDense) (hlam : IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ)
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} {Bm : H → Wp} (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π Bm)
    {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r)) {v : H} (hv : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) (hBv : Bm v ≠ 0) :
    ∃ u : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ u ∧ Bm (σ t u) ≠ 0 := by
  have hU : IsURepOn (UH (Hpk k r)) σ := Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hσ
  have hti := WeylGroupFacts.uh_inv ht
  have hu : IsUnit t.det := (unitary_group_closed k r).unit t ht
  set x := σ t⁻¹ v with hx
  have hxs : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := TranslationBesselVanishing.smooth_translate hσ hv hti
  have htx : σ t x = v := by
    rw [hx, ← ContinuousLinearMap.comp_apply, ← TranslationBesselVanishing.sigma_mul hσ ht hti, Matrix.mul_nonsing_inv _ hu,
      (MatrixMultiplicationContinuity.sigma_facts hσ).1]
    rfl
  obtain ⟨hadd, -, -, C, Ws, hWs, hbd⟩ := hB
  have hpos : 0 < ‖Bm v‖ := norm_pos_iff.mpr hBv
  set e : ℝ := ‖Bm v‖ / (|C| + 1) with he
  have he0 : 0 < e := div_pos hpos (by positivity)
  obtain ⟨u, huK, hue⟩ := hKD k r ε lam H σ hlam hσ x hxs (Ws.map (List.map fun X => t⁻¹ * X * t))
    (fun w hw X hX => by
      obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
      obtain ⟨X0, hX0, rfl⟩ := List.mem_map.1 hX
      exact ReciprocityTheory.ChartRestriction.DS.Mult1.Down.ScaleMoveB.lie_conj ht (hWs w0 hw0 X0 hX0)) e he0
  refine ⟨u, huK, fun h0 => ?_⟩
  have hus : u ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := CompanionTheory.D.gk.admitted.k_finite_smooth k r ε lam H σ hlam hσ u huK
  have hds : x - u ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ u]
    exact DDSmoothness.smooth_add hxs (DDSmoothness.smooth_smul (-1) hus)
  have hsplit : Bm v = Bm (σ t (x - u)) := by
    have := hadd _ (TranslationBesselVanishing.smooth_translate hσ hds ht) _ (TranslationBesselVanishing.smooth_translate hσ hus ht)
    rw [← map_add (f := _), sub_add_cancel, htx, h0, add_zero] at this
    exact this
  have hb := hbd _ (TranslationBesselVanishing.smooth_translate hσ hds ht)
  have hmap : (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (σ t (x - u))‖) =
      (Ws.map (List.map fun X => t⁻¹ * X * t)).map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (x - u)‖ := by
    rw [List.map_map]
    refine List.map_congr_left fun w hw => ?_
    rw [dsigW_conj hU ht w (hWs w hw), (MatrixMultiplicationContinuity.sigma_facts hσ).2 t ht]
    rfl
  rw [hmap, ← hsplit] at hb
  set S := ((Ws.map (List.map fun X => t⁻¹ * X * t)).map
    fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (x - u)‖).sum with hS
  have hS0 : 0 ≤ S := by
    rw [hS]; apply List.sum_nonneg; intro y hy
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy; exact norm_nonneg _
  have h1 : ‖Bm v‖ ≤ |C| * S := hb.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hS0)
  have h2 : |C| * S ≤ |C| * e := mul_le_mul_of_nonneg_left hue.le (abs_nonneg C)
  have h3 : |C| * e < ‖Bm v‖ := by
    rw [he, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg C]
  linarith

theorem side_nz (hKD : Pv.AmpDD.KDense) {h : ℝ} (hlam : IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hO : ThreeDimData.GapOK k r h) {w0 : H} (hw0 : PI.UpqRep.IsLowUnitH k r ε lam σ w0)
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {c : ℂ} (hc : c ≠ 0) {u : Fin k → ℝ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} (hπ : IsHCTypeW k r z u π) {μW : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW)
    (hW1 : μW Set.univ = 1) {κ : ℝ≥0∞} (h0 : κ ≠ 0) (h1 : κ ≠ ⊤) {l : H → Wp}
    (hl : ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      ThreeDimData.be z c π σ μW (haarLie (Nset k r) κ) w v = (innerSL ℂ (l v)).smulRight (l w))
    {v : H} (hv : PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v) (hlv : l v ≠ 0) {t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ht : t ∈ UH (Hpk k r)) :
    ∃ y : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ y ∧ l (σ t y) ≠ 0 ∧ ∀ a : ℂ, l (a • σ t y) = a • l (σ t y) := by
  obtain ⟨μG, hμG⟩ := unitary_group_haar_exists k r
  have hGsk : IsHaarOn (UH (Hpk k r)) μG := ⟨B5.haar_sigmaFinite hμG, hμG.ne_zero, hμG.conc, hμG.left⟩
  have hS := Formalism.L2.SG.Pf.Choice.isHaarOn_muS hz hT hW hW1 h0 h1
  obtain ⟨νq, hq⟩ := Formalism.L2.SG.Pf.QuotMeasExists.quotMeasExists k r z hz hT μG _ hGsk hS
  have hN : IsHaarOn (Nset k r) (haarLie (Nset k r) κ) := Formalism.MainNotions.BridgeCSB.haarLieN k r κ h0 h1
  have hB := PI.WBL.S5.G.beBessel_of growth_spherical_bound
    ⟨CompanionTheory.FamilyDerivativeExpansion.DecS.decay_low_range, CompanionTheory.FamilyDerivativeExpansion.DecS.decay_infinite_range, CompanionTheory.D.gk.admitted.k_finite_smooth, trivial⟩
    k r ε lam h H σ w0 Wp z c u π μW _ μG νq ⟨hlam, hσ, hg, hO, hw0, hz, hT, hc, hπ, hW, hN, hGsk, hq⟩ v (Or.inr hv) (l v)
  have hvs := CompanionTheory.D.gk.admitted.k_finite_smooth k r ε lam H σ hlam hσ v hv
  have hn : ⟪l v, l v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hlv
  have he : ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      ThreeDimData.be z c π σ μW (haarLie (Nset k r) κ) x v (l v) = ⟪l v, l v⟫_ℂ • l x := fun x hx => by
    rw [hl x hx v hvs]; rfl
  obtain ⟨y, hy, hne⟩ := nz_translate hKD hlam hσ hB ht hvs (by
    show ThreeDimData.be z c π σ μW (haarLie (Nset k r) κ) v v (l v) ≠ 0
    rw [he v hvs]; exact smul_ne_zero hn hlv)
  have hys := TranslationBesselVanishing.smooth_translate hσ (CompanionTheory.D.gk.admitted.k_finite_smooth k r ε lam H σ hlam hσ y hy) ht
  refine ⟨y, hy, fun h0 => hne ?_, fun a => ?_⟩
  · show ThreeDimData.be z c π σ μW (haarLie (Nset k r) κ) _ v (l v) = 0
    rw [he _ hys, h0, smul_zero]
  · have h2 : ThreeDimData.be z c π σ μW (haarLie (Nset k r) κ) (a • σ t y) v (l v) =
        a • ThreeDimData.be z c π σ μW (haarLie (Nset k r) κ) (σ t y) v (l v) := hB.2.1 a _ hys
    rw [he _ hys, he _ (DDSmoothness.smooth_smul a hys), smul_comm] at h2
    exact smul_right_injective _ hn h2

end Formalism.MainStatements.RankOne
end
end
end
