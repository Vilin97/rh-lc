module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.DecaysZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClosedParabolicSubgroups
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroup
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Abstract
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ContinuousAverage
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.FlagNW
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.InvMemFlagN
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.RingTheory.PicardGroup
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsCompactBall
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroupStatement

section

@[expose] public section

open Formalism.MainNotions.S Matrix MeasureTheory

theorem _root_.GlobalTheory.T.schur_orthogonality_indefiniteUnitaryGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsSqIntOn ε σ → ∃ d : ℝ, IsFdeg (Formalism.REAL.muG ε) σ d := by
  first | exact @GlobalTheory.schur_orthogonality_unitary | exact GlobalTheory.schur_orthogonality_unitary | (intros; apply GlobalTheory.schur_orthogonality_unitary <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ConvCoef

section

@[expose] public section

open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

theorem UpperTheory.Lit.Cusp.conv_coef :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → ∀ v a : H,
        Continuous (coefOn (ε := ε) σ a v) ∧
          ∀ x, conv (muG ε) (coefOn σ v v) (coefOn σ a v) x = ((‖v‖ ^ 2 / d : ℝ) : ℂ) * coefOn σ a v x := by
  intro n ε H _ _ σ d hrep hF v a
  obtain ⟨⟨_, hmul⟩, hiso, hcont⟩ := hrep
  have hinner : ∀ g ∈ UJset ε, ∀ x y : H, ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g hg x y =>
    LinearIsometry.inner_map_map ⟨(σ g).toLinearMap, hiso g hg⟩ x y
  have hmem : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hcoef : ∀ w z : H, Continuous (coefOn (ε := ε) σ w z) := by
    intro w z
    have hu : Continuous fun g : UJ ε => umat g :=
      Units.continuous_val.comp continuous_subtype_val
    have hs : Continuous fun g : UJ ε => σ (umat g) w :=
      (hcont w).comp_continuous hu hmem
    exact continuous_const.inner hs
  refine ⟨hcoef a v, fun x => ?_⟩
  have hback : ∀ (g : UJ ε) (y : H), σ (umat g) (σ (umat g⁻¹) y) = y := by
    intro g y
    have h := hmul _ (hmem g) _ (hmem g⁻¹)
    have hone : umat g * umat g⁻¹ = 1 := by
      show ((g * g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val = 1
      rw [mul_inv_cancel]
      rfl
    rw [hone] at h
    have h1 : σ 1 = 1 := by assumption
    rw [h1] at h
    exact (congrArg (fun f : H →L[ℂ] H => f y) h).symm
  have key : ∀ g : UJ ε, coefOn σ v v g * coefOn σ a v (g⁻¹ * x) =
      coefOn σ v v g * star (coefOn σ v (σ (umat x) a) g) := by
    intro g
    congr 1
    simp only [coefOn]
    have hsplit : σ (umat (g⁻¹ * x)) a = σ (umat g⁻¹) (σ (umat x) a) := by
      rw [show umat (g⁻¹ * x) = umat g⁻¹ * umat x from rfl, hmul _ (hmem _) _ (hmem _)]
      rfl
    rw [hsplit]
    calc ⟪v, σ (umat g⁻¹) (σ (umat x) a)⟫_ℂ
        = ⟪σ (umat g) v, σ (umat g) (σ (umat g⁻¹) (σ (umat x) a))⟫_ℂ :=
          (hinner _ (hmem g) _ _).symm
      _ = ⟪σ (umat g) v, σ (umat x) a⟫_ℂ := by rw [hback]
      _ = star ⟪σ (umat x) a, σ (umat g) v⟫_ℂ := by
          rw [← inner_conj_symm]
          rfl
  show ∫ g, coefOn σ v v g * coefOn σ a v (g⁻¹ * x) ∂(muG ε) = _
  rw [show (fun g => coefOn σ v v g * coefOn σ a v (g⁻¹ * x)) =
      fun g => coefOn σ v v g * star (coefOn σ v (σ (umat x) a) g) from funext key,
    (hF.2 v v v (σ (umat x) a)).2, inner_self_eq_norm_sq_to_K]
  show _ = _ * ⟪v, σ (umat x) a⟫_ℂ
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, mul_comm]
  rw [mul_comm (_ * _) _, mul_comm ⟪v, σ (umat x) a⟫_ℂ, ← mul_assoc]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IntegralCoefEqZero

section

@[expose] public section

open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

theorem UpperTheory.Lit.Cusp.integral_coef_eq_zero :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsSqIntIrr ε σ → ∀ v a : H,
        Decays (coefOn (ε := ε) σ v v) → Decays (coefOn (ε := ε) σ a v) →
        ∀ W, IsIsoC ε W → ∀ ν : Measure (UJ ε), IsHaarSub (NW ε W) ν → ∀ x y : UJ ε,
          ∫ m, ⟪v, σ (umat (x * m * y)) a⟫_ℂ ∂ν = 0 := by
  intro n ε H _ _ σ hσ v a hvv hav W hW ν hν x y
  obtain ⟨hc, hn, hU, hI, hS⟩ := hσ
  obtain ⟨d, hd⟩ := GlobalTheory.T.schur_orthogonality_indefiniteUnitaryGroup n ε H σ hU hI hS
  have hd0 : 0 < d := hd.1
  by_cases hv : v = 0
  · subst hv
    simp
  have hv2 : (‖v‖ : ℝ) ^ 2 ≠ 0 := by positivity
  obtain ⟨hcvv, hconvvv⟩ := conv_coef n ε H σ d hU hd v v
  obtain ⟨hcav, hconvav⟩ := conv_coef n ε H σ d hU hd v a
  obtain ⟨hivv, -⟩ := continuous_average n ε _ hcvv hvv
  obtain ⟨hiav, hcontav⟩ := continuous_average n ε _ hcav hav
  obtain ⟨hν0, hνf, hνN, hνinv⟩ := hν
  haveI := hνf
  obtain ⟨hflag, h1, hNeq, S, hS⟩ := flagN_eq_NW n ε W hW
  obtain ⟨r, Hr, hr⟩ := exists_isRay n ε _ _ hflag (fun i => by fin_cases i; simpa using h1)
  rw [hNeq] at hr
  set k : ℂ := ((d / ‖v‖ ^ 2 : ℝ) : ℂ) with hk
  have hkc : k * ((‖v‖ ^ 2 / d : ℝ) : ℂ) = 1 := by
    rw [hk, ← Complex.ofReal_mul]
    rw [div_mul_div_comm, mul_comm d, div_self (mul_ne_zero hv2 hd0.ne')]
    simp
  have key := average_eq_zero (UJ ε) (muG ε) (NW ε W) r Hr ν hνN hνinv hr
    (fun g => k * coefOn σ v v g) (coefOn σ a v)
    (continuous_const.mul hcvv) (hivv.const_mul k) hcav hiav
    (by
      intro z
      simp only [conv] at hconvvv ⊢
      have := hconvvv z
      simp only [mul_assoc]
      rw [show (fun g => k * (coefOn σ v v g * (k * coefOn σ v v (g⁻¹ * z))))
          = fun g => (k * k) * (coefOn σ v v g * coefOn σ v v (g⁻¹ * z)) by
            funext g; ring]
      rw [MeasureTheory.integral_const_mul, this]
      linear_combination (k * coefOn σ v v z) * hkc)
    (by
      intro z
      simp only [conv] at hconvav ⊢
      have := hconvav z
      simp only [mul_assoc]
      rw [MeasureTheory.integral_const_mul, this]
      linear_combination (coefOn σ a v z) * hkc)
    x (hcontav S ν (by rw [hS]; exact ⟨hν0, hνf, hνN, hνinv⟩) x) y
  exact key
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.FibreIntegralEqZero

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Cusp

open GlobalTheory.FibreAtTau

theorem decays_of_decayAt {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (v a : M.H τ)
    (h : DecayAt M τ v a (2 * V.rank ^ 2 + 1)) : Decays (Formalism.MainNotions.S.coefOn (ε := M.ε τ) (M.σ τ) a v) := by
  obtain ⟨C, hC⟩ := h
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  obtain ⟨-, hmul, -, -⟩ := isCompact_ball V.rank (M.ε τ)
  set c : ℝ := 1 + Real.sqrt (Formalism.REAL.hs (M.fr τ)) * Real.sqrt (Formalism.REAL.hs (M.fr τ)⁻¹) with hc
  refine ⟨c ^ (2 * V.rank ^ 2 + 1) * C, fun u => ?_⟩
  set g := (M.fr τ)⁻¹ * Formalism.MainNotions.S.umat u * M.fr τ with hg
  have hu : M.fr τ * g * (M.fr τ)⁻¹ = Formalism.MainNotions.S.umat u := by
    rw [hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hd]
  have hJ : (Formalism.MainNotions.S.umat u)ᴴ * Formalism.REAL.Jm (M.ε τ) * Formalism.MainNotions.S.umat u = Formalism.REAL.Jm (M.ε τ) := u.2
  have hfg : M.fr τ * g = Formalism.MainNotions.S.umat u * M.fr τ := by
    rw [hg, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  have hmem : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    show gᴴ * gramAt D V τ * g = gramAt D V τ
    rw [← M.fr_gram τ]
    calc gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g
        = (M.fr τ * g)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (M.fr τ)ᴴ * ((Formalism.MainNotions.S.umat u)ᴴ * Formalism.REAL.Jm (M.ε τ) * Formalism.MainNotions.S.umat u) * M.fr τ := by
          rw [hfg]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hJ]
  have h1 := hC g hmem
  have he : M.rep τ g = M.σ τ (Formalism.MainNotions.S.umat u) := by rw [DSModel.rep, hu]
  rw [he] at h1
  have hn : Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.umat u)) ≤
      Real.sqrt (Formalism.REAL.hs (M.fr τ)) * hsn g * Real.sqrt (Formalism.REAL.hs (M.fr τ)⁻¹) := by
    rw [← hu]
    exact (hmul _ _).trans (mul_le_mul_of_nonneg_right (hmul _ _) (Real.sqrt_nonneg _))
  have h0 : 0 ≤ hsn g := Real.sqrt_nonneg _
  have hp : 0 ≤ Real.sqrt (Formalism.REAL.hs (M.fr τ)) * Real.sqrt (Formalism.REAL.hs (M.fr τ)⁻¹) := by positivity
  have h2 : 1 + Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.umat u)) ≤ c * (1 + hsn g) := by rw [hc]; nlinarith
  have h3 : wt u ≤ c ^ (2 * V.rank ^ 2 + 1) * (1 + hsn g) ^ (2 * V.rank ^ 2 + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 _
  calc _ ≤ ‖⟪v, M.σ τ (Formalism.MainNotions.S.umat u) a⟫_ℂ‖ * (c ^ (2 * V.rank ^ 2 + 1) * (1 + hsn g) ^ (2 * V.rank ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = c ^ (2 * V.rank ^ 2 + 1) * (‖⟪v, M.σ τ (Formalism.MainNotions.S.umat u) a⟫_ℂ‖ * (1 + hsn g) ^ (2 * V.rank ^ 2 + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

theorem fibre_integral_eq_zero : ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (v a : ∀ τ, M.H τ), (∀ τ, DecayAt M τ (v τ) (v τ) (2 * V.rank ^ 2 + 1)) → (∀ τ, DecayAt M τ (v τ) (a τ) (2 * V.rank ^ 2 + 1)) →
    ∀ (τ : D.what₂.Tau) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∃ P Q : Subgroup (NI V C), IsClosed (P : Set (NI V C)) ∧ IsClosed (Q : Set (NI V C)) ∧
      (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) ∧ (∀ h, ∃ p ∈ P, ∃ q ∈ Q, h = p * q) ∧ (∀ h, h ∈ P → h ∈ Q → h = 1) ∧
      ∀ ν : Measure P, ν.IsHaarMeasure → ∀ q ∈ Q, ∀ x y : GA D V,
        ∫ p, coef θ M K v a (x * (((p : NI V C) * q : NI V C) : GA D V) * y) ∂ν = 0 := by
  intro D θ hθ V S M K v a hv ha τ r C hC
  refine ⟨atP θ V C τ, offP θ V C τ, (L_closed θ hθ V C τ).1, (L_closed θ hθ V C τ).2, (L_comm θ hθ V C τ).1,
    L_decomp θ hθ V C hC τ, (L_comm θ hθ V C τ).2, ?_⟩
  intro ν hν q hq x y
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.REAL.UJ (M.ε τ)) := ⟨rfl⟩
  obtain ⟨E, hE⟩ := L_hom θ hθ V S M τ
  obtain ⟨W, hW, hemb, hrange⟩ := L_emb θ hθ V S M τ C hC E hE
  obtain ⟨R, hR⟩ := L_factor θ hθ V S M K v a τ C q hq x y
  let ι : atP θ V C τ →* Formalism.REAL.UJ (M.ε τ) := E.comp ((NI V C).subtype.comp (atP θ V C τ).subtype)
  have hι : Topology.IsClosedEmbedding ι := hemb
  have hmap := isHaarSub_map_closedEmb ι hι ⊤ isClosed_univ ν (isHaarSub_top ν)
  have hr : (((⊤ : Subgroup (atP θ V C τ)).map ι : Subgroup _) : Set _) = GlobalTheory.Dec.NW (M.ε τ) W := by
    rw [← MonoidHom.range_eq_map, MonoidHom.coe_range]
    exact hrange
  rw [hr] at hmap
  have hsq : GlobalTheory.Dec.IsSqIntIrr (M.ε τ) (M.σ τ) := by
    have hDS := M.ds τ
    exact ⟨hDS.1, hDS.2.1, hDS.2.2.1, hDS.2.2.2.1, hDS.2.2.2.2.1⟩
  have h0 := integral_coef_eq_zero V.rank (M.ε τ) (M.H τ) (M.σ τ) hsq (v τ) (a τ)
    (decays_of_decayAt M τ _ _ (hv τ)) (decays_of_decayAt M τ _ _ (ha τ)) W hW (ν.map ι) hmap (E x) (E y)
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have key : ∀ p : atP θ V C τ, coef θ M K v a (x * (((p : NI V C) * q : NI V C) : GA D V) * y) =
      ⟪v τ, M.σ τ (Formalism.MainNotions.S.umat (E x * ι p * E y)) (a τ)⟫_ℂ * R := by
    intro p
    rw [hR p p.2]
    congr 2
    show M.σ τ (M.fr τ * _ * (M.fr τ)⁻¹) (a τ) = M.σ τ _ (a τ)
    congr 2
    change M.fr τ * _ * (M.fr τ)⁻¹ = Formalism.MainNotions.S.umat (E x) * Formalism.MainNotions.S.umat (E ((p : NI V C) : GA D V)) * Formalism.MainNotions.S.umat (E y)
    rw [hE, hE, hE]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  simp_rw [key]
  have hint := hι.measurableEmbedding.integral_map (μ := ν)
    (fun m => ⟪v τ, M.σ τ (Formalism.MainNotions.S.umat (E x * m * E y)) (a τ)⟫_ℂ)
  rw [integral_mul_const, ← hint, h0, zero_mul]

end UpperTheory.Lit.Cusp
end
end
end
