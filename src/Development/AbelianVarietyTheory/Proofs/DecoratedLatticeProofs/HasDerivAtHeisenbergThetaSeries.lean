module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSummableBoundSchwartzMajorantRationalTransStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixClosedDerivLinearAdd

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

namespace GlobalTheory.SchwartzDeriv

section General

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]

theorem addHom_eq_zero (F : Type) [DivisionRing F] [CharZero F] [Module F X] (h : ℝ →+ X) (hc : Continuous h) {b : ℝ}
    (hb : b ≠ 0) (h0 : h b = 0) (t : ℝ) : h t = 0 := by

  have hq : ∀ q : ℚ, h ((q : ℝ) * b) = 0 := by
    intro q
    have hn : (q.den : F) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    have hnum : (q.den : ℝ) * ((q : ℝ) * b) = (q.num : ℝ) * b := by
      rw [← mul_assoc]
      congr 1
      have : ((q.den : ℚ) * q : ℚ) = q.num := by rw [mul_comm]; exact Rat.mul_den_eq_num q
      exact_mod_cast this
    have h1 : q.den • h ((q : ℝ) * b) = 0 := by
      rw [← map_nsmul, nsmul_eq_mul, hnum, ← zsmul_eq_mul, map_zsmul, h0, smul_zero]
    have h2 : h ((q : ℝ) * b) = (q.den : F)⁻¹ • ((q.den : F) • h ((q : ℝ) * b)) := by
      rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
    rw [h2, Nat.cast_smul_eq_nsmul, h1, smul_zero]
  have hsurj : Function.Surjective fun y : ℝ => y * b := fun y => ⟨y / b, div_mul_cancel₀ y hb⟩
  have hdense : DenseRange fun q : ℚ => (q : ℝ) * b :=
    hsurj.denseRange.comp Rat.denseRange_cast (continuous_mul_const b)
  exact hdense.induction_on t (isClosed_eq hc continuous_const) hq

theorem hasDerivAt_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : SchwartzMap E ℂ) (c s : E) :
    HasDerivAt (fun t : ℝ => G (s + t • c)) ((LineDeriv.lineDerivOp c G : SchwartzMap E ℂ) s) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => s + t • c) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const c).const_add s
  have h2 : HasFDerivAt (G : E → ℂ) (fderiv ℝ (G : E → ℂ) (s + (0 : ℝ) • c)) (s + (0 : ℝ) • c) :=
    G.differentiableAt.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  simp only [zero_smul, add_zero] at h3
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  exact h3

theorem exists_schwartz_deriv (F : Type) [DivisionRing F] [CharZero F] [Module F X] (P : X → Prop)
    (hP : ∀ a b, P a → P b → P (a + b)) (φ : X → ℂ)
    (hφ : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ X), (Continuous L ∧ ∀ t, P (L t)) → Function.Injective L →
      ∀ x, ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ t, g t = φ (x + L t))
    (M : ℝ →+ X) (hM : Continuous M) (hMP : ∀ t, P (M t)) {k : ℕ} (L : (Fin k → ℝ) →+ X)
    (hL : Continuous L ∧ ∀ t, P (L t)) (hi : Function.Injective L) (x : X) :
    ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ s, HasDerivAt (fun t : ℝ => φ (x + L s + M t)) (g s) 0 := by
  obtain ⟨hLc, hLP⟩ := hL

  let A : (Fin (k + 1) → ℝ) →+ (Fin k → ℝ) :=
    (LinearMap.funLeft ℝ ℝ (Fin.castSucc : Fin k → Fin (k + 1))).toAddMonoidHom
  let B : (Fin (k + 1) → ℝ) →+ ℝ := Pi.evalAddMonoidHom (fun _ => ℝ) (Fin.last k)
  let L' : (Fin (k + 1) → ℝ) →+ X := L.comp A + M.comp B
  have hA : Continuous A := continuous_pi fun i => continuous_apply _
  have hB : Continuous B := continuous_apply _
  have hL'c : Continuous L' := (hLc.comp hA).add (hM.comp hB)
  have hL'P : ∀ u, P (L' u) := fun u => hP _ _ (hLP _) (hMP _)
  have hL'apply : ∀ u, L' u = L (fun i => u (Fin.castSucc i)) + M (u (Fin.last k)) := fun u => rfl
  by_cases hinj : Function.Injective L'
  ·
    obtain ⟨H, hH⟩ := hφ (k + 1) L' ⟨hL'c, hL'P⟩ hinj x
    let e : Fin (k + 1) → ℝ := Pi.single (Fin.last k) 1
    let j : (Fin k → ℝ) →L[ℝ] (Fin (k + 1) → ℝ) :=
      ContinuousLinearMap.pi (Fin.lastCases (motive := fun _ => (Fin k → ℝ) →L[ℝ] ℝ) 0
        fun i => ContinuousLinearMap.proj i)
    have hj_cs : ∀ s i, j s (Fin.castSucc i) = s i := by intro s i; simp [j]
    have hj_last : ∀ s, j s (Fin.last k) = 0 := by intro s; simp [j]
    have hup : ∃ (n : ℕ) (C : ℝ), ∀ s, ‖s‖ ≤ C * (1 + ‖j s‖) ^ n := by
      refine ⟨1, 1, fun s => ?_⟩
      rw [one_mul, pow_one]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      calc ‖s i‖ = ‖j s (Fin.castSucc i)‖ := by rw [hj_cs]
        _ ≤ ‖j s‖ := norm_le_pi_norm _ _
        _ ≤ 1 + ‖j s‖ := by linarith
    refine ⟨SchwartzMap.compCLM ℝ j.hasTemperateGrowth hup (LineDeriv.lineDerivOp e H), fun s => ?_⟩
    have hd := hasDerivAt_line H e (j s)
    have heq : (fun t : ℝ => H (j s + t • e)) = fun t => φ (x + L s + M t) := by
      funext t
      have e1 : (fun i => (j s + t • e) (Fin.castSucc i)) = s := by
        funext i
        simp [e, hj_cs, Fin.castSucc_ne_last]
      have e2 : (j s + t • e) (Fin.last k) = t := by simp [e, hj_last]
      rw [hH, hL'apply, e1, e2, add_assoc]
    rw [heq] at hd
    exact hd
  ·
    obtain ⟨u, hu, hu0⟩ : ∃ u, L' u = 0 ∧ u ≠ 0 := by
      rw [injective_iff_map_eq_zero] at hinj
      push Not at hinj
      exact hinj
    rw [hL'apply] at hu
    have ht0 : u (Fin.last k) ≠ 0 := by
      intro h
      rw [h, map_zero, add_zero] at hu
      have hs : (fun i => u (Fin.castSucc i)) = 0 := hi (by rw [hu, map_zero])
      apply hu0
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · exact h
      · exact congrFun hs i
    let v : Fin k → ℝ := -((u (Fin.last k))⁻¹ • fun i => u (Fin.castSucc i))
    let Lv : ℝ →+ (Fin k → ℝ) := AddMonoidHom.mk' (fun t => t • v) fun a b => add_smul a b v
    have hMv : ∀ t, M t = L (t • v) := by
      intro t
      have h1 := addHom_eq_zero F (M - L.comp Lv)
        (hM.sub (hLc.comp (continuous_id.smul continuous_const))) ht0 ?_ t
      · simpa [sub_eq_zero, Lv] using h1
      · simp only [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply, Lv, v, smul_neg,
          smul_smul, mul_inv_cancel₀ ht0, one_smul, map_neg, sub_neg_eq_add]
        rw [add_comm]
        exact hu
    obtain ⟨G, hG⟩ := hφ k L ⟨hLc, hLP⟩ hi x
    refine ⟨LineDeriv.lineDerivOp v G, fun s => ?_⟩
    have hd := hasDerivAt_line G v s
    have heq : (fun t : ℝ => G (s + t • v)) = fun t => φ (x + L s + M t) := by
      funext t
      rw [hG, hMv, map_add (f := _), add_assoc]
    rw [heq] at hd
    exact hd

end General

open GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies

variable {D : D7} {m n : ℕ}

theorem isSchwartzBruhat_add {φ φ' : Mx D m n → ℂ} (h : IsSchwartzBruhat φ) (h' : IsSchwartzBruhat φ') :
    IsSchwartzBruhat (φ + φ') := by
  refine { level := ?_, supp := ?_, schwartz := ?_ }
  · obtain ⟨U, hU, hφU⟩ := h.level
    obtain ⟨U', hU', hφU'⟩ := h'.level
    refine ⟨U ⊓ U', ?_, fun u hu hu0 x => ?_⟩
    · change IsOpen ((U : Set (Mx D m n)) ∩ (U' : Set (Mx D m n)))
      exact hU.inter hU'
    · have hu' := AddSubgroup.mem_inf.mp hu
      simp [hφU u hu'.1 hu0 x, hφU' u hu'.2 hu0 x]
  · obtain ⟨K, hK, hφK⟩ := h.supp
    obtain ⟨K', hK', hφK'⟩ := h'.supp
    refine ⟨K ∪ K', hK.union hK', fun x hx => ?_⟩
    by_cases h1 : φ x = 0
    · have h2 : φ' x ≠ 0 := by simpa [h1] using hx
      exact Or.inr (hφK' x h2)
    · exact Or.inl (hφK x h1)
  · intro k L hL hi x
    obtain ⟨g, hg⟩ := h.schwartz k L hL hi x
    obtain ⟨g', hg'⟩ := h'.schwartz k L hL hi x
    exact ⟨g + g', fun t => by simp [hg, hg']⟩

theorem isSchwartzBruhat_linear_mul {φ : Mx D m n → ℂ} (h : IsSchwartzBruhat φ) (ℓ : Mx D m n →+ ℂ) (hc : Continuous ℓ)
    (h0 : ∀ u : Mx D m n, u.map (infPart D) = 0 → ℓ u = 0) : IsSchwartzBruhat fun x => ℓ x * φ x := by
  refine { level := ?_, supp := ?_, schwartz := ?_ }
  · obtain ⟨U, hU, hφU⟩ := h.level
    refine ⟨U, hU, fun u hu hu0 x => ?_⟩
    show ℓ (x + u) * φ (x + u) = ℓ x * φ x
    rw [map_add (f := _), h0 u hu0, add_zero, hφU u hu hu0 x]
  · obtain ⟨K, hK, hφK⟩ := h.supp
    exact ⟨K, hK, fun x hx => hφK x (right_ne_zero_of_mul hx)⟩
  · intro k L hL hi x
    obtain ⟨g, hg⟩ := h.schwartz k L hL hi x

    let A : (Fin k → ℝ) →L[ℝ] ℂ := (ℓ.comp L).toRealLinearMap (hc.comp hL.1)
    have ht : (fun t => ℓ x + A t).HasTemperateGrowth := by fun_prop
    refine ⟨SchwartzMap.smulLeftCLM ℂ (fun t => ℓ x + A t) g, fun t => ?_⟩
    rw [SchwartzMap.smulLeftCLM_apply_apply ht, hg]
    simp [A, smul_eq_mul]

theorem exists_isSchwartzBruhat_deriv {φ : Mx D m n → ℂ} (h : IsSchwartzBruhat φ) (M : ℝ →+ Mx D m n) (hM : Continuous M)
    (hM0 : ∀ t, (M t).map (finPart D) = 0) :
    ∃ φ', IsSchwartzBruhat φ' ∧ ∀ x, HasDerivAt (fun t : ℝ => φ (x + M t)) (φ' x) 0 := by
  have : T2Space (Mx D m n) := (lattice_Mx D m n).2.2.2.1
  have hP : ∀ a b : Mx D m n, a.map (finPart D) = 0 → b.map (finPart D) = 0 → (a + b).map (finPart D) = 0 := by
    intro a b ha hb
    rw [Matrix.map_add _ (map_add _), ha, hb, add_zero]

  have hdiff : ∀ y, HasDerivAt (fun t : ℝ => φ (y + M t)) (deriv (fun t : ℝ => φ (y + M t)) 0) 0 := by
    intro y
    obtain ⟨g, hg⟩ := exists_schwartz_deriv D.host.F (fun u : Mx D m n => u.map (finPart D) = 0) hP φ h.schwartz
      M hM hM0 (k := 0) 0 ⟨continuous_const, fun t => by simp⟩ (fun a b _ => Subsingleton.elim a b) y
    have hg0 := hg 0
    simp only [AddMonoidHom.zero_apply, add_zero] at hg0
    exact hg0.differentiableAt.hasDerivAt
  refine ⟨fun x => deriv (fun t : ℝ => φ (x + M t)) 0, ⟨?_, ?_, ?_⟩, hdiff⟩
  · obtain ⟨U, hU, hφU⟩ := h.level
    refine ⟨U, hU, fun u hu hu0 x => ?_⟩
    simp only [add_right_comm x u, hφU u hu hu0]
  · obtain ⟨K, hK, hφK⟩ := h.supp
    refine ⟨K, hK, fun x hx => ?_⟩
    by_contra hxK
    apply hx
    have hz : (fun t : ℝ => φ (x + M t)) = fun _ => 0 := by
      funext t
      by_contra ht
      apply hxK
      have := hφK _ ht
      rwa [Matrix.map_add _ (map_add _), hM0, add_zero] at this
    simp only [hz, deriv_const]
  · intro k L hL hi x
    obtain ⟨g, hg⟩ := exists_schwartz_deriv D.host.F (fun u : Mx D m n => u.map (finPart D) = 0) hP φ h.schwartz
      M hM hM0 L hL hi x
    exact ⟨g, fun s => (hg s).deriv.symm⟩

theorem isSchwartzBruhat_closed : ∀ (D : D7) (m n : ℕ) (φ : Mx D m n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → (∀ M : ℝ →+ Mx D m n, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ φ', GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' ∧ ∀ x, HasDerivAt (fun t : ℝ => φ (x + M t)) (φ' x) 0) ∧ (∀ ℓ : Mx D m n →+ ℂ, Continuous ℓ → (∀ u : Mx D m n, u.map (infPart D) = 0 → ℓ u = 0) → GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat fun x => ℓ x * φ x) ∧ ∀ φ', GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' → GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat (φ + φ') := fun _ _ _ _ hφ =>
  ⟨fun M hM hM0 => exists_isSchwartzBruhat_deriv hφ M hM hM0, fun ℓ hc h0 => isSchwartzBruhat_linear_mul hφ ℓ hc h0,
    fun _ h' => isSchwartzBruhat_add hφ h'⟩

end GlobalTheory.SchwartzDeriv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixClosedDerivLinearAddStatement

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff


theorem _root_.GlobalTheory.T.isSchwartzBruhatAdelicMatrix_closed_deriv_linear_add : ∀ (D : D7) (m n : ℕ) (φ : Mx D m n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → (∀ M : ℝ →+ Mx D m n, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ φ', GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' ∧ ∀ x, HasDerivAt (fun t : ℝ => φ (x + M t)) (φ' x) 0) ∧ (∀ ℓ : Mx D m n →+ ℂ, Continuous ℓ → (∀ u : Mx D m n, u.map (infPart D) = 0 → ℓ u = 0) → GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat fun x => ℓ x * φ x) ∧ ∀ φ', GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' → GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat (φ + φ') := by
  first | exact @GlobalTheory.SchwartzDeriv.isSchwartzBruhat_closed | exact GlobalTheory.SchwartzDeriv.isSchwartzBruhat_closed | (intros; apply GlobalTheory.SchwartzDeriv.isSchwartzBruhat_closed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtHeisenbergThetaSeries

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

noncomputable section

namespace GlobalTheory.Core.Rk.OntoDer

theorem hasDerivAt_term {G : Type} [AddCommGroup G] (a : ℝ →+ G) (p : G →+ ℂ) (κ : ℂ) (hκ : ∀ t : ℝ, p (a t) = t * κ)
    (φ φ₁ : G → ℂ) (hφ : ∀ x, HasDerivAt (fun t : ℝ => φ (x + a t)) (φ₁ x) 0) (u : G) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (t * p (a t) + t * p u + t * p u) * φ (u + a t))
      (Complex.exp (s * p (a s) + s * p u + s * p u) * ((p + p) (u + a s) * φ (u + a s) + φ₁ (u + a s))) s := by
  have h1 : HasDerivAt (fun t : ℝ => φ (u + a t)) (φ₁ (u + a s)) s := by
    have h := hφ (u + a s)
    rw [← sub_self s] at h
    have h' := HasDerivAt.comp_sub_const s s h
    refine h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show φ (u + a t) = φ (u + a s + a (t - s))
    rw [map_sub, add_assoc, add_sub_cancel]
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
  have h2 := (((h0.mul (h0.mul_const κ)).add (h0.mul_const (p u))).add (h0.mul_const (p u))).cexp
  have h3 := h2.mul h1
  simp only [hκ]
  refine h3.congr_deriv ?_
  simp only [AddMonoidHom.add_apply, map_add (f := _), hκ, Pi.add_apply, Pi.mul_apply]
  ring

variable {D : D7}

theorem two_halves (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

theorem phase_identity {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x y a b ξ : Mx D T.rank ρ) :
    symplOH S T (d.extX T x + d.extY T y) (d.extX T a + d.extY T b) +
        (-(symplOH S T (d.extX T (x + a)) (d.extY T (y + b)))) + symplO S T (d.extX T (x + a + ξ)) (d.extY T (y + b)) =
      -(symplOH S T (d.extX T x) (d.extY T y)) + symplO S T (d.extX T (x + ξ)) (d.extY T y) +
        (symplOH S T (d.extX T a) (d.extY T b) + symplOH S T (d.extX T (x + ξ)) (d.extY T b) +
          symplOH S T (d.extX T (x + ξ)) (d.extY T b)) := by
  simp only [two_halves, map_add (f := _), GlobalTheory.WeilVacMove.symplOH_add_left, GlobalTheory.WeilVacMove.symplOH_add_right,
    HypDec.symplOH_extX_extX, HypDec.symplOH_extY_extY,
    GlobalTheory.WeilVacMove.symplOH_skew S T (d.extX T a) (d.extY T y)]
  ring

theorem eq_ext (A B : HSp D) (w : WO (dblSp A) B) :
    w = (dblDec A).extX B (HMul.hMul w (dblDec A).jX) + (dblDec A).extY B (HMul.hMul w (dblDec A).jY) := by
  have h0 : HMul.hMul (dblDec A).j0 (dblDec A).p0 = (0 : Mx D (dblSp A).rank (dblSp A).rank) := by
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => Fin.elim0 k
  have h := (dblDec A).sum_eq_one
  rw [h0, add_zero] at h
  rw [HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, h, Matrix.mul_one]

def mulLine {m n k : ℕ} (M : ℝ →+ Mx D m n) (j : Mx D n k) : ℝ →+ Mx D m k where
  toFun t := HMul.hMul (M t) j
  map_zero' := by rw [map_zero, Matrix.zero_mul]
  map_add' s t := by rw [map_add (f := _), Matrix.add_mul]

theorem continuous_mulLine {m n k : ℕ} {M : ℝ →+ Mx D m n} (hM : Continuous M) (j : Mx D n k) :
    Continuous (mulLine M j) := hM.matrix_mul continuous_const

theorem map_mul_zero {m n k : ℕ} {R : Type} [CommRing R] (q : AE D →+* R) {u : Mx D m n} (hu : u.map q = 0)
    (j : Mx D n k) : (HMul.hMul u j : Mx D m k).map q = 0 := by
  rw [Matrix.map_mul, hu, Matrix.zero_mul]

theorem exists_summable_bound {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} {φ : Mx D m n → ℂ}
    (hφ : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ) {Q : Set (Mx D m n)} (hQ : IsCompact Q) :
    ∃ b : Matrix (Fin m) (Fin n) D.host.E → ℝ, Summable b ∧ ∀ x ∈ Q, ∀ ξ, ‖φ (x + rat ξ)‖ ≤ b ξ := by
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ m n
  obtain ⟨-, K, hK, hC⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ m n φ hφ
  obtain ⟨C, hC⟩ := hC N
  obtain ⟨b, hb, hb'⟩ := hN K Q hK hQ
  refine ⟨fun ξ => |C| * b ξ, hb.mul_left _, fun x hx ξ => (hC _).trans ?_⟩
  exact mul_le_mul (le_abs_self C) (hb' x hx ξ) (GlobalTheory.Unf.maj_nonneg _ _ _ _) (abs_nonneg C)



theorem hasDerivAt_heisO_thetaSeries : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (φ : Mx D B.rank A.rank → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → ∀ f : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ (HMul.hMul w (dblDec A).jX + rat ξ)) → ∀ M : ℝ →+ WO (dblSp A) B, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ φ' : Mx D B.rank A.rank → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' ∧ ∀ f' : WO (dblSp A) B → ℂ, (∀ w : WO (dblSp A) B, f' w = ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ' (HMul.hMul w (dblDec A).jX + rat ξ)) → ∀ w, HasDerivAt (fun t : ℝ => heisO ψ (dblSp A) B (M t) f w) (f' w) 0 := by
  intro D ψ hψ A B φ hφ f hf M hM hM0
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
  have hn : ∀ z, ‖ψ z‖ = 1 := hψ.1.2.1
  haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  let d := dblDec A
  let a : ℝ →+ Mx D B.rank A.rank := mulLine M d.jX
  let b : ℝ →+ Mx D B.rank A.rank := mulLine M d.jY
  let L : ℝ →+ WO (dblSp A) B := mulLine b d.pY
  have ha : Continuous a := continuous_mulLine hM _
  have hL : Continuous L := continuous_mulLine (continuous_mulLine hM _) _
  have ha0 : ∀ t, (a t).map (finPart D) = 0 := fun t => map_mul_zero _ (hM0 t) _
  have hL0 : ∀ t, (L t).map (finPart D) = 0 := fun t => map_mul_zero _ (map_mul_zero _ (hM0 t) _) _
  let p : Mx D B.rank A.rank →+ ℂ := (GlobalTheory.WeilVacMove.phase lam (dblSp A) B (L 1)).comp (d.extX B)
  have hX : Continuous (d.extX B) := continuous_id.matrix_mul continuous_const
  have hp : Continuous p := hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH (dblSp A) B hX continuous_const)
  have hp0 : ∀ u : Mx D B.rank A.rank, u.map (infPart D) = 0 → p u = 0 := fun u hu => by
    show lam (symplOH (dblSp A) B (d.extX B u) (L 1)) = 0
    rw [(GlobalTheory.WeilVacMove.symplOH_fin_real (dblSp A) B (d.extX B u) (L 1) (map_mul_zero _ hu _) (hL0 1)).1, map_zero]
  have hψp : ∀ (u : Mx D B.rank A.rank) (t : ℝ),
      ψ (symplOH (dblSp A) B (d.extX B u) (d.extY B (b t))) = Complex.exp (t * p u) := fun u t =>
    GlobalTheory.WeilVacMove.psi_sympl_line hl hlam hL hL0 (d.extX B u) t
  have hκ : ∀ t : ℝ, p (a t) = t * p (a 1) := fun t =>
    GlobalTheory.WeilVacMove.additive_real (p.comp a) (hp.comp ha) t
  obtain ⟨hd, hm, hadd⟩ := GlobalTheory.T.isSchwartzBruhatAdelicMatrix_closed_deriv_linear_add D _ _ φ hφ
  obtain ⟨φ₁, hφ₁, hder⟩ := hd a ha ha0
  have hℓ := hm (p + p) (hp.add hp) fun u hu => by rw [AddMonoidHom.add_apply, hp0 u hu, add_zero]
  have hφ' := (GlobalTheory.T.isSchwartzBruhatAdelicMatrix_closed_deriv_linear_add D _ _ _ hℓ).2.2 φ₁ hφ₁
  refine ⟨_, hφ', fun f' hf' w => ?_⟩
  set φ' : Mx D B.rank A.rank → ℂ := (fun x => (p + p) x * φ x) + φ₁ with hφ'def
  let x : Mx D B.rank A.rank := HMul.hMul w d.jX
  let y : Mx D B.rank A.rank := HMul.hMul w d.jY
  let c : Matrix (Fin B.rank) (Fin A.rank) D.host.E → ℂ := fun ξ =>
    ψ (symplO (dblSp A) B (d.extX B (x + rat ξ)) (d.extY B y))
  let e : Matrix (Fin B.rank) (Fin A.rank) D.host.E → ℝ → ℂ := fun ξ t =>
    Complex.exp (t * p (a t) + t * p (x + rat ξ) + t * p (x + rat ξ))
  have he : ∀ ξ t, e ξ t = ψ (symplOH (dblSp A) B (d.extX B (a t)) (d.extY B (b t)) +
      symplOH (dblSp A) B (d.extX B (x + rat ξ)) (d.extY B (b t)) +
      symplOH (dblSp A) B (d.extX B (x + rat ξ)) (d.extY B (b t))) := fun ξ t => by
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψp, hψp, ← Complex.exp_add, ← Complex.exp_add]
  have he0 : ∀ ξ, e ξ 0 = 1 := fun ξ => by simp [e]
  have hform : ∀ t, heisO ψ (dblSp A) B (M t) f w =
      ψ (-(symplOH (dblSp A) B (d.extX B x) (d.extY B y))) * ∑' ξ, c ξ * (e ξ t * φ (x + rat ξ + a t)) := by
    intro t
    have e1 : HMul.hMul (w + M t) (dblDec A).jX = x + a t := Matrix.add_mul _ _ _
    have e2 : HMul.hMul (w + M t) (dblDec A).jY = y + b t := Matrix.add_mul _ _ _
    have e3 : symplOH (dblSp A) B w (M t) =
        symplOH (dblSp A) B (d.extX B x + d.extY B y) (d.extX B (a t) + d.extY B (b t)) :=
      congrArg₂ (symplOH (dblSp A) B) (eq_ext A B w) (eq_ext A B (M t))
    rw [heisO, hf, e1, e2, e3, ← mul_assoc, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun ξ => ?_
    rw [he, add_right_comm x (rat ξ) (a t), ← mul_assoc, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, phase_identity]
  have hQ : IsCompact ((fun t : ℝ => x + a t) '' Set.Icc (-1) 1) :=
    isCompact_Icc.image (continuous_const.add ha)
  obtain ⟨u, hu, hu'⟩ := exists_summable_bound hθ hφ' hQ
  obtain ⟨v, hv, hv'⟩ := exists_summable_bound hθ hφ (isCompact_singleton (x := x))
  have key := hasDerivAt_tsum_of_isPreconnected (t := Set.Ioo (-1 : ℝ) 1) (y₀ := (0 : ℝ)) (y := (0 : ℝ))
    (g := fun ξ t => c ξ * (e ξ t * φ (x + rat ξ + a t)))
    (g' := fun ξ t => c ξ * (e ξ t * φ' (x + rat ξ + a t))) hu isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => (hasDerivAt_term a p _ hκ φ φ₁ hder (x + rat ξ) t).const_mul (c ξ))
    (fun ξ t ht => by
      rw [norm_mul, norm_mul, he, hn, hn, one_mul, one_mul, add_right_comm]
      exact hu' _ ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩ ξ)
    (by norm_num)
    (Summable.of_norm_bounded hv fun ξ => by
      rw [norm_mul, norm_mul, he, hn, hn, one_mul, one_mul, map_zero, add_zero]
      exact hv' x rfl ξ)
    (by norm_num)
  simp only [he0, map_zero, add_zero, one_mul] at key
  rw [hf', funext hform]
  exact key.const_mul _

end GlobalTheory.Core.Rk.OntoDer

end
end
end
