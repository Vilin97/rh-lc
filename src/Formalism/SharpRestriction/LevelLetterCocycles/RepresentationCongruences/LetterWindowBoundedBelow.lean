module

public import Formalism.SharpRestriction.LevelLetterCocycles.AdmBoundsBOfAdm
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcGamLiftCore
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
public import Formalism.SharpRestriction.LevelLetterCocycles.PsCoprimeOf
public import Formalism.SharpRestriction.LevelLetterCocycles.KillerLevCoreOf
public import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible
public import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfRestriction
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
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeMembershipPolynomialGamma
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SectionInIdealOfLevels
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.GammaLiftAlongArc

section

@[expose] public section

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.UnusedSlot80.UnivF

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem gamma_lift_along_arc [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W)
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (hS : Formalism.MainNotions.UnusedSlot80.KL.PsStable W)
    (hP : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : 5 ≤ PD.p) (A : ArcP n) (hA : A.OK) (c : ZMod n) (hc : c ∈ A.cuts)
    (e : ℕ) (hje : A.j ≤ e) (hel : e ≤ A.len c) (T : LocLat G Qp LL O) (hT : Win W A T)
    (d : ℕ) (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hhor : IsHor W T (c - ((A.len c : ℕ) : ZMod n)) b sol)
    (f : Fin d → W.EE)
    (hf : ∀ k, InFr W (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) 1
      (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) (f k))
    (hinv : InvNL W T (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e
      (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) b f) :
    ∃ u, InI W T (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) u ∧
      InFP W T (c - ((A.len c : ℕ) : ZMod n)) e 1
        (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e • u) ∧
      RepVV W T (c - ((A.len c : ℕ) : ZMod n)) e (A.M PD.p)
        (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) b sol u
        (fun k => lE W (A.σ PD.p) * f k) := by
  have hπ := Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W
  have hAC := (hArc hCA h5 A hA c hc e hje hel).2 T hT
  set c' := c - ((A.len c : ℕ) : ZMod n) with hc'
  set a := c' + (e : ZMod n) with ha
  set Λ := abelian₂ W A a e with hΛdef
  obtain ⟨hP1, hP2, -, hF⟩ := hAC
  obtain ⟨-, -, hlift, -, hNL, hzero, -⟩ := hF d b sol hhor
  have hΛmem : Λ ∈ W.AΔ := lam_mem W A a e
  obtain ⟨u, huP, huR⟩ := hlift f hf
  obtain ⟨p0, hp0, hup0⟩ := huP
  rw [one_smul] at hup0
  have hlet : InLet W T a u := by
    show (letE a : LetA O n) • u = u
    refine lam_cancel W hR A a e T ?_
    rw [smul_comm, hup0]
    exact Relay2.Pp_letter W T c' e p0 hp0
  have hΔ : IsΔ W T u := by
    intro δ hδ
    refine lam_cancel W hR A a e T ?_
    have h1 : W.γD T δ (Λ • u) = Λ • W.γD T δ u := by
      rw [Formalism.MainNotions.LiftingTheory.frame_γD_smul, hΛmem δ hδ]
    rw [← h1, hup0, Relay2.Pp_Δ W T c' e p0 hp0 δ hδ]
  obtain ⟨w, hw, w', hw', hww, hγΛ⟩ := lam_γ W hS A a e
  obtain ⟨u0, hu0, hγπ⟩ := hP
  have hπΛ : ∃ t, W.γA W.gam (W.π₀ * Λ ^ 2) = t * (W.π₀ * Λ ^ 2) ∧ t ∈ W.AΔ :=
    ⟨u0 * w ^ 2, by rw [map_mul, map_pow, hγπ, hγΛ]; ring, W.AΔ.mul_mem hu0 (W.AΔ.pow_mem hw _)⟩
  have hJJ : ∀ x', Formalism.MainNotions.LiftingTheory.InNΔi W T c' x' →
      InFP W T c' e (W.π₀ * Λ ^ 2) (((W.φD T) ^ e) (W.π₀ ^ A.M PD.p • x')) :=
    fun x' hx' => jj_lam W hR h5 A hA a e T c' hx'
  have hsol : ∀ k, Formalism.MainNotions.LiftingTheory.IsSol W T c' b 0 (sol k) := fun k => (hhor.2 k).1
  have hγu := repVV_γ W hsol hJJ hw hw' hww hγΛ hπΛ huR
  obtain ⟨g, hgNL, hg⟩ := hinv
  obtain ⟨y, hyN, hyR⟩ := hNL g hgNL
  have hπy := repVV_smul W hyR hπ
  have hz := repVV_sub W hinj (repVV_sub W hinj hγu huR) hπy
  have hz0 : (((fun k => W.γE W.gam (lE W (A.σ PD.p) * f k)) - fun k => lE W (A.σ PD.p) * f k) -
      fun k => algebraMap (LetA O n) W.EE W.π₀ * (lE W (A.σ PD.p) * g k)) = 0 := by
    funext k
    simp only [Pi.sub_apply, Pi.zero_apply, map_mul]
    have hl : W.γE W.gam (lE W (A.σ PD.p)) = lE W (A.σ PD.p) := by
      unfold lE; rw [map_pow, map_natCast]
    rw [hl, ← mul_sub, hg k]
    ring
  rw [hz0] at hz
  have hγΛu : InFP W T c' e 1 (Λ • W.γ T u) := by
    have h1 : Λ • W.γ T u = w' • W.γ T (Λ • u) := by
      show _ = w' • W.γD T W.gam (Λ • u)
      rw [Formalism.MainNotions.LiftingTheory.frame_γD_smul, hγΛ, smul_smul, ← mul_assoc, hww, one_mul]
      rfl
    refine ⟨w' • W.γ T p0, Relay2.Pp_smul W T c' _ hw' _ (Relay2.Pp_γ W T c' _ p0 hp0), ?_⟩
    rw [one_smul, h1, hup0]
  have hΛu : InFP W T c' e 1 (Λ • u) := ⟨p0, hp0, by rw [one_smul, hup0]⟩
  have hΛy : InFP W T c' e 1 (Λ • (W.π₀ • y)) := by
    rw [smul_comm]
    exact Relay2.inMultiple_smul W T c' _ _ hπ (hP2 y hyN)
  have hΛz : InFP W T c' e 1 (Λ • (W.γ T u - u - W.π₀ • y)) := by
    rw [smul_sub, smul_sub]
    exact Relay2.inMultiple_sub W T c' _ _ (Relay2.inMultiple_sub W T c' _ _ hγΛu hΛu) hΛy
  obtain ⟨p1, hp1, hzp⟩ := hzero _ hΛz hz
  obtain ⟨y2, hy2, hy2c, hy2e⟩ := hP1 p1 hp1
  obtain ⟨y1, hy1, hy1c, hy1e⟩ := hyN
  rw [one_smul] at hy2e hy1e
  refine ⟨u, ⟨hlet, hΔ, y1 + y2, (W.NΔ T).add_mem hy1 hy2, ?_, ?_⟩, ⟨p0, hp0, by rw [one_smul, hup0]⟩,
    huR⟩
  · rw [smul_add, hy1c, hy2c]
  · have : W.γ T u - u = (W.γ T u - u - W.π₀ • y) + W.π₀ • y := by abel
    rw [this, hzp, mul_smul, hy2e, hy1e, smul_add, add_comm]

end Core

end Formalism.MainNotions.N.Ln17
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LetterWindowBoundedBelow

section

@[expose] public section

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.UnusedSlot80.UnivF

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem letter_window_bounded_below (ty : Formalism.MainNotions.LocalTheoryWindows.LT) (G₁ S₁ η₁ : ℕ) :
    ∃ U : ℤ, ∀ x ∈ ty.win G₁ S₁ η₁, U ≤ x := by
  cases ty with
  | thin => exact ⟨-(G₁ : ℤ), fun x hx => hx.1⟩
  | up b =>
    refine ⟨-(η₁ : ℤ), fun x hx => ?_⟩
    rcases hx with hx | hx
    · have := hx.1; omega
    · exact hx.1
  | down b =>
    refine ⟨-(b : ℤ) - S₁ - η₁, fun x hx => ?_⟩
    rcases hx with hx | hx
    · have := hx.1; omega
    · have := hx.1; omega

theorem arc_gamma_lift [IsDomain O] [FiniteDimensional Qp LL]
    (hinj : Function.Injective (algebraMap O LL)) (hArc : ArcCore W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hFL : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcFilLowCore W) : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcGamLiftCore W := by
  intro hCA h5 A hA c hc e hje hel T hT d b sol hhor g hg hyp
  have hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W :=
    (Formalism.MainNotions.LiftingTheory.uniformizer_ring_and_module_clauses W hP9 hCA W.one (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1
  have : NeZero n := ⟨by
    rw [W.n_eq]
    have := PD.finK₀
    exact Module.finrank_pos.ne'⟩
  have hS := Formalism.MainNotions.UnusedSlot80.KF.psStable_of W hR
  have hC := Formalism.MainNotions.UnusedSlot80.KF.psCoprime_of W hR
  obtain ⟨t, htΔ, hγπ⟩ := Formalism.MainNotions.LiftingTheory.gamma_uniformizer_eq_mul_unit' W hR
  have hP : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u :=
    ⟨_, W.AΔ.add_mem (W.AΔ.algebraMap_mem _) (W.AΔ.mul_mem hR.1 htΔ), hγπ⟩
  obtain ⟨h, hγ, hhFr, hlev⟩ := hyp
  refine gamma_lift_along_arc W hinj hArc hR hS hP hCA h5 A hA c hc e hje hel T hT d b sol hhor g hg
    ⟨h, ⟨hhFr, ?_⟩, hγ⟩
  rcases Nat.eq_zero_or_pos e with h0 | hpos
  · subst h0
    refine ⟨0, d, h, fun i => Pi.single i 1, fun _ _ => 0,
      fun i => ⟨?_, fun s hs => absurd hs (Nat.not_lt_zero s)⟩, fun k => ?_⟩
    · have := hhFr i
      simpa [InId, abelian₂] using this
    · rw [Finset.sum_eq_single k (fun i _ hik => by simp [hik.symm]) (by simp)]
      simp [lE]
  · refine section_in_ideal_of_levels W hR hC T _ e hpos b h hlev fun t' ht' => ?_
    obtain ⟨U, hU⟩ := letter_window_bounded_below
      (A.ty ((c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) - (t' : ZMod n))) A.G₀ A.S A.η
    exact ⟨U, fun u hu c₀ =>
      (hFL hCA h5 A hA c hc e hje hel T hT d b sol hhor c₀ t' ht').1 u fun x hx => hu.trans (hU x hx)⟩

end Core

section Record

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)

theorem arc_gamma_lift_at {CR CA CB CK : ℝ} (hU : AdmBoundsB D HW F Cm CR CA CB CK)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL)
    (hFL : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcFilLowCore ((HW l).W K 1 LL hG)) :
    Formalism.MainNotions.N.FrobeniusPowerSeries.ArcGamLiftCore ((HW l).W K 1 LL hG) := by
  intro hCA h5
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have h5' : 5 ≤ l := hpl ▸ h5
  have hFD : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact arc_gamma_lift _ Subtype.val_injective (hU.a12 l K LL hG hK h5').1 (hU.p9 l K 1 LL hG) hFL
    hCA h5

end Record

end Formalism.MainNotions.N.Ln17
end
end
end
