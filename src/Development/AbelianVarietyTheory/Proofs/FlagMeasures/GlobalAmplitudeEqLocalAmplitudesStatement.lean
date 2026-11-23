module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GoodOfHpEqOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianAmplitudeMassProductStructureStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GoodOfHpEqOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDatumOfTermInMovedLatticeOrbitStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTermLatticeIsGlobalTermPhaseStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOrbitsHeightsAmplitudesInCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumOrbitNormaliser
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodEqProdMulFinprodIte

section

@[expose] public section

namespace GlobalTheory.FinprodProdMulIte


open Classical in
theorem finprod_eq_prod_mul_finprod_ite {ι : Type} (S₁ : Finset ι) (f g : ι → ℂ)
    (hf : (Function.mulSupport f).Finite) (hfg : ∀ p, p ∉ S₁ → f p = g p) :
    ∏ᶠ p, f p = (∏ p ∈ S₁, f p) * ∏ᶠ p, (if p ∈ S₁ then (1 : ℂ) else g p) := by
  have hsub₁ : Function.mulSupport (fun p => if p ∈ S₁ then f p else (1 : ℂ)) ⊆ (S₁ : Set ι) := by
    intro p hp
    by_contra h
    have h' : p ∉ S₁ := h
    exact hp (by simp [h'])
  have hsub₂ : Function.mulSupport (fun p => if p ∈ S₁ then (1 : ℂ) else g p)
      ⊆ Function.mulSupport f := by
    intro p hp
    by_cases h : p ∈ S₁
    · exact absurd (by simp [h]) hp
    · intro h1
      exact hp (by simp [h, ← hfg p h, h1])
  have h₁ : ∏ᶠ p, (if p ∈ S₁ then f p else (1 : ℂ)) = ∏ p ∈ S₁, f p := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub₁]
    exact Finset.prod_congr rfl fun p hp => by simp [hp]
  rw [← h₁, ← finprod_mul_distrib (S₁.finite_toSet.subset hsub₁) (hf.subset hsub₂)]
  refine finprod_congr fun p => ?_
  by_cases h : p ∈ S₁
  · simp [h]
  · simp [h, hfg p h]

end GlobalTheory.FinprodProdMulIte
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeExpansionOverFinitePlaces

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.DefectPhase

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ} (G : GFrames A r k)

theorem amp_eq_finsum (d : G.Dat) (hT : {o : Quot G.LRel | G.IsTerm d o.out}.Finite) (Q : G.Lt → Prop) :
    G.amp d Q = ∑ o ∈ hT.toFinset, if Q o.out then (G.mu o.out : ℂ) * G.om d o.out else 0 := by
  unfold GFrames.amp
  rw [tsum_eq_sum (s := hT.toFinset)]
  · refine Finset.sum_congr rfl fun o ho => ?_
    have : G.IsTerm d o.out := hT.mem_toFinset.1 ho
    simp only [this, true_and]
  · intro o ho
    have : ¬ G.IsTerm d o.out := fun h => ho (hT.mem_toFinset.2 h)
    simp only [this, false_and, if_false]

theorem finprod_split' {ι : Type} (S1 : Finset ι) (f g : ι → ℂ) (hf : (Function.mulSupport f).Finite)
    (hfg : ∀ p ∉ S1, f p = g p) :
    ∏ᶠ p, f p = (∏ p ∈ S1, f p) * ∏ᶠ p, (if p ∈ S1 then 1 else g p) := by
  first
  | exact @_root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite
  | exact _root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite
  | (apply _root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinprodProdMulIte.finprod_eq_prod_mul_finprod_ite ..)

theorem norm_finprod_eq_one {ι : Type} (g : ι → ℂ) (hg : (Function.mulSupport g).Finite)
    (h1 : ∀ p, ‖g p‖ = 1) : ‖∏ᶠ p, g p‖ = 1 := by
  rw [finprod_eq_prod_of_mulSupport_subset (s := hg.toFinset) g (fun p hp => hg.mem_toFinset.2 hp), norm_prod]
  exact Finset.prod_eq_one fun p _ => h1 p

def cond (d : G.Dat) (B : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 F)) :
    Submodule (A.L p).O (G.S p).V → Prop :=
  if p ∈ B then fun Λ => ¬ (G.S p).BBzero (d p) Λ else (G.S p).BBzero (d p)

theorem amp_cond (d : G.Dat) (B : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 F)) :
    (G.S p).amp (d p) (cond G d B p) = if p ∈ B then (G.S p).amp (d p) (fun Λ => ¬ (G.S p).BBzero (d p) Λ)
      else (G.S p).amp (d p) ((G.S p).BBzero (d p)) := by
  unfold cond
  split_ifs <;> rfl

theorem cond_pos (d : G.Dat) {B : Finset (HeightOneSpectrum (𝓞 F))} {p : HeightOneSpectrum (𝓞 F)} (h : p ∈ B)
    (Λ : Submodule (A.L p).O (G.S p).V) : cond G d B p Λ ↔ ¬ (G.S p).BBzero (d p) Λ := by
  unfold cond
  rw [if_pos h]

theorem cond_neg (d : G.Dat) {B : Finset (HeightOneSpectrum (𝓞 F))} {p : HeightOneSpectrum (𝓞 F)} (h : p ∉ B)
    (Λ : Submodule (A.L p).O (G.S p).V) : cond G d B p Λ ↔ (G.S p).BBzero (d p) Λ := by
  unfold cond
  rw [if_neg h]

end GlobalTheory.HL.DefectPhase

namespace GlobalTheory.HL.DefectPhase

theorem amp_sum_defect_sets : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) → ∀ S1 : Finset (HeightOneSpectrum (𝓞 F)), G.Om ⊆ S1 → ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ Q : Prop → Prop, G.amp d (fun Λ => Q (¬ G.Gen d Λ)) = κ * ∑ B ∈ S1.powerset.filter (fun B => Q B.Nonempty), ∏ p ∈ S1, (if p ∈ B then (G.S p).amp (d p) (fun Λ => ¬ (G.S p).BBzero (d p) Λ) else (G.S p).amp (d p) ((G.S p).BBzero (d p))) := by
  intro F E _ _ _ _ _ sig A r k G hk d hex S1 hS1
  obtain ⟨Λ₀, hΛ₀⟩ := hex
  obtain ⟨-, -, -, -, hgood⟩ := GlobalTheory.HL.BadPlaces.bad_places A r k G hk d Λ₀ hΛ₀
  have hinv : ∀ p, ∀ h ∈ (G.S p).St, ∀ Λ, (G.S p).IsTerm (d p) Λ →
      ((G.S p).BBzero (d p) (h • Λ) ↔ (G.S p).BBzero (d p) Λ) := by
    intro p h hh Λ hΛ
    have := (A.loc p).lf
    have := (A.loc p).char0
    exact (GlobalTheory.FrameAct.stabiliser_acts_on_terms _ r k (G.S p) (d p) Λ hΛ h hh).2.2.2.2.2.2.2.1
  have hBB : ∀ p ∉ (S1 : Set _), ∀ Λ, (G.S p).IsTerm (d p) Λ → (G.S p).BBzero (d p) Λ :=
    fun p hp Λ hΛ => (hgood p fun h => hp (hS1 h)).1 _ _ hΛ
  have hprod : ∀ B : Finset (HeightOneSpectrum (𝓞 F)), B ⊆ S1 →
      G.amp d (fun Λ => ∀ p, cond G d B p (A.lat p Λ)) = ∏ᶠ p, (G.S p).amp (d p) (cond G d B p) ∧
      {p | (G.S p).amp (d p) (cond G d B p) ≠ 1 ∨ (G.S p).mass (d p) (cond G d B p) ≠ 1}.Finite ∧
      {o : Quot G.LRel | G.IsTerm d o.out}.Finite := by
    intro B hB
    have hI : ∀ p, ∀ h ∈ (G.S p).St, ∀ Λ, (G.S p).IsTerm (d p) Λ → cond G d B p Λ →
        cond G d B p (h • Λ) := by
      intro p h hh Λ hΛ hP
      by_cases hp : p ∈ B
      · rw [cond_pos G d hp] at hP ⊢
        rwa [hinv p h hh Λ hΛ]
      · rw [cond_neg G d hp] at hP ⊢
        rwa [hinv p h hh Λ hΛ]
    have hF : {p | ∃ Λ, (G.S p).IsTerm (d p) Λ ∧ ¬ cond G d B p Λ}.Finite := by
      refine S1.finite_toSet.subset fun p ⟨Λ, hΛ, hP⟩ => ?_
      by_contra hp
      have hpB : p ∉ B := fun h => hp (hB h)
      rw [cond_neg G d hpB] at hP
      exact hP (hBB p hp Λ hΛ)
    obtain ⟨a1, -, a3, a4⟩ := GlobalTheory.T.hermitian_amplitude_mass_product_structure A r k G hk d ⟨Λ₀, hΛ₀⟩ (cond G d B) hI hF
    exact ⟨a1, a3, a4⟩
  have hT := (hprod ∅ (Finset.empty_subset _)).2.2
  set g : HeightOneSpectrum (𝓞 F) → ℂ := fun p => (G.S p).amp (d p) ((G.S p).BBzero (d p)) with hg
  set c : ℂ := ∏ᶠ p, (if p ∈ S1 then 1 else g p) with hc
  have hsupp : ∀ B : Finset (HeightOneSpectrum (𝓞 F)), B ⊆ S1 →
      (Function.mulSupport fun p => (G.S p).amp (d p) (cond G d B p)).Finite := fun B hB =>
    (hprod B hB).2.1.subset fun p hp => Or.inl hp
  have hsplit : ∀ B : Finset (HeightOneSpectrum (𝓞 F)), B ⊆ S1 →
      G.amp d (fun Λ => ∀ p, cond G d B p (A.lat p Λ)) =
        c * ∏ p ∈ S1, (if p ∈ B then (G.S p).amp (d p) (fun Λ => ¬ (G.S p).BBzero (d p) Λ)
          else (G.S p).amp (d p) ((G.S p).BBzero (d p))) := by
    intro B hB
    rw [(hprod B hB).1, finprod_split' S1 _ g (hsupp B hB), mul_comm]
    · rw [Finset.prod_congr rfl fun p _ => amp_cond G d B p]
    · intro p hp
      have hpB : p ∉ B := fun h => hp (hB h)
      rw [amp_cond, if_neg hpB]
  have hc1 : ‖c‖ = 1 := by
    refine norm_finprod_eq_one _ ?_ fun p => ?_
    · refine (hsupp ∅ (Finset.empty_subset _)).subset fun p hp => ?_
      by_cases h : p ∈ S1
      · exact absurd (if_pos h) hp
      · change (G.S p).amp (d p) (cond G d ∅ p) ≠ 1
        rw [amp_cond, if_neg (Finset.notMem_empty p)]
        simpa [h] using hp
    · by_cases h : p ∈ S1
      · simp [h]
      · simp only [h, if_false, hg]
        exact ((hgood p fun hp => h (hS1 hp)).2 (d p) ⟨A.lat p Λ₀, hΛ₀.2 p⟩).1
  refine ⟨c, hc1, fun Q => ?_⟩
  have hsum : G.amp d (fun Λ => Q (¬ G.Gen d Λ)) = ∑ B ∈ S1.powerset.filter (fun B => Q B.Nonempty),
      G.amp d (fun Λ => ∀ p, cond G d B p (A.lat p Λ)) := by
    rw [amp_eq_finsum G d hT]
    simp only [amp_eq_finsum G d hT]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun o ho => ?_
    have hto : ∀ p, (G.S p).IsTerm (d p) (A.lat p o.out) := (hT.mem_toFinset.1 ho).2
    have hS : ∀ p, ¬ (G.S p).BBzero (d p) (A.lat p o.out) → p ∈ S1 := fun p hn => by
      by_contra hp
      exact hn (hBB p hp _ (hto p))
    set B₀ := S1.filter fun p => ¬ (G.S p).BBzero (d p) (A.lat p o.out) with hB₀
    have hgen : (¬ G.Gen d o.out) = B₀.Nonempty := by
      apply propext
      constructor
      · intro h
        obtain ⟨p, hp⟩ := not_forall.1 h
        exact ⟨p, Finset.mem_filter.2 ⟨hS p hp, hp⟩⟩
      · rintro ⟨p, hp⟩ h
        exact (Finset.mem_filter.1 hp).2 (h p)
    have heq : ∀ B ∈ S1.powerset.filter (fun B => Q B.Nonempty),
        (if ∀ p, cond G d B p (A.lat p o.out) then (G.mu o.out : ℂ) * G.om d o.out else 0) =
          if B₀ = B then (G.mu o.out : ℂ) * G.om d o.out else 0 := by
      intro B hB
      have hBS : B ⊆ S1 := Finset.mem_powerset.1 (Finset.mem_filter.1 hB).1
      have hiff : (∀ p, cond G d B p (A.lat p o.out)) ↔ B₀ = B := by
        constructor
        · intro hQ
          ext p
          constructor
          · intro hp
            by_contra hpB
            exact (Finset.mem_filter.1 hp).2 ((cond_neg G d hpB _).1 (hQ p))
          · intro hp
            exact Finset.mem_filter.2 ⟨hBS hp, (cond_pos G d hp _).1 (hQ p)⟩
        · rintro rfl p
          by_cases hp : p ∈ B₀
          · exact (cond_pos G d hp _).2 (Finset.mem_filter.1 hp).2
          · refine (cond_neg G d hp _).2 ?_
            by_contra hn
            exact hp (Finset.mem_filter.2 ⟨hS p hn, hn⟩)
      simp only [hiff]
    rw [Finset.sum_congr rfl heq, Finset.sum_ite_eq, hgen]
    have hmem : B₀ ∈ S1.powerset.filter (fun B => Q B.Nonempty) ↔ Q B₀.Nonempty := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨fun h => h.2, fun h => ⟨Finset.filter_subset _ _, h⟩⟩
    by_cases hq : Q B₀.Nonempty
    · rw [if_pos hq, if_pos (hmem.2 hq)]
    · rw [if_neg hq, if_neg (fun h => hq (hmem.1 h))]
  rw [hsum, Finset.sum_congr rfl fun B hB => hsplit B (Finset.mem_powerset.1 (Finset.mem_filter.1 hB).1),
    ← Finset.mul_sum]

end GlobalTheory.HL.DefectPhase
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeExpansionOverFinitePlacesStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.amplitude_expansion_over_finite_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) → ∀ S1 : Finset (HeightOneSpectrum (𝓞 F)), G.Om ⊆ S1 → ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ Q : Prop → Prop, G.amp d (fun Λ => Q (¬ G.Gen d Λ)) = κ * ∑ B ∈ S1.powerset.filter (fun B => Q B.Nonempty), ∏ p ∈ S1, (if p ∈ B then (G.S p).amp (d p) (fun Λ => ¬ (G.S p).BBzero (d p) Λ) else (G.S p).amp (d p) ((G.S p).BBzero (d p))) := by
  first | exact @GlobalTheory.HL.DefectPhase.amp_sum_defect_sets | exact GlobalTheory.HL.DefectPhase.amp_sum_defect_sets | (intros; apply GlobalTheory.HL.DefectPhase.amp_sum_defect_sets <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalAmplitudeEqLocalAmplitudes

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.AmpLoc



theorem global_amp_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (R : ∀ p, LocNG.Reps (FP p)) (S1 : Finset (PlF D)) (Om : Finset {p // p ∈ S1}) (d : ∀ p : {p // p ∈ S1}, LocNG.Datum (FP p.1)), (∀ p, p ∉ S1 → (FP p).PrimeTo) → (∀ p, p ∈ Om ↔ ¬ (FP p.1).PrimeTo) → (∀ p : {p // p ∈ S1}, Over (FP p.1) (d p) (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1 t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u'))) → ∀ Q : Prop → Prop, ‖G.amp (G.datOf (c.lat ρ t₀.lam)) (fun Γ => Q (¬ G.Gen (G.datOf (c.lat ρ t₀.lam)) Γ))‖ = ‖∑ A ∈ Om.powerset.filter (fun A => Q A.Nonempty), ∏ p, (if p ∈ A then LocNG.amp (R p.1) (d p) (LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1)) else LocNG.amp (R p.1) (d p) (fun t => ¬ LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1) t))‖ := by
  intro D X Y u u' hst hk w F00 F'0 FP hw hG hbase G c t₀ ρ U U' hmv R S1 Om d hout hOm hover Q
  have hT : G.IsTerm (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) :=
    (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hst hk w F00 F'0 FP hw hG hbase G c t₀ ρ U U' hmv).1
  have hW := fun p => GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates (Y.M p) (Y.agree p).1 (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p)
    D.R.rS D.R.k (FP p) (G.S p) (c.c p)
  obtain ⟨-, -, -, -, hgood⟩ := GlobalTheory.HL.BadPlaces.bad_places _ _ _ G hk _ _ hT
  have hOmS : G.Om ⊆ (S1 : Set (PlF D)) := by
    intro p hp
    by_contra hn
    exact hp ((hW p).2.2.2.1 (hout p hn))
  obtain ⟨κ, hκ, hdec⟩ := GlobalTheory.T.amplitude_expansion_over_finite_places _ _ _ G hk _ ⟨_, hT⟩ S1 hOmS
  rw [hdec Q, norm_mul, hκ, one_mul]

  have hloc : ∀ p : {p // p ∈ S1},
      (G.S p.1).amp (G.datOf (c.lat ρ t₀.lam) p.1)
          (fun Λ => ¬ (G.S p.1).BBzero (G.datOf (c.lat ρ t₀.lam) p.1) Λ) =
        LocNG.amp (R p.1) (d p) (LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1)) ∧
      (G.S p.1).amp (G.datOf (c.lat ρ t₀.lam) p.1) ((G.S p.1).BBzero (G.datOf (c.lat ρ t₀.lam) p.1)) =
        LocNG.amp (R p.1) (d p) (fun t => ¬ LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1) t) := by
    intro p
    haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p.1).lf
    haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p.1).char0
    have hu : (Function.update (G.datOf (c.lat ρ t₀.lam)) p.1 ((c.c p.1).dat (d p))) p.1 = (c.c p.1).dat (d p) :=
      Function.update_self _ _ _
    obtain ⟨h, hh, hδ⟩ := GlobalTheory.T.localDatum_of_term_in_movedLattice_orbit D X Y u u' hst hk w F00 F'0 FP hw hG hbase G c t₀ ρ U U' hmv p.1 (d p)
      (hover p) _ hu
    rw [hu] at hδ
    obtain ⟨e1, e2⟩ := (hW p.1).2.2.2.2 (R p.1) (d p)
    rw [e1, e2, ← hδ]
    constructor
    · refine (GlobalTheory.InvH.amp_mass_smul _ _ _ _ h hh _ _ _ ?_ ?_).1
      · intro s hs Λ hΛ hq hb
        exact hq ((GlobalTheory.FrameAct.stabiliser_acts_on_terms _ _ _ _ _ Λ hΛ s hs).2.2.2.2.2.2.2.1.1 hb)
      · intro Λ hΛ
        obtain ⟨-, -, -, hM, hs, -⟩ := GlobalTheory.HL.ComplAct.main _ _ _ _ _ Λ hΛ h hh
        exact not_congr ⟨fun e => hM.trans (e.trans hs.symm), fun e => hM.symm.trans (e.trans hs)⟩
    · refine (GlobalTheory.InvH.amp_mass_smul _ _ _ _ h hh _ _ _ ?_ ?_).1
      · intro s hs Λ hΛ hq
        exact (GlobalTheory.FrameAct.stabiliser_acts_on_terms _ _ _ _ _ Λ hΛ s hs).2.2.2.2.2.2.2.1.2 hq
      · intro Λ hΛ
        obtain ⟨-, -, -, hM, hs, -⟩ := GlobalTheory.HL.ComplAct.main _ _ _ _ _ Λ hΛ h hh
        exact ⟨fun e => hM.trans (e.trans hs.symm), fun e => hM.symm.trans (e.trans hs)⟩
  have hzero : ∀ p ∈ S1, (FP p).PrimeTo →
      (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p) (fun Λ => ¬ (G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p) Λ) = 0 := by
    intro p _ hp
    have hBB := (hgood p (fun hm => hm ((hW p).2.2.2.1 hp))).1
    unfold Frames.amp
    calc
      _ = ∑' _ : MulAction.orbitRel.Quotient (G.S p).St (Submodule _ (G.S p).V), (0 : ℂ) := by
        apply tsum_congr
        intro o
        rw [if_neg]
        rintro ⟨ht, hb⟩
        exact hb (hBB _ _ ht)
      _ = 0 := tsum_zero
  congr 1
  symm
  let emb : {p // p ∈ S1} ↪ PlF D := Function.Embedding.subtype _
  let embF : Finset {p // p ∈ S1} ↪ Finset (PlF D) := ⟨fun A => A.map emb, Finset.map_injective emb⟩
  calc _ = ∑ A ∈ Om.powerset.filter (fun A => Q A.Nonempty), ∏ p ∈ S1,
          (if p ∈ A.map emb then (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p)
              (fun Λ => ¬ (G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p) Λ)
            else (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p) ((G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p))) := by
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [← Finset.prod_coe_sort S1]
        refine Finset.prod_congr rfl fun p _ => ?_
        have hm : (p.1 ∈ A.map emb) ↔ p ∈ A := Finset.mem_map' emb
        by_cases hp : p ∈ A
        · rw [if_pos hp, if_pos (hm.2 hp), (hloc p).1]
        · rw [if_neg hp, if_neg (fun h => hp (hm.1 h)), (hloc p).2]
    _ = ∑ B ∈ (Om.powerset.filter (fun A => Q A.Nonempty)).map embF, ∏ p ∈ S1,
          (if p ∈ B then (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p)
              (fun Λ => ¬ (G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p) Λ)
            else (G.S p).amp (G.datOf (c.lat ρ t₀.lam) p) ((G.S p).BBzero (G.datOf (c.lat ρ t₀.lam) p))) :=
        by rw [Finset.sum_map]; rfl
    _ = _ := by
        apply Finset.sum_subset
        · intro B hB
          obtain ⟨A, hA, rfl⟩ := Finset.mem_map.1 hB
          rw [Finset.mem_filter, Finset.mem_powerset] at hA ⊢
          refine ⟨fun x hx => ?_, ?_⟩
          · obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
            exact y.2
          · show Q (A.map emb).Nonempty
            rw [Finset.map_nonempty]
            exact hA.2
        · intro B hB hn
          rw [Finset.mem_filter, Finset.mem_powerset] at hB
          by_cases hall : ∀ p ∈ B, ¬ (FP p).PrimeTo
          · exfalso
            apply hn
            have e : (B.subtype (· ∈ S1)).map emb = B := Finset.subtype_map_of_mem hB.1
            refine Finset.mem_map.2 ⟨B.subtype (· ∈ S1), ?_, e⟩
            rw [Finset.mem_filter, Finset.mem_powerset]
            refine ⟨fun q hq => (hOm q).2 (hall q.1 (Finset.mem_subtype.1 hq)), ?_⟩
            rw [← Finset.map_nonempty (f := emb), e]
            exact hB.2
          · push_neg at hall
            obtain ⟨p, hpB, hp⟩ := hall
            exact Finset.prod_eq_zero (hB.1 hpB) (by rw [if_pos hpB]; exact hzero p (hB.1 hpB) hp)

end GlobalTheory.HL.AmpLoc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalAmplitudeEqLocalAmplitudesStatement

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.globalAmplitude_eq_localAmplitudes : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (R : ∀ p, LocNG.Reps (FP p)) (S1 : Finset (PlF D)) (Om : Finset {p // p ∈ S1}) (d : ∀ p : {p // p ∈ S1}, LocNG.Datum (FP p.1)), (∀ p, p ∉ S1 → (FP p).PrimeTo) → (∀ p, p ∈ Om ↔ ¬ (FP p.1).PrimeTo) → (∀ p : {p // p ∈ S1}, Over (FP p.1) (d p) (locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1 t₀.toTerm.lam (lf D (X.Fu u)) (Quot.out t₀.toTerm.cls).1 (Tu D u) (Tu D u'))) → ∀ Q : Prop → Prop, ‖G.amp (G.datOf (c.lat ρ t₀.lam)) (fun Γ => Q (¬ G.Gen (G.datOf (c.lat ρ t₀.lam)) Γ))‖ = ‖∑ A ∈ Om.powerset.filter (fun A => Q A.Nonempty), ∏ p, (if p ∈ A then LocNG.amp (R p.1) (d p) (LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1)) else LocNG.amp (R p.1) (d p) (fun t => ¬ LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p.1) t))‖ := by
  first | exact @GlobalTheory.HL.AmpLoc.global_amp_local | exact GlobalTheory.HL.AmpLoc.global_amp_local | (intros; apply GlobalTheory.HL.AmpLoc.global_amp_local <;> assumption)
end
end
