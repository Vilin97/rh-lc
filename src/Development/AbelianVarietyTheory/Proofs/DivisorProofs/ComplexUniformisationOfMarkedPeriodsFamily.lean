module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasePointAndExponentialHolomorphicInPeriodsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationsSamePointDifferByIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationsSamePointDifferByIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMapLiftsLocallyToPeriodFamiliesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtTransportIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteImageOfLocallyConstantOnHolomorphicFamilie
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMapLiftsLocallyToPeriodFamiliesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtTransportIsometryStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteMarkedLatticePeriodRepresentatives

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

variable {O : Type} [Ring O] {bar : O → O}

theorem isPeriod_comp_symm {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {D D' : PLat O bar}
    {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ρ P) (w : D.La ≃ₗ[O] D'.La) (hw : IsIsom D D' w) :
    IsPeriod D' ρ (P.comp w.symm.toAddEquiv.toAddMonoidHom) := by
  obtain ⟨h1, h2, h3, h4, Hm, hH, hpos, hEF⟩ := hP
  have hr : (P.comp w.symm.toAddEquiv.toAddMonoidHom).range = P.range := by
    ext z
    simp only [AddMonoidHom.mem_range, AddMonoidHom.coe_comp, Function.comp_apply]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨w x, by simp⟩
  refine ⟨fun a x => ?_, ?_, ?_, ?_, Hm, hH, hpos, fun x y => ?_⟩
  · simp [h1]
  · exact h2.comp w.symm.injective
  · rw [hr]; exact h3
  · have : Set.range (P.comp w.symm.toAddEquiv.toAddMonoidHom) = Set.range P := by
      rw [← AddMonoidHom.coe_range, hr, AddMonoidHom.coe_range]
    rw [this]; exact h4
  · simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [hEF, ← hw]
    simp

def unifClass {Λ : Type} {g : ℕ} (F : Fam ℂ O Λ g) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (N : ℕ)
    (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (y : Sp ℂ ⟶ F.X) : Set ((D' : PLat O bar) × (Λ → D'.La)) :=
  {p | C p.1 p.2 ∧ ∃ P e, UnifAt F (RingHom.id ℂ) ρ N p.1 p.2 P y e}

theorem unifClass_eq {Λ : Type} {g : ℕ} (F : Fam ℂ O Λ g) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) {N : ℕ}
    (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (hN : 0 < N) {y : Sp ℂ ⟶ F.X} {D₀ : PLat O bar}
    {t₀ : Λ → D₀.La} {P₀ : D₀.La →+ (Fin g → ℂ)} {e₀ : (Fin g → ℂ) → (Over.mk y ⟶ F.A)}
    (hU : UnifAt F (RingHom.id ℂ) ρ N D₀ t₀ P₀ y e₀) :
    unifClass F ρ N C y = {p | C p.1 p.2 ∧ ∃ w, IsMarkedIsom N D₀ p.1 t₀ p.2 w} := by
  ext ⟨D', t'⟩
  constructor
  · rintro ⟨hC, P, e, hU'⟩
    obtain ⟨w, -, hw, -⟩ := GlobalTheory.T.complexUniformisations_same_point_differ_by_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D₀ D' t₀ t' P₀ P y e₀ e hN hU hU'
    exact ⟨hC, w, hw⟩
  · rintro ⟨hC, w, hw⟩
    exact ⟨hC, P₀.comp w.symm.toAddEquiv.toAddMonoidHom, _,
      GlobalTheory.T.uniformisationAt_transport_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D₀ D' t₀ t' P₀ (P₀.comp w.symm.toAddEquiv.toAddMonoidHom) y e₀ w
        (LinearEquiv.refl ℂ _) hN hU hw (fun x => by simp) (isPeriod_comp_symm hU.2.1 w hw.1)⟩

theorem exists_finite_representatives : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ), 0 < N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → FineAt F (RingHom.id ℂ) ρ N C → ∃ (n : ℕ) (Di : Fin n → PLat O bar) (t : ∀ i, Λ → (Di i).La), (∀ i, C (Di i) (t i) ∧ ∃ P, IsPeriod (Di i) ρ P) ∧ (∀ D' t', C D' t' → (∃ P, IsPeriod D' ρ P) → ∃ i w, IsMarkedIsom N D' (Di i) t' (t i) w) ∧ ∀ i j w, IsMarkedIsom N (Di i) (Di j) (t i) (t j) w → i = j := by
  intro O _ bar g ρ Λ F N C d hN heta hsm hqc hF
  have : Smooth F.s := SmoothOfRelativeDimension.smooth d F.s
  have hlft : LocallyOfFiniteType F.s := inferInstance

  have hloc : ∀ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ F.X)), IsOpen B →
      (∀ b ∈ B, y b ≫ F.s = spMap (RingHom.id ℂ)) → IsHolTo B y → ∀ b₀ ∈ B,
      ∀ᶠ b in nhds b₀, unifClass F ρ N C (y b) = unifClass F ρ N C (y b₀) := by
    intro B y hB hy hhol b₀ hb₀
    obtain ⟨D₀, t₀, P₀, e₀, -, hU₀⟩ := hF.pts (y b₀) (hy b₀ hb₀)
    obtain ⟨B', P, e, hB', hb₀', -, -, -, -, hU⟩ :=
      GlobalTheory.T.holomorphicMap_lifts_locally_to_periodFamilies O bar g ρ Λ F N D₀ t₀ d B y b₀ P₀ e₀ hN heta hlft hB hb₀ hy hhol hU₀
    filter_upwards [hB'.mem_nhds hb₀'] with b hb
    rw [unifClass_eq F ρ C hN (hU b hb), unifClass_eq F ρ C hN hU₀]
  have hfin := GlobalTheory.FiniteClasses.finite_image_of_locally_constant_on_holomorphic_families
    GlobalTheory.SubfieldChart.exists_holomorphic_chart ℂ (RingHom.id ℂ) F.X F.s d _ (unifClass F ρ N C) hsm hqc hloc
  set T := unifClass F ρ N C '' {x | x ≫ F.s = spMap (RingHom.id ℂ)} with hT
  haveI := hfin.fintype
  let E := (Fintype.equivFin T).symm
  have hch : ∀ c : T, ∃ (p : (D' : PLat O bar) × (Λ → D'.La)) (y : Sp ℂ ⟶ F.X), unifClass F ρ N C y = c.1 ∧ p ∈ unifClass F ρ N C y := by
    rintro ⟨c, y, hy, rfl⟩
    obtain ⟨D', t', P, e, hC, hU⟩ := hF.pts y hy
    exact ⟨⟨D', t'⟩, y, rfl, hC, P, e, hU⟩
  choose p y hcls hmem using hch
  refine ⟨Fintype.card T, fun i => (p (E i)).1, fun i => (p (E i)).2, fun i => ?_, ?_, ?_⟩
  · obtain ⟨hC, P, e, hU⟩ := hmem (E i)
    exact ⟨hC, P, hU.2.1⟩
  · rintro D' t' hC ⟨P, hP⟩
    obtain ⟨y', e', hU'⟩ := hF.occ D' t' P hC hP
    let c : T := ⟨unifClass F ρ N C y', y', hU'.1, rfl⟩
    refine ⟨E.symm c, ?_⟩
    have h1 : p (E (E.symm c)) ∈ unifClass F ρ N C y' := by
      have := hmem (E (E.symm c))
      have h2 : ((E (E.symm c)) : Set ((D' : PLat O bar) × (Λ → D'.La))) = unifClass F ρ N C y' :=
        congrArg Subtype.val (E.apply_symm_apply c)
      rwa [hcls, h2] at this
    rw [unifClass_eq F ρ C hN hU'] at h1
    exact h1.2
  · intro i j w hw
    apply E.injective
    apply Subtype.ext
    obtain ⟨hCi, Pi, ei, hUi⟩ := hmem (E i)
    obtain ⟨hCj, Pj, ej, hUj⟩ := hmem (E j)
    have hj' : p (E j) ∈ unifClass F ρ N C (y (E i)) := by
      rw [unifClass_eq F ρ C hN hUi]
      exact ⟨hCj, w, hw⟩
    obtain ⟨-, Pj', ej', hUj'⟩ := hj'
    rw [← hcls, ← hcls, unifClass_eq F ρ C hN hUj', unifClass_eq F ρ C hN hUj]

end GlobalTheory.PELU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteMarkedLatticePeriodRepresentativesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_finite_markedLattice_period_representatives : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ), 0 < N → (∀ a, F.eta a ^ N = 1) → SmoothOfRelativeDimension d F.s → QuasiCompact F.s → FineAt F (RingHom.id ℂ) ρ N C → ∃ (n : ℕ) (Di : Fin n → PLat O bar) (t : ∀ i, Λ → (Di i).La), (∀ i, C (Di i) (t i) ∧ ∃ P, IsPeriod (Di i) ρ P) ∧ (∀ D' t', C D' t' → (∃ P, IsPeriod D' ρ P) → ∃ i w, IsMarkedIsom N D' (Di i) t' (t i) w) ∧ ∀ i j w, IsMarkedIsom N (Di i) (Di j) (t i) (t j) w → i = j := by
  first | exact @GlobalTheory.PELU.exists_finite_representatives | exact GlobalTheory.PELU.exists_finite_representatives | (intros; apply GlobalTheory.PELU.exists_finite_representatives <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationOfMarkedPeriodsFamily

section

@[expose] public section

noncomputable section

namespace GlobalTheory.PELU

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem isPeriod_comp_isometry_symm {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    (D D' : PLat O bar) (w : D.La ≃ₗ[O] D'.La) (hw : IsIsom D D' w) (P : D.La →+ (Fin g → ℂ))
    (hP : IsPeriod D ρ P) : IsPeriod D' ρ (P.comp w.symm.toLinearMap.toAddMonoidHom) := by
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, him⟩ := hP
  have hrange : (P.comp w.symm.toLinearMap.toAddMonoidHom).range = P.range := by
    ext v
    simp only [AddMonoidHom.mem_range, AddMonoidHom.comp_apply]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨w x, by simp⟩
  have hrange' : Set.range (P.comp w.symm.toLinearMap.toAddMonoidHom) = Set.range P := by
    have := congrArg (fun S : AddSubgroup (Fin g → ℂ) => (S : Set (Fin g → ℂ))) hrange
    simpa [AddMonoidHom.coe_range] using this
  refine ⟨fun a x => ?_, ?_, ?_, ?_, Hm, hH, hpos, fun x y => ?_⟩
  · simp [hlin]
  · intro x y hxy
    have := hinj hxy
    simpa using this
  · rw [hrange]; exact hdisc
  · rw [hrange']; exact hspan
  · have := hw (w.symm x) (w.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    simp [him, this]

theorem unif_of_fineAt : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type)
    (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ), 3 ≤ N → (∀ a, F.eta a ^ N = 1) →
    SmoothOfRelativeDimension d F.s → QuasiCompact F.s → (∀ D' t, C D' t → FullMark N D' t) →
    FineAt F (RingHom.id ℂ) ρ N C → Nonempty (Unif F (RingHom.id ℂ) ρ N C) := by
  intro O _ bar g ρ Λ F N C d hN heta hsm hqc hfull hF
  have hN0 : 0 < N := by omega
  have hlft : LocallyOfFiniteType F.s := by
    haveI := hsm
    haveI : Smooth F.s := SmoothOfRelativeDimension.smooth d F.s
    infer_instance
  obtain ⟨n, Di, t, hmem, hall, hdist⟩ := GlobalTheory.T.exists_finite_markedLattice_period_representatives O bar g ρ Λ F N C d hN0 heta hsm hqc hF
  have hQ : ∀ i (P : (Di i).La →+ (Fin g → ℂ)), ∃ Q, IsPeriod (Di i) ρ Q ∧ (IsPeriod (Di i) ρ P → Q = P) := by
    intro i P
    by_cases hP : IsPeriod (Di i) ρ P
    · exact ⟨P, hP, fun _ => rfl⟩
    · obtain ⟨Q, hQ⟩ := (hmem i).2
      exact ⟨Q, hQ, fun h => absurd h hP⟩
  choose Q hQp hQe using hQ
  have hex : ∀ i P, ∃ y e, UnifAt F (RingHom.id ℂ) ρ N (Di i) (t i) (Q i P) y e :=
    fun i P => hF.occ _ _ _ (hmem i).1 (hQp i P)
  choose u ex hu using hex
  have hunif : ∀ i P, IsPeriod (Di i) ρ P → UnifAt F (RingHom.id ℂ) ρ N (Di i) (t i) P (u i P) (ex i P) := by
    intro i P hP
    have := hu i P
    rwa [hQe i P hP] at this
  have hrefl : ∀ i, IsMarkedIsom N (Di i) (Di i) (t i) (t i) (LinearEquiv.refl O _) :=
    fun i => ⟨fun x y => rfl, fun a => ⟨0, by simp⟩⟩
  have cmpEq : ∀ (D' D'' : PLat O bar) (t' : Λ → D'.La) (t'' : Λ → D''.La) (P : D'.La →+ (Fin g → ℂ))
      (P' : D''.La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ F.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ F.A))
      (e' : (Fin g → ℂ) → (Over.mk y' ⟶ F.A)), y = y' →
      UnifAt F (RingHom.id ℂ) ρ N D' t' P y e → UnifAt F (RingHom.id ℂ) ρ N D'' t'' P' y' e' →
      ∃ (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
        IsMarkedIsom N D' D'' t' t'' w ∧ ∀ x, P' (w x) = h (P x) := by
    intro D' D'' t' t'' P P' y y' e e' hy h1 h2
    subst hy
    obtain ⟨w, h, hw, hP, -⟩ := GlobalTheory.T.complexUniformisations_same_point_differ_by_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D' D'' t' t'' P P' y e e' hN0 h1 h2
    exact ⟨w, h, hw, hP⟩
  refine ⟨{
      n := n
      Di := Di
      t := t
      mem := fun i => (hmem i).1
      ne := fun i => (hmem i).2
      all := hall
      distinct := hdist
      u := u
      ex := ex
      unif := hunif
      onto := ?_
      disj := ?_
      fibre := ?_
      hol := ?_
      lift := ?_ }⟩
  · intro y hy
    obtain ⟨D', t', P, e, hC, hU⟩ := hF.pts y hy
    obtain ⟨i, w, hw⟩ := hall D' t' hC ⟨P, hU.2.1⟩
    have hP' := isPeriod_comp_isometry_symm D' (Di i) w hw.1 P hU.2.1
    refine ⟨i, _, hP', ?_⟩
    exact (hF.sep D' (Di i) t' (t i) P _ y _ e (ex i _) hU (hunif i _ hP') w (LinearEquiv.refl ℂ _) hw
      (fun x => by simp)).symm
  · intro i j P P' hP hP' huu
    obtain ⟨w, h, hw, -⟩ := cmpEq _ _ _ _ _ _ _ _ _ _ huu (hunif i P hP) (hunif j P' hP')
    exact hdist i j w hw
  · intro i P P' hP hP'
    constructor
    · intro huu
      exact cmpEq _ _ _ _ _ _ _ _ _ _ huu (hunif i P hP) (hunif i P' hP')
    · rintro ⟨w, h, hw, hPw⟩
      exact hF.sep _ _ _ _ _ _ _ _ _ _ (hunif i P hP) (hunif i P' hP') w h hw hPw
  · intro i m B P hB hHol
    exact GlobalTheory.T.basePoint_and_exponential_holomorphic_in_periods O bar g ρ Λ F N C d (Di i) (t i) m B P (fun b => u i (P b)) (fun b => ex i (P b)) hN heta hsm
      hqc hF (hmem i).1 (hfull _ _ (hmem i).1) hB hHol (fun b hb => hunif i (P b) (hHol.1 b hb))
  · intro m B y hB hy hhol b₀ hb₀
    obtain ⟨D', t', P, e, hC, hU⟩ := hF.pts (y b₀) (hy b₀ hb₀)
    obtain ⟨i, w, hw⟩ := hall D' t' hC ⟨P, hU.2.1⟩
    have hP' := isPeriod_comp_isometry_symm D' (Di i) w hw.1 P hU.2.1
    have hU' := GlobalTheory.T.uniformisationAt_transport_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D' (Di i) t' (t i) P _ (y b₀) e w
      (LinearEquiv.refl ℂ _) hN0 hU hw (fun x => by simp) hP'
    obtain ⟨B', P₁, e₁, hB', hb₀', hBB, -, hHol, -, hU₁⟩ :=
      GlobalTheory.T.holomorphicMap_lifts_locally_to_periodFamilies O bar g ρ Λ F N (Di i) (t i) m B y b₀ _ _ hN0 heta hlft hB hb₀ hy hhol hU'
    refine ⟨B', i, P₁, hB', hb₀', hBB, hHol, fun b hb => ?_⟩
    exact hF.sep _ _ _ _ _ _ _ _ _ _ (hunif i (P₁ b) (hHol.1 b hb)) (hU₁ b hb) (LinearEquiv.refl O _)
      (LinearEquiv.refl ℂ _) (hrefl i) (fun x => rfl)

end GlobalTheory.PELU
end
end
end
